#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/* Helper function to calculate index of a block */
static int calculate_index(header *block) {
  int allocable_size = get_size(block) - ALLOC_HEADER_SIZE;
  int index = (allocable_size / 8) - 1;

  if (index > (N_LISTS-1) ) {
    index = N_LISTS - 1;
  }

  return index;
}


/* Helper function to find a block in the freelist of allocable_size */
static header *find_block_in_freelist(int allocable_size) {

  /* Calculate index again */
  int index = (allocable_size / 8) - 1;
  //printf("index: %d\n", index);
  if (index > (N_LISTS - 1)) {
    index = N_LISTS - 1;
  }

  bool block_was_found = false;

  /* Search 0 through N_LISTS-2 */
  for (int i = index; i < N_LISTS-1; i++) {
    if (freelistSentinels[i].next == &freelistSentinels[i]) {      // if list is empty, it is pointing to itself
      // empty, go to next list
      continue;
    } else {
      // block found, return it
      block_was_found = true;
      return freelistSentinels[i].next;
    }
  }

  /* BLOCK NOT FOUND IN 0 THROUGH N_LISTS-2, GO TO N_LISTS-1 */

  /* Search N_LISTS-1 */
  index = N_LISTS - 1;
  header *sentinel = &freelistSentinels[index];  // If node == sentinel, it has looped back around and block was not found.
  header *current_block = freelistSentinels[index].next;  // Set current to the first NODE, not the sentinel
  while (current_block != sentinel) {
    /* Subtract 16 because we want to compare allocable size, NOT actual size */
    if ( (get_size(current_block) - ALLOC_HEADER_SIZE) >= allocable_size) {
      block_was_found = true;
      return current_block;
    }
    /* Update current_block */
    current_block = current_block->next;
  }


  if (block_was_found == false) {
     //CALL ALLOCATE_CHUNK() -> HANDLE IN TASK 3
     return NULL;
  }

  return NULL;
}


/* Helper function to remove a block from the freelist */
static void remove_block(header *block) {

  /* Calculate index */
  int allocable_size = get_size(block) - ALLOC_HEADER_SIZE;
  int index = (allocable_size/8) - 1;

  if (index > (N_LISTS - 1)) {
    index = N_LISTS - 1;
  }

  /* Remove the block using the pointer that was passed into the function */
  block->prev->next = block->next;
  block->next->prev = block->prev;

}



/* Helper function to insert block in the freelist */
static void insert_block(header *block) {
  /* Calculate Index */
  int allocable_size = get_size(block) - ALLOC_HEADER_SIZE;
  int index = (allocable_size/8) - 1;

  /* Set any index greater to N_LISTS-1 to N_LISTS-1 */
  if (index > (N_LISTS - 1)) {
    index = N_LISTS - 1;
  }

  /* Insert at beginning of the index */
  block->next = freelistSentinels[index].next;
  block->prev = &freelistSentinels[index];
  freelistSentinels[index].next->prev = block;
  freelistSentinels[index].next = block;

}



/* Helper function to split a block */
static inline header *split_block(header *block, int allocable_size) {
  int og_index = calculate_index(block);
  //remove_block(block);

  /* Calculate actual size required to allocate for the new_block */
  int actual_size = allocable_size + ALLOC_HEADER_SIZE;

  /* Calculate extra space/actual size of extra block for the block that you are going to insert */
  int extra_block_allocable_size = get_size(block) - ALLOC_HEADER_SIZE - actual_size;

  /* Create a pointer for the remainder block */
  header *remainder = block;

  /* Set a pointer for the block to allocate (higher in memory - to the right) */
  header *new_block = (header *)((char*)remainder + extra_block_allocable_size + ALLOC_HEADER_SIZE);

  set_size(new_block, allocable_size + ALLOC_HEADER_SIZE);
  set_size(remainder, extra_block_allocable_size + ALLOC_HEADER_SIZE);

  set_state(new_block, ALLOCATED);
  set_state(remainder, UNALLOCATED);

  new_block->left_size = get_size(remainder);

  int remainder_index = calculate_index(remainder);
  if (og_index != remainder_index) {
    remove_block(block);
    insert_block(remainder);
  }

  (get_right_header(new_block))->left_size = get_size(new_block);

  /* Return new_block */
  return (header *)new_block->data;


}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {

  /* Base case */
  if (raw_size == 0) {
    return NULL;
  }

  int req_size = raw_size;

  /* raw_size is the size that the user requests */
  /* allocable_size is the size of the block that is allocable. Does NOT include header */
  /* actual_size is the actual size of the block (allocable_size + 16) --> INCLUDES header */


  /* Round up request_size to the next 8-byte modulo to find allocable_size */
  int remainder = req_size%8;
  int allocable_size = req_size;
  if (remainder != 0) {
    allocable_size = req_size + (8 - remainder);
  }

  /* Add ALLOC_HEADER_SIZE to the alloc size to get the actual size */
  /* ALLOC_HEADER_SIZE is 16 */
  int actual_size = allocable_size + ALLOC_HEADER_SIZE;

  /* Round up to 32 is actual size is less than that */
  if (actual_size < sizeof(header)) {
    actual_size = sizeof(header);
    allocable_size = actual_size - ALLOC_HEADER_SIZE; // Update allocable size since it was changed in this if statement
  }

  /* Find a block of the appropriate size */
  header *block = find_block_in_freelist(allocable_size);


  /* TASK 3 */
  if (block == NULL) {
    /* CHUNK CODE */
    /* Call allocate_chunk */
    header *new = allocate_chunk(ARENA_SIZE);
    set_state(new, UNALLOCATED);
    header *new_fp1 = get_header_from_offset(new, -ALLOC_HEADER_SIZE);
    set_state(new_fp1, FENCEPOST);

    /* Check if it is contiguous to the chunk before it */
    //if ( (header *)((char *)new_fp1 - ALLOC_HEADER_SIZE) == (header *)((char *)lastFencePost) ) {
    if ( (get_header_from_offset(new_fp1, -ALLOC_HEADER_SIZE)) == get_header_from_offset(lastFencePost, 0) ) {
      /* Coalesce */
      header *left = get_left_header(lastFencePost);       // should this be before allocate_chunk() ?
      /* Check if the left block is free. If it is, coalesce into one block*/
      if (get_state(left) == UNALLOCATED) {
        remove_block(left);
        int size_left = get_size(left);
        int size_new = get_size(new);
        int final_size = size_left + size_new + ALLOC_HEADER_SIZE + ALLOC_HEADER_SIZE;
        set_size(left, final_size);
        set_state(left, UNALLOCATED);

        insert_block(left);

        /* Update lastFencePost */
        lastFencePost = get_header_from_offset(left, get_size(left));
        set_state(lastFencePost, FENCEPOST);
        lastFencePost->left_size = get_size(left);
      } else {  /* left block is allocated */
        /* Move "new" back to lastFencePost's location */
        header *c = get_header_from_offset(new, -(2*ALLOC_HEADER_SIZE));
        set_size(c, get_size(new) + (2*ALLOC_HEADER_SIZE) );
        set_state(c, UNALLOCATED);
        insert_block(c);

        /* Update lastFencePost */
        //lastFencePost = (header *) ((char *)  new + get_size(new));
        lastFencePost = get_header_from_offset(c, get_size(c));
        set_state(lastFencePost, FENCEPOST);
        lastFencePost->left_size = get_size(c);
      }
    } else {  /* Not Contiguous */
      insert_os_chunk(new_fp1);
      insert_block(new);
      /* Update lastFencePost */
      lastFencePost = get_header_from_offset(new, get_size(new));
      set_state(lastFencePost, FENCEPOST);
      lastFencePost->left_size = get_size(new);
    }

    return allocate_object(raw_size);    // use recursion --> call alllocate object again
  }

  /* Determine if it needs to be split */
  /* If block.  found size - actual size needed > sizeof(header) */
  if ( (get_size(block) - actual_size) >= sizeof(header) ) {
    /* Split the block */
    split_block(block, allocable_size);
   } else {
    /* Do not split the block */
    /* Change state */
    set_state(block, ALLOCATED);
    /* Remove from freelist */
    remove_block(block);
    /* Return block */
    return (header *)block->data;
    }
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {

  if (p == NULL) {
    return;
  }

  /* Get pointers */
  header *block = ptr_to_header(p);
  header *right_block = get_right_header(block);
  header *left_block = get_left_header(block);

  /* Check for double free */
  if (get_state(block) != ALLOCATED) {
    printf("Double Free Detected\n");
    assert(false);
    exit(1);
  }

  set_state(block, UNALLOCATED);

  /* CASE 1 - left free --> coalesce */
  if (get_state(left_block) == UNALLOCATED && (get_state(right_block) != UNALLOCATED) ) {
    /* Coalesce left block and block */


    int og_index = calculate_index(left_block);

    /* Remove left from freelist */
    //remove_block(left_block);

    header *right_to_block = get_right_header(block);
    /* We will be update LEFT BLOCK to the updated size and state */
    set_size(left_block, get_size(left_block) + get_size(block));
    set_state(left_block, UNALLOCATED);
    right_to_block->left_size = get_size(left_block);

    /* Insert Left block into correct freelist if it is not in N_LISTS-1 */
    int new_index = calculate_index(left_block);
    if (og_index != new_index) {
      remove_block(left_block);
      insert_block(left_block);
    }
    block = NULL;





  }

  /* CASE 2 - right free --> coalesce */
  if (get_state(right_block) == UNALLOCATED && (get_state(left_block) != UNALLOCATED) ) {
    /* Coalesce right block and block */

    /* Remove both from freelist */
    //remove_block(block);

    header *right_of_right = get_right_header(right_block);
    //remove_block(right_block);
    int og_index = calculate_index(right_block);

    /* We will be updating BLOCK to the updated size and state */
    set_size(block, get_size(block) + get_size(right_block));
    set_state(block, UNALLOCATED);
    right_of_right->left_size = get_size(block);

    /* Insert Block into correct freelist if it is not already*/
    int new_index = calculate_index(block);
    if (og_index != new_index) {
      remove_block(right_block);
      insert_block(block);
    }
    //right_block = NULL;
  }

  /* CASE 3 - neither free --> DON'T coalesce */
  if ( (get_state(right_block) != UNALLOCATED) && (get_state(left_block) != UNALLOCATED) ) {
    /* Change state */
    set_state(block, UNALLOCATED);
    /* Insert into freelist */
    insert_block(block);

  }


  /* CASE 4 - both free --> coalesce */
  if ( (get_state(right_block) == UNALLOCATED) && (get_state(left_block) == UNALLOCATED) ) {
  /* Coalesce block and right first */
    /* Remove both from freelist */
    //remove_block(block);
    remove_block(right_block);

    /* We will be updating BLOCK to the updated size and state */
    set_size(block, get_size(block) + get_size(right_block));
    set_state(block, UNALLOCATED);
    get_right_header(block)->left_size = get_size(block);

    /* Insert Block into correct freelist */
    //insert_block(block);         // uncomment this is issues arise

  /* Coalesce left block and block */

    int og_left_index = calculate_index(left_block);

    /* Remove both from freelist */
    //remove_block(left_block);
    //remove_block(block);
    /* We will be update LEFT BLOCK to the updated size and state */
    set_size(left_block, get_size(left_block) + get_size(block));
    set_state(left_block, UNALLOCATED);
    get_right_header(left_block)->left_size = get_size(left_block);

    /* Insert Left block into correct freelist */
    if (og_left_index != N_LISTS - 1) {
      //remove_block(block);     // uncomment this is issues arise
      insert_block(left_block);
    }

  }


}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
