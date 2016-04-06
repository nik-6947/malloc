/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Project-Malloc",
	/* First member's full name */
	"VV SaiTeja",
	/* First member's email address */
	"201401036@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"Nikita Bhagat",
	/* Second member's email address (leave blank if none) */
	"201401063@daiict.ac.in"
};

#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

/*Max value of 2 values*/
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)


/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)  ((void *)(bp) - WSIZE)
#define FTRP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)  ((void *)(bp) - GET_SIZE((void *)(bp) - DSIZE))

/* Given ptr in free list, get next and previous ptr in the list */
/* bp is address of the free block. Since minimum Block size is 16 bytes, 
   we utilize to store the address of previous block pointer and next block pointer.
*/
#define GET_NEXTP(bp)  (*(char **)(bp + WSIZE))
#define GET_PREVP(bp)  (*(char **)(bp))

/* Puts pointers in the next and previous elements of free list */
#define SET_NEXTP(bp, qp) (GET_NEXTP(bp) = qp)
#define SET_PREVP(bp, qp) (GET_PREVP(bp) = qp)

/* Global declarations */
static char *heap_listp = 0; 
static char *list_head = 0;

/* Function prototypes for internal helper routines */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for maintaining free list*/
static void insert_list(void *bp); 
static void remove_list(void *bp); 

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/*Functions for the checking of the free list and the blocks present in it*/
static void in_heap(const void *p);
static void check_coalescing();
static void check_free_list();
static void check_free_blocks();

/**
 * Initialize the memory manager.
 * @param - void no parameter passed in
 * @return - int 0 for success or -1 for failure
 */
int 
mm_init(void) 
{
  
  /* Create the initial empty heap. */
  if ((heap_listp = mem_sbrk(8*WSIZE)) == (void *)-1) 
    return -1;

  PUT(heap_listp, 0);                            /* Alignment padding */
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
  list_head = heap_listp + 3*WSIZE; 
  SET_NEXTP(list_head, NULL);					/*setting next pointer to null*/

  /* Extend the empty heap with a free block of minimum possible block size */
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL){ 
    return -1;
  }
  return 0;
}

/* 
 * Requires:
 *   size of memory asked by the programmer.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
  size_t asize;      /* Adjusted block size */
  size_t extendsize; /* Amount to extend heap if no fit */
  void *bp;

  /* Ignore spurious requests. */
  if (size == 0)
    return (NULL);

  /* Adjust block size to include overhead and alignment reqs. */
  if (size <= DSIZE)
    asize = 2 * DSIZE;
  else
    asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

  /* Search the free list for a fit. */
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return (bp);
  }

  /* No fit found.  Get more memory and place the block. */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
    return (NULL);
  place(bp, asize);
  return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void 
mm_free(void *bp)
{
  size_t size;
  /* Ignore spurious requests. */
  if (bp == NULL)
    return;
  /* Free and coalesce the block. */
  size = GET_SIZE(HDRP(bp));
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero. If "size" is zero, frees the block "ptr" and returns NULL.  
 *   If the block "ptr" is already a block with at least "size" bytes of payload, then "ptr" may optionally be returned.
 *   If the requested size is greater than the present block size,and next block is free then we can just 
 *	 combine present block and next block to resize them so as to satisfy the requested realloc size. 
 *   If nothing can be done then a new block is allocated (using malloc) and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
	 size_t presize;
     size_t reqsize; 

  /* If size == 0 then this is just free, and we return NULL. */
  if((int)size == 0){ 
    mm_free(ptr); 
    return NULL; 
  } 

  /*any spurious requests*/
  else if((int)size < 0) 
    return NULL; 

/* If oldptr is NULL, then this is just malloc. */
  else if (ptr == NULL)
  {
  	/* code */
  	return mm_malloc(size);
  }
  else if(size > 0){ 

       presize = GET_SIZE(HDRP(ptr)); 
       reqsize = size + 2 * WSIZE;
      
		if (presize >= reqsize)
		{
			/* code */
			return ptr;
		}
      
      /*When the requested size is greater than the present allocated size of that pointer */ 
      else { 
          size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr))); 
          size_t tempSize;

          /* when the next block is free and the combined size of the the next block and current block is more than the required
          size then just join the two blocks*/ 
          if(!next_alloc && ((tempSize = presize + GET_SIZE(HDRP(NEXT_BLKP(ptr))))) >= reqsize){ 
            remove_list(NEXT_BLKP(ptr)); 
            PUT(HDRP(ptr), PACK(tempSize, 1)); 
            PUT(FTRP(ptr), PACK(tempSize, 1)); 
            return ptr; 
          }
          else {  
            void *tempptr = mm_malloc(reqsize);  
            place(tempptr, reqsize);
            memcpy(tempptr, ptr, reqsize); 
            mm_free(ptr); 
            return tempptr; 
          } 
      }
  }else 
    return NULL;
} 


/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing. 
 */
static void *
coalesce(void *bp)
{
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
  size_t size = GET_SIZE(HDRP(bp));
  
  /* Next block is free */   
  if (prev_alloc && !next_alloc) {                  
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    remove_list(NEXT_BLKP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  /* Previous block is free */  
  else if (!prev_alloc && next_alloc) {               
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    bp = PREV_BLKP(bp);
    remove_list(bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  /* Both blocks are free */ 
  else if (!prev_alloc && !next_alloc) {                
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
    remove_list(PREV_BLKP(bp));
    remove_list(NEXT_BLKP(bp));
    bp = PREV_BLKP(bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  /*insert bp,free block into free list*/
  insert_list(bp);
  return bp;
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */

static void *
extend_heap(size_t words) 
{
  char *bp;
  size_t size;

  /* Arithmetic to maintain alignment */
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
  
  if ((bp = mem_sbrk(size)) == (void *)-1){ 
    return NULL;
  }
  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));         /* free block header */
  PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */
  
  /* coalesce if next and previous block is free*/
  return coalesce(bp);
}

/*
 * Requires:
 *   Size of memory to find.
 * Effects:
 *   Finds a fit for a block with "asize" bytes from the free list.
 *   or NULL if no suitable block was found. 
 */

static void *
find_fit(size_t asize)
{

  void *bp;
  for (bp = list_head; bp != NULL; bp = GET_NEXTP(bp) ){
    if (asize <= (size_t)GET_SIZE(HDRP(bp)) ) {
      return bp;
    }
  }
  return NULL;

}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void 
place(void *bp, size_t asize)
{
  size_t tempSize = GET_SIZE(HDRP(bp));

  if ((tempSize - asize) >= 4 * WSIZE) {			/*if there is a extra space, split the larger block and then use it*/
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    remove_list(bp);
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(tempSize-asize, 0));
    PUT(FTRP(bp), PACK(tempSize-asize, 0));
    insert_list(bp);
   // coalesce(bp);
  }
  else {
    PUT(HDRP(bp), PACK(tempSize, 1));
    PUT(FTRP(bp), PACK(tempSize, 1));
    remove_list(bp);
  }
}

/*Inserting a free block into the free list*/
static void insert_list(void *bp){
  SET_NEXTP(bp, list_head); 
  SET_PREVP(list_head, bp); 
  SET_PREVP(bp, NULL); 
  list_head = bp; 
}
/*Removing a block from the free list either due to allocation or during coalascing*/
static void remove_list(void *bp){
  if (GET_PREVP(bp))
    SET_NEXTP(GET_PREVP(bp), GET_NEXTP(bp));
  else
    list_head = GET_NEXTP(bp);
  SET_PREVP(GET_NEXTP(bp), GET_PREVP(bp));
}


/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp) 
{

  if ((uintptr_t)bp % DSIZE)
    printf("Error: %p is not doubleword aligned\n", bp);
  if (GET(HDRP(bp)) != GET(FTRP(bp)))
    printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
  void *bp;

  if (verbose)
    printf("Heap (%p):\n", heap_listp);

  if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
      !GET_ALLOC(HDRP(heap_listp)))
    printf("Bad prologue header\n");
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = (void *)NEXT_BLKP(bp)) {
    if (verbose)
      printblock(bp);
    checkblock(bp);
  }

  if (verbose)
    printblock(bp);
  if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
    printf("Bad epilogue header\n");

in_heap(bp);
check_coalescing();
check_free_list();
check_free_blocks();
}

/* This is to check if there are any allocated blocks in the free blocks! */
static void
check_free_list(){

  void *bp;
  for (bp = list_head; bp != NULL; bp = GET_NEXTP(bp) ){
    if (GET_ALLOC(bp)) {
      printf("ERROR: allocated block in free list!\n");
      printblock(bp);
    }
  }

}

/*This is to check if there are any free blocks that missed the coalescing and end up in the free list as two different blocks */
static void
check_coalescing(){

void *bp;
void *temp;

  for (bp = list_head; bp != NULL; bp = GET_NEXTP(bp) ){
  	for (temp = list_head; temp != NULL; temp = GET_NEXTP(temp))
  	{
  		/* code */
  		if(NEXT_BLKP(bp) == temp)
  		{
  			printf("ERROR: A block missed during Coalescing.");
  			printblock(bp);
  			printblock(temp);
  		}
  	}
  }


}


/*This is to check whether every free block in the heap list is present in the free list and print out an error if not!*/

static void
check_free_blocks(){
	void *bp;
    unsigned int heapCount = 0;
    unsigned int listCount = 0;
    /*Iterate over list*/   
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if(!GET_ALLOC(HDRP(bp))) {
            heapCount++;
        }
    }
    /* Moving free list by pointers*/
    for (bp = list_head; bp != NULL; bp = GET_NEXTP(bp) ){
    	listCount++;	
    }
    
    if(heapCount!=listCount) {
        printf("ERROR: There is a mismatch between the free blocks in the heap_list and the free_list.\n");
    }
}

/*This routine checks whether each block in the free list is present in the heap or not/is a valid block. */

static void 
in_heap(const void *p) {
    if(!(p <= mem_heap_hi() && p >= mem_heap_lo()))
    	printf("ERROR: Block out of heap boundaries.");
}


/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
  bool halloc, falloc;
  size_t hsize, fsize;

  checkheap(false);
  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));  
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOC(FTRP(bp));  

  if (hsize == 0) {
    printf("%p: end of heap\n", bp);
    return;
  }

  printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
      hsize, (halloc ? 'a' : 'f'), 
      fsize, (falloc ? 'a' : 'f'));
}


/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */