/* 
 * Simple, 32-bit and 64-bit clean allocator based on implicit free
 * lists, first fit placement, and boundary tag coalescing, as described
 * in the CS:APP2e text. Blocks must be aligned to doubleword (8 byte) 
 * boundaries. Minimum block size is 16 bytes. 
 * 		something
 * Book code found here: http://csapp.cs.cmu.edu/public/code.html
 */
 
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
	/* Team name */
	"Super Secret NSA Hacker Team",
	/* First member's full name */
	"Michael Garate",
	/* First member's NYU NetID */
	"mpgarate@nyu.edu",
	/* Second member's full name (leave blank if none) */
	"William Garate",
	/* Second member's email address (leave blank if none) */
	"bill.garate@nyu.edu"
};

/* Macros based on book code mm.c */

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((void *)(bp) - WSIZE)
#define FTRP(bp)       ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((void *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((void *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*  macros for free block pointers */
#define NEXT_FREE(bp)	((char *)(bp))
#define PREV_FREE(bp) 	((char *)(bp) + WSIZE)

/* Set and retrieve free pointers */
#define SET(p, val)		(*(unsigned int *)(p) = (val))
#define GET_PTR(p)		(void *)(p)

/*SOME MORE MACROS*/
#define BP_TO_SIZE(bp) (((unsigned int *)bp)[-1])
#define BP_TO_NEXT_FREE(bp) (((void**)bp)[0])
#define BP_TO_PREV_FREE(bp) (((void**)bp)[1])

/* DEBUG: 1 if true, 0 if false. Will say more things if true.*/
#define DEBUG	1

/* Call heapchecker */
#define	CHEAP() {if(DEBUG)mm_check(0);fflush(stdout);}
#define	PLIST() {if(DEBUG)printlist();;fflush(stdout);}


/* Epic macros for SAY */
#define SAY(fmt)		SAY0(fmt)
#define SAY0(fmt)		{if(DEBUG){printf(fmt); fflush(stdout);}}
#define SAY1(fmt,parm1)	{if(DEBUG){printf(fmt,parm1); fflush(stdout);}}
#define SAY2(fmt,parm1,parm2)	{if(DEBUG){printf(fmt,parm1,parm2); fflush(stdout);}}
#define SAY3(fmt,parm1,parm2,parm3)	{if(DEBUG){printf(fmt,parm1,parm2,parm3); fflush(stdout);}}
#define SAY4(fmt,parm1,parm2,parm3,parm4)	{if(DEBUG){printf(fmt,parm1,parm2,parm3,parm4); fflush(stdout);}}
#define SAY5(fmt,parm1,parm2,parm3,parm4,parm5)	{if(DEBUG){printf(fmt,parm1,parm2,parm3,parm4,parm5); fflush(stdout);}}
#define SAY6(fmt,parm1,parm2,parm3,parm4,parm5,parm6)	{if(DEBUG){printf(fmt,parm1,parm2,parm3,parm4,parm5,parm6); fflush(stdout);}}
#define SAY7(fmt,parm1,parm2,parm3,parm4,parm5,parm6,parm7)	{if(DEBUG){printf(fmt,parm1,parm2,parm3,parm4,parm5,parm6,parm7); fflush(stdout);}}
#define SAY8(fmt,parm1,parm2,parm3,parm4,parm5,parm6,parm7)	{if(DEBUG){printf(fmt,parm1,parm2,parm3,parm4,parm5,parm6,parm7); fflush(stdout);}}


#ifdef DEBUG
#define Assert(c) doAssert(c)
#else
#define Assert(c)
#endif

void doAssert(int c)
{
  if (c) return;
  int x = 0;
  x = x / x;
}


/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static char *heap_lastp = 0; /* pointer to last free block */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);

/* TODO: Functions we want to make */

void mm_check(int verbose);
/* Print our free block list(s) */
//tatic void list_print(void);
/* Add to list, return 1 if success and 0 if fail */
static int list_add(void* bp); 
/* Delete to list, return 1 if success and 0 if fail */
/* NOTE: list_rm should not call coalesce */
static int list_rm(void* bp);
/* NOTE: We're skipping this for now. Combine two adjacent free blocks */
//static int combine(void* bp, void* bp2);
/* Print the list */
static void printlist();
/* Check if block is in the list */
static int list_search(void* bp);

/* Our global variables */


/* TODO: update this value in extend_heap AND place AND anywhere else? */
static void* free_p;		/* Point to first free list item */
static void* free_lastp;	/* Point to last free list item*/

/* 
 * mm_init - Initialize the memory manager 
 * Based on book code mm.c
 */
int mm_init(void) 
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(8*WSIZE)) == (void *)-1)
		return -1;
		
	heap_lastp = heap_listp;
	free_p = NULL;
	free_lastp = NULL;
	// one block here is unused
    heap_listp += (4*WSIZE);
	
    PUT(heap_listp, 0);                          /* Alignment padding */
	SAY1("DEBUG: mm_init: heap_listp is %p\n", heap_listp);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	SAY1("DEBUG: mm_init: heap_listp + 4 is %p\n", heap_listp + (1*WSIZE));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	SAY1("DEBUG: mm_init: heap_listp + 8 is %p\n", heap_listp + (2*WSIZE));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
	SAY1("DEBUG: mm_init: heap_listp + 12 is %p\n", heap_listp + (3*WSIZE));
	SAY1("DEBUG: mm_init: heap_listp + 20 is %p\n", heap_listp + (5*WSIZE));
    heap_listp += (2*WSIZE);
	


	SAY0("DEBUG: mm_init: calling extend_heap\n");
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
	SAY("DEBUG: mm_init: check heap before extend\n");
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
		return -1;
	PLIST()
	SAY("DEBUG: mm_init: check heap after extend\n");
	CHEAP()
	SAY0("DEBUG: mm_init: returning\n");
    return 0;
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 * Based on book code mm.c
 */
void *mm_malloc(size_t size) 
{
	SAY1("DEBUG: mm_malloc: mm_malloc called for (%u)\n", size);
	SAY0("DEBUG: mm_malloc: calling mm_check(0)\n")
	PLIST()
	CHEAP()
	size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    if (heap_listp == 0){
		SAY("ERROR: mm_free: heap_listp is zero, calling mm_init again");
		mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
	return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
	asize = 2*DSIZE;
    else
	asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
	
	SAY0("DEBUG: mm_malloc: calling find_fit\n");
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
		SAY2("DEBUG: mm_malloc calling place(%p, %i)\n", bp, asize);
		list_rm(bp);
		place(bp, asize);
		SAY2("DEBUG: mm_malloc returning %p, size: %i\n", bp, GET_SIZE(HDRP(bp)));
		SAY("DEBUG: mm_malloc printing list before return:\n");
		PLIST()
		CHEAP()
		return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
		return NULL;
	SAY2("DEBUG: mm_malloc calling place(%p, %i)\n", bp, asize);
    place(bp, asize);
	SAY1("DEBUG: mm_malloc returning %p\n", bp);
	SAY("DEBUG: mm_malloc printing list:\n");
	PLIST()
	CHEAP()
    return bp;
} 

/* 
 * mm_free - Free a block 
 * Based on book code mm.c
 */
void mm_free(void *bp)
{
	SAY1("DEBUG: mm_free: called on [%p]\n", bp);
	SAY("DEBUG: mm_free: checking heap:\n");
	CHEAP()
    if(bp == 0) 
	return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
		SAY("ERROR: mm_free: heap_listp is zero, calling mm_init again\n");
		mm_init();
    }

	/* CASE: mm_free is passed a value that is outside the heap */
	if ((void*)heap_lastp < bp || (void*)heap_listp > bp) {
		/* You can't free it then! */
		return;
	}
	
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
	
	/* TODO: addToList is called from within coalesce */
    coalesce(bp);
	SAY("DEBUG: mm_free: removed block [%bp]\n");
	PLIST()
	CHEAP()
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 * Based on book code mm.c
 */
static void *coalesce(void *bp)
{
	SAY1("DEBUG: coalesce: entering with bp:[%p]\n",bp);
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	SAY0("DEBUG: coalesce: size_t prev_alloc set\n");
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	SAY0("DEBUG: coalesce: size_t next_alloc set\n");
    size_t size = GET_SIZE(HDRP(bp));
	SAY0("DEBUG: coalesce: locals declared\n");
	/* Check if free AND not from extend heap, and then remove from list. This lets us call it from both mm_free, extend_heap, and place */
	
	/* Get NEXT_FREE as an unsigned int so that we can compare it to DEADBEEF */
	if(GET_ALLOC(FTRP(bp)))
	{
		SAY1("DEBUG: coalesce: ERROR: tried to remove allocated block bp:[%p] from list\n",bp)
		list_rm(bp);
	}
	
	/* In each of these functions, check if the block-to-be-merged is in free list and remove it first */
    if (prev_alloc && next_alloc) {            /* Case 1 */
		SAY1("DEBUG: coalesce: [%p] does not need to be merged. Adding to list and returning\n", bp);
		list_add(bp);
		return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
	
	/* Remove the block to be merged from the list. It's ok if it isn't there. */
	list_rm(NEXT_BLKP(bp));
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
	list_rm(PREV_BLKP(bp));
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
	list_rm(NEXT_BLKP(bp));
	list_rm(PREV_BLKP(bp));
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
	    GET_SIZE(FTRP(NEXT_BLKP(bp)));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);
    }
	
	SAY1("DEBUG: coalesce: calling list_add(bp:[%p])\n", bp);
	
	/* add new block to the free list */
	list_add(bp);
	SAY1("DEBUG: coalesce: returning bp:[%p]\n", bp);
	SAY0("DEBUG: coalesce: calling mm_check after list_add\n");
	CHEAP()
	PLIST()
    return bp;
}

/*
 * mm_realloc - Naive implementation of realloc
 * Based on book code mm.c
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
	mm_free(ptr);
	return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
	return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
	return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

/* 
 * check - Based from book code
 */
void mm_check(int verbose)
{ 
    char *bp = heap_listp;

    if (verbose)
	SAY1("DEBUG: mm_check: Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	{
		SAY0("DEBUG: mm_check: ERROR: Bad prologue header\n");
		Assert(0==1);
	}
    checkblock(heap_listp);
	//SAY0("DEBUG: mm_check: checking for blocks that have escaped coalescing\n");
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		//SAY1("DEBUG: mm_check: In the loop with bp:[%p]\n", bp);
		if (verbose) 
			printblock(bp);
		checkblock(bp);
		
		/* Check if two blocks next to each other are free */
		if(!(GET_ALLOC(HDRP(bp))) && !(GET_ALLOC(HDRP(bp+GET_SIZE(HDRP(bp))))))
			{
				SAY0("DEBUG: mm_check: Double free blocks:\n");
				printblock(bp);
				printblock(bp+GET_SIZE(HDRP(bp)));
				Assert(0==1);
			}
    }
	//SAY0("DEBUG: mm_check: out of the loop\n");

    if (verbose)
	printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	SAY0("DEBUG: mm_check: ERROR: Bad epilogue header\n");
	
	void *fp = free_p;
    for (fp = free_p; fp != NULL; fp = BP_TO_NEXT_FREE(fp)) {
	
		/* Check for free blocks not in the list and allocated blocks in the list */
		if(GET_ALLOC(HDRP(fp)) == list_search(fp))
		{
			if (GET_ALLOC(HDRP(fp)) && list_search(fp))
			{
				SAY1("ERROR: mm_check: allocated block %p in list\n", fp);
				SAY2("DEBUG: mm_check: allocated block in free list. GET_ALLOC is %i, list_search is %i\n", (GET_ALLOC(HDRP(fp))), list_search(fp));
				printblock(fp);
				Assert(!GET_ALLOC(HDRP(fp)));
			}
			else
			{
				SAY1("ERROR: mm_check: free block %p not in list\n", fp);
				SAY2("DEBUG: mm_check: GET_ALLOC is %i, list_search is %i\n", (GET_ALLOC(HDRP(fp))), list_search(fp));
				Assert(0==1);
			}
		}
	
	
		}
	
}

/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
 
static void *extend_heap(size_t words)
{
	SAY0("DEBUG: extend_heap: entering\n");
    char *bp;
    size_t size;
	
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)  
		return NULL;
	SAY1("DEBUG: extend_heap: mem_sbrk(%u) has returned successfully\n", size);
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	SAY0("DEBUG: extend_heap: free block initialized; epilogue set\n");
	SAY0("DEBUG: extend_heap: calling coalesce\n");
    /* Coalesce if the previous block was free */
	heap_lastp = bp;
	SAY1("DEBUG: extend_heap: calling list_add %p\n", bp);
	//list_add(bp); /* This prevents list_rm from breaking in this case */
	SAY1("DEBUG: extend_heap: calling coalesce(%p)\n", bp);
	bp = coalesce(bp);
	
	SAY("DEBUG: extend_heap: calling PLIST()\n");
	PLIST()
	SAY("DEBUG: extend_heap: calling CHEAP()\n");
	CHEAP()
	
	return bp;
}




/* Add to list, return 1 if success and 0 if fail
	
	Make sure to update the following variables:
	static void* free_p;		 Point to first free list item 
	static void* free_lastp;	 Point to last free list item

 */

/* Add to list, return 1 if success and 0 if fail
	
	Make sure to update the following variables:
	static void* free_p;		 Point to first free list item 
	static void* free_lastp;	 Point to last free list item
static int list_add(void* bp)
*/
static int list_add(void* bp)
{
	SAY("DEBUG: list_add: State of list before list_add:\n");
	PLIST()
	SAY2("DEBUG: list_add: adding %p, alloc: %i\n", bp, GET_ALLOC(HDRP(bp)));
	Assert(!GET_ALLOC(HDRP(bp)));
	
	/* If list is empty */
	if (free_p == NULL)
	{
		SAY0("DEBUG: list_add: nothing in list yet\n");
		/* Create list */
		free_p = bp;
		free_lastp = bp; /* last free block */
		
		/* If the list is empty, the block's next and previous pointers should be NULL */
		
		BP_TO_PREV_FREE(bp) = NULL; 
		BP_TO_NEXT_FREE(bp) = NULL;
		SAY3("DEBUG: list_add: bp: %p BP_TO_PREV_FREE(bp):%p BP_TO_NEXT_FREE(bp): %p\n", bp, BP_TO_PREV_FREE(bp), BP_TO_NEXT_FREE(bp));
		SAY("DEBUG: list_add: State of list after list_add:\n");
		PLIST()
		return 1;
	}
	else //if (free_p == bp)
	{
		/*list wasn't empty; inserting into the beginning of the list */
		SAY0("DEBUG: list_add: list wasn't empty, inserting at beginning\n");
		SAY2("DEBUG: list_add: free_p: [%p], bp: [%p] \n", free_p, bp);
		void* old_first = free_p;
		BP_TO_PREV_FREE(bp) = NULL;
		BP_TO_NEXT_FREE(bp) = old_first;
		BP_TO_PREV_FREE(old_first) = bp;
		free_p = bp;
		SAY3("DEBUG: list_add: bp: %p BP_TO_PREV_FREE(bp):%p BP_TO_NEXT_FREE(bp): %p\n", bp, BP_TO_PREV_FREE(bp), BP_TO_NEXT_FREE(bp));
		SAY("DEBUG: list_add: State of list after list_add:\n");
		PLIST()
		return 1;
	}
return 0;
}


/* Delete a block from the free list
*  return 1 if success and 0 if fail 
* NOTE: list_rm should not call coalesce */

static int list_rm(void* bp)
{	/* If list is empty */
	SAY1("DEBUG: list_rm: removing %p\n", bp);
	if (free_p == NULL)
	{
		SAY1("DEBUG: list_rm: free_p was null, returning fail %p\n", free_p);
		return 0;
	}
	
	if(GET_ALLOC(HDRP(bp))) {
		SAY1("DEBUG: list_rm: Someone's trying to remove an allocated block from the free list %p\n", bp);
		return 1; 
	}
	
	if (free_p == NULL && free_lastp == NULL)
	{ /* thge list is empty*/
		SAY0("DEBUG: list_rm: the list is empty\n");
		return 1;
	}
	SAY3("DEBUG: list_rm: free_p: [%p] bp: [%p] free_lastp: [%p]\n", free_p, bp, free_lastp);
	if (free_p == bp && free_lastp == bp) 
	{ /* it's the only one in the list */
		free_p = NULL;
		free_lastp = NULL;
		return 1;
	}
	SAY("DEBUG: list_rm: not the only one in the list\n");
	/* else if it's first one in list	*/
	if (free_p == bp)
	{
		void* bp_of_next = BP_TO_NEXT_FREE(bp);
		SAY2("DEBUG: list_rm: %p comes out to %p\n", bp, PREV_FREE(bp_of_next));
		free_p = bp_of_next;
		BP_TO_PREV_FREE(bp_of_next) = NULL;
		return 1;
	}
	/* else if it's the last one in the list */
	if (free_lastp == bp)
	{
		void* bp_of_prev = BP_TO_PREV_FREE(bp);
		free_lastp = bp_of_prev;
		BP_TO_NEXT_FREE(bp_of_prev) = NULL;
		return 1;
	}
	/* else it's in the middle */
 	
	void* bp_of_prev = BP_TO_PREV_FREE(bp);
	void* bp_of_next = BP_TO_NEXT_FREE(bp);
	SAY3("DEBUG: list_rm: %p %p %p\n", bp, bp_of_prev, bp_of_next);
	BP_TO_PREV_FREE(bp_of_next) = BP_TO_PREV_FREE(bp);
	SAY("DEBUG: list_rm: Made it here 7\n");
	BP_TO_NEXT_FREE(bp_of_prev) = BP_TO_NEXT_FREE(bp);
	SAY("DEBUG: list_rm: Made it here 8\n");
	

	return 0;
}
/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
 
static void place(void *bp, size_t asize)

{
    size_t csize = GET_SIZE(HDRP(bp));

	SAY1("DEBUG: placing %p\n", bp);
	
    if ((csize - asize) >= (2*DSIZE)) {
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	SAY2("DEBUG: place just made block [%p], size: %i\n", bp, GET_SIZE(HDRP(bp)));
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
	SAY2("DEBUG: place just split off block [%p], size: %i\n", bp, GET_SIZE(HDRP(bp)));
	
	/* Add this block slice to the free list */
	/* Update heap_lastp to point to last block after extend_heap call */
	if (bp > heap_lastp)
		{
			heap_lastp = bp;
			SAY1("DEBUG: place: calling coalesce on %p\n", bp);
			coalesce(bp);
		}
	}
    else { 
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
    }
}


/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
 
 
 
    /* First fit search */
 /*   void *bp;
    for (bp = NEXT_FREE(free_p); bp != NULL; bp = GET(NEXT_FREE(bp))) {
		if (asize <= GET_SIZE(HDRP(bp))) {
			SAY4("DEBUG: find_fit: found for asize: %i, %p: %i, %i\n", asize, bp, GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));
			if (list_rm(bp)) SAY("We removed it\n");
			return bp;
		}
    }
    return NULL; // no fit
	
	*/
 
 
 /* TODO: make this get fit from free list */
static void *find_fit(size_t asize)
{
 /* Best fit search */
	
	/*CASE: list is empty, so no fit, DUH */
	if(free_p == NULL) 
	{
		SAY("DEBUG: find_fit: List is empty, returning\n");
		return 0;
	}	
	
	/* begin search at the beginning of the list */
    void *bp = free_p;
	
	void *best = NULL; /* return NULL if none found */
	size_t best_size = (size_t)-1;	/* Gets the max size of size_t */
	size_t curr_size;	/* Gets the max size of size_t */
	SAY1("DEBUG: find_fit: bp is %p\n", bp);
	while(bp != NULL)
	{
		curr_size = GET_SIZE(HDRP(bp));
		
		SAY("DEBUG: find_fit: List is not empty\n");
		if (asize == curr_size)
		{
			SAY("DEBUG: find_fit: equal sizes, this is the best fit\n");
			return bp;		/* If they are equal, this fit is the best */
		}
		else if(asize < curr_size && curr_size < best_size)
		{
			best_size = curr_size;
			best = bp;
		}
		bp = BP_TO_NEXT_FREE(bp);
	}
	
	SAY2("DEBUG: find_fit: after loop, %p is best, size is: %i\n", best, best_size);
	return best;
}


static int list_search(void* bp)
{
	//SAY0("DEBUG: list_search: entering\n");
	
	/* Check if list is uninitialized */
	if (free_p == NULL) return 0; /* Not in the list */
	
	
	void * lp = free_p;
	
	//SAY2("DEBUG: list_search: lp is %p, bp is %p \n", lp, bp);
	
	if (bp == NULL)
	{
		//SAY1("DEBUG: list_search: lp was null %p \n", lp);
		return 0; /* not in the list */
	}
	
	if (bp == lp) { 		/* We have found a match */
		//SAY0("DEBUG: list_search: we have found a match | returning\n")
		return 1;
	}
	
	//SAY1("DEBUG: loop: lpget is %p \n", NEXT_FREE(lp));
	while(BP_TO_NEXT_FREE(bp) != NULL)
	{
		bp = BP_TO_NEXT_FREE(bp);
		//SAY1("DEBUG: list_search: looping, lp is %p \n", lp);
		lp = bp;
		if (bp == lp) { 	/* We have found a match */
			return 1;
		}
	}
	return 0;
	}

static void printlist()
{
	void *bp = free_p;
	SAY("DEBUG: ------------- Printing Free List -------------\n");
	SAY2("free_p: [%p] free_lastp: [%p]\n", free_p, free_lastp);
    for (bp = free_p; bp != NULL; bp = BP_TO_NEXT_FREE(bp)) {
			//SAY1("DEBUG: printlist: in the loop and bp is [%p]\n", bp);
			printblock(bp);
		}
	SAY("DEBUG: ------------- End Free List Print ------------\n");
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;
	void* next;
	void* prev;
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp)); 
	next = BP_TO_NEXT_FREE(bp);
	prev = BP_TO_PREV_FREE(bp);

    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }

	SAY7("DEBUG: ---- | %p: header: [%i:%c] footer: [%i:%c]\nDEBUG:      | n:%p p:%p\n", bp, 
	hsize, (halloc ? 'a' : 'f'), 
	fsize, (falloc ? 'a' : 'f'),
	next,
	prev);
}

static void checkblock(void *bp) 
{
	//SAY1("DEBUG: checkblock: entering checkblock(%p)\n", bp);
    if ((size_t)bp % 8)
	{
		printf("Error: %p is not doubleword aligned\n", bp);
		Assert(0==1);
	}
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
	{
		printf("Error: header does not match footer\n");
		Assert(0==1);
	}
	//SAY1("DEBUG: checkblock: exiting checkblock(%p)\n", bp);
}