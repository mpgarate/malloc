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
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*  macros for free block pointers */
#define NEXT_FREE(bp)	(void *)(bp)
#define PREV_FREE(bp) 	(void *)(bp + WSIZE)

/* Set and retrieve free pointers */
#define SET(p, val)		(*(unsigned int *)(p) = val)
#define GET_PTR(p)		(void *)(p)


/* DEBUG: 1 if true, 0 if false. Will say more things if true.*/
#define DEBUG	0

/* Call heapchecker */
#define	HC {if(DEBUG)mm_check(0);fflush(stdout);}


/* Epic macros for SAY */
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
static void list_print(void);
/* Add to list, return 1 if success and 0 if fail */
static int list_add(void* bp); 
/* Delete to list, return 1 if success and 0 if fail */
/* NOTE: list_rm should not call coalesce */
static int list_rm(void* bp);
/* NOTE: We're skipping this for now. Combine two adjacent free blocks */
//static int combine(void* bp, void* bp2);


/* Our global variables */


/* TODO: update this value in extend_heap AND place AND anywhere else? */ 
static void* heap_lastp;	/* Point to last item in heap */
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
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);


	SAY0("DEBUG: mm_init: calling extend_heap\n");
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
		return -1;
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
	mm_check(0);
	size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    if (heap_listp == 0){
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

	SAY0("DEBUG: mm_init: calling find_fit\n");
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
	place(bp, asize);
	return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
	return NULL;
    place(bp, asize);
    return bp;
} 

/* 
 * mm_free - Free a block 
 * Based on book code mm.c
 */
void mm_free(void *bp)
{
    if(bp == 0) 
	return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
	mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
	
	/* TODO: addToList is called from within coalesce */
    coalesce(bp);
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
	if(!GET_ALLOC(FTRP(bp)) && GET(NEXT_FREE(bp)) != 0xDEADBEEF)
	{
		SAY1("DEBUG: coalesce: 0xDEADBEEF found; removing bp:[%p] from list",bp)
		list_rm(bp);
	}
	
	/* In each of these functions, check if the block-to-be-merged is in free list and remove it first */
    if (prev_alloc && next_alloc) {            /* Case 1 */
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
	mm_check(1);
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
	printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (verbose) 
	    printblock(bp);
	checkblock(bp);
    }

    if (verbose)
	printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	printf("Bad epilogue header\n");
	
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
	/* Add something to block here in the get_next field 
			that coalesce can check for to know that it came 
			from extend_heap. Something like 0xDEADBEEF
	*/
	
	SET(NEXT_FREE(bp), 0xDEADBEEF);
	SAY0("DEBUG: extend_heap: calling coalesce\n");
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}


/* Add to list, return 1 if success and 0 if fail
	
	Make sure to update the following variables:
	static void* free_p;		 Point to first free list item 
	static void* free_lastp;	 Point to last free list item

 */

static int list_add(void* bp)
{
	SAY0("DEBUG: list_add: entering\n");
	/* list add needs to handle the following cases:
		- The list has not yet been initialized
		- The list has been initialized
			- There is a free block that is too big (CALL place)
			- There is not a free block big enough
		*/
	SAY0("DEBUG: list_add: checking if list is empty\n");
	if (free_p == NULL)
	{
		SAY0("DEBUG: list_add: list was empty; creating list\n");
		free_p = bp;
		free_lastp = bp;
		SAY0("DEBUG: list_add: free_p and free_lastp set\n");
		SET(NEXT_FREE(free_p), 0x0);
		SET(PREV_FREE(free_p), 0x0);
		SAY0("DEBUG: list_add: returning 1! Hooray!\n");
		return 1;
	}
	else
	{
		SAY0("DEBUG: list_add: list wasn't empty; inserting into list");
		void* old_next = GET_PTR(NEXT_FREE(free_p));
		SET(NEXT_FREE(free_p), bp);
		SET(NEXT_FREE(bp), old_next);
		SET(PREV_FREE(bp), free_p);
		free_lastp = old_next;
		SAY0("DEBUG: list_add: returning 1! Hooray!\n");
		return 1;
	}
	SAY0("DEBUG: list_add: returning 0 :-(\n");
	return 0;
}
		/* This is the start of an alternate way that places a block at the end 
			//Copy the start pointer to a counter pointer 
		void* cp = free_p;
			//Loop through list until on the last free block
		while (NEXT_FREE(cp) != NULL)
		{
			cp = GET(NEXT_FREE(cp));
		}
		SET(NEXT_FREE(cp), bp);
		cp = GET(NEXT_FREE(cp));
		free_lastp = bp;
		SET(NEXT_FREE(free_p), NULL);
		SET(PREV_FREE(free_p), NULL);
		return 1;
		*/


/* Delete a block from the free list
*  return 1 if success and 0 if fail 
* NOTE: list_rm should not call coalesce */

static int list_rm(void* bp)
{	/* If list is empty */
	if (free_p == NULL)
	{
		return 1;
	}
	/* Insert at beginning of list */

	void* next = GET_PTR(NEXT_FREE(bp));
	void* prev = GET_PTR(PREV_FREE(bp));
	
	SET(PREV_FREE(next), GET(prev));
	SET(NEXT_FREE(prev), GET(next));
	
	SET(PREV_FREE(bp), NULL);
	SET(NEXT_FREE(bp), NULL);
	
	return 0;
}
/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
 
static void place(void *bp, size_t asize)

{
    size_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= (2*DSIZE)) { 
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
	
	/* Add this block slice to the free list */
	coalesce(bp);
    }
    else { 
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
    }
}


/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
 
 
 /* TODO: make this get fit from free list */
static void *find_fit(size_t asize)

{
    /* First fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
	    return bp;
	}
    }
    return NULL; /* No fit */
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }

	//SAY5("%p: header: [%p:%c] footer: [%p:%c]\n", bp, 
	//hsize, (halloc ? 'a' : 'f'), 
	//fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
	printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: header does not match footer\n");
}
