/* 
 * Simple, 32-bit and 64-bit clean allocator based on implicit free
 * lists, first fit placement, and boundary tag coalescing, as described
 * in the CS:APP2e text. Blocks must be aligned to doubleword (8 byte) 
 * boundaries. Minimum block size is 16 bytes. 
 * 
 * Parts based on book code found here: http://csapp.cs.cmu.edu/public/code.html
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


#define DEBUG 1	/* printf and flush, verbose, debug */
#define PRINTITALL 1	/* printf and flush, verbose, debug */

/* Macros based on book code mm.c */

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  //This equals 4096

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)                    //use 1 for allocated, 0 for free

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //use 1 for allocated, 0 for free
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, get the next and previous free blocks */
#define	NEXT_FREE(bp)	(char *)(bp)
#define PREV_FREE(bp)	(char *)(bp + WSIZE)


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
static char *heap_lastp = 0;  /* Pointer to last block */  
static void **fblocks;

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize, int index);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkheap(int verbose);
static void checkblock(void *bp);


static void addToList(int size, void *bp); //fb stands for Free Block
void deleteFromList(void *bp, int index);
void printlist(void);
static void printfreeblock(void *bp, int index);
static int findList(void *bp );

/* 
 * mm_init - Initialize the memory manager 
 * Based on book code mm.c
 */
/* $begin mminit */
int mm_init(void) 
{
	/* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(12*WSIZE)) == (void *)-1)
	return -1;
	
	fblocks = (void*)heap_listp;
    heap_listp += (8*WSIZE);
	
	fblocks[0] = 0x00000000; //later make this a NULL or something
	fblocks[1] = 0x00000000; //later make this a NULL or something
	fblocks[2] = 0x00000000; //later make this a NULL or something
	fblocks[3] = 0x00000000; //later make this a NULL or something
	fblocks[4] = 0x00000000; //later make this a NULL or something
	
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);
	
	/* Create array of lists to store addresses of free blocks by size */
	/*
	 * 			Let's store these free block sizes:
	 *			array[x]		0	1	2	3		4
	 *			double words:	2	3	4	5-8		9+
	 *			bytes:			16	24	32	40-64	72-infinity
	 */	
	 
    return 0;
}


/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 * Based on book code mm.c
 */
 
void *mm_malloc(size_t size) 
{
	checkheap(1);fflush(stdout);
	if(PRINTITALL){printf("Print list from beginning of mm_malloc:\n"); fflush(stdout);}
	printlist();
	if(PRINTITALL){printf("mm_malloc called for %i\n", size); fflush(stdout);}

    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *bp;     

	
    if (heap_listp == 0){
	mm_init();
    }
	
    /* Ignore spurious requests */
    if (size == 0)
	return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
	/* Maybe we could save space here */
	asize = 2*DSIZE;
    else
	asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 

	/* Calculate the appropriate list segment to use */
	int index = 0;
	if (asize > 71) {					//we need to check that asize isn't too big, either
		index = 4;
	}
	else if (asize > 39){
		index = 3;
	}
	else if (asize > 31){
		index = 2;
	}
	else if (asize > 23){
		index = 1;
	}
	else if (asize > 15){
		index = 0;
	}
	
    /* Search the seg list for a fit */
		bp = NULL;
		bp = find_fit(asize, index);
		if (bp != NULL) { 
		if(PRINTITALL){printf("Found a fit! Too bad it's %p\n", bp); fflush(stdout);}
		place(bp, asize);
		if(PRINTITALL){printf("mm_malloc returning %p\n", bp); fflush(stdout);}
		checkheap(0);fflush(stdout);
		return bp;
    }

    /* No fit found. Get more memory and place the block */
	
	extendsize = MAX(asize, CHUNKSIZE);
	checkheap(1);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
	return NULL;
	
	if(PRINTITALL){printf("Extended heap by %d\n", (extendsize)); fflush(stdout);}

	if(PRINTITALL){printf("Calling place (%p, %d)\n", bp, asize); fflush(stdout);}
	place(bp, asize); 
	
	if(PRINTITALL){
		printf("mm_malloc just finished place:\n"); 
		checkheap(0);
		fflush(stdout);
	}
	
	if(PRINTITALL){printf("mm_malloc ex. returning %p\n", bp); fflush(stdout);}
	printlist();
    return bp;
} 

/* 
 * mm_free - Free a block 
 * Based on book code mm.c
 */
void mm_free(void *bp)
{
	printf("CHECKHEAP mm_free \n");
	checkheap(1);	
	if(PRINTITALL){printf("mm_free called for bp: %p\n", bp); fflush(stdout);}
	printlist();
	
    if(bp == 0) 
	return;

    size_t size = GET_SIZE(HDRP(bp));
	
    if (heap_listp == 0){
	mm_init();
    }
	
	/* Set header info to free */
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	addToList(size, bp);
	if(DEBUG){printf("freed block %p\n", bp);}
    coalesce(bp);
}


/* stores the passed value in the header of the last item in fblocks[arrayIndex]*/
static void addToList(int size, void *bp)
{
	int index = 0;
	if (size > 71) {
		index = 4;
	}
	else if (size > 39){
		index = 3;
	}
	else if (size > 31){
		index = 2;
	}
	else if (size > 23){
		index = 1;
	}
	else if (size > 15){
		index = 0;
	}
	else {
		if(DEBUG){printf("FREE ERROR: No suitable list!\n");fflush(stdout);}
		coalesce(bp); //this might not be right
	}
	void *fb = fblocks[index];
	
		/* Check if list is empty */
		if (fb == 0x00000000)
		{
			PUT(PREV_FREE(bp), 0xDEADBEEF);
			PUT(NEXT_FREE(bp), 0xDEADBEEF);
			if(PRINTITALL){printf("Adding to list: %p\n", bp); fflush(stdout);}
			fblocks[index] = bp;
			return;
		}
	
	while(GET(NEXT_FREE(fb)) != 0xDEADBEEF)
	{
		if(DEBUG){printf("in the loop! %p | %p \n", fb, GET(NEXT_FREE(fb))); fflush(stdout);}
		fb = (void *)GET(NEXT_FREE(fb)); //this line increments to the next free block
	}
	if(DEBUG){printf("after loop! %p | %p \n", fb, GET(NEXT_FREE(fb))); fflush(stdout);}
	
	/* hold onto the last block */
	void* lastfree = fb;
	PUT(NEXT_FREE(fb), bp);
	
	if(DEBUG){printf("Next: %p Expected: %p fb: %p \n", GET(NEXT_FREE(fb)), bp, fb); fflush(stdout);}

	fb = (void *)GET(NEXT_FREE(fb)); //step forward
	PUT(PREV_FREE(fb), GET(lastfree));
	PUT(NEXT_FREE(fb), 0xDEADBEEF);
}


/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 * Based on book code mm.c
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
		return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
	    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
    }
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

/* Check. Here's the description from the assignment pdf:

Heap Consistency Checker
	Dynamic memory allocators are notoriously tricky beasts to program correctly and efficiently. They are
	difficult to program correctly because they involve a lot of untyped pointer manipulation. You will find it
	very helpful to write a heap checker that scans the heap and checks it for consistency.
	Some examples of what a heap checker might check are:
	
	• Is every block in the free list marked as free?
	• Are there any contiguous free blocks that somehow escaped coalescing?
	• Is every free block actually in the free list?
	• Do the pointers in the free list point to valid free blocks?
	• Do any allocated blocks overlap?
	• Do the pointers in a heap block point to valid heap addresses (as opposed to stack addresses)
	
	Your heap checker will consist of the function int mm check(void) in mm.c. It will check any invari-
	ants or consistency conditions you consider prudent. It returns a nonzero value if and only if your heap is
	consistent. You are not limited to the listed suggestions nor are you required to check all of them. You are
	encouraged to print out error messages when mm check fails.
	This consistency checker is for your own debugging during development. When you submit mm.c, make
	sure to comment out any calls to mm check as they will slow down your throughput. Style points will be
	given for your mm check function. Make sure to put in comments and document what you are checking.

 */
void mm_check(int verbose)  
{
	
}

/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
 
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)  
	return NULL;

	/* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
 
static void place(void *bp, size_t asize)
{
	if(DEBUG){printf("Place: BP1 is %p\n", bp);fflush(stdout);}
	checkheap(0);
    size_t csize = GET_SIZE(HDRP(bp));
	if ((csize - asize) >= (2*DSIZE)) { 
	
	if(DEBUG){printf("Place before delete bp\n");fflush(stdout);
	//printlist();
	}

	int index = findList(bp);
	if (index != -1)
	{
		if(PRINTITALL){printf("calling deleteFromList(%d)\n", index); fflush(stdout);}
		deleteFromList(bp, index);
	}
	
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
	if(DEBUG){printf("PLACE %u minus %u in list\n", csize, asize);fflush(stdout);}
	if(DEBUG){printf("Header says: %u\n", GET_SIZE(HDRP(bp)));fflush(stdout);}
	Assert(csize-asize == GET_SIZE(HDRP(bp)));
	if(DEBUG){printf("BP2 is %p\n", bp);fflush(stdout);}
	addToList(csize-asize, bp);
	
	//printlist();
    }
    else { 
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
	coalesce(bp);
    }
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize, int index){
	
	void *addr = NULL;
	void *free = fblocks[index]; //this and previous line used to be void *
	void *check;
	checkheap(1);fflush(stdout);
	if(DEBUG){printf("Find Fit\n"); fflush(stdout);}
	
	check = free;
	if (free != 0) 	/* Check if this free block exists */
		{
			int whatsup = GET_SIZE(HDRP(free));
			/* See if block is not the last free one and is large enough */
			if (GET(NEXT_FREE(free)) != 0xDEADBEEF && asize <= GET_SIZE(HDRP(free)) ) //DEADBEEF is our terminator
			{
				if(DEBUG){printf("Not first block in list: %p\n", free); fflush(stdout);}
				addr = free; //save the address we want to return
				if(DEBUG){printf("addr is: %p\n", addr);}
				deleteFromList(free, index);
				//fblocks[index] = (void *)GET(NEXT_FREE(free)); //make [index] point to former list item #2
				//PUT(PREV_FREE(free), 0xDEADBEEF);
			}
			else if (GET(NEXT_FREE(free)) == 0xDEADBEEF && asize <= GET_SIZE(HDRP(free)))
			{
				if(DEBUG){printf("First block in list: %p\n", free); fflush(stdout);}
				addr = free; //save the address we want to return
				if(DEBUG){printf("addr is: %p\n", addr); fflush(stdout);}
				fblocks[index] = 0x00000000;
			}
			else if(index < 4) //look in the next biggest size available
			{
				if(DEBUG){printf("calling find fit again\n"); fflush(stdout);}
				addr = find_fit(asize, index + 1);
			}
			else if (asize > GET_SIZE(HDRP(free))) return addr; //nothing big enough in the list :(
		return addr;
		}
		/* Check for block available in a bigger list */
		if(index < 4)
		{
			return find_fit(asize, index + 1);
		}
		return addr;
}

void deleteFromList(void *bp, int index)
{
	/* If is the only block in list*/
	if(GET(NEXT_FREE(bp)) == 0xDEADBEEF && GET(PREV_FREE(bp)) == 0xDEADBEEF)
	{	
		if(DEBUG){printf("Delete from list 1 %p\n", bp); fflush(stdout);}
		
		fblocks[index] = 0x00000000;
		if(DEBUG){printf("fblocks[%d]: %p\n", index, fblocks[index]); fflush(stdout);}
		return;
	}
	else if (GET_SIZE(HDRP(bp)) == 0) return;
	if(DEBUG){printf("Delete from list 2 %p\n", bp); fflush(stdout);}
	void* prev = (void *)GET(PREV_FREE(bp));
	if(DEBUG){printf("prev: %p\n", prev); fflush(stdout);}	
	if(DEBUG){printf("bp: %p\n", bp); fflush(stdout);}
	PUT(NEXT_FREE(prev), 0xDEADBEEF);

}

//static void *find_fit(size_t asize)
//{
/* $begin mmfirstfit */
    /* First fit search */
 //   void *bp;

//    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	/* If it's free and requested size fits, return bp*/
//	if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//	    return bp;
//	}
//    }
//    return NULL; /* No fit */
/* $end mmfirstfit */
//}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }

    printf("%p: header: [%p:%c] footer: [%p:%c]\n", bp, 
	hsize, (halloc ? 'a' : 'f'), 
	fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
	/* make sure block is aligned to doubleword */
    if ((size_t)bp % 8)
	printf("Error: %p is not doubleword aligned\n", bp);
	
	/* make sure header and footer match */
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: header does not match footer\n");
}

/* 
 * checkheap - Minimal check of the heap for consistency 
 */
void checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose==2)
	printf("Heap (%p):\n", heap_listp);

	/* Check for a bad prologue header */
    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	printf("Bad prologue header\n");
    checkblock(heap_listp);
	//int blocknum = 1; /*linear block order in list, used to test if blocks are the same*/
	/* Loop through memory until header is 0 */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		
		if (verbose) 
			printblock(bp);
		checkblock(bp);
		/* Check if two blocks next to each other are free */
		if(!(GET_ALLOC(HDRP(bp))) && !(GET_ALLOC(HDRP(bp+GET_SIZE(HDRP(bp))))))
			{
				printf("Double free block!\n");
			}
		if(!(GET_ALLOC(HDRP(bp))) && findList(bp) == -1)
			{
				printf("Block %p is not in the free list!\n", bp);
			}	
		/* 
		 * Loops through the list and checks for overlapping blocks
		 */ 
		char* bp2 = bp;
		if(PRINTITALL) {printf("Checking against  bp=[%p]:\n", bp);}
		
		for (bp2 = heap_listp; GET_SIZE(HDRP(bp2)) > 0; bp2= NEXT_BLKP(bp2)) {
			//printf("YYY bp = [%p] NEXT_BLKP(bp)= [%p] bp2= [%p] YYY\n", bp, NEXT_BLKP(bp), bp2); fflush(stdout);
			printf("                 bp2=[%p]\n", bp2);fflush(stdout);
			
			//size_t bp_size = GET_SIZE(HDRP(bp));
			char* bp_next = NEXT_BLKP(bp);
			//size_t bp_next_size = GET_SIZE(HDRP(bp_next));
			
			if (bp2 > bp && (char*)bp2 < (char*)NEXT_BLKP(bp)) 
			{ /* We have an overlapping block because:
				If bp2 > bp1 and bp2 < bp1.next, then bp2 must lie between the two 
				note that case bp1 = bp2 will be handled correctly because 
				comparison used is < and > not <= and >=
				*/
				if(PRINTITALL){printf("                 "); fflush(stdout);}
				printf("ERROR: CONFLICTING BLOCKS NOTICED:[%p] and [%p]\n", bp, bp2);	fflush(stdout);
				/*printf("ERROR: block [addr:%p size:%u nextblock:%p] and block: [addr:%p size:%08x]\n \
				have a block in the middle: [addr:%p] \n", 
				bp, bp_size, bp_next,
				bp_next, bp_next_size,
				bp2
				); fflush(stdout); */
				exit(1);
			} else {
				//printf("Phwew: Blocks addr:[%p] size[%u] and addr:[%p] do not overlap. Thank God.\n",
				//bp, bp_size, bp2); fflush(stdout);
				if (bp == bp2) { 
					if (PRINTITALL) 
						{ printf("                 Equality.\n"); } 
				} else
				if (PRINTITALL) printf("                 ");
				printf("no overlap\n");
			}
		
		} if(PRINTITALL) {printf("End of embedded loop\n");}
	}

	/* Check for a bad epilogue header */
    if (verbose)
	printblock(bp);
	/* make sure that header exists and allocated bit is zero*/
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) 
	printf("Bad epilogue header\n");
}


void printlist(void) {
	int i = 0;
	
	for (i=0; i<5; i++)
	{
		void* lp = fblocks[i];
		printf("LIST %d ------------\n", i); fflush(stdout);
		if (lp != 0) {
			printfreeblock(lp, i);
				while(lp != 0x00000000 && GET(NEXT_FREE(lp)) != 0xDEADBEEF){
				lp = (void *)GET(NEXT_FREE(lp));
				printfreeblock(lp, i);
			}
		}
		printf("End List ----------\n");
	}

}

static void printfreeblock(void *bp, int index) 
{
    size_t hsize, halloc, fsize, falloc, next, prev;

    //checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));
	next = GET(NEXT_FREE(bp));
	prev = GET(PREV_FREE(bp));

    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }
    printf("%p: header: [%p:%c] next: [%p] previous: [%p]  footer: [%p:%c] index: [%d]\n", bp, 
	hsize, (halloc ? 'a' : 'f'),
	GET(NEXT_FREE(bp)),
	GET(PREV_FREE(bp)),
	fsize, (falloc ? 'a' : 'f'),
	index
	);
	fflush(stdout);
}

static int findList(void *bp ) {
	int i;
	for (i = 5; i > -1 ; i--)
	{
		void* lp = fblocks[i];
		if (lp != 0) {
			if (bp == lp) { 		/* We have found a match */
				return i;
			}
			while(fblocks[i] != 0 && GET(NEXT_FREE(lp)) != 0xDEADBEEF){
				lp = (void *)GET(NEXT_FREE(lp));
				if (bp == lp) { 	/* We have found a match */
					return i;
				}
	}}}
	return -1;
}