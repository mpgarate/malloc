malloc
======

/* 
 * Simple, 32-bit and 64-bit clean allocator based on explicit free
 * lists, best fit placement, and boundary tag coalescing. 
 * Based from book code found here: http://csapp.cs.cmu.edu/public/code.html
 * 
 * An allocated block has a one word header and footer. Both of these contain
 * the size of the block and a bit to state whether allocated or free.
 *
 * A free block contains the same header and footer as an allocated block,
 * and additionally has two one-word sized blocks containing pointers to the next
 * and previous blocks in that list. 
 *
 * This free list is organized in reverse order of insertion. 
 * 
 */
