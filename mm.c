/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 *
 * You may use mm-baseline.c as a starting point instead of building
 * your own solution from scratch (which may be a good idea).
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want debugging output, uncomment the following. Be sure not
 * to have debugging enabled in your final submission
 */
// #define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__) 
#define dbg_checkheap(...) mm_checkheap(__VA_ARGS__)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#define dbg_requires(...)
#define dbg_ensures(...)
#define dbg_checkheap(...)
#define dbg_printheap(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* What is the correct alignment? */
/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

typedef struct block hblock;

struct block {
    size_t header;
    hblock *succ_p;
    hblock *pred_p;
    size_t footer;
};

#define ALIGNMENT 2*dsize;

static size_t ALIGN(size_t x) {
    return ((x + (ALIGNMENT - 1)) & ~0XF);
}

#define HSIZE      ALIGN(sizeof(hblock)) /* The minimum size of a block */

*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, size_t alloc)
{
    return ((size) | (alloc));
}

static size_t GET(hblock *p)
{
    return (*(size_t *)(p));   
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t GET_SIZE(hblock *block)
{
    return (GET(p) & ~0x1);
}

static hblock* HDRP(hblock *bp)
{
    return ((char *)(bp));   
}

static hblock* FTRP(hblock *bp)
{
    return ((char *)(bp) + GET_SIZE((bp));   
}


static hblock *NEXT_BLKP(hblock *bp)
{
    return ((char *)(bp) + GET_SIZE(bp));    
}

static hblock *PREV_BLKP(hblock *bp)
{
    return ((char *)(bp) - GET_SIZE(bp));   
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool GET_ALLOC(hblock *block)
{
    return (GET(p) & 0x1);
}

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/* Private global variables */
static hblock *p;         /* Points to the starting block at all times */

/*
 * Initialize: return false on error, true on success.
 */
bool mm_init(void) {
    /* Attempt to create an empty heap with just a prologue 
     * at the beginning 
     */
    if (mem_sbrk(HSIZE) == (void *)-1)
        return false;
 
    p = (hblock *) mem_heap_lo();

    /* Set the block size of the header, and make it point to itself */
    p->header = HSIZE | 0x1; // The prologue will be the only allocated block of HSIZE
    p->footer = p->header;
    p->succ_p = p;
    p->pred_p = p;

    return true;
}

/*
 * Attempts to find the right size of free block in the free list. The free list is 
 * implemented as an explicit list, which is simply a doubly linked list.
 */
static void *find_free(size_t size)
{
    /* Iterate over each of the blocks in the free list until a block
     * of the appropriate size is found. If the block wraps back around
     * to the prologue, then a free block wasn't found.
     */ 
    hblock *bp;
    for(bp = p->succ_p; bp != p && bp->header < size; bp = bp->succ_p) {
    }

    /* If the free list wrapped back around, then there were no free spots */
    if (bp == p)
        return NULL;
    else
    /* Otherwise return the pointer to the free block */
        return bp; 
}

static void remove_free_block(hblock *bp)
{
    bp->pred_p->succ_p = bp->succ_p;
    bp->succ_p->pred_p = bp->pred_p;
}

static void *coalesce(hblock *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(bp);

    /* If the next block is free, then coalesce the current
     * block (bp) and the next block */
    if (prev_alloc && !next_alloc) {           /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        bp->header = size | 0x0;
        bp->footer = bp->header;
    }

    /* If the previous block is free, then coalesce the current
     * block (bp) and the previous block */
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        bp->footer = size | 0x0;
        bp->pred_p->header = size | 0x0;
    }

    
    else if (!prev_alloc && !next_alloc) {
        size += GET_SIZE(FTRP(PREV_BLKP(bp))) + 
                GET_SIZE(HDRP(NEXT_BLKP(bp)));
        bp->pred_p->header = size | 0x0;
        bp->succ_p->footer = size | 0x0;
    }

    return bp;
}

static void place(hblock *bp, size_t newsize)
{  
    size_t csize = GET_SIZE(bp->header);

    if ((csize - newsize) >= HSIZE) {
        bp->header = newsize | 0x1;
        bp->footer = bp->header;
        remove_free_block(bp);
        bp = (hblock *) NEXT_BLKP(bp);
        bp->header = (csize-newsize) | 0x0;
        bp->footer = bp->header; 
        coalesce(bp);
    }


    else {
        bp->header = csize | 0x1;
        bp->footer = bp->header;
        remove_free_block(bp);
    }
    /* Set the allocated bit of the header and footer */
    //bp->header |= 0x1;
    //bp->footer = bp->header;

    /* Set up the link for the free list */  
    //remove_free_block(bp);

    return;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    /* Ignore spurious requests */
    if (size < 1)
        return NULL;

    /* The size of the new block is equal to the size of the header, plus
     * the size of the payload
     */
    int newsize = ALIGN(size + HSIZE);
    
    /* Try to find a free block that is large enough */
    hblock *bp = (hblock *) find_free(newsize);
   
    /* If a large enough free block was not found, then coalesce
     * the existing free blocks */ 

    /* After coalsecing, if a large enough free block cannot be found, then
     * extend the heap with a free block */
    if (bp == NULL) { 
        bp = mem_sbrk(newsize);
        if ((long)(bp) == -1)
            return NULL;
        else {
            bp->header = newsize | 0x1;
            bp->footer = bp->header;
        }
    }
    else {
        /* Otherwise, a free block of the appropriate size was found. Place
         * the block */
        place(bp, newsize); 
    }

    // Return a pointer to the payload
    return (char *) bp + HSIZE;
}

/*
 * free
 */
void free (void *ptr) {
    /* Get the pointer to the allocated block */
    hblock *bp = ptr - HSIZE; 
    //hblock *cbp; // stores a pointer to the coalesced block

    //cbp = (hblock *) coalesce(bp);

    /* Modify the allocated bit for the header and footer */ 
    bp->header &= ~1;
    bp->footer = bp->header;

    /* Set up the doubly linked explicit free list */
    bp->succ_p = p->succ_p;
    bp->pred_p = p;
    p->succ_p = bp;
    bp->succ_p->pred_p = bp;
   
    return;
}

/*
 * realloc
 */
void *realloc(void *oldptr, size_t size) {
    return NULL;
}

/*
 * calloc
 * This function is not tested by mdriver
 */
void *calloc (size_t nmemb, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    // Multiplication overflowed
    return NULL;
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);
    return bp;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void *p) {
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines,                       *
 * except if you're replacing the entire code in this file                   *
 * with the entire code contained in mm-baseline.c!                          *
 *                                                                           *
 * 54 68 69 73 20 69 73 20 61 20 73 75 62 6c 69 6d 69 6e 61 6c               *
 *                                                                           *
 * 20 6d 65 73 73 61 67 69 6e 67 20 65 6e 63 6f 75 72 61 67 69               *
 * 6e 67 20 79 6f 75 20 74 6f 20 73 74 61 72 74 20 77 69 74 68               *
 * 20 74 68 65 20 63 6f 64 65 20 69 6e 20 6d 6d 2d 62 61 73 65               *
 *                                                                           *
 * 6c 69 6e 65 2e 63 21 20 2d 44 72 2e 20 45 76 69 6c 0a de ad               *
 * be ef 0a 0a 0a 0a 0a 0a 0a 0a 0a 0a 0a 0a 0a 0a 0a 0a 0a 0a               *
 *                                                                           *
 *****************************************************************************
 */

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno) {
    return true;
}
