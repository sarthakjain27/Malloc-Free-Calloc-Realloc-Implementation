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
#define ALIGNMENT 16
#define MAXLIST 9
#define WSIZE 4
#define is_free 0x0
#define is_alloc 0x1
#define prev_alloc 0x2
#define MIN_FREE_SIZE 16

/* Global Variables */
static char *heap_list_pointer = 0;
static char *heap_base_address=0;
static char *first_seglist=0;
static char *last_seglist=0;
static char *epilogue=0;
typedef uint64_t word_t;

static word_t PACK(size_t size,int prev,int curr)
{
    return ((size) | (prev) | (curr));   
}

static void PUT(char *p,word_t val)
{
       (unsigned int *)(p) = val;
}

static char* head_pointer(void *bp)
{
    return ((char *)(bp)-WSIZE);   
}

static char* foot_pointer(void *bp)
{
    return ((char *)(bp) + GET_SIZE(head_pointer(bp)) - DSIZE);   
}
/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

static word_t GET(void *p)
{
    return (*(unsigned int *)(p));   
}

static size_t GET_SIZE(void *p)
{
    return (GET(p) & ~0x7);   
}

static size_t GET_ALLOC(void *p)
{
    return (GET(p) & 0x1);   
}

static size_t GET_PREV_ALLOC(void *p)
{
    return (GET(p) & 0x2);   
}

static void *next_block_address(void *bp)
{
    return ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));    
}

static void *prev_bloc_address(void *bp)
{
    return ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)));   
}

static size_t find_list(size_t asize)
{
    if (asize == MIN_FREE_SIZE)
        return 0;
    else if (asize < (1 << 1) * MIN_FREE_SIZE)
        return 1;
    else if (asize < (1 << 2) * MIN_FREE_SIZE)
        return 2;
    else if (asize < (1 << 3) * MIN_FREE_SIZE)
        return 3;
    else if (asize < (1 << 4) * MIN_FREE_SIZE)
        return 4;
    else if (asize < (1 << 5) * MIN_FREE_SIZE)
        return 5;
    else if (asize < (1 << 6) * MIN_FREE_SIZE)
        return 6;
    else if (asize < (1 << 7) * MIN_FREE_SIZE)
        return 7;
    else if (asize < (1 << 8) * MIN_FREE_SIZE)
        return 8;
    else 
        return 9;
}

static void* NEXT_PTR(void *bp)
{
    return bp;   
}

static void* PREV_PTR(void *bp)
{
    return ((char *)bp + WSIZE);   
}

static void FREE_PREV(void *bp)
{
    PUT(bp, (GET(bp) & (~prev_alloc)));   
}

static void* NEXT_FREE_BLKP(void *bp)
{
    return (base + (*(unsigned int *)(NEXT_PTR(bp))));   
}

static void* PREV_FREE_BLKP(void *bp)
{
    return (base + (*(unsigned int *)(PREV_PTR(bp))));   
}

static inline void addBlock(void *bp, size_t index)
{
    PUT(NEXT_PTR(bp), GET(NEXT_PTR(first_list + index * DSIZE)));
    PUT(PREV_PTR(bp), GET(PREV_PTR(NEXT_FREE_BLKP(bp))));

    PUT(NEXT_PTR(first_list + index * DSIZE), (long)bp - (long)base);
    PUT(PREV_PTR(NEXT_FREE_BLKP(bp)), (long)bp - (long)base);
}

static inline void delBlock(void *bp)
{
    PUT(PREV_PTR(NEXT_FREE_BLKP(bp)), GET(PREV_PTR(bp)));
    PUT(NEXT_PTR(PREV_FREE_BLKP(bp)), GET(NEXT_PTR(bp)));
}

static void *coalesce(void *bp)
{
    /* Find bp's prev and next block is allocate or not */
    size_t prev_alloc = GET_PREV_ALLOC(head_pointer(bp));
    size_t next_alloc = GET_ALLOC(head_pointer(next_block_address(bp)));
    
    /* Initialize */
    size_t size = GET_SIZE(head_pointer(bp));   // bp's size
    size_t index;                       // index used to find correct seg list
    
    /* 
     * Case 1 - both prev and next block is allocate 
     *   add bp into correct seg list
     *   update bp's next block's prev_alloc bit to IS_FREE
     */
    if (prev_alloc && next_alloc) {
        index = find_list(size);
        addBlock(bp, index);
        FREE_PREV(head_pointer(next_block_address(bp)));
        return bp;
    }
    
    /* 
     * Case 2 - only prev block is allocate 
     *   find new size for new free block and correct seg list index
     *   delete next block from its seg list
     *   merge bp and next block together 
     *   update bp's prev_alloc bit to PREV_ALLOC
     *   add new free block into seglist
     */
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(head_pointer(next_block_address(bp)));
        index = find_list(size);
        
        delBlock(next_block_address(bp));
        
        PUT(head_pointer(bp), PACK(size,prev_alloc,0));
        PUT(foot_pointer(bp), size);
        
        addBlock(bp, index);
        return bp;
    }
    
    /* 
     * Case 3 - only next block is allocate 
     *   find new size for new free block and correct seg list index
     *   find bp's prev block's prev_alloc bit
     *   delete prev block from its seg list
     *   merge bp and prev block together 
     *   update bp's prev_alloc bit to bp's prev block's prev_alloc bit
     *   add new free block into seglist
     */
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(head_pointer(prev_block_address(bp)));
        index = find_list(size);
        
        size_t prev_prev_alloc = GET_PREV_ALLOC(head_pointer(prev_block_address(bp)));
        
        delBlock(prev_block_address(bp));
        
        PUT(foot_pointer(bp), size);
        PUT(head_pointer(prev_block_address(bp)),PACK(size, prev_prev_alloc, is_free));
        FREE_PREV(head_pointer(next_block_address(prev_block_address(bp))));
        
        addBlock(prev_block_address(bp), index);
        return (prev_block_address(bp));
    }
    
    /* 
     * Case 4 - both prev and next block is free 
     *   find new size for new free block and correct seg list index
     *   find bp's prev block's prev_alloc bit
     *   delete prev and next block from its seg list
     *   merge bp, prev and next block together 
     *   update bp's prev_alloc bit to bp's prev block's prev_alloc bit
     *   add new free block into seglist
     */
    else {
        size += GET_SIZE(head_pointer(prev_block_address(bp)))+GET_SIZE(foot_pointer(next_block_address(bp)));
        index = find_list(size);
        
        size_t prev_prev_alloc = GET_PREV_ALLOC(head_pointer(prev_block_address(bp)));
        
        delBlock(next_block_address(bp));
        delBlock(prev_block_address(bp));
        
        PUT(head_pointer(prev_block_address(bp)),PACK(size, prev_prev_alloc, is_free));
        PUT(foot_pointer(next_block_address(bp)),size);
        
        addBlock(prev_block_address(bp), index);
        return (prev_block_address(bp));
    }
}

/*
 * extend_heap - Extend heap size and return a pointer to the extend memory
 *
 *  If cannot extend heap, return NULL.
 */
static void *extend_heap(size_t word)
{
    char *bp;
    size_t size;
    size_t is_prev_alloc;

    /* Allocate to maintain alignment requests */
    size = (word % 2) ? (word + 1) * WSIZE : word * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1) {
        printf("mem_sbrk fails\n");
        return NULL;
    }

    /* Find bp's prev_alloc info to set extended block's prev_alloc */
    is_prev_alloc = GET_PREV_ALLOC(head_pointer(bp));

    /* Initialize the extended block header and footer */
    PUT(head_pointer(bp), PACK(size, is_prev_alloc, is_free));
    PUT(foot_pointer(bp), PACK(size, is_free, is_free));

    /* Initialize the epilogue header */
    epilogue = head_pointer(next_block_address(bp));
    PUT(head_pointer(next_block_address(bp)), PACK(0, prev_alloc,is_alloc));

    return coalesce(bp);
}

/*
 * Initialize: return false on error, true on success.
 */
bool mm_init(void) {
    /* Create initial empty heap */
    size_t init_size = (2 * (MAXLIST + 1) + 4) * WSIZE;
    size_t prologue_size = (2 * (MAXLIST + 1) + 2) * WSIZE;
    if ((heap_list_pointer = mem_sbrk(init_size)) == (void *)-1) {
        printf("mem_sbrk fails\n");
        return false;
    }

    /* Get heap start address and first/last seglist start part */
    heap_base_address = heap_list_pointer;
    first_seglist = heap_list_pointer + DSIZE;
    last_seglist = first_seglist + MAXLIST * DSIZE;
    epilogue = heap_list_pointer + (2 * (MAXLIST + 1) + 3) * WSIZE;
    
    /* Padding part (4 bytes) for alignment */
    PUT(heap_list_pointer, PACK(0, is_free, is_free));

    /* Prologue part */
    heap_list_pointer = heap_list_pointer + WSIZE;    // move to prologue header
    PUT(heap_list_pointer, PACK(prologue_size, prev_aloc,is_alloc));
    heap_list_pointer = heap_list_pointer + WSIZE; 
    PUT(foot_pointer(heap_list_pointer), PACK(prologue_size, prev_alloc,is_alloc));

    /* 
     * Put each seglist's start part in the following space,
     * and store the offset value for later query use
     */
    size_t offset;
    for (size_t i = 0; i <= MAXLIST; i++) {
        offset = (i + 1) * DSIZE;
        PUT(base + offset, offset);
        PUT(base + (offset + WSIZE), offset);
    }

    /* Epilogue part */
    PUT(foot_pointer(heap_list_pointer) + WSIZE, PACK(0, prev_alloc,is_alloc));

    /* Extend the empty heap with a block of INITSIZE bytes */
    if (extend_heap(INITSIZE/WSIZE) == NULL) {
        return false;
    }
    
    return true;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    return NULL;
}

/*
 * free
 */
void free (void *ptr) {
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
    return NULL;
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

