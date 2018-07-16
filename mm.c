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

/* What is the correct ment? */
#define ALIGNMENT 16
#define MAXLIST 9
#define WSIZE 4
#define is_free 0x0
#define is_alloc 0x1
#define prev_alloc 0x2
#define MIN_ALLOC_SIZE 12
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

static void PUT(void *p,word_t val)
{
       (unsigned int *)(p) = val;
}

static void* head_pointer(void *bp)
{
    return ((char *)(bp)-WSIZE);   
}

static void* foot_pointer(void *bp)
{
    return ((char *)(bp) + GET_SIZE(head_pointer(bp)) - DSIZE);   
}
/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

static size_t GET(void *p)
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
    return (heap_base_address + (*(unsigned int *)(NEXT_PTR(bp))));   
}

static void* PREV_FREE_BLKP(void *bp)
{
    return (heap_base_address + (*(unsigned int *)(PREV_PTR(bp))));   
}

static inline void addBlock(void *bp, size_t index)
{
    PUT(NEXT_PTR(bp), GET(NEXT_PTR(first_list + index * DSIZE)));
    PUT(PREV_PTR(bp), GET(PREV_PTR(NEXT_FREE_BLKP(bp))));

    PUT(NEXT_PTR(first_list + index * DSIZE), (long)bp - (long)heap_base_address);
    PUT(PREV_PTR(NEXT_FREE_BLKP(bp)), (long)bp - (long)heap_base_address);
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
        PUT(heap_base_address + offset, offset);
        PUT(heap_base_address + (offset + WSIZE), offset);
    }

    /* Epilogue part */
    PUT(foot_pointer(heap_list_pointer) + WSIZE, PACK(0, prev_alloc,is_alloc));

    /* Extend the empty heap with a block of INITSIZE bytes */
    if (extend_heap(INITSIZE/WSIZE) == NULL) {
        return false;
    }
    return true;
}

static size_t ALIGN(size_t size)
{
    return (((size_t)(size) + (ALIGNMENT - 1)) & ~0X7);   
}

static void *find_fit(size_t asize)
{
    /* Initialization */
    void *bp;
    void *temp_list;
    
    /* Find seglist index and corresponding seglist start part */
    size_t index = find_list(asize);
    char *cur_list = first_seglist + index * DSIZE;

    /* For larger required size, use best fit approach */
    if (index >= BIGLIST) {
        /* Initialize min_bp to NULL in case cannot find suitable block */
        void *min_bp = NULL;        
        /* Initialize best_size to upper bound of a seglist */
        size_t best_size = MIN_FREE_SIZE * (1 << index) - 1;
        
        /* Loop each seglist which range's lower bound >= asize */
        for(temp_list = cur_list; temp_list != (char *)last_list + DSIZE; temp_list = (char *)temp_list + DSIZE) {
            /* Loop each block of this seglist */
            for (bp = NEXT_FREE_BLKP(temp_list); bp != temp_list; bp = NEXT_FREE_BLKP(bp)) {
                if (!GET_ALLOC(head_pointe(bp)) && (asize <= GET_SIZE(head_pointer(bp)))) {
                    /* 
                     * min_bp = NULL means first get into this seglist
                     * or we find a block is better, whose size < best_size
                     */
                    if (min_bp == NULL || GET_SIZE(head_pointer(bp)) < best_size) {
                        /* Update related variables */
                        min_bp = bp;
                        best_size = GET_SIZE(head_pointer(bp));
                    }
                }
            }
        }

        return min_bp;
    }

    /* For smaller required size, use first fit approach */
    else {
         /* Loop each seglist which range's lower bound >= asize */
        for (temp_list = cur_list; temp_list != (char *)last_list + DSIZE; temp_list = (char *)temp_list + DSIZE) {
            /* Loop each block of this seglist */
            for (bp = NEXT_FREE_BLKP(temp_list); bp != temp_list; bp = NEXT_FREE_BLKP(bp)) {
                /* Find first suitable block then return the pointer */
                if (!GET_ALLOC(head_pointer(bp)) && (asize <= GET_SIZE(head_pointer(bp)))) {
                    return bp;
                }
            }
        }
    }

    /* Cannot find suitable block */
    return NULL;
}

static void ALLOC_PREV(void *p)
{
    PUT(p, (GET(p) | prev_alloc));
}

static void place(void *bp, size_t asize)
{
    /* Initialization */
    size_t csize = GET_SIZE(head_pointer(bp));
    size_t index;
    size_t is_prev_alloc = GET_PREV_ALLOC(head_pointer(bp));

    /* Need split block to avoid fragmentation */
    if ((csize - asize) >= MIN_FREE_SIZE) {
        delBlock(bp);
        
        /* Make first part as allocated */
        PUT(head_pointer(bp), PACK(asize, is_prev_alloc, is_alloc));
        
        /* Make second part as free */
        bp = next_block_address(bp);
        PUT(head_pointer(bp), PACK(csize - asize, prev_alloc, is_free));
        PUT(foot_pointer(bp), PACK(csize - asize, is_free, is_free));

        index = find_list(csize - asize);

        addBlock(bp, index);
    }

    else {
        delBlock(bp);

        PUT(head_pointer(bp), PACK(csize, is_prev_alloc, is_alloc));

        ALLOC_PREV(head_pointer(next_block_address(bp)));
    }
}

/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0) {
        return NULL;
    }

    /* Adjust block size to include alignment and overhead requirements */
    if (size <= MIN_ALLOC_SIZE) {
        asize = MIN_FREE_SIZE;
    }
    else {
        asize = ALIGN(size + WSIZE);
    }

    /* Search free lists to find fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    
    /* No fit found, get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }

    /* Go to newly extended memory and allocate */
    place(bp, asize);
    
    return bp;
}

/*
 * free
 */
void free (void *ptr) {
    /* Ignore spurious request */
    if (bp == 0) {
        return;
    }

    /* Get bp's size and prev_alloc info */
    size_t size = GET_SIZE(HDRP(bp));
    size_t is_prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    /* Set alloc bit to 0 to free this block and maintain prev alloc info */
    PUT(head_pointer(bp), PACK(size, is_prev_alloc, is_free));
    PUT(foot_pointer(bp), PACK(size, is_free, is_free));

    coalesce(bp);
}

/*
 * realloc
 */
void *realloc(void *oldptr, size_t size) {
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return NULL;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return NULL;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    //mm_checkheap(1);
    return newptr;
}

/*
 * calloc
 * This function is not tested by mdriver
 */
void *calloc (size_t nmemb, size_t size) {
    if (nmemb == 0 || size == 0) {
        return NULL;
    }

    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
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

