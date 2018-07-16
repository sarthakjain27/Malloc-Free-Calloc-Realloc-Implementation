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

/** Basic constants and macros **/
/* $begin mallocmacros */
#define WSIZE           4           /* Word and header/footer size (bytes) */
#define DSIZE           8           /* Doubleword size (bytes) */
#define CHUNKSIZE       (1 << 9)    /* Extend heap by this amount (bytes) */
#define INITSIZE        (1 << 12)   /* Initially extend heap by this amount */
#define MIN_FREE_SIZE   16          /* Min free block size (bytes) */
#define MIN_ALLOC_SIZE  12          /* Min allocate block size (bytes) */
#define MAX_SIZE        4096        /* Max block size for seglist #8 */

#define MAXLIST     9           /* Max seg list index */
#define BIGLIST     4           /* Seg list index of big size */

#define IS_FREE     0x0         /* Current block is free */
#define IS_ALLOC    0x1         /* Current block is allocate */
#define PREV_ALLOC  0X2         /* Current block's prev block is allocate */

/* Doubleword (8) alignment */
#define ALIGNMENT   8

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t MAX(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

static size_t ALIGN(size_t x) {
    return ((x + (ALIGNMENT - 1)) & ~0X7);
}

static size_t PACK(size_t size,int prev,int curr)
{
    return ((size) | (prev) | (curr));   
}

static size_t GET(void *p)
{
    return (*(unsigned int *)(p));   
}

static void PUT(void *p,size_t val)
{
       (*(unsigned int *)(p))= val;
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

static void ALLOC_PREV(void *p)
{
    PUT(p, (GET(p) | PREV_ALLOC));
}

static void FREE_PREV(void *bp)
{
    PUT(bp, (GET(bp) & (~PREV_ALLOC)));   
}

static void* HDRP(void *bp)
{
    return ((char *)(bp)-WSIZE);   
}

static void* FTRP(void *bp)
{
    return ((char *)(bp) + GET_SIZE(head_pointer(bp)) - DSIZE);   
}


static void *NEXT_BLKP(void *bp)
{
    return ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));    
}

static void *PREV_BLKP(void *bp)
{
    return ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)));   
}

static void* NEXT_PTR(void *bp)
{
    return bp;   
}

static void* PREV_PTR(void *bp)
{
    return ((char *)bp + WSIZE);   
}

static void* NEXT_FREE_BLKP(void *bp)
{
    return (base + (*(unsigned int *)(NEXT_PTR(bp))));   
}

static void* PREV_FREE_BLKP(void *bp)
{
    return (base + (*(unsigned int *)(PREV_PTR(bp))));   
}

/** Global Variables **/
/* $begin global variables definition */
static char *heap_listp = 0;        // heap start and then move to prologue
static char *base = 0;              // heap start address (not change)
static char *first_list = 0;        // seg list #0 start
static char *last_list = 0;         // seg list #9 start
static char *epilogue = 0;          // epilogue part
/* $end global variables definition */

/** Function prototype for internal helper routines **/
/* $begin internal helper funtion prototype */
/* Helper functions for general use */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

/* Helper functions for place block */
static inline void addBlock(void *bp, size_t index);
static inline void delBlock(void *bp);
static size_t find_list(size_t asize);

/* Helper functions for mm_checkheap */
static void printblock(void *bp); 
static void checkblock(void *bp);
static size_t check_cycle(void *bp);
static size_t checklist(int verbose);
static size_t check_freelist(int verbose);
void mm_checkheap(int verbose);
/* $end internal helper funtion prototype */

/*
 * Initialize - return -1 on error, 0 on success.
 *
 *  Initialize empty heap and build segregated list's start part, then extend
 *  heap with a block of INITSIZE bytes to prepare for later use
 */
bool mm_init(void)
{
    /* Create initial empty heap */
    size_t init_size = (2 * (MAXLIST + 1) + 4) * WSIZE;
    size_t prologue_size = (2 * (MAXLIST + 1) + 2) * WSIZE;
    if ((heap_listp = mem_sbrk(init_size)) == (void *)-1) {
        printf("mem_sbrk fails\n");
        return false;
    }

    /* Get heap start address and first/last seglist start part */
    base = heap_listp;
    first_list = heap_listp + DSIZE;
    last_list = first_list + MAXLIST * DSIZE;
    epilogue = heap_listp + (2 * (MAXLIST + 1) + 3) * WSIZE;
    
    /* Padding part (4 bytes) for alignment */
    PUT(heap_listp, PACK(0, IS_FREE, IS_FREE));

    /* Prologue part */
    heap_listp = heap_listp + WSIZE;    // move to prologue header
    PUT(heap_listp, PACK(prologue_size, PREV_ALLOC, IS_ALLOC));
    heap_listp = heap_listp + WSIZE; 
    PUT(FTRP(heap_listp), PACK(prologue_size, PREV_ALLOC, IS_ALLOC));

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
    PUT(FTRP(heap_listp) + WSIZE, PACK(0, PREV_ALLOC, IS_ALLOC));

    /* Extend the empty heap with a block of INITSIZE bytes */
    if (extend_heap(INITSIZE/WSIZE) == NULL) {
        return false;
    }
    
    return true;
}

/*
 * mm_malloc - allocate size bytes and return a pointer to the allocated 
 *             memory.
 *  
 *  If size is 0, then mm_malloc will return NULL;
 *  If cannot extend more memory from system, then mm_malloc will return NULL.
 */
void *mm_malloc(size_t size)
{
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
 * mm_free - frees the memory space pointed to by bp
 *
 *  bp must hae been returned by a previous call to mm_malloc(), mm_calloc() 
 *  or mm_realloc(). Otherwise, or if free(bp) has already been called before, 
 *  undefined behavior occurs. If bp is 0, no operation is performed.
 */
void mm_free(void *bp)
{
    /* Ignore spurious request */
    if (bp == 0) {
        return;
    }

    /* Get bp's size and prev_alloc info */
    size_t size = GET_SIZE(HDRP(bp));
    size_t is_prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    /* Set alloc bit to 0 to free this block and maintain prev alloc info */
    PUT(HDRP(bp), PACK(size, is_prev_alloc, IS_FREE));
    PUT(FTRP(bp), PACK(size, IS_FREE, IS_FREE));

    coalesce(bp);
}

/*
 * extend_heap - Extend heap size and return a pointer to the extend memory
 *
 *  If cannot extend heap, return NULL.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    size_t is_prev_alloc;

    /* Allocate to maintain alignment requests */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1) {
        printf("mem_sbrk fails\n");
        return NULL;
    }

    /* Find bp's prev_alloc info to set extended block's prev_alloc */
    is_prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    /* Initialize the extended block header and footer */
    PUT(HDRP(bp), PACK(size, is_prev_alloc, IS_FREE));
    PUT(FTRP(bp), PACK(size, IS_FREE, IS_FREE));

    /* Initialize the epilogue header */
    epilogue = HDRP(NEXT_BLKP(bp));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, PREV_ALLOC, IS_ALLOC));

    return coalesce(bp);
}

/*
 * find_fit - Find a block which satisfy the size requirement and return a 
 *            pointer to this block
 *
 *  Based on asize, use best fit or first fit correctly
 *  If cannot find such block, return NULL
 */
static void *find_fit(size_t asize)
{
    /* Initialization */
    void *bp;
    void *temp_list;
    
    /* Find seglist index and corresponding seglist start part */
    size_t index = find_list(asize);
    char *cur_list = first_list + index * DSIZE;

    /* For larger required size, use best fit approach */
    if (index >= BIGLIST) {
        /* Initialize min_bp to NULL in case cannot find suitable block */
        void *min_bp = NULL;        
        /* Initialize best_size to upper bound of a seglist */
        size_t best_size = MIN_FREE_SIZE * (1 << index) - 1;
        
        /* Loop each seglist which range's lower bound >= asize */
        for(temp_list = cur_list; temp_list != (char *)last_list + DSIZE; 
            temp_list = (char *)temp_list + DSIZE) {
            /* Loop each block of this seglist */
            for (bp = NEXT_FREE_BLKP(temp_list); bp != temp_list; 
                bp = NEXT_FREE_BLKP(bp)) {
                if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                    /* 
                     * min_bp = NULL means first get into this seglist
                     * or we find a block is better, whose size < best_size
                     */
                    if (min_bp == NULL || GET_SIZE(HDRP(bp)) < best_size) {
                        /* Update related variables */
                        min_bp = bp;
                        best_size = GET_SIZE(HDRP(bp));
                    }
                }
            }
        }

        return min_bp;
    }

    /* For smaller required size, use first fit approach */
    else {
         /* Loop each seglist which range's lower bound >= asize */
        for (temp_list = cur_list; temp_list != (char *)last_list + DSIZE; 
            temp_list = (char *)temp_list + DSIZE) {
            /* Loop each block of this seglist */
            for (bp = NEXT_FREE_BLKP(temp_list); bp != temp_list; 
                bp = NEXT_FREE_BLKP(bp)) {
                /* Find first suitable block then return the pointer */
                if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                    return bp;
                }
            }
        }
    }

    /* Cannot find suitable block */
    return NULL;
}

/*
 * delBlock - delete a free block from the seglist
 */
static inline void delBlock(void *bp)
{
    PUT(PREV_PTR(NEXT_FREE_BLKP(bp)), GET(PREV_PTR(bp)));
    PUT(NEXT_PTR(PREV_FREE_BLKP(bp)), GET(NEXT_PTR(bp)));
}

/*
 * addBlock - add a free block to the front of the seglist
 */
static inline void addBlock(void *bp, size_t index)
{
    PUT(NEXT_PTR(bp), GET(NEXT_PTR(first_list + index * DSIZE)));
    PUT(PREV_PTR(bp), GET(PREV_PTR(NEXT_FREE_BLKP(bp))));

    PUT(NEXT_PTR(first_list + index * DSIZE), (long)bp - (long)base);
    PUT(PREV_PTR(NEXT_FREE_BLKP(bp)), (long)bp - (long)base);
}

/*
 * place - Put a allocated block which size is asize to the block which is
 *         pointed by bp and split if need.
 *
 *  First delete the block which is pointed by bp from seglist;
 *  then updated bp's header/footer with asize and split if need;
 *  if split happens, then add the remain free block to seglist
 */
static void place(void *bp, size_t asize)
{
    /* Initialization */
    size_t csize = GET_SIZE(HDRP(bp));
    size_t index;
    size_t is_prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    /* Need split block to avoid fragmentation */
    if ((csize - asize) >= MIN_FREE_SIZE) {
        delBlock(bp);
        
        /* Make first part as allocated */
        PUT(HDRP(bp), PACK(asize, is_prev_alloc, IS_ALLOC));
        
        /* Make second part as free */
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, PREV_ALLOC, IS_FREE));
        PUT(FTRP(bp), PACK(csize - asize, IS_FREE, IS_FREE));

        index = find_list(csize - asize);

        addBlock(bp, index);
    }

    else {
        delBlock(bp);

        PUT(HDRP(bp), PACK(csize, is_prev_alloc, IS_ALLOC));

        ALLOC_PREV(HDRP(NEXT_BLKP(bp)));
    }
}

/*
 * mm_realloc - change the size of the memory block pointed to by ptr to size
 *              bytes.
 *
 *  The contents will be unchanged to the minimun of the old and new sizes;
 *  newly allocated memory will be uninitialized.
 *  If ptr is NULL, then the call is equivalent to malloc(size), for all values
 *  of size; if size is 0, and ptr is not NULL, then the call is equivalent to
 *  free(ptr).
 *  Unless ptr is NULL, it must have been returned by previous call to 
 *  mm_malloc(), mm_calloc() or mm_realloc(). If the area pointed to was moved, 
 *  a free(ptr) is done.
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

    //mm_checkheap(1);
    return newptr;
}

/*
 * coalesce - Coalesce bp with its prev and next block if free to avoid two
 *            consecutive free blocks in the heap. Return a pointer to the
 *            coalesced block
 */
static void *coalesce(void *bp)
{
    /* Find bp's prev and next block is allocate or not */
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    
    /* Initialize */
    size_t size = GET_SIZE(HDRP(bp));   // bp's size
    size_t index;                       // index used to find correct seg list
    
    /* 
     * Case 1 - both prev and next block is allocate 
     *   add bp into correct seg list
     *   update bp's next block's prev_alloc bit to IS_FREE
     */
    if (prev_alloc && next_alloc) {
        index = find_list(size);
        addBlock(bp, index);
        FREE_PREV(HDRP(NEXT_BLKP(bp)));
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
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        index = find_list(size);
        
        delBlock(NEXT_BLKP(bp));
        
        PUT(HDRP(bp), PACK(size,prev_alloc,0));
        PUT(FTRP(bp), size);
        
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
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        index = find_list(size);
        
        size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
        
        delBlock(PREV_BLKP(bp));
        
        PUT(FTRP(bp), size);
        PUT(HDRP(PREV_BLKP(bp)),PACK(size, prev_prev_alloc, IS_FREE));
        FREE_PREV(HDRP(NEXT_BLKP(PREV_BLKP(bp))));
        
        addBlock(PREV_BLKP(bp), index);
        return (PREV_BLKP(bp));
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
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
        index = find_list(size);
        
        size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
        
        delBlock(NEXT_BLKP(bp));
        delBlock(PREV_BLKP(bp));
        
        PUT(HDRP(PREV_BLKP(bp)),PACK(size, prev_prev_alloc, IS_FREE));
        PUT(FTRP(NEXT_BLKP(bp)),size);
        
        addBlock(PREV_BLKP(bp), index);
        return (PREV_BLKP(bp));
    }
}

/*
 * mm_calloc - allocate memory of nmemb elements of size bytes each and returns
 *             a pointer to the allocated memory which is set to zero.
 *
 *  If nmemb or size is 0, then calloc() returns NULL.
 */

void *mm_calloc (size_t nmemb, size_t size)
{
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
 * find_fit - Return seglist index based on asize
 */
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

/*
 * in_heap - Return whether the pointer is in the heap
 */
static int in_heap(const void *p) 
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * aligned - Return whether the pointer is aligned.
 */
static long aligned(const void *p) 
{
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * printblock - Print block information
 */
static void printblock(void *bp)
{
    /* Block size got from header and footer */
    size_t hsize = GET_SIZE(HDRP(bp));       
    size_t fsize = GET_SIZE(FTRP(bp)); 

    /* Block allocate/free info got from header and footer */
    size_t halloc = GET_ALLOC(HDRP(bp));    
    size_t falloc = GET_ALLOC(FTRP(bp));

    /* Block prev's allocate/free info got from header */
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));  
    
    /* Epilogue Case */
    //if (hsize == 0) {
    if (GET_SIZE(bp) == 0) {
        printf("Epilogue at %p : (%zu, %c)\n", bp, (size_t)GET_SIZE(bp), 
                (GET_ALLOC(bp) ? 'A' : 'F'));
    }
    /* Not epilogue */
    else {
        /* Allocate block info */
        if (halloc) {
            printf("Allocate block at %p: header (%zu, %c, %c)\n", bp, hsize, 
                    (halloc ? 'A' : 'F'), (prev_alloc ? 'A' : 'F'));
        }
        /* Free block info */
        else {
            printf("Free block at %p: header (%zu, %c, %c),",  
                bp, hsize, (prev_alloc ? 'A' : 'F'), (halloc ? 'A' : 'F'));
            printf(" footer (%zu, %c)\n", fsize, (falloc ? 'A' : 'F'));
        }
    }
}

/*
 * checkblock - check each block's header and footer consistency
 */
static void checkblock(void *bp)
{
    /* Block size got from header and footer */
    size_t hsize = GET_SIZE(HDRP(bp));       
    size_t fsize = GET_SIZE(FTRP(bp)); 

    /* Block allocate/free info got from header and footer */
    size_t halloc = GET_ALLOC(HDRP(bp));    
    size_t falloc = GET_ALLOC(FTRP(bp));
    
    /* Check block is inside heap range or not */
    if (!in_heap(bp)) {
        printf("Error: Block at %p is outside heap range [%p, %p]\n", bp, 
                mem_heap_lo(), mem_heap_hi());
    }

    /* Check block address is aligned or not */
    if (!aligned(bp)) {
        printf("Error: Block at %p with size %zu is not doubleword aligned\n", 
                bp, hsize);
    }
    
    /* Check block size >= MIN_FREE_SIZE */
    if ((hsize < MIN_FREE_SIZE)) {
        printf("Error: Block at %p size %d is smaller than minimun size %d\n", 
                bp, (int)hsize, (int)MIN_FREE_SIZE);
    }

    /* Check free block's header and footer consistency */
    if ((!halloc) && ((hsize != fsize) || (halloc != falloc))) {
        printf("Error: Block at %p's header doesn't match footer\n", bp);
        printf("Block's header : (%zu, %c), footer : (%zu, %c)\n", 
                hsize, (halloc ? 'A' : 'F'), fsize, (falloc ? 'A' : 'F'));
    }         
}

/*
 * check_cycle - Check if there is a cycle in linked list
 *               Return 1 if exsit, 0 if not
 */
static size_t check_cycle(void *bp)
{
    char *hare = NEXT_FREE_BLKP(bp);        // faster pointer
    char *tortoise = NEXT_FREE_BLKP(bp);    // slower pointer
    
    while (hare != bp && NEXT_FREE_BLKP(hare) != bp) {
        if (NEXT_FREE_BLKP(hare) == tortoise
            || NEXT_FREE_BLKP(NEXT_FREE_BLKP(hare)) == tortoise) {
                return 1;
        }

        /* Update hare and tortoise */
        hare = NEXT_FREE_BLKP(NEXT_FREE_BLKP(hare));
        tortoise = NEXT_FREE_BLKP(tortoise);
    }
    
    return 0;
}

/*
 * checklist - Loop each block in heap to check and return free block number
 */
static size_t checklist(int verbose)
{
    /* Initialization */
    void *bp = heap_listp;
    size_t size = GET_SIZE(HDRP(bp));
    size_t consec_free = 0;            
    size_t stored_alloc = PREV_ALLOC;
    size_t free_blk_num = 0;
    
    /* When size is 0 means we meet epilogue */
    while (size != 0) {
        size_t is_alloc = GET_ALLOC(HDRP(bp));
        size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
        
        /* Check each block in heap */
        /* Check address alignment */
        if (!aligned(bp)) {
            printf("Error: not satisfy alignment\n");
            if (verbose) {
                printf("Block at address %p doesn't satisfy alignment\n", bp);
            }
        }
        
        /* Check address in heap or not */
        if (!in_heap(bp)) {
            printf("Error: not in heap range\n");
            if (verbose) {
                printf("Block at address %p isn't in heap range [%p, %p]\n", 
                        bp, mem_heap_lo(), mem_heap_hi());
            }
        }
        
        if (verbose) {
            printblock(bp);
        }
        
        /* Check prev/next allocate bit consistency */
        if (stored_alloc != prev_alloc) {
            printf("Error: prev/next allocate bit doesn't match\n");
        }
        stored_alloc = is_alloc << 1; 

        /* Free blocks in heap */
        if (is_alloc) {
            free_blk_num++;
            checkblock(bp);
            
            /* consec_free is 1 iff there are two consecutive free blocks */
            if (consec_free == 1) {
                printf("Error: two consecutive free blocks\n");
                if (verbose) {
                    printblock(bp);
                    printblock(PREV_BLKP(bp));
                }
            }
            else {
                /* Update consec_free value */
                consec_free++;
            }
        }
        /* Allocate blocks in heap */
        else {
            /* Reset consecutive flag */
            consec_free = 0;
        }
        
        /* Move to next block */
        bp = NEXT_BLKP(bp);
        size = GET_SIZE(HDRP(bp));
    }
    
    return free_blk_num;
}

/*
 * check_freelist - Loop each free block in seglist to check 
 *                  and return free block number
 */
static size_t check_freelist(int verbose) 
{
    /* Initialization */
    size_t free_blk_num = 0;
    size_t free_list_num = 0;
    size_t lower_bound = MIN_FREE_SIZE / 2;
    size_t upper_bound = MIN_FREE_SIZE;
    
    char *cur_list;
    char *bp;
    char *cycle_bp;
    
    size_t bp_size;
    
    /* Loop each seglist */
    for (cur_list = first_list; cur_list != last_list + DSIZE; 
         cur_list = cur_list + DSIZE) {
        free_list_num++;
        
        /* Check if there is cyclic linked list */
        cycle_bp = NEXT_FREE_BLKP(cur_list);
        if (check_cycle(cycle_bp)) {
            printf("Error: there is cyclic linked list\n");
        }

        /* Loop each free block in this seglist */
        for (bp = NEXT_FREE_BLKP(cur_list); bp != cur_list; 
            bp = NEXT_FREE_BLKP(bp)) {
            bp_size = GET_SIZE(HDRP(bp));
            free_blk_num++;
            
            if (verbose) {
                printblock(bp);
            }
            
            /* Check general block info correctness */
            checkblock(bp);
            
            /* Check next/prev pointer consistency */
            if (PREV_FREE_BLKP(NEXT_FREE_BLKP(bp)) != bp) {
                printf("Error: free block next/prev pointer not consist\n");
                if (verbose) {
                    printf("free block at %p, prev %p, next %p, prev free \
                        block's next point to %p\n", bp, PREV_FREE_BLKP(bp),
                        NEXT_FREE_BLKP(bp), PREV_FREE_BLKP(NEXT_FREE_BLKP(bp)));
                }
            }
            
            /* Check free block fall into correct seg list */
            /* seglist #0 - #8 */
            if (lower_bound < MAX_SIZE) {
                if (bp_size < lower_bound || bp_size > upper_bound) {
                    printf("Error: free block falls into wrong seg list\n");
                    if (verbose) {
                        printf("free block at %p has size %zu when this", 
                                bp, bp_size);
                        printf(" seglist range [%zu, %zu]\n", 
                                lower_bound, upper_bound);
                    }
                }
            }
            /* seglist #9 */
            else {
                if (bp_size < lower_bound) {
                    printf("Error: free block falls into wrong seg list\n");
                    if (verbose) {
                        printf("free block at %p has size %zu when this", 
                                bp, bp_size);
                        printf(" seglist range >= %u\n", MAX_SIZE);
                    }
                }    
            }
        }  

        /* Update lower_bound and upper_bound */
        lower_bound = lower_bound * 2;
        upper_bound = upper_bound * 2;
    }
    
    /* Check seg list number */
    if (free_list_num != (MAXLIST + 1)) {
        printf("Error: seglist number doesn't match\n");
        if (verbose) {
            printf("Counted seglist number is %zu", free_list_num);
            printf("while the correct number is %u\n", (MAXLIST + 1));
        }
    }

    return free_blk_num;    
}

/*
 * mm_checkheap - check the heap and free list, print error message
 */
bool mm_checkheap(int verbose) 
{
    /* Check padding part */
    if (GET(mem_heap_lo()) != 0) {
        printf("Error: Padding part content isn't 0\n");
	    return false;
    }
    
    /* Check prologue and epilogue blocks */
    char *prologue = heap_listp;
    size_t prologue_size = (2 * (MAXLIST + 1) + 2) * WSIZE;
    
    checkblock(prologue);
    
    if (GET_SIZE(HDRP(prologue)) != prologue_size) {
        printf("Error: prologue %p size : %d doesn't match \
            correct size : %d\n", prologue, (int)GET_SIZE(HDRP(prologue)), 
            (int)prologue_size);
	    return false;
    }
    
    if (!GET_ALLOC(HDRP(prologue))) {
        printf("Error: prologue isn't allocated\n");
	    return false;
    }
       
    if (verbose) {
        printblock(prologue);
    }
    
    if (GET_SIZE(epilogue) != 0) {
        printf("Error: epilogue %p size : %d doesn't match \
            correct size : 0\n", prologue, (int)GET_SIZE(HDRP(prologue)));
	    return false;
    }
    
    if (!GET_ALLOC(epilogue)) {
        printf("Error: epilogue isn't allocated\n");
	    return false;
    }
    
    if (verbose) {
        printblock(epilogue);
    }
    /* end check prologue and epilogue blocks */
    
    /* Check block in heap and in seglist */
    size_t free_num_heap = checklist(verbose);
    size_t free_num_list = check_freelist(verbose);
    if (free_num_heap != free_num_list) {
        printf("Error: different free block number\n");
        if (verbose) {
            printf("Free block number counted in heap is %zu", free_num_heap);
            printf(" while free block number counted in list is %zu\n",
                    free_num_list);
        }
	    return false;
    }
	return true;
}


