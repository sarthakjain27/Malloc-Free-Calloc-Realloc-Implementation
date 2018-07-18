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
#include <stddef.h>
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

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

#define ALIGNMENT 2*dsize

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    char payload[0];
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;

typedef struct free_block
{
    word_t header;
    struct free_block *next_free;
    struct free_block *prev_free;
} block_f;

static block_f *freeList_start=NULL;
static block_t *heap_start = NULL;

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static void freeList_LIFO_insert(block_f *block);
static void freeList_del(block_f *block);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_free_size(block_f *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

/*
 * Initialize: return false on error, true on success.
 */
bool mm_init(void) {
    // Create the initial empty heap 
    printf("mm_init called \n");
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true); // Prologue footer
    start[1] = pack(0, true); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start=(block_t *) &(start[1]);
    freeList_start = (block_f *) &(start[1]);
    freeList_start->next_free=NULL;
    freeList_start->prev_free=NULL;
    printf("freeList_start %p\n",freeList_start);
    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
    printf("Returned from init \n");
}

/*
 * malloc
 */
void *malloc (size_t size) {
    printf("Malloc called with size %zu\n",size);
   dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);
    printf("Size %zu Asize %zu\n",size,asize);
    // Search the free list for a fit
    printf("Calling find_fit from malloc \n");
    block = find_fit(asize);
    printf("Returned from find_fit from malloc \n");

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }
    printf("Calling place from malloc \n");
    place(block, asize);
    printf("Returned to malloc from place \n");
    bp = header_to_payload(block);
    dbg_ensures(mm_checkheap(__LINE__));
    printf("Returning from malloc \n");
    return bp;
}

/*
 * free
 */
void free (void *bp) {
    printf("Free called %p\n",bp);

	if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    printf("Free block pointer %p\n",block);
	size_t size = get_size(block);

    write_header(block, size, false);
    write_footer(block, size, false);

    coalesce(block);
}

/*
 * realloc
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * calloc
 * This function is not tested by mdriver
 */
void *calloc (size_t elements, size_t size) {
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

static void place(block_t *block, size_t asize)
{
    printf("Place entered\n");
	size_t csize = get_size(block);
	printf("csize %zu asize %zu min_block_size %zu\n",csize,asize,min_block_size);
    if ((csize - asize) >= min_block_size)
    {
		printf("If entered \n");	
        block_t *block_next;
        write_header(block, asize, true);
        write_footer(block, asize, true);

        block_next = find_next(block);
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);
       
		printf("New block created with size %zu\n",csize-asize);
		 
        block_f* block_free=(block_f *)block;
        block_f* block_next_free=(block_f *)block_next;
        printf("block %p size %zu block next %p size %zu",block_free,block_free->header,block_next_free,block_next_free->header);
	    
	if(freeList_start==block_free)
		freeList_start=block_next_free;
	
	if(block_free->prev_free==NULL && block_free->next_free==NULL)
	{
		block_next_free->prev_free=NULL;
		block_next_free->next_free=NULL;
	}
	else if(block_free->prev_free==NULL && block_free->next_free!=NULL)
	{
		block_next_free->prev_free=NULL;
		block_next_free->next_free=block_free->next_free;
		block_free->next_free->prev_free=block_next_free;
	}
	else if(block_free->prev_free!=NULL && block_free->next_free==NULL)
	{
		block_next_free->next_free=NULL;
		block_next_free->prev_free=block_free->prev_free;
		block_free->prev_free->next_free=block_next_free;
	}
	else
	{
		block_next_free->next_free=block_free->next_free;
		block_next_free->prev_free=block_free->prev_free;
		block_free->prev_free->next_free=block_next_free;
		block_free->next_free->prev_free=block_next_free;
	}
		printf("FreeList_start %p\n",freeList_start);
    }

    else
    { 
        write_header(block, csize, true);
        write_footer(block, csize, true);
	block_f* block_free=(block_f *)block;
	if(block_free==freeList_start)
	{
        	freeList_start=freeList_start->next_free;
		freeList_start->prev_free=NULL;
	}
	//both prev and next null possible? and if yes then do what? freeList-start=NULL?
	if(block_free->prev_free==NULL && block_free->next_free!=NULL)
	{
		block_free->next_free->prev_free=NULL;
	}
	else if(block_free->prev_free!=NULL && block_free->next_free==NULL)
	{
		block_free->prev_free->next_free=NULL;
	}
	else{
		block_free->prev_free->next_free=block_free->next_free;
		block_free->next_free->prev_free=block_free->prev_free;
	}
    }
     printf("Asize %zu FreeList_start %p\n",asize, freeList_start);
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno) {
    printf("Printing Heap blocks \n");
    block_t *i;
	block_f *j;
	for(i=heap_start;get_size(i) > 0; i = find_next(i))
	{
		if(get_alloc(i))
			printf("Heap Block %p size %zu\n",i,get_size(i));
	}
	for(j=freeList_start;j!=NULL && get_free_size(j)>0; j = j->next_free)
	{
		printf("FreeList Block %p size %zu\n",j,get_free_size(j));	
	}
	printf("Returning from checkheap \n");
    return true;
}

static block_t *extend_heap(size_t size) 
{
    printf("Extend heap called with size %zu",size);
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);
    
	printf("new extend heap block address %p size %zu\n",block,size);
	// Create new epilogue header
    block_t *block_next = find_next(block);
    printf("new epilogue %p\n",block_next);
    write_header(block_next, 0, true);
    printf("Calling coalesce from extend_heap\n");
    // Coalesce in case the previous block was free
    return coalesce(block);
}

/*
 * <what does coalesce do?>
 */
static block_t *coalesce(block_t * block) 
{
	printf("Coalesce called \n");
    block_t *block_next = find_next(block);
    block_t *block_prev = find_prev(block);

    block_f *block_free=(block_f *)block;
    block_f *block_next_free=(block_f *)block_next;
    block_f *block_prev_free=(block_f *)block_prev;
   	
	printf("freeList start %p block_free %p block_f_next %p block_p_next %p\n",freeList_start,block_free,block_next_free,block_prev_free);
 
    bool prev_alloc = extract_alloc(*(find_prev_footer(block)));
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);

    if (prev_alloc && next_alloc)              // Case 1
    {
	printf("Case 1 entered \n");
        if(block_free!=freeList_start)
		freeList_LIFO_insert(block_free);
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
	printf("Case 2 entered \n");
        size += get_size(block_next);
        write_header(block, size, false);
        write_footer(block, size, false);
	printf("block %p size %zu\n",block,block->header); 
	freeList_del(block_next_free);
	freeList_LIFO_insert(block_free);	
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
	printf("Case 3 entered \n");
        size += get_size(block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
    printf("block %p size %zu\n",block_prev,block_prev->header);    
	freeList_del(block_prev_free);
	freeList_LIFO_insert(block_prev_free);
        block=block_prev;
    }

    else                                        // Case 4
    {
	    printf("Case 4 entered \n");
        size += get_size(block_next) + get_size(block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
		printf("block %p sze %zu \n",block_prev,block_prev->header);
	    
	freeList_del(block_next_free);
	freeList_del(block_prev_free);
	freeList_LIFO_insert(block_prev_free);
	    
        block=block_prev;
    }
	printf("Returning from coalesce \n");
	printf("freeList_start %p freeList next %p freeList prev %p\n",freeList_start,freeList_start->next_free,freeList_start->prev_free);
    return block;
}

static void freeList_LIFO_insert(block_f *block){
	printf("freeList_LIFO called freeList %p\n",freeList_start);
	block->next_free=freeList_start;
	block->prev_free=NULL;
	if(freeList_start!=NULL && freeList_start->prev_free!=NULL)
		freeList_start->prev_free=block;
	freeList_start=block;
}

static void freeList_del(block_f *block){
	printf("freeList_del called \n");
	if(block->prev_free==NULL) //at start of freeList
	{
		printf("start of freelist block\n");
		freeList_start=freeList_start->next_free;
		if(freeList_start!=NULL)
			freeList_start->prev_free=NULL;
	}
	else if(block->next_free==NULL) //Last block of freeList
		block->prev_free->next_free=NULL;
	else //in middle of freeList
	{
		printf("Middle \n");
		block->prev_free->next_free=block->next_free;
		block->next_free->prev_free=block->prev_free;
	}
}

static block_t *find_fit(size_t asize)
{
    block_f *block;
    for (block = freeList_start; block!=NULL && get_free_size(block)>0; block = block->next_free)
    {
        if (asize <= get_free_size(block))
        {
            return (block_t *)block;
        }
    }
    return NULL; // no fit found
}


/*
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
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | alloc_mask) : size;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

static size_t get_free_size(block_f *block)
{
    return ((block->header) & size_mask);    
}


/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block->header = pack(size, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}

