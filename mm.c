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

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size
static const size_t CHUNKSIZE = 224;    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

/* What is the correct alignment? */
#define ALIGNMENT 2*dsize

/* Variables used as offsets for
   segregated lists headers */
#define SEGLIST1     0
#define SEGLIST2     wsize
#define SEGLIST3     2*wsize
#define SEGLIST4     3*wsize
#define SEGLIST5     4*wsize
#define SEGLIST6     5*wsize
#define SEGLIST7     6*wsize
#define SEGLIST8     7*wsize
#define SEGLIST9     8*wsize
#define SEGLIST10    9*wsize
#define SEGLIST11    10*wsize
#define SEGLIST12    11*wsize
#define SEGLIST13    12*wsize
#define SEGLIST14    13*wsize

/* Maximum size limit of each list */
#define LIST1_LIMIT      32
#define LIST2_LIMIT      64
#define LIST3_LIMIT      96
#define LIST4_LIMIT      128
#define LIST5_LIMIT      160
#define LIST6_LIMIT      640
#define LIST7_LIMIT      1280
#define LIST8_LIMIT      2560
#define LIST9_LIMIT      5120
#define LIST10_LIMIT     10240
#define LIST11_LIMIT     20480
#define LIST12_LIMIT     40960
#define LIST13_LIMIT     81920

#define TOTALLIST   14
/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

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

block_t *heap_start = NULL;
char *freeList_start=NULL;

static void PUT(char *p,size_t val);
static block_t *extend_heap(size_t size);
static block_t *coalesce(block_t *block);
static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);
static void freeList_LIFO_insert(block_f *block,size_t size);
static void freeList_FIFO_insert(block_f *block);
static void freeList_del(block_f *block,size_t size);
static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static size_t get_size(block_t *block);
static size_t GET(char *p);
static void *find_fit(size_t asize);
static size_t get_payload_size(block_t *block);

static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);
static void place(void *bp, size_t asize);
static size_t MAX(size_t x, size_t y);
static block_t *payload_to_header(void *bp);
static void write_footer(block_t *block, size_t size, bool alloc);
static void write_header(block_t *block, size_t size, bool alloc);

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t MAX(size_t x, size_t y)
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

static void PUT(char *p,size_t val)
{
    *((size_t*) (p)) = (val);   
}

/*
 * Initialize: return false on error, true on success.
 */
bool mm_init(void) {
    // Create the initial empty heap 
    printf("mm_init called \n");
    
    printf("Initialising memory location for storing start pointers of seg list on heap \n");
    freeList_start=(char *)(mem_sbrk(14*wsize));
    if (freeList_start == (void *)-1) 
    {
        return false;
    }
    
    /* Initializing the segregated list pointers on heap */
	PUT(freeList_start + SEGLIST1, (size_t) NULL);
	PUT(freeList_start + SEGLIST2, (size_t) NULL);
	PUT(freeList_start + SEGLIST3, (size_t) NULL);
	PUT(freeList_start + SEGLIST4, (size_t) NULL);
	PUT(freeList_start + SEGLIST5, (size_t) NULL);
	PUT(freeList_start + SEGLIST6, (size_t) NULL);
	PUT(freeList_start + SEGLIST7, (size_t) NULL);
	PUT(freeList_start + SEGLIST8, (size_t) NULL);
	PUT(freeList_start + SEGLIST9, (size_t) NULL);
	PUT(freeList_start + SEGLIST10, (size_t) NULL);
	PUT(freeList_start + SEGLIST11, (size_t) NULL);
	PUT(freeList_start + SEGLIST12, (size_t) NULL);
	PUT(freeList_start + SEGLIST13, (size_t) NULL);
	PUT(freeList_start + SEGLIST14, (size_t) NULL);
   
    printf("FreeList_start initialised %p mem_heap_lo %p mem_heap_hi %p \n",freeList_start,mem_heap_lo(),mem_heap_hi());
    
    word_t *start = (word_t *)(mem_sbrk(2*wsize));
    if (start == (void *)-1) 
    {
        return false;
    }
    start[0] = pack(0, true); // Prologue footer
    start[1] = pack(0, true); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start=(block_t *) &(start[1]);
    printf("Heap_start initialised%p\n",heap_start);
    
    printf("Calling extend heap from mm_init \n");
    if (extend_heap(CHUNKSIZE) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    printf("Malloc called with size %zu\n",size);
    size_t asize, extendsize;;
    void *bp=NULL;
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
    
    printf("Calling find_fit\n");
	/* Search through heap for possible fit */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);	/* Actual assignment */
		return bp;
	}
    printf("No fit found, calling extend heap \n");
	/* If no fit, get more memory and allocate memory */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize)) == NULL)
		return NULL;
	place(bp, asize);		/* Assignment */
	return bp;
}

/*
 * free
 */
void free (void *ptr) {
    printf("Free called %p\n",ptr);
    if (ptr == NULL)
    {
        return;
    }
    block_t *block = payload_to_header(ptr);
    printf("Free block pointer %p\n",block);
	size_t size = get_size(block);

    write_header(block, size, false);
    write_footer(block, size, false);

    printf("calling freeList_LIFO_insert in seglist \n");
	/* Add free block to appropriate segregated list */
	freeList_LIFO_insert((block_f *)block, size);
	printf("Calling coalesce from free\n");
	coalesce((block_t *)block);
	printf("Returned from coalesce in free \n");
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

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno) {
	printf("Printing Heap blocks \n");
	block_t *i;
	char *listpointer = NULL;
	unsigned sizeatstart = 0;
	unsigned minimumblocksize = 0;
	unsigned maximumblocksize = 0;
	for(i=heap_start;get_size(i) > 0; i = find_next(i))
	{
		if(get_alloc(i))
			printf("Heap Block %p size %zu\n",i,get_size(i));
	}
	for(i=heap_start;get_size(i) > 0; i = find_next(i))
	{
		if(!get_alloc(i))
			printf("FreeList Block %p size %zu\n",i,get_size(i));
	}
	
	/* Checking if all blocks in each freelist fall within
	   the appropriate ranges (Different segregated lists) */
	for (sizeatstart = 0; sizeatstart < TOTALLIST; sizeatstart++) 
    	{
		if (sizeatstart == 0) {
			listpointer = (char *) GET(freeList_start + SEGLIST1);
			minimumblocksize = 0;
			maximumblocksize = LIST1_LIMIT;
		} else if (sizeatstart == 1) {
			listpointer = (char *) GET(freeList_start + SEGLIST2);
			minimumblocksize = LIST1_LIMIT;
			maximumblocksize = LIST2_LIMIT;
		} else if (sizeatstart == 2) {
			listpointer = (char *) GET(freeList_start + SEGLIST3);
			minimumblocksize = LIST2_LIMIT;
			maximumblocksize = LIST3_LIMIT;
		} else if (sizeatstart == 3) {
			listpointer = (char *) GET(freeList_start + SEGLIST4);
			minimumblocksize = LIST3_LIMIT;
			maximumblocksize = LIST4_LIMIT;
		} else if (sizeatstart == 4) {
			listpointer = (char *) GET(freeList_start + SEGLIST5);
			minimumblocksize = LIST4_LIMIT;
			maximumblocksize = LIST5_LIMIT;
		} else if (sizeatstart == 5) {
			listpointer = (char *) GET(freeList_start + SEGLIST6);
			minimumblocksize = LIST5_LIMIT;
			maximumblocksize = LIST6_LIMIT;
		} else if (sizeatstart == 6) {
			listpointer = (char *) GET(freeList_start + SEGLIST7);
			minimumblocksize = LIST6_LIMIT;
			maximumblocksize = LIST7_LIMIT;
		} else if (sizeatstart == 7) {
			listpointer = (char *) GET(freeList_start + SEGLIST8);
			minimumblocksize = LIST7_LIMIT;
			maximumblocksize = LIST8_LIMIT;
		} else if (sizeatstart == 8) {
			listpointer = (char *) GET(freeList_start + SEGLIST9);
			minimumblocksize = LIST8_LIMIT;
			maximumblocksize = LIST9_LIMIT;
		} else if (sizeatstart == 9) {
			listpointer = (char *) GET(freeList_start + SEGLIST10);
			minimumblocksize = LIST9_LIMIT;
			maximumblocksize = LIST10_LIMIT;
		} else if (sizeatstart == 10) {
			listpointer = (char *) GET(freeList_start + SEGLIST11);
			minimumblocksize = LIST10_LIMIT;
			maximumblocksize = LIST11_LIMIT;
		} else if (sizeatstart == 11) {
			listpointer = (char *) GET(freeList_start + SEGLIST12);
			minimumblocksize = LIST11_LIMIT;
			maximumblocksize = LIST12_LIMIT;
		} else if (sizeatstart == 12) {
			listpointer = (char *) GET(freeList_start + SEGLIST13);
			minimumblocksize = LIST12_LIMIT;
			maximumblocksize = LIST13_LIMIT;
		} else {
			listpointer = (char *) GET(freeList_start + SEGLIST14);
			minimumblocksize = LIST13_LIMIT;
			maximumblocksize = ~0;
		}

		while (listpointer != NULL) 
        	{
			if(!get_alloc((block_t *)listpointer))
			{
				if (!(minimumblocksize < get_size((block_t *)listpointer) && get_size((block_t *)listpointer) <= maximumblocksize)) 
            			{
					printf("Free block pointer %p is not in the appropriate list", listpointer);
                			return false;
				}
			}
			listpointer = find_next(listpointer);
		}
	}
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
    printf("new extend heap block address %p size %zu and original bp %p\n",block,size,bp);
	
    printf("Calling freeList_LIFO_insert in extend heap \n");
    /* Add to segregated list */
	freeList_LIFO_insert((block_f *)block, size);
	printf("Returned from freeList_LIFO_insert in extend heap \n");
    
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
   	
	printf("block_free %p block_f_next %p block_p_next %p\n",block_free,block_next_free,block_prev_free);
 
    bool prev_alloc = extract_alloc(*(find_prev_footer(block)));
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);

    if (prev_alloc && next_alloc)              // Case 1
    {
	    printf("Case 1 entered \n");
		return block;
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
	    printf("Case 2 entered \n");
        
        freeList_del(block_free,size);
	    freeList_del(block_next_free,get_size(block_next));
	    
        size += get_size(block_next);
        write_header(block, size, false);
        write_footer(block, size, false);
	    printf("block %p size %zu\n",block,block->header);
        freeList_LIFO_insert(block_free,size);
	    
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
	    printf("Case 3 entered \n");
        
        freeList_del(block_free,size);
	    freeList_del(block_prev_free,get_size(block_prev));
        
        size += get_size(block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        printf("block %p size %zu\n",block_prev,block_prev->header);    
	    
	    freeList_LIFO_insert(block_prev_free,get_size(block_prev));
	        
        block=block_prev;
    }

    else                                        // Case 4
    {
	    printf("Case 4 entered \n");
        
        freeList_del(block_free,size);
        freeList_del(block_next_free,get_size(block_next));
	    freeList_del(block_prev_free,get_size(block_prev));
        
        size += get_size(block_next) + get_size(block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
		printf("block %p sze %zu \n",block_prev,block_prev->header);
	    
	    freeList_LIFO_insert(block_prev_free,get_size(block_prev));
	    
        block=block_prev;
    }
	printf("Returning from coalesce \n");
    return block;
}

static void freeList_LIFO_insert(block_f *block,size_t size)
{
    printf("FreeList_LIFO_insert called with block %p and size %zu \n",bp,size);
    
	/* Address of head of a particular list */
	char *listhead;
    
	/* Address pointing to the address of head of a particular list */
	char *segstart;
	
    size_t size = get_size(block);
    
    if (size <= LIST1_LIMIT) {
		segstart = freeList_start + SEGLIST1;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST2_LIMIT) {
		segstart = freeList_start + SEGLIST2;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST3_LIMIT) {
		segstart = freeList_start + SEGLIST3;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST4_LIMIT) {
		segstart = freeList_start + SEGLIST4;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST5_LIMIT) {
		segstart = freeList_start + SEGLIST5;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST6_LIMIT) {
		segstart = freeList_start + SEGLIST6;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST7_LIMIT) {
		segstart = freeList_start + SEGLIST7;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST8_LIMIT) {
		segstart = freeList_start + SEGLIST8;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST9_LIMIT) {
		segstart = freeList_start + SEGLIST9;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST10_LIMIT) {
		segstart = freeList_start + SEGLIST10;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST11_LIMIT) {
		segstart = freeList_start + SEGLIST11;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST12_LIMIT) {
		segstart = freeList_start + SEGLIST12;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST13_LIMIT) {
		segstart = freeList_start + SEGLIST13;
		listhead = (char *) GET(segstart);

	} else {
		segstart = freeList_start + SEGLIST14;
		listhead = (char *) GET(segstart);
	}
	
	printf("Seg start %p listhead %p \n",segstart,listhead);
    
    // if there are no blocks in the list
    if(listhead==NULL)
    {
        printf("If of freeList_lifo_insert \n");
        //set current block as head
        PUT(segstart,(size_t)(block));
        printf("segstart %p size %zu \n", segstart, (size_t)bp);
        block->prev_free==NULL;
        block->next_free==NULL;
    }
    //there are blocks in the list
    else
    {
        printf("Else of freeList_lifo_insert \n");
        block_f * listhead_blockf=(block_f *)listhead;
        
        block->next_free=listhead_blockf;
        listhead_blockf->prev_free=block;
        
        //set current block as head
        PUT(segstart, (size_t) block);
		printf("segstart %p size %zu \n", segstart, (size_t)bp);
        
        block->prev_free=NULL;
    }
}

static void freeList_FIFO_insert(block_f *block)
{
	//printf("FreeList_FIFI called freeList_end %p\n",freeList_end);
	if(freeList_end!=NULL)
		freeList_end->next_free=block;
	block->prev_free=freeList_end;
	block->next_free=NULL;
	freeList_end=block;
	if(freeList_start==NULL)
		freeList_start=block;
}

static void freeList_del(block_f *block,size_t size)
{
	printf("freeList_del called for block %p and size %zu \n",block,size);
	if(block->prev_free==NULL) //at start of freeList
	{
		printf("block at start of freelist\n");
		
        if (size <= LIST1_LIMIT)
			PUT(freeList_start + SEGLIST1, (size_t) (block->next_free));
		else if (size <= LIST2_LIMIT)
			PUT(freeList_start + SEGLIST2, (size_t) (block->next_free));
		else if (size <= LIST3_LIMIT)
			PUT(freeList_start + SEGLIST3, (size_t) (block->next_free));
		else if (size <= LIST4_LIMIT)
			PUT(freeList_start + SEGLIST4, (size_t) (block->next_free));
		else if (size <= LIST5_LIMIT)
			PUT(freeList_start + SEGLIST5, (size_t) (block->next_free));
		else if (size <= LIST6_LIMIT)
			PUT(freeList_start + SEGLIST6, (size_t) (block->next_free));
		else if (size <= LIST7_LIMIT)
			PUT(freeList_start + SEGLIST7, (size_t) (block->next_free));
		else if (size <= LIST8_LIMIT)
			PUT(freeList_start + SEGLIST8, (size_t) (block->next_free));
		else if (size <= LIST9_LIMIT)
			PUT(freeList_start + SEGLIST9, (size_t) (block->next_free));
		else if (size <= LIST10_LIMIT)
			PUT(freeList_start + SEGLIST10, (size_t) (block->next_free));
		else if (size <= LIST11_LIMIT)
			PUT(freeList_start + SEGLIST11, (size_t) (block->next_free));
		else if (size <= LIST12_LIMIT)
			PUT(freeList_start + SEGLIST12, (size_t) (block->next_free));
		else if (size <= LIST13_LIMIT)
			PUT(freeList_start + SEGLIST13, (size_t) (block->next_free));
		else
			PUT(freeList_start + SEGLIST14, (size_t) (block->next_free));
        
        if((block->next_free) != NULL)
			block->next_free->prev_free=NULL;
	}
	else if(block->next_free==NULL) //Last block of freeList
	{
        printf("it is last block in its list \n");
		block->prev_free->next_free=NULL;
	}
	else //in middle of freeList
	{
	    printf("in Middle of its list\n");
		block->prev_free->next_free=block->next_free;
		block->next_free->prev_free=block->prev_free;
	}
}


static void *find_fit(size_t asize)
{
	printf("Find_fit called with asize %zu\n",asize);
	size_t sizeatstart;
	char *bp = NULL;

	/* Segregated lists- Size breakdown */
	if (asize <= LIST1_LIMIT) {
		for (sizeatstart = 0; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST2_LIMIT) {
		for (sizeatstart = 1; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST3_LIMIT) {
		for (sizeatstart = 2; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST4_LIMIT) {
		for (sizeatstart = 3; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST5_LIMIT) {
		for (sizeatstart = 4; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST6_LIMIT) {
		for (sizeatstart = 5; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST7_LIMIT) {
		for (sizeatstart = 6; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST8_LIMIT) {
		for (sizeatstart = 7; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST9_LIMIT) {
		for (sizeatstart = 8; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST10_LIMIT) {
		for (sizeatstart = 9; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST11_LIMIT) {
		for (sizeatstart = 10; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST12_LIMIT) {
		for (sizeatstart = 11; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST13_LIMIT) {
		for (sizeatstart = 12; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else {
		sizeatstart = 13;
		if ((bp = find(sizeatstart, asize)) != NULL) {
			return bp;
		}
	}
	printf("All if else failed in find_fit \n");
	return bp;
}

/*
 * Function: find
 * Description: 
 Find searches through a particular size free list
 to find a possible free block >= size requested and returns
 pointer to a possible free block or NULL if none are found.
 */
static void *find(size_t sizeatstart, size_t actual_size)
{
	printf("Find called with sizeatstart %zu actual size %zu and freeList_start %p\n",sizeatstart,actual_size,freeList_start);
	char *current = NULL;
    block_t *current_f=NULL;
	/* Finding which list to look into */
	if (sizeatstart == 0)
		current = (char *) GET(freeList_start + SEGLIST1);
	else if (sizeatstart == 1)
		current = (char *) GET(freeList_start + SEGLIST2);
	else if (sizeatstart == 2)
		current = (char *) GET(freeList_start + SEGLIST3);
	else if (sizeatstart == 3)
		current = (char *) GET(freeList_start + SEGLIST4);
	else if (sizeatstart == 4)
		current = (char *) GET(freeList_start + SEGLIST5);
	else if (sizeatstart == 5)
		current = (char *) GET(freeList_start + SEGLIST6);
	else if (sizeatstart == 6)
		current = (char *) GET(freeList_start + SEGLIST7);
	else if (sizeatstart == 7)
		current = (char *) GET(freeList_start + SEGLIST8);
	else if (sizeatstart == 8)
		current = (char *) GET(freeList_start + SEGLIST9);
	else if (sizeatstart == 9)
		current = (char *) GET(freeList_start + SEGLIST10);
	else if (sizeatstart == 10)
		current = (char *) GET(freeList_start + SEGLIST11);
	else if (sizeatstart == 11)
		current = (char *) GET(freeList_start + SEGLIST12);
	else if (sizeatstart == 12)
		current = (char *) GET(freeList_start + SEGLIST13);
	else if (sizeatstart == 13)
		current = (char *) GET(freeList_start + SEGLIST14);

    current_f=(block_t *)current;
	printf("Current value current %p current_f %p \n",current,current_f);

	/* Finding available free block in list */
	while (current_f != NULL) {
		if (actual_size <= get_size(current_f) {
			break;
		}
		current_f = current_f->next_free;
	}
	if(current!=NULL)
            printf("Current where block will fit %p size %zu \n",current,GET_SIZE(HDRP(current)));
	else 
            printf("Current is null \n");
	return current;
}

 static void place(void *bp, size_t asize)
 {
     block_t * block=(block_t *)bp;
     printf("Place called with bp %p and asize %zu\n",bp,asize);
     size_t csize = get_size(block);
     printf("Asize %zu Csize %zu remainsize %zu\n",asize,csize,remainsize);
    
     freeList_del((block_f *)block,csize);
     
     if ((csize - asize) >= min_block_size)
     {
         printf("If entered of place \n");	
         write_header(block, asize, true);
         write_footer(block, asize, true);
         
         block_t *block_next=find_next(block);
         write_header(block_next, csize-asize, false);
         write_footer(block_next, csize-asize, false);
         
         freeList_LIFO_insert((block_f *)block_next,csize-asize);
     }
     else
     {
         write_header(block, csize, true);
         write_footer(block, csize, true);
     }
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
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
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
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}
