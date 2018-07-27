/*
 * Name: Sarthak Jain
 * Andrew ID: sarthak3
 * mm.c
 *
 * The below code is for a general purpose dynamic memory allocator. 
 * I have used Segregated free list with 14 different sized classes.
 * Whenever a request for malloc occurs, it is first rounded up to included header and meet alignment requirements.
 * Thereafter, according to the new size, classes are searched to get a first free block that can accommodate this request.
 * If a block is found, then it is removed from free list, spliced up if (free block size - requested size) >= minimum block size.
 * And then the newly freed block is added in the appropriate list.
 *
 * I have used a FIFO strategy to find a block and for insertion of a free block in the list. 
 * 
 * Free block structure
 * | block size | (PREVIOUSALLOCATION)|(CURRENTALLOCATION)|
 * | pointer to next free block				  |
 * | pointer to previous free block			  |
 * | Optional padding					  |
 * | block size | (PREVIOUSALLOCATION)|(CURRENTALLOCATION)|
 *
 *
 * Allocated block
 * | block size | (PREVIOUSALLOCATION)|(CURRENTALLOCATION)|
 * | Application requested size				  |
 * | Optional Padding					  |
 *
 *
 * I have stored each free list's starting and ending pointer on the heap itself at the very start when the heap is initialised
 * For each free list the header and pointer are present consecutively.
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
//#define DEBUG

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
static const size_t min_block_size =2*dsize ; // Minimum block size
static const size_t CHUNKSIZE = 512;    // requires (chunksize % 16 == 0)

//static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

/* What is the correct alignment? */
#define ALIGNMENT dsize

/* Variables used as offsets for
   segregated lists headers */
#define SEGLIST1     0
#define SEGLIST2     dsize
#define SEGLIST3     2*dsize
#define SEGLIST4     3*dsize
#define SEGLIST5     4*dsize
#define SEGLIST6     5*dsize
#define SEGLIST7     6*dsize
#define SEGLIST8     7*dsize
#define SEGLIST9     8*dsize
#define SEGLIST10    9*dsize
#define SEGLIST11    10*dsize
#define SEGLIST12    11*dsize
#define SEGLIST13    12*dsize
#define SEGLIST14    13*dsize

/* Maximum size limit of each list */
#define LIST1_LIMIT      32
#define LIST2_LIMIT      64
#define LIST3_LIMIT      128
#define LIST4_LIMIT      256
#define LIST5_LIMIT      512
#define LIST6_LIMIT      1024
#define LIST7_LIMIT      2048
#define LIST8_LIMIT      4096
#define LIST9_LIMIT      8192
#define LIST10_LIMIT     16384
#define LIST11_LIMIT     32768
#define LIST12_LIMIT     65536
#define LIST13_LIMIT     131072

#define TOTALLIST   14
#define CURRENTALLOCATED   1
#define PREVIOUSALLOCATED  2
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
char *freeList_end=NULL;

static void PUT(char *p,size_t val);
static block_t *extend_heap(size_t size);
static block_t *coalesce(block_t *block);
static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);
static void freeList_LIFO_insert(block_f *block,size_t size);
static void freeList_FIFO_insert(block_f *block,size_t size);
static void freeList_del(block_f *block,size_t size);
static bool extract_alloc(word_t header);
static size_t get_alloc(block_t *block);
static size_t GET_PREV_ALLOC(block_t *block);

static size_t get_size(block_t *block);
static size_t GET(char *p);
static void *find_fit(size_t asize);
static void *find_best(size_t sizeatstart, size_t actual_size);
static void *find(size_t sizeatstart, size_t actual_size);
static size_t get_payload_size(block_t *block);

static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, size_t alloc);
static void place(void *bp, size_t asize);
static size_t MAX(size_t x, size_t y);
static block_t *payload_to_header(void *bp);
static void write_footer(block_t *block, size_t size, size_t alloc);
static void write_header(block_t *block, size_t size, size_t alloc);
static size_t extract_size(word_t word);
static char *HDRP(block_t *block);
static char *FTRP(block_t *block);

//returns pointer to header of the block
static char *HDRP(block_t *block)
{
	return (char *)block;
}

//returns pointer to footer of the block
static char *FTRP(block_t *block)
{
	return (char *)((char *)block + get_size(block) - wsize);
}

/* Read and write 8 bytes at address p */
static size_t GET(char *p)
{
    return (*((size_t*) (p)));   
}

//returns allocation status of previous block
static size_t GET_PREV_ALLOC(block_t *block)
{
	return ((block->header) & 0x2);	
}

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
static word_t pack(size_t size, size_t alloc)
{
    return (size | alloc);
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
    dbg_printf("mm_init called \n");
    
    freeList_start=(char *)(mem_sbrk(14*dsize));
    freeList_end = freeList_start + wsize;
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
	
	PUT(freeList_end + SEGLIST1, (size_t) NULL);
	PUT(freeList_end + SEGLIST2, (size_t) NULL);
	PUT(freeList_end + SEGLIST3, (size_t) NULL);
	PUT(freeList_end + SEGLIST4, (size_t) NULL);
	PUT(freeList_end + SEGLIST5, (size_t) NULL);
	PUT(freeList_end + SEGLIST6, (size_t) NULL);
	PUT(freeList_end + SEGLIST7, (size_t) NULL);
	PUT(freeList_end + SEGLIST8, (size_t) NULL);
	PUT(freeList_end + SEGLIST9, (size_t) NULL);
	PUT(freeList_end + SEGLIST10, (size_t) NULL);
	PUT(freeList_end + SEGLIST11, (size_t) NULL);
	PUT(freeList_end + SEGLIST12, (size_t) NULL);
	PUT(freeList_end + SEGLIST13, (size_t) NULL);
	PUT(freeList_end + SEGLIST14, (size_t) NULL);
	
    dbg_printf("FreeList_start initialised %p FreeList_end %p\n",freeList_start,freeList_end);
    
    word_t *start = (word_t *)(mem_sbrk(2*wsize));
    if (start == (void *)-1) 
    {
        return false;
    }
    start[0] = pack(0, 1); // Prologue footer
    start[1] = pack(0, PREVIOUSALLOCATED | CURRENTALLOCATED); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start=(block_t *) &(start[1]);
    dbg_printf("Heap_start initialised%p\n",heap_start);
    
    dbg_printf("Calling extend heap from mm_init \n");
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
    dbg_printf("Malloc called with size %zu\n",size);
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
    dbg_printf("Requested Size %zu allocating size %zu\n",size,asize);
    
    //dbg_printf("Calling find_fit\n");
	/* Search through heap for possible fit */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		//dbg_printf("Returning from malloc %p \n",bp+wsize);
		return bp+wsize;
	}
    dbg_printf("No fit found, calling extend heap \n");
	/* If no fit, get more memory and allocate memory */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize)) == NULL)
		return NULL;
	place(bp, asize);		
	return bp+wsize;
}

/*
 * free
 */
void free (void *ptr) {
    //dbg_printf("Free called %p\n",ptr);
    if (ptr == NULL)
    {
        return;
    }
    block_t *block = payload_to_header(ptr);
    dbg_printf("Free called for block pointer %p\n",block);
	size_t size = get_size(block);

    write_header(block, size, GET_PREV_ALLOC(block));
    write_footer(block, size, GET_PREV_ALLOC(block));
    write_header(find_next(block),get_size(find_next(block)),get_alloc(find_next(block)));
    
	/* Add free block to appropriate segregated list */
	//freeList_LIFO_insert((block_f *)block, size);
	freeList_FIFO_insert((block_f *)block, size);
	dbg_printf("after call of FIFO insert in free block next %p and its size %zu\n",find_next(block),get_size(find_next(block)));
	//dbg_printf("Calling coalesce from free\n");
	coalesce((block_t *)block);
	//dbg_printf("Returned from coalesce in free \n");
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
	dbg_printf("Printing Heap blocks \n");
	dbg_printf("Heap size %zu \n",mem_heapsize());
	block_t *i;
	block_f *f=NULL;
	block_f *slow_ptr=NULL;
	block_f *fast_ptr=NULL;
	char *listpointer = NULL;
	unsigned sizeatstart = 0;
	unsigned minimumblocksize = 0;
	unsigned maximumblocksize = 0;
	unsigned int total_free_block=0;
	unsigned int total_free_block_list=0;
	for(i=heap_start;get_size(i) > 0; i = find_next(i))
	{
		if(get_alloc(i))
			dbg_printf("Heap Block %p size %zu\n",i,get_size(i));
		
		if(!get_alloc(i))
		{
			total_free_block++;
			block_f *free_block=(block_f *)i;
			dbg_printf("FreeList Block %p size %zu\n",i,get_size(i));
			//check for free block header and footer mismatch
			if(GET(HDRP(i)) != GET(FTRP(i)))
			{
				dbg_printf("Free block %p header and footer mismatch \n",i);
				return false;
			}
			//check for free block prev and next pointer consistency
			if(free_block->next_free!=NULL && free_block->next_free->prev_free!=free_block)
			   {
				   dbg_printf("Free block %p next pointer is incosistent \n",i);
				   return false;
			   }
			if(free_block->prev_free!=NULL && free_block->prev_free->next_free!=free_block)
			   {
				   dbg_printf("Free block %p prev pointer is inconsistent \n",i);
				   return false;
			   }
			   //check for two consecutive free blocks presence
			if(find_next(i)!=NULL && get_alloc(find_next(i))!=1)
			   {
				   dbg_printf("Two consecutive free block %p and %p present \n",i,find_next(i));
				   return false;
			   }
			
		}
		//alignment check
		if(!aligned((char *)i+wsize))
		   {
			   dbg_printf("Block pointer %p isn't aligned \n",i);
			   return false;
		   }
		// presence inside heap check
		if(!in_heap((char *)i+wsize))
		{
			dbg_printf("Block pointer %p isn't in heap \n",i);
			return false;
		}
		//previous/next allocation/free bit consistency check
		if(get_alloc(i)==0) 
		{
			if(GET_PREV_ALLOC(find_next(i))!=0)
			{
				dbg_printf("Bit inconsistency ! block ponter %p current alloc bit %zu and next block %p prev alloc %zu \n",i,get_alloc(i),find_next(i),GET_PREV_ALLOC(find_next(i)));
				return false;
			}
		}
		if(get_alloc(i)==1)
		{
			if(GET_PREV_ALLOC(find_next(i))!=2)
			{
				dbg_printf("Bit inconsistency ! block ponter %p current alloc bit %zu and next block %p prev alloc %zu \n",i,get_alloc(i),find_next(i),GET_PREV_ALLOC(find_next(i)));
				return false;
			}
		}
	}
	dbg_printf("All blocks printed now checking for each free block's range \n");	
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
		f=(block_f *)listpointer;
		slow_ptr=f;
		if(slow_ptr)
			fast_ptr=slow_ptr->next_free;
		while (f != NULL) 
        	{
			if(!(get_alloc((block_t *)f)))
			{
				total_free_block_list++;
				//checking for each free block to be in correct seglist
				if (!(minimumblocksize < get_size((block_t *)f) && get_size((block_t *)f) <= maximumblocksize)) 
            			{
					dbg_printf("Free block pointer %p is not in the appropriate list", f);
                			return false;
				}
			}
			f=f->next_free;
		}
		//checking for presence of loop in a free list
		while(slow_ptr && fast_ptr && fast_ptr->next_free)
		{
			slow_ptr=slow_ptr->next_free;
			fast_ptr=fast_ptr->next_free->next_free;
			if(slow_ptr==fast_ptr)
			{
				dbg_printf("Found loop in list %d \n",sizeatstart);
				return false;
			}
		}
	}
	//checking for total count of free block via heap traversal and seglist traversal
	if(total_free_block != total_free_block_list)
	{
		dbg_printf("total free block inconsistency block traversal count %u list traversal count %u \n",total_free_block,total_free_block_list);
		return false;
	}
	return true;
}

static block_t *extend_heap(size_t size) 
{
    dbg_printf("Extend heap called with size %zu\n",size);
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size, GET_PREV_ALLOC(block));
    write_footer(block, size, GET_PREV_ALLOC(block));
    dbg_printf("new extend heap block address %p size %zu and original bp %p\n",block,size,bp);
	
    //dbg_printf("Calling freeList_FIFO_insert in extend heap \n");
    /* Add to segregated list */
	freeList_FIFO_insert((block_f *)block, size);
	dbg_printf("Returned from freeList_FIFO_insert in extend heap \n");
    
    // Create new epilogue header
    block_t *block_next = find_next(block);
    dbg_printf("new epilogue %p\n",block_next);
    write_header(block_next, 0, 1);
    
    //dbg_printf("Calling coalesce from extend_heap\n");
    // Coalesce in case the previous block was free
    return coalesce((block_t *)block);
}

/*
 * <what does coalesce do?>
 */
static block_t *coalesce(block_t * block) 
{
	dbg_printf("Coalesce called\n");
	block_t *block_next = find_next(block);
    block_t *block_prev = find_prev(block);
    block_f *block_free=(block_f *)block;
    block_f *block_next_free=(block_f *)block_next;
    block_f *block_prev_free=(block_f *)block_prev;
    size_t prev_alloc = GET_PREV_ALLOC(block);
	size_t next_alloc = get_alloc(block_next);
    size_t size = get_size(block);
	
    if (prev_alloc && next_alloc)              // Case 1
    {
	    dbg_printf("Case 1 entered \n");
    	size_t block_next_size=get_size(block_next);
		write_header(block_next,block_next_size,1);
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
	    dbg_printf("Case 2 entered \n");
    	size_t block_next_size=get_size(block_next);
        freeList_del(block_free,size);
	    freeList_del(block_next_free,block_next_size);
	    
        size += block_next_size;
        write_header(block, size, prev_alloc);
        write_footer(block, size, prev_alloc);
	    //dbg_printf("block %p size %zu\n",block,block->header);
	    freeList_FIFO_insert(block_free,size);
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
	    dbg_printf("Case 3 entered \n");
  	  	size_t block_prev_size=get_size(block_prev);
    	size_t block_next_size=get_size(block_next);
        
		freeList_del(block_free,size);
	    freeList_del(block_prev_free,block_prev_size);
        
        size += block_prev_size;
	write_header(block_prev, size, GET_PREV_ALLOC(block_prev));
        write_footer(block_prev, size, GET_PREV_ALLOC(block_prev));
	write_header(block_next,block_next_size,1);
      	//dbg_printf("block %p size %zu\n",block_prev,block_prev->header);    
	freeList_FIFO_insert(block_prev_free,size);
	        
        block=block_prev;
    }

    else                                        // Case 4
    {
	    dbg_printf("Case 4 entered \n");
  	  	size_t block_prev_size=get_size(block_prev);
    	size_t block_next_size=get_size(block_next);
        freeList_del(block_free,size);
        freeList_del(block_next_free,block_next_size);
	    freeList_del(block_prev_free,block_prev_size);
        
        size += block_next_size + block_prev_size;
        write_header(block_prev, size, GET_PREV_ALLOC(block_prev));
        write_footer(block_prev, size, GET_PREV_ALLOC(block_prev));
		//dbg_printf("block %p sze %zu \n",block_prev,block_prev->header);
	    
	freeList_FIFO_insert(block_prev_free,size);
        block=block_prev;
    }
	dbg_printf("Returning from coalesce \n");
    return block;
}

static void freeList_FIFO_insert(block_f *block,size_t size)
{
	dbg_printf("freelist_fifo entered with blck pointer %p and size %zu \n",block,size);
	char *listend;
	char *segstart;
	char *segend;
	
	if (size <= LIST1_LIMIT) {
		segstart = freeList_start + SEGLIST1;
		segend = freeList_end + SEGLIST1;
		listend = (char *) GET(segend);

	} else if (size <= LIST2_LIMIT) {
		segstart = freeList_start + SEGLIST2;
		segend = freeList_end + SEGLIST2;
		listend = (char *) GET(segend);

	} else if (size <= LIST3_LIMIT) {
		segstart = freeList_start + SEGLIST3;
		segend = freeList_end + SEGLIST3;
		listend = (char *) GET(segend);

	} else if (size <= LIST4_LIMIT) {
		segstart = freeList_start + SEGLIST4;
		segend = freeList_end + SEGLIST4;
		listend = (char *) GET(segend);

	} else if (size <= LIST5_LIMIT) {
		segstart = freeList_start + SEGLIST5;
		segend = freeList_end + SEGLIST5;
		listend = (char *) GET(segend);

	} else if (size <= LIST6_LIMIT) {
		segstart = freeList_start + SEGLIST6;
		segend = freeList_end + SEGLIST6;
		listend = (char *) GET(segend);

	} else if (size <= LIST7_LIMIT) {
		segstart = freeList_start + SEGLIST7;
		segend = freeList_end + SEGLIST7;
		listend = (char *) GET(segend);

	} else if (size <= LIST8_LIMIT) {
		segstart = freeList_start + SEGLIST8;
		segend = freeList_end + SEGLIST8;
		listend = (char *) GET(segend);

	} else if (size <= LIST9_LIMIT) {
		segstart = freeList_start + SEGLIST9;
		segend = freeList_end + SEGLIST9;
		listend = (char *) GET(segend);

	} else if (size <= LIST10_LIMIT) {
		segstart = freeList_start + SEGLIST10;
		segend = freeList_end + SEGLIST10;
		listend = (char *) GET(segend);

	} else if (size <= LIST11_LIMIT) {
		segstart = freeList_start + SEGLIST11;
		segend = freeList_end + SEGLIST11;
		listend = (char *) GET(segend);

	} else if (size <= LIST12_LIMIT) {
		segstart = freeList_start + SEGLIST12;
		segend = freeList_end + SEGLIST12;
		listend = (char *) GET(segend);

	} else if (size <= LIST13_LIMIT) {
		segstart = freeList_start + SEGLIST13;
		segend = freeList_end + SEGLIST13;
		listend = (char *) GET(segend);

	} else {
		segstart = freeList_start + SEGLIST14;
		segend = freeList_end + SEGLIST14;
		listend = (char *) GET(segend);
	}
	dbg_printf("segstart %p segend %p listend %p\n",segstart,segend,listend);
	if(listend==NULL)
    	{
        	dbg_printf("If of freeList_fifo_insert \n");
        	//set current block as head
        	PUT(segstart,(size_t)(block));
		PUT(segend,(size_t)(block));
        	dbg_printf("segstart %p segend %p size %zu \n", segstart, segend,(size_t)block);
        	block->prev_free=NULL;
        	block->next_free=NULL;
    	}
	else
	{
		dbg_printf("Else of fifo insert \n");
       		block_f * listend_blockf=(block_f *)listend;
		
		block->prev_free=listend_blockf;
		block->next_free=NULL;
		listend_blockf->next_free=block;
		PUT(segend,(size_t)block);
	}
}

static void freeList_del(block_f *block,size_t size)
{
	dbg_printf("freeList_del called for block %p and size %zu \n",block,size);
	if(block->prev_free==NULL) //at start of freeList
	{
		dbg_printf("block at start of freelist\n");
		
        	if (size <= LIST1_LIMIT)
		{
			if( block->next_free==NULL  )
			{
				PUT(freeList_end + SEGLIST1, (size_t)NULL);
				PUT(freeList_start + SEGLIST1,(size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST1, (size_t) (block->next_free));
		}
		else if (size <= LIST2_LIMIT)
		{
			if( block->next_free==NULL  )
			{
				PUT(freeList_end + SEGLIST2, (size_t)NULL);
				PUT(freeList_start + SEGLIST2, (size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST2, (size_t) (block->next_free));
		}
		else if (size <= LIST3_LIMIT)
		{
			if( block->next_free==NULL )
			{
				PUT(freeList_end + SEGLIST3, (size_t)NULL);
				PUT(freeList_start + SEGLIST3,(size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST3, (size_t) (block->next_free));
		}
		else if (size <= LIST4_LIMIT)
		{
			if( block->next_free==NULL  )
			{
				PUT(freeList_end + SEGLIST4, (size_t)NULL);
				PUT(freeList_start + SEGLIST4, (size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST4, (size_t) (block->next_free));
		}
		else if (size <= LIST5_LIMIT)
		{
			if( block->next_free==NULL  )
			{
				PUT(freeList_end + SEGLIST5, (size_t)NULL);
				PUT(freeList_start + SEGLIST5,(size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST5, (size_t) (block->next_free));
		}
		else if (size <= LIST6_LIMIT)
		{
			if( block->next_free==NULL  )
			{
				PUT(freeList_end + SEGLIST6, (size_t)NULL);
				PUT(freeList_start + SEGLIST6,(size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST6, (size_t) (block->next_free));
		}
		else if (size <= LIST7_LIMIT)
		{
			if( block->next_free==NULL  )
			{
				PUT(freeList_end + SEGLIST7, (size_t)NULL);
				PUT(freeList_start + SEGLIST7,(size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST7, (size_t) (block->next_free));
		}
		else if (size <= LIST8_LIMIT)
		{
			if( block->next_free==NULL  )
			{
				PUT(freeList_end + SEGLIST8, (size_t)NULL);
				PUT(freeList_start + SEGLIST8,(size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST8, (size_t) (block->next_free));
		}
		else if (size <= LIST9_LIMIT)
		{
			if( block->next_free==NULL  )
			{
				PUT(freeList_end + SEGLIST9, (size_t)NULL);
				PUT(freeList_start + SEGLIST9,(size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST9, (size_t) (block->next_free));
		}
		else if (size <= LIST10_LIMIT)
		{
			if( block->next_free==NULL  )
			{
				PUT(freeList_end + SEGLIST10, (size_t)NULL);
				PUT(freeList_start + SEGLIST10,(size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST10, (size_t) (block->next_free));
		}
		else if (size <= LIST11_LIMIT)
		{
			if( block->next_free==NULL  )
			{
				PUT(freeList_end + SEGLIST11, (size_t)NULL);
				PUT(freeList_start + SEGLIST11,(size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST11, (size_t) (block->next_free));
		}
		else if (size <= LIST12_LIMIT)
		{
			if( block->next_free==NULL  )
			{
				PUT(freeList_end + SEGLIST12, (size_t)NULL);
				PUT(freeList_start + SEGLIST12,(size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST12, (size_t) (block->next_free));
		}
		else if (size <= LIST13_LIMIT)
		{
			if( block->next_free==NULL  )
			{
				PUT(freeList_end + SEGLIST13, (size_t)NULL);
				PUT(freeList_start + SEGLIST13,(size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST13, (size_t) (block->next_free));
		}
		else
		{
			if( block->next_free==NULL  )
			{
				PUT(freeList_end + SEGLIST14, (size_t)NULL);
				PUT(freeList_start + SEGLIST14,(size_t)NULL);
			}
			else
				PUT(freeList_start + SEGLIST14, (size_t) (block->next_free));
		}
        	
        	if((block->next_free) != NULL)
		{
			block->next_free->prev_free=NULL;
			block->next_free=NULL;
		}
	}
	else if(block->next_free==NULL) //Last block of freeList
	{
		if (size <= LIST1_LIMIT)
			PUT(freeList_end + SEGLIST1, (size_t) (block->prev_free));
		else if (size <= LIST2_LIMIT)
			PUT(freeList_end + SEGLIST2, (size_t) (block->prev_free));
		else if (size <= LIST3_LIMIT)
			PUT(freeList_end + SEGLIST3, (size_t) (block->prev_free));
		else if (size <= LIST4_LIMIT)
			PUT(freeList_end + SEGLIST4, (size_t) (block->prev_free));
		else if (size <= LIST5_LIMIT)
			PUT(freeList_end + SEGLIST5, (size_t) (block->prev_free));
		else if (size <= LIST6_LIMIT)
			PUT(freeList_end + SEGLIST6, (size_t) (block->prev_free));
		else if (size <= LIST7_LIMIT)
			PUT(freeList_end + SEGLIST7, (size_t) (block->prev_free));
		else if (size <= LIST8_LIMIT)
			PUT(freeList_end + SEGLIST8, (size_t) (block->prev_free));
		else if (size <= LIST9_LIMIT)
			PUT(freeList_end + SEGLIST9, (size_t) (block->prev_free));
		else if (size <= LIST10_LIMIT)
			PUT(freeList_end + SEGLIST10, (size_t) (block->prev_free));
		else if (size <= LIST11_LIMIT)
			PUT(freeList_end + SEGLIST11, (size_t) (block->prev_free));
		else if (size <= LIST12_LIMIT)
			PUT(freeList_end + SEGLIST12, (size_t) (block->prev_free));
		else if (size <= LIST13_LIMIT)
			PUT(freeList_end + SEGLIST13, (size_t) (block->prev_free));
		else
			PUT(freeList_end + SEGLIST14, (size_t) (block->prev_free));
        dbg_printf("it is last block in its list \n");
		block->prev_free->next_free=NULL;
		block->prev_free=NULL;
	}
	else //in middle of freeList
	{
	    dbg_printf("in Middle of its list\n");
		block->prev_free->next_free=block->next_free;
		block->next_free->prev_free=block->prev_free;
		block->prev_free=NULL;
		block->next_free=NULL;
	}
}

/*
* find fit determines the appropriate seglist to start searching for a block which can fit asize sized block
*/
static void *find_fit(size_t asize)
{
	dbg_printf("Find_fit called with asize %zu\n",asize);
	size_t sizeatstart;
	char *bp = NULL;

	/* Segregated lists*/
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
		if ((bp = find(sizeatstart, asize)) != NULL) 
			return bp;
	}
	dbg_printf("All if else failed in find_fit \n");
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
	dbg_printf("Find called with sizeatstart %zu actual size %zu and freeList_start %p\n",sizeatstart,actual_size,freeList_start);
	char *current = NULL;
    block_t *current_f=NULL;
	block_f *current_free=NULL;
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
	
	/* Finding available free block in list */
	while (current_f != NULL)
	{
		current_free=(block_f *)current_f;
		if (actual_size <= get_size(current_f))
			break;	
		current_f = (block_t *)(current_free->next_free);
	}
	if(current_f!=NULL)
            dbg_printf("Current where block will fit %p size %zu \n",current_f,get_size(current_f));
	else 
            dbg_printf("Current is null \n");
	return current_f;
}

 static void place(void *bp, size_t asize)
 {
     block_t * block=(block_t *)bp;
     size_t csize = get_size(block);
     dbg_printf("place called with bp %p requesting size %zu with passed block size %zu\n",bp,asize,csize);
    
     freeList_del((block_f *)block,csize);
     
     if ((csize - asize) >= min_block_size)
     {
         dbg_printf("If entered of place \n");	
         write_header(block, asize, (GET_PREV_ALLOC(block) | CURRENTALLOCATED));
         
         block_t *block_next=find_next(block);
         dbg_printf("Block_next %p\n",block_next);
	 write_header(block_next, csize-asize, PREVIOUSALLOCATED);
         write_footer(block_next, csize-asize, PREVIOUSALLOCATED);
         
	 freeList_FIFO_insert((block_f *)block_next,csize-asize);
     }
     else
     {
         write_header(block, csize, (GET_PREV_ALLOC(block) | CURRENTALLOCATED));
		 block_t *block_next=find_next(block);
		 write_header(block_next,get_size(block_next),(PREVIOUSALLOCATED | get_alloc(block_next)));
		 if(!get_alloc(block_next))
			write_footer(block_next,get_size(block_next), (PREVIOUSALLOCATED | get_alloc(block_next)));
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
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (size_t)(word & size_mask);
}
/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
	//dbg_printf("block %p its size %zu\n",block,block->header);
    return extract_size(block->header);
}


/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static size_t get_alloc(block_t *block)
{
    return ((block->header) & 0x1);
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
	//dbg_printf("find_prev footer called with block %p and its headwer address is %p an prev footer %p\n",block,&(block->header),((&(block->header))-1));
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
static void write_header(block_t *block, size_t size, size_t alloc)
{
    block->header = pack(size, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, size_t alloc)
{
    //dbg_printf("write footer called with block %p, its footer is %p\n",block,((block->payload)+get_size(block)-dsize));
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
