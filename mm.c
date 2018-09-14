/*
 * Name: Sarthak Jain
 * Andrew ID: sarthak3
 * mm.c
 *
 * The below code is for a general purpose dynamic memory allocator. 
 * I have used Segregated free list with 15 different sized classes.
 * Whenever a request for malloc occurs, it is first rounded up to included header and meet alignment requirements.
 * Thereafter, according to the new size, classes are searched to get a first free block that can accommodate this request.
 * If a block is found, then it is removed from free list, spliced up if (free block size - requested size) >= minimum block size.
 * And then the newly freed block is added in the appropriate list.
 *
 * I have used a FIFO strategy to find a block and for insertion of a free block in the list. 
 * 
 * Free block structure
 * | block size | (PREVIOUSALLOCATION)|(CURRENTALLOCATION)|
 * | pointer to next free block				  			  |
 * | pointer to previous free block			  			  |
 * | Optional padding					  				  |
 * | block size | (PREVIOUSALLOCATION)|(CURRENTALLOCATION)|
 *
 *
 * Allocated block
 * | block size | (PREVIOUSALLOCATION)|(CURRENTALLOCATION)|
 * | Application requested size				  			  |
 * | Optional Padding					  				  |
 *
 * 
 * The segregated free list for 16B blocks would be singly linked list. So need for prev pointer for this.
 * Free 16B block
 * | block size | (PREVIOUSALLOCATION)|(CURRENTALLOCATION)|
 * | pointer to next free block				  		      |
 *
 * Allocated 16B block
 * | block size | (PREVIOUSALLOCATION)|(CURRENTALLOCATION)|
 * | Application requested size				  			  |
 * 
 * I have stored each free list's starting and ending pointer on the heap itself at the very start when the heap is initialised
 * For each free list the header and pointer are present consecutively.
 *
 *
 * We can assume that Segregated Free Lists from SEGLIST1 to SEGLIST14 are doubly linked list with previous and next pointer
 * SEGLIST 0 is the only segregated free list which is Singly linked list and has only next pointer. 
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
static const size_t min_block_size =dsize ; // Minimum block size
static const size_t CHUNKSIZE = 4096;    // requires (chunksize % 16 == 0)

//static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

/* What is the correct alignment? */
#define ALIGNMENT dsize

/* Variables used as offsets for
   segregated lists headers */
#define SEGLIST0     0
#define SEGLIST1     dsize
#define SEGLIST2     2*dsize
#define SEGLIST3     3*dsize
#define SEGLIST4     4*dsize
#define SEGLIST5     5*dsize
#define SEGLIST6     6*dsize
#define SEGLIST7     7*dsize
#define SEGLIST8     8*dsize
#define SEGLIST9     9*dsize
#define SEGLIST10    10*dsize
#define SEGLIST11    11*dsize
#define SEGLIST12    12*dsize
#define SEGLIST13    13*dsize
#define SEGLIST14    14*dsize

/* Maximum size limit of each list */
#define LIST0_LIMIT	     16
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

#define TOTALLIST   15
#define CURRENTALLOCATED   1
#define PREVIOUSALLOCATED  2
/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

typedef struct block
{
    /* Header contains size + previous and current allocation bits */
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
	/* Header contains size + previous and current allocation status*/
    word_t header;
    struct free_block *next_free;
    struct free_block *prev_free;
} block_f;

typedef struct free_sixteen_block
{
	/* Header contains size + previous and current allocation status */
	word_t header;
	struct free_sixteen_block *next_free;
} block_f_sixteen;

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
	//dbg_printf("FTRP value for pointer %p %zu",block,*(word_t *)(block->payload + get_size(block)-dsize));
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
 * mm_init creates an initial empty heap of free CHUNKSIZE
 * Also it initializes the freeList_start and end pointers
 * of each segregated list on the heap.
 *
 * Additionally, Prologue header and footer and epilogue header
 * is also initialized with size 0 and current allocation 1.
 */
bool mm_init(void) {
    // Create the initial empty heap 
    dbg_printf("mm_init called \n");
    
    freeList_start=(char *)(mem_sbrk(15*dsize));
    freeList_end = freeList_start + wsize;
    if (freeList_start == (void *)-1) 
    {
        return false;
    }
    
    /* Initializing the segregated list pointers on heap */
	PUT(freeList_start + SEGLIST0, (size_t) NULL);
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
	
	PUT(freeList_end + SEGLIST0, (size_t) NULL);
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
    
    word_t *start = (word_t *)(mem_sbrk(4*wsize));
    if (start == (void *)-1) 
    {
        return false;
    }
    start[0] = pack(0, 1); // Prologue header
    start[1] = pack(0, 1); // Prologue footer
	start[2] = pack(0,1); //optional padding for alignment
    start[3] = pack(0, PREVIOUSALLOCATED | CURRENTALLOCATED); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start=(block_t *) &(start[3]);
    dbg_printf("Heap_start initialised%p\n",heap_start);
    
    dbg_printf("Calling extend heap from mm_init \n");
    if (extend_heap(CHUNKSIZE) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * malloc: This is the main function that fulfills the
 * memory requests. The requested size if first adjusted
 * to accommodate header and meet alignment request.
 * Then this new size is allocated and a pointer to payload
 * is returned.
 */
void *malloc (size_t size) {
    
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
	if(size<=wsize)
		asize=min_block_size;
	else
		asize = round_up(size + wsize, dsize);
    
    
	/* Search through segregated lists for possible fit */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp+wsize; //returning +wsize since bp points to header of assigned block and not payload.
	}
    
	/* If no fit, get more memory and allocate memory */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize)) == NULL)
		return NULL;
	place(bp, asize);		
	return bp+wsize;
}

/*
 * free : This function frees the allocated requests by malloc.
 * It modifies the header and footer of the free block to inlcude
 * the size and previous and current allocation status.
 * Also, the header of next block in memomry of current block
 * is modified to show that its previous block is now free.
 */
void free (void *ptr) {
    
    if (ptr == NULL)
    {
        return;
    }
    block_t *block = payload_to_header(ptr);
	block_t *block_next=find_next(block);
	size_t size = get_size(block);

    write_header(block, size, GET_PREV_ALLOC(block));
	
	//writing footer of the current free block only if the size is grater than 16B
	if(size > dsize)
    	write_footer(block, size, GET_PREV_ALLOC(block));
    
	//modify header of next block to denote that its previous block is now free.
	write_header(block_next,get_size(block_next),get_alloc(block_next));
    
	/* Add free block to appropriate segregated list */
	freeList_FIFO_insert((block_f *)block, size);
	coalesce((block_t *)block);	
}

/*
 * realloc: It changes the size of block allocated by malloc
 * to new given size. Depending on whether the new size is 0,
 * greater than or less than the old allocated size, the appropriate
 * action is taken.
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
 * A function that checks all the invariants of my dynamic memory allocator.
 * It checks for each block's alignment and whether they are in limits of heap
 * It checks for previous and current bit consistency.
 * for free blocks we check for total count of free block when traversing entire heap with
 * total count by just traversing free list
 * also we check for previous and next pointer consistencies.
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
		//printing starting address of each heap block along with its size
		//and previous and current allocation present in its header
		if(get_alloc(i))
			dbg_printf("Heap Block %p size %zu prev allocation %zu current allocation %zu\n",i,get_size(i),GET_PREV_ALLOC(i),get_alloc(i));
		
		//Doing the below only for free blocks
		if(!get_alloc(i))
		{
			total_free_block++;
			block_f *free_block=(block_f *)i;
			dbg_printf("FreeList Block %p size %zu prev allocation %zu current allocation %zu \n",i,get_size(i),GET_PREV_ALLOC(i),get_alloc(i));
			
			//check for free block header and footer mismatch
			//only if free block size is greater than dsize
			if(get_size(i) > dsize && GET(HDRP(i)) != GET(FTRP(i)))
			{
				dbg_printf("Free block %p header %p size %zu and footer %p size %zu mismatch \n",i,HDRP(i),GET(HDRP(i)),FTRP(i),GET(FTRP(i)));
				return false;
			}
			//check for free block prev and next pointer consistency
			// can check for net pointer in 16B as 16B free block stores next pointer
			if( free_block->next_free!=NULL && get_size( (block_t *)(free_block->next_free) ) > dsize && free_block->next_free->prev_free!=free_block)
			   {
				   dbg_printf("Free block %p next pointer is incosistent \n",i);
				   return false;
			   }
			//checking for previous pointer consistency only for free block size > dsize
			if(get_size(i) > dsize && free_block->prev_free!=NULL && free_block->prev_free->next_free!=free_block)
			   {
				   dbg_printf("Free block %p prev pointer is %p whose next pointer is %p inconsistent \n",i,free_block->prev_free,free_block->prev_free->next_free);
				   return false;
			   }
			   //check for two consecutive free blocks presence
			if(find_next(i)!=NULL && get_alloc(find_next(i))!=1)
			   {
				   dbg_printf("Two consecutive free block %p and %p present \n",i,find_next(i));
				   return false;
			   }			
		}
		
		//alignment check for each block
		if(!aligned((char *)i+wsize))
		   {
			   dbg_printf("Block pointer %p isn't aligned \n",i);
			   return false;
		   }
		// presence inside heap check for each block
		if(!in_heap((char *)i+wsize))
		{
			dbg_printf("Block pointer %p isn't in heap \n",i);
			return false;
		}
		
		//previous/next allocation/free bit consistency check for each block
		// If current allocation is 0 then next block's prev allocation should also be 0
		if(get_alloc(i)==0) 
		{
			if(GET_PREV_ALLOC(find_next(i))!=0)
			{
				dbg_printf("Bit inconsistency ! block ponter %p current alloc bit %zu and next block %p prev alloc %zu \n",i,get_alloc(i),find_next(i),GET_PREV_ALLOC(find_next(i)));
				return false;
			}
		}
		// If current allocation is 1 then next block's prev allocation should also be 1
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
			dbg_printf("sizeattart %d \n",sizeatstart);
			if (sizeatstart == 0) {
				listpointer = (char *) GET(freeList_start + SEGLIST0);
				minimumblocksize = 0;
				maximumblocksize = LIST0_LIMIT;
			} else if (sizeatstart == 1) {
				listpointer = (char *) GET(freeList_start + SEGLIST1);
				minimumblocksize = LIST0_LIMIT;
				maximumblocksize = LIST1_LIMIT;
			} else if (sizeatstart == 2) {
				listpointer = (char *) GET(freeList_start + SEGLIST2);
				minimumblocksize = LIST1_LIMIT;
				maximumblocksize = LIST2_LIMIT;
			} else if (sizeatstart == 3) {
				listpointer = (char *) GET(freeList_start + SEGLIST3);
				minimumblocksize = LIST2_LIMIT;
				maximumblocksize = LIST3_LIMIT;
			} else if (sizeatstart == 4) {
				listpointer = (char *) GET(freeList_start + SEGLIST4);
				minimumblocksize = LIST3_LIMIT;
				maximumblocksize = LIST4_LIMIT;
			} else if (sizeatstart == 5) {
				listpointer = (char *) GET(freeList_start + SEGLIST5);
				minimumblocksize = LIST4_LIMIT;
				maximumblocksize = LIST5_LIMIT;
			} else if (sizeatstart == 6) {
				listpointer = (char *) GET(freeList_start + SEGLIST6);
				minimumblocksize = LIST5_LIMIT;
				maximumblocksize = LIST6_LIMIT;
			} else if (sizeatstart == 7) {
				listpointer = (char *) GET(freeList_start + SEGLIST7);
				minimumblocksize = LIST6_LIMIT;
				maximumblocksize = LIST7_LIMIT;
			} else if (sizeatstart == 8) {
				listpointer = (char *) GET(freeList_start + SEGLIST8);
				minimumblocksize = LIST7_LIMIT;
				maximumblocksize = LIST8_LIMIT;
			} else if (sizeatstart == 9) {
				listpointer = (char *) GET(freeList_start + SEGLIST9);
				minimumblocksize = LIST8_LIMIT;
				maximumblocksize = LIST9_LIMIT;
			} else if (sizeatstart == 10) {
				listpointer = (char *) GET(freeList_start + SEGLIST10);
				minimumblocksize = LIST9_LIMIT;
				maximumblocksize = LIST10_LIMIT;
			} else if (sizeatstart == 11) {
				listpointer = (char *) GET(freeList_start + SEGLIST11);
				minimumblocksize = LIST10_LIMIT;
				maximumblocksize = LIST11_LIMIT;
			} else if (sizeatstart == 12) {
				listpointer = (char *) GET(freeList_start + SEGLIST12);
				minimumblocksize = LIST11_LIMIT;
				maximumblocksize = LIST12_LIMIT;
			} else if (sizeatstart == 13){
				listpointer = (char *) GET(freeList_start + SEGLIST13);
				minimumblocksize = LIST12_LIMIT;
				maximumblocksize = LIST13_LIMIT;
			}
			else{
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
				total_free_block_list++;
				//checking for each free block to be in correct seglist
				if (!(minimumblocksize < get_size((block_t *)f) && get_size((block_t *)f) <= maximumblocksize)) 
            	{
							dbg_printf("Free block pointer %p is not in the appropriate list", f);
                			return false;
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

/*
* In case a malloc request for certain size is not able to be accommodated
* with present free blocks in free list. 
* We call extend heap to create new free memory of size maximum of requested v/s defined chunksize.
* After creating this new memory we call coalesce in case the previous continous chunk of memory in heap
* was also free. To not let two consecutive free memory present together.
*/ 
static block_t *extend_heap(size_t size) 
{
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
    
    /* Add to appropriate segregated list */
	freeList_FIFO_insert((block_f *)block, size);
    
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, 1);
    
    // Coalesce in case the previous block was free
    return coalesce((block_t *)block);
}

/*
 * Coalesce is for combining consecutive free blocks in memory to form
 * a single unified block of free memory. 
 * It is done so that in future if certain request come to allocate memory
 * which can be served by this unified block, it can be served and thus to
 * not call extend_heap.
 */
static block_t *coalesce(block_t * block) 
{
	dbg_printf("Coalesce called\n");
	size_t prev_alloc = GET_PREV_ALLOC(block);
   	size_t size = get_size(block);
	
	block_t *block_next = find_next(block);
	size_t next_alloc = get_alloc(block_next);
   	block_t *block_prev = NULL;
	
	// Since 16B free blocks doesn't have footer. 
	// I am taking the present passed starting block address - 2 * wsize 
	// Then i am checking if this calculated address is header of 16B free block
	// And if this 16B free block is free
	// And if this 16B free block is present in 16B segregated free list. 
	
	// The presence in segregated free list check is performed since
	// some garbage value was apparently satisfying dsize and free bit allocationg requirement
	// which was giving wrong results.
	// It indeed affects a bit of throughput
	block_f_sixteen *startp=(block_f_sixteen *)(GET(freeList_start+SEGLIST0));
	block_f_sixteen *headerp=(block_f_sixteen *)((&(block->header))-2);
	word_t *head=(&(block->header)) -2;
	size_t prev_size=extract_size(*head);
    
	while(prev_alloc == 0 && get_alloc( (block_t *)headerp )==0 &&startp!=NULL && prev_size==dsize && startp!=headerp)
	{
		startp=startp->next_free;	
	}
	
	if(startp!=headerp)
		block_prev=find_prev(block);
	else block_prev=(block_t *)((char *)block-dsize);
	
	// since free block of 16B doesn't have footer. And we know that 16B block is of dsize. So we manually check for size of block
	// whose address starts at current block's header address - 2 word before the header;
	
    block_f *block_free=(block_f *)block;
    block_f *block_next_free=(block_f *)block_next;
    block_f *block_prev_free=(block_f *)block_prev;
	
	
    if (prev_alloc && next_alloc)              // Case 1
    {
    	size_t block_next_size=get_size(block_next);
		//tell next block that its previous block is now free
		write_header(block_next,block_next_size,CURRENTALLOCATED);
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
    	size_t block_next_size=get_size(block_next);
        freeList_del(block_free,size);
	    freeList_del(block_next_free,block_next_size);
	    
        size += block_next_size;
        
		write_header(block, size, prev_alloc);
	    write_footer(block,size,prev_alloc);
		
	    freeList_FIFO_insert((block_f *)block,size);
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {   
  	  	size_t block_prev_size=get_size(block_prev);
    	size_t block_next_size=get_size(block_next);
        size_t prev_alloc_prev_block=GET_PREV_ALLOC(block_prev);
		
		freeList_del(block_free,size);
	    freeList_del(block_prev_free,block_prev_size);
         
        size += block_prev_size;
		
		write_header(block_prev, size, prev_alloc_prev_block);
		write_footer(block_prev,size,prev_alloc_prev_block); 
		
		//tell next block that prev block is now free.
		write_header(block_next,block_next_size,CURRENTALLOCATED);
        
		freeList_FIFO_insert(block_prev_free,size);
        block=block_prev;
    }

    else                                        // Case 4
    {	    
  	  	size_t block_prev_size=get_size(block_prev);
    	size_t block_next_size=get_size(block_next);
        size_t prev_alloc_prev_block=GET_PREV_ALLOC(block_prev);
		
		freeList_del(block_free,size);
        freeList_del(block_next_free,block_next_size);
	    freeList_del(block_prev_free,block_prev_size);
        
        size += block_next_size + block_prev_size;
        write_header(block_prev, size, prev_alloc_prev_block);
	    write_footer(block_prev,size,prev_alloc_prev_block); 
		freeList_FIFO_insert(block_prev_free,size);
		block=block_prev;
    }
    return block;
}

static void freeList_FIFO_insert(block_f *block,size_t size)
{
	char *listend;
	char *segstart;
	char *segend;
	
	if (size <= LIST0_LIMIT) {
		segstart = freeList_start + SEGLIST0;
		segend = freeList_end + SEGLIST0;
		listend = (char *) GET(segend);

	} else if (size <= LIST1_LIMIT) {
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
	
	//handling cases of insertion of free block of sizes dsize and others separately
	if(size <= LIST0_LIMIT)
	{
		block_f_sixteen *small_block=(block_f_sixteen *)block;
		//if list is empty
		if(listend==NULL)
    		{
        		//set current block as head
        		PUT(segstart,(size_t)(small_block));
				PUT(segend,(size_t)(small_block));
        		small_block->next_free=NULL;
    		}
		//insert at last of list
		else
		{
       		block_f_sixteen *listend_blockf=(block_f_sixteen *)listend;
			small_block->next_free=NULL;
			listend_blockf->next_free=small_block;
			PUT(segend,(size_t)small_block);
		}
	}
	else
	{
		if(listend==NULL)
    		{
        		//set current block as head
        		PUT(segstart,(size_t)(block));
				PUT(segend,(size_t)(block));
        		block->prev_free=NULL;
        		block->next_free=NULL;
    		}
		else
		{
       		block_f * listend_blockf=(block_f *)listend;
			block->prev_free=listend_blockf;
			block->next_free=NULL;
			listend_blockf->next_free=block;
			PUT(segend,(size_t)block);
		}
	}
}

static void freeList_del(block_f *block,size_t size)
{
	//handling deletion of free block of sizes dsize and others separately
	if (size <= LIST0_LIMIT)
		{
			block_f_sixteen *small_block=(block_f_sixteen *)block;
			if(small_block == ( (block_f_sixteen *)(GET(freeList_start + SEGLIST0)) ))
			{
				if(small_block->next_free==NULL)
				{
					PUT(freeList_end + SEGLIST0, (size_t)NULL);
					PUT(freeList_start + SEGLIST0,(size_t)NULL);
				}
				else
					PUT(freeList_start + SEGLIST0, (size_t) (block->next_free));
				
				if(small_block->next_free!=NULL)
					small_block->next_free=NULL;
			}
			else if(small_block->next_free==NULL)
			{
				block_f_sixteen *startp=(block_f_sixteen *)(GET(freeList_start + SEGLIST0));
				block_f_sixteen *prevp=NULL;
				while(startp!=small_block)
				{
					prevp=startp;
					startp=startp->next_free;
				}
				prevp->next_free=NULL;
				PUT(freeList_end + SEGLIST0, (size_t)prevp);
			}
			else
			{
				block_f_sixteen *startp=(block_f_sixteen *)(GET(freeList_start + SEGLIST0));
				block_f_sixteen *prevp=NULL;
				while(startp != small_block)
				{
					prevp=startp;
					startp=startp->next_free;
				}
				prevp->next_free=small_block->next_free;
				small_block->next_free=NULL;
			}
			//maintaining allocation status in the header since removing them was throwing segmentation fault
			small_block->header=(small_block->header) & 0x3;
		}
	else
	{
		if(block->prev_free==NULL) //at start of freeList
		{
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
			block->prev_free->next_free=NULL;
			block->prev_free=NULL;
		}
		else //in middle of freeList
		{
			block->prev_free->next_free=block->next_free;
			block->next_free->prev_free=block->prev_free;
			block->prev_free=NULL;
			block->next_free=NULL;
		}
	}
}

/*
* find fit determines the appropriate seglist to start searching for a block which can fit asize sized block
* Rather than checking all the free list starting from seglist 0 for a free block
* large enough to accommodate the requested size, I have compared
* the requested size with maximum limit of each seglist
*
* And if requested size is greater than a seglist's maximum size, then that
* seglist is not checked for a free block to accommmodate
* the request.
*/
static void *find_fit(size_t asize)
{
	size_t sizeatstart;
	char *bp = NULL;

	/* Segregated lists*/
	if (asize <= LIST0_LIMIT) {
		for (sizeatstart = 0; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST1_LIMIT) {
		for (sizeatstart = 1; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST2_LIMIT) {
		for (sizeatstart = 2; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST3_LIMIT) {
		for (sizeatstart = 3; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST4_LIMIT) {
		for (sizeatstart = 4; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST5_LIMIT) {
		for (sizeatstart = 5; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST6_LIMIT) {
		for (sizeatstart = 6; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST7_LIMIT) {
		for (sizeatstart = 7; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST8_LIMIT) {
		for (sizeatstart = 8; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST9_LIMIT) {
		for (sizeatstart = 9; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST10_LIMIT) {
		for (sizeatstart = 10; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST11_LIMIT) {
		for (sizeatstart = 11; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST12_LIMIT) {
		for (sizeatstart = 12; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else if (asize <= LIST13_LIMIT) {
		for (sizeatstart = 13; sizeatstart < TOTALLIST; sizeatstart++) {
			if ((bp = find(sizeatstart, asize)) != NULL)
				return bp;
		}
	} else {
		sizeatstart = 14;
		if ((bp = find(sizeatstart, asize)) != NULL) 
			return bp;
	}
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
	block_f *current_free=NULL;
	/* Finding which list to look into */
	if (sizeatstart == 0)
	{
		current = (char *) GET(freeList_start + SEGLIST0);
		if(current!=NULL && actual_size<=LIST0_LIMIT)
			return current;
		else return NULL;	
	}
	else
	{
		if (sizeatstart == 1)
			current = (char *) GET(freeList_start + SEGLIST1);
		else if (sizeatstart == 2)
			current = (char *) GET(freeList_start + SEGLIST2);
		else if (sizeatstart == 3)
			current = (char *) GET(freeList_start + SEGLIST3);
		else if (sizeatstart == 4)
			current = (char *) GET(freeList_start + SEGLIST4);
		else if (sizeatstart == 5)
			current = (char *) GET(freeList_start + SEGLIST5);
		else if (sizeatstart == 6)
			current = (char *) GET(freeList_start + SEGLIST6);
		else if (sizeatstart == 7)
			current = (char *) GET(freeList_start + SEGLIST7);
		else if (sizeatstart == 8)
			current = (char *) GET(freeList_start + SEGLIST8);
		else if (sizeatstart == 9)
			current = (char *) GET(freeList_start + SEGLIST9);
		else if (sizeatstart == 10)
			current = (char *) GET(freeList_start + SEGLIST10);
		else if (sizeatstart == 11)
			current = (char *) GET(freeList_start + SEGLIST11);
		else if (sizeatstart == 12)
			current = (char *) GET(freeList_start + SEGLIST12);
		else if (sizeatstart == 13)
			current = (char *) GET(freeList_start + SEGLIST13);
		else if(sizeatstart ==14 )
			current = (char *) GET(freeList_start + SEGLIST14);

    		current_free=(block_f *)current;
	
		/* Finding available free block in list */
		while (current_free != NULL)
		{
			if (actual_size <= get_size((block_t *)current_free))
				break;	
			current_free = current_free->next_free;
		}
		return ((block_t *)current_free);
	}
}

 static void place(void *bp, size_t asize)
 {
     block_t * block=(block_t *)bp;
     size_t csize = get_size(block);
    
     freeList_del((block_f *)block,csize);
     
	 //handling cases where splicing of a bigger block results in either a
	 // 16B block or more, separately.
	 // 
	 // This is because, 16B free block doesn't have footer. So better to handle
	 // such case with an if else
	 if ( (csize - asize) == min_block_size )
	 {
		 write_header(block, asize, (GET_PREV_ALLOC(block) | CURRENTALLOCATED));
		 block_t *block_next=find_next(block);
	 	 write_header(block_next, min_block_size, PREVIOUSALLOCATED);
		 freeList_FIFO_insert((block_f *)block_next,min_block_size);
	 }
     else if ((csize - asize) > min_block_size)
     {	
         write_header(block, asize, (GET_PREV_ALLOC(block) | CURRENTALLOCATED));
         
         block_t *block_next=find_next(block);
      
	 	 write_header(block_next, csize-asize, PREVIOUSALLOCATED);
         write_footer(block_next, csize-asize, PREVIOUSALLOCATED);
         
	 	freeList_FIFO_insert((block_f *)block_next,csize-asize);
     }
     else
     {
         write_header(block, csize, (GET_PREV_ALLOC(block) | CURRENTALLOCATED));
		 block_t *block_next=find_next(block);
		 write_header(block_next,get_size(block_next),(PREVIOUSALLOCATED | get_alloc(block_next)));
		 
		 //update the footer of next block only if next block is a free block of size more than dsize
		 if( (!get_alloc(block_next)) && get_size(block_next) > dsize )
			write_footer(block_next,get_size(block_next), (PREVIOUSALLOCATED | get_alloc(block_next)));
     }
 }
		    
/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header size.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
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
