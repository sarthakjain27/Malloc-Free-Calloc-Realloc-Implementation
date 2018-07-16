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


#define WSIZE 4       /* Word and header/footer size (bytes) */
#define DSIZE 8       /* Doubleword size (bytes) */
#define CHUNKSIZE 1<<9  /* Extend heap by this amount (bytes) */
#define HEADER_SIZE 24  /* minimum block size */
#define LIST_NO 20

/* 4 or 8 byte alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t ALIGN(size_t x) {
    return ((x + (ALIGNMENT - 1)) & ~0X7);
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t MAX(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

static size_t PACK(size_t size,int curr)
{
    return ((size) | (curr));   
}

static size_t GET(void *p)
{
    return (*(unsigned int *)(p));   
}

static void PUT(char *p,size_t val)
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

static void* head_pointer(void *bp)
{
    return ((char *)(bp)-WSIZE);   
}

static void* foot_pointer(void *bp)
{
    return ((char *)(bp) + GET_SIZE(head_pointer(bp)) - DSIZE);   
}

static void *next_block_address(void *bp)
{
    return ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));    
}

static void *prev_block_address(void *bp)
{
    return ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)));   
}

static void *extend_heap(size_t words);
static void alloc(void *free_block, size_t req_size);
static void *first_fit(size_t req_size);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);
static void insert_free_list(void *bp, int size);
static void remove_block(void *bp,int size);
static int get_free_list_head( unsigned int n);

static char *heap_list_head = 0;
static char *heap_header = 0;
static char *free_list_head;

/* init_fee_list- Sets the pointers pointing to heads of free lists to 0
 *
 */
void init_free_list(char *bp)
{
	for(int i=0;i<LIST_NO;i++)
		(*((char **)(free_list_head) + i)) = bp;
}

/*remove_block - Removes the block from the free list
 * Sets the next pointer of the previous-free block of bp to the next-free block of bp
 * Sets the previous pointer of the next-free block of bp to the previous-free block of bp
 */
static void remove_block(void *bp, int size)
{
	if ((*((char **)(bp) + 1)) != NULL )
		(*(char **)((*((char **)(bp) + 1)))) = (*(char **)(bp));
	else
	{
		int free_list_index = get_free_list_head(size);
		(*((char **)(free_list_head) + free_list_index)) = (*(char **)(bp));
	}
	(*((char **)((*(char **)(bp))) + 1)) = (*((char **)(bp) + 1));
}

/* coalesce - Merge the free block neighbours and place them
 * at the head of the free list
 *
 */

static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(foot_pointer(prev_block_address(bp))) || (prev_block_address(bp) == bp);
	size_t next_alloc = GET_ALLOC(head_pointer(next_block_address(bp)));
	size_t size = GET_SIZE(head_pointer(bp));

	if (prev_alloc && next_alloc)
	{
		// Do nothing
	}

	else if (prev_alloc && !next_alloc)
	{
		size += GET_SIZE(head_pointer(next_block_address(bp)));
		remove_block(next_block_address(bp),GET_SIZE(head_pointer(next_block_address(bp))));
		PUT(head_pointer(bp), PACK(size, 0));
		PUT(foot_pointer(bp), PACK(size,0));
	}

	else if (!prev_alloc && next_alloc)
	{
		size += GET_SIZE(head_pointer(prev_block_address(bp)));
		bp = prev_block_address(bp);
		remove_block(bp,GET_SIZE(head_pointer(bp)));
		PUT(head_pointer(bp), PACK(size, 0));
		PUT(foot_pointer(bp), PACK(size, 0));

	}

	else
	{
		size += GET_SIZE(head_pointer(prev_block_address(bp))) + GET_SIZE(head_pointer(next_block_address(bp)));
		void *pbp = prev_block_address(bp);
		remove_block(pbp, GET_SIZE(head_pointer(pbp)));
		void *nbp = next_block_address(bp);
		remove_block(nbp, GET_SIZE(head_pointer(nbp)));
		bp = prev_block_address(bp);
		PUT(head_pointer(bp), PACK(size, 0));
		PUT(foot_pointer(bp), PACK(size, 0));
	}

	insert_free_list(bp,size);
	return bp;
}

/*insert_free_list - inserts the pointer at the head of the
 * free list.
 *
 */
static void insert_free_list(void *bp, int size)
{
	int free_list_index = get_free_list_head(size);
	(*(char **)(bp)) = (*((char **)(free_list_head) + free_list_index))
	(*((char **)(*((char **)(free_list_head) + free_list_index)) + 1)) = bp;
	(*((char **)(bp) + 1)) = NULL;
	(*((char **)(free_list_head) + free_list_index)) = bp;
}

static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if (size < HEADER_SIZE)
		size = HEADER_SIZE;
	if ((long) (bp = mem_sbrk(size)) == -1)
		return NULL ;

	/* Initialize free block header/footer and the epilogue header */
	PUT(head_pointer(bp), PACK(size, 0)); /* free block header */
	PUT(foot_pointer(bp), PACK(size, 0)); /* free block footer */
	PUT(head_pointer(next_block_address(bp)), PACK(0, 1)); /* new epilogue header */

	/* Coalesce if the previous block was free and add the block to
	 * the free list */
	//mm_checkheap(1);
	return coalesce(bp);                                //line:vm:mm:returnblock

}

/*
 * Initialize: return -1 on error, 0 on success.
 */
bool mm_init(void)
{

	if ((heap_list_head = mem_sbrk(2 * HEADER_SIZE + 20*DSIZE)) == NULL )
		return false;

	PUT(heap_list_head, 0); //Alignment padding

	/*initialize dummy block header*/
	PUT(heap_list_head + WSIZE, PACK(HEADER_SIZE, 1)); //WSIZE = padding
	PUT(heap_list_head + DSIZE, 0); //pointer to next free block
	PUT(heap_list_head + DSIZE+WSIZE, 0); //pointer to the previous free block

	free_list_head = heap_list_head + 2*DSIZE + WSIZE;

	/*initialize dummy block footer*/
	PUT(heap_list_head + HEADER_SIZE, PACK(HEADER_SIZE, 1));

	/*initialize epilogue*/
	PUT(heap_list_head+WSIZE + HEADER_SIZE, PACK(0, 1));


	/*initialize the free list pointer to the tail block*/

	heap_list_head += DSIZE;
	heap_header = heap_list_head;
	init_free_list(heap_list_head);

	/*return -1 if unable to get heap space*/
	if ((heap_list_head = extend_heap(CHUNKSIZE / WSIZE)) == NULL )
		return false;
	return true;

}

/*
 * malloc
 */
void *malloc (size_t size)
{
	//printf("\nMalloc Count: %d\n",++malloc_count);
	size_t asize;
	size_t extendsize;
	char *bp;

	/* Ignore spurious requests */
	if (size <= 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs */
	asize = MAX(ALIGN(size) + DSIZE, HEADER_SIZE);

	/* Search the free list for a fit */
	if ((bp = first_fit(asize)))
	{
		alloc(bp, asize);
		//mm_checkheap(1);
		return bp;
	}

	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL; 	//return NULL if unable to get heap space
	alloc(bp, asize);
	//mm_checkheap(1);
	return bp;

}

/*
 * free- Free the occupied block and coalesces the block
 */
void free(void *ptr)
{

	//printf("\nFree Count: %d\n",++free_count);

	if (ptr == 0)
		return;
	size_t size = GET_SIZE(head_pointer(ptr));
	if (heap_list_head == 0)
		mm_init();

	PUT(head_pointer(ptr), PACK(size, 0));
	PUT(foot_pointer(ptr), PACK(size, 0));
	coalesce(ptr);
	//mm_checkheap(1);
}

/*
 * realloc - referred mm-naive.c
 */
void *realloc(void *oldptr, size_t size)
{
	size_t oldsize;
	void *newptr;
	/* Adjust block size to include overhead and alignment reqs */
	size_t req_size = MAX(ALIGN(size) + DSIZE, HEADER_SIZE);
	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0)
	{
		free(oldptr);
		return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (oldptr == NULL )
		return malloc(size);

	oldsize = GET_SIZE(head_pointer(oldptr));

	if(req_size == oldsize || (oldsize-req_size)<=HEADER_SIZE)
		return oldptr;

	if(req_size <= oldsize)
	{
		PUT(head_pointer(oldptr),PACK(req_size,1));
		PUT(foot_pointer(oldptr),PACK(req_size,1));
		PUT(head_pointer(next_block_address(oldptr)),PACK(oldsize-req_size,1));
		PUT(foot_pointer(next_block_address(oldptr)),PACK(oldsize-req_size,1));
		free(next_block_address(oldptr));
		return oldptr;
	}

	newptr = malloc(size);
	/* If realloc() fails the original block is left untouched  */
	if (!newptr)
		return 0;

	/* Copy the old data. */

	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, oldptr, oldsize);

	/* Free the old block. */
	free(oldptr);

	return newptr;
}

/*
 * calloc - referred mm-naive.c
 */
void *calloc (size_t nmemb, size_t size)
{
	size_t bytes = nmemb * size;
	void *newptr;

	newptr = malloc(bytes);
	memset(newptr, 0, bytes);

	return newptr;
}

/*
 * alloc - Allocates  block of req_size bytes at start of free block
 *         and split if free block is larger
 */
static void alloc(void *free_block, size_t req_size)
{
	void *next_bp;
    size_t csize = GET_SIZE(head_pointer(free_block));
    //Split the free block into allocated and free.
    if ((csize - req_size) >= HEADER_SIZE)
	{
    	PUT(head_pointer(free_block), PACK(req_size, 1)); //Allocating the block
		PUT(foot_pointer(free_block), PACK(req_size, 1));
		remove_block(free_block,csize);
		next_bp = next_block_address(free_block);
		PUT(head_pointer(next_bp), PACK(csize-req_size, 0));//Resetting the size of the free block
		PUT(foot_pointer(next_bp), PACK(csize-req_size, 0));
		coalesce(next_bp); //Coalesce of the newly resized free block
	}
	else
    {
		PUT(head_pointer(free_block), PACK(csize, 1));
		PUT(foot_pointer(free_block), PACK(csize, 1));
		remove_block(free_block,csize);
	}

}

/*first_fit - Iterates through the free list to search for a free block
 * with size greater than or equal to the requested block size.
 *
 */
static void *first_fit(size_t req_size)
{

	char *bp;
	for (int i = get_free_list_head(req_size); i < LIST_NO; i++)
	{
		for (bp = (*((char **)(free_list_head) + i)); GET_ALLOC(head_pointer(bp)) == 0; bp =(*(char **)(bp)) )
		{
			if (req_size <= (size_t) GET_SIZE(head_pointer(bp)))
				return bp;
		}
	}
	/*for (int i = 0; i < get_free_list_head(req_size); i++)
		{
			for (bp = free_list_head[i]; GET_ALLOC(HDRP(bp)) == 0; bp =NEXT_FREE_BLK(bp) )
			{
				if (req_size <= (size_t) GET_SIZE(HDRP(bp)))
					return bp;
			}
		}*/
	return NULL ; // No fit
}

static void printblock(void *bp)
{
	size_t header_size = GET_SIZE(head_pointer(bp));
	size_t header_alloc = GET_ALLOC(head_pointer(bp));
	size_t footer_size = GET_SIZE(foot_pointer(bp));
	size_t footer_alloc = GET_ALLOC(foot_pointer(bp));

	if (header_size == 0)
	{
		printf("%p: EOL\n", bp);
		return;
	}

	if (header_alloc)
		printf("%p: header:[%d:%c] footer:[%d:%c]\n", bp, (int) header_size,
				(header_alloc ? 'a' : 'f'), (int) footer_size, (footer_alloc ? 'a' : 'f'));
	else
		printf("%p:header:[%d:%c] prev:%p next:%p footer:[%d:%c]\n", bp,
				(int) header_size, (header_alloc ? 'a' : 'f'), (*((char **)(bp) + 1)),
				(*(char **)(bp)), (int) footer_size, (footer_alloc ? 'a' : 'f'));
}

static void checkblock(void *bp)
{
    if ((size_t)bp % 8)
	printf("Error: %p is not 8 byte aligned\n", bp);
    if (GET(head_pointer(bp)) != GET(foot_pointer(bp)))
	printf("Error: header and footer are not equal\n");
}

/*
 * checkheap - functions with multiple checks
 */
bool mm_checkheap(int verbose)
{

	char *bp = heap_list_head;

	if (verbose)
	{
		printf("Heap (%p):\n", heap_list_head);
		//printf("Free List (%p):\n", free_list_head);
	}

	if ((GET_SIZE(head_pointer(heap_header)) != HEADER_SIZE)
			|| !GET_ALLOC(head_pointer(heap_header)))
	{
		//printf("Bad prologue header\n");
		//return 1;
	}
	checkblock(heap_list_head);
	for (bp = heap_list_head; GET_SIZE(head_pointer(bp)) > 0; bp = next_block_address(bp))
	{
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}
	if (verbose)
		printblock(bp);
	if ((GET_SIZE(head_pointer(bp)) != 0) || !(GET_ALLOC(head_pointer(bp))))
	{
		printf("Bad epilogue header\n");
		//return 1;
	}

	return true;
}

static int get_free_list_head( unsigned int n)
{
	int count = 0;
	while(n>1)
	{
		n = n>>1;
		count++;
	}
	if(count > LIST_NO-1 )
		return  LIST_NO-1;
	return count;
}
