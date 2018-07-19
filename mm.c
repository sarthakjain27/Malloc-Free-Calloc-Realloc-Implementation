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
typedef uint64_t word_t;
static const size_t WSIZE = sizeof(word_t);   // word and header size (bytes)
static const size_t DSIZE = 2*WSIZE;          // double word size (bytes)
static const size_t MINBLOCK = 32; // Minimum block size

#define CHUNKSIZE   224
#define ALIGNMENT DSIZE

/* For storing in lower 3 bits of header in allocated blocks
   and header & footer in free blocks */
#define CURRENTALLOCATED   1
#define PREVIOUSALLOCATED  2

/* Variables used as offsets for
   segregated lists headers */
#define SEGLIST1     0
#define SEGLIST2     16
#define SEGLIST3     32
#define SEGLIST4     48
#define SEGLIST5     64
#define SEGLIST6     80
#define SEGLIST7     96
#define SEGLIST8     112
#define SEGLIST9     128
#define SEGLIST10    144
#define SEGLIST11    160
#define SEGLIST12    176
#define SEGLIST13    192
#define SEGLIST14    208

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

/* Total number of segregated lists */
#define TOTALLIST   14

static size_t MAX(size_t x, size_t y);
static size_t MIN(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static size_t pack(size_t size, size_t alloc);
static size_t GET(char *p);
static void PUT(char *p,size_t val);
static size_t GET4BYTES(char *p);
static void PUT4BYTES(char *p,size_t val);
static size_t GET_SIZE(char *p);
static size_t GET_ALLOC(char *p);
static size_t GET_PREV_ALLOC(char *p);
static char* HDRP(char *bp);
static char* FTRP(char *bp);
static char* NEXT_BLKP(char *bp);
static char* PREV_BLKP(char *bp);
static char* SUCCESSOR(char *bp);
static char* PREDECESSOR(char *bp);
static size_t round_up(size_t size, size_t n);
static void place(void *bp, size_t asize);
static void *find(size_t sizeatstart, size_t actual_size);
static void *find_fit(size_t asize);
static bool aligned(const void *p);
static size_t align(size_t x);


static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/* Read and write 8 bytes at address p */
static size_t GET(char *p)
{
    return (*((size_t*) (p)));   
}

static void PUT(char *p,size_t val)
{
    *((size_t*) (p)) = (val);   
}

/* Read and write 4 bytes at address p */
static size_t GET4BYTES(char *p)
{
    return (*((unsigned*) (p)));   
}

static void PUT4BYTES(char *p,size_t val)
{
       *((unsigned*) (p)) = (val);
}

/* Read the size and allocated fields from address p */
static size_t GET_SIZE(char *p)
{
    return (GET4BYTES(p) & ~0x7);   
}

static size_t GET_ALLOC(char *p)
{
    return (GET4BYTES(p) & 0x1);   
}

static size_t GET_PREV_ALLOC(char *p)
{
    return (GET4BYTES(p) & 0x2);   
}

static char* HDRP(char *bp)
{
    return ((char*)(bp) - WSIZE);   
}

static char* FTRP(char *bp)
{
    return ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);   
}

static char* NEXT_BLKP(char *bp)
{
    return ((char*)(bp) + GET_SIZE((char*)(bp) - WSIZE));   
}

static char* PREV_BLKP(char *bp)
{
    return ((char*)(bp) - GET_SIZE((char*)(bp) - DSIZE));   
}

static char* SUCCESSOR(char *bp)
{
    return ((char*) ((char*)(bp)));
}
static char* PREDECESSOR(char *bp)
{
    return ((char*) ((char*)(bp) + DSIZE));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static size_t PACK(size_t size, size_t alloc)
{
    return (size | alloc) ;
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t MAX(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * min: returns x if x < y, and y otherwise.
 */
static size_t MIN(size_t x, size_t y)
{
    return (x < y) ? x : y;
}


/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/* Helper functions */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);

static void *find(size_t sizeatstart, size_t actual_size);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static void addingtoseglist(char *bp, size_t size);
static void removefromseglist(char *bp, size_t size);


/* Global variables-- Base of the heap(heap_listp) */
static char *heap_listp;
char *h_start;

/*
 * Initialize: return false on error, true on success.
 */
bool mm_init(void) {
    
    /* Allocating segregated free list pointers on heap */
	if ((heap_listp = mem_sbrk(TOTALLIST * DSIZE)) == NULL)
		return false;

	/* Creating prologue and epilogue */
	if ((h_start = mem_sbrk(4 * WSIZE)) == NULL)
		return false;
    
	/* Alignment padding */
	PUT4BYTES(h_start, 0);
	/* Prologue header */
	PUT4BYTES(h_start + WSIZE, PACK(DSIZE, 1));
	/* Prologue footer */
	PUT4BYTES(h_start + (2 * WSIZE), PACK(DSIZE, 1));
	/* Epilogue header */
	PUT4BYTES(h_start + (3 * WSIZE), PACK(0, PREVIOUSALLOCATED | CURRENTALLOCATED));

	/* Initializing the segregated list pointers on heap */
	PUT(heap_listp + SEGLIST1, (size_t) NULL);
	PUT(heap_listp + SEGLIST2, (size_t) NULL);
	PUT(heap_listp + SEGLIST3, (size_t) NULL);
	PUT(heap_listp + SEGLIST4, (size_t) NULL);
	PUT(heap_listp + SEGLIST5, (size_t) NULL);
	PUT(heap_listp + SEGLIST6, (size_t) NULL);
	PUT(heap_listp + SEGLIST7, (size_t) NULL);
	PUT(heap_listp + SEGLIST8, (size_t) NULL);
	PUT(heap_listp + SEGLIST9, (size_t) NULL);
	PUT(heap_listp + SEGLIST10, (size_t) NULL);
	PUT(heap_listp + SEGLIST11, (size_t) NULL);
	PUT(heap_listp + SEGLIST12, (size_t) NULL);
	PUT(heap_listp + SEGLIST13, (size_t) NULL);
	PUT(heap_listp + SEGLIST14, (size_t) NULL);

	/* Create initial empty space of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE) == NULL)
		return false;

	return true;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;		/* adjusted block size */
	size_t extendsize;		/* size to be extended */
	char *bp;

	/* Ignore less size requests */
	if (size <= 0)
		return NULL;

	/* Adjust block size to include header and alignment requests */
		/* Rounds up to the nearest multiple of ALIGNMENT */
		asize = round_up(size + DSIZE, DSIZE);;

	/* Search through heap for possible fit */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);	/* Actual assignment */
		return bp;
	}

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
    char *nxtblkheader;
	size_t size;

	if (ptr == NULL)
		return;

	size = GET_SIZE(HDRP(ptr));
	nxtblkheader = HDRP(NEXT_BLKP(ptr));

	/* Update header and footer to unallocated */
	PUT4BYTES(HDRP(ptr), size | GET_PREV_ALLOC(HDRP(ptr)));
	PUT4BYTES(FTRP(ptr), GET4BYTES(HDRP(ptr)));

	/* Update next block, its previous is no longer allocated */
	PUT4BYTES(nxtblkheader,
			GET_SIZE(nxtblkheader) | GET_ALLOC(nxtblkheader));

	/* Add free block to appropriate segregated list */
	addingtoseglist(ptr, size);

	coalesce(ptr);
}

/*
 * realloc
 */
void *realloc(void *oldptr, size_t size) {
    /* After malloc, new address with size "size" */
	char *newaddress;

	/* Size to be copied */
	size_t copysize;

	/* If ptr is NULL, call equivalent to malloc(size) */
	if (oldptr == NULL)
		return malloc(size);

	/* If size = 0, call equivalanet to free(oldptr), returns null */
	if (size == 0) {
		free(oldptr);
		return NULL;
	}

	/* Else, allocate new free block, copy old content over */
	newaddress = malloc(size);
	copysize = MIN(size, GET_SIZE(HDRP(oldptr)) - WSIZE);

	/* Move from source to dest */
	memmove(newaddress, oldptr, copysize);

	/* Free the old block */
	free(oldptr);

	return newaddress;
}

/*
 * calloc
 * This function is not tested by mdriver
 */
void *calloc (size_t nmemb, size_t size) {
    size_t i;
	size_t tsize = nmemb * size;
	char *ptr = malloc(tsize);

	char *temp = ptr;

	for (i = 0; i < nmemb; i++) {
		*temp = 0;
		temp = temp + size;
	}

	return ptr;
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
bool mm_checkheap(int lineno)
{
    /* Variables for testing if block falls under appropriate size list */
	char *listpointer = NULL;
	unsigned minimumblocksize = 0;
	unsigned maximumblocksize = 0;
	unsigned sizeatstart = 0;

	/* Pointer to the very first block */
	char *ptr = heap_listp + 2 * DSIZE + TOTALLIST * DSIZE;

	/* If block is free, check for:
	   1. Header/footer mismatch
	   2. Next/prev free pointer inconsistencies
	   3. Adjacent free blocks
	   */
	if (!GET_ALLOC(HDRP(ptr))) 
    {
		/*Header/footer mismatch */
		if ((GET4BYTES(HDRP(ptr)) != GET4BYTES(FTRP(ptr))))
        {
            printf("Free block pointer %p: header and footer mismatch\n", ptr);
            return false;
        }

		/* Next/prev free pointer inconsistencies */
		if ((char *) GET(SUCCESSOR(ptr)) != NULL && (char *) GET(PREDECESSOR(SUCCESSOR(ptr))) != ptr)
        {
            printf("Free block pointer %p's next pointer is inconsistent\n", ptr);
            return false;
        }

		if ((char *) GET(PREDECESSOR(ptr)) != NULL && (char *) GET(SUCCESSOR(PREDECESSOR(ptr))) != ptr)
        {
            printf("Free block pointer %p's previous pointer is inconsistent\n", ptr);
            return false;
        }

		/* Adjacent free blocks */
		if ((GET4BYTES(HDRP(NEXT_BLKP(ptr))) != 1) && (GET4BYTES(HDRP(NEXT_BLKP(ptr))) != 3) && !GET_ALLOC(HDRP(NEXT_BLKP(ptr))))
        {
            printf("Error: Free block pointer %p and %p are adjacent\n", ptr, NEXT_BLKP(ptr));
            return false;
        }
	}

	/* Checking if all blocks in each freelist fall within
	   the appropriate ranges (Different segregated lists) */
	for (sizeatstart = 0; sizeatstart < TOTALLIST; sizeatstart++) 
    {
		if (sizeatstart == 0) {
			listpointer = (char *) GET(heap_listp + SEGLIST1);
			minimumblocksize = 0;
			maximumblocksize = LIST1_LIMIT;
		} else if (sizeatstart == 1) {
			listpointer = (char *) GET(heap_listp + SEGLIST2);
			minimumblocksize = LIST1_LIMIT;
			maximumblocksize = LIST2_LIMIT;
		} else if (sizeatstart == 2) {
			listpointer = (char *) GET(heap_listp + SEGLIST3);
			minimumblocksize = LIST2_LIMIT;
			maximumblocksize = LIST3_LIMIT;
		} else if (sizeatstart == 3) {
			listpointer = (char *) GET(heap_listp + SEGLIST4);
			minimumblocksize = LIST3_LIMIT;
			maximumblocksize = LIST4_LIMIT;
		} else if (sizeatstart == 4) {
			listpointer = (char *) GET(heap_listp + SEGLIST5);
			minimumblocksize = LIST4_LIMIT;
			maximumblocksize = LIST5_LIMIT;
		} else if (sizeatstart == 5) {
			listpointer = (char *) GET(heap_listp + SEGLIST6);
			minimumblocksize = LIST5_LIMIT;
			maximumblocksize = LIST6_LIMIT;
		} else if (sizeatstart == 6) {
			listpointer = (char *) GET(heap_listp + SEGLIST7);
			minimumblocksize = LIST6_LIMIT;
			maximumblocksize = LIST7_LIMIT;
		} else if (sizeatstart == 7) {
			listpointer = (char *) GET(heap_listp + SEGLIST8);
			minimumblocksize = LIST7_LIMIT;
			maximumblocksize = LIST8_LIMIT;
		} else if (sizeatstart == 8) {
			listpointer = (char *) GET(heap_listp + SEGLIST9);
			minimumblocksize = LIST8_LIMIT;
			maximumblocksize = LIST9_LIMIT;
		} else if (sizeatstart == 9) {
			listpointer = (char *) GET(heap_listp + SEGLIST10);
			minimumblocksize = LIST9_LIMIT;
			maximumblocksize = LIST10_LIMIT;
		} else if (sizeatstart == 10) {
			listpointer = (char *) GET(heap_listp + SEGLIST11);
			minimumblocksize = LIST10_LIMIT;
			maximumblocksize = LIST11_LIMIT;
		} else if (sizeatstart == 11) {
			listpointer = (char *) GET(heap_listp + SEGLIST12);
			minimumblocksize = LIST11_LIMIT;
			maximumblocksize = LIST12_LIMIT;
		} else if (sizeatstart == 12) {
			listpointer = (char *) GET(heap_listp + SEGLIST13);
			minimumblocksize = LIST12_LIMIT;
			maximumblocksize = LIST13_LIMIT;
		} else {
			listpointer = (char *) GET(heap_listp + SEGLIST14);
			minimumblocksize = LIST13_LIMIT;
			maximumblocksize = ~0;
		}

		while (listpointer != NULL) 
        {
			if (!(minimumblocksize < GET_SIZE(HDRP(listpointer)) && GET_SIZE(HDRP(listpointer)) <= maximumblocksize)) 
            {
				printf("Free block pointer %p is not in the appropriate list", listpointer);
                return false;
			}
			listpointer = (char *) GET(SUCCESSOR(listpointer));
		}
	}


	/* Traverse through the entire heap:
	 *  For all blocks, check for:
	 1. Alignment
	 2. Existence in heap
	 */
	while ((GET4BYTES(HDRP(ptr)) != 1) && (GET4BYTES(HDRP(ptr)) != 3)) 
    {
		if (!aligned(ptr)) {
			printf("Block pointer %p isn't aligned\n", ptr);
            return false;
		}
		if (!in_heap(ptr)) {
			printf("Block pointer %p isn't in heap\n", ptr);
            return false;
		}

		/* This information is printed for every block irrespective
		   of the error 
		   */
		//if (verbose) {

			printf("\nBlock pointer: %p\n", ptr);
			printf("Block size is: %zu\n", GET_SIZE(HDRP(ptr)));

			if (GET_ALLOC(HDRP(ptr)))
				printf("Block is allocated\n");
			else
				printf("Block is free\n");

			if (GET_PREV_ALLOC(HDRP(ptr)))
				printf("Previous block is allocated\n");
			else
				printf("Previous block is free\n");
		//}
		ptr = NEXT_BLKP(ptr);
	}
    return true;
}

/*
 *  Function: place 
 *  Description: 
 Allocates block of memory at address bp. if remaining
 memory is >= min free block size, allocate requested
 amount and form new free block to add to segregated
 list. If not, allocate entire block of memory at
 address bp.
 */
static void place(void *bp, size_t asize)
{

	/* Original free block size */
	size_t csize = GET_SIZE(HDRP(bp));
	/* Remaining free block size */
	size_t remainsize = csize - asize;

	/* Next adjacent block address */
	char *nextaddress = NEXT_BLKP(bp);

	/* Remove free block from the appropriate seg list */
	removefromseglist(bp, csize);

	/* If the remaining block is larger than min block size of 
	   24 bytes, then splitting is done to form new free block 
	   */
	if (remainsize >= MINBLOCK) {

		/* Update new header information, store info bits */
		PUT4BYTES(HDRP(bp),
				PACK(asize,
					GET_PREV_ALLOC(HDRP(bp)) | CURRENTALLOCATED));

		/* Update next block's address to remaining free block's address */
		nextaddress = NEXT_BLKP(bp);


		/* Inform next adjacent free block that its previous block 
		   is allocated */
		PUT4BYTES(HDRP(nextaddress), remainsize | PREVIOUSALLOCATED);
		PUT4BYTES(FTRP(nextaddress), remainsize | PREVIOUSALLOCATED);

		/* Add remaining free block to appropriate segregated list */
		addingtoseglist(nextaddress, remainsize);

		/* If the remaining is not larger than min block, then assign 
		   entire free block to allocated */
	} else {

		/* Update new header information, store info bits */
		PUT4BYTES(HDRP(bp),
				PACK(csize,
					GET_PREV_ALLOC(HDRP(bp)) | CURRENTALLOCATED));

		/* Inform next adjacent block that its previous block 
		   is allocated */
		PUT4BYTES(HDRP(nextaddress),
				GET4BYTES(HDRP(nextaddress)) | PREVIOUSALLOCATED);

		/* Update next adjacent block's footer only if free */
		if (!GET_ALLOC(HDRP(nextaddress)))
			PUT4BYTES(FTRP(nextaddress), GET4BYTES(HDRP(nextaddress)));

	}
}


/*
 * Extend_heap - Extends the heap upward of size bytes
 and adds free block to appropriate free list before
 coalescing.
 */
static void *extend_heap(size_t words)
{
	char *bp;

	if ((long) (bp = mem_sbrk(words)) < 0)
		return NULL;

	/* Change epilogue header to new free block header */
	PUT4BYTES(HDRP(bp), PACK(words, GET_PREV_ALLOC(HDRP(bp))));

	/* Set new free block footer */
	PUT4BYTES(FTRP(bp), GET4BYTES(HDRP(bp)));
	/* Add to segregated list */
	addingtoseglist(bp, words);

	/* Set new epilogue header */
	PUT4BYTES(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

	/* coalesce free blocks if needed */
	return coalesce(bp);
}

/*
 * Function name: Addingtoseglist 
 * Description: Adds free block to the appropriate segregated list
 *              by adding it to the front of the list as head &
 *              and linking it to the previous head
 */
static void addingtoseglist(char *bp, size_t size)
{
	/* Address of head of a particular list */
	char *listhead;

	/* Address pointing to the address of head of a particular list */
	char *segstart;


	if (size <= LIST1_LIMIT) {
		segstart = heap_listp + SEGLIST1;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST2_LIMIT) {
		segstart = heap_listp + SEGLIST2;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST3_LIMIT) {
		segstart = heap_listp + SEGLIST3;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST4_LIMIT) {
		segstart = heap_listp + SEGLIST4;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST5_LIMIT) {
		segstart = heap_listp + SEGLIST5;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST6_LIMIT) {
		segstart = heap_listp + SEGLIST6;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST7_LIMIT) {
		segstart = heap_listp + SEGLIST7;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST8_LIMIT) {
		segstart = heap_listp + SEGLIST8;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST9_LIMIT) {
		segstart = heap_listp + SEGLIST9;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST10_LIMIT) {
		segstart = heap_listp + SEGLIST10;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST11_LIMIT) {
		segstart = heap_listp + SEGLIST11;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST12_LIMIT) {
		segstart = heap_listp + SEGLIST12;
		listhead = (char *) GET(segstart);

	} else if (size <= LIST13_LIMIT) {
		segstart = heap_listp + SEGLIST13;
		listhead = (char *) GET(segstart);

	} else {
		segstart = heap_listp + SEGLIST14;
		listhead = (char *) GET(segstart);

	}


	/* If there is no block in that size list */
	if (listhead != NULL) 
    {
		/* Set the current block as head */
		PUT(segstart, (size_t) bp);

		/* Set the current free block's previous pointer to NULL */
		PUT(PREDECESSOR(bp), (size_t) NULL);

		/* set current free block's next pointer to previous head */
		PUT(SUCCESSOR(bp), (size_t) listhead);

		/* Set the previous head's previous pointer to 
		   current free block */
		PUT(PREDECESSOR(listhead), (size_t) bp);

	}
	/* If there are blocks in the size list */
	else {
		/* Set the current block as head */
		PUT(segstart, (size_t) bp);
		/* Set the free block's next and prev free block 
		   addresses to NULL */
		PUT(SUCCESSOR(bp), (size_t) NULL);
		PUT(PREDECESSOR(bp), (size_t) NULL);
	}
}

/*
 * Function: removefromseglist 
 * Description: 
 Removes free block from the appropriate segregated list
 by linking blocks to the left or right of it.  possibly
 updating initial list pointer to head of list.
 */

static void removefromseglist(char *bp, size_t size)
{
	/* Previous block address */
	char *nextaddress = (char *) GET(SUCCESSOR(bp));
	/* Next block address */
	char *prevaddress = (char *) GET(PREDECESSOR(bp));

	if (prevaddress == NULL && nextaddress != NULL) {

		/* Update head pointer of segregated list */
		if (size <= LIST1_LIMIT)
			PUT(heap_listp + SEGLIST1, (size_t) nextaddress);
		else if (size <= LIST2_LIMIT)
			PUT(heap_listp + SEGLIST2, (size_t) nextaddress);
		else if (size <= LIST3_LIMIT)
			PUT(heap_listp + SEGLIST3, (size_t) nextaddress);
		else if (size <= LIST4_LIMIT)
			PUT(heap_listp + SEGLIST4, (size_t) nextaddress);
		else if (size <= LIST5_LIMIT)
			PUT(heap_listp + SEGLIST5, (size_t) nextaddress);
		else if (size <= LIST6_LIMIT)
			PUT(heap_listp + SEGLIST6, (size_t) nextaddress);
		else if (size <= LIST7_LIMIT)
			PUT(heap_listp + SEGLIST7, (size_t) nextaddress);
		else if (size <= LIST8_LIMIT)
			PUT(heap_listp + SEGLIST8, (size_t) nextaddress);
		else if (size <= LIST9_LIMIT)
			PUT(heap_listp + SEGLIST9, (size_t) nextaddress);
		else if (size <= LIST10_LIMIT)
			PUT(heap_listp + SEGLIST10, (size_t) nextaddress);
		else if (size <= LIST11_LIMIT)
			PUT(heap_listp + SEGLIST11, (size_t) nextaddress);
		else if (size <= LIST12_LIMIT)
			PUT(heap_listp + SEGLIST12, (size_t) nextaddress);
		else if (size <= LIST13_LIMIT)
			PUT(heap_listp + SEGLIST13, (size_t) nextaddress);
		else
			PUT(heap_listp + SEGLIST14, (size_t) nextaddress);

		/* Update the new head block's previous to NULL */
		PUT(PREDECESSOR(nextaddress), (size_t) NULL);

	}

	/* If only free block in list, update head pointer to NULL */
	else if (prevaddress == NULL && nextaddress == NULL) {

		if (size <= LIST1_LIMIT)
			PUT(heap_listp + SEGLIST1, (size_t) NULL);
		else if (size <= LIST2_LIMIT)
			PUT(heap_listp + SEGLIST2, (size_t) NULL);
		else if (size <= LIST3_LIMIT)
			PUT(heap_listp + SEGLIST3, (size_t) NULL);
		else if (size <= LIST4_LIMIT)
			PUT(heap_listp + SEGLIST4, (size_t) NULL);
		else if (size <= LIST5_LIMIT)
			PUT(heap_listp + SEGLIST5, (size_t) NULL);
		else if (size <= LIST6_LIMIT)
			PUT(heap_listp + SEGLIST6, (size_t) NULL);
		else if (size <= LIST7_LIMIT)
			PUT(heap_listp + SEGLIST7, (size_t) NULL);
		else if (size <= LIST8_LIMIT)
			PUT(heap_listp + SEGLIST8, (size_t) NULL);
		else if (size <= LIST9_LIMIT)
			PUT(heap_listp + SEGLIST9, (size_t) NULL);
		else if (size <= LIST10_LIMIT)
			PUT(heap_listp + SEGLIST10, (size_t) NULL);
		else if (size <= LIST11_LIMIT)
			PUT(heap_listp + SEGLIST11, (size_t) NULL);
		else if (size <= LIST12_LIMIT)
			PUT(heap_listp + SEGLIST12, (size_t) NULL);
		else if (size <= LIST13_LIMIT)
			PUT(heap_listp + SEGLIST13, (size_t) NULL);
		else
			PUT(heap_listp + SEGLIST14, (size_t) NULL);
	}
	/* If head of list, update head pointer to next free block */
	else if (prevaddress != NULL && nextaddress == NULL) {

		/* Update new tail block's next to null */
		PUT(SUCCESSOR(prevaddress), (size_t) NULL);

		/* If in middle of a list, link blocks on either sides */
	} else {

		/* Link next block's previous to current's previous block */
		PUT(PREDECESSOR(nextaddress), (size_t) prevaddress);

		/* Link previous block's next to current's next block */
		PUT(SUCCESSOR(prevaddress), (size_t) nextaddress);

	}
}

/*
 * coalesce - combines free blocks from left and right with current
 *              free block to form larger free block.  removes current
 *              and/or left and/or right free blocks from their own lists
 *              and add to appropriate free list of new combined sizs.
 *              Called after each addition of a free block.
 */
static void *coalesce(void *bp)
{
	/* store prev and next block's info */
	size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	/* get size of current, prev, next free block (including header) */
	size_t size = GET_SIZE(HDRP(bp));
	size_t nsize = 0;
	size_t psize = 0;

	/* previous block's address and its header address */
	char *prev_hd;
	char *prev_blk;

	char *next_blk;

	/* 4 Cases */
	/* Case 1: Prev and Next both allocated */
	if (prev_alloc && next_alloc) {
		/* return current pointer to free block */
		return bp;
	}
	/* Case 2: Prev allocated, Next free */
	else if (prev_alloc && !next_alloc) {
		next_blk = NEXT_BLKP(bp);

		/* remove current free block and next free block from lists */
		removefromseglist(bp, size);
		removefromseglist(next_blk, GET_SIZE(HDRP(next_blk)));

		/* new block size is current free size plus next free size */
		size += GET_SIZE(HDRP(next_blk));

		/* change header to reflect new size */
		PUT4BYTES(HDRP(bp), PACK(size, prev_alloc));

		/* change footer to reflect new size */
		PUT4BYTES(FTRP(bp), PACK(size, prev_alloc));

		/* add new free block to segregated list */
		addingtoseglist(bp, size);

		/* return current pointer to free block 
		   since block expanded to next */
		return bp;
	}
	/* Case 3- Prev free, Next allocated */
	else if (!prev_alloc && next_alloc) {

		/* get previous block's location and header location */
		prev_blk = PREV_BLKP(bp);
		prev_hd = HDRP(prev_blk);

		psize = GET_SIZE(prev_hd);

		/* remove current free block and prev free block from lists */
		removefromseglist(bp, size);
		removefromseglist(prev_blk, psize);

		/* size is current free size plus prev free size */
		size += psize;

		/* change header to reflect new size */
		PUT4BYTES(prev_hd, PACK(size, GET_PREV_ALLOC(prev_hd)));

		/* change footer to reflect new size */
		PUT4BYTES(FTRP(prev_blk), GET4BYTES(prev_hd));

		/* add new free block to segregated list */
		addingtoseglist(prev_blk, size);

		/* return prev pointer to prev block 
		   since block expanded to prev */
		return prev_blk;
	}

	/* Case 4- Prev free, Next free */
	else {

		/* Get previous block's location and header location */
		prev_blk = PREV_BLKP(bp);
		prev_hd = HDRP(prev_blk);

		next_blk = NEXT_BLKP(bp);

		psize = GET_SIZE(prev_hd);
		nsize = GET_SIZE(HDRP(next_blk));

		/* Remove current, prev, and next free block from lists */
		removefromseglist(bp, size);
		removefromseglist(prev_blk, psize);
		removefromseglist(next_blk, nsize);

		/* Size is current free plus prev free and next free size */
		size += psize + nsize;


		/* Change header to reflect new size */
		PUT4BYTES(prev_hd, PACK(size, GET_PREV_ALLOC(prev_hd)));

		/* Change footer to reflect new size */
		PUT4BYTES(FTRP(prev_blk), GET4BYTES(prev_hd));

		/* Add new free block to segregated list */
		addingtoseglist(prev_blk, size);

		/* Return prev pointer to free block 
		   since block expanded to prev */
		return prev_blk;
	}
}

/*
 * Function: find_fit  
 * Description: Searches through all free lists containing
 blocks with size greater than size requested and returns
 pointer to a satisfacotry free block or NULL if none 
 are found. 
 */
static void *find_fit(size_t asize)
{
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
	char *current = NULL;

	/* Finding which list to look into */
	if (sizeatstart == 0)
		current = (char *) GET(heap_listp + SEGLIST1);
	else if (sizeatstart == 1)
		current = (char *) GET(heap_listp + SEGLIST2);
	else if (sizeatstart == 2)
		current = (char *) GET(heap_listp + SEGLIST3);
	else if (sizeatstart == 3)
		current = (char *) GET(heap_listp + SEGLIST4);
	else if (sizeatstart == 4)
		current = (char *) GET(heap_listp + SEGLIST5);
	else if (sizeatstart == 5)
		current = (char *) GET(heap_listp + SEGLIST6);
	else if (sizeatstart == 6)
		current = (char *) GET(heap_listp + SEGLIST7);
	else if (sizeatstart == 7)
		current = (char *) GET(heap_listp + SEGLIST8);
	else if (sizeatstart == 8)
		current = (char *) GET(heap_listp + SEGLIST9);
	else if (sizeatstart == 9)
		current = (char *) GET(heap_listp + SEGLIST10);
	else if (sizeatstart == 10)
		current = (char *) GET(heap_listp + SEGLIST11);
	else if (sizeatstart == 11)
		current = (char *) GET(heap_listp + SEGLIST12);
	else if (sizeatstart == 12)
		current = (char *) GET(heap_listp + SEGLIST13);
	else if (sizeatstart == 13)
		current = (char *) GET(heap_listp + SEGLIST14);


	/* Finding available free block in list */
	while (current != NULL) {
		if (actual_size <= GET_SIZE(HDRP(current))) {
			break;
		}
		current = (char *) GET(SUCCESSOR(current));
	}

	return current;
}


