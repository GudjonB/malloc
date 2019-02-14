/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in below _AND_ in the
 * struct that follows.
 *
 * Note: This comment is parsed. Please do not change the
 *       Format!
 *
 * === User information ===
 * Group: Mallakútarnir
 * User 1: gudjon17
 * SSN: 251192-3089
 * User 2: dagfinnur15
 * SSN: 130593-2329
 * User 3: muggur16
 * SSN: 100596-2029
 * === End User Information ===
 ********************************************************/
team_t team = {
    /* Group name */
    "Mallakútarnir",
    /* First member's full name */
    "Guðjón Björnsson",
    /* First member's email address */
    "gudjon17@ru.is",
    /* Second member's full name (leave blank if none) */
    "Dagfinnur Ari Normann",
    /* Second member's email address (leave blank if none) */
    "dagfinnur15@ru.is",
    /* Third full name (leave blank if none) */
    "Muggur Ólafsson",
    /* Third member's email address (leave blank if none) */
    "muggur16@ru.is"
};

/* Heap checker debug  -  see section 5 in pdf
• Is every block in the free list marked as free?
• Are there any contiguous free blocks that somehow escaped coalescing?
• Is every free block actually in the free list?
• Do the pointers in the free list point to valid free blocks?
• Do any allocated blocks overlap?
• Do the pointers in a heap block point to valid heap addresses?
 */
/*
#ifdef DEBUG
    #define CHECKHEAP(verbose) mm_checkheap(verbose);
#else
    #define CHECKHEAP(verbose);
#endif
*/
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y)? (x) :(y))
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Private global variables */
static char *heap_ptr;

/* Private helper functions */
static void *coalesce (void *bp);
static void *extend_heap(size_t words);

/* Node struct, doubly linked list ?? ** þurfum við doubly linked ?*/
typedef struct node *nodePtr; // typedef needed here ? mby not
struct node {
    nodePtr next;
    nodePtr prev;
};


 /* mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_ptr = mem_sbrk(4*WSIZE)) == (void *)-1) { // skoda betur villu
        return -1;
    }
    PUT(heap_ptr, 0);                          /* Alignment padding */
    PUT(heap_ptr + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_ptr + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_ptr + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_ptr += (2*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1) {
        return NULL;
    }
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{

    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
coalesce function as in textbook pg. 867
*/

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;

}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = (char *)mem_sbrk(size)) == (void *)-1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    // initializeNode(bp);
    // need a function to initialize them nodes

    return bp;
}

void mm_heapcheck(int verbose) {

    char *bp = heap_ptr;

    if (verbose) {
        printf("Heap (%p):\n", heap_ptr);
    }
    if ((GET_SIZE(HDRP(heap_ptr)) != DSIZE) || !GET_ALLOC(HDRP(heap_ptr))) {
        printf("Bad prologue header\n");
   // checkblock(heap_ptr);
   // need to create such function
    }
    for (bp = heap_ptr; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) {
            // printblock(bp);
            // need to create such function
      //  checkblock(bp);
      //  need to create such function
        }
    }

    if (verbose) {
        // printblock(bp);
        // need to create such function
    }
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
        printf("Bad epilogue header\n");
    }

    if(verbose) {
        printf("Checking for errors in the free list\n");
    }
    // checkFreeList();
    // need to create such function
    if(verbose) {
        printf("Finished checking the free list\n");
    }
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    return NULL;
    /* %% Geymum í bili -> notum ekkert í fyrstu

    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL) {
        return NULL;
    }
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize) {
        copySize = size;
    }
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
    */
}
