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
/* printf("%s\n, __func__"); */
#ifdef DEBUG
    #define CHECKHEAP(verbose) printf("%s\n, __func__"); mm_checkheap(verbose);
#else
    #define CHECKHEAP(verbose);
#endif

/* $begin mallocmacros */
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + OVERHEAD + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)         (*(size_t *)(p))
#define PUT(p, val)    (*(size_t *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)    (GET(p) & ~0x7)
#define GET_ALLOC(p)   (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Get head of the free list*/
#define LISTHEAD ((listNode)(heap_listp-WSIZE-DSIZE))
/* $end mallocmacros */

/* Node for the free node list */
typedef struct freeNode * listNode;
struct freeNode{
    listNode next;
    listNode prev;
};
/* Global variables */
static char *heap_listp;  /* pointer to first block */ 

/* function prototypes for internal helper routines */
void removeFromList(void *bp);
void addToList(void *bp);
static void freeListChecker();
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);

/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) 
{
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(6*WSIZE)) == NULL) {
        return -1;
    }
    PUT(heap_listp, 0);                        /* alignment padding */
    listNode head = ((listNode)(heap_listp+WSIZE)); // pointer extra 8 bytes 1 DSIZE
    head->next = NULL;
    head->prev = NULL;
    PUT(heap_listp+DSIZE+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(heap_listp+DSIZE+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+DSIZE+DSIZE+WSIZE, PACK(0, 1));   /* epilogue header */
    heap_listp += (DSIZE+DSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }

    return 0;
}
/* $end mminit */

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{   
    CHECKHEAP(0);      /* Ekki gleyma að kommenta út þegar við skilum */
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;      

    /* Ignore spurious requests */
    if (size <= 0) {
        return NULL;
    }

    /* size + overhead aligned */
    asize = ALIGN(size);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{    
    CHECKHEAP(0);      /* Ekki gleyma að kommenta út þegar við skilum */
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    addToList(bp);
    coalesce(bp);
}

/* $end mmfree */

/*
 * mm_realloc 
 * if the new size is 0 the block is freed,
 * if the new size is smaller then the old one the old pointer is returned.
 * if the pointer ir NULL then mm_mallock is called
 * if the new size is bigger then the old, checks to see if the new size can be fitted in the neighboring blocks conbined with the old one.
 * 
 */
void *mm_realloc(void *ptr, size_t size)
{
    if(size == 0){ // asked for 0 space, pointer freed
        mm_free(ptr);
        return NULL; 
    }
    if(ptr == NULL){ // asked for new malloc
        ptr = mm_malloc(size);
        return ptr; 
    }

    void *newp;
    size_t copySize, newBlock;
    size_t newSize = ALIGN(size); // size aligned + overhead
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));

    copySize = GET_SIZE(HDRP(ptr));
    if (newSize == copySize) { // asked to allocate the same amount of space
        return ptr; 
    }
    else if (newSize < copySize) { // at first we implamented this and the following if loops to behave sortof like the function place,
        return ptr;                // So it would segment the blocks if thay were bigger then needed, but after many tries this gave us the best score
    }
    else if (!prev_alloc){ // if the block on the left is not allocated, we try to fit the new allocation in to them conbined 
        newBlock = (copySize + GET_SIZE(HDRP(PREV_BLKP(ptr))));
        if(newBlock >= newSize){
            newp = PREV_BLKP(ptr);              // for readability
            removeFromList(newp);               // remove the block on the left from the free list.
            PUT(HDRP(newp), PACK(newBlock, 1)); // change the header of the block on the left
            memcpy(newp, ptr, newSize);         // copy the contents of the oldblock in to the one on the left
            PUT(FTRP(newp), PACK(newBlock, 1)); // change the footer to match the header
            return newp;                        // return a pointer to the new blocks
        }
    }
    else if (!next_alloc){ // if the block on the right is not allocated, we try to fit the new allocation in to them conbined 
        newBlock = (copySize + GET_SIZE(FTRP(NEXT_BLKP(ptr))));
        if(newBlock >= newSize){
            removeFromList(NEXT_BLKP(ptr));     // if the newblock fits then we just change the header since the data is already the first thing
            PUT(HDRP(ptr), PACK(newBlock, 1));  // after the header
            PUT(FTRP(ptr), PACK(newBlock, 1));
            return ptr;                         // return the old pointer but with new header and footer 
        }
    }
    else if (!prev_alloc && !next_alloc){ // if both neighboring blocks are unallocated and the new block didn't fit in to just the left or right conbined with the old block 
        newBlock = (copySize + GET_SIZE(FTRP(NEXT_BLKP(ptr))) + GET_SIZE(FTRP(PREV_BLKP(ptr)))); // then we check if it fits in all three conbined
        if(newBlock >= newSize){
            newp = PREV_BLKP(ptr);
            removeFromList(newp);               // remove block on the left
            removeFromList(NEXT_BLKP(ptr));     // remove bblock on the right
            PUT(HDRP(newp), PACK(newBlock, 1)); // change the header of the new block, size of all three and allocated
            memcpy(newp, ptr, copySize);        // copy contents of the old block
            PUT(FTRP(newp), PACK(newBlock, 1)); // change the footer to match header
        return newp; 
        }
    }
    else{                                       // at this point in the code the new block didn't fit in to any conbination
        newp = mm_malloc(size);                 // mallock is called 
        if(newp == NULL){
            printf("ERROR: mm_malloc failed in mm_realloc\n");
            exit(1);
        }
        else {
            memcpy(newp, ptr, size);            // contents copyed over
            mm_free(ptr);                       // the old block is freed
            return newp;                        // pointer to new block returned
        }
    }
    return NULL; // hopfully we never end up here....
}

/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose) {
        printf("Heap (%p):\n", heap_listp);
    }

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) {
        printf("Bad prologue header\n");
    }
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) {
            printblock(bp);
	}
        checkblock(bp);
    }
     
    if (verbose) {
        printblock(bp);
    }
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
        printf("Bad epilogue header\n");
    }
    if(verbose) {
        printf("Checking for errors in the free list\n");
    }
    freeListChecker();
    if(verbose) {
        printf("All checks of the free list have finished!\n");
    }
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;
        
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    
    /* Coalesce if the previous block was free */
    addToList(bp);
    //coalesce(bp);
    return bp;
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= (DSIZE + OVERHEAD)) { 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        removeFromList(bp);
        PUT(HDRP(NEXT_BLKP(bp)), PACK(csize-asize, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(csize-asize, 0));

        addToList(NEXT_BLKP(bp));
    }
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        removeFromList(bp);
    }
    
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 * implemented with best fit and a tolarence for wasted space so we don't always
 * have to traverse the whole list
 */
static void *find_fit(size_t asize)
{

    /* best fit search */
    listNode bp = LISTHEAD->next;
    listNode bestFit = NULL;
    size_t remainder = 9999999; // some huges number

    for (; bp != NULL; bp = bp->next) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))) && (GET_SIZE(HDRP(bp))-asize) < remainder) {
            remainder = GET_SIZE(HDRP(bp)) - asize; // the remainder of the block that was not asked for
            bestFit = bp;
            if(remainder  < 4000){ // when the remainder of the block is less then 4000 bits the block is considered goodenough
                return bestFit;   // the number 4000 is a multiple of 8 and was found through trial and error
            }
        }
    }
    return bestFit; /*if still NULL = no fit */ // if we got to this point then either a block with a higher remainder is used, or a block was not found :(
}


/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }
    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        removeFromList(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        removeFromList(bp);
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {                                     /* Case 4 */
        removeFromList(NEXT_BLKP(bp));
        removeFromList(bp);
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}


static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8) {
        printf("Error: %p is not doubleword aligned\n", bp);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("Error: header does not match footer\n");
    }
}

/* 
 *this function inserts the new freeListNodes at the top of the list  
 */
void addToList(void *bp){ //LIFO
    listNode newNode = (listNode)bp;
    newNode->next = LISTHEAD->next;
    newNode->prev = LISTHEAD;
    if(LISTHEAD->next != NULL){
        LISTHEAD->next->prev = newNode;
    }
    LISTHEAD->next = newNode;
}
/* 
 *this function removes the node that bp points to and connects the neighbor nodes to each other 
 */
void removeFromList(void *bp){ // LISTHEAD er alltaf fyrsta node
    if((listNode)bp == LISTHEAD){
        return;
    }
    listNode nodeToDelete = (listNode)bp;
    if(nodeToDelete->next != NULL ){
        nodeToDelete->next->prev = nodeToDelete->prev;
    }
    nodeToDelete->prev->next = nodeToDelete->next;
    nodeToDelete->prev = NULL;
    nodeToDelete->next = NULL;
}

static void freeListChecker() {
    listNode last = LISTHEAD, tmp;
    for(tmp = LISTHEAD->next; tmp !=NULL; tmp = tmp->next, last = last->next) {
        if(!(tmp->prev == last)) {
            printf("The first block is not correctly pointing to prev pointer of the second block\n");
            printblock(tmp);
            printblock(last);
        }
        if(GET_ALLOC(HDRP(tmp))) {
            printf("Allocated block in free list!!\n");
        }
    }
}