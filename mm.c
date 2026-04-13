/*
 * mm.c - Segregated explicit free list allocator.
 *
 * Free blocks are grouped by size class and linked with explicit
 * predecessor/successor pointers stored in the payload area.
 * Allocation uses a first-fit search across the appropriate size class
 * and larger classes. Free blocks are coalesced eagerly.
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
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team5",
    /* First member's full name */
    "JAEHYEOK LEE",
    /* First member's email address */
    "cncnvmvm@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define LISTLIMIT 12 //프리블록 의 크기별 구간을 12개로 만들겠다
#define PTRSIZE (sizeof(void *)) //포인터 하나의 크기=8로, freeblock안에 prev,next포인터를 넣어야해서.
#define MINBLOCKSIZE (ALIGN(DSIZE + 2 * PTRSIZE))
#define FIRST_FIT_POLICY 0
#define NEXT_FIT_POLICY 1
#define BEST_FIT_POLICY 2

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PRED(bp) (*(void **)(bp))
#define SUCC(bp) (*(void **)((char *)(bp) + PTRSIZE))

static char *heap_listp;
static void *seg_free_lists[LISTLIMIT];
static void *rover;
static int rover_index;
static int fit_policy = BEST_FIT_POLICY;

static int get_list_index(size_t size);
static void insert_free_block(void *bp, size_t size);
static void remove_free_block(void *bp);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *first_fit(size_t asize);
static void *next_fit(size_t asize);
static void *best_fit(size_t asize);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int i; //free list head 배열을 초기화하기 위해 반복 변수를 둔다

    for (i = 0; i < LISTLIMIT; i++)
        seg_free_lists[i] = NULL;

    rover = NULL;
    rover_index = 0;

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * mm_malloc - Allocate a block using segregated explicit free lists.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    asize = MAX(ALIGN(size + DSIZE), MINBLOCKSIZE);

    if ((bp = find_fit(asize)) != NULL) { //힙 전체가 아니라, free list안에서 적당한 블록 탐색
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

/*
 * mm_free - Mark a block free and coalesce immediately.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Resize a block, reusing neighbors when possible.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    void *next_bp;
    void *remainder_bp;
    size_t asize;
    size_t oldsize;
    size_t nextsize;
    size_t combined;
    size_t copySize;

    if (ptr == NULL)
        return mm_malloc(size);

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    asize = MAX(ALIGN(size + DSIZE), MINBLOCKSIZE); //새로 필요한 블록 크기 계산
    oldsize = GET_SIZE(HDRP(ptr)); //현재 블록 전체 크기 계산

    if (asize <= oldsize) { //현재 블록의 크기가 충분히 
        if ((oldsize - asize) >= MINBLOCKSIZE) { //split가능한지 판단
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));

            remainder_bp = NEXT_BLKP(ptr); //남는 부분을 free block으로
            PUT(HDRP(remainder_bp), PACK(oldsize - asize, 0));
            PUT(FTRP(remainder_bp), PACK(oldsize - asize, 0));
            coalesce(remainder_bp);
        }
        return ptr;
    }

    next_bp = NEXT_BLKP(ptr);
    if (!GET_ALLOC(HDRP(next_bp))) { //다음 block이 free라면 합쳐서 제자리 확장이 가능한지 판단
        nextsize = GET_SIZE(HDRP(next_bp));
        combined = oldsize + nextsize;

        if (combined >= asize) {
            remove_free_block(next_bp);

            if ((combined - asize) >= MINBLOCKSIZE) { //합치고, split이 가능한지 확인
                PUT(HDRP(ptr), PACK(asize, 1));
                PUT(FTRP(ptr), PACK(asize, 1));

                remainder_bp = NEXT_BLKP(ptr);
                PUT(HDRP(remainder_bp), PACK(combined - asize, 0));
                PUT(FTRP(remainder_bp), PACK(combined - asize, 0));
                insert_free_block(remainder_bp, combined - asize);
            }
            else {
                PUT(HDRP(ptr), PACK(combined, 1));
                PUT(FTRP(ptr), PACK(combined, 1));
            }

            return ptr;
        }
    }

    newptr = mm_malloc(size); //제자리 확장이 안 될 경우, 기존 방식대로 새 블록 할당 후 복사
    if (newptr == NULL)
        return NULL;

    copySize = oldsize - DSIZE;
    if (size < copySize)
        copySize = size;

    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}

static int get_list_index(size_t size)
{
    int index = 0;
    size_t limit = MINBLOCKSIZE;

    while ((index < LISTLIMIT - 1) && (size > limit)) {
        limit <<= 1;
        index++;
    }

    return index;
}

static void insert_free_block(void *bp, size_t size)
{
    int index = get_list_index(size);
    void *head = seg_free_lists[index];

    PRED(bp) = NULL;
    SUCC(bp) = head;

    if (head != NULL)
        PRED(head) = bp;

    seg_free_lists[index] = bp;
}

static void remove_free_block(void *bp)
{
    int index = get_list_index(GET_SIZE(HDRP(bp)));

    if (rover == bp) {
        rover = SUCC(bp);
        rover_index = index;
    }

    if (PRED(bp) != NULL)
        SUCC(PRED(bp)) = SUCC(bp);
    else
        seg_free_lists[index] = SUCC(bp);

    if (SUCC(bp) != NULL)
        PRED(SUCC(bp)) = PRED(bp);
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if (size < MINBLOCKSIZE)
        size = MINBLOCKSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        insert_free_block(bp, size);
        return bp;
    }

    if (prev_alloc && !next_alloc) {
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        remove_free_block(PREV_BLKP(bp));
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    insert_free_block(bp, size);
    return bp;
}

static void *first_fit(size_t asize)
{
    void *bp;
    int index = get_list_index(asize);

    for (; index < LISTLIMIT; index++) {
        for (bp = seg_free_lists[index]; bp != NULL; bp = SUCC(bp)) {
            if (asize <= GET_SIZE(HDRP(bp)))
                return bp;
        }
    }

    return NULL;
}

static void *next_fit(size_t asize)
{
    void *bp;
    void *start_bp;
    int base_index = get_list_index(asize);
    int start_index;
    int index;

    if (rover != NULL && rover_index >= base_index) {
        start_index = rover_index;
        start_bp = rover;
    }
    else {
        start_index = base_index;
        start_bp = seg_free_lists[start_index];
    }

    for (index = start_index; index < LISTLIMIT; index++) {
        bp = (index == start_index) ? start_bp : seg_free_lists[index];
        for (; bp != NULL; bp = SUCC(bp)) {
            if (asize <= GET_SIZE(HDRP(bp))) {
                rover = SUCC(bp);
                rover_index = index;
                return bp;
            }
        }
    }

    for (index = base_index; index <= start_index; index++) {
        bp = seg_free_lists[index];

        if (index == start_index) {
            for (; bp != NULL && bp != start_bp; bp = SUCC(bp)) {
                if (asize <= GET_SIZE(HDRP(bp))) {
                    rover = SUCC(bp);
                    rover_index = index;
                    return bp;
                }
            }
        }
        else {
            for (; bp != NULL; bp = SUCC(bp)) {
                if (asize <= GET_SIZE(HDRP(bp))) {
                    rover = SUCC(bp);
                    rover_index = index;
                    return bp;
                }
            }
        }
    }

    return NULL;
}

static void *best_fit(size_t asize)
{
    void *bp;
    void *best_bp = NULL;
    size_t size;
    size_t best_size = ~(size_t)0;
    int index = get_list_index(asize);

    for (; index < LISTLIMIT; index++) {
        for (bp = seg_free_lists[index]; bp != NULL; bp = SUCC(bp)) {
            size = GET_SIZE(HDRP(bp));

            if (asize <= size && size < best_size) {
                best_bp = bp;
                best_size = size;

                if (size == asize)
                    return bp;
            }
        }

        if (best_bp != NULL)
            return best_bp;
    }

    return NULL;
}

static void *find_fit(size_t asize)
{
    if (fit_policy == NEXT_FIT_POLICY)
        return next_fit(asize);
    if (fit_policy == BEST_FIT_POLICY)
        return best_fit(asize);

    return first_fit(asize);
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    size_t remainder = csize - asize;
    void *next_bp;

    remove_free_block(bp);

    if (remainder >= MINBLOCKSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(remainder, 0));
        PUT(FTRP(next_bp), PACK(remainder, 0));
        insert_free_block(next_bp, remainder);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
