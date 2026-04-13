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
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
// 이건 삭제 #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<< 12)
#define MAX(x,y) ((x)>(y) ? (x):(y))
#define PACK(size,alloc) ((size)|(alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p)=(val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp)+GET_SIZE(HDRP(bp))-DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp)+GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

// 헬퍼 함수 선언 부분
static char *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

//
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp=mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0); //정렬용 4바이트 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE,1)); //프롤로그 헤더
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE,1)); //프롤로그 푸터
    PUT(heap_listp + (3 * WSIZE), PACK(0,1)); //에필로그 블럭의 크기는 4이지만, 헤더에 들어있는 size는 0
    heap_listp+=(2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE)==NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize; //free block이 없을 때, 힙을 늘릴 크기
    char *bp;

    if (size==0)
        return NULL;
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE -1))/DSIZE); //8의 배수로 맞추는 과정

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE); //free block을 못찾았을 때 힙을 얼마나 늘릴지
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) //byte로 넘기지 않고 word 개수로 바꿔서 extend_heap에 넘김
        return NULL;
    
    place(bp, asize);
    return bp;
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
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    void *next_bp;
    size_t asize;
    size_t oldsize;
    size_t nextsize;
    size_t copySize;

    if (size == 0) { //해당 block을 free로 하라는 말
        mm_free(ptr);
        return NULL;
    }

    if (ptr == NULL) { //블록이 없으니 새로 만들라는 말
        return mm_malloc(size);
    }

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    oldsize = GET_SIZE(HDRP(ptr));

    // 이미 현재 블록이 충분히 크면 그대로 사용
    if (asize <= oldsize)
        return ptr;

    // 다음 블록이 free이고 합치면 충분한 경우, 제자리 확장
    next_bp = NEXT_BLKP(ptr);
    if (!GET_ALLOC(HDRP(next_bp))) {
        nextsize = GET_SIZE(HDRP(next_bp));
        if ((oldsize + nextsize) >= asize) {
            size_t combined = oldsize + nextsize;

            if ((combined - asize) >= (2 * DSIZE)) {
                PUT(HDRP(ptr), PACK(asize, 1));
                PUT(FTRP(ptr), PACK(asize, 1));

                next_bp = NEXT_BLKP(ptr);
                PUT(HDRP(next_bp), PACK(combined - asize, 0));
                PUT(FTRP(next_bp), PACK(combined - asize, 0));
            }
            else {
                PUT(HDRP(ptr), PACK(combined, 1));
                PUT(FTRP(ptr), PACK(combined, 1));
            }

            return ptr;
        }
    }

    newptr = mm_malloc(size);
    if (newptr == NULL) //만들어지지 않았으면 NULL반환
        return NULL;

    copySize = oldsize - DSIZE; //기존 block의 payload크기만큼만 복사
    if (size < copySize)
        copySize = size;

    memcpy(newptr, ptr, copySize); //기존 payload 데이터를 새 payload로 붙여넣기
    mm_free(ptr); //기존 block 할당 해제
    return newptr;
}

//헬퍼함수 정의
static void *extend_heap(size_t words) //free block를 만드는 함수
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; 
    //블럭의 사이즈를 항상 8의 배수가 되게끔
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size,0)); //free block이니깐 alloc=0
    PUT(FTRP(bp), PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); 
    //새 epilogue header 생성, 기존의 epilogue자리에 새 free block이 들어감

    return coalesce(bp);

}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp=PREV_BLKP(bp);
    }

    return bp;
}

static void *find_fit(size_t asize) //first fit 구현
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= (2 * DSIZE)){ //블럭의 최소 사이즈가 16이므로, 케이스를 나눔
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else { //최소 사이즈 보다 작을땐 그냥 그 블럭을 통째로 할당
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}








