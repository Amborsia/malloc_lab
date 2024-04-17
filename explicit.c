// explicit 방법

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
    "8th",
    /* First member's full name */
    "남홍근, 김태훈, 박진용",
    /* First member's email address */
    " ghdrms1220@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) (((char *)(bp) + GET_SIZE((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) (((char *)(bp)-GET_SIZE((char *)(bp)-DSIZE)))

// 추가된 선언
/* Given ptr in free list, get next and previous ptr in the list */
#define NEXT(bp) (*(char **)(bp + WSIZE))
#define PREV(bp) (*(char **)(bp))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *heap_listp;

// 추가된 함수
static void putFreeBlock(void *bp);
static void removeBlock(void *bp);
static char *free_listp;

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(8 * WSIZE)) == (void *)-1)
    {
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), NULL);               /* prev free block pointer 는 null */
    PUT(heap_listp + (3 * WSIZE), NULL);               /* succ free block pointer 는 null */
    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));         /* Epilogue header */
    free_listp = heap_listp + (2 * WSIZE);
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }

    return 0;
}

/*
    extend_heap이 사용되는 경우 2가지
        1. 힙이 초기화될 때,
        2. mm_malloc이 적당한 fit을 찾지 못했을 때
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    // PREV_BLK(bp) == bp: epilogue block을 만났을 떄. Extend했을 때 epilogue를 만나는 유일한 경우
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* case 1 : 이전, 다음 블록 모두 할당되어있다면 */
    // if (prev_alloc && next_alloc)
    // {
    //     putFreeBlock(bp);
    //     return bp;
    //     /* case 2 : 이전 블록은 할당되어있고, 다음 블록은 가용상태라면 */
    // }
    // else
    if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        removeBlock(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        /* case 3 : 이전 블록은 가용상태이고, 다음 블록이 할당상태라면 */
    }
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        removeBlock(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        /* case 4 : 이전, 다음 블록 모두 가용 상태라면 */
    }
    else if (!prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        removeBlock(NEXT_BLKP(bp));
        removeBlock(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    putFreeBlock(bp);
    return bp;
}

/*
 * mm_free - 공간 할당 해제.
 */
void mm_free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *find_fit(size_t asize)
{
    /* First-fit search */
    void *bp;

    for (bp = free_listp; !GET_ALLOC(HDRP(bp)); bp = NEXT(bp))
    {
        if (asize <= (size_t)GET_SIZE(HDRP(bp)))
        {
            return bp;
        }
    }
    return NULL;
}

/*
 * place - 할당할 크기를 담을 수 있는 블록을 분할 해줌
 *         분할 해서 뒤에 공간은 가용 공간으로 만들어줌, 내부 단편화를 줄여줌
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        removeBlock(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        removeBlock(bp);
    }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
    {
        return NULL;
    }

    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // 요청 크기가 0 이하인 경우 해당 포인터를 해제하고 NULL을 반환합니다.
    if ((int)size <= 0)
    {
        mm_free(ptr);
        return NULL;
    }
    else
    {
        size_t old_size = GET_SIZE(HDRP(ptr)); // 이전 블록의 크기를 가져옵니다.
        size_t new_size = size + (2 * WSIZE);  // 새로운 요청 크기를 설정합니다.

        // 새로운 크기가 이전 크기보다 작거나 같다면 기존 포인터를 반환합니다.
        if (new_size <= old_size)
        {
            return ptr;
        }
        else
        {
            size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr))); // 다음 블록의 할당 여부를 확인합니다.
            size_t csize;

            // 다음 블록이 가용 상태이고, 합쳐진 크기가 새로운 크기보다 크거나 같다면 기존 포인터를 반환합니다.
            if (!next_alloc && ((csize = old_size + GET_SIZE(HDRP(NEXT_BLKP(ptr))))) >= new_size)
            {
                removeBlock(NEXT_BLKP(ptr));    // 다음 블록을 가용 리스트에서 제거합니다.
                PUT(HDRP(ptr), PACK(csize, 1)); // 합쳐진 블록의 헤더를 설정합니다.
                PUT(FTRP(ptr), PACK(csize, 1)); // 합쳐진 블록의 푸터를 설정합니다.
                return ptr;                     // 기존 포인터를 반환합니다.
            }
            else // 새로운 크기로 할당할 공간이 부족하면
            {
                // 새로운 메모리 블록을 할당하고 데이터를 복사합니다.
                void *new_ptr = mm_malloc(new_size);
                place(new_ptr, new_size);       // 새로운 메모리 블록을 할당합니다.
                memcpy(new_ptr, ptr, old_size); // 기존 데이터를 새로운 메모리 블록으로 복사합니다.
                mm_free(ptr);                   // 기존 메모리 블록을 해제합니다.
                return new_ptr;                 // 새로운 메모리 블록의 포인터를 반환합니다.
            }
        }
    }
}

// 연결리스트에 추가
static void putFreeBlock(void *bp)
{
    NEXT(bp) = free_listp;
    PREV(free_listp) = bp;
    PREV(bp) = NULL;

    free_listp = bp;
}

// 연결리스트에 제거
static void removeBlock(void *bp)
{
    // 다음 블록이 있다면
    if (PREV(bp))
    {
        // 다음 블록의 주소에, 이전 블록의 주소를 넣는다.

        NEXT(PREV(bp)) = NEXT(bp);
        // 다음 블록이 없다면, 즉 자신이 젤 앞 블록이라면
    }
    else
    {
        // 이전 노드를 젤 앞 블록으로 만들어준다.
        free_listp = NEXT(bp);
    }
    PREV(NEXT(bp)) = PREV(bp);
}