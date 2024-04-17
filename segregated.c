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
    " HongGeun Nam ",
    /* First member's email address */
    " ghdrms1220@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 7)
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
#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소
// segregated
#define SEGREGATED_SIZE (12)

// 해당 가용 리스트의 루트
#define GET_ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *heap_listp;
// 추가된 함수
static void putFreeBlock(void *bp);
static void removeBlock(void *bp);
static char *free_listp;
int get_class(size_t size);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 초기 힙 생성
    if ((heap_listp = mem_sbrk((SEGREGATED_SIZE + 4) * WSIZE)) == (void *)-1) // 8워드 크기의 힙 생성, heap_listp에 힙의 시작 주소값 할당(가용 블록만 추적)
        return -1;
    PUT(heap_listp, 0);                                                    // 정렬 패딩
    PUT(heap_listp + (1 * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1)); // 프롤로그 Header (크기: 헤더 1 + 푸터 1 + segregated list 크기)
    for (int i = 0; i < SEGREGATED_SIZE; i++)
        PUT(heap_listp + ((2 + i) * WSIZE), NULL);
    PUT(heap_listp + ((SEGREGATED_SIZE + 2) * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1)); // 프롤로그 Footer
    PUT(heap_listp + ((SEGREGATED_SIZE + 3) * WSIZE), PACK(0, 1));                             // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치
    heap_listp += (2 * WSIZE);
    if (extend_heap(4) == NULL)
        return -1;
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
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
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    /* case 1 : 이전, 다음 블록 모두 할당되어있다면 */
    if (prev_alloc && next_alloc)
    {
        putFreeBlock(bp);
        return bp;
        /* case 2 : 이전 블록은 할당되어있고, 다음 블록은 가용상태라면 */
    }
    else if (prev_alloc && !next_alloc)
    {
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

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
    int class = get_class(asize);
    void *bp = GET_ROOT(class);
    while (class < SEGREGATED_SIZE) // 현재 탐색하는 클래스가 범위 안에 있는 동안 반복
    {
        bp = GET_ROOT(class);
        while (bp != NULL)
        {
            if ((asize <= GET_SIZE(HDRP(bp)))) // 적합한 사이즈의 블록을 찾으면 반환
                return bp;
            bp = GET_SUCC(bp); // 다음 가용 블록으로 이동
        }
        class += 1;
    }
    return NULL;
}
/*
 * place - 할당할 크기를 담을 수 있는 블록을 분할 해줌
 *         분할 해서 뒤에 공간은 가용 공간으로 만들어줌, 내부 단편화를 줄여줌
 */
static void place(void *bp, size_t asize)
{
    removeBlock(bp);
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        putFreeBlock(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
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
    if ((int)size <= 0)
    {
        mm_free(ptr);
        return NULL;
    }
    else
    {
        size_t old_size = GET_SIZE(HDRP(ptr));
        size_t new_size = size + (2 * WSIZE);
        if (new_size <= old_size)
        {
            return ptr;
        }
        else
        {
            size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
            size_t csize;
            if (!next_alloc && ((csize = old_size + GET_SIZE(HDRP(NEXT_BLKP(ptr))))) >= new_size)
            {
                removeBlock(NEXT_BLKP(ptr));
                PUT(HDRP(ptr), PACK(csize, 1));
                PUT(FTRP(ptr), PACK(csize, 1));
                return ptr;
            }
            else
            {
                void *new_ptr = mm_malloc(new_size);
                if (new_ptr == NULL)
                    return NULL;
                memcpy(new_ptr, ptr, old_size - DSIZE);
                mm_free(ptr);
                return new_ptr;
            }
        }
    }
}
// 연결리스트에 추가
static void putFreeBlock(void *bp)
{
    int class = get_class(GET_SIZE(HDRP(bp)));
    void *ptr = GET_ROOT(class); // 반복되는 부분을 변수에 할당
    GET_SUCC(bp) = ptr;          // 변수를 사용하여 할당
    if (ptr != NULL)             // list에 블록이 존재했을 경우만
        GET_PRED(ptr) = bp;      // 변수를 사용하여 할당
    GET_ROOT(class) = bp;
}

// 연결리스트에 제거
static void removeBlock(void *bp)
{
    int class = get_class(GET_SIZE(HDRP(bp)));
    if (bp == GET_ROOT(class)) // 분리하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
    {
        GET_ROOT(class) = GET_SUCC(GET_ROOT(class)); // 다음 블록을 루트로 변경
        return;
    }
    // 이전 블록의 SUCC을 다음 가용 블록으로 연결
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    // 다음 블록의 PRED를 이전 블록으로 변경
    if (GET_SUCC(bp) != NULL) // 다음 가용 블록이 있을 경우만
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

int get_class(size_t size)
{
    if (size < 16) // 최소 블록 크기는 16바이트
        return -1; // 잘못된 크기

    // 클래스별 최소 크기를 저장하는 배열
    size_t class_sizes[SEGREGATED_SIZE];
    class_sizes[0] = 16;

    // 주어진 크기에 적합한 클래스를 찾습니다.
    for (int i = 0; i < SEGREGATED_SIZE; i++)
    {
        // 클래스별 최소 크기를 설정합니다.
        if (i != 0)
            class_sizes[i] = class_sizes[i - 1] << 1;

        // 주어진 크기가 해당 클래스의 최소 크기보다 작거나 같으면 해당 클래스를 반환합니다.
        if (size <= class_sizes[i])
            return i;
    }

    // 주어진 크기가 8192바이트 이상인 경우, 마지막 클래스로 처리합니다.
    return SEGREGATED_SIZE - 1;
}
