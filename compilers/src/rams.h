#if !defined(rams_h)
#define rams_h

#include <stdio.h>
#include <stdlib.h>

// ==================================================
//
//  Memory Allocation
//
// ==================================================

#define MEMORY_ERROR \
    { fprintf(stderr, "error: not enough memory\n"); \
    exit(1); } \

#define MALLOC(x, t) \
    x = (t*)malloc(sizeof(t)); \
    if (!x) MEMORY_ERROR; \

#define MALLOC_ARRAY(x, t, n) \
    x = (t*)malloc(n * sizeof(t)); \
    if (!x) MEMORY_ERROR; \

// ==================================================
//
//  Function Types
//
// ==================================================

typedef const char* (*StringifyFunction)(void*);

#endif
