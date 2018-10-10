#if !defined(set_h)
#define set_h

#include <stdbool.h>

typedef struct Set* Set;

typedef void* SetValue;

typedef void* SetIterator;

typedef bool (*CompareFunction)(void*, void*);

typedef const char* (*ValueDumpFunction)(void*);

extern Set set_new(void);
extern Set set_clone(Set);
extern void set_free(Set);

extern size_t set_size(Set);

extern void set_add(Set, SetValue);
extern void set_remove(Set, SetValue);

extern SetValue set_get(Set, void*, CompareFunction);
extern bool set_contains(Set, SetValue);
extern bool set_is_empty(Set);

extern SetIterator set_iterator(Set);
extern SetIterator set_iterator_next(SetIterator);
extern SetValue set_iterator_value(SetIterator);

extern void set_dump(Set, ValueDumpFunction);

extern Set set_intersection(Set, Set);

#endif
