#if !defined(set_h)
#define set_h

#include <stdbool.h>

#include "rams.h"

typedef struct Set* Set;

typedef void* SetValue;

typedef void* SetIterator;

typedef bool (*CompareFunction)(SetValue, void*);

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

extern void set_dump(Set, StringifyFunction);

extern bool set_equals(Set, Set);
extern Set set_intersection(Set, Set);

#endif
