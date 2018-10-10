#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

#include "list.h"
#include "malloc.h"
#include "set.h"

struct Set {
    List* list;
};

Set set_new(void) {
    Set set;
    MALLOC(set, struct Set);
    set->list = list_new();
    return set;
}

Set set_clone(Set set) {
    Set new = set_new();
    for (ListNode* node = list_first(set->list); node; node = list_next(node)) {
        set_add(new, (SetValue)list_value(node));
    }
    return new;
}

void set_free(Set set) {
    list_free(set->list);
    free(set);
}

size_t set_size(Set set) {
    return list_size(set->list);
}

void set_add(Set set, SetValue value) {
    list_append(set->list, (ListValue)value);
}

void set_remove(Set set, SetValue value) {
    assert(NULL); // TODO
}

SetValue set_get(Set set, void* value, CompareFunction compare) {
    for (ListNode* node = list_first(set->list); node; node = list_next(node)) {
        ListValue listvalue = list_value(node);
        if (compare((void*)listvalue, value)) {
            return (SetValue)listvalue;
        }
    }
    return NULL;
}

bool set_contains(Set set, SetValue value) {
    for (ListNode* node = list_first(set->list); node; node = list_next(node)) {
        if (list_value(node) == (ListValue)value) {
            return true;
        }
    }
    return false;
}

bool set_is_empty(Set set) {
    return list_size(set->list) == 0;
}

SetIterator set_iterator(Set set) {
    return (SetIterator)list_first(set->list);
}

SetIterator set_iterator_next(SetIterator iterator) {
    return (SetIterator)list_next(iterator);
}

SetValue set_iterator_value(SetIterator iterator) {
    return (SetValue)list_value((ListNode*)iterator);
}

void set_dump(Set set, const char* (*value_string)(void*)) {
    printf("[");
    for (ListNode* e = list_first(set->list); e; e = list_next(e)) {
        void* value = (void*)list_value(e);
        printf("%s%s", value_string(value), list_next(e) ? ", " : "");
    }
    printf("]");
}

Set set_intersection(Set set1, Set set2) {
    List* list = set1->list;
    Set set = set2;
    if (list_size(list) > list_size(set2->list)) {
        list = set2->list;
        set = set1;
    }

    Set intersection = set_new();
    for (ListNode* node = list_first(list); node; node = list_next(node)) {
        SetValue value = (SetValue)list_value(node);
        if (set_contains(set, value)) {
            set_add(intersection, value);
        }
    }

    return intersection;
}
