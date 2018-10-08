#include <stdlib.h>

#include "list.h"
#include "malloc.h"

struct ListNode {
    ListValue value;
    ListNode* next;
    ListNode* previous;
};

struct List {
    size_t size;
    ListNode* first;
    ListNode* last;
};

List* list_new(void) {
    List* list;
    MALLOC(list, List);
    list->size = 0;
    list->first = NULL;
    list->last = NULL;
    return list;
}

size_t list_size(List* list) {
    return list->size;
}

ListNode* list_first(List* list) {
    return list->first;
}

ListNode* list_last(List* list) {
    return list->last;
}

void list_append(List* list, ListValue value) {
    ListNode* node;
    MALLOC(node, ListNode);
    node->value = value;
    node->next = NULL;

    if (list->size == 0) {
        node->previous = NULL;
        list->first = node;
        list->last = node;
    } else {
        node->previous = list->last;
        list->last->next = node;
        list->last = node;
    }

    list->size++;
}

ListValue list_value(ListNode* node) {
    return node->value;
}

ListNode* list_next(ListNode* node) {
    return node->next;
}

ListNode* list_previous(ListNode* node) {
    return node->previous;
}
