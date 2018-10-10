#if !defined(list_h)
#define list_h

typedef struct List List;
typedef struct ListNode ListNode;
typedef void* ListValue;

extern List* list_new(void);
extern void list_free(List*);

extern size_t list_size(List*);
extern ListNode* list_first(List*);
extern ListNode* list_last(List*);

extern void list_append(List*, ListValue);

extern ListValue list_value(ListNode*);
extern ListNode* list_next(ListNode*);
extern ListNode* list_previous(ListNode*);

#endif
