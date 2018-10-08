#if !defined(bb_h)
#define bb_h

#include <llvm-c/Core.h>

#include "list.h"

typedef struct BB* BB;
struct BB {
    const char* name;
    LLVMBasicBlockRef llvm;
    List* successors;
    List* predecessors;
};

typedef struct BBs* BBs;
struct BBs {
    size_t size;
    BB* array;
};

extern BBs bbs_successors_predecessors(LLVMValueRef function);

#endif
