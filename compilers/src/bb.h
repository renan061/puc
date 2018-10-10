#if !defined(bb_h)
#define bb_h

#include <llvm-c/Core.h>

#include "set.h"

typedef struct BB* BB;
struct BB {
    const char* name;
    LLVMBasicBlockRef llvm;
    Set successors;
    Set predecessors;
};

typedef struct BBs* BBs;
struct BBs {
    size_t size;
    BB* array;

    // dominance[i] is the set of all nodes that dominate basic block array[i]
    Set* dominance;
};

extern BBs bbs_successors_predecessors(LLVMValueRef function);
extern void bbs_dominance(BBs);

#endif
