#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include <llvm-c/Core.h>

#include "list.h"
#include "malloc.h"
#include "bb.h"

static void bbs_dump(BBs);

BB bb_new(LLVMBasicBlockRef block) {
    BB bb;
    MALLOC(bb, struct BB);
    bb->name = LLVMGetBasicBlockName(block);
    bb->llvm = block;
    bb->successors = list_new();
    bb->predecessors = list_new();
    return bb;
}

BBs bbs_new(size_t size) {
    BBs bbs;
    MALLOC(bbs, struct BBs);
    bbs->size = size;
    MALLOC_ARRAY(bbs->array, BB, size);
    return bbs;
}

BB bbs_find(BBs bbs, const char* name) {
    for (size_t i = 0; i < bbs->size; i++) {
        if (bbs->array[i]->name == name) {
            return bbs->array[i];
        }
    }
    return NULL;
}

BBs bbs_successors_predecessors(LLVMValueRef function) {
    // if the function has no basic blocks, return NULL
    size_t num_bbs = LLVMCountBasicBlocks(function);
    if (num_bbs == 0) {
        return NULL;
    }

    // initializes the array of basic blocks
    BBs bbs = bbs_new(num_bbs);

    // loops each block, and sets the block in the array of blocks
    size_t i = 0;
    for (LLVMBasicBlockRef bb = LLVMGetFirstBasicBlock(function); bb;) {
        bbs->array[i++] = bb_new(bb);
        bb = LLVMGetNextBasicBlock(bb);
    }

    // sets the successors for each block
    for (unsigned i = 0; i < bbs->size; i++) {
        BB bb = bbs->array[i];

        // gets the terminator instruction for the current block
        LLVMValueRef terminator = LLVMGetBasicBlockTerminator(bb->llvm);
        assert(terminator);

        // sets the successors for the current basic block
        unsigned num_successors = LLVMGetNumSuccessors(terminator);
        for (unsigned j = 0; j < num_successors; j++) {
            LLVMBasicBlockRef block = LLVMGetSuccessor(terminator, j);
            const char* successor_name = LLVMGetBasicBlockName(block);
            BB successor = bbs_find(bbs, successor_name);
            list_append(bb->successors, (void*)successor);
        }
    }

    // sets the predecessors for each block
    for (unsigned i = 0; i < bbs->size; i++) {
        BB bb = bbs->array[i];
        ListNode* first = list_first(bb->successors);
        for (ListNode* node = first; node; node = list_next(node)) {
            BB successor = (BB)list_value(node);
            list_append(successor->predecessors, (void*)bb);
        }
    }

    bbs_dump(bbs);

    return bbs;
}

// ==================================================
//
//  Auxiliary
//
// ==================================================

static void bbs_dump(BBs bbs) {
    for (unsigned i = 0; i < bbs->size; i++) {
        BB bb = bbs->array[i];

        printf("%s \t(%zu, s[%d])", bb->name, list_size(bb->successors), i);
        ListNode* first = list_first(bb->successors);
        for (ListNode* node = first; node; node = list_next(node)) {
            BB successor = (BB)list_value(node);
            printf(" %s", successor->name);
        }
        printf("\n");

        printf("%s \t(%zu, p[%d])", bb->name, list_size(bb->predecessors), i);
        first = list_first(bb->predecessors);
        for (ListNode* node = first; node; node = list_next(node)) {
            BB predecessor = (BB)list_value(node);
            printf(" %s", predecessor->name);
        }
        printf("\n===\n");            
    }
}
