#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include <llvm-c/Core.h>

#include "list.h"
#include "malloc.h"
#include "bb.h"

static void bbs_dump(BBs);

// TODO: move
const char* bb_string(void* bb) {
    return ((BB)bb)->name;
}

// TODO: move
bool bb_name_compare(void* bb, void* name) {
    return ((BB)bb)->name == name;
}

BB bb_new(LLVMBasicBlockRef block) {
    BB bb;
    MALLOC(bb, struct BB);
    bb->name = LLVMGetBasicBlockName(block);
    bb->llvm = block;
    bb->successors = set_new();
    bb->predecessors = set_new();
    return bb;
}

BBs bbs_new(size_t size) {
    BBs bbs;
    MALLOC(bbs, struct BBs);
    bbs->size = size;
    MALLOC_ARRAY(bbs->array, BB, size);
    MALLOC_ARRAY(bbs->dominance, Set, size);
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
            set_add(bb->successors, (SetValue)successor);
        }
    }

    // sets the predecessors for each block
    for (unsigned i = 0; i < bbs->size; i++) {
        BB bb = bbs->array[i];
        for (SetIterator* iterator = set_iterator(bb->successors); iterator;) {
            BB successor = (BB)set_iterator_value(iterator);
            set_add(successor->predecessors, (SetValue)bb);
            iterator = set_iterator_next(iterator);
        }
    }

    bbs_dump(bbs);

    return bbs;
}

void bbs_dominance(BBs bbs) {
    // // nodes: Set<Node>, predecessor: Node, r: Node
    // // nodes: Set<Node>, predecessor: Node, index: Integer

    // // initializes the set that contains all basic blocks
    // Set all = set_new();
    // for (int i = 0; i < bbs->size; i++) {
    //     set_add(all, (SetValue)bbs->array[i]);
    // }

    // // D: Set<Node>
    // Set D, T;
    // // n, p: Node
    // bool change = true;
    // // dominance[i] = {i}
    // bbs->dominance[index] = set_new();
    // set_add(bbs->dominance[index], bbs->array[i]);

    // for (int i = 1; i < bbs->size; i++) {
    //     // dominance[i] = {1, 2, ..., N}
    //     bbs->dominance[i] = set_clone(all);
    // }

    // do {
    //     change = false;
    //     for (int i = 1; i < bbs->size; i++) {
    //         T = set_clone(all);
    //         for (ListNode* e = list_first(bbs->array[i]->predecessors); e;) {
    //             // BB predecessor = (BB)list_value(e);
    //             // Set temp = 
    //             // e = list_next(e);
    //         }
    //     }
    // } while (change);
}

void bbs_df(BBs bbs) {
    // TODO
    // DFlocal(x) = { y E Succ(x) | idom(y) != x             }
    // DFup(x,z)  = { y E DF(z) | idom(z) = x & idom(y) != x }
    // DF(x)      = DFlocal(x) U U[z E N idom(z) = x] DFup(x, z)
}

// ==================================================
//
//  Auxiliary
//
// ==================================================

static void bbs_dump(BBs bbs) {
    for (unsigned i = 0; i < bbs->size; i++) {
        BB bb = bbs->array[i];

        printf("%s \t(%zu, s[%d])", bb->name, set_size(bb->successors), i);
        set_dump(bb->successors, &bb_string);
        printf("\n");

        printf("%s \t(%zu, p[%d])", bb->name, set_size(bb->predecessors), i);
        set_dump(bb->predecessors, &bb_string);
        printf("\n===\n");            
    }
}
