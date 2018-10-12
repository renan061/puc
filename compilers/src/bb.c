#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include <llvm-c/Core.h>

#include "list.h"
#include "rams.h"
#include "bb.h"

static void bbs_dump(BBs);

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

int bbs_find_index(BBs xs, BB x) {
    for (int i = 0; i < (int)xs->size; i++) {
        if (xs->array[i] == x) {
            return i;
        }
    }
    return -1;
}

BBs bbs_successors_predecessors(LLVMValueRef function) {
    size_t bbs_count = LLVMCountBasicBlocks(function);
    assert(bbs_count != 0);

    // initializes the array of basic blocks
    BBs bbs = bbs_new(bbs_count);

    { // loops each block, and sets the block in the array of blocks
        size_t i = 0;
        LLVMBasicBlockRef bb = LLVMGetFirstBasicBlock(function);
        while (bb) {
            bbs->array[i++] = bb_new(bb);
            bb = LLVMGetNextBasicBlock(bb);
        }
    }    

    // sets the successors for each block
    for (int i = 0; i < (int)bbs->size; i++) {
        BB bb = bbs->array[i];

        // gets the terminator instruction for the current block
        LLVMValueRef terminator = LLVMGetBasicBlockTerminator(bb->llvm);
        assert(terminator);

        // sets the successors for the current basic block
        int num_successors = LLVMGetNumSuccessors(terminator);
        for (int j = 0; j < num_successors; j++) {
            const char* name = LLVMGetBasicBlockName(
                LLVMGetSuccessor(terminator, j)
            );
            set_add(bb->successors, (SetValue)bbs_find(bbs, name));
        }
    }

    // sets the predecessors for each block
    for (int i = 0; i < (int)bbs->size; i++) {
        BB bb = bbs->array[i];
        for (SetIterator* iterator = set_iterator(bb->successors); iterator;) {
            BB successor = (BB)set_iterator_value(iterator);
            set_add(successor->predecessors, (SetValue)bb);
            iterator = set_iterator_next(iterator);
        }
    }

    return bbs;
}

void bbs_dominance(BBs bbs) {
    // initializes the set that contains all basic blocks
    Set all = set_new();
    for (int i = 0; i < (int)bbs->size; i++) {
        set_add(all, (SetValue)bbs->array[i]);
    }

    Set d;
    Set t;
    bool change = true;

    // dominance[entry] = {entry}
    bbs->dominance[0] = set_new();
    set_add(bbs->dominance[0], bbs->array[0]);

    // all nodes except for "entry" start dominanting all nodes
    for (int i = 1; i < (int)bbs->size; i++) {
        bbs->dominance[i] = set_clone(all);
    }

    do {
        change = false;

        // all nodes except for "entry"
        for (int i = 1; i < (int)bbs->size; i++) {
            BB bb = bbs->array[i];

            t = set_clone(all);

            for (SetIterator si = set_iterator(bb->predecessors); si;) {
                BB predecessor = set_iterator_value(si);

                // t = t `intersection` dominance[predecessor]
                Set temp = t;
                int predecessor_index = bbs_find_index(bbs, predecessor);
                t = set_intersection(t, bbs->dominance[predecessor_index]);
                set_free(temp);

                si = set_iterator_next(si);
            }

            // d = {bb} U t
            d = set_clone(t);
            set_add(d, bb);
            if (!set_equals(d, bbs->dominance[i])) {
                change = true;
                bbs->dominance[i] = d;
            } else {
                set_free(d);
            }
        }
    } while (change);

    bbs_dump(bbs);
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

static const char* bb_to_name(void* bb) {
    return ((BB)bb)->name;
}

static void bbs_dump(BBs bbs) {
    printf("-------------------------\n");

    for (int i = 0; i < (int)bbs->size; i++) {
        BB bb = bbs->array[i];

        printf("%s \t(%zu, s[%d])", bb->name, set_size(bb->successors), i);
        set_dump(bb->successors, bb_to_name);
        printf("\n");

        printf("%s \t(%zu, p[%d])", bb->name, set_size(bb->predecessors), i);
        set_dump(bb->predecessors, bb_to_name);
        if (i + 1 < (int)bbs->size) {
            printf("\n-----\n");
        } else {
            printf("\n");
        }
    }

    printf("-------------------------\n");

    for (int i = 0; i < (int)bbs->size; i++) {
        BB bb = bbs->array[i];
        printf("%s \t(%zu, d[%d])", bb->name, set_size(bbs->dominance[i]), i);
        set_dump(bbs->dominance[i], bb_to_name);
        printf("\n");
    }

    printf("-------------------------\n");
}
