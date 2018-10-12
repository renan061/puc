#include <stdio.h>
#include <stdlib.h>

#include <llvm-c/BitReader.h>
#include <llvm-c/BitWriter.h>
#include <llvm-c/Core.h>

#include "bb.h"

static LLVMModuleRef loadmodule(const char* const input);
static void writemodule(LLVMModuleRef module, const char* const output);

int main(int argc, char* argv[]) {
    if (argc != 3) {
        fprintf(stderr, "error: invalid command line arguments.\n");
        return 1;
    }

    const char* const input = argv[1];
    const char* const output = argv[2];
    
    LLVMModuleRef module = loadmodule(input);


    for (LLVMValueRef function = LLVMGetFirstFunction(module); function;) {
        if (LLVMCountBasicBlocks(function) != 0) {
            BBs bbs = bbs_successors_predecessors(function);
            bbs_dominance(bbs);
        }
        function = LLVMGetNextFunction(function);
    }

    writemodule(module, output);

    return 0;
}

// ==================================================
//
//  Auxiliary
//
// ==================================================

static LLVMModuleRef loadmodule(const char* const input) {
    LLVMBool ok;
    char* err;

    // reading the input file
    LLVMMemoryBufferRef memory_buffer;
    ok = !LLVMCreateMemoryBufferWithContentsOfFile(input, &memory_buffer, &err);
    if (!ok) {
        fprintf(stderr, "error reading the input file: %s.\n", err);
        exit(1);
    }

    // creating the module
    LLVMModuleRef module;
    ok = !LLVMParseBitcode2(memory_buffer, &module);
    if (!ok) {
        fprintf(stderr, "error: could not create module.\n");
        exit(1);
    }
    LLVMDisposeMemoryBuffer(memory_buffer);

    return module;
}

static void writemodule(LLVMModuleRef module, const char* const output) {
    // writing the module to the output file
    LLVMBool ok = !LLVMWriteBitcodeToFile(module, output);
    if (!ok) {
        fprintf(stderr, "error writing bitcode to the output file.\n");
        exit(1);
    }
    LLVMDisposeModule(module);
}
