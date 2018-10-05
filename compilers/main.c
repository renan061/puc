#include <stdio.h>

#include <llvm-c/BitReader.h>
#include <llvm-c/BitWriter.h>
#include <llvm-c/Core.h>

int main(int argc, char* argv[]) {
    if (argc != 3) {
        fprintf(stderr, "error: invalid command line arguments.\n");
        return 1;
    }

    const char *const input = argv[1];
    const char *const output = argv[2];

    // auxiliary
    LLVMBool ok;
    char* err;

    // reading the input file
    LLVMMemoryBufferRef memory_buffer;
    ok = !LLVMCreateMemoryBufferWithContentsOfFile(input, &memory_buffer, &err);
    if (!ok) {
        fprintf(stderr, "error reading the input file: %s.\n", err);
        return 1;
    }

    // creating the module
    LLVMModuleRef module;
    ok = !LLVMParseBitcode2(memory_buffer, &module);
    if (!ok) {
        fprintf(stderr, "error: could not create module.\n");
        return 1;
    }
    LLVMDisposeMemoryBuffer(memory_buffer);

    // writing the module to the output file
    ok = !LLVMWriteBitcodeToFile(module, output);
    if (!ok) {
        fprintf(stderr, "error writing bitcode to the output file.\n");
        return 1;
    }
    LLVMDisposeModule(module);

    return 0;
}
