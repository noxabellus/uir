# UIR todo list

## High priority, immediate
+ Handle i128 properly in LLVM abi
+ Handle function comparisons in LLVM backend
+ Pass value names through from IR in LLVM backend
+ Add optimization passes in LLVM backend
+ Create thorough test suite
+ Clean up, organize, refactor LLVM backend
+ During validation, check that types are not improperly self-referential
	(probably gives stack overflow to get their size now)

## High priority, no plan
+ Create and attach debug information in the LLVM backend
+ Create C backend

## Low priority
+ Add insert/extract element instructions for aggregates on the stack
+ Add vector types
+ Add JIT support to LLVM backend on native target

## Random ideas
+ Create a wasm backend
+ Create an interpreter
+ Generate RTTI tables such as type names and layouts
+ Generate JSON representation of items for external tools