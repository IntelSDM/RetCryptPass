# Ret Crypt Pass
Built for LLVM 19.1 - Windows x64 <br> <br>

This is a component of Nessa's homomorphism engine.<br> 
The idea is quite simple, Certain function calls will pass constants through them. <br>

The concept is very very simple, You mark a function with `retcrypt` and it will then find all xrefs, clone a copy of the function; so each function has 1 return address. <br>
Then we encrypt the copy with the return address of the known caller. <br>
Due to how different functions return, we use an annotation here, processing everything at link time as a function pass when downstream optimisations can turn functions we use into different calling conventions makes it difficult to know if it will still return to the same address. <br>
It also doesn't account for things like threading, callbacks and other indirect pointer calling, so you need to be careful with the annotation usecase. <br>

<br>
<img width="698" height="900" alt="image" src="https://github.com/user-attachments/assets/3d158104-8c87-4da4-9b81-84861d100999" />
<br>
<img width="1413" height="965" alt="image" src="https://github.com/user-attachments/assets/084073bf-1253-49d4-87f6-4fadb196415d" />

## Annotations
```c
__attribute__((annotate("retcrypt")))
``` 
* Activates the pass on the function

## How To Build
* Download [LLVM 19.1](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.0)
* Download [VCPKG](https://github.com/microsoft/vcpkg)
* VCPKG install asmjit
* Open build.bat in a text editor.
* Find the LLVM 19.1 references in the command line, Change them to your file path.
* Find the VCPKG references in the command line, Change them to your file path.
* Run the build script
* Build your application with the ``` -load-pass-plugin ``` Param to the FunctionPass.dll
