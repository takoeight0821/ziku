# External Builtins Implementation Design Space

## Overview

This document surveys the design space for implementing external/foreign builtins in programming languages. It covers FFI (Foreign Function Interface) design patterns, runtime extension mechanisms, and the tradeoffs involved in different approaches.

**Relevance to Ziku**: PR #40 proposes adding external builtins via YAML configuration and Scheme code generation. This research informs design decisions and identifies potential improvements.

---

## 1. Taxonomy of Extension Mechanisms

### 1.1 Compile-Time vs Runtime Binding

| Approach | Description | Examples | Tradeoffs |
|----------|-------------|----------|-----------|
| **Compile-time intrinsics** | Compiler recognizes special functions, generates optimized code | GCC `__builtin_*`, LLVM intrinsics | Fast, type-safe; inflexible |
| **Static FFI** | Foreign calls resolved at link time | GHC unsafe FFI, OCaml external | Good performance; requires recompilation |
| **Dynamic FFI** | Foreign calls resolved at runtime via libffi | Racket FFI, Python ctypes | Flexible; overhead, less type safety |
| **Subprocess/IPC** | External process handles calls | **Ziku's current approach** | Most flexible; highest overhead |

### 1.2 Type Safety Spectrum

```
Full static checking ←————————————————————→ No checking
        │                                        │
   OCaml ctypes                             Ziku (YAML)
   Haskell FFI                              Dynamic FFI
```

---

## 2. Design Patterns

### 2.1 Intrinsic Functions (Compiler Built-ins)

**Definition**: Functions whose implementation is handled specially by the compiler, often substituting optimized instruction sequences.

**Characteristics** ([Wikipedia](https://en.wikipedia.org/wiki/Intrinsic_function)):
- Compiler has intimate knowledge of the function
- Better integration and optimization than inline functions
- May fall back to library implementation without optimization

**LLVM Approach** ([LLVM Docs](https://llvm.org/docs/ExtendingLLVM.html)):
- Intrinsics prefixed with `llvm.`
- Adding intrinsics is "far easier than adding an instruction"
- Must describe memory access characteristics for optimization
- "Almost all extensions to LLVM should start as an intrinsic"

**GCC Built-ins** ([GCC Manual](https://gcc.gnu.org/onlinedocs/gcc/Built-in-Functions.html)):
- Large number of implicitly-declared builtins
- Some correspond to standard library routines
- Others expose low-level functionality or target-specific instructions

### 2.2 Foreign Function Interface (FFI)

**Definition**: Mechanism for calling functions compiled in another language.

**Key Challenges** ([Wikipedia](https://en.wikipedia.org/wiki/Foreign_function_interface), [Inko](https://inko-lang.org/news/the-challenge-of-building-a-foreign-function-interface/)):

1. **Type Mapping**: Converting between language representations
   - Integers: Size differences (e.g., passing 300 to C `char`)
   - Strings: NULL termination, encoding differences
   - Complex types: Structs, unions, pointers

2. **Memory Management**: GC vs manual allocation
   - JNI: C code must communicate object references to JVM
   - Explicit release required when C no longer needs objects

3. **Calling Conventions**: ABI differences
   - stdcall, cdecl, fastcall on x86
   - Varargs handling complications

4. **Multitasking**: Thread scheduling interactions
   - Pre-emptive languages may move tasks between OS threads
   - Blocking C calls can exhaust thread pools (M:N scheduling)

5. **Callbacks**: Allowing foreign code to call back
   - Stack unwinding complexities
   - GC interaction issues
   - "Difficult enough that C callbacks simply are not supported" in some languages

### 2.3 Plugin/Extension Systems

**Dynamic Loading Pattern** ([Eli Bendersky](https://eli.thegreenplace.net/2012/08/24/plugins-in-c)):
1. Search directory for plugin files (`.so`, `.dll`)
2. Load with `dlopen`/`LoadLibrary`
3. Find initialization function (`init_<pluginname>`)
4. Register plugin capabilities

**RPC-Based Plugins** ([hashicorp/go-plugin](https://github.com/hashicorp)):
- Plugin runs as separate process
- Communication via RPC (net/rpc or gRPC)
- Avoids version compatibility issues of dynamic loading
- Higher overhead but better isolation

---

## 3. Implementation Strategies by Language

### 3.1 Haskell (GHC)

**Safe vs Unsafe FFI** ([GHC User Guide](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/ffi.html)):

| Aspect | `safe` | `unsafe` |
|--------|--------|----------|
| Blocking | Allowed | Not allowed |
| Callbacks to Haskell | Allowed | Not allowed |
| GC during call | Possible | Guaranteed not (since GHC 8.4) |
| Performance | Substantial overhead | As fast as C call |

**Runtime Architecture**:
- User-space threads distributed on "capabilities"
- Capability management adds overhead for safe calls
- `hs_init()` required before any Haskell calls

**Memory Allocation**:
- `alloca`: Uses `MutableByteArray#`, faster than C malloc
- `mallocForeignPtr`: GC-managed, very cheap

### 3.2 Racket

**Design Philosophy** ([Racket Docs](https://docs.racket-lang.org/foreign/intro.html), [PRL Blog](https://prl.khoury.northeastern.edu/blog/2016/06/27/tutorial-using-racket-s-ffi/)):
- "Keep the C parts to a minimum"
- Library named `ffi/unsafe` as explicit safety declaration
- Dynamic interface using libffi
- Type system via combinators (`_fun`, `_ptr`, `_cstruct`)

**Key Features**:
- `foreign` function: looks up symbol via `dlsym`
- `@->` operator for building parameter lists
- `returning` terminates parameter list with return type
- Multiple allocation strategies for different tradeoffs

### 3.3 OCaml

**Traditional Approach**:
- `external` declarations link to C functions
- Requires writing C stubs manually
- Type-safe within OCaml's type system

**ctypes Library** ([GitHub](https://github.com/yallop/ocaml-ctypes)):
- Pure OCaml bindings without writing C
- Two modes: libffi (dynamic) and stub generation (compile-time)
- Combinators describe C type structure

### 3.4 Lua

**C API Design** ([Programming in Lua](https://www.lua.org/pil/24.html)):
- Emphasis on embedding and extending
- Virtual stack for all data exchange
- "Flexibility and simplicity, sometimes at the cost of ease of use"
- Host has complete control over available functions

**Extension Pattern**:
- Shared object with `luaopen_xxx` function
- Loader packs C function pointers into Lua table
- Registration makes functions available to scripts

### 3.5 Larceny (Scheme)

**Minimal Low-Level Design** ([FFI Notes](https://www.khoury.northeastern.edu/home/lth/larceny/notes/note7-ffi.html)):
- "A suitable target for interface generator tools"
- Rejects elaborate copy-avoidance mechanisms
- Requires explicit copying for type mismatches

**Calling Models**:
1. Single stack: Full continuations, expensive copying
2. Coroutines: Separate continuations, poor error handling
3. Threads: Cross-language calls as thread creation

---

## 4. libffi: The Common Foundation

**Purpose** ([libffi GitHub](https://github.com/libffi/libffi)):
- Portable foreign-function interface library
- Call functions given information at runtime instead of compile time
- "Lowest, machine dependent layer" of FFI

**Architecture**:
- Call Interface (CIF): Describes function signature
- ABI handling: Abstracts calling convention differences
- Platform support: Multiple ABIs per platform (stdcall, fastcall)

**Notable Users**:
- CPython's ctypes
- OpenJDK
- Most dynamic language FFIs

---

## 5. Type Safety Research

### 5.1 Academic Work

**"Checking Type Safety of Foreign Function Calls"** (Furr & Foster, [ACM TOPLAS](https://dl.acm.org/doi/10.1145/1377492.1377493)):
- O-Saffire (OCaml-C) and J-Saffire (JNI) type inference systems
- Ensures C code accesses high-level data safely
- Found many bugs in real-world FFI code
- Key insight: Polymorphism important for JNI; flow-sensitivity critical for OCaml

**Key Findings**:
- Static checking of FFIs valuable for correct multilingual software
- FFIs "provide a rich source of hard-to-find programming errors"

### 5.2 Verified FFI

**"A Verified Foreign Function Interface between Coq and C"** (POPL 2025):
- Formal verification of FFI correctness
- Represents frontier of FFI safety research

---

## 6. Design Tradeoffs Matrix

| Dimension | Options | Ziku PR #40 Choice |
|-----------|---------|-------------------|
| **Binding time** | Compile / Link / Runtime / IPC | Runtime + IPC (Scheme subprocess) |
| **Type safety** | Static / Dynamic / None | Dynamic (YAML signatures) |
| **Performance** | Native / libffi / Subprocess | Subprocess (highest overhead) |
| **Flexibility** | Fixed / Configurable / Arbitrary | Highly configurable (YAML) |
| **Safety** | Safe / Unsafe | Unsafe (arbitrary Scheme code) |
| **GC integration** | Automatic / Manual / None | None (subprocess isolation) |

---

## 7. Recommendations for Ziku

### 7.1 Current Approach Analysis

**Strengths**:
- Maximum flexibility (arbitrary Scheme code)
- No linking/compilation required
- Clean separation from core evaluator
- Subprocess provides isolation

**Weaknesses**:
- Highest performance overhead (process spawn per call)
- No static type checking
- Silent failure on registry not initialized (`unsafe` code)
- Security concerns (arbitrary code execution)

### 7.2 Alternative Designs

#### Option A: Compile-Time Code Generation
```
YAML → Generate Lean code → Compile with Ziku
```
- Pros: Type-safe, no runtime overhead
- Cons: Requires recompilation for new builtins

#### Option B: libffi Integration
```
YAML → libffi calls at runtime
```
- Pros: Industry standard, good performance
- Cons: Requires native library support

#### Option C: Scheme Prelude (Current, Improved)
```
YAML → Single Scheme process → Multiple calls
```
- Pros: Keeps current flexibility
- Cons: Requires persistent Scheme process management

#### Option D: Embedded Scheme Interpreter
```
YAML → Embedded Chez Scheme → Direct evaluation
```
- Pros: Fast, no process overhead
- Cons: Complex integration, binary size

### 7.3 Incremental Improvements

1. **Type Checking**: Validate YAML types against actual usage
2. **Caching**: Reuse Scheme process for multiple calls
3. **Error Handling**: Better YAML parse error reporting
4. **Timeouts**: Add subprocess timeout handling
5. **Sandboxing**: Restrict available Scheme primitives

---

## 8. Sources

### Documentation
- [Foreign Function Interface - Wikipedia](https://en.wikipedia.org/wiki/Foreign_function_interface)
- [GHC FFI User Guide](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/ffi.html)
- [Racket Foreign Interface](https://docs.racket-lang.org/foreign/index.html)
- [LLVM Extending Guide](https://llvm.org/docs/ExtendingLLVM.html)
- [GCC Built-in Functions](https://gcc.gnu.org/onlinedocs/gcc/Built-in-Functions.html)

### Implementation References
- [libffi GitHub](https://github.com/libffi/libffi)
- [ocaml-ctypes GitHub](https://github.com/yallop/ocaml-ctypes)
- [Larceny FFI Notes](https://www.khoury.northeastern.edu/home/lth/larceny/notes/note7-ffi.html)

### Academic Papers
- [Checking Type Safety of Foreign Function Calls](https://dl.acm.org/doi/10.1145/1377492.1377493) - Furr & Foster
- [Improving Quality of Software with Foreign Function Interfaces](https://www.cse.psu.edu/~gxt29/papers/SILIANG_LI_Dissertation.pdf) - Li (Dissertation)

### Tutorials & Articles
- [The Challenge of Building an FFI](https://inko-lang.org/news/the-challenge-of-building-a-foreign-function-interface/) - Inko
- [Plugins in C](https://eli.thegreenplace.net/2012/08/24/plugins-in-c) - Eli Bendersky
- [Tutorial: Using Racket's FFI](https://prl.khoury.northeastern.edu/blog/2016/06/27/tutorial-using-racket-s-ffi/) - PRL Blog
- [Real World OCaml: FFI](https://dev.realworldocaml.org/foreign-function-interface.html)
- [Programming in Lua: C API](https://www.lua.org/pil/24.html)
