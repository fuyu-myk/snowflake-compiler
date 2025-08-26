# Snowflake-Compiler
This project documents my journey in learning Rust and subsequently coding a compiler. 

Compilers have always been a black box to me, ever since I learnt C some time back. Intrigued by my friend's infectious enthusiasm on the subject, I went to do my own reading and was fascinated by how compilers work. So fascinated that I challenged myself to (attempt to) code one from scratch, doing so with an equally interesting programming language. Though there are no immediate plans on creating my own programming language, I chose to use my own syntax (for certain keywords at least) as sort of a personal touch.

I referenced Julian Hartl's video series on YouTube for the creation of this project.

# Compiler architecture
Thus far, the current compiler architecture is highlighted below:

`input code` -> [Lexical Analyser] -> [Syntax Analyser] -> [Semantic Analyser] -> [IR Lowering + optimisations] -> [Backend]

## Backends explored
* C-transpiler
* [`iced_x86`](https://github.com/icedland/iced)
* LLVM
    * The [`inkwell`](https://github.com/TheDan64/inkwell) library is used due to my unfamiliarity with LLVM

# Current features

## Architecture

- [x] **Lexer** [completed 04.06.2025]
* Takes in an input and transforms it to a token stream

- [x] **Parser** [completed 05.06.2025]
* Takes in input data (text; Tokens) and builds the Abstract Syntax Tree (AST)
* Gives structural representation of the input while also checking for appropriate syntax

- [x] **Semantic Analyser** [WIP]
* Updated as more functionality is added
* Resolves semantic information
    * Checks AST for errors

- [x] **Evaluator** [WIP]
* Updated as more functionality is added
* Used in place of a backend for now

- [x] **C transpiler**
* A basic C transpiler has been implemented as a temporary backend

- [x] **Intermediate Representation (IR) Lowering** [completed 09.08.2025]
* Transformation of IR to lower-level representation
    * Essentially preparing the IR for efficient backend code generation

    - [x] *High-level IR (HIR)* [completed 24.06.2025]
    * Removal/change of certain structures to facilitate type and syntax analyses
        * One such example are loops as shown:

        ```
        while a > 0 {
            a = a - 1
        }
        ```
        ```
        loop {
            if a > 0 {
                a = a - 1
            } else {
                break
            }
        }
        ```
    * Proper span tracking for diagnostics

    - [x] *Mid-level IR (MIR)* [completed 28.04.2025]
    * Based on a control-flow graph (CFG)
    * No nested expressions
    * Explicit types
    * Consists of:
        * Basic blocks - nodes of the CFG
        ```
        bb0: {
            statement0; // one successor each
            statement1;
            ...
            terminator; // potential multiple successors; always at end of bb
        }
        ```
        * Locals - function arguments, local variables etc.
    * Proper span tracking for diagnostics
    
    - [x] *MIR Optimisations* [completed 30.07.2025]
    * Optimisations that aims to enhance the performance and efficiency of the executed code
    * The optimisations implemented are as follows:
        * Dead Code Elimination - Eg: removal of unused declared variables
        * Unreachable Code Elimination - Eg: blocks with no incoming edges are eliminated
        * Branch Elimination - Removal of unneeded branches
        * Copy Propagation - Reduces compile time by reducing copying
        * Constant Folding - Variables that can be computed at compile time are computed
        * Algebraic Simplification - Using mathematical properties to reduce complexity of expressions in the code
    
    - [x] *Low-level IR (LIR)* [completed 09.08.2025]
    * Further lowering of MIR to facilitate iced_x86 codegen
        * Instructions become more 'assembly-like'

- [x] **X86_64 Assembly Code Generation** [completed 15.08.2025]
* Utilising the [`iced_x86`](https://github.com/icedland/iced) library to generate assembly instructions
* Limited type support for now
* Incredibly unoptimised
* *Huge WIP as I am unfamiliar with assembly*
* *Also, I am not going to do codegen for all instruction types; pivoting to LLVM instead*

- [x] **LLVM IR Generation** [WIP]
* The inkwell wrapper is used to lower complexity
* The generated IR is then written to a temp file, eg: `temp.ll`
* An executable is then generated through `Clang`

## Types supported
### Primitives
- [x] Integers
- [x] Floats
- [x] Boolean
- [x] Strings

### Data Structures supported
- [x] Arrays [completed 05.08.2025]
    * Defined and indexed as follows:
```
// One dimensional array
let arr: [int, 3] = [1, 2, 3];
let a: int = a[0]; // 1

// Multi-dimensional array
let matrix: [[int; 3]; 3] = [[1, 2, 3], [4, 5, 6], [7, 8, 9]];
let b: int = matrix[0][2] + matrix[2][0]; // 10
```
* Type is defined as `[T, len]`
> [!NOTE]
> `T` can be of type `[T, len]` in multi-dimensional arrays
* Indexes are of type `usize`
* TODO: Slice indexes

- [x] Tuples [completed 25.08.2025]
    * Defined and indexed as follows:
```
let tuple: (int, float, string) = (1, 1.01, "hello");
let a: int = tuple.0;
let b: float = tuple.1;
let c: string = tuple.2;
```
* Type is defined as `(T1, T2)`

## Operators
- [x] **Basic arithmetic support** [completed 05.06.2025]
* Ability to apply BODMAS to evaluate the below statement:
```
6 - (23 + 8) * 10 / 3
```

- [x] **Bitwise operations support** [completed 08.06.2025]
* Ability to apply bitwise operations to evaluate the below statement:
```
-1 + 2 * 3 - 4 / 5 | 6 + ~6 ^ 7 ** 2
```

- [x] **Relational operators** [completed 09.06.2025]

- [x] **Assignment operators** [completed 01.08.2025]
* Handled by desugaring
    * For example, `a += 5` becomes `a = (a + 5)`
* Such assignment expressions return a void type; thereby disallowing expressions such as:
```
a += 5 -= 1 // lhs must have same type (int) as rhs
```
* On the other hand, expressions such as below are valid
```
a += a * 2 + 3
```
* TODO: Perhaps find a better way of handling spans

## Functionalities
- [x] **Error reporting** [WIP]
* Updated as more functionality is added
* Highlights errors in red
* Error messages are printed in a specific format

- [x] **`let` statements** [completed 06.06.2025]
* Variable lexing, parsing & error checking
* Ability to parse and evaluate the below statement:
    ```
    let a = 2 + 6
    let b = 23
    let c = a + b
    ```

- [x] **Scoping functionality** [completed 09.06.2025]
* Variables defined in the scope only exists throughout the lifetime of the scope
    * Global and Local scopes implemented
* Ability to parse and evaluate the below statement:
    ```
    let a = 2301
    {
        let a = 806
    }
    ```

- [x] **`if` statements** [completed 09.06.2025]
* Inclusive of optional `else` statements
* Ability to parse and evaluate the below statement:
    ```
    let a = 23
    if a > 8 {
        a = 8
    } else {
        a = 6
    }
    ```
* `if` can also be used in a `let` statement like so:
    ```
    let a = 10
    let b = 20
    let d = if a == b {
            10
        } else {
            20
        }
    ```

- [x] **`while` loops** [completed 09.06.2025]
* Ability to parse and evaluate the below statement:
    ```
    let a = 0
    while a < 10 {
        a = a + 1
        // a += 1 also works
    }
    ```
* `return` can also be used to return a value immediately:
    ```
    let a = 0
    while a < 10 {
        if a >= 5 {
            return a;
        }
        a += 1
    }
    // returns 5
    ```
* `break` and `continue` can also be used to exit the loop and skip the current iteration respectively

- [x] **Functions** [completed 11.06.2025]
* Ability to define, parse, store and evaluate functions
    * Local scope created per function
* Functions here are defined using the `fx` keyword
* Functions do not need to be defined with variables
    * Such functions can be defined without parentheses
* Functions are items and not expressions
* Function's types are checked during parsing
* Some examples:
    ```
    fx dog {

    }
    ```
    ```
    fx foo(a: int, b: int) -> int {
        return a + b
    }
    ```
    ```
    fx cat() -> int {
        let a = 0;

        while a < 10 {
            if a >= 5 {
                return a;
            }

            a += 1;
        }

        return a + 1;
    }
    // cat() returns 5
    ```

- [x] **Types & type checking** [completed 14.06.2025]
* Ability to declare and infer types
    ```
    let x: int = 86
    let y: bool = true
    let z: string = "Hello World"
    let a = 10 // type inference => int
    ```  
* Explicit suffix typecasting (WIP as more types are supported)
    * Current supported suffixes are outlined below:
    ```
    let x = 8usize
    ```

- [x] **Comments** [completed 05.08.2025]
* Both line and block comments, in traditional C syntax
* Nested block comments are not supported
    ```
    // This is a line comment

    /* This is 
    a
    block comment */
    ```

- [x] **Runtime panics** [WIP]
* Will abort the program and generate a diagnostic in the following scenarios:
    * Illegal index access for arrays in runtime
* Currently WIP, will improve handling and include more scenarios in future

- [x] **Mutability** [completed 27.08.2025]
* Similar to Rust's mutability
* Defined through the `mut` keyword