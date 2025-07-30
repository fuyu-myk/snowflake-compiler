# Snowflake-Compiler
This project documents my journey in learning Rust and subsequently coding a compiler. I referenced Julian Hartl's video series on YouTube for the creation of this project.

## Compiler architecture
Thus far, the current compiler architecture is highlighted below:

`input code` -> [Lexical Analyser] -> [Syntax Analyser] -> [Semantic Analyser] -> [IR Lowering + optimisations] -> [x86_64 backend]

* A C transpiler backend is used for this compiler for now
* The final goal will be to adopt an LLVM backend 

## Current features

### Architecture

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

- [x] **C transpiler** [WIP]
* A basic C transpiler has been implemented as a temporary backend

- [ ] **Intermediate Representation (IR) Lowering**
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
    
    - [x] *MIR Optimisations* [completed 30.07.2025]
    * Optimisations that aims to enhance the performance and efficiency of the executed code
    * The optimisations implemented are as follows:
        * Dead Code Elimination - Eg: removal of unused declared variables
        * Unreachable Code Elimination - Eg: blocks with no incoming edges are eliminated
        * Branch Elimination - Removal of unneeded branches
        * Copy Propagation - Reduces compile time by reducing copying
        * Constant Folding - Variables that can be computed at compile time are computed
        * Algebraic Simplification - Using mathematical properties to reduce complexity of expressions in the code
    
    -[ ] *Low-level IR (LIR)*

### Types supported
* Integers
* Boolean
* TODO: Strings

### Operators
- [x] **Basic arithmetic support** [completed 05.06.2025]
* Ability to apply BODMAS to evaluate the below statement:
```
6 - (23 + 8) * 10 / 3
```

- [x] **Bitwise operations support** [completed 08.06.2025]
* Ability to apply bitwise operations to evaluate the below statement:
    * TODO: Shift operations
```
-1 + 2 * 3 - 4 / 5 | 6 + ~6 ^ 7 ** 2
```

- [x] **Relational operators** [completed 09.06.2025]

- [ ] **Assignment operators**

### Functionalities
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
    while a < 10 [
        a = a + 1
    ]
    ```

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

    fx foo(a, b) {
        return a + b
    }
    ```

- [x] **Types & type checking** [completed 14.06.2025]
* Ability to declare and infer types
    ```
    let x: int = 86
    let y: bool = true
    let z: string = "Hello World"
    let a = 10 // type inference => int
    ```  