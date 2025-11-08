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

- [x] **Evaluator** [Deprecated]

* Updated as more functionality is added
* Used in place of a backend for now

- [x] **C transpiler** [Deprecated]

* A basic C transpiler has been implemented as a temporary backend

- [x] **Intermediate Representation (IR) Lowering** [completed 09.08.2025]

* Transformation of IR to lower-level representation
    * Essentially preparing the IR for efficient backend code generation

    - [x] *High-level IR (HIR)* [completed 24.06.2025]
    * Removal/change of certain structures to facilitate type and syntax analyses
        * One such example are loops as shown:

        ```snow
        while a > 0 {
            a = a - 1
        }
        ```

        ```snow
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

        ```MIR
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

> [!NOTE]
> Phi nodes could cause odd executable generation issues in certain circumstances (like in while loops).
> They are resolved through extra logic in LLVM IR generation for `TerminatorKind::Goto`.

## Types supported

### Primitives

- [x] Integers
- [x] Floats
- [x] Boolean
- [x] Strings

### Data Structures supported

- [x] Arrays [completed 05.08.2025]

* Defined and indexed as follows:

```snow
// One dimensional array
let arr: [int; 3] = [1, 2, 3];
let a: int = a[0]; // 1

// Multi-dimensional array
let matrix: [[int; 3]; 3] = [[1, 2, 3], [4, 5, 6], [7, 8, 9]];
let b: int = matrix[0][2] + matrix[2][0]; // 10
```

* Type is defined as `[T, len]`

> [!NOTE]
> `T` can be of type `[T, len]` in multi-dimensional arrays.

* Indexes are of type `usize`
* TODO: Slice indexes

- [x] Tuples [completed 25.08.2025]

* Defined and indexed as follows:

```snow
let tuple: (int, float, string) = (1, 1.01, "hello");
let a: int = tuple.0;
let b: float = tuple.1;
let c: string = tuple.2;
```

* Type is defined as `(T1, T2)`

- [x] Structs [completed 02.09.2025]

* Defined and indexed as follows:

```snow
// Regular struct
struct MyStruct {
    first_field: <type>,
    second_field: <type>,
}

// Tuple struct
struct MyStruct(<type>, <type>);

// Unit struct
struct MyStruct;
```

* Struct names should be defined in `UpperCamelCase`, otherwise a warning would be generated

* Structs also feature generic paramter support
    * Type is inferred from the expression like so:

```snow
// Declaration
struct MyStruct<T, U> {
    first_field: T,
    second_field: U,
}

struct MyTupleStruct<T, U, V>(T, U, V);

struct MyUnitStruct<T>;

// Inference: T: int; U: float
let a = MyStruct { first_field: 1, second_field: 2.3 };

// Inference: T: int, U: float, V: string
let b = MyTupleStruct(1, 2.3, "Hello!");
```

* Structs can also be used in fields:

```snow
struct Coordinates {
    x: int,
    y: int,
    z: int,
}

struct Line {
    start: Coordinates,
    end: Coordinates,
}
```

- [x] Enumerations [completed 24.10.2025]

* Defined and accessed as follows:

```snow
enum Shapes {
    Circle(int),
    Rectangle {
        length: int,
        width: int,
    },
    Triangle {
        base: int,
        height: int,
    },
    Hexagon,
}

fx main() {
    let x: Shapes = Shapes::Circle(23);
}
```

* Enum names should be defined in `UpperCamelCase`, otherwise a warning would be generated
* TODO: Generic parameters

## Operators

- [x] **Basic arithmetic support** [completed 05.06.2025]

* Ability to apply BODMAS to evaluate the below statement:

```snow
6 - (23 + 8) * 10 / 3
```

- [x] **Bitwise operations support** [completed 08.06.2025]

* Ability to apply bitwise operations to evaluate the below statement:

```snow
-1 + 2 * 3 - 4 / 5 | 6 + ~6 ^ 7 ** 2
```

- [x] **Relational operators** [completed 09.06.2025]

- [x] **Assignment operators** [completed 01.08.2025]

* Handled by desugaring
    * For example, `a += 5` becomes `a = (a + 5)`
* Such assignment expressions return a void type; thereby disallowing expressions such as:

```snow
a += 5 -= 1 // lhs must have same type (int) as rhs
```

* On the other hand, expressions such as below are valid

```snow
a += a * 2 + 3
```

- [x] **Logical operators** [completed 04.11.2025]

* Logical and and logical or for booleans

```snow
// Assuming a, b, c and d are bool
if a && b {
    // do something
}

if c || d {
    // do something else
}
```

* TODO: Perhaps find a better way of handling spans

## Functionalities

- [x] **Diagnostic reporting** [WIP]

* Updated as more functionality is added
* Errors (in red)
    * Diagnostics have a special format
* Warnings (in yellow)
    * Underlined with waves "~"

- [x] **`let` statements** [completed 06.06.2025]

* Variable lexing, parsing & error checking
* Ability to parse and evaluate the below statement:

    ```snow
    let a = 2 + 6
    let b = 23
    let c = a + b
    ```

- [x] **Scoping functionality** [completed 09.06.2025]

* Variables defined in the scope only exists throughout the lifetime of the scope
    * Global and Local scopes implemented
* Ability to parse and evaluate the below statement:

    ```snow
    let a = 2301
    {
        let a = 806
    }
    ```

- [x] **`if` expressions** [completed 09.06.2025]

* Inclusive of optional `else` expressions
* Can be chained with additional `if` expressions
* Ability to parse and evaluate the below expression:

    ```snow
    let a = 23
    if a > 8 {
        a = 2
    } else if a == 8 {
        a = 3
    } else {
        a = 6
    }
    ```

* `if` can also be used in a `let` statement like so:

    ```snow
    let a = 10
    let b = 20
    let d = if a == b {
            10
        } else {
            20
        }
    ```

- [x] **`while` loops** [completed 09.06.2025]

* Ability to parse and evaluate the statement below:

    ```snow
    let a = 0
    while a < 10 {
        a = a + 1
        // a += 1 also works
    }
    ```

* `return` can also be used to return a value immediately:

    ```snow
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

- [ ] **`for` loops** [WIP]

* Ability to parse and evaluate the statement below:

    ```snow
    let elements: [int; 3] = [1, 2, 3];
    for element in elements {
        // do something
    }
    ```

* In future, comprehension may be explored

    ```snow
    let elements: [int; 5] = [1, 2, 3, 4, 5];
    let new_elements = [element * 2 for element in elements if element %% 2 == 0];
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

    ```snow
    fx dog {

    }
    ```

    ```snow
    fx foo(a: int, b: int) -> int {
        return a + b
    }
    ```

    ```snow
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

    ```snow
    let x: int = 86
    let y: bool = true
    let z: string = "Hello World"
    let a = 10 // type inference => int
    ```  

* Explicit suffix typecasting (WIP as more types are supported)
    * Current supported suffixes are outlined below:

    ```snow
    let x = 8usize
    ```

* A block's final value will be inferred from the last expression statement without semicolons
    * Works for anything with block expressions, i.e. function blocks, if/else blocks, while loop blocks, etc

    ```snow
    // Inference: int
    fx foo() {
        let a: int = 8;
        a
    }

    // Inference: SomeStruct
    fx bar() {
        let a: SomeStruct = SomeStruct::new();
        a
    }
    ```

- [x] **Comments** [completed 05.08.2025]

* Both line and block comments, in traditional C syntax
* Nested block comments are not supported

    ```snow
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

- [x] **Compile-time constants** [completed 27.08.2025]

* Defined through the `const` keyword
* Works the same as other languages, i.e. cannot be assigned to
* Should always be defined in `UPPER_CASE` (though you could define it in `lower_case` as well)
* Must have an explicit type annotation

- [x] **Implementations** [completed 03.11.2025]

* Defined throught the `impl` keyword
* Associate functions and constants with specific data type
* TODO: Generic parameters

    ```snow
    struct Rectangle {
        x: int,
        y: int,
    }

    impl Rectangle {
        fx new(x: int, y: int) -> Self {
            Self {
                x,
                y,
            }
        }

        fx area(self) -> int {
            self.x * self.y
        }
    }
    ```

- [ ] **Pattern matching** [WIP]

* Simple pattern matching (`let` statement binding and destructuring in tuples, structs and tuple structs)
* Wildcards and rests can be used in patterns as well to ignore values/fields

    ```snow
    let (((a, _), _), d) = (((1, 2), 3), 4);
    let sum = a + d  // Expected: 5
    ```

    ```snow
    struct Point3D {
        x: int,
        y: int,
        z: int,
    }

    let p = Point3D { x: 5, y: 10, z: 15 };
    let pair = (p, 20);
    let (Point3D { x, .. }, val) = pair;
    x + val  // Expected: 25
    ```

    ```snow
    enum Shape {
        Circle(int),
        Rectangle(int, int),
        Triangle(int, int, int),
    }

    let s = Shape::Circle(9);
    let Shape::Circle(radius) = s;
    radius * 2  // Expected: 18
    ```

* More complex pattern matching defined using `match` keyword
    * Exhaustiveness checks

* Other pattern matching through `if let`, `while let`
