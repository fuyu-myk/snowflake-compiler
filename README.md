# Snowflake-Compiler
This project documents my journey in learning Rust and subsequently coding a compiler. I referenced Julian Hartl's video series on YouTube for the creation of this project.

## Compiler architecture
Thus far, the current compiler architecture is highlighted below:

`input code` -> [Lexical Analyser] -> [Syntax Analyser] -> [Semantic Analyser]

* At this juncture, only the front end code of the compiler is being worked on, as I implement more types and keyword statements

## Roadmap

[x] Lexer [completed 04.06.2025]
* Takes in an input and transforms it to a token stream

[x] Parser [completed 05.06.2025]
* Takes in input data (text; Tokens) and builds the Abstract Syntax Tree (AST)
* Gives structural representation of the input while also checking for appropriate syntax

[x] Basic arithmetic support [completed 05.06.2025]
* Ability to apply BODMAS to evaluate the below statement:
```
6 - (23 + 8) * 10 / 3
```

[x] Bitwise operations support [completed 08.06.2025]
* Ability to apply bitwise operations to evaluate the below statement:
```
-1 + 2 * 3 - 4 / 5 | 6 + ~6 ^ 7 ** 2
```

[x] Error reporting [WIP]
* Highlights errors in red
* Error messages are printed in a specific format
* Updated as more functionality is added

[x] `let` statements [completed 06.06.2025]
* Variable lexing, parsing & error checking
* Ability to parse and evaluate the below statement:
    ```
    let a = 2 + 6
    let b = 23
    let c = a + b
    ```

[x] Scoping functionality [completed 09.06.2025]
* Variables defined in the scope only exists throughout the lifetime of the scope
* Ability to parse and evaluate the below statement:
    ```
    let a = 2301
    {
        let a = 806
    }
    ```

[x] `if` statements [completed 09.06.2025]
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

[x] `while` loops [completed 09.06.2025]
* Ability to parse and evaluate the below statement:
    ```
    let a = 0
    while a < 10 [
        a = a + 1
    ]
    ```