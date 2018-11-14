[![Build Status](https://travis-ci.org/zachsully/dl.svg?branch=master)](https://travis-ci.org/zachsully/dl)

# A Prototype Compiler for λcop

λcop is a language with recursive (co)data types and nested (co)pattern matching
presented in
[Sullivan '18](https://www.cs.uoregon.edu/Reports/MS-201806-Sullivan.pdf). `dl`
is a compiler for λcop capable of generating code for Haskell, Ocaml, and
Racket.

## Example Program

Here is a program that constructs the stream of Fibonacci numbers and then gets
the fourth element.

```
codata Stream a
  { Head : Stream a -> a
  , Tail : Stream a -> Stream a }

let zipwith = (fix f in { Head [# o a b] -> o (Head a) (Head b)
                        , Tail [# o a b] -> f o (Tail a) (Tail b) }) in
let fib = (fix x in
             { Head # -> 1
    	     , Head [Tail #] -> 1
             , Tail [Tail #] -> zipwith {# p q -> p + q} x (Tail x) })
in Head (Tail (Tail (Tail (Tail fib))))
```

## Compiling

`dl` features several compilers that are invoked with the following command.

```
dl compile <compiler-num> <file-in> <file-out>
```

| Backend | compiler-num |
|---------|--------------|
| Haskell | 0 |
| Ocaml   | 1 |
| Racket  | 2 |
| JavaScript | 3 |
