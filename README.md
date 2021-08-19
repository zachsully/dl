[![Build Status](https://travis-ci.com/zachsully/dl.svg?branch=master)](https://travis-ci.com/zachsully/dl)

# A Prototype Compiler for λcop

λcop is a language with recursive (co)data types and nested (co)pattern matching
presented in
[Sullivan '18](https://www.cs.uoregon.edu/Reports/MS-201806-Sullivan.pdf). `dl`
is a compiler for λcop capable of generating code for Haskell, Ocaml, and
Racket.

## An Example Program

`dl` programs are a series of data and codata declarations followed by a term to
evaluate. To observe the final output, that term must be an integer or some data
type. Here is a program that constructs the stream of Fibonacci numbers and then
gets the fourth element:

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
dl compile <compiler-backend> <file-in> <file-out>
```

For the compiler backends, the evaluation strategy of the entire program is
decided by which backed. For example, the `haskell` backend will be call-by-need
and the `ml` backend will be call-by-value.

## Evaluation

Another way to run `dl` programs is to evaluate them with the abstract machine.

```
dl eval <cbn or cbv> <file-in>
```

Here the debug flag `-D` will force the interpreter to show the entire trace of
execution.
