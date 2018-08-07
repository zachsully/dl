[![Build Status](https://travis-ci.org/zachsully/dl.svg?branch=master)](https://travis-ci.org/zachsully/dl)

# A Prototype Compiler for λcop

`dl` is a compiler for λcop capable of generating code for Haskell, Ocaml, and
Racket.

## Example Program

Here is a program that constructs the stream of Fibonacci numbers and then gets
the fourth element.

```
codata Stream a
  { Head : Stream a -> a
  , Tail : Stream a -> Stream a }

let zipwith = (fix f in { Head [# o a b] -> o (Head a) (Head b)
                        , Tail [# o a b] -> f o (Tail a) (Tail b) })
in let fib = (fix x in
                { Head # -> 1
    	        , Head [Tail #] -> 1
                , Tail [Tail #] -> zipwith ({# p q -> p + q}) x (Tail x) })
   in Head (Tail (Tail (Tail (Tail fib))))
```

## Running and Compiling

* Repl
```
dl repl
```

* Interpreter
```
dl eval <file-in>
```

* Haskell
```
dl compile call-by-name <file-in> <file-out>
```

* Ocaml
```
dl compile call-by-value <file-in> <file-out>
```

* Racket
```
dl compile call-by-value --untyped <file-in> <file-out>
```
