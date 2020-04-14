# `hdiff`: Hash-based Diffing for AST's 

This README provides some general info on the library.
For detailed information on the algorithm, check our 
[ICFP Paper](https://victorcmiraldo.github.io/data/icfp2019.pdf). 
If you want even more details, please check my
[PhD thesis](https://victorcmiraldo.github.io/data/MiraldoPhD.pdf)

The `hdiff` tool computes provides your usual differencing functions:

```haskell
diff  :: a -> a -> Patch a

apply :: Patch a -> a -> Maybe a
```

The difference with respect to the other tree differencing tools out there
is that `HDiff.Patch a` is a pattern-expression based patch. A picture is
worth 1024 words: Take the following files:

```
   O.while                 A.while

a := n;                | a := 1;
while n > 0 do {       | while n > 0 do {
  n := n - 1;          |   a := a * n;
  a := a * n;          |   n := n - 1;
}                      | }
res := n;              | res := n;
```

Running `hdiff examples/While/Factorial/{O,A}.while` to compute
their differences will the following patch:

```
[0] := n;       -|+  [0] := 1;
while [1] do {  -|+  while [1] do {
  [2];          -|+    [3];
  [3];          -|+    [2];
}               -|+  }
[4];            -|+  [4];
```

Everything to the left of `-|+` is called the pattern, or deletion context. Everything
to the right ot `-|+` is called the expression, or insertion context.
The square brackets denote *metavariables*, which is how `hdiff` copies information
over. If we overlay the deletion context above over `O.while`, we will get
an assignment of variables that we can use in the insertion context to produce `A.while`.

In reality, the output is a bit more complicated since it includes information
about where each individual change happened. In this case, there are five changes:

1. Copy of identifier `a`
2. Change `n` into `1`
3. Copy condition of while loop
4. Permute statements inside while loop
5. Copy rest of the prorgam

The actual output is more like the following:

```
{-# [Cpy #0] #-} := {-# {- n -}{+ 1 +} #-}
while {-# [Cpy #1] #-} do {
  {-# [Prm #2 <=> #3]
      [Prm #3 <=> #2]  #-}
}
{-# [Cpy #4] #-}
```

Everything inside a `{-# ... #-}` is a change that happens in
its own individual scope. Some changes are copies, some changes involve
permutations and some changes delete match on something and insert something else.

But in reality, you will see the following ugly output because
we have not implemented pretty-printing yet.

```
(Seq
 (:
  (Assign {-# [Cpy #7 ] #-} {-# {{- (Var "n") -} {+ (IntConst 1) +}} #-})
  (:
   (While
    {-# [Cpy #4 ] #-}
    (Seq {-# (: [Prm #2 <=> #3 ] (: [Prm #3 <=> #2 ] [])) #-}))
   {-# [Cpy #6 ] #-})))
```

Just like line-based diff, `hdiff` can be configured in many ways. Please,
refer to `hdiff --help` for all the modes and options.

To see the result of a merge run with `--verbose` or `-v`; to see the patch
produced by a merge run with `--debug`.
