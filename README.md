# `hdiff`: Hash-based Diffing for AST's 

This README provides some general info on the library.
For detailed information on the algorithm, check our [ICFP Paper](https://victorcmiraldo.github.io/data/icfp2019.pdf).

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

Running `hdiff -d nonest examples/While/Factorial/{O,A}.while` to compute
their differences will yield something that resembles the following:

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

The actual output is a little uglier since we have not implemented
pretty printing AST's yet. It looks like the following:

```
(Seq              -|+ (Seq
 (:               -|+  (:
  (Assign         -|+   (Assign
   [K| 11 |]      -|+    [K| 11 |]
   (Var           -|+    (IntConst
    n))           -|+     1))
  (:              -|+   (:
   (While         -|+    (While
    [I| 2 |]      -|+     [I| 2 |]
    (Seq          -|+     (Seq
     (:           -|+      (:
      [I| 9 |]    -|+       [I| 10 |]
      (:          -|+       (:
       [I| 10 |]  -|+        [I| 9 |]
       []))))     -|+        []))))
   [I| 3 |])))    -|+    [I| 3 |])))
```

Just like line-based diff, `hdiff` can be configured in many ways. One that deserves
an honorable mention is the differencing mode. In the example above, we
run it in *no-nested-shares* mode, indicated by the `-d nonest` flag.

## Differencing Modes

TODO
