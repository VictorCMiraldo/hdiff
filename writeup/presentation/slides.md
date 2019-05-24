---
author: 
 - Victor Cacciari Miraldo
 - Wouter Swierstra
title: Efficient Structural Differencing
subtitle: ... and the lessons learned from it
institute: Utrecht University
theme: metropolis
mainfont: Open Sans
mainfontoptions: Scale=0.8
sansfont: Open Sans
sansfontoptions: Scale=0.8
monofont: Ubuntu Mono
monofontoptions: Scale=0.8
---

# Line-by-Line Differencing

## The `UNIX` diff

  Compares files line-by-line, outputs an _edit script_.

\columnsbegin
\column{.48\textwidth}
```
type checker: "You fool!
What you request makes no sense,
rethink your bad code."
```
\column{.48\textwidth}
```
type checker: "You fool!
What you request makes no sense,
it's some ugly code."
```
\columnsend

. . .

\vfill
\rule{.8\textwidth}{.1mm}

`UNIX` diff outputs:

```
@@ -3,1 , +3,1 @@
- rethink your bad code."
+ it's some ugly code."
```


## The `UNIX` diff: In a Nutshell

Encodes changes as an _edit script_
```haskell
data ES    = Ins String | Del | Cpy
type Patch = [ES]
```

. . .

Computes changes by enumeration.
```haskell
diff :: [String] -> [String] -> Patch
diff x y = head $ sortBy mostCopies $ enumerate_all x y 
```

. . .

Example,

\columnsbegin
\column{.30\textwidth}
```
@@ -3,1 , +3,1 @@
- rethink your bad code."
+ it's some ugly code."
```
\column{.48\textwidth}
```haskell
[Cpy , Cpy , Del , Ins "it's some ..."]
```
\columnsend


## The `UNIX` diff: Abstractly

`UNIX` diff works for `[String]`{.haskell}. 

Abstractly, `diff` computes differences between two objects:

```haskell
diff  :: a -> a -> Patch a
```

. . .

as a _transformation_ that can be applied,

```haskell
apply :: Patch a -> a -> Maybe a
```

. . .

such that,

```haskell
apply (diff x y) x == Just y
```

## The `UNIX` diff Generalized: Edit Scripts

Modify edit scripts

```haskell
data ES = Ins Tree | Del | Cpy
```

. . .

\vfill

\columnsbegin
\column{.25\textwidth}
```{=latex}
\begin{forest}
[, rootchange [Bin [T] [U]] [T] ]
\end{forest}
```
\column{.58\textwidth}
 
. . .

Source tree preorder: `[Bin , T , U]`{.haskell}

Destination tree preorder: `[T]`{.haskell}

. . .


```haskell
diff [Bin , T , U] [T] = [Del , Cpy , Del]
```
\columnsend

\vfill


## Edit Scripts: The Problem

Which subtree to copy?

```{=latex}
\begin{center}
\begin{forest}
[, rootchange [Bin [T] [U]] [Bin [U] [T]] ]
\end{forest}
\end{center}
```

\vfill

. . .

Copy `T`? `[Cpy , Del , Cpy , Ins T]`{.haskell}

. . .

Copy `U`? `[Cpy , Ins U , Cpy , Del]`{.haskell}

. . .

Choice is __arbitrary__!

## Edit Scripts: The Problem

Choice is necessary: only `Ins`{.haskell}, `Del`{.haskell} and `Cpy`{.haskell} 

. . .

Drawbacks:

1. Cannot explore all copy oportunities: must chose one per subtree

. . .

2. Choice points makes algorithms slow

. . .

Why not copy both?

```{=latex}
\begin{center}
\begin{forest}
[, rootchange [Bin [0, metavar] [1, metavar]] 
              [Bin [1, metavar] [0, metavar]] ]
\end{forest}
\end{center}
```

# New Structure for Changes

## Changes

\columnsbegin
\column{.54\textwidth}
```haskell
diff (Node2 (Node2 t u) t) (Node3 t u x) =
```
\column{.4\textwidth}
```{=latex}
\begin{forest}
[,rootchange
  [Node2C [Node2C [0 , metavar] [1 , metavar]] [0 , metavar]] 
  [Node3C [0, metavar] [1 , metavar] [x , triang]] ]
\end{forest}
```
\columnsend

. . .

\vfill

* Arbitrary duplications, contractions, permutations
  - Can explore all copy opportunities

. . .

* Faster to compute 
  - Our `diff x y`{.haskell} runs in $\mathcal{O}(\textrm{size x}+\textrm{size y})$

## Changes

* Two _contexts_:
 - deletion context matches variables
 - insertion context instantiates variables


```haskell 
type Change23 = (Tree23C MetaVar , Tree23C MetaVar)
```

. . .


```haskell
data Tree23 = Leaf
            | Node2 Tree23 Tree23
            | Node3 Tree23 Tree23 Tree23
```

Context are datatypes annotated with holes.


```haskell
data T23C h = LeafC
            | Node2C Tree23C Tree23C
            | Node3C Tree23C Tree23C Tree23C
            | Hole h
```

## Computing Changes 

Idea: copy as many subtrees as possible

. . .

Computation proceeds in two parts

. . .

Hard
 : Identify the common subtrees in `x` and `y`

Easy
 : Extract the context around the copies

. . .

Consequence of definition of `Change23`{.haskell}

## Computing Changes: The Easy Part

Consider:

```haskell
ics :: Tree23 -> Tree23 -> Tree23 -> Maybe MetaVar
ics s d x = elemIndex x (subtrees s `intersect` subtrees y)
```

. . .

Then write:

```haskell
extract :: (Tree23 -> Maybe MetaVar) -> Tree23 -> Tree23C
extract f x = maybe (extract' x) Hole $ f x
  where
    extract' (Node2 a b) = Node2C (extract f a) (extract f b)
    ... 
```

. . .

Finally, `diff s d = (extract (ics s d) s , extract (ics s d) d)`{.haskell}

