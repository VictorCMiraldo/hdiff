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

# Why Structural Differencing?

## Motivation

\columnsbegin \column{.28\textwidth}
```
Plato    , B5, 5
Aristotle, B7, 12
Focault  , C1, 7
```

\pause

\column{.28\textwidth}
```
Plato    , B5, 5
Aristotle, B8, 12
Focault  , C1, 7
```

\pause

\column{.28\textwidth}
```
Plato    , B5, 5
Aristotle, B7, 13
Focault  , C1, 7
```
\columnsend


## Contributions

. . .

* Efficient Algorithm for structured diffing (and merging)
    + Think of `UNIX` diff, over AST's.

. . .

* Wrote it in Haskell, generically

. . .

* Tested against dataset from GitHub
    + mined Lua repositories

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
data EOp        = Ins String | Del | Cpy

type EditScript = [EOp]
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

\vspace{1em}
\pause

Computes changes by enumeration.
```haskell
diff :: [String] -> [String] -> Patch
diff x y = head $ sortBy mostCopies $ enumerate_all x y 
```


## The `UNIX` diff: Abstractly

. . .

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

. . .

`UNIX` diff works for `[String]`{.haskell}. 


## The `UNIX` diff Generalized: Edit Scripts

. . .

Modify edit scripts

```haskell
data EOp = Ins TreeConstructor | Del | Cpy
```

. . .

\vfill

\columnsbegin
\column{.25\textwidth}

\begin{forest}
[, rootchange [Bin [T] [U]] [T] ]
\end{forest}

\column{.58\textwidth}
 
. . .

src tree preorder: `[Bin , T , U]`{.haskell}

dst tree preorder: `[T]`{.haskell}

. . .


```haskell
diff [Bin , T , U] [T] = [Del , Cpy , Del]
```
\columnsend

\vfill


## Edit Scripts: The Problem of Ambuiguity

. . .

Which subtree to copy?

\begin{center}
\begin{forest}
[, rootchange [Bin [T] [U]] [Bin [U] [T]] ]
\end{forest}
\end{center}

\vfill

. . .

\columnsbegin

\column{.48\textwidth}
Copy `U` : `[Cpy , Del , Cpy , Ins T]`{.haskell}

. . .

\column{.48\textwidth}
Copy `T` : `[Cpy , Ins U , Cpy , Del]`{.haskell}

\columnsend \pause

* Choice is __arbitrary__! \pause
* Edit Script with the most copies is not unique! \pause

Counting copies is reminescent of logest common subsequence.

## Edit Scripts: The Problem

Choice is necessary: only `Ins`{.haskell}, `Del`{.haskell} and `Cpy`{.haskell} 

. . .

Drawbacks:

1. Cannot explore all copy oportunities: must chose one per subtree

. . .

2. Choice points makes algorithms slow

. . .

_Generalizations generalize specifications!_

. . .

\alert{Solution:} Detach from _edit-scripts_

\begin{center}
\begin{forest}
[, rootchange [Bin [0, metavar] [1, metavar]] 
              [Bin [1, metavar] [0, metavar]] ]
\end{forest}
\end{center}

# New Structure for Changes

## Changes

\columnsbegin
\column{.42\textwidth}
\vspace{1.5em}
```haskell
diff (Bin (Bin t u) t) (Tri t u x) =
```
\column{.4\textwidth}
\begin{forest}
[,rootchange
  [BinC [BinC [0 , metavar] [1 , metavar]] [0 , metavar]] 
  [TriC [0, metavar] [1 , metavar] [x , triang]] ]
\end{forest}

\columnsend

. . .

\vfill

* Arbitrary duplications, contractions, permutations
    + Can explore all copy opportunities

. . .

* Faster to compute 
    + Our `diff x y`{.haskell} runs in $\mathcal{O}(\textrm{size x}+\textrm{size y})$

## Changes

Two _contexts_
 : * deletion: matching 
 * insertion: instantiation

```haskell
type Change = (TreeC MetaVar , TreeC MetaVar)

data Tree = Leaf
          | Bin Tree Tree
          | Tri Tree Tree Tree
```

Contexts are datatypes annotated with holes.

. . .

```haskell
data TreeC h = LeafC
             | BinC TreeC TreeC
             | TriC TreeC TreeC TreeC
             | Hole h
```

## Applying Changes

\begin{center}
\begin{forest}
[, rootchange
  [BinC [0, metavar] [BinC [1 , metavar] [t , triang]]]
  [BinC [0, metavar] [1 , metavar]]
]
\end{forest}
\end{center}

. . .

Call it `c`, \pause application function sketch:

```haskell
apply c = \x -> case x of
   Bin a (Bin b c) -> if c == t then Just (Bin a b) else Nothing
   _               -> Nothing
```

## Computing Changes 

. . .

Can _copy as much as possible_

. . .

Computation of `diff x y` divided:

. . .

Hard
 : Identify the common subtrees in `x` and `y`

Easy
 : Extract the context around the common subtrees

. . .

Consequence of definition of `Change`{.haskell}

. . .

Postpone the _hard_ part for now

* Oracle: `wcs :: Tree -> Tree -> (Tree -> Maybe MetaVar)`{.haskell}
    + stands for _which common subtree_

## Computing Changes: The Easy Part

Extracting the context:

```haskell
extract :: (Tree -> Maybe MetaVar) -> Tree -> TreeC
extract f x = maybe (extract' x) Hole $ f x
  where
    extract' (Bin a b) = BinC (extract f a) (extract f b)
    ... 
```

. . .


Finally, with `wcs s d` as an _oracle_ 

```haskell
diff :: Tree -> Tree -> Change MetaVar
diff s d = let o = wcs s d
            in (extract o s , extract o d)
```

. . .

if `wcs s d` is efficient, then so is `diff s d`

## Computing Changes: Defining the Oracle

. . .

Defining an _inefficient_ `wcs s d` is easy:

```haskell
wcs :: Tree -> Tree -> Tree -> Maybe MetaVar
wcs s d x = elemIndex x (subtrees s `intersect` subtrees d)
```

. . .

\vfill

Efficient `wcs` akin to *hash-consing*:

* annotates `Tree` with hashes
* store those in a `Trie` (amortized const. time search)
* topmost hash for equality

. . .

Runs in amortized $\mathcal{O}(1)$

\vfill

# Experiments

## Computing Changes: But how fast?

Diffed files from $\approx\!1200$ commits from top Lua repos

. . .

\columnsbegin

\column{.48\textwidth}
\centerbegin
![](plots/runtimes-less-than-10000.pdf)
\centerend

. . .

\column{.48\textwidth}
\centerbegin
![](plots/runtimes-all.pdf)
\centerend

\columnsend

## Merging Changes

Merging is our main motivation

. . .

```haskell
merge :: Change -> Change -> Either Conflict Change
merge p q = if p `disjoint` q then p else Conflict
```
\begin{displaymath}
\xymatrix{ & o \ar[dl]_{p} \ar[dr]^{q} & \\
          a \ar[dr]_{\texttt{merge q p}} & & b \ar[dl]^{\texttt{merge p q}} \\
            & c &}
\end{displaymath}

. . .

11% of mined merge commits could be _merged_

## Summary

New representation enables:

* Clear division of tasks ( `wcs` oracle + context extraction) \pause
* Express more changes than edit scripts \pause
* Faster algorithm altogether

. . .

We have learned:

1. Generalizations generalize specs \pause
2. More expressiveness does not mean higher complexity \pause
3. There is no free lunch

. . .

New representaion comes short:

* Hard to reason about
* Detaching from existing metatheory = more work to do 
* Can't copy bits *inside* a tree.

