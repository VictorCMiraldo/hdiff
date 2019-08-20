---
author: 
 - Victor Cacciari Miraldo
 - Wouter Swierstra
title: Efficient Structural Differencing
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
Flour , B5, 5
Sugar , B7, 12
...
```

\pause

\column{.28\textwidth}
```
Flour , B5, 5
Sugar , F0, 12
...
```

\pause

\column{.28\textwidth}
```
Flour , B5, 5
Sugar , B7, 42
...
```
\columnsend

\vfill

. . .

Same line changes in two different ways

. . .

Not same *column*

. . .

Here, merging requires knowledge about structure

\vfill

## Contributions

. . .

* Representation for changes

. . .

* Efficient Algorithm for structured diffing (and merging)
    + Think of `UNIX` diff, over algebraic datatypes.

. . .

* Wrote it in Haskell, generically

. . .

* Evaluated against dataset from GitHub
    + mined Lua repositories

# Line-by-Line Differencing

## The `UNIX` diff

  Compares files line-by-line, outputs an _edit script_.

\columnsbegin
\column{.48\textwidth}
```
function tap.packet(pinfo,tvb,ip)
  local src = tostring(ip.ip_src)
  local dmp = "some/file.log" 
```
\column{.48\textwidth}
```
function tap.packet(pinfo,tvb,ip)
  local src = tostring(ip.ip_src)
  local dmp = "some/other/file.log" 
```
\columnsend

. . .

\vfill
\rule{.8\textwidth}{.1mm}

`UNIX` diff outputs:

```
@@ -3,1 , +3,1 @@
-   local dmp = "some/file.log"
+   local dmp = "some/other/file.log" 
```

## The `UNIX` diff: In a Nutshell

Encodes changes as an _Edit Script_
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
-   local dmp = "some/file.log"
+   local dmp = "some/other/file.log" 
```
\column{.48\textwidth}
```haskell
[Cpy , Cpy , Del , Ins "local dmp ..."]
```
\columnsend

\vspace{1em}
\pause

Computes changes by enumeration.
```haskell
diff :: [String] -> [String] -> Patch
diff s d = head $ sortBy mostCopies $ enumerate_all s d
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
apply (diff s d) s == Just d
```

. . .

`UNIX` diff works for `[String]`{.haskell}. 


## The `UNIX` diff Generalized: Edit Scripts

. . .

Modify Edit Scripts

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

Counting copies is reminiscent of longest common subsequence.

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
    + Our `diff s d`{.haskell} runs in $\mathcal{O}(\textrm{size s}+\textrm{size d})$

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

Contexts are datatypes augmented with holes.

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

Application function sketch:

```haskell
\x -> case x of
   Bin a (Bin b c) -> if c == t then Just (Bin a b) else Nothing
   _               -> Nothing
```

## Computing Changes 

. . .

Can _copy as much as possible_

. . .

Computation of `diff s d` can be split:

. . .

Hard
 : Identify the common subtrees in `s` and `d`

Easy
 : Extract the context around the common subtrees

. . .

Consequence of definition of `Change`{.haskell}

. . .

Spec of the _hard_ part:

```haskell
wcs :: Tree -> Tree -> (Tree -> Maybe MetaVar)
wcs s d = flip elemIndex (subtrees s `intersect` subtrees d)
```

. . .

Efficient `wcs` is akin to *hash-consing*. Runs in $\mathcal{O}(1)$.

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

Since `wcs s d` is efficient, so is `diff s d`

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

. . .

```haskell
merge :: Change -> Change -> Either Conflict Change
merge p q = if p `disjoint` q then p else Conflict
```

. . .

\begin{displaymath}
\xymatrix{ & s \ar[dl]_{p} \ar[dr]^{q} & \\
          d_1 \ar[dr]_{q} & & d_2 \ar[dl]^{p} \\
            & r &}
\end{displaymath}

. . .

11% of all mined merge commits could be _automatically merged_


## Open Questions

* How to reason over new change repr? \pause
* Where do we stand with metatheory? \pause
* Can't copy bits inside a tree. Is this a problem? \pause
* ...


## Summary

* Clear division of tasks ( `wcs` oracle + context extraction) \pause
* Express more changes than edit scripts \pause
* Faster algorithm than ES based tree-diff

. . .

* Overall:
    + Fast and generic algorithm
    + Encouraging empirical evidence
