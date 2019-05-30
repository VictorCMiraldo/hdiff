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

# Intro

## Contributions

. . .

* Efficient Algorithm for structured diffing (and merging)
  - Think of `UNIX` diff, but for AST's.

. . .

* Wrote it in Haskell, generically

. . .

* Tested against dataset from GitHub
  - mined Lua repositories

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

## The `UNIX` diff Generalized: Edit Scripts

. . .

Modify edit scripts

```haskell
data ES = Ins Tree | Del | Cpy
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

Not ideal

## Edit Scripts: The Problem


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

\columnsend


* Choice is __arbitrary__! \pause
* Counting Copies:
  - List case: corresponds to _longest common subseq._
  - Tree case: Not so simple, most copies can be bad.
    
\begin{center}
\pause
\begin{forest} [, rootchange [Bin [A] [A]] [Bin [A] [A]]] 
\end{forest}
\end{center}



## Edit Scripts: The Problem

Choice is necessary: only `Ins`{.haskell}, `Del`{.haskell} and `Cpy`{.haskell} 

. . .

Drawbacks:

1. Cannot explore all copy oportunities: must chose one per subtree

. . .

2. Choice points makes algorithms slow

. . .

\alert{Solution:} don't chose, copy both trees!

\begin{center}
\begin{forest}
[, rootchange [Bin [0, metavar] [1, metavar]] 
              [Bin [1, metavar] [0, metavar]] ]
\end{forest}
\end{center}

# New Structure for Changes

## Changes

\columnsbegin
\column{.54\textwidth}
```haskell
diff (Node2 (Node2 t u) t) (Node3 t u x) =
```
\column{.4\textwidth}

\begin{forest}
[,rootchange
  [Node2C [Node2C [0 , metavar] [1 , metavar]] [0 , metavar]] 
  [Node3C [0, metavar] [1 , metavar] [x , triang]] ]
\end{forest}

\columnsend

. . .

\vfill

* Arbitrary duplications, contractions, permutations
  - Can explore all copy opportunities

. . .

* Faster to compute 
  - Our `diff x y`{.haskell} runs in $\mathcal{O}(\textrm{size x}+\textrm{size y})$

## Changes

Two _contexts_
 : * deletion: matching 
 * insertion: instantiation


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

. . .

```haskell
data Tree23C h = LeafC
               | Node2C Tree23C Tree23C
               | Node3C Tree23C Tree23C Tree23C
               | Hole h
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

Consequence of definition of `Change23`{.haskell}

. . .

Postpone the _hard_ part for now

* Oracle: `wcs :: Tree23 -> Tree23 -> (Tree23 -> Maybe MetaVar)`{.haskell}

## Computing Changes: The Easy Part

Extracting the context:

```haskell
extract :: (Tree23 -> Maybe MetaVar) -> Tree23 -> Tree23C
extract f x = maybe (extract' x) Hole $ f x
  where
    extract' (Node2 a b) = Node2C (extract f a) (extract f b)
    ... 
```

. . .


Finally, with `wcs s d` as an _oracle_ \pause (reads: _which common subtree_)

```haskell
diff :: Tree23 -> Tree23 -> Change23 MetaVar
diff s d = (extract (wcs s d) s , extract (wcs s d) d)
```

. . .

`diff s d` is efficient __iff__ `wcs s d` is efficient

## Computing Changes: Defining the Oracle

. . .

Defining an _inefficient_ `wcs s d` is easy:

```haskell
wcs :: Tree23 -> Tree23 -> Tree23 -> Maybe MetaVar
wcs s d x = elemIndex x (subtrees s `intersect` subtrees d)
```

. . .

\vfill

Efficient `wcs`:

* annotates `Tree23` with cryptographic hashes, akin to a _Merkle Tree_
* store those in a `Trie` (amortized const. time search)
* uses topmost hash to compare trees for equality.

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

Merging is a constant motivation for structured diffing

. . .

We defined a (very!) simple merging algorithm:

. . .

```haskell
merge :: Change23 -> Change23 -> Either Conflict Change23
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

# In Greater Depth

## In Depth: The Efficient Oracle

Recall,

```haskell
wcs :: Tree23 -> Tree23 -> Tree23 -> Maybe MetaVar
wcs s d x = elemIndex x (subtrees s `intersect` subtrees d)
```

. . .

Two inefficiency points:\pause

* Comparing trees for equality\pause
* Searching for a subtree in all enumerated subtrees

## In Depth: The Efficient Oracle (Inefficiency #1)

\centerbegin
![](merkle-tree.pdf)
\centerend

## In Depth: The Efficient Oracle (Merkle Trees)
. . .

Annotate Trees with `Digest`{.haskll}s:

```haskell
decorate :: Tree23 -> Tree23H
data Tree23H = LeafH
             | Node2H (Tree23H, Digest) (Tree23H, Digest)
             | Node3H (Tree23H, Digest) (Tree23H, Digest) (Tree23H, Digest)
```

. . .


```haskell
root :: Tree23H -> Digest
root LeafH                      = hash "leaf"
root (Node2H (_ , dx) (_ , dy)) = hash ("node2" ++ dx ++ dy)
...
```

. . .

Compare roots:

```haskell 
instance Eq Tree23H where
  t == u = root t == root u
```


## In Depth: The Efficient Oracle (Inefficiency #2)

. . .

Good structure to lookup hashes: __Tries__!

. . .

```haskell
wcs :: Tree23H -> Tree23H -> (Tree23H -> Maybe MetaVar)
wcs s d = lookup (tr empty s `intersect` tr empty d) . root
```

. . .

```haskell
tr :: Trie -> Tree23H -> Trie
tr db t = insert (root t) 
        $ case t of
            LeafH                  -> db
            Node2H (x , _) (y , _) -> tr (tr db x) y
            ...
```

## In Depth: The Efficient Oracle: The `diff` function

One could write:

```haskell
diff :: Tree23 -> Tree23 -> Change23
diff s d = let s' = decorate s; d' = decorate d
            in (extract (wcs s' d') s' , extract (wcs s' d') d')
```

. . .

Subtle issue: `a = Node2 (Node2 t k) u`{.haskell}; `b = Node2 (Node2 t k) t`{.haskell}

. . .

\columnsbegin
\column{.30\textwidth}
Wrong
\begin{center}
\begin{forest}
[, rootchange
  [Node2 [0 , metavar] [t , triang]]
  [Node2 [0 , metavar] [1 , metavar]]
]
\end{forest} \pause
\end{center}

\column{.30\textwidth}
Easy option:
\begin{center}
\begin{forest}
[, rootchange
  [Node2 [0 , metavar] [u , triang]]
  [Node2 [0 , metavar] [t , triang]]
]
\end{forest} \pause
\end{center}

\column{.36\textwidth}
Hard option:
\begin{center}
\vspace{-1.6em}
\begin{forest}
[, rootchange
  [Node2 [Node2 [0 , metavar] [1 , metavar]] [u , triang]  ]
  [Node2 [Node2 [0 , metavar] [1 , metavar]] [0 , metavar] ]
]
\end{forest}
\end{center}

\columnsend

## In Depth: Merging

Hard to reason with `Change23`{.haskell} \pause

* Redundant Info
* Metavariable Scope

. . .

un-_distribute_ the redundant constructors.


```haskell
type Patch23 = Tree23C Change23
```

. . .

\vfill

\columnsbegin
\column{.48\textwidth}
\begin{forest}
[,rootchange
  [Node2C [Node2C [0 , metavar] [1 , metavar]]
          [t , triang] ]
  [Node2C [Node2C [1 , metavar] [0 , metavar]]
          [t , triang] ]
]
\end{forest} \pause

\column{.48\textwidth}
\begin{forest}
[Node2C [, change 
           [Node2C [0 , metavar] [1 , metavar]]
           [Node2C [1 , metavar] [0 , metavar]] ]
        [t , triang] ]
\end{forest}
\columnsend

## In Depth: Merging and Anti-unification

. . .

Extract the _greatest common prefix_ from two `Tree23C`{.haskell}:

```haskell
gcp :: Tree23C a -> Tree23C b -> Tree23C (Tree23C a , Tree23C b)
gcp LeafC LeafC                   = LeafC
gcp (Node2C x y) (Node2C u v)     = Node2C (gcp x u) (gcp y v)
gcp (Node3C x y z) (Node3C u v w) = Node3C (gcp x u) (gcp y v) (gcp z w)
```

. . .

Problematic. Can break scoping:


\columnsbegin
\column{.25\textwidth}
\begin{forest}
[,rootchange
 [Node2C [t , triang]  [0 , metavar]]
 [Node2C [0 , metavar] [0 , metavar]]
]
\end{forest} \pause
\column{.13\textwidth}
\vspace{1em}
\begin{tikzpicture}
  \node (A) at (-0.8 , -0.2) {};
  \node (B) at (0.8  , -0.2) {};
  \node at (0 , 0) {\texttt{gcp}};
  \draw [arrows=->] (A) -> (B);
\end{tikzpicture}

\column{.38\textwidth}
\begin{forest}
[Node2C [, change [t , triang]  [0 , metavar]]
        [, change [0 , metavar] [0 , metavar]] ]
\end{forest}
\columnsend

## In Depth: Merging and Anti-unification



## Merging Changes

\begin{forest}
[Node2C 
  [ Node2C [, change [Node2C [0 , metavar] [0 , metavar]] [0 , metavar] ] [x, triang] ]
  [ t , triang ]
]
\end{forest}

## Technical Details

We can make


Consider:

```haskell
ics :: Tree23 -> Tree23 -> Tree23 -> Maybe MetaVar
ics s d x = elemIndex x (subtrees s `intersect` subtrees y)
```

. . .
