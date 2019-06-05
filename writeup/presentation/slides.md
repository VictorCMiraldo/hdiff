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

. . .

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

\columnsend \pause


* Choice is __arbitrary__! \pause
* Counting Copies:
    + List case: corresponds to _longest common subseq._ \pause
    + Tree case: Not so simple, most copies can be bad.
    
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

_Generalizations can break specifications!_

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

. . .


```haskell
data Tree = Leaf
          | Bin Tree Tree
          | Tri Tree Tree Tree
```

Context are datatypes annotated with holes.

. . .

```haskell
data TreeC h = LeafC
             | BinC TreeC TreeC
             | TriC TreeC TreeC TreeC
             | Hole h

type Change = (TreeC MetaVar , TreeC MetaVar)
```

## Relation to Edit Scripts

`Change`{.haskell} represents families of `ES`{.haskell}:

. . .

\vspace{-2em}

\begin{center}
\[ \texttt{\color{forest-digems-constr} Change} \approx \texttt{\color{forest-digems-constr} Tree} \rightarrow \texttt{\color{forest-digems-constr}Maybe}\; \texttt{[{\color{forest-digems-constr}ES}]} \]
\end{center}

. . .

\columnsbegin
\column{.25\textwidth}
\begin{forest}
[, rootchange
  [Bin [A] [0 , metavar]]
  [Tri [A] [0 , metavar] [0, metavar]]]
\end{forest}

\column{.001\textwidth}
\vspace{2em}=
\column{.03\textwidth}
\begin{forest}
[Bin [A] [B]]
\end{forest}

\column{.001\textwidth}
\vspace{2em}$\mapsto$

\vspace{5.6em}\bgroup \color{white} $\mapsto$ \egroup
\column{.5\textwidth}
\vspace{-0.8em}
```haskell
Just [ 
  [Del, Ins Tri, Cpy, Ins B, Cpy],
  [Del, Ins Tri, Cpy, Cpy, Ins B],
 ...]
```

\columnsend

\vfill

## Relation to Edit Scripts

`Change`{.haskell} represents families of `ES`{.haskell}:

\vspace{-2em}

\begin{center}
\[ \texttt{\color{forest-digems-constr} Change} \approx \texttt{\color{forest-digems-constr} Tree} \rightarrow \texttt{\color{forest-digems-constr}Maybe}\; \texttt{[{\color{forest-digems-constr}ES}]} \]
\end{center}

\columnsbegin
\column{.25\textwidth}
\begin{forest}
[, rootchange
  [Bin [A] [0 , metavar]]
  [Tri [A] [0 , metavar] [0, metavar]]]
\end{forest}

\column{.001\textwidth}
\vspace{2em}=
\column{.03\textwidth}
\begin{forest}
[Bin [A] [x,triang]]
\end{forest}
\vspace{3em}
_

\column{.001\textwidth}
\vspace{2em}$\mapsto$

\vspace{5em}$\mapsto$
\column{.5\textwidth}
\vspace{-0.8em}
```haskell
Just [ 
  [Del, Ins Tri, Cpy, Ins x, Cpy],
  [Del, Ins Tri, Cpy, Cpy, Ins x],
 ...]

Nothing
```

\columnsend

\vfill


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
                  Bin a (Bin b c) -> if c == t then Just (Bin a b)
                                                   else Nothing
                  _                   -> Nothing
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
diff s d = (extract (wcs s d) s , extract (wcs s d) d)
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

Efficient `wcs`:

* annotates `Tree` with cryptographic hashes, akin to a _Merkle Tree_
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

1. Generalizations can break specs \pause
2. More expressiveness does not mean higher complexity \pause
3. Thinking extensionally is very helpful

# In Greater Depth

## In Depth: The Efficient Oracle

Recall,

```haskell
wcs :: Tree -> Tree -> Tree -> Maybe MetaVar
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
decorate :: Tree -> TreeH
data TreeH = LeafH
             | BinH (TreeH, Digest) (TreeH, Digest)
             | TriH (TreeH, Digest) (TreeH, Digest) (TreeH, Digest)
```

. . .


```haskell
root :: TreeH -> Digest
root LeafH                      = hash "leaf"
root (BinH (_ , dx) (_ , dy)) = hash ("node2" ++ dx ++ dy)
...
```

. . .

Compare roots:

```haskell 
instance Eq TreeH where
  t == u = root t == root u
```


## In Depth: The Efficient Oracle (Inefficiency #2)

. . .

Good structure to lookup hashes: __Tries__!

. . .

```haskell
wcs :: TreeH -> TreeH -> (TreeH -> Maybe MetaVar)
wcs s d = lookup (tr empty s `intersect` tr empty d) . root
```

. . .

```haskell
tr :: Trie -> TreeH -> Trie
tr db t = insert (root t) 
        $ case t of
            LeafH                  -> db
            BinH (x , _) (y , _) -> tr (tr db x) y
            ...
```

## In Depth: The Efficient Oracle: The `diff` function

One could write:

```haskell
diff :: Tree -> Tree -> Change
diff s d = let s' = decorate s; d' = decorate d
            in (extract (wcs s' d') s' , extract (wcs s' d') d')
```

. . .

Subtle issue: `a = Bin (Bin t k) u`{.haskell}; `b = Bin (Bin t k) t`{.haskell}

. . .

\columnsbegin
\column{.30\textwidth}
Wrong
\begin{center}
\begin{forest}
[, rootchange
  [Bin [0 , metavar] [u , triang]]
  [Bin [0 , metavar] [1 , metavar]]
]
\end{forest} \pause
\end{center}

\column{.30\textwidth}
Easy option:
\begin{center}
\begin{forest}
[, rootchange
  [Bin [0 , metavar] [u , triang]]
  [Bin [0 , metavar] [t , triang]]
]
\end{forest} \pause
\end{center}

\column{.36\textwidth}
Hard option:
\begin{center}
\vspace{-1.6em}
\begin{forest}
[, rootchange
  [Bin [Bin [0 , metavar] [1 , metavar]] [u , triang]  ]
  [Bin [Bin [0 , metavar] [1 , metavar]] [0 , metavar] ]
]
\end{forest}
\end{center}

\columnsend

## In Depth: Merging

Hard to reason with `Change`{.haskell} \pause

* Redundant Info
* Metavariable Scope

. . .

un-_distribute_ the redundant constructors.


```haskell
type Patch = TreeC Change
```

. . .

\vfill

\columnsbegin
\column{.48\textwidth}
\begin{forest}
[,rootchange
  [BinC [BinC [0 , metavar] [1 , metavar]]
          [t , triang] ]
  [BinC [BinC [1 , metavar] [0 , metavar]]
          [t , triang] ]
]
\end{forest} \pause

\column{.48\textwidth}
\begin{forest}
[BinC [, change 
           [BinC [0 , metavar] [1 , metavar]]
           [BinC [1 , metavar] [0 , metavar]] ]
        [t , triang] ]
\end{forest}
\columnsend

## In Depth: Merging and Anti-unification

. . .

Extract the _greatest common prefix_ from two `TreeC`{.haskell}:

```haskell
gcp :: TreeC a -> TreeC b -> TreeC (TreeC a , TreeC b)
gcp LeafC        LeafC        = LeafC
gcp (BinC x y)   (BinC u v)   = BinC (gcp x u) (gcp y v)
gcp (TriC x y z) (TriC u v w) = TriC (gcp x u) (gcp y v) (gcp z w)
```

. . .

Problematic. Can break scoping. \pause


\columnsbegin
\column{.25\textwidth}
\begin{forest}
[,rootchange
 [BinC [t , triang]  [0 , metavar]]
 [BinC [0 , metavar] [0 , metavar]]
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
[BinC [, change [t , triang]  [0 , metavar]]
        [, change [0 , metavar] [0 , metavar]] ]
\end{forest}
\columnsend
\pause

Define `closure :: Patch -> Patch` to fix scopes.

# Discussion

## Discussion

Performance of structural diffing: \pause Fixed \pause

Now what?

* Metatheory \pause
* Sharing Control \pause
* Merge Strategies \pause
* Domain-specific conflict resolution\pause
* Bigger univeses \pause
