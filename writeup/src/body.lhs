\section{Introduction}
\label{sec:introduction}

% Bug because of double lines?
% https://blog.codecentric.de/en/2014/02/curly-braces/

\victor{hype the use of FP. Why do we use it here?}

  Software Version Control Systems are an essential tool in the 
belt of today's software engineer. At their core is a
differencing algorithm that computes patches between two versions of a file, 
the most well-known being the UNIX \texttt{diff}~\cite{McIlroy1976}.
It is a line-based tool, ie, look at changes
on the level of the \emph{lines} of a file, hence, it fails
to identify more fine grained changes in software source code. 

  Let us take a step back and introduce the differencing problem
abstractly. The well-typed differencing problem for some type |a|
consists in finding a type constructor, call it |Patch a|, together with
functions |diff| and |apply|. Naturally, the |diff| function computes
the differences between two trees of type |a| whereas |apply| will
attempt to transform one tree according to a |Patch|. The
\emph{well-typed} refers to the fact that a |Patch| is guaranteed, by
construction, to generate well-typed elements once its applied. This
is not the case for the approaches~\cite{Asenov2017,Falleri2014} using
\texttt{xml} or \texttt{json} to represent their abstract syntax
trees, where the result of an arbitrary patch could be an ill formed tree.

\begin{myhs}
\begin{code}
diff   :: a -> a -> Patch a
apply  :: Patch a -> a -> Maybe a 
\end{code}
\end{myhs}

  Not every such triple |(Patch , diff , apply)| solves
the differencing problem. We expect certain properties on these
components for them to be of any practical use. 

  The first property one expects from this pair of functions
is correctness, stating that |apply| faithfully reproduces |y|
from |x| and |diff x y|.

\[
| forall x y dot apply (diff x y) x == Just y |
\]

  Yet, there is a collection of other properties that might
be desirable. For instance, we require that |diff|
is both space and time efficient. That is, it must be fast to compute
a |Patch| and the size of the patch must be smaller than storing both elements
of type |a|. Otherwise, one could argue that |Patch a = (a,a)| is a perfectly
fine solution, for example. Yet, storing all revisions of every file under
version control is not really an acceptable solution.

  Another interesting property we want to have is the ability to apply
a patch to biggest amount of elements possible. In fact, we want to
apply a patch to as much elements other than |x| as possible. One way
of saying this is that |diff| will be the identity when there are no changes.
Note that this is \emph{a different property} than correctness:

\[ | forall x y dot apply (diff x x) y == Just y | \]

  This captures the idea that a patch that comes from not changing
anything must be applicable to any element performing exactly 
that action: not changing anything. 

  The UNIX \texttt{diff}~\cite{McIlroy1979} solves the differencing
problem, and satisfies many of these desirable properties, for the
special case of |a == [String]|, ie, files are seen as lists of
lines. Although there has been attempts at a solution~\cite{Loh2009,Miraldo2017} for arbitrary
such datatypes, all of them have the same \emph{modus operandis}: compute
all possible patches between two objects, then filter out \emph{the
best} such patch. There are two big problems with this approach: (A)
the inefficiency of a non-deterministic algorithm with many choice
points, and, (B) defining what is \emph{the best} patch. These two
problems stem from the same design choice: having only insert,
delete and copy as the base operations.

  We expect that the core of a differencing algorithm is to identify
and pursue the copy opportunities as much as possible. Therefore the
lack of a representation for moving and duplicating subtrees is an
inherent issue in a structured setting: upon finding a subtree that
can be copied in two different ways, the algorithm must choose between
one of them. Besides efficiency problems, this also brings a
complicated theoretical problems: it is impossible to order these
patches in an educated fashion, and hence one cannot single out \emph{the
best} possible patch. We illustrate this in \Cref{fig:linear-patch}. The tools
dealing with insertions, deletions and copies all work on the preorder
flattening of the tree as shown in the right side of
\Cref{fig:linear-patch}. Hence, if we want to transform |Bin t u| into
|Bin u t| using these tools, we will have to choose between copying
|t| or |u|, but never both. One could choose to copy the bigger tree,
but what if they have the same size? The choice becomes arbitrary.

\begin{figure}
\includegraphics[scale=0.3]{src/img/patch-00.pdf}
\caption{Visualization of a |diff (Bin t u) (Bin u t)| using insertions, deletions and copies only}
\label{fig:linear-patch}
\end{figure}

  The lesson here that no option is better than the other. 
If, however, we have some operation
that encodes permutation of subtrees, we have not only removed a
choice point from the algorithm but also constructed a patch that
pursues all copy opportunities without having to resort to heuristics or such
arbitrary choices. And, contrary to what one might expect, more is
less in this scenario: adding more expressive basic change
operations, duplicate and permute, enables us to remove choice
points and write a efficient deterministic structure-aware differencing 
algorithm. 

  The contributions presented in this paper are listed as:

\begin{itemize}
  \item A generic solution to the well-typed differencing problem
        that does not suffer from problems (A) and (B) outline above.
        In fact, our approach supports subtree duplication and permutations
        and satisfy the desired properties outlined above, including
        space efficiency.
  \item An idealized algorithm capable of computing a patch that
        transforms a source tree into a target tree. We also give a practical
        instantiation of this algorithm that is correct modulo cryptographic hash
        collisions and runs in linear time, offering competitive performance
        with widely used tools such as the UNIX \texttt{diff}.
  \item An implementation of our algorithm that exploits generic programming
        techniques making it readily applicable to a large universe of datatypes,
        namely, any mutually recursive family.
  \item We define a \emph{merging} algorithm capable of merging trivially disjoint
        patches and evaluate our prototype over data mined from GitHub repositories.
\end{itemize}

\section{Tree Diffing: A Concrete Example}
\label{sec:concrete-changes}

  Before exploring the generic implementation of our algorithm, let us
look at a simple, concrete instance, first. This sets the stage and
introduces the intuition behind the building blocks used throughout
the generic implementation
(\Cref{sec:representing-changes}). Throughout this section we will
explore the central ideas from our algorithm instantiated for a
specific type, namely, two-three-trees, defined below.

\begin{myhs}
\begin{code}
data Tree23  = Leaf
             | Node2 Tree23 Tree23
             | Node3 Tree23 Tree23 Tree23
\end{code}
\end{myhs}

  The central concept of our work is the encoding of a
\emph{change}.  Unlike the previous
work~\cite{Loh2009,Miraldo2017,Klein1998} based on
tree-edit-distance~\cite{Bille2005} which uses only insertions,
deletions and copies and consider the preorder traversal
of a tree, as shown in \Cref{fig:linear-patch}, we go a step
further. We explicitly model duplications and contractions of subtrees
within our notion of \emph{change}. 

  The representation of a \emph{change} between two values of type
|Tree23| is given by identifying the bits and pieces that must be
copied from source to destination.

  A new datatype, |Tree23C|, enables us to annotate a value of
|Tree23| with holes that represent metavariables
within a |Tree23|. These metavariables correspond to arbitrary trees
that are \emph{common subtrees} of both the source and destination of the change.
These are exactly the bits that are being copied from source to destination.
We refer to a value of |Tree23C| as a \emph{context}. 
For now, the metavariables will be a simple |Int|
but later we shall see how this construction is generalized.

\begin{myhs}
\begin{code}
type MetaVar = Int

data Tree23C = LeafC
             | Node2C Tree23C Tree23C
             | Node3C Tree23C Tree23C Tree23C
             | Hole MetaVar
\end{code}
\end{myhs}

  A \emph{change}, then, is defined by a pattern that
binds some metavariables, called the deletion context, and an expression
where we are supposed to instantiate its metavariables, called the insertion
context:

\begin{myhs}
\begin{code}
type Change = (Tree23C , Tree23C)
\end{code}
\end{myhs}

\begin{figure}
\includegraphics[scale=0.3]{src/img/patch-01.pdf}
\caption{Visualization of a |diff (Node2 t u) (Node2 u t)|, metavariables are shown in red}
\label{fig:first-patch}
\end{figure}

  The change that transforms |Node2 t u| in |Node2 u t| is then
represented by a pair of |Tree23C|, |(Node2C (Hole 0) (Hole 1) ,
Node2C (Hole 1) (Hole 0))|, as seen in \Cref{fig:first-patch}.
This change works on any tree built using the |Node2| constructor
and swaps the children of the root.

\subsubsection{Applying Changes}

  Applying a change, therefore, is done by instantiating the
metavariables against the deletion context and the insertion context:

\begin{myhs}
\begin{code}
applyChange :: Change -> Tree23 -> Maybe Tree23
applyChange (d , i) x = del d x >>= ins i
\end{code}
\end{myhs}

Naturally, if the term |x| and
the deletion context |d| are \emph{incompatible}, this operation will
fail, as we can see in the definition of |del|, below.
Contrary to regular pattern-matching, however, we allow variables to
appear more than once on both the deletion and insertion
contexts. Their semantics are dual: duplicate variables in the
deletion context must match equal trees whereas when in the insertion
context will duplicate trees. We use an auxiliary function within the
definition of |del| to make this check easier to perform.

\begin{myhs}
\begin{code}
del :: Tree23C -> Tree23 -> Maybe (Map MetaVar Tree23)
del ctx tree = go ctx tree empty 
  where
    go :: Tree23C -> Tree23 -> Map MetaVar Tree23 -> Maybe (Map MetaVar Tree23)
    go LeafC           Leaf           m = return m
    go (Node2C x y)    (Node2 a b)    m = go x a m >>= go y b
    go (Node3C x y z)  (Node3 a b c)  m = go x a m >>= go y b >>= go z c
    go (Hole i)        t              m = case lookup i m of
                                            Nothing  -> return (M.insert i t m)
                                            Just t'  -> guard (t == t') 
                                                     >> return m
    go _               _              m = Nothing
\end{code}
\end{myhs}

  The |go| function above is mostly entirely structural. Only when
we reach a |Hole| is that we check whether we have already instantiated
this metavariable. If that is the case we must make sure that the values agree.
Otherwise we simply instantiate the metavariable with the corresponding tree.

  Once we have obtained a valuation from a deletion context and 
a tree, we substitute the variables in the insertion context
with their respective values obtaining the resulting tree.
This phase can also fail if the change contains unbound variables.

\begin{myhs}
\begin{code}
ins :: Tree23C -> Map MetaVar Tree23 -> Maybe Tree23
ins LeafC           m  = return Leaf
ins (Node2C x y)    m  = Node2 <$$> ins x m <*> ins y m
ins (Node3C x y z)  m  = Node3 <$$> ins x m <*> ins y m <*> ins z m
ins (Hole i)        m  = lookup i m
\end{code}
\end{myhs}

\subsubsection{Computing Patches}

  Next, we explore how to produce a change from a source and a
destination, defining our idealized |diff| function. This function
will exploit as many
copy opportunities as possible. For now, we delegate the
decision of whether a subtree should be copied or not to an
oracle. Assume we have access to an oracle, ie, a function |ics|, \emph{``is common
subtree''}, with type |Tree23 -> Tree23 -> Tree23 -> Maybe Int|, where
|ics s d x| returns |Nothing| when |x| is not a subtree of |s| and |d|
or |Just i| when |x| is a common subtree. The |Int| inside the |Just|
tells us which metavariable to use. The only condition we impose is
injectivity of |ics s d| on the |Just| subset of the image. That is, if
|ics s d x == ics s d y == Just j|, then |x == y|. That is, the same subtree
is assigned the same metavariable. 
  
  Assuming the existence of this oracle is commonplace.  There is an
obvious inefficient implementation for |ics|. Later on, in
\Cref{sec:oracle}, we provide a more subtle, efficient, generic
implementation for |ics|.
  
  Abstracting away the oracle allows for a simple separation of tasks.
The |diff| function merely has to compute the deletion and insertion
contexts using said oracle.  This is done by the means of an |extract|
function that receives an oracle and a tree and extracts a context from its
second argument.

\begin{myhs}
\begin{code}
diffTree23 :: Tree23 -> Tree23 -> Change
diffTree23 s d = (extract (ics s d) s , extract (ics s d) d)
\end{code}
\end{myhs}

  The |extract| function traverses its argument tree, looking for
sharing opportunities.  Recall that the oracle answers whether a tree
is a subtree of both |s| and |d|. If that is the case, we want our
change to \emph{copy} such subtree. That is, we return a |Hole|
whenever the second argument of |extract| is a common subtree
according to the given oracle.  If the oracle returns |Nothing|, we
peel the topmost constructor to the context and recurse into the
children.

\begin{myhs}
\begin{code}
extract :: (Tree23 -> Maybe Int) -> Tree23 -> Tree23C
extract o x = maybe (peel x) Hole (o x)
  where
    peel Leaf           = LeafC
    peel (Node2 a b)    = Node2C (extract o a) (extract o b)
    peel (Node3 a b c)  = Node3C (extract o a) (extract o b) (extract o c)
\end{code}
\end{myhs}

  Assuming that |ics s d| is \emph{the best} possible such function,
that is, it correctly issues metavariables to \emph{all} common
subtrees of |s| and |d|, it is not hard to see that our implementation 
satisfies the properties enumerated in \Cref{sec:introduction}, namely:

\begin{description}
  \item[Correctness] Assuming |ics| is correct, 
    \[ |forall x y dot apply (diff x y) x == Just y| \]
  \item[Preciseness] Assuming |ics| is correct,
    \[ |forall x y dot apply (diff x x) y == Just y| \]
  \item[Time Efficiency] 
    On the worst case, we perform one query to the oracle per
    constructor in our trees. Assuming |ics| to be a constant time
    function, our algorithm is linear on the number of constructors
    in the source and destination trees. We will provide such |ics|
    in \Cref{sec:oracle}.
  \item[Space Efficiency] 
    The size of a |(Tree23C , Tree23C)| is, on average, smaller than 
    storing its source and destination tree completely. On the worst case,
    where there is no common subtree, they have the same size.
\end{description}

\paragraph{Summary} In this section we provided a simple algorithm to
solve the differencing problem for 2-3-trees. We began by creating the
type of contexts over |Tree23|, which consisted in annotating a
|Tree23| with a \emph{metavariable} constructor. Later, assuming the
existence of an oracle that answers whether an arbitrary tree is a
subtree of the source and the destination we described how to
construct a value of type |Tree23C| from a |Tree23|. This operation,
when applied to the source and destination trees will produce a
\emph{change} that captures the transformation between them. Those
steps are the core principles behind the algorithm: maximizing sharing
using the oracle.

  Naturally, this simplified version of our algorithm has some
shortcomings that will be addressed in the remainder of this paper.

%% For one, we are not trying to
%% minimize the changes after we |extract| a context from the source or
%% destination trees. This makes merging significantly harder.  Another
%% problem is that we are not addressing what happens when there
%% exists a subtree that appears in at least two different places with
%% one occurrence being under a larger subtree. This can break the apply
%% function and needs to be identified and handled. Moreover, this example algorithm
%% shares subtrees too eagerly. For instance, every occurrence of |Leaf|
%% will be shared under the same metavariable. This restriction does not
%% impact the correctness of the algorithm but is an important point on
%% the design space: how to \emph{drive} this algorithm, \Cref{sec:sharing}.

\section{Tree Diffing Generically}
\label{sec:generic-diff}

\subsection{Background on Generic Programming}
\label{sec:generic-prog}

  Now that we have an idea of how our algorithm works for a specific
type, let us briefly review the
\texttt{generics-mrsop}~\cite{Miraldo2018} library, that we will use to give
a generic version of our algorithm.
This library follows the \emph{sums-of-products}
school of generic programming~\cite{deVries2014} and, additionally, enables 
us to work with mutually recursive families. This is important
as the abstract syntax trees of most programming languages are mutually recursive.

  For example, take the |Tree23| type from
\Cref{sec:concrete-changes}.  Its structure can be seen in a
\emph{sum-of-products} fashion through the |CodesTree23| type given
below.  The |CodesTree23| type represents the shape in which every
|Tree23| will come and consists in two nested lists of
\emph{atoms}. The outer list represents the choice of constructor, and
packages the \emph{sum} part of the datatype whereas the inner list
represents the \emph{product} of the fields of a given
constructor. The |I 0| flags a recursive position.  The numeric
argument supplied to |I| indicates the index of the recursive type
within the family. For |Tree23| we only have one recursive type.

\begin{myhs}
\begin{code}
type CodesTree23 = P  ([  P [] 
                      ,   P ([ I 0 , I 0 ]) 
                      ,   P ([ I 0 , I 0 , I 0 ]) ])
\end{code}
\end{myhs}

 The \texttt{generics-mrsop} goes one step further and uses |Atom|s
to distinguish whether a field is a recursive position referencing the
$n$-th type in the family, |I n|, or a opaque type, for example, |Int|
or |Bool|, which are represented by |K KInt|, |K KBool|.

\begin{myhs}
\begin{code}
type family Code (a :: Star) :: P ([ (P [Atom]) ])
\end{code}
\end{myhs}

  Let us look at a slightly more involved example than |CodesTree23|. 
The mutually recursive family containing types |Zig| and |Zag| has
its codes defined as a list of codes, one for each member of the family:

\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data Zig  = Zig Int   | ZigZag Zag
data Zag  = Zag Bool  | ZagZig Zig
\end{code}
\end{myhs}
\end{minipage} %
\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
type CodesZig = P  [ P [ P [ K KInt ]   , P [ I 1 ] ]
                   , P [ P [ K KBool ]  , P [ I 0 ] ]
                   ]
\end{code}
\end{myhs}
\end{minipage} %

Note that the codes come in the same order as the family. The code for |Zig| is
the first element of the |CodesZig| type level list. It consists in two lists, since
|Zig| has two constructors. One receives a value of type |Int|, the other consists in
a recursive call to the second element of the family. The code acts as a recipe that
the \emph{representation} functor must follow in order to interpret those into
a type of kind |Star|. 

  The representation is defined by the means of $n$-ary sums (|NS|)
and products (|NP|) that work by induction on the \emph{codes} and one
interpretation for atoms.

\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data NS :: (k -> Star) -> [k] -> Star where
  Here   :: f x      -> NS f (x PCons xs)
  There  :: NS f xs  -> NS f (x PCons xs)
\end{code}
\end{myhs}
\end{minipage} %
\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data NP :: (k -> Star) -> [k] -> Star where
  Nil   :: NP f (P [])
  Cons  :: f x -> NP f xs -> NP f (x PCons xs)
\end{code}
\end{myhs}
\end{minipage} %
\begin{myhs}
\begin{code}
data NA :: (Nat -> Star) -> Atom -> Star where
  NA_I :: phi i  -> NA phi (I i)
  NA_K :: Opq k  -> NA phi (K k)
\end{code}
\end{myhs}

  The |NS| type is responsible for determining the choice of
constructor whereas the |NP| applies a representation functor to all
the fields of the selected constructor.  Finally, |NA| distinguishes
between representation of a recursive position from an opaque
type. Although the \texttt{generics-mrsop} provides a way to customize
the set of opaque types used, this is not central do the developments
in this paper and hence we will assume a type |Opq| that interprets
the necessary atom types, ie, |Int|, |Bool|, etc. We refer the
interested reader to the original paper~\cite{Miraldo2018} for more
information. Nevertheless, we define the representation functor |Rep|
as the composition of the interpretations of the different pieces:

\begin{myhs}
\begin{code}
type Rep phi = NS (NP (NA phi))
\end{code}
\end{myhs}


  Naturally, |NS|, |NP| and |NA| come equipped with their elimination principles:

\begin{myhs}
\begin{code}
elimNS :: (forall at dot f at -> a) -> NS f s -> a
elimNS f (There s)  = elimNS f s
elimNS f (Here x)   = f x
\end{code}
\end{myhs}
\begin{myhs}
\begin{code}
elimNP :: (forall at dot f at -> a) -> NP f p -> [a]
elimNP f NP0        = []
elimNP f (x :* xs)  = f x : elimNP f xs
\end{code}
\end{myhs}
\begin{myhs}
\begin{code}
elimNA :: (forall ix dot f x -> a) -> (forall k dot g k -> a) -> NA f g at -> a
elimNA f g (NA_I x)  = f x
elimNA f g (NA_K x)  = g x
\end{code}
\end{myhs}

  Finally, we tie the recursive knot with a functor of kind |Nat -> Star| that we 
pass as a parameter to |NA| in order to interpret the recursive positions. The
familiar reader might recognize it as the indexed least fixedpoint:

\begin{myhs}
\begin{code}
newtype Fix (codes :: P [ P [ P [ Atom ] ] ]) (ix :: Nat)
  = Fix { unFix :: Rep (Fix codes) (Lkup codes ix) }
\end{code}
\end{myhs}

  Where |Lkup codes ix| denotes the type level lookup of the element
with index |ix| within the list |codes|. This type family throws a
type error if the index is out of bounds.  The generic versions of the
constructors of type |Zig| are given by:

\begin{myhs}
\begin{code}
gzig :: Int -> Fix CodesZig 0
gzig n = Fix (Here (Cons (NA_K (OpqInt n)) Nil))

gzigzag :: Fix CodesZig 1 -> Fix CodesZig 0
gzigzag zag = Fix (There (Here (Cons (NA_I zag) Nil)))
\end{code}
\end{myhs}

  One of the main benefits of the \emph{sums-of-products} approach to
generic programming is that it enables us to pattern match
generically. In fact, we can state that a value of a type consists
precisely in a choice of constructor and a product of its fields by
defining a \emph{view} type. Take the \emph{constructor} of a generic
type to be:

\begin{myhs}
\begin{code}
data Constr :: [[k]] -> Nat -> Star where
  CZ ::                 Constr (x PCons xs)  Z
  CS :: Constr xs c ->  Constr (x PCons xs)  (S c)
\end{code}
\end{myhs}

  And use |Constr sum c| as a predicate indicating that |c| is a valid
constructor for |sum|, ie, it is a valid index into the type level
list |sum|. Then define a |View| over a value of a sum type to be a
choice of constructor and corresponding product:

\begin{myhs}
\begin{code}
data View :: (Nat -> Star) -> P [ P [ Atom ] ] -> Star where
  Tag :: Constr sum c -> NP (NA phi) (Lkup c sum) -> View phi sum

sop :: Fix codes i -> View (Fix codes) (Lkup i codes)
\end{code}
\end{myhs}

  The |sop| functions converts a value in its standard representation
to the more useful choice of constructor and associated product.  This
brief introduction covers the basics of generic programming in Haskell
that we will use in this paper. We refer the interested reader to the
literature~\cite{deVries2014,Miraldo2018} for more information.

\subsection{Representing and Computing Changes, Generically}
\label{sec:representing-changes}

  
  In \Cref{sec:concrete-changes} we gained some intuition about the
workings of our algorithm whereas in \Cref{sec:generic-prog} we
discussed techniques for writing programs over arbitrary mutually
recursive families. The next step is to start writing our algorithm in
a generic fashion. 

  First we need to define a generic notion of context, analogously to
|Tree23C| (\Cref{sec:concrete-changes}) which augmented the
|Tree23| type with an extra constructor for representing holes.  This
type construction is crucial to the representation of patches. In
fact, this construction can be done for any mutually recursive family
and any representation of \emph{metavariable}, hence we parametrize by
a functor:

\begin{myhs}
\begin{code}
data Tx :: [[[Atom]]] -> (Atom -> Star) -> Atom -> Star where
  TxHole  :: phi at  -> Tx codes phi at
  TxOpq   :: Opq k   -> Tx codes phi (K k)
  TxPeel  :: Constr (Lkup i codes) c
          -> NP (Tx codes phi) (Tyof codes c)
          -> Tx codes phi (I i)
\end{code}
\end{myhs}

  We can read the type |Tx codes phi at| as the element of the
mutually recursive family |codes| indexed by |at| augmented with holes
of type |phi|.  The |Tx| type is, in fact, the indexed free monad over
the |Rep| functor.  Essentially, a value of type |Tx codes phi at| is
a value of type |NA (Fix codes) at| augmented with \emph{holes} of
type |phi|. To illustrate this, let us define the injection of a |NA|
into a |Tx|:

\begin{myhs}
\begin{code}
na2tx :: NA (Fix codes) at -> Tx codes phi at
na2tx (NA_K k)        = TxOpq k
na2tx (NA_I (Fix x))  = case sop x of
                          Tag c p -> TxPeel c (mapNP na2tx p) 
\end{code}
\end{myhs}

  The inverse operations is partial. We can translate
a |Tx| into an |NA| when the |Tx| has no \emph{holes}:

\begin{myhs}
\begin{code}
tx2na :: Tx codes phi at -> Maybe (NA (Fix codes) at)
tx2na (TxHole _)      = Nothing
tx2na (TxOpq k)       = NA_K k
tx2na (TxPeel c txs)  = inj c <$$> mapNPM tx2na txs
\end{code}
\end{myhs}

  Differently than with |Tree23C|, in |Tx| we parametrize the type of
\emph{metavariables}.  This comes in quite handy as it allows us to
use the |Tx| differently for a number of intermediate steps in the algorithm
and the representation. 

\paragraph{Representation of Changes}

  With a generic notion of contexts, we can go ahead and define our
|Change| type.  We need a pair of |Tx|, with the same semantics
as in \Cref{sec:concrete-changes}: one deletion context and one insertion context. 
This time, however, we define a new datatype to be able to partially
apply its type arguments later on.

\begin{myhs}
\begin{code}
data Change codes phi at = Change (Tx codes phi at) (Tx codes phi at)
\end{code}
\end{myhs}

  The interpretation for the metavariables, |MetaVarIK| will carry the
identifier for the variable itself but also identifies whether this
metavariable is supposed to be instantiated by a recursive member of
the family or a opaque type. We do so by carrying a value of type
|NA|, enabling the compiler to gain knowledge over |at| when
pattern-matching.  This is important since we must know the types of
the values supposed to be matched against a metavariable to ensure we
will produce well-typed trees.

\begin{myhs}
\begin{code}
data MetaVarIK at = MetaVarIK Int (NA (Const Unit) at)
\end{code}
\end{myhs}

  The type of changes over |Tree23| can now be written using the
generic representation for changes and metavariables. Since the type
|ChangeTree23|, defined below, is isomorphic to |(Tree23C , Tree23C)|
we will commit a slight abuse of notation and use their values
interchangeably. For example, we write |Node2C a b| for |TxPeel (CS
CZ) (Cons a (Cons b Nil))|.

\begin{myhs}
\begin{code}
type ChangeTree23 = Change Tree23Codes MetaVarIK (I Z)
\end{code}
\end{myhs}

\paragraph{Computing Changes} Next, we look at how can we compute a
|Change codes MetaVarIK| from a source and a destination elements of
type |Fix codes ix|.  We are still assuming an efficient
oracle |ics :: Oracle codes|, for answering whether \emph{|t| is a
subtree of a fixed |s| and |d| indexed by |n|}, where:

\begin{myhs}
\begin{code}
type Oracle codes = forall j dot Fix codes j -> Maybe Int
\end{code}
\end{myhs}

  Recall that the core of computing a change is in the extraction of
the deletion and insertion contexts. This was done by the |extract|
function in \Cref{sec:concrete-changes}. Unfortunately that function
has an important issue: it forgets the subtrees the oracle identified
as common subtrees. This is a problem when a tree is both a subtree of
the source and destination but occurs, additionally, as the subtree of
another common subtree.  In \Cref{fig:problematic-ics} we see the
subtree |t| as one such case. Since the oracle recognizes |Node2 t k|
and |t| as common subtrees, and |t| additionally occurs by itself one
of the extracted contexts will contain an undefined metavariable.
Hence our |txExtract| function will be a bit more involved. We will
annotate the locations marked by the oracle as potential copies
and later on evaluate whether we want to consider it a true copy
or not.

\begin{figure}
\begin{minipage}[t]{.4\textwidth}
\begin{myhs}
\begin{code}
a  = Node2 (Node2 t k) u
b  = Node2 (Node2 t k) t
\end{code}
\end{myhs}
\end{minipage}
\begin{minipage}[t]{.5\textwidth}
\begin{myhs}
\begin{code}
extract (ics a b) a  = Node2C (Hole 0) u
extract (ics a b) b  = Node2C (Hole 0) (Hole 1)
\end{code}
\end{myhs}
\end{minipage}
\caption{Example of erroneous context extraction due to nested common subtrees}
\label{fig:problematic-ics}
\end{figure}

  We will use the |ForceI| type to ensure that the index of the 
copied position is of the |I ix|
form, that is, we are only \emph{sharing} recursive positions so
far. We also use the indexed product type |(:*:)| to carry along information.

\begin{myhs}
\begin{code}
data (:*:) f g x = f x :*: g x

data ForceI :: (Nat -> Star) -> Atom -> Star where
  ForceI :: f i -> ForceI f (I i)
\end{code}
\end{myhs}

  Finally, we define our |txExtract| function to check whether a given
|x| is a subtree of the fixed source and destinations by calling the
provided oracle, if so, we return a hole with the subtree annotated If
|x| is not a common subtree we extract the topmost constructor and its
fields then map |TxOpq| on the opaque fields and continue extracting
the context on the fields that reference recursive positions.

\begin{myhs}
\begin{code}
txExtract  :: Oracle codes
           -> Fix codes ix 
           -> Tx codes (ForceI (Const Int :*: Fix codes)) (I ix)
txExtract ics x = case ics x of
    Just i   -> TxHole (ForceI (Const i :*: x))
    Nothing  ->  let Tag c p = sop (unFix x)
                 in TxPeel c (mapNP (elimNA TxOpq (extractAtom ics)) p)
\end{code}
\end{myhs}

  After extracting a context with potential copies we must decide
which subtrees are true copies and which other subtrees must be kept
as part of the context. We do so by postprocessing the result of
extracting both contexts from a source and a destination.  In case we
need to keep a given tree and forget that it was shared we convert it
to a context with |na2tx|.  We want to keep only the metavariables
that occur in both the insertion and deletion contexts to prevent any
\texttt{undefined variable} when applying our patches. In
\Cref{fig:problematic-ics}, metavariable |1| would trigger such error.

\begin{myhs}
\begin{code}
txPostprocess  ::  Tx codes (ForceI (Const Int :*: Fix codes)) (I ix)
               ->  Tx codes (ForceI (Const Int :*: Fix codes)) (I ix)
               ->  (  Tx codes (ForceI (Const Int)) (I ix)
                   ,  Tx codes (ForceI (Const Int)) (I ix))
\end{code}
\end{myhs}

  The definition is uninteresting and is omitted. The function
proceeds by grouping every metavariable in a set, computing the
intersection of the sets, then mapping over its arguments and
replacing the |Const Int :*: Fix codes| hole by either |Const Int|, if
the |Int| belongs in the set, or by translating the |Fix codes| with
|na2tx . NA_I|.

  At this point, given two trees |a, b| of type |Fix codes ix|, we
have extracted and post-processed both the deletion and insertion
contexts, of type |Tx codes (ForceI (Const Int)) (I ix)|. These are
just like a value of type |Fix codes ix| with holes in some
recursive positions only.  This is enforced by the |ForceI| type.

  Assume we have a function that builds an efficient oracle at hand,

\begin{myhs}
\begin{code}
buildOracle :: Fix codes i -> Fix codes i -> Oracle codes
\end{code}
\end{myhs}

  Assembling these pieces into the generic version of
the |diffTree23| function presented in \Cref{sec:concrete-changes} yields
the function |diff0|, defined below.

\begin{myhs}
\begin{code}
diff0 :: Fix codes ix -> Fix codes ix -> Change codes (ForceI (Const Int)) (I ix)
diff0 x y =  let  ics = buildOracle x y
                  del = txExtract ics x
                  ins = txExtract ics y
             in uncurry Change $$ txPostprocess del ins
\end{code}
\end{myhs}

  Note that unlike |diffTree23|, our |diff0| function will only produce
closed changes. That is, a deletion and a insertion context that have
the same set of variables. Intuitively, this means that every variable
that is declared is used and vice-versa. 

\subsection{Minimizing the Changes: Computing Patches}
\label{sec:representing-patches}

  Calling |diff0 x y| yields a potentialy large |Change| over trees that
transforms, in particular, |x| into |y|. Having \emph{one} single change
that transforms |x| into |y| is not ideal. A number of 
constructors are being deleted, then inserted back agin. Besides the
redundant information in the contexts, changes are hard to manipulate
and reason about. In order to make the fact that these constructors
are also \emph{copies}, we say that they are part of the \emph{spine}
of the patch, which contains the changes on its leaves.

\begin{myhs}
\begin{code}
type Patch codes at = Tx codes (Change codes MetaVarIK) at
\end{code}
\end{myhs}

\Cref{fog:example-patch} illustrates a value of type |Patch Tree23Codes (I Z)|,
the changes are shown with a
shade in the background, placed always in the leaves of the
spine. Note that the changes encompass only the minimum number of
constructor necessary to bind and use all metavariables. This keeps
changes small and isolated. On this section we will discuss how
to take the results of |diff0| and transform them into a |Patch|.

\begin{figure}
\includegraphics[scale=0.3]{src/img/patch-example.pdf}
\vspace{.4em}
\begin{myhs}
\begin{code}
Node3C  (Change (Hole 0) (Hole 0))
        (Change (Node2C (Hole 0) (Hole 1)) (Node2C (Hole 1) (Hole 0))
        (Node2C  (Change (na2tx w) (na2tx w'))
                 (Change (Hole 3)  (Hole 3)))
\end{code}
\end{myhs}
\caption{Graphical and textual representation of the patch that transforms the value %
|Node3 t (Node2 u v) (Node2 w x)| into the value |Node3 t (Node2 v u) (Node2 w' x)|.}
 \label{fig:patch-example}
\end{figure}

  The first step is to identify the \emph{spine}. That is, the
constructors that are present in both the deletion and insertion
contexts.  We are essentially splitting a big change into the
\emph{greatest common prefix} of the insertion and deletion contexts
and the smaller changes inside:

\begin{myhs}
\begin{code}
txGCP :: Tx codes phi at -> Tx codes psi at -> Tx codes (Tx codes phi :*: Tx codes psi) at
txGCP (TxHole x) b = TxHole (TxHole x :*: b)
txGCP a (TxHole y) = TxHole (a :*: TxHole y)
txGCP (TxOpq x) (TxOpq y) 
  | x == y     = TxOpq x
  | otherwise  = TxHole (TxOpq x :*: TxOpq y)
txGCP (TxPeel cx px) (TxPeel cy py)
  = case testEquality cx px of
      Nothing   -> TxHole (TxPeel cx px :*: TxPeel cy py)
      Jus Refl  -> TxPeel cx (mapNP (uncurry' txGCP) (zipNP px py))
\end{code}
\end{myhs}

  The |txGCP| can be seen as a generalized |zip| function that instead
of stopping whenever one of its arguments has been consumed, it stores
the rest of the other argument. It is \emph{greatest} in the sense
that it eagerly consumes as many constructors as possible and
places in the |TxHole|s just the different parts. 

%% We can write
%% this as the following property, with |Delta a = (a :*: a)|:
%% 
%% \[ |forall x dot txGCP x x == txMap (\h -> Delta . TxHole) x| \]

  It is worth mentioning that it is trivial to invert a spine back
to a change by the means of a distributive law:

\begin{myhs}
\begin{code}
txJoin :: Tx codes (Tx codes phi) at -> Tx codes phi at

distr :: Tx codes (Tx codes phi :*: Tx codes psi) at -> (Tx codes phi :*: Tx codes psi) at
distr spine = txJoin (txMap fst spine) :*: txJoin (txMap snd spine)
\end{code}
\end{myhs}

  We cannot simply take the result of |diff0| and get its
\emph{greatest common prefix}. The |txGCD| function is not aware
of metavariables and might break their scoping. 
This can happen when subtrees are being duplicated or transported
across different parts of the source and destination. One such
example is shown in \Cref{fig:patch-scoping-problem}. The \emph{greatest
common prefix} is too permissive and must be later refined.

\begin{figure}
\begin{minipage}[t]{.55\textwidth}
\begin{myhs}
\begin{code}
-- prob = diff0 (Node2 t t) (Node2 x t)
prob  :: Change Tree23Codes (Const Int) (I Z)
prob  =  Change  (Node2C (Hole 0)  (Hole 0))
                 (Node2C x         (Hole 0))
\end{code}
\end{myhs}
\end{minipage} %
\begin{minipage}[t]{.35\textwidth}
\[ |txGCP prob ==| \hspace{6em} \]
\includegraphics[scale=0.3]{src/img/patch-02.pdf}
\end{minipage}
\caption{How |txGCP| breaks binding. The triangle represents a |Tx| with no holes.}
\label{fig:patch-scoping-problem}
\end{figure}
  
  This refinement aims to fix the scoping problems introduced by |txGCP|.
For example, \Cref{fig:patch-scoping-problem}  has |TxHole 0| unbound in its
insertion context. That happens because |TxHole 0| was supposedly bound by
the left child from the root, but the |txGCP| function broke this
dependency. In this example, |txGCP prob| has what
one \emph{closed change} and one \emph{open change}. 
Closed changes are those where all instantiated variables are used
and vice-versa, ie, the set of variables in both the insertion
and deletion context is the same. The \emph{open changes},
on the other hand, are those that contain metavariables
that occur solely in the insertion or deletion context.
The process of translating a patch with open changes into
one with closed changes is called \emph{closure}.

  Before we explain the machinery necessary to identify and eliminate
the open changes inside a spine let us introduce some auxiliary definitions:

\begin{myhs}
\begin{code}
data Sum f g x = InL (f x) | InR (g x)

either' :: (f x -> r x) -> (g x -> r x) -> Sum f g x -> r x
either' a b (InL fx) = a fx
either' a b (InR gx) = b gx
\end{code}
\end{myhs}
 
  Which in turn allow us to define a predicate that returns whether
a change is closed or not by tagging it with |InR| or |InL|

\begin{myhs}
\begin{code}
isClosed :: Change codes at -> Sum (Change codes) (Change codes) at
isClosed (Change del ins)
  | variables ins == variables del  = InR (Change del ins)
  | otherwise                       = InL (Change del ins)
\end{code}
\end{myhs}

  The |Sum| comes in handy for it can be passed as an argument to
|Tx|, of kind |Atom -> Star|. This enables us to map our
predicate over a patch, as shown below:

%\begin{figure}
\begin{myhs}
\begin{code}
txMap isClosed (txGCP prob)  = Node2C  (InR (Change (TxHole 0)  (TxHole 0)))
                                       (InL (Change x           (TxHole 0)))
\end{code} 
\end{myhs}
%\caption{Patch with open and closed changes inside}
%\label{fig:closure-problem}
%\end{figure}

  We could \emph{close} all changes by pushing the |Node2C| from the
\emph{spine} to the changes, which is essentially what the
|closure| function does.  This can be visualized in
\Cref{fig:closure-patch-scoping-problem}. 

  The |closure| function receives a patch with identified open and
closed changes and tries to eliminate all the \emph{open changes},
tagged by |InL|. We do so by finding the smallest closed change that
binds the required variables. If we cannot find such change, we
translate the whole patch as an \emph{open change} altogether. The first
three cases are trivial:

\begin{figure}
\includegraphics[scale=0.3]{src/img/patch-03.pdf}
\caption{The closure of |txGCP prob|, shown in \Cref{fig:patch-scoping-problem}}
\label{fig:closure-patch-scoping-problem}
\end{figure}

\begin{myhs}
\begin{code}
closure'  :: Tx codes (Sum (Change codes) (Change codes)) at
          -> Sum (Change codes) (Tx codes (Change codes)) at
closure' (TxOpq x) = InR (TxOpq x)
closure' (TxHole (InL oc)) = InL oc
closure' (TxHole (InR cc)) = InR cc
\end{code}
\end{myhs}

  The interesting case of the |closure'| function is the |TxPeel|
pattern, where we first try to compute the closures for the fields of
the constructor and check whether all these fields contain only closed
changes. If that is the case, we are done. If some fields contain open
changes, however, the |mapNPM fromInR| fails with a |Nothing| and
we must massage some data. The |inss| and |dels| are the projections
of the insertion contexts and deletion contexts of \emph{all} changes
inside the fields of the product |px|, regardless of whether these are 
open or closed. We then assemble a new change by \emph{pushing} the |TxPeel cx|
and checking whether this suffices to bind all variables. That is,
if this closes the change. 

\begin{myhs}
\begin{code}
closure' (TxPeel cx px) 
  = let aux = mapNP closure' px
     in case mapNPM fromInR aux of
       Just np  -> InR (TxPeel cx np)
       Nothing  -> let  chgs = mapNP (either' InL (InR . distr)) aux
                        dels = mapNP (either' chgDel chgDel) chgs
                        inss = mapNP (either' chgIns chgIns) chgs
                        tmp  = Change (TxPeel cx dels) (TxPeel cx inss)
                    in if isClosed tmp
                       then InR (TxHole tmp)
                       else InL (Change tmp)
\end{code}
\end{myhs}

  We then wrap |closure'| within a larger function that always returns
a |Tx codes (Change codes) ix| with all changes being \emph{closed}.
The necessary observation is that if we pass a given |tx| to |closure'|
such that there is no undefined or unreferenced variable, |closure'|
will always return a |InR| value. In our case, the |txPostprocess|
guarantees that.

\begin{myhs}
\begin{code}
closure  :: Tx codes (Sum (Change codes) (Change codes)) at
         -> Tx codes (Change codes) at
closure  = either' (const $$ error "no closure exists") id
\end{code} %%
\end{myhs}

  The final |diff| function is assembled by getting the closure
of the greatest common prefix of the change the comes from |diff0|.  

\begin{myhs}
\begin{code}
diff :: Fix codes ix -> Fix codes ix -> Patch codes (I ix)
diff x y =  let  ics   = buildOracle x y
                 del0  = txExtract ics x
                 ins0  = txExtract ics y
                 (del1 , ins1) = txPostprocess del ins
            in  closure  $$  txRefine TxHole mkCpy 
                         $$  txMap isClosed (txGCP del1 ins1) 
\end{code}
\end{myhs}

  The |txRefine| step identifies the opaque
values that should be copied, further enlarging the domain of our patch.  
This is easy to identify since the |txGCP|
already put those opaque values in the \emph{spine} of the
patch. Hence, we simply need to traverse the patch and replace the
occurrences of |TxOpq| by a new \emph{copy} change. We use the
|txRefine| function, declared below.

\begin{myhs}
\begin{code}
txRefine  :: (forall at  dot f at   -> Tx codes g at) 
          -> (forall k   dot Opq k  -> Tx codes g (K k)) 
          -> Tx codes f at -> Tx codes g at
\end{code}
\end{myhs}

\victor{IM HERE}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%
%%%  A patch is characterized by a |Tx|, called the \emph{spine},
%%%which contains \emph{changes} in its leaves. The spine represents a prefix
%%%of constructors to be copied from source to destination. This is more
%%%convenient than having a single \emph{change} that transforms the source
%%%into the destination. Firstly because a good number of the constructors
%%%of our trees will be repeated on both the insertion and deletion
%%%contexts. Moreover, when trying to merge these changes together, it is
%%%simpler to have a number of small changes that can be independently
%%%classified and understood instead of a big, complex, change working
%%%on the whole tree.
%%%
%%%
%%%
%%%  In \Cref{fig:patch-example} we show an illustration of the value of
%%%type |Patch| we expect from calling our diff function with the
%%%below parameters:
%%%
%%%\begin{myhs}
%%%\begin{code}
%%%diff (Node3 t (Node 2 u v) (Node2 w x)) (Node3 t (Node2 v u) (Node2 w' x))
%%%\end{code}
%%%\end{myhs}
%%%
%%%  Note that in \Cref{fig:patch-example} we borrow notation from
%%%\Cref{sec:concrete-changes} for conciseness, but bear in mind that
%%%|Node2C a b|, for example, stands for |TxPeel (CS CZ) (Cons a (Cons b
%%%Nil))|. 
%%%\begin{myhs}
%%%\begin{code}
%%%apply :: Patch codes ix -> Fix codes ix -> Maybe (Fix codes ix)
%%%apply patch el = txZip patch (na2tx el)  >>=  txMapM (uncurry' applyChange') 
%%%                                         >>=  return . tx2na
%%%\end{code}
%%%\end{myhs}
%%%
%%%  Where |(:*:)| the indexed product, |uncurry'| the indexed
%%%variant of |uncurry| made to work over the indexed product 
%%%and |txZip| is the function that zips together two treefixes.
%%%Note that the function fails if the structure disagrees at any point,
%%%unlike |zip| for lists, for example.
%%%
%%%\begin{myhs}
%%%\begin{code}
%%%
%%%txZip :: Tx codes phi ix -> Tx codes psi ix -> Maybe (Tx codes (phi :*: psi) ix)
%%%\end{code}
%%%\end{myhs}
%%%
%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%
%%%
%%%
%%%On this section we present our generic algorithm
%%%and address the shortcomings discussed in \Cref{sec:concrete-changes}.
%%%We shall omit some type variables that are not relevant to our domain
%%%for clarity. The full code can be found in our
%%%repository\footnote{\hsdigemsgit}.
%%%
%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%
%%%
%%%
%%%Going from a source and a destination
%%%trees directly to a |Patch| is hard. As seen in
%%%\Cref{fig:patch-example}, one has to identify the copy opportunities
%%%and isolate the largest possible spine that still respects the
%%%independent bindings of the changes.  These will be done with the help
%%%a number of intermediate steps.  First we extract the insertion and
%%%deletion contexts by using the oracle, much like we did in
%%%\Cref{sec:concrete-changes}.  We must, however, post-process those
%%%contexts replacing undefined metavariables since the oracle might copy
%%%\emph{too eagerly}.  Next we extract the greatest common prefix,
%%%yielding the spine and fix any bindings that have been broken by a too
%%%large spine.  
%%%
%%%
%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%
%%%
%%%Coming back to the example
%%%in \Cref{fig:closure-problem}, we can \emph{close} all changes by pushing the
%%%|Node2C| from the \emph{spine} to the changes. 
%%%%% 
%%%%% \begin{myhs}
%%%%% \begin{code}
%%%%% closure (txMap isClosed (txGCP prob))  
%%%%%   ==  closure (Node2C  (InR (Change (TxHole 0)  (TxHole 0)))
%%%%%                        (InL (Change x           (TxHole 0))))
%%%%%   ==  Change  (Node2C (TxHole 0)  (TxHole 0))
%%%%%               (Node2C x           (TxHole 0))
%%%%% \end{code}         
%%%%% \end{myhs}
%%%This can be visualized in \Cref{fig:closure-patch-scoping-problem}.
%%%We finalize by assembling all of the pieces in our final |diff| function.


\paragraph{Applying Patches} Recall the definition of the
application function.

\begin{myhs}
\begin{code}
apply :: Patch codes ix -> Fix codes ix -> Maybe (Fix codes ix)
apply patch el  =    txZip patch (na2tx el) 
                >>=  txMapM (uncurry' applyChange') 
                >>=  return . tx2na
\end{code}
\end{myhs}

  Where |applyChange'| very closely the implementation
of the application presented in \Cref{sec:concrete-changes} but uses
some more advanced type level mechanisms. The most important detail is the
encoding of the interpretation of an atom with an existential index:

\begin{myhs}
\begin{code}
data NAE :: [[[Atom kon]]] -> * where
  SomeFix :: Fix codes ix -> NAE codes
  SomeOpq :: Opq k        -> NAE codes
\end{code}
\end{myhs}

  Which allows the application function to carry a |Map Int (NAE codes)|,
analogously to the |Map MetaVar Tree23| in \Cref{sec:concrete-changes}. When
looking a value in a |Map Int (NAE codes)| we must be able to cast
it to the correct type, extracted from a |MetaVarIK|.

\begin{myhs}
\begin{code}
naeCast  :: NAE ki codes
         -> MetaVarIK ki at
         -> Either String (NA ki (Fix ki codes) at)
\end{code}
\end{myhs}

  This definition is uninteresting and can be found in the code. With these
mechanisms in place the definition of the application function follows
closely that of the sketched version in \Cref{sec:concrete-changes}. 
Its type is:

\begin{myhs}
\begin{code}
apply  :: Patch codes ix -> Fix codes ix -> Maybe (Fix codes ix)
\end{code}
\end{myhs}

  Whenever a patch |p| can be applied to an element |x|, that is,
|apply p x| returns |Just y| for some |y|, we say that |p| is \emph{applicable}
to |x|.

\subsection{Defining the Oracle}
\label{sec:oracle}

  We have been assuming the existence of an \emph{oracle} to answer
whether a tree was a subtree of the source and destination of a patch.
We have seen that the efficiency with which we can answer this query is 
fundamental to the overall efficiency of our algorithm: we perform one such
query per constructor in the source and destination. It is time for us to
finally define this efficient lookup function. Yet, it is worthwhile
to define the inefficient, naive version, first. Besides providing
important intuition to what this function is doing it is an interesting
generic programming exercise in its own. 

  When deciding whether a given tree |x| is a subtree of both |s| and
|d|, for |s| and |d| fixed trees, a naive oracle would check every
single subtree of |s| and |d| for equality against |x|.  Upon finding
a match, it would return the index of such subtree in the list of all
subtrees. Lets try to write this very function. First, we enumerate
all possible subtrees. Since these subtrees might be indexed by
different |Atom|s, we need an existential type to put all of these in
the same list.

\begin{myhs}
\begin{code}
data Exists :: (Atom n -> Star) -> Star where
  Ex :: f at -> Exists f

subtrees :: Fix codes i -> [ Exists (Fix codes) ]
subtrees x = Ex x : case sop x of
  Tag _ pt -> concat (elimNP (elimNA (const []) subtrees) pt)
\end{code}
\end{myhs}

  Next, we define an equality over |Exist (Fix codes)| and search
through the list of all possible subtrees. The comparison function
starts by comparing the indexes of the |Fix codes| values wrapped
within |Ex|. If they agree, we pattern match on |Refl|, which
in turn allows us to compare the values for propositional equality.

\begin{myhs}
\begin{code}
idx :: (a -> Bool) -> [a] -> Maybe Int
idx f  []     = Nothing
idx f  (x:xs) = if f x then Just 0 else (1+) <$$> idx f xs

heqFix :: Exists (Fix codes) -> Exists (Fix codes) -> Bool
heqFix (Ex x) (Ex y) = case testEquality x y of
                         Nothing    -> False
                         Just Refl  -> eqFix x y
\end{code}
\end{myhs}

  Finally, we put it all together in |buildOracle|: start
by looking for our target, |t|, in the subtrees of |x|. Upon finding something,
we proceed to check whether |t| also belongs in the subtrees of |y|. Since
we are in the |Maybe| monad, if either of those steps fail, the entire function
will return  |Nothing|.
 
\begin{myhs}
\begin{code}
type Oracle codes = forall j dot Fix codes j -> Maybe Int

buildOracle :: Fix codes i -> Fix codes i -> Oracle codes
buildOracle x y t = do
  ix <- idx (heqFix t) (subtrees x)
  iy <- idx (heqFix t) (subtrees y)
  return ix
\end{code}
\end{myhs}

  There are two points of inefficiency this naive
|buildOracle|. First, we build the |subtrees| list twice, once for the
source and once for the destination. This is inherent to this
approach and cannot be surpassed. We then proceed to compare a
third tree, |t|, for equality with every subtree in the prepared
lists. This, on the other hand, can be made fast.

  In order to compare trees for equality in constant time we can
annotate them with cryptographic hashes~\cite{Menezes1997} and compare
these hashes instead. This technique transforms our trees into
\emph{merkle trees}~\cite{Merkle1988} and is more commonly seen in the
security and authentication context~\cite{Miller2014,Miraldo2018HAMM}.
Our generic programming machinery that is already at our disposal
enables us to create \emph{merkle trees} generically quite easily.
The \texttt{generics-mrsop} provide some attribute
grammar~\cite{Knuth1990} mechanisms, in particular synthetization of
attributes:

\begin{myhs}
\begin{code}
newtype AnnFix x codes i = AnnFix (x i , Rep (AnnFix x codes) (Lkup i codes))

prepare :: Fix codes i -> AnnFix (Const Digest) codes i
prepare = synthesize authAlgebra
\end{code}
\end{myhs}

\begin{figure}
\includegraphics[scale=0.3]{src/img/merkle-tree.pdf}
\caption{Example of a merkelized |Tree23|, where |n_2| is some fixed
identifier and |h| is a hash function.}
\label{fig:merkelized-tree}
\end{figure}


  Here, |AnnFix| is the cofree comonad, used to add a label to each
recursive branch of our generic trees. In our case, this label will be
the cryptographic hash of the concatenation of its subtree's hashes.
\Cref{fig:merkelized-tree} shows an example of an input and corresponding
output of the |prepare| function, producing a \emph{merkelized} |Tree23|.
The |synthesize| generic combinator annotates each node of the tree
with the result of the catamorphism called at that point with the
given algebra. Our algebra is sketched in pseudo-Haskell below:

\begin{myhs}
\begin{code}
authAlgebra :: Rep (Const Digest) sum -> Const Digest iy
authAlgebra rep = case sop rep of
  Tag c [p_1 , dots , p_n]  -> Const . sha256Concat
                            $$ [encode c , encode (getSNat (TApp iy)) , p_1 , dots , p_n]
\end{code}
\end{myhs} 

  We must append the index of the type in question, in this case |iy|, to our
hash computation to differentiate constructors of different types in
the family represented by the same number.  Once we have the hashes of
all subtrees we must store them in a search-efficient structure.
Given that a hash is just a |[Word]|, the optimal choice is a
|Trie|~\cite{Brass2008} from |Word| to |Int|, where the |Int|
indicates what is the \emph{identifier} of that very tree.

  Looking up whether a tree |x| is a subtree of two fixed trees |s| and |d|
is then merely looking up |x|'s topmost hash, also called the \emph{merkle root},
against the intersection of the tries of the hashes in |s| and |d|.
The depth of our trie is always |4| or |8| for a |sha256| hash can be
be put in that number of machine words, depending on the architecture. 
Assume we have a 32-bit |Word|, this means that the complexity of the 
overall lookup is $\bigO{ \log{} n_1 \times \cdots \times \log{} n_8 }$, 
where $n_i$ indicates how many elements are in each level. Take $m = max(n_1 , \cdots, n_8)$
and we have that the complexity of our lookup is $\bigO{ \log{} m }$. Since we can have at most
256 elements per layer, the complexity of the lookup is bound by $ \bigO{ \log{} 256 } \equiv \bigO{ 1 } $. Naturally, this only holds if we precompute all the hashes,
which is why we have to start handling annotated fixpoints instead
of regular |Fix codes|.

  After a small modification to our |Oracle|, allowing it to receive
trees annotated with hashes we proceed to define the efficient
|buildOracle| function.

\begin{myhs}
\begin{code}
type Oracle codes = forall j dot AnnFix (Const Digest) codes j -> Maybe Int

buildOracle :: Fix codes i -> Fix codes i -> Oracle codes
buildOracle s d = let  s'  = prepare s
                       d'  = prepare d
                   in lookup (mkSharingTrie s' `intersect` mkSharingTrie d')
  where
    -- insert all digests in a trie
    mkSharingTrie :: AnnFix (Const Digest) codes j -> Trie Word Int
\end{code}
\end{myhs}

  Where the |mkSharingTrie| function will maintain a counter and traverse
its argument. At every node it will insert an entry with that node's hash and
the counter value. It then increases the counter and recurses over the children.
The same subtree might appear in different places in |s| and |d|, for the
|Int| associated with it will differ from |mkSharingTrie s'| and |mkSharingTrie d'|.
This is not an issue since our |intersect| has type |Trie k v -> Trie k t -> Trie k v|,
hence, keeping only the assignments from the first trie such that the key is
also an element of the second.

  We can easily get around hash collisions by computing an intermediate
|Trie Word (Exists (Fix codes))| in the |mkSharingTrie| function and every time
we find a potential collision we check the trees for equality.
If equality check fails, a hash collision is found and the entry would be
removed from the map. When using a cryptographic hash, the chance of
collision is negligible. Hence, we ignore such step.

\section{Merging Patches}
\label{sec:merging}

  One of the main motivations for generic structure-aware diffing 
is being able to merge patches that previously required human interaction. 
We have started working on a preliminary algorithm for merging two
|Patch|es but this is still very much a work in progress. It is
worthwhile, nevertheless, to go over how one can solve the easy cases
and document the difficulties of the hard cases.

  The merging problem, illustrated in \Cref{fig:merge-square}, is the
problem of computing |q // p| given two patches |p| and |q|. The patch
|q // p| is sometimes called the \emph{transport} of |q| over |p| or
the \emph{residual}~\cite{Huet1994} of |p| and |q|. Regardless of the
name, it represents the patch that contains the changes of |q| adapted
to be applied on a value that has already been modified by |p|.

\begin{figure}[t]
\begin{displaymath}
\xymatrix{ & o \ar[dl]_{p} \ar[dr]^{q} & \\
          a \ar[dr]_{|q // p|} & & b \ar[dl]^{|p // q|} \\
            & c &}
\end{displaymath}
\caption{Merge square}
\label{fig:merge-square}
\end{figure}

  Our merging operator, |(//)|, receives two patches and returns a patch
possibly annotated with conflicts. Conflicts happen when an automatic
merge is not possible. This operator is very similar to the \emph{residual}
operator, usually studied within a term-rewriting perspective. 

\begin{myhs}
\begin{code}
(//) :: Patch codes at -> Patch codes at -> PatchConf codes at
\end{code}
\end{myhs}

  A |Conflict|, here, is nothing but a pair of irreconcilable
patches. In practice one would carry a label around to identify the
type of conflict for easier resolution. Note that the location is
trivially kept, since the conflicts will where the patches disagree.

\begin{myhs}
\begin{code}
type Conflict codes = Patch codes :*: Patch codes

type PatchConf codes =  Tx codes (Sum (Conflict codes) (Change codes))
\end{code}
\end{myhs}

 The intuition is that |p // q| must preserve the intersection of the
spines of |p| and |q| and reconcile the differences whenever one of
the patches has a change. Note that it is impossible to have
disagreeing spines since |p| and |q| are applicable to at least one
common element.  This is yet another job for the \emph{greatest common
prefix} operator:

\begin{myhs}
\begin{code}
p // q = utxMap (uncurry' reconcile) $$ txGCP p q
\end{code}
\end{myhs}

  The |reconcile| function receives two disagreeing patches and attempt
to transport the left argument over the right argument, that is, |reconcile p q|
attempts to adapt |p| to the codomain |q|. If the patches cannot be
reconciled, we return both patches marked as a conflict. This is 
where we borrow from residual theory~\cite{Huet1994} to discharge 
trivial cases for us. Let us look at the definition of
|reconcile|:

\begin{myhs}
\begin{code}
reconcile  :: Patch codes at -> Patch codes at -> Sum (Conflict codes) (Change codes) at
reconcile p q
  | patchIden p || patchIden q  = InR $$ distr p
  | patchEquiv p q              = InR $$ copy
  | otherwise                   = difficultCases p q
\end{code}
\end{myhs}

  The first branch borrows from the two identity laws from residual
theory that state that |p // id == p| and |id // p == id|. This is
fairly intuitive when spoken out loud. Take the first law as an
example, |p / id|: we are adapting a change |p| to work over an object
has been changed by |id|, but this means the object is the same and we
can apply |p| itself. The second law is also captured by the first
conditional clause of |reconcile|. The third residual law on the
other hand, needs its very own clause. It states that |p // p == id|,
meaning that applying a patch over something that has been modified by
this very patch amounts to not changing anything. The |patchIden| functions
checks whether all changes in that patch are copies and |patchEquiv|
checks if two patches are $\alpha$-equivalent.

  We are now left to handle the difficult cases, when the patches are
not equivalent and none is equivalent to the identity patch. As noted
before, our work in understanding these cases and handling them
successfully is still in progress. We have, however, found that there
are two main situations that can happen: (A) no action needed and (B)
transport of pieces of a patch to different locations in the three.
In \Cref{fig:merging-AB} we illustrate situations (A) and (B) in the
merge square for the patches below:

\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
oa = diff (Node2 t u) (Node2 u t)
ob = diff (Node2 y x) (Node2 y w)
\end{code}
\end{myhs}
\end{minipage}%
\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
oa // ob = oa
ob // oa = apply oa ob
\end{code}
\end{myhs}
\end{minipage}

  In order to apply a patch to another patch we use the same machinery
used to apply a patch to an element. We omit the actual definition of these
functions here as they are verbose and perhaps not final. That is,
this is still a work in progress and our merging approach still has room
for improvement and requires further study. For the interested 
reader, the experiments in \Cref{sec:experiments} were performed
with the code in commit \texttt{53967e7} of our repository\footnote{\hsdigemsgit}.

\begin{figure}
\includegraphics[scale=0.3]{src/img/merge-01.pdf}
\includegraphics[scale=0.3]{src/img/merge-02.pdf}
\caption{Example of a merge square where the first residual is obtained by
not changing the patch and the second is computed by applying a patch
to another patch, transporting the changes.}
\label{fig:merging-AB}
\end{figure}



%%  We have taken care of all the easy cases and are left with the definition
%% of |mergeChange|, the function that merges two changes that are not equal
%% nor copies, we are left with insertions, deletions or modifications. 
%% In fact, it is simple to classify a change as one of these classes: if there
%% is a leaf in the deletion context that is not a |TxHole|, then the
%% change deletes information; if such leaf exists in the insertion
%% context, it inserts information; if it exists in both, it modifies
%% information. 
%% 
%% \begin{myhs}
%% \begin{code}
%% data ChangeType = CIns | CDel | CMod
%% 
%% classify :: Change codes at -> ChangeType
%% \end{code}
%% \end{myhs}
%% 
%%   Recall that the first argument to |mergeChange| is the change
%% that must be adapted to work on the codomain of the second. In
%% case we are attempting to merge two insertions or two deletions
%% we return a conflict. It is worth mentioning that our merge algorithm
%% is very primitive and is the current topic of our research. Here
%% we present a preliminary \emph{underaproximation} algorithm. It is
%% encouraging that such a simple approach already
%% gives us decent results, \Cref{sec:experiments}. That being said,
%% let us start discussing a simple merge algorithm for our
%% structured patches.
%% 
%% \victor{experiment! seems like del/mod should be a conflict, huh?}
%% 
%%   There are three cases that are trivial. Namelly adapting
%% an insertion over deletion or modification; and a deletion
%% over a modification. \victor{after experimentation, explain why}
%% This is because the insertion will be carrying new information that
%% could not have been fiddled with by the deletion or modification.
%% 
%%   The other cases requires a more intricate treatment. Intuitively,
%% when adapting a change |cp| to work on a tree modified by |cq| one \emph{applies} |cq| 
%% to |cp|. This allows us to \emph{transport} the necessary bits of the change to the location
%% they must be applied. For instance, imagine we are given the two patches over |Tree23|: |pa| and |pb| with
%% type |Tx Tree23Codes (Tx Tree23Codes MetaVar :*: Tx Tree23Codes MetaVar) (I Z)|, that is, a common prefix
%% to be copied with \emph{changes} inside. 
%% 
%% \begin{myhs}
%% \begin{code}
%% pa = Node2C (Hole (Change (Leaf 10) (Leaf 20)) (Hole (Change (Hole 0) (Hole 0)))
%% pb = Hole (Change (Node2C (Hole 0) (Hole 1)) (Node2C (Hole 1) (Hole 0)))
%% \end{code}
%% \end{myhs}
%% 
%%   Here, |pa| changes the value in the left children of the root and |pb| swaps the 
%% root children. If we are to apply |pa| on a tree already modified by |pb|, we must transport
%% the |(Leaf 10 , Leaf 20)| change to the right children. This can be easily done by \emph{applying}
%% |pb| to |pa|. That is, instantiate the metavariables in the deletion context of |pb| with
%% values from |pa|. In this case, 0 becomes |Hole (Leaf 10 , Leaf 20)| and 1 becomes |Hole (Hole 0, Hole 0)|.
%% Now we substitute that in the insertion context of |pb|, yielding:
%% 
%% \begin{myhs}
%% \begin{code}
%% pa / pb = Node2C (Hole (Hole 0 , Hole 0)) (Hole (Leaf 10 , Leaf 20))
%% \end{code}
%% \end{myhs}
%% 
%%   This is analogous to applying a change to a term, but instead we apply a change to a change. 
%% We call the function that performs this application |adapt|. Finally, a simple |mergeChange| 
%% can be given below. Recall that we only call this function on changes |cp| and |cq| that
%% are not the identity and |cp /= cq|.
%% 
%% \begin{myhs}
%% \begin{code}
%% mergeChange  :: Change codes at 
%%              -> Change codes at 
%%              -> Sum (Conflict codes) (Change codes) at
%% mergeChange cp cq = case (classify cp , classify cq) of
%%   (CIns , CIns)  -> InL (cp , cq)
%%   (CDel , CDel)  -> InL (cp , cq)
%%   
%%   (CIns , _)     -> InR cp
%%   (CDel , CMod)  -> InR cp
%%   
%%   _              -> adapt cp cq
%% \end{code}
%% \end{myhs}
%%  

\section{Experiments}
\label{sec:experiments}

  We have conducted two experiments over a number of real
Lua~\cite{what} source files. We obtained the data by mining the top
Lua repositories on GitHub and extracting all the merge conflicts recorded
in their history. We then proceeded to run two experiments over this data:
a performance test and a merging test.

\paragraph{Performance Evaluation} In order to evaluate the
performance of our implementation we have timed the computation of the
two diffs, |diff o a| and |diff o b|, for each merge conflict |a,o,b|
using our algorithm.  In order to ensure that the numbers we obtained
are valid and representative of a real execution trace we timed the
execution time of parsing the files and running of |length . encode
. uncurry diff|, where |encode| comes from |Data.Serialize|. Besides
ensuring that the patch is fully evaluated, the serialization also
mimics what would happen in a real version control system since the
patch would have to be saved to disk.  After timing approximately 1200
executions from real examples we have plotted the data over the total
number of constructors for each source-destination pair in
\Cref{fig:performance-plot}. To the left we see a section of the
bigger plot in greater detail. The results are what we would expect
given that |diff x y| runs in $\bigO{n + m}$ where |n| and |m| are the
number of constructors in |x| and |y| abstract syntax trees, respectively.

\paragraph{Merging Evaluation} While working on our merging
algorithm we wanted to analyze whether we could solve any of the 
conflicts that the \texttt{UNIX} diff failed over. Upon a successful
merge from our tool we attempted to apply the merges to the respective
files and made sure that the merge square (\Cref{fig:merge-square})
was commuting. At commit \texttt{53967e7}\footnote{\hsdigemsgit} we
were able to solve a total of 140 conflicts, amounting to 24\% of
the analyzed conflicts.

\begin{figure}\centering
\ra{1.1} % better spacing
\begin{tabular}{@@{}lllll@@{}}
\toprule
Repository         & Commits & Contributors  & Total Conflicts & Solved \\ 
\midrule
awesome            & 9289    & 250 & 5   & 0  \\
busted             & 936     & 39  & 9   & 1  \\
CorsixTH           & 3207    & 64  & 25  & 10 \\
hawkthorne-journey & 5538    & 61  & 158 & 49 \\
kong               & 4669    & 142 & 163 & 31 \\
koreader           & 6418    & 89  & 14  & 5  \\
luakit             & 4160    & 62  & 28  & 7  \\
luarocks           & 2131    & 51  & 45  & 4  \\
luvit              & 2862    & 68  & 4   & 1  \\
nn                 & 1839    & 177 & 3   & 0  \\
Penlight           & 730     & 46  & 6   & 5  \\
rnn                & 622     & 42  & 6   & 3  \\
snabb              & 8075    & 63  & 94  & 19 \\
tarantool          & 12299   & 82  & 33  & 4  \\
telegram-bot       & 729     & 50  & 5   & 1  \\
\midrule
\multicolumn{3}{r}{total}    & 598 & 140 \\
\bottomrule
\end{tabular}
\caption{Lua repositories mined from \emph{GitHub}}
\label{fig:repositoriesmined}
\end{figure}

\begin{figure}
% \includegraphics[scale=0.5]{src/img/runtimes-less-than-10000.pdf}
% \includegraphics[scale=0.5]{src/img/runtimes-all.pdf}
\includegraphics[scale=0.5]{src/img/runtimes.pdf}
\caption{Plot of the time for diffing two lua files over the total AST nodes}
\label{fig:performance-plot}
\end{figure}

\subsection{Threats to Validity} There are two main threats to the
validity of our empirical results. Firstly, we are diffing and merging
abstract syntax trees, hence ignoring comments and formatting. There is no
extra effort in handling those besides writing a custom parser that
records this information. Nevertheless, it is reasonable to expect 
a smaller success rate since we are ignoring all formatting changes
altogether. Secondly, a significant number of developers prefer
to rebase their branches instead of merging them. Hence, we might have
missed a number of important merge conflicts. There is no way of
mining these conflicts back since rebasing erases history. \victor{maybe
not mention this:} Another
important threat to mention is that we did not check whether our merge
corresponds to the merge executed by the developer that manually solved
the conflict. We plan to address this points in the near future. 

\section{Discussions, Future and Related Work}
\label{sec:discussion}

  The results from \Cref{sec:experiments} are very encouraging. 
We see that our diffing algorithm has competitive performance 
and our naive merging operation is already capable of merging
a number of patches that \texttt{diff3} yields conflicts. In order to
leave the research realm and deliver a production tool, there is
still a number of points that must be addressed.

\subsection{Future Work}  

\paragraph{Extending the Generic Universe.}
Our prototype is built on top of \texttt{generics-mrsop}, a generic
programming library for handling mutually recursive families in the
sums of products style. With recent advances in generic
programming~\cite{Serrano2018}, we can think about go a step further
and extend the library to handle mutually recursive families that have
\texttt{GADTs} inside. Moreover, due to a performance bug~\cite{our-memleak-bug} in GHC
we are not able to compile our code for larger abstract syntax tress
such as C, for example. 

\paragraph{Controlling Sharing}
One interesting discussion point in the algorithm is how to control
sharing. As it stands, the differencing algorithm will share anything
that the oracle indicates as \emph{shareable}. This can be undesirable
behavior. For example, we do not want to share \emph{all} occurrences
of a variable in a program, but only those under the same scope.  That
is, we want to respect the scope variables. Same applies for
constants. There are a variety of options to enable this behavior.
The easiest seems to be changing the oracle. Making a custom oracle
that keeps track of scope and hashes occurrences of the same identifier
under a different scope differently will ensure that the scoping is
respected, for instance.

\paragraph{Better Merge Algorithm}
As noted in \Cref{sec:merging}, our merging algorithm is a topic of current study
at the time of writing this paper. We wish to better understand the operation
of merging patches. It seems to share a number of properties from unification theory,
residual systems, rewriting systems and we would like to look into this 
in more detail. This would enable us to better pinpoint the role
that merging plays within our meta-theory, ie, one would hope that it would
have some resemblance to a pushout as in \cite{Mimram2013}. 


\paragraph{Automatic Merge Strategies}
Besides improving on the fully generic algorithm, though, we would like to
have a language to specify domain specific strategies for conflict resolution.
For instance, whenever the merging tool finds a conflict in the \texttt{build-depends}
section of a cabal file, it tries sorting the packages alphabetically and keeping
the ones with the higher version number. Ideally, these rules should be simple to
write and would allow a high degree of customization.

\paragraph{Formalization and Meta-theory}
We would be happy to engage in a formal verification of our work. This could
be achieved by rewriting our code in Agda~\cite{agda} whilst proving
the correctness properties we desire. This process would provide
invaluable insight into developing the meta-theory of our system.

\subsection{Related Work}
\label{sec:related-work}

  The work related to ours can be divided in the typed and untyped
variants. The untyped tree differencing problem was introduced in 1979
\cite{Tai1979} as a generalization of the longest common subsequence
problem~\cite{Bergroth2000}. There has been a significant body of work
on the untyped tree differencing
problem~\cite{Demaine2007,Klein1998,Akutsu2010}, but these hardly transport
to the typed variant, that is, when the transformations are
guaranteed to produce well-typed trees.

  The first attempt was done by Lempsink and L\"{o}h~\cite{Loh2009},
which was later extended by Vassena~\cite{Vassena2016}. Their work
consists largely in using the same algorithm as \texttt{diff} in the
flattened representations of a tree. The main observation is that
basic operations (insertion, deletion and copy) can be shown to be
well-typed when operating on flattened representations. Although one
could compute differences with reasonably fast algorithms, merging
these changes is fairly difficult and in some cases might be
impossible~\cite{Vassena2016}. A different attempt was done by Miraldo
et al.~\cite{Miraldo2017}, where the authors tried to define
operations that work directly on tree shaped data. Using this
approach, changes become easier to merge but harder to compute.
Both bodies of work follow the same general idea as the untyped
variants: compute all possible patches and filter out the bad ones.
As we have already mentioned (\Cref{sec:intro}), this is not an optimal
strategy. The number of patches explodes and defining \emph{the best} is
impossible without heuristics using only insertions, deletions and copies.

  Of the untyped variant, the work of Asenov et al.~\cite{Asenov2017}
is worth mentioning as it uses and interesting technique: it
represents trees in an flattened fashion with some extra information,
then uses the UNIX \texttt{diff} tool to find the differences. Finally, it
transports the changes back to the tree shaped data using the additional
information. The authors also identify a number of interesting situations
that occur when merging tree differences. Another important mention
is the \texttt{gumtree}~\cite{Falleri2014} project, which uses its own
algorithm for computing graph transformations between untyped representations
of abstract syntax trees. 

  From a more theoretical point of view it is also important to
mention the work of Mimram and De Giusto~\cite{Mimram2013}, where the
authors model line-based patches in a categorical fashion. Swierstra
and L\"{o}h~\cite{Swierstra2014} propose an interesting meta theory
for version control of structured data based on separation logic to
model disjoint changes. Lastly, Angiuli et al.~\cite{Angiuli2014}
describes a patch theory based on homotopical type theory.

\subsection{Conclusions}
\label{sec:conclusions}

\victor{conclusion needs a lot of fixing}

  On this paper we have presented an encoding of structured
differences over generic, well-typed, abstract syntax trees that supports
additional operations in comparison with the standard approaches.
We have also presented an efficient algorithm to compute
these differences. Our implementation was validated in practice by
computing diffs over real Lua source files. Moreover, we sketch
the start of a merging algorithm and show some partial results 
obtained with it.

  Our algorithm borrows some techniques from cryptography that
enable a significant speedup from what one would have without them.
The performance of our algorithm shows it is clearly applicable in
practice. This is a very important first step in bringing structured
diffing to practice as a whole and seeing the other potential applications
of this work outside software version control. For example, one could envision writing
\emph{conflict-free replicated datatypes}~\cite{CRDT} in a more generic setting
using a structured differencing algorithm and custom, deterministic, conflict 
resolution strategies.

%% \subsubsection{Edit Scripts}
%% \label{sec:es}
%% 
%%   Before explaining the tree-structured version of \emph{edit scripts}, it is worthwhile
%% to take a look at the original notion of edit scripts upsed by the unix \texttt{diff}~\cite{McIlroy1979}.
%% Those edit scripts are nothing but a list of \emph{instructions} to be applied on a per-line basis
%% on the source file. Below we sketch how the list of instructions would act on a a file
%% seen as a list of lines:
%% 
%% \begin{myhs}
%% \begin{code}
%% data EditInst = Ins String | Del String | Cpy
%% 
%% apply :: [EditInst] -> [String] -> Maybe [String]
%% apply [] [] = Just []
%% apply (Cpy    : es) (line : file) 
%%   = (line :) <$$> apply es file
%% apply (Del s  : es) (line : file) 
%%   | s == line  = apply es file
%%   | otherwise  = Nothing
%% apply (Ins s  : es) file 
%%   = (s :) <$$> apply es file
%% apply _ _
%%   = Nothing
%% \end{code}
%% \end{myhs}
%% 
%%   We call the list of instructions, |[EditInst]|, the \emph{edit script}. Note how this list
%% is essentially isomorphic to a partial function from |Nat| to |EditInst|, tabulating
%% that list. Under this view there is a nice correlation between the operations on the
%% file and their semantics over the subsequent locations. Deleting a line can be seen
%% as decreasing the locations (by pattern matching). Inserting a line is changing
%% the locations to be their successor and copying a line is the identity operation on locations.
%% 
%%    In \citet{Loh2009}, we see an extension of this idea based on the Euler traversal of a tree:
%% one can still have a list of edit instructions and apply them to a tree. By traverssing the tree
%% in a predetermined order, we can look at all the elements as if they were in a list. In fact,
%% using some clever type level programming, one can even ensure that the edit intructions
%% are well typed. The core idea relies on indexing the type of instructions based on the 
%% code of the family being used:
%% 
%% \victor{should we really be showing datatypes?}
%% \begin{myhs}
%% \begin{code}
%% data ES (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> Star where
%%   E0   :: ES codes '[] '[]
%%   Ins  :: Cof codes a c
%%        -> ES codes i  (Tyof codes c  :++:     j)
%%        -> ES codes i  (a            PCons  j)
%%   Del  :: Cof codes a c
%%        -> ES codes (Tyof codes c  :++:     i)  j
%%        -> ES codes (a            PCons  i)  j
%%   Cpy  :: Cof codes a c
%%        -> ES codes (Tyof codes c :++:     i)  (Tyof codes c  :++:   j)
%%        -> ES codes (a           PCons  i)  (a             (P :)  j)
%% \end{code}
%% \end{myhs}
%% 
%%   Where |Cof codes a c| is a predicate that states that |c| is a valid constructor
%% for a type |a| and |Tyof codes c| is a type level function that returns the list of
%% atoms representing the fields of said constructor. 
%% \victor{how important are the details of this implementations? I feel like we should
%% just show the signature of |EditInst| and leave the details for the intersted reader to pursue}
%% 
%%   The application function would then be declared as:
%% 
%% \begin{myhs}
%% \begin{code}
%% apply :: ES codes xs ys -> NP (NA (Fix codes)) xs -> Maybe (NP (NA (Fix codes)) ys)
%% \end{code}
%% \end{myhs}
%% 
%%   Which states that given a product of trees with types |xs|, it might be able to
%% produce a product of trees with types |ys|. This approach has the advantage to enjoy
%% a number of the optimization techniques that have been employed for the unix \texttt{diff}.
%% In fact, a simple memoization table would already yield a quadratic algorithm in the sum
%% of constructors in both origin and destinations. The heterogeneity brings a complicated problem,
%% however, when one wants to consider the merging of two such edit scripts~\cite{Vassena2016}.
%% Given |p :: ES codes xs ys| and |q :: ES codes xs zs|, it is hard to decide what will the
%% index of the merge, |merge p q :: ES codes xs _| by. In fact, this might be impossible.
%% 
%%   In an effort to overcome this limitation \citet{Miraldo2017} introduces a 
%% more structured approach that consists in constraining the heterogeneity to
%% only the necessary places. That is, the |Patch| type receives a single
%% index, call it |ty|, and represents a change that transform values of type |ty|
%% into each other. \TODO{cite Arian and Giovanni?} Although this
%% makes merging easier, computing these patches is drastically more expensive. 
%% The algorithm is not more complicated, per se, but we lose the ability to
%% easily exploit memoization to speed up the computation.
%% 
%% \TODO{linear vs tree patches nomenclature}
%%   
%% 
%% 
%% 
%%   Regardless of the representation, the core of a differencing algorithm is 
%% to identify and pursue the copy opportunities as much as possible. In the
%% previous approaches, discussed in \Cref{sec:es}, the lack of a representation for
%% moving subtrees and duplicating them means that, upon finding a subtree that can be copied
%% to two different places, the algorithm needs to choose between one of them. Besides
%% efficiency problems, this also brings a complicated theoretical problems: it is impossible
%% to order tree structured patches like one can do with linear patches~\cite{Mimram2013}. 
%% If the only operations we have at hand are insertions, deletions and copying of a subtree,
%% we cannot choose between copying the left or the right subtree in:
%% 
%% \begin{myhs}
%% \begin{code}
%% diff (Node2 42 a a) a
%% \end{code}
%% \end{myhs}
%% 
%%   As we mentioned before, the |diff| function has to choose between deleting the constructor
%% accompained by the left or the right subtree in |Node2 42 a a|. Yet, we cannot compare these
%% patches in arguing which is \emph{better} than which without making some arbitrary choices.
%% One example of an arbitrary choice would be to prefer patches that delete leftmost subtrees first.
%% This would make the |diff| function choose to copy the rightmost |a|, but this is not an educated
%% decision: \TODO{and the result might be different. Applying one or the other to |Node2 42 x y|}.
%% 
%% 
%% To illustrate
%% this and other concepts, we will be referring to |Tree23|, even though our definitions
%% will be given in a generic setting.
%% 
%% 
%% 
%%   Unlike the previous work on well-typed structured differencing, we will 
%% represent changes in a different fashion. 
%% 
%% 
%% We will illustrate our generic
%% definitions by instantiating them to work on top of |Tree23|, defined as follows:
%% 
%% \begin{myhs}
%% \begin{code}
%% data Tree23  = Leaf
%%              | Node2 Int Tree23 Tree23
%%              | Node3 Int Tree23 Tree23 Tree23
%% \end{code}
%% \end{myhs}
%% 
%%   Now, suppose one wants to transform the trees below into each other:
%% 
%% \begin{myhs}
%% \begin{code}
%% t1 = Node2 10 (Node3 100 a b c) d
%% t2 = Node3 42 a b d
%% \end{code}
%% \end{myhs}
%% 
%%   \TODO{draw the treefixes}
%% 
%%   
%% 
%% 
%%   Our representation of changes will abstract away all the subtrees that are 
%% copied. 
%% 
%%   Extensionally, a diff is a collection of changes coupled with a location
%% inside a given tree, which dictates ``where'' in the source object this
%% change should be applied. 
%% 
%%   \TODO{As we hinted earlier, a patch is all about a location and a instruction}
%%   \TODO{look at locations in a tree}
%%   \TODO{show how there are more operations we can perform on that and explain that that's
%%         where the slow down is!}
%% 
%%   Some of the previous work on well-typed, structured differencing 
%% 
%% \subsection{Well Typed Tree Prefixes}
%% \label{sec:treefix}
%% 
%% \TODO{I use ``source tree'' here; define it somewhere}
%%  
%%   Extensionally, diff is nothing but a collection of locations inside
%% a tree with a change to be applied on each said location. 
%% 
%% 
%% Since there can
%% only be at most one change per location, overlapping these changes into a 
%% single datatype that consists of a tree
%% with the same shape as the source tree and holes where the changes happen.
%% We can even go a step further and parametrize the type of said holes
%% ariving in the following (free) monad:
%% 
%% \begin{myhs}
%% \begin{code}
%% data Tx :: [[[Atom]]] -> (Atom -> Star) -> Atom -> Star where
%%   TxHole  :: phi at  -> Tx codes phi at
%%   TxOpq   :: Opq k   -> Tx codes phi (K k)
%%   TxPeel  :: Constr (Lkup i codes) c
%%           -> NP (Tx codes phi) (Tyof codes c)
%%           -> Tx codes phi (I i)
%% \end{code}
%% \end{myhs}
%% 
%% \TODO{Why no indicies?}
%% 
%%   A value |t| of type |Tx codes phi (I i)| consists in a value of 
%% type |Fix codes i| with certain subtrees replaced by a value of type |phi|. 
%% There are two important operations one can perform over a ``treefix''. We can inject
%% a valuation for the atoms into the treefix, yielding a tree. Or we can project a
%% valuation from a treefix and a tree.
%% 
%% 
%% \begin{myhs}
%% \begin{code}
%% txInj :: Tx codes phi at
%%       -> Valuation codes phi
%%       -> Maybe (NA (Fix codes) at)
%% \end{code}
%% \end{myhs}
%% 
%% 
%% 
%% \section{Computing Changes}
%% \label{sec:algorithm}
%% 
%%   Convey the observation that contractions and permutations are
%% paramount to have a fast algorithm: if we don't have to choose one of
%% all common subtrees to copy, we can copy them all and remove the choice point!
%% 
%%   Assume we have an oracle that answers the question: ``is $t$ a subtree of
%% both the origin and the destination''?
%% 
%% \subsection{Instantiating the Oracle}
%% \label{sec:oracle}
%% 
%%   With crypto is quite easy to create such oracle.
%% 
%% \section{Discussion and Future Work}
%% \label{sec:discussion}
%% 
%% \section{Conclusion}
%% \label{sec:conclusion}