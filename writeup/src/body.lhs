\section{Introduction}
\label{sec:introduction}

% Bug because of double lines?
% https://blog.codecentric.de/en/2014/02/curly-braces/

  Software version control systems are vastly present in the
software development community. They are responsible to manage a
differencing algorithm that computes the differences between two files, 
the most common being the UNIX \texttt{diff}~\cite{McIlroy1979}.
Line-based tools, however, are of very coarse granularity and fail
to identify more fine grained changes in software source code. As a result,
we have a lot of man-hours being spent in conflict resolution. 

  Let us abstract the granularity on which version control takes place
and have a look at the problem description for an arbitrary type.
The (well-typed) differencing problem consists in finding a type |Patch|, 
together with functions |diff| and |apply|, for some type |a|, that
satisfy a collection of properties.

\begin{myhs}
\begin{code}
diff   :: a -> a -> Patch a
apply  :: Patch a -> a -> Maybe a 
\end{code}
\end{myhs}

  The |diff| function computes a |Patch| for a given type whereas the
|apply| function interprets these patches as partial functions over |a|.
Naturally, we must impose some properties on how |diff| and |apply|
behave for them to be of any use.

  Among the properties one might expect from this pair of functions
is, at least, correctness:

\[
| forall x y dot apply (diff x y) x == Just y |
\]

  Yet, there is a collection of other properties that might
by desirable to enjoy. For instance, it is certainly desirable that |diff|
is both space and time efficient. That is, it must be fast to compute
a |Patch| and the size of the patch must be smaller than storing both trees.

  Another property one might want to have is the ability to apply a patch
to a number of trees. In fact, we want to apply a patch to the \emph{maximum}
number of trees possible. For example:

\[ | forall x y dot apply (diff x x) y == Just y | \]

  Capturing the idea that a patch that comes from not changing
anything must be applicable to any element performing exactly 
that action: not changing anything.

  The unix \texttt{diff}~\cite{McIlroy1979} solves the differencing
problem, and satisfies many of these desirable properties, for the
special case of |a == [String]|, ie, files are seen as lists of
lines. Although there has been attempts at a solution for arbitrary
such |a|s, all of them have the same \emph{modus operandis}: compute
all possible patches betweem two objects, then we filter out \emph{the
best}. There two big problems being (A) the inefficiency of a
non-deterministic algorithm with many choice points and (B) defining
what is \emph{the best} patch.  These two problems stem from the same
place: having access only to insert, delete and copy as base
operations.

  The core of a differencing algorithm is to identify and pursue the
copy opportunities as much as possible. Therefore the lack of a
representation for moving and duplicating subtrees is an inherent
issue.  Upon finding a subtree that can be copied in two different
ways, he algorithm must choose between one of them. Besides efficiency
problems, this also brings a complicated theoretical problems: it is
impossible to order these patches in an educated fashion.

  Imagine we want to compute a patch that transforms a tree |Bin t u| 
into |Bin u t|.  If the only operations we have at hand are insertions,
deletions and copying of a subtree, we cannot compare choosing to copy
the left or the right subtree. No option is better than the other. If, however,
we have some operation that encodes permutation of subtrees, we have not only removed
a choice point from the algorithm but also arrived at a provably better patch
\victor{provably according to who? Me!!! but what does it mean to be better anyway?}
without having to resort to heuristics or arbitrary choices. And, 
contrary to what one might expect, more is less in this scenario. By
adding more expressive basic change operations (duplicate and permute) we
were able to remove choice points and arrive at a very efficient algorithm.

\paragraph{Contributions.} 

\begin{itemize}
  \item A solution to the well-typed differencing problem
        that does not suffer from problems (A) and (B) outline above.
        In fact, our approach supports subtree duplications and permutations
        and satisfy a number of the desired properties listed above, including
        space efficiency.
  \item An idealized algorithm capable of computing a patch that
        transforms a source tree into a target tree. We also give a practical
        instantiation of this algorithm that is correct modulo cryptographic hash
        collisions and runs in linear time.
  \item A prototype implementation of our algorithm that
        is immediately applciable to a large universe of datatypes,
        namelly, any mutually recursive family.
  \item A prorotype notion and implementation of a merging algorithm.
        We have evaluated our implementation against unsolved conflicts
        from a number of GitHub repositories in the Lua programming language.
        \victor{how many?}
\end{itemize}

\section{Sketch and Background}

  Before exploring the fully generic implementation of our algorithm,
it is very valuable to look at a simple instance first. On this
section we will sketch our algorithm for a simple type and outline its
basic building blocks, \Cref{sec:concrete-changes}.  Then, we will
briefly explain some generic programming techniques,
\Cref{sec:generic-prog}, that are necessary to translate the simple
implementation into a fully generic one.

\subsection{Representing Changes, Concrete Example}
\label{sec:concrete-changes}

  Let us define a solution to the differencing problem for |Tree23|, the type
of two-three-trees, defined below:

\begin{myhs}
\begin{code}
data Tree23  = Leaf
             | Node2 Tree23 Tree23
             | Node3 Tree23 Tree23 Tree23
\end{code}
\end{myhs}

  Recall that we are interested in identifying and pursuing as many copy
opportunities as possible. Once we copy a subtree, we need not inspect inside
it any longer. Hence, we will represent patches as trees with \emph{holes}. The holes
correspond to coppied subtrees whereas the tree leading to the hole corresponds to
the deleted an inserted part. The type of changes over |Tree23| can be obtained by
adding an extra constructor to |Tree23|:

\begin{myhs}
\begin{code}
data Tree23C = LeafC
             | Node2C Tree23C Tree23C
             | Node3C Tree23C Tree23C Tree23C
             | Hole Int
\end{code}
\end{myhs}

  We could now represent the patch that transforms |Node2 t u| in |Node2 u t|
by a pair of |Tree23C|, namelly: |(Node2C (Hole 0) (Hole 1) , Node2C (Hole 1) (Hole 0))|.
The |fst| component of the pair denotes the deleted tree with \emph{metavariables} inside,
whereas the second component is the inserted tree. Applying a patch is modelled by 
deleting the first component, yielding a valuation of metavariables to trees when successful,
then substituing the metavariables in the insertion context with such valuation. 

\begin{myhs}
\begin{code}
del :: Tree23C -> Tree23 -> Maybe (Map Int Tree23)
del ctx tree = go ctx tree empty 
  where
    go :: Tree23C -> Tree23 -> Map Int Tree23 -> Maybe (Map Int Tree23)
    go LeafC           Leaf           m = return m
    go (Node2C x y)    (Node2 a b)    m = go x a m >>= go y b
    go (Node3C x y z)  (Node3 a b c)  m = go x a m >>= go y b >>= go z c
    go (Hole i)        t              m = case lookup i t of
                                            Nothing  -> return (singleton i t)
                                            Just t'  -> guard (t == t') 
                                                     >> return m
    go _               _              m = Nothing
\end{code}
\end{myhs}

  Note that we use an auxiliar function that starts with an empty valuation
and gradually inserts new values into it. This makes it easier to make sure
that in case a variable already exist, its value is the same as what we are
trying to insert.

  Inserting a |Map Int Tree23| into a |Tree23C| is the dual operation:

\begin{myhs}
\begin{code}
ins :: Tree23C -> Map Int Tree23 -> Maybe Tree23
ins LeafC           m  = return Leaf
ins (Node2C x y)    m  = Node2 <$$> ins x m <*> ins y m
ins (Node3C x y z)  m  = Node3 <$$> ins x m <*> ins y m <*> ins z m
ins (Hole i)        m  = lookup i m
\end{code}
\end{myhs}

  Finally, we can define our application function by composing |ins| and
|del|:

\begin{myhs}
\begin{code}
type Patch = (Tree23C , Tree23C)

apply :: Patch -> Tree23 -> Maybe Tree23
apply (d , i) x = del d x >>= ins i
\end{code}
\end{myhs}

  Next, we must be able to produce a |Patch| from a source and a destination,
essentially defining our |diff| function. Recall that the core characteristic
of the differencing function is to exploit as many copy opportunities as possible.
Assume we have access to a function |ics|, \emph{is common subtree},
with type |Tree23 -> Tree23 -> Tree23 -> Maybe Int|. When calling |ics s d x|
we shall get a |Nothing| when |x| is not a subtree of |s| and |d| or |Just i|
when |x| is a common subtree. The |Int| inside the |Just| tells us which metavariable
number to use. The only condition we impose is injectivty of |ics s d| on the |Just|
subset of the image. That is, if |ics s d x == ics s d y == Just j|, then |x == y|.
Later on we will provide an efficient implementation for |ics|, but for now, let us
take it as an oracle. Finally, the |diff| function is defined as:

\begin{myhs}
\begin{code}
diff :: Tree23 -> Tree23 -> Patch
diff s d = (extract (ics s d) s , extract (ics s d) d)
\end{code}
\end{myhs}

  Where the |extract| function traverses the |Tree23| and extracts a |Tree23C|
according to a function that assigns metavariables to trees. This assignment must be
injective whenever it returns a |Just|.

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

  Assuming that |ics s d| is \emph{the best} possible such function, that is, it will
correctly issue metavariables to \emph{all} common subtrees of |s| and |d|, we see
that our implementation satisfy a number of the desired properties stated in \Cref{sec:intro}:

\begin{description}
  \item[Correctness] Assuming |ics| is correct, 
    \[ |forall x y dot apply (diff x y) x == Just y| \]
  \item[Preciseness] Assuming |ics| is correct,
    \[ |forall x y . apply (diff x x) y == Just y| \]
  \item[Time Efficiency] 
    Assuming |ics| constant, the run-time of our algorithm 
    is linear on the number of constructors everywhere else.
    We will provide such constant |ics| function in \Cref{sec:oracle}.
  \item[Space Efficiency] 
    The size of a |Patch| is, on average, smaller than 
    storing its source and destination tree.
\end{description}

\paragraph{Summary} We have provided a simple algorithm 
to solve the differencing problem for |Tree23|. We start by creating 
a type |Tree23C| which consists in adding a \emph{metavariable} constructor
to |Tree23| and assume the existence of an oracle that answers whether
an arbitrary tree is a subtree of the source and the destination. We then
construct a value of type |Tree23C| from a |Tree23| and an oracle. That
really is the core principle behind the algorithm.

  Naturally, this illustrative version of our algorithm does have some shortcomings that
are addressed in a later stage, \Cref{sec:representing-changes}.
For one, we are not trying to minimize the changes after we |extract| 
a context from the source or destination trees. This makes merging harder.
Another shortcomming is that we are not addressing what happens when there
exists a subtree that appears in at least two different places with one occurence
being under a larger subtree. This can break the apply function and needs to
be idenfied. Moreover, this example algorithm shares subtrees too eagerly.
For instance, every occurence of |Leaf| will be shared under the same metavariable.
This restriction does not impact the correctness of the algorithm but 
is an important point on the design space: how do we drive this machinery,
\Cref{sec:sharing}.

\subsection{Background: Generic Programming}
\label{sec:generic-prog}

  Now that we have an idea of how our algorithm looks like for a specific
type, let us briefly explain the \texttt{generics-mrsop}~\cite{Miraldo2018}
library, which will allow us to rewrite the code in \Cref{sec:concrete-changes}
in a fully generic setting. This library follows the \emph{sums-of-products} school of generic 
programming~\cite{deVries2014}. Yet, since we need to handle arbitrary abstract 
syntax trees, must encode mutually recursive families within 
our universe. 

  In the \emph{sums-of-products} approach, every datatype is assigned
a \emph{code} that consists in two nested lists of atoms. The outer
list represents the choice of constructor, and packages the \emph{sum} part
of the datatype whereas the inner list represents the \emph{product} of the
fields of a given constructor. The \texttt{generics-mrsop} goes one step further
and uses atoms to distinguish whether a field is a recursive
position, |I n|, or a opaque type, |K k|.

\begin{myhs}
\begin{code}
type family Code (a :: Star) :: P ([ (P [Atom]) ])
\end{code}
\end{myhs}

  The codes for a mutually recursive family, then, are defined as a 
list of codes for sums-of-products. Consider the following mutually 
recursive family: 

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

  The representation is defined by the means of $n$-ary sums and products that work
by induction on the \emph{codes} and one interpretation for atoms.

\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data NS :: (k -> Star) -> [k] -> Star where
  Here   :: f x      -> NS f (x (P (:)) xs)
  There  :: NS f xs  -> NS f (x (P (:)) xs)
\end{code}
\end{myhs}
\end{minipage} %
\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data NP :: (k -> Star) -> [k] -> Star where
  Nil   :: NP f (P [])
  Cons  :: f x -> NP f xs -> NP f (x (P (:)) xs)
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

  The |NS| type is responsible for determining the choice of constructor whereas the
|NP| applyes a representation functor to all the fields of the selected constructor.
In our case, it is |NA|, that distinguishes between representation of a recursive position
from an opaque type. Although the \texttt{generics-mrsop} provides a way to customize the
set of opaque types used, this is not central do the developments in this paper and
hence we will assume a type |Opq| that interprets the necessary atom types. We refer the
interested reader to the original paper~\cite{Miraldo2018} for more information.

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

  The last piece of our puzzle is to define a functor of kind |Nat -> Star| that we can
pass as a parameter to |NA| to interpret the recursive positions. The indexed least fixedpoint
fits perfectly:

\begin{myhs}
\begin{code}
type Rep phi = NS (NP (NA phi))

newtype Fix (codes :: P [ P [ P [ Atom ] ] ]) (ix :: Nat)
  = Fix { unFix :: Rep (Fix codes) (Lkup codes ix) }
\end{code}
\end{myhs}

  Where |Lkup codes ix| denotes the type level lookup of the element with index |ix| within
the list |codes|. This type family throws a type error if the index is out of bounds.
We could then write the generic versions of the constructors of type |Zig|:

\begin{myhs}
\begin{code}
gzig :: Int -> Fix CodesZig 0
gzig n = Fix (Here (Cons (NA_K (OpqInt n)) Nil))

gzigzag :: Fix CodesZig 1 -> Fix CodesZig 0
gzigzag zag = Fix (There (Here (Cons (NA_I zag) Nil)))
\end{code}
\end{myhs}

  One of the main benefits of the \emph{sums-of-products} approach to generic
programming is that it enables us to pattern match generically. In fact,
we can state that a value of a type consists precisely in a choice of constructor
and a product of its fields. We start by defining the notion of \emph{constructor}
of a generic type:

\begin{myhs}
\begin{code}
data Constr :: [[k]] -> Nat -> Star where
  CZ ::                 Constr (x (P (:)) xs)  Z
  CS :: Constr xs c ->  Constr (x (P (:)) xs)  (S c)
\end{code}
\end{myhs}

  We use |Constr sum c| as a predicate indicating that |c| is a valid constructor, ie,
it is a valid index into the type level list |sum|. Next, we define a |View| over
a value of a sum type to be a choice of constructor and corresponding product:

\begin{myhs}
\begin{code}
data View :: (Nat -> Star) -> P [ P [ Atom ] ] -> Star where
  Tag :: Constr sum c -> NP (NA phi) (Lkup c sum) -> View phi sum

sop :: Fix codes i -> View (Fix codes) (Lkup i codes)
\end{code}
\end{myhs}

  The |sop| functions converts a value in its standard representation
to the more useful choice of constructor and associated product.

\section{Representing and Computing Changes, Generically}
\label{sec:representing-changes}

\TODO{Disclaimer: we present significantly simpler code.
go check the repo for the actual stuff!}

  In \Cref{sec:concrete-changes} we gained some intuition about the
workings of our algorithm. In \Cref{sec:generic-prog} we saw some techniques
for writting programs over arbitrary mutually recursive families. The natural
next step is to start writing our algorithm in a generic fashion. Throughout
this section we will continue to assume the existence of an efficient oracle
|ics|, for answering \emph{is |t| a subtree of |s| and |d| indexed by |n|}.
The type of oracles is defined below together with a function that
builds an oracle from a source, |s|, and a destination, |d|: 

\begin{myhs}
\begin{code}
type Oracle codes = forall j dot Fix codes j -> Maybe Int

buildOracle :: Fix codes i -> Fix codes i -> Oracle codes
\end{code}
\end{myhs}

  Recall our |Tree23C| type, from \Cref{sec:concrete-changes}. It augmented
the |Tree23| type with an extra constructor for representing holes, by the
means of a \emph{metavariable}. This type construction is crucial to the
representation of our patches. In fact, it works out for an arbitrary
mutually recursive family:

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

  Note that our |Tx| is, in fact, the indexed free monad over the |Rep| functor.
Essentialy, a value of type |Tx codes phi at| is nothing but a value of
type |NA (Fix codes) at| augmented with \emph{holes} of type |phi|.

  Differently then with |Tree23C|, in |Tx| we parametrize the type of \emph{metavariables}.
This comes in quite handy as it allows us to use the |Tx| for a number of intermediate
steps in the algorithm. The first one being the extraction of a |Tx| from
a |Fix codes ix| by annotating the common subtrees with their index,
provided by the oracle. We first check whether |x| is a subtree, if so,
we annotate it with a hole. Otherwise we extract the constructor and
its fields from |x|. We the map |TxOpq| on the opaque fields and continue extracting
on the fields that reference recursive positions:

\begin{myhs}
\begin{code}
txExtract :: Oracle codes
          -> Fix codes ix 
          -> Tx codes (ForceI (Const Int :*: Fix codes)) (I ix)
txExtract ics x = case ics x of
    Just i   -> TxHole (ForceI (Const i :*: x))
    Nothing  -> let Tag c p = sop (unFix x)
                 in TxPeel c (mapNP (elimNA TxOpq (extractAtom ics)) p)
\end{code}
\end{myhs}

  The above code is very similar to |extract| from \Cref{sec:concrete-changes},
but here we hace some additional types: |ForceI| is used to ensure that 
the index is of the |I ix| form and |(:*:)| is just a indexed product.

\begin{myhs}
\begin{code}
data ForceI :: (Nat -> Star) -> Atom -> Star where
  ForceI :: f i -> ForceI f (I i)

data (:*:) f g x = f x :*: g x
\end{code}
\end{myhs}

  Once we extract the |Tx| from both the source and destination trees,
we must decide which holes should be kept, and which holes whould be demoted
to a |Tx|. In fact, we only want the holes that appear both in the source |Tx|
and the destination |Tx|. To ilustrate the problem, magine the following two |Tree23|:

\begin{myhs}
\begin{code}
a = Node2 (Node2 t k) u
b = Node2 (Node2 t k) t
\end{code}
\end{myhs}

  Our oracle will recognize |Node2 t k| and |t| as a common subtree. Extracting
the |Tree23C| will from both trees yields:

\begin{myhs}
\begin{code}
extract a = Node2C (Hole 0) u
extract b = Node2C (Hole 0) (Hole 1)
\end{code}
\end{myhs}

  Note how the metavariable |Hole 1| is appears only on one side. That happens because it
occurs inside a bigger common subtree. If we were to apply this patch to |a|, we would
get an \emph{undefined variable} error. We solve this by postprocessing the resulting
|Tx|s and keeping only the metavariables that occur in both contexts. Lets call this
function |txPostprocess|:

\begin{myhs}
\begin{code}
txPostprocess  ::  Tx codes (ForceI (Const Int :*: Fix codes)) (I ix)
               ->  Tx codes (ForceI (Const Int :*: Fix codes)) (I ix)
               ->  (  Tx codes (ForceI (Const Int)) (I ix)
                   ,  Tx codes (ForceI (Const Int)) (I ix))
\end{code}
\end{myhs}

  The definition is uninteresting. It proceeds by grouping every metariable in a set,
computing the intersection of the sets, then mapping over the arguments and replacing
the |Const Int :*: Fix codes| hole by either |Const Int|, if the |Int| belongs in
the set, or by a |Tx codes (ForceI (Const Int))| with no holes, isomorphic to the 
second component of the pair.

  At this point, given two trees |a, b| of type |Fix codes ix|, we have extracted both
the deletion and insertion contexts, of type |Tx codes (ForceI (Const Int)) (I ix)|. These
are just like a value of type |Fix codes ix| with possible holes in some recursive positions,
called \emph{metavariables}. In fact, one such deletion and one such insertion context
make up a \emph{change}.

\begin{myhs}
\begin{code}
data Change codes phi at = Change (Tx codes phi at) (Tx codes phi at)
\end{code}
\end{myhs}

  We could then write a prelimanry |diff| function using the |txExtract| and |txPostprocess|
described above:

\begin{myhs}
\begin{code}
diff0 :: Fix codes ix -> Fix codes ix -> Change codes (ForceI (Const Int)) (I ix)
diff0 x y = let  ics = buildOracle x y
                del = txExtract ics x
                ins = txExtract ics y
            in uncurry Change $$ txPostprocess del ins
\end{code}
\end{myhs}

  This function will output \emph{one} single change that transforms |x| into |y|. This is not
very ideal. For starters, a good number of the constructors of our trees will be repeated on both
the insertion and deletion contexts. Moreover, when we try to merge these changes together, it is 
much easier to have a number of small changes throughout the tree than a single big change. Hence,
we want to chop that big change comming out of |diff0| into a tree with holes, where these holes
contain smaller changes. That is, we will divide that change into the \emph{greatest common prefix}
of the insertion and deletion context with smaller changes inside:

\begin{myhs}
\begin{code}
txGCP :: Tx codes phi at -> Tx codes psi at -> Tx codes (Tx phi :*: Tx psi) at
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

\victor{see \ref{comment:minimality}}

  Now, given a |Change codes phi at|, we can identify the exactly where the
changes happen by pushing the |Change| as close to the leaves as possible
by pulling out the constructors that are \emph{deleted} then \emph{inserted}.
This is not without consequences, though. Imagine the following value of
type |Change Tree23Codes (Const Int) (I Z)|, shown here in its isomorphic
type |(Tree23C , Tree23C)| and the resulting call to |txGCP|:

\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
prob  :: (Tree23C , Tree23C)
prob  =  (  Node2C (Hole 0) x
         ,  Node2C (Hole 0) (Hole 0)
         )
\end{code}
\end{myhs}
\end{minipage}
\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
txGCP prob = Node2C  (Change (TxHole 0)  (TxHole 0))
                     (Change x           (TxHole 0))
\end{code}
\end{myhs}
\end{minipage}
  
  Note how the second change in |txGCP prob| has |TxHole 0| unbound. That happens because
|TxHole 0| will be bound to the left child from the root. Hence, we cannot decouple these changes.
We call the changes were the deletion context instantiates all the necessary variables for the
insertion context \emph{closed changes}. The \emph{open changes} are those that contain metavariables in the
insertion context that do not occur on the deletion context.

  We can map over |txGCP prob| and tag the changes we see in either \emph{open}
or \emph{closed}. We would arrive at something like:
\victor{shall I add the code? How about explaining |Sum|?}

\begin{myhs}
\begin{code}
txMap isClosed (txGCP prov)  = Node2C  (InR (Change (TxHole 0)  (TxHole 0)))
                                       (InL (Change x           (TxHole 0)))
\end{code} 
\end{myhs}

  Finally, we traverse the result trying to eliminate all the \emph{open changes},
tagged by |InL|. We do so by finding the closest closed change that binds the required
variables:

\begin{myhs}
\begin{code}
closure  :: Tx codes (Sum (Change codes phi) (Change codes phi)) at
         -> Sum (Change codes phi) (Tx codes (Change codes phi)) at
closure (TxOpq x) = InR (TxOpq x)
closure (TxHole (InL oc)) = InL oc
closure (TxHole (InR cc)) = InR cc
closure (TxPeel cx px) 
  = let aux = mapNP closure px
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

  The interesting case of the |closure| function is the |TxPeel| pattern. We
essentially try to compute all the closures for the fields of the constructor.
If no more open changes are left, we are done. Otherwise, we have to bubble the changes
up to the |TxPeel| and finally check whether we were able to \emph{close} this
change or not. We use two simple auxiliar functions to distribute a |Change| over
a |Tx| and to eliminate a |Sum| type:

\TODO{move |either'| out of here}
\begin{myhs}
\begin{code}
distr :: Tx codes (Change codes phi) at -> Change codes phi at
distr tx = Change (join (txMap chgDel tx)) (join (txMap chgIns tx))

either' :: (f x -> r x) -> (g x -> r x) -> Sum f g x -> r x
either' a b (InL fx) = a fx
either' a b (InR gx) = b gx

\end{code}
\end{myhs}

  We finalize by assembling all of these pieces in a single |diff| function.
Where |MetaVarIK| is defined by |NA (Const Int) (Const Int)|, essentially distinguishing
between a metavariable that is suppused to be instantiated by a recursive member of the
family or a opaque type. 

\begin{myhs}
\begin{code}
type Patch codes at = Tx codes (Change codes MetaVarIK) at

diff :: Fix codes ix -> Fix codes ix -> Patch codes (I ix)
diff x y = let  ics   = buildOracle x y
                del0  = txExtract ics x
                ins0  = txExtract ics y
                (del1 , ins1) = txPostprocess del ins
            in case closure (txGCP del1 ins1) of
              InL _ -> error "unreachable"
              InR r -> txRefine TxHole mkCpy r
\end{code}
\end{myhs}

  The last step in the |diff| function is identifying the opaque values that should be copied. 
This is easy to do since the |txGCP| already put those opaque values in the \emph{copied} part
of the patch. Hence, we simply need to traverse the patch and replace the occurences of |TxOpq|
by a new \emph{copy} change. We use the |txRefine| function, declared below.

\begin{myhs}
\begin{code}
txRefine :: (forall at  dot f at   -> Tx codes g at) 
         -> (forall k   dot Opq k  -> Tx codes g (K k)) 
         -> Tx codes f at -> Tx codes g at
\end{code}
\end{myhs}

  The center of our algorithm is the |Tx| free monad. We use said type
in different contexts with different meanings. In summary, a value of
type |Tx codes phi at| consists of a representation of a value indexed
by |at| with holes of type |phi|. Recall the definition of |Patch|,
and note it can be simplified as |Tx codes (Tx codes MetaVarIK :*: Tx codes MetaVarIK)|,
hence, the outer |Tx| represents the copied constructors that lead to the
changes, of type |Tx codes MetaVarIK :*: Tx codes MetaVarIK|. These,
in turn, represent both a deletion context and an insertion context
respectively. The deletion context contains the constructors that must 
be \emph{pattern matched} and the metavariables that must be instantiated
whereas the insertion context is the dual: constructors are injected and
variables are looked up. We shall see yet another use of |Tx| when we
come to merging, \Cref{sec:merging}.

  The application of a |Patch| follows very closely the implementation
of the application presented in \Cref{sec:concrete-changes} but uses
some more advanced type level mechanisms. The most important one being the
encoding of the interpretation of an atom with an existential index.

\begin{myhs}
\begin{code}
data NAE :: [[[Atom kon]]] -> * where
  SomeFix :: Fix codes ix -> NAE codes
  SomeOpq :: Opq k        -> NAE codes
\end{code}
\end{myhs}

  Which allows the application function to carry a |Map Int (NAE codes)|,
analogously to the |Map Int Tree23| in \Cref{sec:concrete-changes}. When
looking a value in a |Map Int (NAE codes)| we must be able to cast
it to the correct type, extracted from a |MetaVarIK|.

\begin{myhs}
\begin{code}
naeCast  :: NAE ki codes
         -> MetaVarIK ki at
         -> Either String (NA ki (Fix ki codes) at)
\end{code}
\end{myhs}

  The definition is uninteresting and can be found in the code. With these
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

\subsection{The Oracle}
\label{sec:oracle}

  The oracle used to decide which subtrees to share between source and
destination is a central part of the algorithm. The overall efficiency
of the algorithm depends exclusively on this oracle being
efficient. In this section we shall provide two implementations for
the oracle. One inefficient but intuitive, and another that is more
involved but satisfies the efficiency constraints.

  When deciding whether a given subtree |x| should be shared, s naive
oracle would check every single subtree of the source and destination
for equality against |x|.  Upon finding a match, it would return the
index of such subtree in the list of all subtrees. The implementation
of this oracle is quite straightforwar. First, we enumerate all
possible subtrees:

\victor{Does this typecheck? I think I need a |Exists|}
\begin{myhs}
\begin{code}
subtrees :: Fix codes i -> [ forall j dot Fix codes j ]
subtrees x = x : case sop x of
  Tag _ pt -> concat (elimNP (elimNA (const []) subtrees) pt)
\end{code}
\end{myhs}

  Next, we define a heterogeneous equality over |Fix codes| and search through the
list of all possible subtrees. The heterogeneous equality starts by comparing the
indexes of the |Fix codes| values. If they agree, we proceed to compare them for
propositional equality.

\begin{myhs}
\begin{code}
idx :: (a -> Bool) -> [a] -> Maybe Int
idx f  []     = Nothing
idx f  (x:xs) = if f x then Just 0 else (1+) <$$> idx f xs

heqFix :: Fix codes i -> Fix codes j -> Bool
heqFix x y = case testEquality x y of
               Nothing    -> False
               Just Refl  -> eqFix x y
\end{code}
\end{myhs}

  Finally, we can put together our inefficient |buildOracle|: start
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

  There are two points of inefficiency in the naive |buildOracle| above. First,
we build the |subtrees| list twice, once for the source and once for the destination.
We then proceed to compare a third tree, |t|, for equality with every subtree in
the prepared lists. That is an extremely expensive computation that can be avoided
by precomputing some values and storing them in the correct structure.

  In order to compare trees for equality in constant time we can annotate them
with cryptographic hashes~\cite{Menezes1997} and compare those instead. This technique 
transforms our trees into \emph{merkle trees}~\cite{Merkle1988} and is more commonly
seen in the security and authentication context~\cite{Miller2014,Miraldo2018HAMM}.
Nevertheless, we can use the generic programming machinery that is already at our
disposal. The \texttt{generics-mrsop} provide some attribute grammar~\cite{Knuth1990} mechanisms,
in particular synthetization of attributes:

\begin{myhs}
\begin{code}
newtype AnnFix x codes i = AnnFix (x i , Rep (AnnFix x codes) (Lkup i codes))

prepare :: Fix codes i -> AnnFix (Const Digest) codes i
prepare = synthesize authAlgebra
\end{code}
\end{myhs}

  Here, |AnnFix| is a cofree comonad to add a label to each recursive branch
of our generic trees. In our case, this label will be the cryptographic hash of the
concatenation of its subtree's hashes.
The |synthesize| generic combinator annotates each node of the tree with
the result of the catamorphism called at that point. Our algebra
is sketched in pseudo-Haskell below:

\begin{myhs}
\begin{code}
authAlgebra :: Rep (Const Digest) sum -> Const Digest iy
authAlgebra rep = case sop rep of
  Tag c [p_1 , dots , p_n]  -> Const . sha256Concat
                            $$ [encode c , encode (getSNat @iy) , p_1 , dots , p_n]
\end{code}
\end{myhs} 

  Note that we must append the index of the type in question to our hash computation
to differentiate constructors of different types in the family represented by the same number.
Once we have the hashes of all subtrees we must store them in a search-efficient structure.
Given that a hash is just a |[Word]|, the optimal choice is a |Trie|~\cite{Brass2008} 
from |Word| to |Int|, where the |Int| indicates what is the \emph{identifier} of that very tree. 

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

  The resulting trie will contain only the hashes of the subtrees
of the source and destination, and these can be efficiently looked up
returning a unique identifier for that specific subtree. 

  We can easily get around hash collisions by computing an intermediate
|Trie Word (Exists (Fix codes))| in the |mkSharingTrie| function and
later forgetting the trees. This strucure keeps the trees associated with each hash,
which can in turn be checked for equality when inserting a new tree. If a hash collision
is found we can conservatively remove the entry from the map and do not consider
such tree as a shared subtree. When using a cryptographic hash, the chance of
collision is negligible. Hence, we ignore such step.

\section{Merging Patches}
\label{sec:merging}

  One of the main motivations for generic structure-aware diffing 
is being able to merge patches that previously required human interaction. 
We have started working on said problem and have achieved some interesting
results shown in \Cref{sec:experiments}, yet, it is worth mentioning that
this is very much a work in progress.

  The merging problem, illustrated in \Cref{fig:merge-square}, is the problem
of computing |q / p| given two patches |p| and |q|. The patch |q / p| is sometimes
called the \emph{transport} of |q| over |p| or the \emph{residual}~\cite{Huet1994}
of |p| and |q|. Regardless of the name, it represents the patch that contains
the changes of |q| adapted to be applied on a value that has already
been modivied by |p|.

\begin{figure}[t]
\begin{displaymath}
\xymatrix{ & o \ar[dl]_{p} \ar[dr]^{q} & \\
          a \ar[dr]_{|q / p|} & & b \ar[dl]^{|p / q|} \\
            & c &}
\end{displaymath}
\caption{Merge square}
\label{fig:merge-square}
\end{figure}

  Our merging operator, |(/)|, receives two patches and returns a patch
possibly annotated with conflicts. Conflicts happen when an automatic
merge is not possible.

\begin{myhs}
\begin{code}
(/) :: Patch codes at -> Patch codes at -> PatchConf codes at
\end{code}
\end{myhs}

  A |Conflict|, here, is nothing but a pair of irreconciliable
patches. In practice one would carry a label around to identify the
type of conflict for easier resolution. Note that the location is
trivially kept, since the conflicts will where the patches disagree.

\begin{myhs}
\begin{code}
type Conflict codes = Patch codes :*: Patch codes

type PatchConf codes =  Tx codes (Sum (Conflict codes) (Change codes))
\end{code}
\end{myhs}

  The definition of |p / q| is simple. First we extract the greatest common
prefix of |p| and |q|. This is the prefix of the source tree that both
|p| and |q| copy and can safely be kept. Once we take the |txGCP p q|,
of type |Tx codes (Patch codes :*: Patch codes) at|, we are left with
a treefix with a pair of patches in its holes. Moreover, we know that
these patches will disagree on the topmost constructor. Hence, we
try to reconcile those:

\begin{myhs}
\begin{code}
p / q = utxMap (uncurry' reconcile) $$ txGCP p q
\end{code}
\end{myhs}

  The |reconcile| function receives two disagreeing patches and attempt
to transport the left argument over the right argument, that is, |reconcile p q|
attempts to adapt |p| to the codomain |q|. If the patches cannot be
reconciled, we return both patches marked as a conflict. 

\begin{myhs}
\begin{code}
reconcile :: Patch codes at -> Patch codes at -> Sum (Conflict codes) (Change codes) at
\end{code}
\end{myhs}

  Our first case consist in both patches being changes. We start by checking
whether either change is a copy. If so, we return |p|. If |p| is a copy,
then adapting a copy over a new domain is just another copy, hence
we can return |p| itself. It |q| is a copy, adapting |p| to work on
the \emph{same} domain is simply |p| itself. If neither change is
a copy, but they are $\alpha$-equivalent, we return a copy. 
Finally, when the changes are not a copy nor equivalent we must
try a more complicated merge.

\begin{myhs}
\begin{code}
reconcile (TxHole p) (TxHole q)
  | isCpy p || isCpy q  = TxHole (InR p)
  | p == q              = TxHole (InR copy)
  | otherwise           = TxHole (mergeChange p q)
\end{code}
\end{myhs}

  The cases where only one of the patches consist in a change
are analogous. We must check whether that change is a copy and
return the corresponding value. If it is not a copy we use
the distributive law |distr :: Patch codes at -> Change codes at|
and merge the changes.

\begin{myhs}
\begin{code}
reconcile p (TxHole q) 
  | isCpy q    = utxMap InR p
  | otherwise  = TxHole (mergeChange (distr p) q)
reconcile (TxHole p) q = ... -- analogous
\end{code}
\end{myhs}

  Lastly, case neither patch is a change is an impossible branch.
We assumed that both patches were applicable to at least one common
element and |reconcile| is called \emph{after} extracting the greatest
common prefix. 

\begin{myhs}
\begin{code}
reconcile _ _ = error "unreachable"
\end{code}
\end{myhs}

\TODO{I'm HERE}

\victor{define the notion of applicable}
tHere, we also assume that both patches are applicable to at least one common value.

  \TODO{Describe reconcile; describe change classification}


  
\victor{\label{comment:minimality} we should mention this earlier. What is
this concept?
  -- The merging algorithm algorithm works best when we are merging
patches with minimal changes.
}

  The actual algorithm is fairly simple and can be built moslty from
combinators we already introduced. 



\section{Experiments}
\label{sec:experiments}

\TODO{show how many conflicts of each lua repository we can solve}

\section{Discussions, Future and Related Work}
\label{sec:discussion}

\victor{Make these in paragraphs}
\subsection{Extending the Generic Universe}
\label{sec:gadts}

  Our prototype is built on top of \texttt{generics-mrsop}, a generic
programming library for handling mutually recursive families in the
sums of products style. With recent advances in generic programming~\cite{Serrano2018},
we can think about go a step further and extend the library to handle
mutually recursive families that have \texttt{GADTs} inside.

\subsection{Controlling Sharing}
\label{sec:sharing}

  One interesting discussion point in the algorithm is how to control sharing. As
it stands, the differencing algorithm will share anything that the oracle 
indicates as \emph{shareable}. This can be undesired. For example, we do not
want to share \emph{all} occurences of a variable in a program. We need to respect
the scope of this variables. Same applies for constants. It seems like
the easiest way to control this is by the means of a custom oracle that
keeps track of scope and hashes occurences of the same identifer under a different
scope differently, for instance.

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

  Although also untyped, the work of Asenov et al.~\cite{Asenov2017}
is worth mentioning as it uses and interesting technique: it
represents trees in an flattened fashion with some extra information,
then uses the UNIX \texttt{diff} tool to find the differences. Finally, it
transports the changes back to the tree shaped data using the additional
information. The authors also identify a number of interesting situations
that occur when merging tree differences.

  From a more theoretical point of view it is also important to mention
the work of Mimram and De Giusto~\cite{Mimram2013}, where the authors model line-based
patches in a categorical fashion. Swierstra and L\"{o}h~\cite{Swierstra2014} propose
an interesting meta theory for version control of structured data based on separation
logic to model disjoint changes. Lastly, Angiuli et al.~\cite{Angiuli2014} describes a patch
theory based on homotopical type theory.

\subsection{Conclusions}
\label{sec:conclusions}


\TODO{\huge I'm here!}


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
%%        -> ES codes i  (a             (P (:))  j)
%%   Del  :: Cof codes a c
%%        -> ES codes (Tyof codes c  :++:     i)  j
%%        -> ES codes (a             (P (:))  i)  j
%%   Cpy  :: Cof codes a c
%%        -> ES codes (Tyof codes c :++:     i)  (Tyof codes c  :++:   j)
%%        -> ES codes (a            (P (:))  i)  (a             (P :)  j)
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