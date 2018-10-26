\section{Introduction}
\label{sec:introduction}

\TODO{one or two paragraphs here}

  The (well-typed) differencing problem consists in finding a type |Patch|, 
together with functions |diff| and |apply|, for some type |a|, that
satisfy a collection of properties.

\begin{myhs}
\begin{code}
diff  :: a -> a -> Patch a
apply :: Patch a -> a -> Maybe a 
\end{code}
\end{myhs}

  Among the properties one might expect from this pair of functions
is, at least, correctness:

\[ \forall x y . apply (diff x y) x \equiv y \]

  Yet, there is a collection of other properties that might
by desirable to enjoy. For instance, it is certainly desirable that |diff|
is both space and time efficient. That is, it must be fast to compute
a |Patch| and the size of the patch must be smaller than storing both trees.

  Another property one might want to have is the ability to apply a patch
to a number of trees. In fact, we want to apply a patch to the \emph{maximum}
number of trees possible. For example:

\[ forall x y . apply (diff x x) y \equiv y \]

  Capturing the idea that a patch that comes from not changing
anything must be applicable to any element performing exactly 
that action: not changing anything.

  The unix \texttt{diff}~\cite{McIlroy1979} solves the differencing problem
for the special case of |a == [String]|, ie, it files are seen as
lists of lines. We are interested in a more generic solution, however.

  \TODO{one or two para's here}


\subsection{Contributions}

  Our contribution 
\begin{itemize}
  \item We provide a linear algorithm to compute tree differences
        with support for swapping and contractions.
\end{itemize}

\section{Background}
\label{sec:background}

  There are two dimensions of backgroung to our work. On one hand, we
use recent generic programming techniques that allows us to write our
algorithm for a range of datatypes at once. On the other hand, there
is the nuances of our diffing algorithm with the previous work in the
field.  These dimensions are not independent. A more expressive
generic programming library enables us to explore better alternatives
to the existing algorithms. On this section we will briefly present
the generic programming approach we used and we will discuss how the
previous work would look like under that library.

\subsection{Generic Programming}
\label{sec:genericprogramming}

\victor{How much type level programming introduction do we need?}

  We subscribe to the \emph{sums-of-products} school of generic 
programming~\cite{deVries2014}. Yet, since we need to handle arbitrary abstract 
syntax trees, must encode mutually recursive families within 
our universe. The rest of this section briefly explains the 
\texttt{generics-mrsop}~\cite{Miraldo2018} library, which was inspired by
the \texttt{generics-sop}~\cite{deVries2014}. 

  In the \emph{sums-of-products} approach, every datatype is assigned
a \emph{code} that consists in two nested lists of atoms. The outer
list represents the choice of constructor, and packages the \emph{sum} part
of the datatype whereas the inner list represents the \emph{product} of the
fields of a given constructor. The \texttt{generics-mrsop} goes one step further
and uses atoms to distinguish whether a field is a recursive
position, |I n|, or a opaque type, |K k|.

\begin{myhs}
\begin{code}
type family    Code (a :: Star) :: P ([ (P [Atom]) ])
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
interested reader to the original paper for more information.

  The last piece of our puzzle is to define a functor of kind |Nat -> Star| that we can
pass as a parameter to |NA| to interpret the recursive positions. The indexed least fixedpoint
fits perfectly:

\begin{myhs}
\begin{code}
newtype Fix (codes :: P [ P [ P [ Atom ] ] ]) (ix :: Nat)
  = Fix { unFix :: NS (NP (NA (Fix codes))) (Lkup codes ix) }
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

\TODO{Write about |View|, |sop| and |match|}.

\subsection{Structured Differencing}
\label{sec:bgstdiff}

  Once equipped with enough terminology on generic programming, lets
look at representing structured diffs and discuss the advantages and disadvantages
of each technique.

\subsection{Unstructured Differencing}
\label{sec:diff}

Introduce \cite{McIlroy1979}.

\subsubsection{Edit Scripts}
\label{sec:es}

  Before explaining the tree-structured version of \emph{edit scripts}, it is worthwhile
to take a look at the original notion of edit scripts upsed by the unix \texttt{diff}~\cite{McIlroy1979}.
Those edit scripts are nothing but a list of \emph{instructions} to be applied on a per-line basis
on the source file. Below we sketch how the list of instructions would act on a a file
seen as a list of lines:

\begin{myhs}
\begin{code}
data EditInst = Ins String | Del String | Cpy

apply :: [EditInst] -> [String] -> Maybe [String]
apply [] [] = Just []
apply (Cpy    : es) (line : file) 
  = (line :) <$$> apply es file
apply (Del s  : es) (line : file) 
  | s == line  = apply es file
  | otherwise  = Nothing
apply (Ins s  : es) file 
  = (s :) <$$> apply es file
apply _ _
  = Nothing
\end{code}
\end{myhs}
  
  \TODO{Talk about how |[ES]| is isomorphic to |Nat -> ES|, here, the |Nat| corresponds to 
        the location in the file, when seen as a list of lines}
  \TODO{The operations correspond to three operations on |Nat|: pattern match and extract
        something (del); succ (ins) and id (cpy)}

  In \citet{Loh2009}, we see an extension of this idea based on the Euler traversal of a tree:
one can still have a list of edit instructions and apply them to a tree. By traverssing the tree
in a predetermined order, we can look at all the elements as if they were in a list. In fact,
using some clever type level programming, one can even ensure that the edit intructions
are well typed. The core idea relies on indexing the type of instructions based on the 
code of the family being used:

\victor{should we really be showing datatypes?}
\begin{myhs}
\begin{code}
data ES (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  E0   :: ES codes '[] '[]
  Ins  :: Cof codes a c
       -> ES codes i  (Tyof codes c  :++:     j)
       -> ES codes i  (a             (P (:))  j)
  Del  :: Cof codes a c
       -> ES codes (Tyof codes c  :++:     i)  j
       -> ES codes (a             (P (:))  i)  j
  Cpy  :: Cof codes a c
       -> ES codes (Tyof codes c :++:     i)  (Tyof codes c  :++:   j)
       -> ES codes (a            (P (:))  i)  (a             (P :)  j)
\end{code}
\end{myhs}

  Where |Cof codes a c| is a predicate that states that |c| is a valid constructor
for a type |a| and |Tyof codes c| is a type level function that returns the list of
atoms representing the fields of said constructor. 
\victor{how important are the details of this implementations? I feel like we should
just show the signature of |EditInst| and leave the details for the intersted reader to pursue}

  The application function would then be declared as:

\begin{myhs}
\begin{code}
apply :: ES codes xs ys -> NP (NA (Fix codes)) xs -> Maybe (NP (NA (Fix codes)) ys)
\end{code}
\end{myhs}

  Which states that given a product of trees with types |xs|, it might be able to
produce a product of trees with types |ys|. This approach has the advantage to enjoy
a number of the optimization techniques that have been employed for the unix \texttt{diff}.
In fact, a simple memoization table would already yield a quadratic algorithm in the sum
of constructors in both origin and destinations. The heterogeneity brings a complicated problem,
however, when one wants to consider the merging of two such edit scripts~\cite{Vassena2016}.
Given |p :: ES codes xs ys| and |q :: ES codes xs zs|, it is hard to decide what will the
index of the merge, |merge p q :: ES codes xs _| by. In fact, this might be impossible.

\subsubsection{Spines and Alignments}
\label{sec:stdiff}

  \TODO{Homogeneous patches make life esier!}
  \TODO{Homogeneous patches make computer's warm!}  

  Introduce \cite{Miraldo2017}.

\section{Representing Changes}
\label{sec:representing-changes}

  \TODO{As we hinted earlier, a patch is all about a location and a instruction}
  \TODO{look at locations in a tree}
  \TODO{show how there are more operations we can perform on that and explain that that's
        where the slow down is!}

  Some of the previous work on well-typed, structured differencing 

\subsection{Well Typed Tree Prefixes}
\label{sec:treefix}

\TODO{I use ``source tree'' here; define it somewhere}

  In fact, a tree diff is nothing but a collection of locations inside
a tree with a change to be applied on each said location. We can imagine
overlapping these changes into a single datatype that consists of a tree
with the same shape as the source tree and holes where the changes happen.
We can even go a step further and parametrize the type of said holes
ariving in the following (free) monad:

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

\TODO{Why no indicies?}

  Extentionally, a value |t| of type |Tx codes phi (I i)| consists in a value of 
type |Fix codes i| with certain subtrees replaced by a value of type |phi|. 
  


\section{Computing Changes}
\label{sec:algorithm}

  Convey the observation that contractions and permutations are
paramount to have a fast algorithm: if we don't have to choose one of
all common subtrees to copy, we can copy them all and remove the choice point!

  Assume we have an oracle that answers the question: ``is $t$ a subtree of
both the origin and the destination''?

\subsection{Instantiating the Oracle}
\label{sec:oracle}

  With crypto is quite easy to create such oracle.

\section{Discussion and Future Work}
\label{sec:discussion}

\section{Conclusion}
\label{sec:conclusion}