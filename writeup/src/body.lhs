\section{Introduction}
\label{sec:introduction}

\subsection{Contributions}

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

\subsubsection{Edit Scripts}
\label{sec:es}

  Introduce \cite{Loh2009,Vassena2016}.

\subsubsection{Spines and Alignments}
\label{sec:stdiff}

  Introduce \cite{Miraldo2017}.

\subsection{Mutually Recursive Families}
\label{sec:mrsop}

  The \texttt{generics-mrsop} library provides a \emph{sums-of-products}
view over the data.


  \begin{itemize}
    \item Go over representation of data and some generic functionality
    \item the notion of constructors and their fields being the central aspect.
  \end{itemize} 

\section{Representing Changes}
\label{sec:representing-changes}

  Some of the previous work on well-typed, structured differencing 

\subsection{Well Typed Tree Prefixes}
\label{sec:treefix}

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