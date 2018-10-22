\section{Introduction}
\label{sec:introduction}

\subsection{Contributions}

\begin{itemize}
  \item We provide a linear algorithm to compute tree differences
        with support for swapping and contractions.
\end{itemize}

\section{Background}
\label{sec:background}

  There are two dimensions of backgroung to our work. On one hand,
we have the advances in generic programming that allows us to write
better diffing tools. On the other hand, there is the diffing algorithm
used per se. These dimensions are not independent. A more expressive generic
programming library enables us to explore better alternatives to the
existing algorithms. On this section we will briefly present the
generic programming approach we used and we will discuss how the previous
work would look like under that library.

\subsection{Generic Programming}
\label{sec:genericprogramming}

  We subscribe to the \emph{sums-of-products} school of generic 
programming~\cite{deVries2014}. Yet, since we need to handle arbitrary abstract 
syntax trees, we need the abilityto encode mutually recursive families within 
our universe. The rest of this section briefly explains the 
\texttt{generics-mrsop}~\cite{Miraldo2018} library. 

  In a \emph{sums-of-products} approach, every datatype is assigned
a \emph{code} that consists in two nested lists of atoms. The outer
list represents the choice of constructor, and packages the \emph{sum} part
of the datatype whereas the inner list represents the \emph{product} of the
fields of a given constructor. The atoms tells us whether a field is a recursive
position or a opaque type.

\begin{myhs}
\begin{code}
type family    Code (a :: Star) :: P ([ (P [Atom]) ])
\end{code}
\end{myhs}

  The codes for a mutually recursive family, then, are defined as a 
list of codes for sums-of-products. Consider the following mutually 
recursive family: 

\begin{myhs}
\begin{code}
data Zig  = Zig Int   | ZigZag Zag
data Zag  = Zag Bool  | ZagZig Zig
\end{code}
\end{myhs}

  Its codes are:

\begin{myhs}
\begin{code}
type CodesZig = P  [ P [ P [ K KInt ]   , P [ I 1 ] ]
                   , P [ P [ K KBool ]  , P [ I 0 ] ]
                   ]
\end{code}
\end{myhs}

\subsection{Edit Scripts}
\label{sec:es}

  Introduce \cite{Loh2009,Vassena2016}.
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