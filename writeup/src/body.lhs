\section{Introduction}
\label{sec:introduction}

\subsection{Contributions}

\begin{itemize}
  \item We provide a linear algorithm to compute tree differences
        with support for swapping and contractions.
\end{itemize}
  
\section{Representing Data}
\label{sec:representing-data}

  In order achieve a generic algorithm, we must first settle
on a representation for our data. We have implemented our prototype
on using the \texttt{generics-mrsop}~\cite{Miraldo2018} library,
which provides generic functionality for mutually recursive families.

\subsection{Mutually Recursive Families}
\label{sec:mrsop}

  The \texttt{generics-mrsop} library provides a \emph{sums-of-products}
view over the data.

\begin{myhs}
\begin{code}
type family    Code (a :: Star) :: P ([ (P [Star]) ])
\end{code}
\end{myhs}

  \begin{itemize}
    \item Go over representation of data and some generic functionality
    \item the notion of constructors and their fields being the central aspect.
  \end{itemize} 

\section{Representing Changes}
\label{sec:representing-changes}

  Some of the previous work on well-typed, structured differencing 

\subsection{Edit Scripts}
\label{sec:es}

  Introduce \cite{Loh2009,Vassena2016}.
  Introduce \cite{Miraldo2017}.

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