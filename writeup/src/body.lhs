\section{Introduction}
\label{sec:introduction}

% Bug because of double lines?
% https://blog.codecentric.de/en/2014/02/curly-braces/

Software Version Control Systems are an essential tool in modern
software development. Platforms such as Github and Bitbucket are only
possible due to the widespread adoption of tools such as git,
mercurial and darcs, that enable multiple developers to collaborate
effectively.  At the heart of all these tools is the UNIX \texttt{diff}
utility~\cite{McIlroy1976}, that computes a patch between two versions
of a file.  The \texttt{diff} utility compares files on a line-by-line
basis and attempts to share lines between its source and destination
whenever possible. While this works well in practice, this fixed
granularity of change cannot describe common refactorings---such as
variable renaming---effectively. Representing all patches on the basis
of the lines that have been changed may therefore lead to spurious
\emph{merge conflicts} when combining the work of different
developers.
%Wouter: or maximize copies?

In this paper we will present an efficient datatype generic algorithm
to compute the difference between two algebraic datatypes, while
guaranteeing to share subtrees whenever possible. In particular, this
algorithm can be instantiated to the abstract syntax tree of a
programming language---thereby enabling two changes to the same line
of code to be merged, provided they do not modify the same parts of
the underlying tree. We have implemented our algorithm in Haskell,
using the datatype generic libraries it provides. %todo citation to mr-sop?

Before making stating the novel contributions of this paper, we will
start by giving a specification of the problem that we aim to solve.
In general, we intend to compute the difference between two trees of
type |a|, and represent these changes in some type, |Patch a|. There
are two functions, |diff| and |apply|, that manipulate patches. The
|diff| function computes the differences between two values of type
|a|; wherease the |apply| function attempts to transform a value of
type |a| according to the information stored in its argument patch:
\begin{myhs}
\begin{code}
diff   :: a -> a -> Patch a
apply  :: Patch a -> a -> Maybe a 
\end{code}
\end{myhs}
Note that the |apply| function may fail, for example, when attempting
to delete data that is not present. Yet when it succeeds, the |apply|
function must return a value of type |a|. This may seem like an
obvious design choice, but this property does not hold for the
approaches~\cite{Asenov2017,Falleri2014} using \texttt{xml} or
\texttt{json} to represent their abstract syntax trees, where the
result of applying a patch may produce ill-formed tree.


Beyond type correctness, we expect certain properties of our |diff|
and |apply| functions. The first property captures the expected
behaviour of |diff|: the patch that |diff x y| computes can be used to
faithfully reproduces |y| from |x|.

\[
| forall x y dot apply (diff x y) x == Just y |
\]

Yet, there are several other desirable properties.
For instance, we require that |diff|
is both space and time efficient. That is, it must be fast to compute
a |Patch| and its size must be smaller than storing both values
of type |a|. This last point is important: one could argue that |Patch a = (a,a)| is a perfectly
fine solution. Yet, storing all revisions of every file under
version control is clearly not an acceptable solution.

The |apply| function is partial. The property stated above requires
apply to succeed in one particular instance---but what should happen
when applying a patch to a different value than was used to create the
input patch? We argue that the apply function should only fail when
strictly necessary. In particular, if there are no changes, the patch should
represent a \emph{no-op}, and its application should be the identity:

\[ | forall x y dot apply (diff x x) y == Just y | \]

  This captures the idea that a patch that does not make any modifications
must be applicable to any value.

The UNIX \texttt{diff}~\cite{McIlroy1976} satisfies these properties,
but is restricted work on lines of text.  There have been several
attempts at a generalizing these results to handle arbitrary data
types~\cite{Loh2009,Miraldo2017}, following the same pattern: they
describe patches as a series of insertions, deletions, and copy
operations. Finding the best possible patch becomes quite a challenge:
firstly, the non-deterministic nature of the problem quickly leads to
inefficient algorithms; furthermore, there are many situations where
there is no canonical `best' patch available.

Let us illustrate this last point with the example in
\Cref{fig:linear-patch}. Existing datatype generic approaches with
insertions, deletions and copies typically perform a preorder
traversal of the trees, copying over constructors whenever
possible. Yet if we want to transform a binary tree |Bin t u| into
|Bin u t| using only these operations, we will be forced to choose
between copying |t| or |u|, but never both. The choice of which
subtree to copy becomes arbitrary and unpredictable. To make matters
worse, the non-determinism such choice points introduce makes
algorithms intractably slow.
%todo{I don't think you even need the right hand side of Figure 1...}

The central design decision underlying the UNIX \texttt{diff} tool is
to \emph{copy data whenever possible}. Yet this example shows that
restricting the set of operations also limits the opportunities for
copying data. In the presence of richly structured data beyond lines
of text, this becomes especially problematic.

\begin{figure}
\includegraphics[scale=0.3]{src/img/patch-00.pdf}
\caption{Visualization of a |diff (Bin t u) (Bin u t)| using insertions, deletions and copies only}
\label{fig:linear-patch}
\end{figure}

This paper explores a novel direction for differencing algorithms:
rather than restricting ourselves to insertions, deletions, and copy
operations, we allow the arbitrary reordering, duplication, and
contraction of subtrees. Not only does this restrict the inherent
non-determinism in the problem, making it \emph{easier} to find
patches, this also \emph{increases} the opportunities for copying.
More specifically, this paper makes the following novel contributions:

\begin{itemize}
\item This paper defines a datatype generic |diff| function that
  computes a patch between two algebraic datatypes that is efficient
  in both time and space.  This |diff| function supports the
  duplication and permutation of subtrees, and satisfies all the
  desired properties outlined above. We illustrate this algorithm by
  first defining a specific instance
  (Section~\ref{sec:concrete-changes}), before presenting a complete generic
  version capable of handling arbitrary mutually recursive families of
  datatypes (Section~\ref{sec:generic-diff}).
\item Initially, we present our diff algorithm under the assumption
  that an oracle exists, capable of detecting all possible copying
  opportunities. We give a practical implementation of this oracle
  that is correct modulo cryptographic hash collisions and runs in
  linear time (Section~\ref{sec:oracle}). 
\item We show how generic patches that are \emph{disjoint} may be
  \emph{merged} automatically (Section~\ref{sec:merging}). 
\item Finally, we have instantiated our algorithm to the abstract
  syntax tree of Lua and collected historical data regarding merge
  conflicts from popular GitHub repositories. We show how our naive
  merging algorithm is already capable of resolving more than 10\% of
  the merge conflicts encountered automatically, while still offering
  competive performance (Section~\ref{sec:experiments}).
\end{itemize}

\section{Tree Diffing: A Concrete Example}
\label{sec:concrete-changes}

  Before exploring the generic implementation of our algorithm, let us
look at a simple, concrete instance first. This sets the stage and
introduces the intuition behind the building blocks used throughout
the generic implementation
(\Cref{sec:representing-changes}). Throughout this section we will
explore the central ideas from our algorithm instantiated for a
specific type, namely, two-three-trees, defined below.

\begin{myhs}
\begin{code}
data Tree23  =  Leaf
             |  Node2 Tree23 Tree23
             |  Node3 Tree23 Tree23 Tree23
\end{code}
\end{myhs}

  The central concept of our work is the encoding of a \emph{change}.
Unlike previous work~\cite{Loh2009,Miraldo2017,Klein1998} based on
tree-edit-distance~\cite{Bille2005} which uses only insertions,
deletions and copies and considers the preorder traversal of a tree
(\Cref{fig:linear-patch}) we go a step further. We explicitly model
duplications and contractions of subtrees within our notion of
\emph{change}. The representation of a \emph{change} between two
values of type |Tree23| is given by identifying the bits and pieces
that must be copied from source to destination.

  A new datatype, |Tree23C phi|, enables us to annotate a value of
|Tree23| with holes of type |phi|. Therefore, |Tree23C MetaVar|
represents the type of |Tree23| with holes carrying metavariables. 
These metavariables correspond to arbitrary trees
that are \emph{common subtrees} of both the source and destination of the change.
These are exactly the bits that are being copied from source to destination.
We refer to a value of |Tree23C| as a \emph{context}. 
For now, the metavariables will be simple |Int| values but later
on we will need to carry additional information.

\begin{myhs}
\begin{code}
type MetaVar = Int

data Tree23C phi  = Hole phi
                  | LeafC
                  | Node2C Tree23C Tree23C
                  | Node3C Tree23C Tree23C Tree23C
\end{code}
\end{myhs}

  A \emph{change}, then, is defined by a pattern that
binds some metavariables, called the deletion context, and an expression
where we are supposed to instantiate its metavariables, called the insertion
context:

\begin{myhs}
\begin{code}
type Change23 phi = (Tree23C phi , Tree23C phi)
\end{code}
\end{myhs}

\begin{figure}
\includegraphics[scale=0.3]{src/img/patch-01.pdf}
\caption{Visualization of a |diff (Node2 t u) (Node2 u t)|, metavariables are shown in red}
\label{fig:first-patch}
\end{figure}

  The change that transforms |Node2 t u| into |Node2 u t| is then
represented by a pair of |Tree23C|, |(Node2C (Hole 0) (Hole 1) ,
Node2C (Hole 1) (Hole 0))|, as seen in \Cref{fig:first-patch}.
This change works on any tree built using the |Node2| constructor
and swaps the children of the root.

\subsection{Applying Changes}

  Applying a change is done by instantiating the
metavariables against the deletion context and the insertion context:

\begin{myhs}
\begin{code}
applyChange :: Change23 MetaVar -> Tree23 -> Maybe Tree23
applyChange (d , i) x = del d x >>= ins i
\end{code}
\end{myhs}

Naturally, if the term |x| and the deletion context |d| are
\emph{incompatible}, this operation will fail. Contrary to regular
pattern-matching we allow variables to appear more than once on both
the deletion and insertion contexts. Their semantics are dual:
duplicate variables in the deletion context must match equal trees
whereas when in the insertion context will duplicate trees. We use an
auxiliary function within the definition of |del| to make this check
easier to perform.

\begin{myhs}
\begin{code}
del :: Tree23C MetaVar -> Tree23 -> Maybe (Map MetaVar Tree23)
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
we reach |Hole i| is that we check whether we have already instantiated
metavariable |i|. If that is the case we must make sure that the values agree.
Otherwise we simply instantiate the metavariable with the corresponding tree.

  Once we have obtained a valuation from a deletion context and 
a tree, we substitute the variables in the insertion context
with their respective values, obtaining the resulting tree.
This phase fails when the change contains unbound variables.

\begin{myhs}
\begin{code}
ins :: Tree23C MetaVar -> Map MetaVar Tree23 -> Maybe Tree23
ins LeafC           m  = return Leaf
ins (Node2C x y)    m  = Node2 <$$> ins x m <*> ins y m
ins (Node3C x y z)  m  = Node3 <$$> ins x m <*> ins y m <*> ins z m
ins (Hole i)        m  = lookup i m
\end{code}
\end{myhs}

\subsection{Computing Changes}

  Next, we explore how to produce a change from a source and a
destination, defining a |changeTree23| function. This function
will exploit as many copy opportunities as possible. For now, we delegate the
decision of whether a subtree should be copied or not to an
oracle: assume we have access a function |ics|, \emph{``is common
subtree''}, with type |Tree23 -> Tree23 -> Tree23 -> Maybe MetaVar|, where
|ics s d x| returns |Nothing| when |x| is \emph{not} a subtree of |s| and |d|
or |Just i| otherwise. The only condition we impose is
injectivity of |ics s d| on the |Just| subset of the image. That is, if
|ics s d x == ics s d y == Just j|, then |x == y|. That is, the same subtree
is assigned the same metavariable. 
  
  Assuming the existence of this oracle is commonplace.  There is an
obvious inefficient implementation for |ics|. Later on, in
\Cref{sec:oracle}, we provide an efficient and generic
implementation. Nevertheless, abstracting away the oracle allows for a
simple separation of tasks.  The |changeTree23| function merely has to
compute the deletion and insertion contexts using said oracle.  This
is done by the means of an |extract| function that receives an oracle
and a tree and extracts a context from its second argument.

\begin{myhs}
\begin{code}
changeTree23 :: Tree23 -> Tree23 -> Change23 MetaVar
changeTree23 s d = (extract (ics s d) s , extract (ics s d) d)
\end{code}
\end{myhs}

  The |extract| function traverses its argument tree, looking for
sharing opportunities by calling the oracle, which answers whether a tree
is a subtree of both |s| and |d|. If that is the case, we want our
change to \emph{copy} such subtree. That is, we return a |Hole|
whenever the second argument of |extract| is a common subtree
according to the oracle.  If the oracle returns |Nothing|, we
move the topmost constructor to the context and recurse into the
children.

\begin{myhs}
\begin{code}
extract :: (Tree23 -> Maybe MetaVar) -> Tree23 -> Tree23C MetaVar
extract o x = maybe (peel x) Hole (o x)
  where
    peel Leaf           = LeafC
    peel (Node2 a b)    = Node2C (extract o a) (extract o b)
    peel (Node3 a b c)  = Node3C (extract o a) (extract o b) (extract o c)
\end{code}
\end{myhs}

  Note that had we used a version of |ics| that only returns a boolean
value we would not know what to put in the |Hole| and would have to do
some additional computation. Returning a value that uniquely
identifies a subtree allows us to keep the |extract| function linear
in the number of constructors in |x| disconsidering the oracle calls.

  This iteration of the |changeTree23| function suffers from an
important correctness issue: Not all trees identified by the oracle
are \emph{true} copies.  We cannot copy trees that occur as a subtree
of the source and destination but additionally as a subtree of another
common subtree. One such example is shown in
\Cref{fig:problematic-ics}, where the oracle recognizes |Node2 t k|
and |t| as common subtrees, and |t| additionally occurs by itself one
of the extracted contexts will contain an undefined metavariable. This
will trigger an \texttt{undefined variable} error when trying to apply
that change, i.e., applying the change from \Cref{fig:problematic-ics}
would trigger such error when the |ins| function tried to lookup
metavariable |1|.

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
\begin{centering}
\begin{minipage}[t]{.5\textwidth}
\begin{myhs}
\begin{code}
postprocess a b (extract (ics a b) a) (extract (ics a b) b)
  = (Node2C (Hole 0) u , Node2C (Hole 0) t)
\end{code}
\end{myhs}
\end{minipage}
\end{centering}
\caption{Example of erroneous context extraction due to nested common subtrees}
\label{fig:problematic-ics}
\end{figure}

  One way to solve this is using an additional processing step that goes over the 
the contexts and substitutes the variables that occur exclusively in
the deletion or insertion context by their corresponding tree.
We could implement |postprocess| using |del| to get two valuations: one
for the deletion context against the source tree and another for the
insertion context against the destination tree. This information is later used
to know what to substitute the \emph{unused} or \emph{undeclared} metavariables for.
We postpone the implementation until its generic incarnation in \Cref{sec:representing-changes}.

\begin{myhs}
\begin{code}
postprocess  :: Tree23 -> Tree23 -> Tree23C MetaVar -> Tree23C MetaVar
             -> (Tree23C MetaVar , Tree23C MetaVar)
\end{code}
\end{myhs}

  We fix the previous |changeTree23| by
postprocessing the extracted contexts. The new version of
|changeTree23| will only produce closed changes, i.e., a deletion
and a insertion context that have \emph{the same set of
metavariables}. Intuitively, this means that every variable that is
declared is used and vice-versa.

\begin{myhs}
\begin{code}
changeTree23 :: Tree23 -> Tree23 -> Change23 MetaVar
changeTree23 s d = postprocess s d (extract (ics s d) s) (extract (ics s d) d)
\end{code}
\end{myhs}

  Assuming that |ics s d| correctly issues metavariables to \emph{all}
common subtrees of |s| and |d|, it is not hard to see that our
implementation already satisfies the properties enumerated in
\Cref{sec:introduction}, namely:

\begin{description}
  \item[Correctness] Assuming |ics| is correct, 
    \[ |forall x y dot applyTree23 (diffTree23 x y) x == Just y| \]
  \item[Preciseness] Assuming |ics| is correct,
    \[ |forall x y dot applyTree23 (diffTree23 x x) y == Just y| \]
  \item[Time Efficiency] 
    On the worst case, we perform one query to the oracle per
    constructor in our trees. Assuming |ics| to be a constant time
    function, our algorithm is linear on the number of constructors
    in the source and destination trees. We will provide such |ics|
    in \Cref{sec:oracle}.
  \item[Space Efficiency] 
    The size of a |Change23 MetaVar| is, on average, smaller than 
    storing its source and destination tree completely. On the worst case,
    where there is no common subtree, they have the same size.
\end{description}

  Although correct with respect to our specification, our |changeTree23|
is not ideal. A call to |changeTree23 x y| yields a \emph{single} |Change23| over trees that
transforms, in particular, |x| into |y|. This large change is carrying
redundant information as a number of constructors are being deleted, then inserted back again.
Moreover, it is much easier to handle small and isolated changes as we will
see in \Cref{sec:merging}. 

\subsection{Minimizing Changes: Computing Patches}

  The process of minimizing and isolating the changes starts by
identifying the redundant part of the contexts. That is, the
constructors that show up as a prefix in the deletion and the
insertion context. They are essentially being copied over and we want
to make this fact explicit by separating them into what we call the
\emph{spine} of the patch. The spine will then contain changes on its
leaves:

\begin{figure}
\includegraphics[scale=0.3]{src/img/patch-example.pdf}
\vspace{.4em}
\begin{myhs}
\begin{code}
Node3C  (Hole   (Hole 0 , Hole 0))
        (Hole   (Node2C (Hole 0) (Hole 1) , Node2C (Hole 1) (Hole 0))
        (Node2C  (Hole  (tree23toC w, tree23toC w'))
                 (Hole  (Hole 3, Hole 3)))
\end{code}
\end{myhs}
\caption{Graphical and textual representation of the patch that transforms the value %
|Node3 t (Node2 u v) (Node2 w x)| into the value |Node3 t (Node2 v u) (Node2 w' x)|. %
The |tree23toC| function converts a |Tree23| into a |Tree23C| in the canonical way.}
 \label{fig:patch-example}
\end{figure}

\begin{myhs}
\begin{code}
type Patch23 = Tree23C (Change23 MetaVar)
\end{code}
\end{myhs}

\Cref{fig:patch-example} illustrates a value of type |Patch23| with the
\emph{changes} are shown with a shade in the background, placed always in the
leaves of the spine. Note that the changes encompass only the minimum
number of constructor necessary to \emph{bind and use} all
metavariables. This keeps changes small and isolated. 

  On this section we will discuss how to take the results of
|changeTree23| and transform them into a |Patch23|. The first step to
compute a patch from a change is identifying its \emph{spine}. That
is, the constructors that are present in both the deletion and
insertion contexts.  We are essentially splitting a big change into
the \emph{greatest common prefix} of the insertion and deletion
contexts and leaving smaller changes on the leaves of this prefix:

\begin{myhs}
\begin{code}
gcp :: Tree23C var -> Tree23C var -> Tree23C (Change23 var)
gcp LeafC              LeafC              = LeafC
gcp (Node2C a1 b1)     (Node2C a2 b2)     = Node2C (gcp a1 a2) (gcp b1 b2)
gcp (Node3C a1 b1 c1)  (Node3C a1 b2 c2)  = Node3C (gcp a1 a2) (gcp b1 b2) (gcp c1 c2)
gcp a                  b                  = Hole (a , b)
\end{code}
\end{myhs}

  In the last case of the |gcp| function either |a| and |b|
are both holes, and should be kept as such since we cannot do anything
for the function is polymorphic in |var|, or the constructor disagrees
and hence they do \emph{not} belong in the common prefix.

  One might be tempted to take the results of |changeTree23C|, pipe
them into the |gcp| function and be done with it.  Yet, the
\emph{greatest common prefix} consumes all the possible constructors
leading to disagreeing parts of the contexts where this might be too greedy
We must be careful not to break bindings as shown below:

%\begin{figure}
\begin{minipage}[t]{.55\textwidth}
\begin{myhs}
\begin{code}
-- prob = changeTree23 (Node2 t t) (Node2 x t)
prob  :: Change23 MetaVar
prob  =  Change  (  Node2C (Hole 0)  (Hole 0)
                 ,  Node2C x         (Hole 0))
\end{code}
\end{myhs}
\end{minipage} %
\begin{minipage}[t]{.35\textwidth}
\[ |gcp prob ==| \hspace{6em} \]
\includegraphics[scale=0.3]{src/img/patch-02.pdf}
\end{minipage}
% \caption{How |gcp| breaks binding. The triangle represents a |Tree23C| with no holes.}
% \label{fig:patch-scoping-problem}
% \end{figure}

  One could think of writing a more specific version of |gcp|
that is aware of metavariables, but that is not the best solution. Besides
having a complicated implementation, the |gcp| function is used in different
places. Instead, we postprocess the results of |gcp| and pull
the changes up the tree until they are all closed again, that is, the set of
variables in both contexts is identical. We call this process the \emph{closure}
of a patch and declare a function to compute that below.

  Take the illustration of |closure| in
\Cref{fig:closure}, note that in both the input and
output for the |closure| function the subtree |x| appears on the
deletion context. Moreover, the |closure| functions pushes down only
the necessary amount of constructors into the \emph{changes}.

\begin{figure}
\includegraphics[scale=0.3]{src/img/patch-03.pdf}
\caption{Graphical representation of the |closure| function.}
\label{fig:closure}
\end{figure}

\begin{myhs}
\begin{code}
closure :: Tree23C (Change23 MetaVar) -> Patch23
\end{code}
\end{myhs}

  Although the |closure| function is declared as total, it might fail
if there exists no way of closing all the changes. This is not a
problem for us since we know that |changeTree23| outputs a single,
closed, change. Therefore, there exists a way of closing it. We will
come back to the |closure| function in more detail on its generic
incarnation (\Cref{sec:representing-changes}). For now, it is more
important to understand why we need to compute the closures and see
how it fits as the last part in our algorithm: As soon as every change
within the spine has been closed, we have a \emph{patch}. The final
differencing function for |Tree23| is then defined as:

\begin{myhs}
\begin{code}
diffTree23 :: Tree23 -> Tree23 -> Patch23
diffTree23 s d = closure $$ gcp $$ changeTree23 s d
\end{code}
\end{myhs}
 
  Opposed to |applyChange23|, one could define the |applyPatch23| 
function that applies a \emph{patch}. This is done by traversing
the object tree and the spine of the patch until a change is
found and applying that change to the \emph{local} subtree in question.
Besides a having a localized application function, this representation
with minimized changes enables us to trivially identify when two patches
are working over disjoint parts of a tree. This will be specially interesting
in the context of \emph{merging} (\Cref{sec:merging}).

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

 In \Cref{sec:concrete-changes} we provided a simple algorithm to
solve the differencing problem for 2-3-trees. We began by creating the
type of contexts over |Tree23|, which consisted in annotating a
|Tree23| with a \emph{metavariable} constructor. Later, assuming the
existence of an oracle that answers whether an arbitrary tree is a
subtree of the source and the destination we described how to
construct a value of type |Change23 MetaVar| from a |Tree23|. 
Finally, we described how to compute a |Patch23| given a |Change23|
by \emph{minimizing} the changes and isolating
them from the \emph{spine}. On this section we show how can
we write that same algorithm in a generic fashion, working
over any mutually recursive family.


\subsection{Background on Generic Programming}
\label{sec:generic-prog}

  Firstly, let us briefly review the
\texttt{generics-mrsop}~\cite{Miraldo2018} library, that we will use
to give a generic version of our algorithm.  This library follows the
\emph{sums-of-products} school of generic
programming~\cite{deVries2014} and, additionally, enables us to work
with mutually recursive families. This is important as the abstract
syntax trees of most programming languages are mutually recursive.

  Take the |Tree23| type from
\Cref{sec:concrete-changes}.  Its structure can be seen in a
\emph{sum-of-products} fashion through the |Tree23SOP| type given
below.  It represents the shape in which every
|Tree23| comes and consists in two nested lists of
\emph{atoms}. The outer list represents the choice of constructor, and
packages the \emph{sum} part of the datatype whereas the inner list
represents the \emph{product} of the fields of a given
constructor. The |P| notation represents a value that
has been promoted to the type level~\cite{Yorgey2012}. 

\begin{myhs}
\begin{code}
type Tree23SOP = P  ([  P [] 
                    ,   P ([ I 0 , I 0 ]) 
                    ,   P ([ I 0 , I 0 , I 0 ]) ])
\end{code}
\end{myhs}

  The atoms, in this case only |I 0|, represent a recursive position
referencing the first type in the family. In fact, a mutually
recursive family is described by \emph{a list of sums-of-products}:
one for each element in the family. We overload the word ``code'' in
singular or plural to mean the representation of a datatype, or the
representation of a family, respectively.  The context should make
clear the distinction. For example, |Tree23SOP| is the code of type
|Tree23| and |Tree23Codes| is the codes for the mutually recursive
family.

\begin{myhs}
\begin{code}
type Tree23Codes = P  [ Tree23SOP ]
\end{code}
\end{myhs}

 The \texttt{generics-mrsop} uses the type |Atom|
to distinguish whether a field is a recursive position referencing the
$n$-th type in the family, |I n|, or a opaque type, for example, |Int|
or |Bool|, which are represented by |K KInt|, |K KBool|.

  Let us now take a mutually recursive family with more than one
element and see how it is represented within the \texttt{generics-mrsop}
framework. The mutually recursive family containing types |Zig| and |Zag| has
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
type ZigCodes = P  [ P [ P [ K KInt ]   , P [ I 1 ] ]
                   , P [ P [ K KBool ]  , P [ I 0 ] ]
                   ]
\end{code}
\end{myhs}
\end{minipage} %

  Note that the codes come in the same order as the elements of the
family. The code for |Zig| is the first element of the |ZigCodes| type
level list. It consists in two lists, since |Zig| has two
constructors. One receives a value of type |Int|, the other consists
in a recursive call to the second element of the family. The code acts
as a recipe that the \emph{representation} functor must follow in
order to interpret those into a type of kind |Star|.

  The representation is defined by the means of $n$-ary sums (|NS|)
and products (|NP|) that work by induction on the \emph{codes} and one
interpretation for atoms (|NA|). Their definition together with
their respective elimination principles can be found in \Cref{fig:nsnpna}.

\begin{figure}
\begin{minipage}[t]{.5\textwidth}
\begin{myhs}
\begin{code}
data NS :: (k -> Star) -> [k] -> Star where
  Here   :: f x      -> NS f (x PCons xs)
  There  :: NS f xs  -> NS f (x PCons xs)
\end{code}
\end{myhs}
\begin{myhs}
\begin{code}
data NP :: (k -> Star) -> [k] -> Star where
  Nil   :: NP f (P [])
  Cons  :: f x -> NP f xs -> NP f (x PCons xs)
\end{code}
\end{myhs}
\begin{myhs}
\begin{code}
data NA :: (Nat -> Star) -> Atom -> Star where
  NA_I :: phi i  -> NA phi (I i)
  NA_K :: Opq k  -> NA phi (K k)
\end{code}
\end{myhs}
\end{minipage} %
\begin{minipage}[t]{.45\textwidth}
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
elimNP f Nil          = []
elimNP f (Cons x xs)  = f x : elimNP f xs
\end{code}
\end{myhs}
\begin{myhs}
\begin{code}
elimNA  ::  (forall ix dot f x -> a) -> (forall k dot g k -> a) 
        ->  NA f g at -> a
elimNA f g (NA_I x)  = f x
elimNA f g (NA_K x)  = g x
\end{code}
\end{myhs}
\end{minipage}
\caption{Interpretation and elimination principles for each component of a sum-of-products code.}
\label{fig:nsnpna}
\end{figure}


  The |NS| type is responsible for determining the choice of
constructor whereas the |NP| applies a representation functor to all
the fields of the selected constructor.  Finally, |NA| distinguishes
between representation of a recursive position from an opaque
type. Although the \texttt{generics-mrsop} provides a way to customize
the set of opaque types used, this is not central do the developments
in this paper and hence we will assume a type |Opq| that interprets
the necessary atom types, i.e., |Int|, |Bool|, etc. We refer the
interested reader to the original paper~\cite{Miraldo2018} for more
information. Nevertheless, we define the representation functor |Rep|
as the composition of the interpretations of the different pieces:

\begin{myhs}
\begin{code}
type Rep phi = NS (NP (NA phi))
\end{code}
\end{myhs}

  Finally, we tie the recursive knot with a functor of kind |Nat -> Star| that is
passed as a parameter to |NA| in order to interpret the recursive positions. The
familiar reader might recognize it as the indexed least fixpoint:

\begin{myhs}
\begin{code}
newtype Fix (codes :: P [ P [ P [ Atom ] ] ]) (ix :: Nat)
  = Fix { unFix :: Rep (Fix codes) (Lkup codes ix) }
\end{code}
\end{myhs}

  Here, |Lkup codes ix| denotes the type level lookup of the element
with index |ix| within the list |codes|. This type family throws a
type error if the index is out of bounds.  The generic versions of the
constructors of type |Zig| are given by:

\begin{myhs}
\begin{code}
gzig :: Int -> Fix ZigCodes 0
gzig n = Fix (Here (Cons (NA_K (OpqInt n)) Nil))

gzigzag :: Fix ZigCodes 1 -> Fix ZigCodes 0
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

  The |Constr sum c| type represents a predicate indicating that |c|
is a valid constructor for |sum|, that is, it is a valid index into the
type level list |sum|. This enables us to define a |View| over a value
of a sum type to be a choice of constructor and corresponding
product. We can then unwrap a |Fix codes i| value into its topmost
constructor and a product of its fields with the |sop| function.

\begin{myhs}
\begin{code}
data View :: (Nat -> Star) -> P [ P [ Atom ] ] -> Star where
  Tag :: Constr sum c -> NP (NA phi) (Lkup c sum) -> View phi sum

sop :: Fix codes i -> View (Fix codes) (Lkup i codes)
\end{code}
\end{myhs}

This brief introduction covers the basics of generic programming in Haskell
that we will use in this paper. We refer the interested reader to the
literature~\cite{deVries2014,Miraldo2018} for more information.

\subsection{Representing and Computing Changes, Generically}
\label{sec:representing-changes}

  
  In \Cref{sec:concrete-changes} we gained some intuition about the
workings of our algorithm whereas in \Cref{sec:generic-prog} we
discussed techniques for writing programs over arbitrary mutually
recursive families. In this section we write our differencing algorithm
in a fully generic fashion.

  We start defining the generic notion of context, called |Tx|.
Analogously to |Tree23C| (\Cref{sec:concrete-changes}), |Tx| enables
us to augment mutually recursive family with type holes.  This type
construction is crucial to the representation of patches.  This
construction can be done for any mutually recursive family.

  We can read |Tx codes phi at| as the element of the
mutually recursive family |codes| indexed by |at| augmented with holes
of type |phi|. Its definition follows:

\begin{myhs}
\begin{code}
data Tx :: [[[Atom]]] -> (Atom -> Star) -> Atom -> Star where
  TxHole  :: phi at  -> Tx codes phi at
  TxOpq   :: Opq k   -> Tx codes phi (K k)
  TxPeel  :: Constr (Lkup i codes) c
          -> NP (Tx codes phi) (Lkup (Lkup i codes) c)
          -> Tx codes phi (I i)
\end{code}
\end{myhs}

  Looking at the definition of |Tx|, we see that its values
consist in either a \emph{typed} hole, some opaque value, or
a constructor and a product of fields. The |TxPeel| follows
very closely the |View| type from \Cref{sec:generic-prog}. 
The |Tx| type is, in fact, the indexed free monad over
the |Rep|. The return method is just |TxHole|, and the multiplication
is given by: 

\begin{myhs}
\begin{code}
txJoin :: Tx codes (Tx codes phi) at -> Tx codes phi at
txJoin (TxHole tx)   = tx
txJoin (TxOpq opq)   = TxOpq opq
txJoin (TxPeel c d)  = TxPeel c (mapNP txJoin p)
\end{code}
\end{myhs}

  Essentially, a value of type |Tx codes phi at| is
a value of type |NA (Fix codes) at| augmented with \emph{holes} of
type |phi|. To illustrate this, let us define the injection of a |NA|
into a |Tx|:

\begin{myhs}
\begin{code}
na2tx :: NA (Fix codes) at -> Tx codes phi at
na2tx (NA_K k)        = TxOpq k
na2tx (NA_I (Fix x))  = case sop x of Tag c p -> TxPeel c (mapNP na2tx p) 
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

\paragraph{Generic Representation of Changes}

  With a generic notion of contexts, we can go ahead and define our
generic |Change| type.  We use a pair of |Tx| exactly as in
\Cref{sec:concrete-changes}: one deletion context and one insertion
context.  This time, however, we define a new datatype to be able to
partially apply its type arguments later on.

\begin{myhs}
\begin{code}
data Change codes phi at = Change (Tx codes phi at) (Tx codes phi at)
\end{code}
\end{myhs}

  The interpretation for the metavariables, |MetaVar|, now carries the
integer representing the metavariable itself but also carries
information to identify whether this metavariable is supposed to be
instantiated by a recursive member of the family or a opaque type. We
do so by carrying a singleton~\cite{Eisenberg2012} of type |NA|.
This enables the compiler to gain knowledge over |at| when
pattern-matching, which is important purely from the generic programming perspective.
Without this information we would not be able to write a well-typed
application function, for instance. We must know the types of
the values supposed to be matched against a metavariable to ensure we
will produce well-typed trees.

\begin{myhs}
\begin{code}
data MetaVar at = MetaVar Int (NA (Const Unit) at)
\end{code}
\end{myhs}

  The type of changes over |Tree23| can now be written using the
generic representation for changes and metavariables. 

\begin{myhs}
\begin{code}
type ChangeTree23 = Change Tree23Codes MetaVar (I 0)
\end{code}
\end{myhs}

  We can read the type above as the type of changes over the
\emph{zero}-th (|I 0|) type within the mutually recursive family |Tree23Codes|
with values of type |MetaVar| in its holes.

\paragraph{Computing Changes} Computing a
|Change codes MetaVar| from a source and a destination elements of
type |Fix codes ix| follows exactly the road map from \Cref{sec:concrete-changes}:
extract the contexts and fix bindings by removing \emph{false copies}.
We are still assuming an efficient
oracle |buildOracle s d :: Oracle codes|, for answering whether \emph{an arbitrary |t| is a
subtree of a fixed |s| and |d| indexed by |n|}, where:

\begin{myhs}
\begin{code}
type Oracle codes = forall j dot Fix codes j -> Maybe Int

buildOracle :: Fix codes i -> Fix codes i -> Oracle codes
\end{code}
\end{myhs}

  The core of computing a change is in the extraction of the deletion
and insertion contexts (|extract| function,
\Cref{sec:concrete-changes}).  We must care for an important
correctness issue , though. When a tree is both a subtree of the
source and destination but also occurs as the subtree of another
common subtree (\Cref{fig:problematic-ics}) care must be taken before
issuing a copy. We shown how to fix this with a postprocessing step of
the resulting change.  That is still the case, but we now maintain
some extra information from the context extraction step to make the
postprocessing a self contained function.

  Looking at the type of |Oracle|, we see it will only share recursive
positions by construction. We use the |ForceI| type to bring
this fact on the type level. That is, we are only sharing
\emph{recursive} positions so far. We also use the indexed product
type |(:*:)| to carry along information.

\begin{myhs}
\begin{code}
data (:*:) f g x = f x :*: g x

data ForceI :: (Nat -> Star) -> Atom -> Star where
  ForceI :: f i -> ForceI f (I i)
\end{code}
\end{myhs}

  Defining the generic |txExtract| function is simple. We check whether a given
|x| is a subtree of the fixed source and destinations by calling the
provided oracle, if so, we return a hole with the subtree annotated If
|x| is not a common subtree we extract the topmost constructor and its
fields then map |TxOpq| on the opaque fields and continue extracting
the context on the fields that reference recursive positions.

\begin{myhs}
\begin{code}
txExtract  ::  Oracle codes
           ->  Fix codes ix 
           ->  Tx codes (ForceI (Const Int :*: Fix codes)) (I ix)
txExtract ics x = case ics x of
    Just i   -> TxHole (ForceI (Const i :*: x))
    Nothing  ->  let Tag c p = sop (unFix x)
                 in TxPeel c (mapNP (elimNA TxOpq (txExtract ics)) p)
\end{code}
\end{myhs}

  Postprocessing works by traversing the result of the extracted
contexts.  In case we need to keep a given tree and forget that it was
shared we convert it to a context with |na2tx|.  Recall the reason for
wanting to keep only the metavariables that occur in both the
insertion and deletion contexts is to prevent any \texttt{undefined
variable} when applying our patches, which would break
correctness. More technically, the |txPostprocess| function groups the
metavariables of each context in a set and computes the intersection
of such sets, then maps over its arguments replacing the |Const Int
:*: Fix codes| hole by either |Const Int|, if the |Int| belongs in the
set, or by translating the |Fix codes| with |na2tx . NA_I|. The implementation
is shown in \Cref{fig:postprocess}.

\begin{figure}
\begin{myhs}
\begin{code}
txPostprocess  ::  Tx codes (ForceI (Const Int :*: Fix codes)) (I ix)
               ->  Tx codes (ForceI (Const Int :*: Fix codes)) (I ix)
               ->  Change (ForceI (Const Int)) (I ix)
txPostprocess del ins =
  -- We have to txJoin the results since keepOrDrop returns a Tx
  execState  (Change  <$$> (txJoin <$$> utxMapM keepOrDrop del) 
                      <*> (txJoin <$$> utxMapM keepOrDrop ins))
             (varsOf del `intersect` varsOf ins)
 where
   -- traverses a Tx and puts all the variables in a Set.
   varsOf  :: Tx codes (ForceI (Const Int :*: Fix codes)) (I ix) -> Set Int

   -- check whether a variable is in both contexts and decides
   keepOrDrop (ForceI (Const mvar) :*: subtree) = do
     okvars <- get
     if var `elem` okvars  then return (TxHole (ForceI (Const mvar)))
                           else return (na2tx (NA_I subtree))
\end{code}
\end{myhs}
\caption{Post processing of contexts returning closed changes}
\label{fig:postprocess}
\end{figure}

  At this point, given two trees |a| and |b| of type |Fix codes ix|,
we can extract and post-processed both the deletion and insertion
contexts, of type |Tx codes (ForceI (Const Int)) (I ix)|. These are
just like a value of type |Fix codes ix| with holes of type |Const
Int| exclusively in recursive positions. This is the generic version
of the |changeTree23| function presented in
\Cref{sec:concrete-changes}:

\begin{myhs}
\begin{code}
change :: Fix codes ix -> Fix codes ix -> Change codes (ForceI (Const Int)) (I ix)
change x y =  let  ics = buildOracle x y
              in txPostprocess (txExtract ics x) (txExtract ics y)
\end{code}
\end{myhs}

  Recall that this function will only produce closed changes. That is,
a deletion and a insertion context that have the same set of
variables. Intuitively, this means that every variable that is
declared is used and vice-versa.

\paragraph{Minimizing the Changes: Computing Patches}

  The next step is to to minimize the changes coming from |change|
function, yielding a \emph{patch}. The generic counterpart of
|Patch23| from \Cref{sec:concrete-changes} is given by:

\begin{myhs}
\begin{code}
type Patch codes at = Tx codes (Change codes MetaVar) at
\end{code}
\end{myhs}

  Firstly, we have to identify the \emph{spine}, that is, the
constructors that are present in both the deletion and insertion
contexts. This is done by splitting a big change into the
\emph{greatest common prefix} of the insertion and deletion contexts
and the smaller changes inside:

\begin{myhs}
\begin{code}
txGCP :: Tx codes phi at -> Tx codes psi at -> Tx codes (Tx codes phi :*: Tx codes psi) at
txGCP (TxOpq x) (TxOpq y) 
  | x == y     = TxOpq x
  | otherwise  = TxHole (TxOpq x :*: TxOpq y)
txGCP (TxPeel cx px) (TxPeel cy py)
  = case testEquality cx px of
      Nothing   -> TxHole (TxPeel cx px :*: TxPeel cy py)
      Jus Refl  -> TxPeel cx (mapNP (uncurry' txGCP) (zipNP px py))
txGCP a b = TxHole (a :*: b)
\end{code}
\end{myhs}

  The |txGCP| can is just like a generalized |zip| function, but
instead of stopping whenever one of its arguments has been consumed
and forgetting the other, it stores the rest of the other argument.
It is \emph{greatest} in the sense that it consumes as many
constructors as possible and resorts to |TxHole| when it cannot
progress further.

  We know, from \Cref{sec:concrete-changes} that we cannot simply take
the result of |change|, compute its \emph{greatest common prefix} and
be done with it. This would yield a patch with potentially malformed
changes. The |txGCD| function is not aware of metavariables
and might break their scoping (\Cref{fig:patch-scoping-problem}). 
 
  Refining the result of |txGCP| is conceptually simple. All we have
to do is bubble up the changes to a point where they are all \emph{closed},
\Cref{fig:patch-scoping-problem}.  We start by creating some machinery
to distinguish the open changes from the closed changes in the result
of a |txGCP|. Then we define a traversal that shall look at those tags
and decide whether more constructors should be pushed into the changes
or not. This is done by the |closure| function.

  Tagging open and closed changes is done with the indexed sum type.
We use |InL| to mark the \emph{open} changes and |InR| for the \emph{closed} changes.

\begin{myhs}
\begin{code}
data Sum f g x = InL (f x) | InR (g x)

either' :: (f x -> r x) -> (g x -> r x) -> Sum f g x -> r x
either' a b (InL fx) = a fx
either' a b (InR gx) = b gx
\end{code}
\end{myhs}

  The |isClosed| predicate is responsible for deciding how to
tag a change.

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
predicate over an arbitrary patch |p|:

\begin{myhs}
\begin{code}
txMap isClosed p :: Tx codes (Sum (Change codes) (Change codes)) at
\end{code} 
\end{myhs}

  The final |closure| function is defined with an auxiliary function,
|closure'|. This auxiliary function receives a patch with tagged
changes and tries to eliminate all the \emph{open changes}, tagged
with |InL|. We do so by finding the smallest closed change that binds
the required variables. If the |closure'| function cannot find the
constructor that binds all variables, it tags the patch as an
\emph{open change} altogether. The first three cases are trivial:

\begin{myhs}
\begin{code}
closure'  ::  Tx codes (Sum (Change codes) (Change codes)) at
          ->  Sum (Change codes) (Tx codes (Change codes)) at
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
we must massage some data. This is akin to a simple distributive
law for |Tx|, defined below.

\begin{myhs}
\begin{code}
distr :: Tx codes (Change codes phi) at -> Change codes phi at
distr spine = Change  (txJoin (txMap chgDel spine)) 
                      (txJoin (txMap chgIns spine))
\end{code}
\end{myhs}

  The difference between |distr| and the |Nothing| clause in |closure'|
is that in the later we are handling |NP (Tx codes (Change codes phi))|, i.e.,
a sequence of |Tx| instead of a single one. Consequently, we need some more code.

\begin{myhs}
\begin{code}
closure' (TxPeel cx px) 
  = let aux = mapNP closure' px
     in case mapNPM fromInR aux of
       Just np  -> InR (TxPeel cx np) -- everything is closed.
       -- some changes are open. Try pushing cx down the changes in px and
       -- see if this closes them, then.
       Nothing  -> let  chgs = mapNP (either' InL (InR . distr)) aux
                        dels = mapNP (either' chgDel chgDel) chgs
                        inss = mapNP (either' chgIns chgIns) chgs
                        tmp  = Change (TxPeel cx dels) (TxPeel cx inss)
                    in if isClosed tmp
                       then InR (TxHole tmp)
                       else InL (Change tmp)
\end{code}
\end{myhs}

  In the code above, |aux| is a sequence of either open changes
or patches. The local |dels| and |inss| are defined as the
a sequence deletion and insertion contexts from |aux|, regardless
if they come from open or closed changes. This allows us to
assemble a new, larger, change (|tmp|). Finally, we check whether
this larger change is closed or not. We recall the illustration in
\Cref{fig:closure}, repeated below, for a graphical
intuition.

{\centering
\medskip
\includegraphics[scale=0.3]{src/img/patch-03.pdf}
\bigskip
\par}

  To finish it up, we wrap |closure'| within a larger function that
always returns a |Tx| with all changes being \emph{closed}.  The
necessary observation is that if we pass a given |tx| to |closure'|
such that |distr tx| is closed, then |closure'| will always return a
|InR| value. In our case, the |txPostprocess| is in place precisely 
to provided that guarantee, hence, the |error| is unreachable.

\begin{myhs}
\begin{code}
closure  ::  Tx codes (Sum (Change codes) (Change codes)) at
         ->  Patch codes at
closure  = either' (const $$ error "no closure exists") id
\end{code} %%
\end{myhs}

  The final |diff| function is then assembled by using the closure of
the greatest common prefix of the change the comes from the |change|
function.  In order to further enlarge the domain of our patches 
we add a small additional step where we replace the opaque values
in the spine for copies.

\begin{myhs}
\begin{code}
diff :: Fix codes ix -> Fix codes ix -> Patch codes (I ix)
diff x y =  let Change del ins = change x y 
            in closure  $$  txRefine TxHole mkCpy 
                        $$  txMap isClosed 
                        $$  txGCP del ins
\end{code}
\end{myhs}

  The |txRefine| simply traverses the |Tx| and refines the
holes and opaques into |Tx|s using the provided functions. 
In our case we leave the holes unchanged and replace the
occurrences of |TxOpq| by a new \emph{copy} change. 

\begin{myhs}
\begin{code}
txRefine  ::  (forall at  dot f at   -> Tx codes g at) 
          ->  (forall k   dot Opq k  -> Tx codes g (K k)) 
          ->  Tx codes f at -> Tx codes g at
\end{code}
\end{myhs}

\paragraph{Applying Patches}

  Patch application follows closely the scheme sketched in
for 2-3-trees (\Cref{sec:concrete-changes}). There is one main
difference, though. Our changes are now placed in the leaves of our spine
and can be applied locally.

  Our final |applyChange| will be responsible for receiving a change
and a tree and instantiate the metavariables by matching the tree
against the deletion context then substituting this valuation
in the insertion context. Its type is given by:

\begin{myhs}
\begin{code}
applyChange  ::  Change codes MetaVar at 
             ->  NA (Fix codes) at 
             ->  Maybe (NA (Fix codes) at)
\end{code}
\end{myhs}

  We are now left to match the spine with a value of |NA (Fix codes)|.  
and leave the changes paired up with the corresponding local elements
they must be applied to. This is similar to the |txGCP|, and can be implemented
by it. We must extract the greatest common prefix of the spine and the
|Tx| that comes from translating the |NA (Fix codes)| value but must make
sure that the leaves have all |TxHole|s on the left. 

\begin{myhs}
\begin{code}
txZipEl :: Tx codes phi at -> NA (Fix codes) at -> Maybe (Tx codes (phi :*: NA (Fix codes)))
txZipEl tx el = txMapM (uncurry' checkIsHole) $$ txGCP tx (tx2na el)
  where
    checkIsHole :: Tx codes phi at -> Tx codes psi at -> Maybe (phi :*: NA (Fix codes) at)
    checkIsHole (TxHole phi)  el  = (phi :*:) <$$> na2tx el
    checkIsHole _             _   = Nothing
\end{code} %
\end{myhs}

  Finally, we define our application function. First we check whether
the spine matches the element. If that is the case, we apply the changes,
which are already paired with the parts of the element they must be applied to:

\begin{myhs}
\begin{code}
apply :: Patch codes ix -> Fix codes ix -> Maybe (Fix codes ix)
apply patch el = txZipEl patch el >>= return . txMapM (uncurry' applyChange)
\end{code}
\end{myhs}

  Whenever a patch |p| can be applied to an element |x|, that is,
|apply p x| returns |Just y| for some |y|, we say that |p| is \emph{applicable}
to |x|.

\section{Defining the Oracle}
\label{sec:oracle}

  In the previous sections we have implemented a generic diffing
algorithm assuming the existence of a function, called \emph{an
oracle}, that answers whether a given subtree should be copied or
not. We have seen that the overall performance of our algorithm depends
on answering that question efficiently: we perform one such query per
constructor in the source and destination of the diff. In this section
we provide an efficient construction for this oracle.  Yet, it is
worthwhile to define the inefficient, naive version, first. Besides
providing important intuition to what this function is doing it is an
interesting generic programming exercise in its own.

  When deciding whether a given tree |x| is a subtree of two
fixed trees |s| and |d|, a naive oracle would check every
single subtree of |s| and |d| for equality against |x|.  Upon finding
a match, it would return the index of such subtree in the list of all
subtrees. We enumerate all possible subtrees in a list with
the help of |Exists| since the trees might have different indices.

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
through the list of all possible subtrees for a match. The comparison
function starts by comparing the indexes of the |Fix codes| values
wrapped within |Ex| with |testEquality|. If they agree, we pattern
match on |Refl|, which in turn allows us to compare the values for
propositional equality.

\begin{myhs}
\begin{code}
heqFix :: Exists (Fix codes) -> Exists (Fix codes) -> Bool
heqFix (Ex x) (Ex y) = case testEquality x y of
                         Nothing    -> False
                         Just Refl  -> x == y
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

idx :: (a -> Bool) -> [a] -> Maybe Int
idx f  []     = Nothing
idx f  (x:xs) = if f x then Just 0 else (1+) <$$> idx f xs

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
approach and cannot be avoided. We then proceed to compare a
third tree, |t|, for equality with every subtree in the 
lists of subtrees. The performance of this operation can be significantly improved.

  In order to compare trees for equality in constant time we can
annotate them with cryptographic hashes~\cite{Menezes1997} and compare
these hashes instead. This technique transforms our trees into
\emph{merkle trees}~\cite{Merkle1988} and is more commonly seen in the
security and authentication context~\cite{Miller2014,Miraldo2018HAMM}.
Our generic programming machinery that is already at our disposal
enables us to create \emph{merkle trees} generically quite easily.
The \texttt{generics-mrsop} provide some attribute
grammar~\cite{Knuth1990} mechanisms, in particular computation of synthesized
attributes.  The |synthesize| function is just like a catamorphism, but
we annotate the trees with the result of calling a catamorphism instead
of forgetting them. These mechanisms enables us to decorate each node of
a |Fix codes| with a unique identifier (\ref{fig:merkelized-tree}) 
by running the |prepare| function, defined below.

\begin{myhs}
\begin{code}
newtype AnnFix x codes i = AnnFix (x i , Rep (AnnFix x codes) (Lkup i codes))

prepare :: Fix codes i -> AnnFix (Const Digest) codes i
prepare = synthesize authAlgebra
\end{code}
\end{myhs}

\begin{figure}
\includegraphics[scale=0.4]{src/img/merkle-tree.pdf}
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

  We must append the index of the type in question, in this case
|getSNat (TApp iy)|, to our hash computation to differentiate
constructors of different types in the family represented by the same
number.  

  Once we have a tree fully annotated with the hashes for its
subtrees, we store them in a search-efficient structure.  Given
that a hash is just a |[Word]|, the optimal choice is a
|Trie|~\cite{Brass2008} from |Word| to |Int|, where the |Int|
indicates what is the \emph{identifier} of the tree.
Looking up whether a tree |x| is a subtree of two fixed trees |s| and |d|
is then merely looking up |x|'s topmost hash of |x|, also called the \emph{merkle root},
against the intersection of the tries generated from |s| and |d|.
This is a very fast operation and hardly depends on the number
of elements in the trie. In fact, this lookup runs in amortized constant time.
%% The depth of our trie is always |4| or |8| for a |sha256| hash can be
%% be put in that number of machine words, depending on the architecture.
%% Assume we have a 32-bit |Word|, this means that the complexity of the
%% overall lookup is $\bigO{ \log{} n_1 \times \cdots \times \log{} n_8
%% }$, where $n_i$ indicates how many elements are in each level. Take $m
%% = max(n_1 , \cdots, n_8)$ and we have that the complexity of our
%% lookup is $\bigO{ \log{} m }$. Since we can have at most 256 elements
%% per layer, the complexity of the lookup is bound by $ \bigO{ \log{}
%% 256 } \equiv \bigO{ 1 } $. 


  It is of paramount importance to avoid recomputing the merkle root
of a tree |x| every time we wish to know whether it is a common
subtree.  Otherwise, we still end up with an exponential
algorithm. The solution is quite simple: we use |AnnFix (Const Digest)
codes| in the |txExtract| function and the type of our oracle, where
|Fix codes| was used before.  This provides access to the merkle root
in constant time. After this small modification to our |Oracle|,
allowing it to receive trees annotated with hashes we proceed to
define the efficient |buildOracle| function.

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
This is not an issue if we take an |intersect| function with type |Trie k v -> Trie k t -> Trie k v|,
hence, keeping only the assignments from the first trie such that the key is
also an element of the second.

  We can easily get around hash collisions by computing an intermediate
|Trie| from |Word| to |Exists (Fix codes)| in the |mkSharingTrie| function and every time
we find a potential collision we check the trees for equality.
If equality check fails, a hash collision is found and the entry would be
removed from the map. When using a cryptographic hash, the chance of
collision is negligible and we chose to ignore it.

\section{Merging Patches}
\label{sec:merging}

  One of the main motivations for generic structure-aware diffing is
being able to merge patches in a more automatic fashion than using
\texttt{diff3}.  In the past, structural merging has proven to be a
difficult task~\cite{Vassena2016,Miraldo2017} even for trivial cases,
due to how the authors chose to represent patches.  In this section
shows how our new structure for representing changes enables us to
write better merging algorithms.  We write a merging algorithm capable
of merging disjoint patches, that is, patches that work on disjoints
locations of a tree. We evaluate this algorithm in
\Cref{sec:experiments}.

  The merging problem, illustrated in \Cref{fig:merge-square}, is the
problem of computing |q // p| given two patches |p| and |q|. It
consists in a patch that contains the changes of |q| potentially
adapted to work on a value that has already been modified by |p|.
This is sometimes called the \emph{transport} of |q| over |p| or
the \emph{residual}~\cite{Huet1994} of |p| and |q|. 

\begin{figure}[t]
\begin{displaymath}
\xymatrix{ & o \ar[dl]_{p} \ar[dr]^{q} & \\
          a \ar[dr]_{|q // p|} & & b \ar[dl]^{|p // q|} \\
            & c &}
\end{displaymath}
\caption{Merge square}
\label{fig:merge-square}
\end{figure}

  There is a class of patches that are trivial to merge: those that
work on separate locations of a tree. If |p| and |q| are disjoint, then
|p // q| can return |p| without further adaptations. Our algorithm shall
merge only those cases and mark as a |Conflict| any situation where
the patches are \emph{disjoint}. 

  A |Conflict| is returned whenever the patches are not disjoint. We
define it as a pair of irreconcilable patches. In practice one would
carry a label around to identify the type of conflict for easier
resolution. Note that the location is trivially kept, since the
conflicts will where the patches disagree.

\begin{myhs}
\begin{code}
type Conflict codes = Patch codes :*: Patch codes

type PatchConf codes =  Tx codes (Sum (Conflict codes) (Change codes))
\end{code}
\end{myhs}

  Our merging operator, |(//)|, receives two patches and returns a
patch possibly annotated with conflicts.  We do so by matching the
spines against each other and evaluating with more care the places
where the spines differ.

\begin{myhs}
\begin{code}
(//) :: Patch codes at -> Patch codes at -> PatchConf codes at
\end{code}
\end{myhs} %  

  The intuition here is that |p // q| must preserve the intersection of the
spines of |p| and |q| and reconcile the differences whenever one of
the patches has a change. Note that it is impossible to have
disagreeing spines since |p| and |q| are applicable to at least one
common element.  This is yet another task for the \emph{greatest common
prefix} operator:

\begin{myhs}
\begin{code}
p // q = txMap (uncurry' reconcile) $$ txGCP p q
\end{code}
\end{myhs}

  Here, the |reconcile| function shall check whether the
disagreeing parts are disjoint, i.e., either one of them
performs no changes or they perform the same change. If that is
the case, it returns its first argument. In fact, this is very
much in line with the properties of a residual operator~\cite{Huet1994}.

\begin{myhs}
\begin{code}
reconcile  :: Patch codes at -> Patch codes at -> Sum (Conflict codes) (Change codes) at
reconcile p q
  | patchIden p || patchIden q  = InR $$ distr p
  | patchEquiv p q              = InR $$ copy
  | otherwise                   = InL $$ Conflict p q
\end{code}
\end{myhs}

  The first branch borrows from the two identity laws from residual
theory that state that |p // id == p| and |id // p == id|. This is
fairly intuitive when spoken out loud. Take the first law as an
example, |p // id|, we are adapting a change |p| to work over an object
has been changed by |id|, but this means the object is the same and we
can apply |p| itself. The second law is also captured by the first
conditional clause of |reconcile|. The third residual law on the
other hand, needs its very own clause. It states that |p // p == id|,
meaning that applying a patch over something that has been modified by
this very patch amounts to not changing anything. The |patchIden| functions
checks whether all changes in that patch are copies and |patchEquiv|
checks if two patches are $\alpha$-equivalent.

  Our trivial merge algorithm returns a conflict for non-disjoint
patches, but this does not mean that it is impossible to merge
them. Although a full discussion is out of the scope of this paper,
there are a number of non-disjoint patches that are possible to be
merged.  These non-trivial merges can be divided in two main
situations: (A) no action needed even though patches are not disjoint
and (B) transport of pieces of a patch to different locations in the
three.  In \Cref{fig:merging-AB} we illustrate situations (A) and (B)
in the merge square for two non-disjoint patches.

\begin{figure}
\includegraphics[scale=0.3]{src/img/merge-01.pdf}
\includegraphics[scale=0.3]{src/img/merge-02.pdf}
\caption{Example of a merge square where the first residual is obtained by
not changing the patch and the second is computed by applying a patch
to another patch, transporting the changes.}
\label{fig:merging-AB}
\end{figure}

\section{Experiments}
\label{sec:experiments}

  We have conducted two experiments over a number of 
Lua~\cite{Lua} source files. We obtained these files data by mining the top
Lua repositories on GitHub and extracting all the merge conflicts recorded
in their history. Next, we ran two experiments over this data:
a performance test and a merging test. We chose the Lua programming language
for two reasons. First, there is a Haskell parser for Lua readily available
on Hackage and, secondly, due to a performance bug~\cite{ghc-performance-bug} in GHC
we are not able to compile our code for larger abstract syntax tress
such as C, for example. 

\paragraph{Performance Evaluation} In order to evaluate the
performance of our implementation we have timed the computation of the
two diffs, |diff o a| and |diff o b|, for each merge conflict |a,o,b|
in our dataset.  In order to ensure that the numbers we obtained
are valid and representative of a real execution trace we timed the
execution time of parsing the files and running |length . encode
. uncurry diff| over the parsed files, where |encode| comes from |Data.Serialize|. Besides
ensuring that the patch is fully evaluated, the serialization also
mimics what would happen in a real version control system since the
patch would have to be saved to disk.  After timing approximately 1200
executions from real examples we have plotted the data over the total
number of constructors for each source-destination pair.
In \Cref{fig:performance-plot} we see two plots: on the left
we have plotted 70\% of our dataset in more detail whereas
on the right we show the full plot. The results were expected
given that we seen how |diff x y| runs in $\bigO{n + m}$ where |n| and |m| are the
number of constructors in |x| and |y| abstract syntax trees, respectively.
Confirming our analysis with empirical further strengthens our 
algorithm as a practical implementation of structured differencing.

\paragraph{Merging Evaluation} We have tested the trivial merging
algorithm presented in \Cref{sec:merging} by running it over the merge
conflicts we mined from GitHub. Upon a successful merge from our tool we attempted to
apply the residuals to the respective files and made sure that the merge
square (\Cref{fig:merge-square}) was commuting.
We were able to solve a total of 66 conflicts, amounting to 11\% of
the analyzed conflicts. This means that about one tenth of the conflicts
we analyzed are trivially simple to merge with a tool that looks at 
changes in a more refined way other than looking purely at the lines
in a file. 

\begin{figure}\centering
\ra{1.1} % better spacing
\begin{tabular}{@@{}lllll@@{}}
\toprule
Repository         & Commits & Contributors  & Total Conflicts & Trivial Conflicts \\ 
\midrule
awesome            & 9289    & 250 & 5   & 0  \\
busted             & 936     & 39  & 9   & 0  \\
CorsixTH           & 3207    & 64  & 25  & 8  \\
hawkthorne-journey & 5538    & 61  & 158 & 27 \\
kong               & 4669    & 142 & 163 & 11 \\
koreader           & 6418    & 89  & 14  & 2  \\
luakit             & 4160    & 62  & 28  & 2  \\
luarocks           & 2131    & 51  & 45  & 3  \\
luvit              & 2862    & 68  & 4   & 1  \\
nn                 & 1839    & 177 & 3   & 0  \\
Penlight           & 730     & 46  & 6   & 3  \\
rnn                & 622     & 42  & 6   & 1  \\
snabb              & 8075    & 63  & 94  & 6 \\
tarantool          & 12299   & 82  & 33  & 2  \\
telegram-bot       & 729     & 50  & 5   & 0  \\
\midrule
\multicolumn{3}{r}{total}    & 598 & 66 \\
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
abstract syntax trees, hence ignoring comments and formatting. There would
be no extra effort in handling formatting issues besides writing a custom parser that
records this information. Nevertheless, it is reasonable to expect 
a smaller success rate since we are ignoring formatting changes
altogether. Secondly, a significant number of developers prefer
to rebase their branches instead of merging them. Hence, we might have
missed a number of important merge conflicts. There is no way of
mining these conflicts back since rebasing erases history.

\section{Discussion and Conclusion}
\label{sec:discussion}

  The results from \Cref{sec:experiments} are very encouraging. 
We see that our diffing algorithm has competitive performance 
and our trivial merging operation is  capable of merging
a number of patches that \texttt{diff3} yields conflicts. In order to
leave the research realm and deliver a production tool, there is
still a number of points that must be addressed.

\subsection{Future Work}  

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
respected, for instance. Another option would be consider abstract syntax trees
with explicit binding.

\paragraph{Better Merge Algorithm}
The merging algorithm presented in \Cref{sec:merging} only handles trivial cases.
Being able to handle the non trivial cases is the current topic of research
at the time of writing this paper. We wish to better understand the operation
of merging patches. It seems to share a number of properties from unification theory,
residual systems, rewriting systems and we would like to look into this 
in more detail. This would enable us to better pinpoint the role
that merging plays within our meta-theory, that is, one would expect that it would
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
be achieved by rewriting our code in Agda~\cite{Norell2009} whilst proving
the correctness properties we desire. This process would provide
invaluable insight into developing the meta-theory of our system.

\paragraph{Extending the Generic Universe.}
Our prototype is built on top of \texttt{generics-mrsop}, a generic
programming library for handling mutually recursive families in the
sums of products style. With recent advances in generic
programming~\cite{Serrano2018}, we can think about go a step further
and extend the library to handle mutually recursive families that have
\texttt{GADTs} inside. 

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
et al.~\cite{Miraldo2017}, where the authors defined
operations that work directly on tree shaped data. Using this
approach, changes become easier to merge but harder to compute.
Both bodies of work follow the same general idea as the untyped
variants: compute all possible patches and filter out the bad ones.
As we have already mentioned (\Cref{sec:introduction}), this is not an optimal
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
authors model line-based patches in a categorical fashion. This
inspired the version control system \texttt{pijul}. Swierstra
and L\"{o}h~\cite{Swierstra2014} propose an interesting meta-theory
for version control of structured data based on separation logic to
model disjoint changes. Lastly, Angiuli et al.~\cite{Angiuli2014}
describes a patch theory based on homotopical type theory.
The version control system \texttt{darcs}~\cite{Darcs} also uses
a more formal approach in its meta-theory of patches, but the patches
themselves are still working on the line level, they are not structure aware.

\subsection{Conclusions}
\label{sec:conclusions}

  Throughout this paper we have developed an efficient type-directed 
algorithm for computing structured differences for a whole class of datatypes,
namely, mutually recursive families. This class of types is sufficient
for representing programming languages and, hence, our algorithm can
be readily used to compute differences over a number of abstract
syntax trees out of the box.  We validated our implementation by
computing diffs over Lua~\cite{Lua} source files obtained from various
repositories on GitHub. Finally, we shown how our representation
of changes makes it very easy to merge trivially disjoint patches.
We have also seen that about one tenth of the merge conflicts from
the top Lua repositories on GitHub fall under this ``trivially disjoint''
classification.

  In order to bridge the gap between a theoretical algorithm and
a practical, efficient, implementation we had to borrow techniques from
cryptography and programming languages to define a generic function
that answers whether some value is occurs as a subtree of two values:
a source and a destination.  It is worth to mention that without
a tool with similar capabilities as Haskell, the generic development
would have been impossible. 


%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End: 
