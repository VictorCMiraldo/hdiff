\documentclass[acmsmall,screen]{acmart}%
\settopmatter{}

%%%%%%%%%%%%%%
%%%%%%%%%%%%%%
%% Template 

%% END TEMPLATE
%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%
%
% Our formatting rules and included packages.
%
%include lhs2TeX.fmt
%include src/definitions.lhs
%
%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%

%% Conference information
%% Supplied to authors by publisher for camera-ready submission;
%% use defaults for review submission.
\setcopyright{rightsretained}
\acmPrice{}
\acmDOI{10.1145/3341717}
\acmYear{2019}
\copyrightyear{2019}
\acmJournal{PACMPL}
\acmVolume{3}
\acmNumber{ICFP}
\acmArticle{113}
\acmMonth{8}

%% Conference Publishing Team tells me to put this here
%% to get rid of orphans
\clubpenalty = 10000
\widowpenalty = 10000
\displaywidowpenalty = 10000

\begin{document}

%% Title information
\title{An Efficient Algorithm for Type-Safe Structural Diffing}
%Wouter: How about 'An Efficient Datatype Generic Algorithm for Structural Diffing'
%That makes the generic programming aspect more obvious...

%% Author information
%% Contents and number of authors suppressed with 'anonymous'.
%% Each author should be introduced by \author, followed by
%% \authornote (optional), \orcid (optional), \affiliation, and
%% \email.
%% An author may have multiple affiliations and/or emails; repeat the
%% appropriate command.
%% Many elements are not rendered, but should be provided for metadata
%% extraction tools.

\author{Victor Cacciari Miraldo}
\affiliation{
  \position{PhD candidate}
  \department{Information and Computing Sciences}
  \institution{Utrecht University}
  \streetaddress{Princetonplein, 5}
  \city{Utrecht}
  \state{Utrecht}
  \postcode{3584 CC}
  \country{The Netherlands} 
}
\email{v.cacciarimiraldo@@uu.nl}

\author{Wouter Swierstra}
\affiliation{
  \position{Assistant Professor}
  \department{Information and Computing Sciences}
  \institution{Utrecht University}
  \streetaddress{Princetonplein, 5}
  \city{Utrecht}
  \state{Utrecht}
  \postcode{3584 CC}
  \country{The Netherlands} 
}
\email{w.s.swierstra@@uu.nl}

%% Abstract
%% Note: \begin{abstract}...\end{abstract} environment must come
%% before \maketitle command
\begin{abstract}
Effectively computing the difference between two version of a
source file has become an indispensable part of software development.
The \emph{de facto} standard tool used by most version control systems
is the \texttt{UNIX diff} utility,
that compares two files on a line-by-line basis without any regard for the
\emph{structure} of the data stored in these files.
%
This paper presents an alternative \emph{datatype generic} algorithm
for computing the difference between two values of \emph{any}
algebraic datatype. This algorithm maximizes sharing between the
source and target trees, while still running in linear
time.
%
Finally, this paper demonstrates that by instantiating this algorithm
to the Lua abstract syntax tree and mining the commit history of
repositories found on GitHub, the resulting patches can often be
merged automatically, even when existing technology has failed.
%
\end{abstract}


%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10011007.10011006.10011008</concept_id>
<concept_desc>Software and its engineering~General programming languages</concept_desc>
<concept_significance>500</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~General programming languages}
%% End of generated code


%% Keywords
%% comma separated list
\keywords{Generic Programming, diff, Version Control, Haskell}


%% Bibliography style
\bibliographystyle{acmart/ACM-Reference-Format}
\citestyle{acmauthoryear}  %% For author/year citations


%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle

%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%
%
% Body
%
%include src/body.lhs
%
%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%

%% Acknowledgments
%\begin{acks}                            %% acks environment is optional
                                        %% contents suppressed with 'anonymous'
  %% Commands \grantsponsor{<sponsorID>}{<name>}{<url>} and
  %% \grantnum[<url>]{<sponsorID>}{<number>} should be used to
  %% acknowledge financial support and will be used by metadata
  %% extraction tools.
%  This material is based upon work supported by the
%  \grantsponsor{GS100000001}{National Science
%    Foundation}{http://dx.doi.org/10.13039/100000001} under Grant
%  No.~\grantnum{GS100000001}{nnnnnnn} and Grant
%  No.~\grantnum{GS100000001}{mmmmmmm}.  Any opinions, findings, and
%  conclusions or recommendations expressed in this material are those
%  of the author and do not necessarily reflect the views of the
%  National Science Foundation.
%\end{acks}


%% Bibliography
\bibliography{references}


%% Appendix
%% \appendix
%% \section{Appendix}
%% 
%% %include src/appendix.lhs

\end{document}
