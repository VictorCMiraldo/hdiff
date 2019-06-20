%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Recommended by the ACM ppl
\usepackage{booktabs}
\usepackage{subcaption}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Our packages
\usepackage{xcolor}
\usepackage{tikz}
\usetikzlibrary{shapes}
\usepackage[all]{xy}

%% Cleveref must be the last loaded package
%% since it modifies the cross-ref system.
\usepackage{cleveref}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Our defs

%% Drawing patches using tikz
\newenvironment{twothreetree}{%
\begin{tikzpicture}[%
  sibling distance=3em,
  innernode/.style = {rectangle , draw},
  leafnode/.style = { } ,
  subtree/.style = {regular polygon , regular polygon sides=3 , draw , scale=0.2} ]%
}{%
\end{tikzpicture}%
}

%% More space between rows
\newcommand{\ra}[1]{\renewcommand{\arraystretch}{#1}}

%% Logistic Stuff

\definecolor{C1}{RGB}{0,153,204}
\definecolor{C2}{RGB}{89,0,179}

\newcounter{commentctr}[section]
\setcounter{commentctr}{0}
\renewcommand{\thecommentctr}{%
\arabic{section}.\arabic{commentctr}}

\newcommand{\warnme}[1]{%
{\color{red} \textbf{$[$} #1 \textbf{$]$}}}

\newcommand{\TODO}[1]{%
{\color{purple} \textbf{$[$ TODO: } #1 \textbf{$]$}}}

\newcommand{\tmp}[1]{%
{\color{gray} \textit{#1} }}

\newenvironment{temp}{\bgroup \color{gray} \textit}{\egroup}

\newcommand{\victor}[2][nolabel]{%
{\color{C2} \refstepcounter{commentctr}\label{#1} \textbf{$[$ (\thecommentctr) Victor: } #2 \textbf{$]$}}}

%% LaTeX stuff

\newenvironment{myhs}{\par\vspace{0.15cm}\begin{minipage}{\textwidth}}{\end{minipage}\vspace{0.15cm}}

%% Repository
%%   https://github.com/VictorCMiraldo/hs-digems
\newcommand{\hsdigemsgit}[0]{https://github.com/VictorCMiraldo/hs-digems}

\newcommand{\bigO}[1]{\mathcal{O}(#1)}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% lhs2TeX Formatting Rules
%%
%% Comment out to use lhs2TeX default formatting.
%%
%include stylish.lhs
%%

% Easy to typeset Haskell types using the 
% commands from stylish.lhs (if it's defined!)
\newcommand{\HT}[1]{\ifdefined\HSCon\HSCon{#1}\else#1\fi}
\newcommand{\HS}[1]{\ifdefined\HSSym\HSSym{#1}\else#1\fi}
\newcommand{\HV}[1]{\ifdefined\HSVar\HSVar{#1}\else#1\fi}

%%% Datatype Promotion
%format PCons   = "\mathbin{\HS{''\!\!:}}"
%format (P (a)) = "\HS{''}" a

%%% Usefull Notation
%format dots    = "\HS{\dots}"
%format forall  = "\HS{\forall}"
%format dot     = "\HS{.}"
%format ^=      = "\HS{\bumpeq}"
%format alpha   = "\HV{\alpha}"
%format psi     = "\HV{\psi}"
%format psi1    = "\HV{\psi_1}"
%format psi2    = "\HV{\psi_2}"
%format phi     = "\HV{\varphi}"
%format phi1    = "\HV{\varphi_1}"
%format phi2    = "\HV{\varphi_2}"
%format kappa   = "\HV{\kappa}"
%format kappa1  = "\HV{\kappa_1}"
%format kappa2  = "\HV{\kappa_2}"
%format eta     = "\HV{\eta}"
%format eta1    = "\HV{\eta_1}"
%format eta2    = "\HV{\eta_2}"
%format Delta   = "\HV{\Delta}"
%format join    = "\HV{\mu}"
%format fSq     = "\HV{f}"
%format =~=     = "\HS{\approx}"
%format :>:     = "\HT{\triangleright}"
%format :*      = "\HT{\times}"
%format :*:     = "\mathbin{\HT{:\!\!*\!\!:}}"
%format :+:     = "\mathbin{\HT{:\!\!+\!\!:}}"
%format :@:     = "\mathbin{\HT{:\!\!@\!\!:}}"
%format <$$>    = "\HS{<\!\!\$\!\!>}"
%format $$      = "\mathbin{\HS{\$}}"
%format <*>     = "\HS{<\!\!*\!\!>}"
%format <->     = "\HS{\leftrightarrow}"

%% Formatting type-applications
%format (TApp iy) = "{\HS{@\!}" iy "}"

%format intersect = "\mathbin{\HS{\cap}}"

%% Words with wrong kerning
%format LeafC = "\HT{Lea\!f\!C}"
%format Leaf  = "\HT{Lea\!f}"
%format Refl  = "\HT{\mathit{Refl}}"
%format NAE   = "\HT{NAE}"
%format MetaVarIK = "\HT{MetaV\!ar}"
%format MetaVar = "\HT{MetaV\!ar}"
%format Conflict = "\HT{Con\!f\!lict}"
%format PatchConf = "\HT{PatchCon\!f}"
%format Word = "\HT{Word}"
%format Trie = "\HT{Trie}"