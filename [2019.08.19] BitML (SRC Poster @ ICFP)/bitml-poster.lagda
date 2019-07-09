\documentclass[final,hyperref={pdfpagelabels=false}]{beamer}
\usepackage[orientation=portrait,size=a0,scale=1.7]{beamerposter}
\usetheme{I6pd2} % Use the I6pd2 theme supplied with this template

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Packages
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Tikz
\usepackage{tikz}
\usetikzlibrary{chains,arrows,automata,fit,positioning,calc}

% Colors
\usepackage{xcolor}

% Images
\usepackage{graphics}
\graphicspath{{img/}}

% Math Symbols
\usepackage{amsmath,amsthm,amssymb,latexsym,stmaryrd}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Macros
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\renewcommand\alert[1]{\textcolor{mLightBrown}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Agda imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%include polycode.fmt
%include stylish.fmt
\def\commentbegin{}
\def\commentend{}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Fonts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\usepackage{relsize}
\usepackage[tt=false]{libertine}
\usepackage[libertine]{newtxmath}

%----------------------------------------------------------------------------------------
% TITLE SECTION
%----------------------------------------------------------------------------------------

\title{\LARGE \textsc{Formalizing BitML Calculus in Agda}}
\author{Orestis Melkonian}
\date{July 8, 2019}
\institute{Utrecht University, The Netherlands}

\titlegraphic{
\vspace{3.8cm}\flushright\includegraphics[scale=.25]{uu}
\vspace{.3cm}\flushright\includegraphics[scale=.375]{iohk}\hspace{.1cm}
}

%----------------------------------------------------------------------------------------
% FOOTER TEXT
%----------------------------------------------------------------------------------------

\newcommand\footsize{15ex}
\newcommand\leftfoot{
  \begin{minipage}{.45\textwidth}
  \topskip0pt
  \vspace{\fill}
  \includegraphics[scale=1]{uu}
  \vspace{\fill}
  \end{minipage}
} % Left footer text
\newcommand\rightfoot{
  \begin{minipage}{.55\textwidth}
  \topskip0pt
  \vspace{\fill}
  \large \textbf{https://github.com/omelkonian/formal-bitml}
  \vspace{\fill}
  \end{minipage}
} % Right footer text

%----------------------------------------------------------------------------------------
% SIZES ( 3*sepsize + 2*colsize == 1 )
%----------------------------------------------------------------------------------------
\newcommand\sepsize{.05\textwidth}
\newcommand\colsize{.425\textwidth}

\begin{document}

\addtobeamertemplate{block end}{}{\vspace*{4ex}} % White space under blocks

\begin{frame}[t] % The whole poster is enclosed in one beamer frame

\begin{columns}[t] % The whole poster consists of two major columns, each of which can be subdivided further with another \begin{columns} block - the [t] argument aligns each column's content to the top

\begin{column}{\sepsize}\end{column} % Empty spacer column

\begin{column}{\colsize} % The first column

%----------------------------------------------------------------------------------------
% CONTENT
%----------------------------------------------------------------------------------------

\begin{block}{Introduction}
  \begin{itemize}
    \item \textbf{Janus} is an imperative reversible programming language, meaning that every computation and function can be reversed.
    \vspace{1cm}
    \item \textbf{Hanus} is an extended implementation of Janus that can be compiled straight to Haskell. Because of this, Hanus contains many awesome Haskell features that are unthinkable in regular Janus!
  \end{itemize}
\end{block}

\begin{block}{Reverse your program}
\begin{agda}\begin{code}
data _ —→ _ : Configuration ads cs ds → Configuration ads′ cs′ ds′ → Set where

  D-AuthJoin :                                                   D-Join :
        ⟨ A , v ⟩ SD | ⟨ A , v′ ⟩ SD | Γ                                 ⟨ A , v ⟩ SD | ⟨ A , v′ ⟩ SD | A [ 0 ↔ 1 ] | Γ
    —→  ⟨ A , v ⟩ SD | ⟨ A , v′ ⟩ SD | A [ 0 ↔ 1 ] | Γ SP SP SP  SP  —→  ⟨ A , v + v′ ⟩ SD | Γ

  C-Advertise   :  Any (UL ∈ Hon) (participants (G ad)) → (Γ —→ ad | Γ)

  C-AuthCommit  :  (secrets A (G ad) ≡ a₀ DOTS aₙ) × (A ∈ Hon → All (U ≢ ^^ nothing) a SUBI)
                →  ` ad | Γ —→ ` ad | Γ | DOTS ⟨ A : a SUBI ♯ N SUBI ⟩ DOTS ^^ BAR ^^ A [ ♯▷ ^^ ad ]
\end{code}\end{agda}
\end{block}

%----------------------------------------------------------------------------------------

\end{column} % End of the first column

\begin{column}{\sepsize}\end{column} % Empty spacer column

\begin{column}{\colsize} % The second column
\addtobeamertemplate{block end}{}{\vspace*{-2.4ex}} % White space under blocks

%----------------------------------------------------------------------------------------

\begin{block}{Semantic Checking (Janus side)}
\end{block}

\begin{block}{Semantic Checking (Haskell side)}
\end{block}

\begin{block}{Haskell Power}
\end{block}

%----------------------------------------------------------------------------------------

\end{column} % End of the second column

\begin{column}{\sepsize}\end{column} % Empty spacer column

\end{columns} % End of all the columns in the poster

\end{frame} % End of the enclosing frame

\end{document}
