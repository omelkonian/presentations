\documentclass[aspectratio=43]{beamer}
\usetheme[
  block=fill,
  background=light,
  titleformat=smallcaps,
  progressbar=frametitle,
  numbering=none,
]{metropolis}
\setbeamersize{text margin left=.5cm,text margin right=.5cm}

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
\usepackage{stmaryrd}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Macros
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\renewcommand\alert[1]{\textcolor{mLightBrown}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Agda imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% %include agda.fmt
%  \DeclareTextCommandDefault{\nobreakspace}{\leavevmode\nobreak\ }

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

%----------------------------------------------------------------------------

\title{
  \hspace{2pt} Formalizing Extended UTxO and BitML Calculus \\
  \hspace{4.5cm} in Agda
}
\subtitle{
  \hspace{1.1cm} Towards formal verification for smart contracts
}
\author{Orestis Melkonian}
\date{July 8, 2019}
\institute{Utrecht University, The Netherlands}
\titlegraphic{\vspace{5cm}\flushright\includegraphics[scale=0.3]{logo}}

\begin{document}
\begin{center}
\maketitle
\end{center}

%include 1-intro.lagda
%include 2-utxo.lagda
%include 3-bitml.lagda
%include 4-future.lagda

\begin{frame}[standout]
  Questions?
\end{frame}

\end{document}
