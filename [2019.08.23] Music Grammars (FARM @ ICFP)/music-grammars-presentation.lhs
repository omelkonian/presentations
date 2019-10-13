\documentclass[aspectratio=43]{beamer}
\usetheme[
  block=fill,
  background=light,
  titleformat=smallcaps,
  progressbar=frametitle,
  %% numbering=none,
]{metropolis}
\setbeamersize{text margin left=.5cm,text margin right=.5cm}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Packages
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Colors
\usepackage{xcolor}

% Images
\usepackage{graphics}
\graphicspath{{img/}}

% Math Symbols
\usepackage{stmaryrd}

% Quotes
\usepackage{epigraph}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Macros
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\renewcommand\alert[1]{\textcolor{mLightBrown}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Haskell imports
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

%----------------------------------------------------------------------------

\title{Music as Language}
\subtitle{Putting Probabilistic Temporal Graph Grammars to Good Use}
\author{Orestis Melkonian}
\date{August 23, 2019}
\institute{Utrecht University, The Netherlands}

\begin{document}
\begin{center}
\maketitle
\end{center}

%include 1-intro.lhs
%include 2-ptgg.lhs
%include 3-harmony.lhs
%include 4-melody.lhs
%include 5-rhythm.lhs
%include 6-songs.lhs
%include 7-conclusion.lhs

\begin{frame}[standout]
  Questions?
\end{frame}

\end{document}
