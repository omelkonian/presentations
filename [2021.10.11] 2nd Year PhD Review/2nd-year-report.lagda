\documentclass[aspectratio=43]{beamer}
%% \documentclass[aspectratio=169]{beamer}
\usetheme[
  block=fill,
  background=light,
  titleformat=smallcaps,
  progressbar=frametitle,
  numbering=none,
]{metropolis}
\setbeamersize{text margin left=.7cm,text margin right=.7cm}
\usepackage{appendixnumberbeamer}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Packages
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage[backend=bibtex,style=authoryear]{biblatex}

% Tikz
\usepackage{tikz}
\usetikzlibrary{arrows,positioning,matrix,fit,backgrounds,decorations.text,decorations.pathmorphing,calc,shapes}

% Colors
\usepackage{xcolor}
\usepackage{contour}

% Images
\usepackage{graphics}
\graphicspath{{img/}}

% Agda
\usepackage{agda}
\setlength{\mathindent}{0em}
\newfontfamily{\AgdaSerifFont}{Linux Libertine O}
\newfontfamily{\AgdaSansSerifFont}{Linux Biolinum O}
\newfontfamily{\AgdaTypewriterFont}{Linux Biolinum O}
\renewcommand{\AgdaFontStyle}[1]{{\AgdaSansSerifFont{}#1}}
\renewcommand{\AgdaKeywordFontStyle}[1]{{\AgdaSansSerifFont{}#1}}
\renewcommand{\AgdaStringFontStyle}[1]{{\AgdaTypewriterFont{}#1}}
\renewcommand{\AgdaCommentFontStyle}[1]{{\AgdaTypewriterFont{}#1}}
\renewcommand{\AgdaBoundFontStyle}[1]{\textit{\AgdaSerifFont{}#1}}

% Haskell
\usepackage{minted}
\newcommand\hs[1]{\mintinline{haskell}{#1}}
%% \usemintedstyle{friendly}
\usepackage{fontspec}
\setmonofont[Scale=MatchLowercase]{FiraMono-Regular.otf}

% Inference rules
\usepackage{amssymb}
\usepackage{stmaryrd}
\usepackage{proof}
\newenvironment{proposition}[1]
  {\begin{alertblock}{#1}\begin{displaymath}}
  {\end{displaymath}\end{alertblock}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Macros
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\renewcommand\alert[1]{\textcolor{mLightBrown}{#1}}
\newcommand\todo[1]{\textcolor{red}{#1}}

% My publications
\newcommand\citewtsc{%
\textbf{WTSC @ FC'20}\\
The Extended UTxO Model\\
\scriptsize{\textit{M.Chakravarty, J.Chapman, K.MacKenzie, O.Melkonian, M.P.Jones, P.Wadler}}
}
\newcommand\citeutxoma{%
\textbf{RSC @ ISoLA'20}: \textit{UTxO$_{\textsf{ma}}$: UTxO with Multi-Asset Support}
}
\newcommand\citeeutxoma{%
\textbf{RSC @ ISoLA'20}: \textit{Native Custom Tokens in the Extended UTxO Model}
}
\newcommand\citeagda{%
\textbf{CPP @ POPL'22}\\
\small{Reasonable Agda is Correct Haskell: Intrinsic Program Verification using \textsc{agda2Hs}}\\
\scriptsize{\textit{J.Cockx, O.Melkonian, J.Chapman, U.Norell + TU Delft students}}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Fonts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\usepackage{relsize}
\usepackage[tt=false]{libertine}
\usepackage[libertine]{newtxmath}

\usepackage{yfonts}
\usepackage{xspace}
\newcommand\I{\textgoth{I}\xspace}
\newcommand\II{\textgoth{II}\xspace}
\newcommand\III{\textgoth{III}\xspace}

%----------------------------------------------------------------------------

\title{2$^{nd}$-year PhD Report}
%\subtitle{}
\vspace{-1cm}
\author{Orestis Melkonian}
\date{October 11, 2021}
\titlegraphic{
\vspace*{6cm}
\includegraphics[keepaspectratio=true,height=1.2cm]{uoe}\\
\includegraphics[keepaspectratio=true,height=1.0cm]{iohk}
}

\begin{document}
\begin{center}
\setbeamerfont{title}{size=\large}
\setbeamerfont{subtitle}{size=\small}
\maketitle
\setbeamerfont{title}{size=\Large}
\setbeamerfont{subtitle}{size=\large}
\end{center}

\input{0-diagrams.tex}

\section{Year \I: \textit{Recap}}

\begin{frame}{Recap}
Mechanising the meta-theory of two separate objects of study:
  \begin{itemize}
  \item \textbf{BitML}: Bitcoin Modelling Language
  \item The (extended) \textbf{UTxO} model
  \end{itemize}
\end{frame}

\begin{frame}{UTxO [2018-2020]}
\begin{center}
\begin{tikzpicture}
  \utxo
  \begin{pgfonlayer}{background}
    \onslide<+->{
      \node[MSc, MSc-label, fit=(utxo) (eutxo)] {};
      \node[PhD, PhD-label, fit=(iso) (cem)] {};
    }
    \onslide<+>{
      \node[cit, below = of cem] {\citewtsc};
    }
  \end{pgfonlayer}
\end{tikzpicture}
\end{center}
\end{frame}

\begin{frame}{BitML [2018-2020]}
\begin{center}
\begin{tikzpicture}
  \bitml
  \begin{pgfonlayer}{background}
    \onslide<+->{
      \node[MSc, MSc-label, fit=(contracts) (sm)] {};
      \node[PhD, PhD-label, fit=(transactions) (cm)] {};
      \node[PhD, fit=(contracts.south) (comp) (transactions)] {};
    }
  \end{pgfonlayer}
\end{tikzpicture}
\end{center}
\end{frame}

\section{Year \II: \textit{Where I've been...}}

\begin{frame}{UTxO [2020-2021]}
\begin{center}
\begin{tikzpicture}
  \utxo
  \begin{pgfonlayer}{background}
    \onslide<+->{
      \node[MSc, MSc-label, fit=(utxo) (eutxo)] {};
      \node[PhD, PhD-label, fit=(iso) (cem)] {};
    }
  \end{pgfonlayer}
  \begin{pgfonlayer}{background}
    \onslide<+->{
      \node[PhD2, PhD2-label={below}, fit=(l) (cem2)] {};
      %% \node[PhD2, fit=(iso) (cem2)] {};
    }
  \end{pgfonlayer}
  \onslide<+>{
    \node[cit, below = of cem] (utxoma) {\citeutxoma};
    \node[cit, below = 1pt of utxoma] {\citeeutxoma};
  }
\end{tikzpicture}
\end{center}
\end{frame}

\newcommand\froto{$\leftrightarrow$}
\begin{frame}{Separation Logic for UTxO}
\begin{itemize}
\item In collaboration with W.Swierstra (UU) and J.Chapman (IOHK)
\pause
\item[]
\begin{tabular}{ccc}
\textbf{Blockchain} & & \textbf{Concurrency Theory} \\
\hline
ledgers &\froto& computer memory \\
memory locations &\froto& accounts \\
data values &\froto& account balances \\
smart contracts &\froto& programs accessing memory \\
\end{tabular}
\pause
\item[] \includegraphics[keepaspectratio=true,height=3ex]{lightbulb}
Transfer results from (Concurrent) Separation Logic!
\end{itemize}
\end{frame}

\begin{frame}{Hoare-style semantics and correspondences}
\begin{center}
\begin{tikzpicture}
  \hoareSemantics
\end{tikzpicture}
\end{center}
\pause
\begin{minipage}{.4\textwidth}
\begin{proposition}{SL: \texttt{[FRAME]} rule}
\infer
  {\{ P * R \} l \{ Q * R \} }
  {%
    l \# R
  & \{ P \} l \{ Q \}
  }
\end{proposition}
\end{minipage}
\pause
\hfill
\begin{minipage}{.4\textwidth}
\begin{proposition}{CSL: \texttt{[PARALLEL]} rule}
\infer
  {\{ P_1 * P_2 \} l \{ Q_1 * Q_2 \} }
  { \deduce{\{ P_1 \} l_1 \{ Q_1 \} }
           {l_1 \parallel l_2 = l}
  & \deduce{\{ P_2 \} l_2 \{ Q_2 \} }
           {l_1 \# P_2 \quad l_2 \# P_1 }
  }
\end{proposition}
\end{minipage}
\end{frame}

\begin{frame}{BitML [2020-2021]}
\begin{center}
\scalebox{.95}{
  \begin{tikzpicture}
  \bitml
  \begin{pgfonlayer}{background}
    \node[MSc, MSc-label, fit=(contracts) (sm)] {};
    \node[PhD, PhD-label, fit=(transactions) (cm)] {};
    \node[PhD, fit=(contracts.south) (comp) (transactions)] {};
    \onslide<2>{
      \node[greenDot, PhD2-label={above right, xshift=-1em}, fit=(cm.north east) (coh) (sm.south east)] {};
    }
  \end{pgfonlayer}
  \end{tikzpicture}
}
\end{center}
\end{frame}

\begin{frame}{BitML: Coherence}
\vspace{-.35cm}
\hspace{-1.4cm}
\includegraphics[keepaspectratio=true,width=\paperwidth]{bitml-coherence}
\end{frame}

\begin{code}[hide]
open import Haskell.Prim
open import Haskell.Prim.String
open import Haskell.Prim.Bool
open import Haskell.Prim.List
open import Haskell.Prim.Foldable
open import Haskell.Prim.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data _≤_ : Nat → Nat → Set where
  zero-≤ : ∀ {n} → zero ≤ n
  suc-≤ : ∀ {m n} → m ≤ n → suc m ≤ suc n

data Comparison {m n : Nat} : Set where
  LT  : {pf : m ≤ n} → Comparison {m} {n}
  EQ  : {pf : m ≡ n} → Comparison {m} {n}
  GT  : {pf : n ≤ m} → Comparison {m} {n}
{-# COMPILE AGDA2HS Comparison #-}

compare : (m n : Nat) → Comparison {m} {n}
compare zero zero = EQ {pf = refl}
compare zero (suc n) = LT {pf = zero-≤}
compare (suc m) zero = GT {pf = zero-≤}
compare (suc m) (suc n) = case compare m n of λ where
  (LT {pf = m≤n})  → LT {pf = suc-≤ m≤n}
  (EQ {pf = refl}) → EQ {pf = refl}
  (GT {pf = n≤m})  → GT {pf = suc-≤ n≤m}
{-# COMPILE AGDA2HS compare #-}

ShowS : Set
ShowS = String → String
{-# COMPILE AGDA2HS ShowS #-}

showString : String → ShowS
showString = _++_
{-# COMPILE AGDA2HS showString #-}

showParen : Bool → ShowS → ShowS
showParen false s = s
showParen true  s = showString "(" ∘ s ∘ showString ")"
{-# COMPILE AGDA2HS showParen #-}

defaultShowList : (a → ShowS) → List a → ShowS
defaultShowList _     []       = showString "[]"
defaultShowList shows (x ∷ xs) = showString "[" ∘ foldl (λ s x → s ∘ showString "," ∘ shows x) (shows x) xs ∘ showString "]"
{-# COMPILE AGDA2HS defaultShowList #-}
\end{code}
\newcommand{\agdaTrees}{%
\begin{code}
data Tree {l u : Nat} : Set where
  Leaf  : {pf : l ≤ u} → Tree {l} {u}
  Node  : (x : Nat)
    → Tree {l} {x} → Tree {x} {u}
    → Tree {l} {u}
{-# COMPILE AGDA2HS Tree #-}

insert : {l u : Nat} (x : Nat)
  → Tree {l} {u}
  → {l ≤ x} → {x ≤ u}
  → Tree {l} {u}
insert x Leaf {l≤x} {x≤u} =
  Node x (Leaf {pf = l≤x}) (Leaf {pf = x≤u})
insert x (Node y l r) {l≤x} {x≤u} =
  case compare x y of λ where
    (LT {pf = x≤y})  → Node y (insert x l {l≤x} {x≤y}) r
    (EQ {pf = x≡y})  → Node y l r
    (GT {pf = y≤x})  → Node y l (insert x r {y≤x} {x≤u})
{-# COMPILE AGDA2HS insert #-}
\end{code}}
\newcommand{\agdaClasses}{%
\begin{code}
record Show (a : Set) : Set where
  field  show       : a → String
         showsPrec  : Nat → a → ShowS
         showList   : List a → ShowS

record Show₁ (a : Set) : Set where
  field showsPrec : Nat → a → ShowS

  show : a → String
  show x = showsPrec 0 x ""

  showList : List a → ShowS
  showList = defaultShowList (showsPrec 0)

record Show₂ (a : Set) : Set where
  field show : a → String

  showsPrec : Nat → a → ShowS
  showsPrec _ x s = show x ++ s

  showList : List a → ShowS
  showList = defaultShowList (showsPrec 0)

open Show {{...}}
{-# COMPILE AGDA2HS Show class Show₁ Show₂ #-}

instance
  ShowMaybe : {{Show a}} → Show (Maybe a)
  ShowMaybe {a = a} = record {Show₁ s₁}
    where
    s₁ : Show₁ (Maybe a)
    s₁ .Show₁.showsPrec n = λ where
      Nothing   → showString "nothing"
      (Just x)  → showParen true
        (showString "just " ∘ showsPrec 10 x)
{-# COMPILE AGDA2HS ShowMaybe #-}
\end{code}}

\setlength{\AgdaEmptySkip}{1em}
\renewcommand{\AgdaCodeStyle}{\scriptsize}
\setminted[haskell]{fontsize=\tiny}
\begin{frame}[fragile]{agda2hs}
\begin{minipage}[l]{.5\textwidth}
\agdaTrees{}
\end{minipage}
\hfill\vline\hfill
\begin{minipage}[r]{.4\textwidth}
\begin{minted}{haskell}
data Tree = Leaf
          | Node Natural Tree Tree

insert :: Natural -> Tree -> Tree
insert x Leaf = Node x Leaf Leaf
insert x (Node y l r)
  = case compare x y of
      LT -> Node y (insert x l) r
      EQ -> Node x l r
      GT -> Node y l (insert x r)
\end{minted}
\end{minipage}
\end{frame}

\setlength{\AgdaEmptySkip}{0em}
\renewcommand{\AgdaCodeStyle}{\tiny}
\setminted[haskell]{fontsize=\tiny}
\begin{frame}[fragile]{agda2hs: typeclasses}
\begin{minipage}[l]{.4\textwidth}
\agdaClasses{}
\end{minipage}
\hfill\vline\hfill
\begin{minipage}[r]{.5\textwidth}
\begin{minted}{haskell}
class Show a where
  show :: a -> String
  showsPrec :: Natural -> a -> ShowS
  showList :: [a] -> ShowS
  {-# MINIMAL showsPrec | show #-}
  show x = showsPrec 0 x ""
  showList = defaultShowList (showsPrec 0)
  showsPrec _ x s = show x ++ s

instance (Show a) => Show (Maybe a) where
  showsPrec n = \case
    Nothing -> showString "nothing"
    (Just x) -> showParen True
      (showString "just " . showsPrec 10 x)
\end{minted}
\end{minipage}
\pause
\begin{center}
\begin{tikzpicture}[overlay, remember picture]
  %% \tikzset{shift={(page.center)},yshift=-1.5cm}
  \begin{pgfonlayer}{background}
    %% \node[cit,xshift=.3\textwidth,yshift=.3\textheight] {\citeagda};
    \node[cit] at (current page.center) {\citeagda};
  \end{pgfonlayer}
\end{tikzpicture}
\end{center}
\end{frame}

\setminted[yaml]{fontsize=\footnotesize}
\begin{frame}[fragile]{\texttt{setup-agda:} CI infrastructure for Agda}
\begin{minted}{yaml}
name: CI
on: push: {branches: master}
jobs:
  build-deploy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2.3.1
      - uses: omelkonian/setup-agda@v0.1
        with:
          agda-version: 2.6.1.3
          stdlib-version: 1.6
          libraries: |
            omelkonian/formal-prelude#92ef
            omelkonian/formal-bitcoin#0341
            omelkonian/formal-bitml#4382
          main: Main
          token: ${{ secrets.GITHUB_TOKEN }}
\end{minted}
\end{frame}

\newcommand\agdaSolve{%
\begin{code}
open import Prelude.Init using (List)
open import Prelude.Semigroup
open import Prelude.Membership
open import Prelude.Solvers

_ : ∀ {A : Set} {y : A} {xs ys zs : List A}
  → y ∈ ys → y ∈ xs ◇ ys ◇ zs
_ = solve
\end{code}
}

\setlength{\AgdaEmptySkip}{1em}
\renewcommand{\AgdaCodeStyle}{\normalsize}
\begin{frame}{Modular Automatic Solvers for Agda proofs}
\begin{itemize}
\item define strategies for automatic proof search
\item should be able to define solvers incrementally for specific types
\item primarily achieved with Agda's \alert{reflection}
\end{itemize}
\pause
\begin{center}
\agdaSolve{}
\end{center}
\end{frame}


\section{Year \III: \textit{Where I'm going...}}

\begin{frame}{BitML [2021 - mid 2022]}
\begin{enumerate}
\item Finish up coherence
\item Symbolic $\rightarrow$ computational runs
\item Prove \alert{computational soundness}: compiler preserves coherence
\item Write a paper about it!
\end{enumerate}
\begin{center}
\vfill
\scalebox{.8}{
  \begin{tikzpicture}
  \bitml
  \begin{pgfonlayer}{background}
    \node[MSc, MSc-label, fit=(contracts) (sm)] {};
    \node[PhD, PhD-label, fit=(transactions) (cm)] {};
    \node[PhD, fit=(contracts.south) (comp) (transactions)] {};
    \node[greenDot, PhD2-label={above right, xshift=-1em}, fit=(cm.north east) (coh) (sm.south east)] {};
    \pause
    \node[redDot, inner sep = .06cm, rounded corners = 1mm,
          fit=(sm.south east) (coh.east) (cm.north east), xshift=-.3cm] {};
    \pause
    \node[redDot, fit=(comps)] {};
    \node[redDot, fit=(sm.south) (n) (cm.north)] {};
  \end{pgfonlayer}
  \end{tikzpicture}
}
\end{center}
\end{frame}

\begin{frame}{Separation Logic for Blockchain [2021 - mid 2022]}
\begin{enumerate}
\item Obvious next step: extend results to UTxO ledgers
\item Write a paper about it!
\end{enumerate}
\begin{center}
\vfill
\scalebox{.8}{
  \begin{tikzpicture}
  \hoareSemantics
  \end{tikzpicture}
}
\end{center}
\end{frame}

\begin{frame}{Thesis write-up [mid 2022 - late 2022]}
\begin{itemize}
\item Hopefully by then, enough material to fill a thesis
\item Ideally, two more papers on BitML and UTxO at prestigious venues
\item Realistically, UTxO exploration alongside thesis writing
\end{itemize}
\end{frame}

\begin{frame}{Discussion}

\begin{itemize}
\item More ambitious directions (alas, no time)
  \begin{itemize}
  \item \textbf{\textsc{agda2hs}:} extract executable programs from my mechanisations
  \item \textbf{BitML:} improve/re-formulate (e.g. BitML $\to$ EUTxO)
  \item \textbf{EUTxO:} further extentions / state machine verification
  \end{itemize}
\pause
\item Internship?
  \begin{itemize}
  \item some interesting positions/projects so far
  \item[] \includegraphics[keepaspectratio=true,height=3ex]{emoji-thinking}
    is it worth it though?
  \end{itemize}
\pause
\item Extension?
  \begin{itemize}
  \item a few more months would lead to more results
  \item[] \includegraphics[keepaspectratio=true,height=3ex]{emoji-thinking}
    is it worth it though?
  \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}[standout]
Discussion
\end{frame}

\end{document}
