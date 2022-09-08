%% \documentclass[aspectratio=43]{beamer}
\documentclass[aspectratio=169]{beamer}
\usetheme[
  block=fill,
  background=light,
  titleformat=smallcaps,
  progressbar=frametitle,
  numbering=none,
]{metropolis}
%% \setbeamersize{text margin left=.5cm,text margin right=.5cm}
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

\usepackage{amsxtra}
\usepackage{newunicodechar}
\newunicodechar{∷}{::}

\usepackage{minted}
\newcommand\hs[1]{\mintinline{haskell}{#1}}
%% \setminted[haskell]{fontsize=\footnotesize}
%% \usemintedstyle{friendly}
\usepackage{fontspec}
\setmonofont[Scale=MatchLowercase]{FiraMono-Regular.otf}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Macros
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\renewcommand\alert[1]{\textcolor{mLightBrown}{#1}}
\newcommand\todo[1]{\textcolor{red}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Fonts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\usepackage{relsize}
\usepackage[tt=false]{libertine}


\usepackage{yfonts}
\usepackage{xspace}
\newcommand\I{\textgoth{I}\xspace}
\newcommand\II{\textgoth{II}\xspace}
\newcommand\III{\textgoth{III}\xspace}

\newcommand\agdatohs{\textsc{agda2hs}\xspace}

%----------------------------------------------------------------------------

\title{Reasonable Agda Is Correct Haskell:}
\subtitle{Writing Verified Haskell using agdatohs}
\vspace{-1cm}

\newcommand\img[2]{\includegraphics[keepaspectratio=true,height=#1]{#2}}
\newcommand\smallImg[1]{\img{1.7em}{#1}}
\newcommand\largeImg[1]{\img{2.5cm}{#1}}

\newcommand*\vmid[1]{\vcenter{\hbox{#1}}}

\newcommand\agdaHsLove{%
$
\vmid{\smallImg{agda}}
\vmid{\scalebox{1.5}{\ +\ }}
\vmid{\smallImg{haskell}}
\vmid{\scalebox{1.5}{\ =\ }}
\vmid{\smallImg{heart}}
$
}

\author{Jesper Cockx, \alert{Orestis Melkonian}, Lucas Escot, James Chapman, Ulf Norell}
%% \date{September 7$^{th}$, 2022}
\date{}
\titlegraphic{
\vspace*{6cm}
\begin{center}
\[
\vmid{\largeImg{agda}}
\vmid{\scalebox{2}{\Huge$\ \Longrightarrow\ $}}
\vmid{\largeImg{haskell}}
\]
\end{center}
}

\begin{document}
\begin{center}
\setbeamerfont{title}{size=\LARGE}
\setbeamerfont{subtitle}{size=\Large}
\vspace*{-2cm}
\maketitle
%% \setbeamerfont{title}{size=\Large}
%% \setbeamerfont{subtitle}{size=\large}
\end{center}

\begin{frame}[fragile]{Motivation: issues with current program extractors}

\textbf{MAlonzo} covers the entirety of Agda, but produces unreadable code:
\begin{alertblock}{}
\begin{minted}[fontsize=\scriptsize]{haskell}
d_insert_1494 :: Integer -> Integer -> Integer
              -> T_Tree_1340 -> T__'8804'__1324 -> T__'8804'__1324 -> T_Tree_1340
d_insert_1494 ~v0 ~v1 v2 v3 ~v4 ~v5 = du_insert_1494 v2 v3
du_insert_1494 :: Integer -> T_Tree_1340 -> T_Tree_1340
du_insert_1494 v0 v1 = case coe v1 of
  C_Leaf_1348 -> coe C_Node_1352 (coe v0) (coe C_Leaf_1348) (coe C_Leaf_1348)
  C_Node_1352 v2 v3 v4 -> coe MAlonzo.Code.Haskell.Prim.du_case_of__54
    (coe d_compare_1474 (coe v0) (coe v2))
    (coe du_'46'extendedlambda0_1514 (coe v0) (coe v2) (coe v3) (coe v4))
  _ -> MAlonzo.RTE.mazUnreachableError
\end{minted}
\end{alertblock}

\end{frame}

\begin{frame}[fragile]{Motivation: issues with current program extractors}

\textbf{Coq} extracts more reabable code, but still does not readily support typeclasses:

\begin{alertblock}{}
\begin{minipage}{.43\textwidth}%
\begin{minted}[fontsize=\scriptsize]{coq}
Class Monoid (a : Set) :=
  { mempty  : a
  ; mappend : a -> a -> a }.

Instance MonoidNat : Monoid nat :=
  { mempty := 0
  ; mappend i j := i + j }.

Fixpoint sumMon {a} `{Monoid a}
  (xs : list a) : a :=
  match xs with
  | [] => mempty
  | x :: xs => mappend x (sumMon xs)
  end.
\end{minted}
\end{minipage}
\vrule\hspace{.1cm}
\begin{minipage}{.5\textwidth}%
\begin{minted}[fontsize=\scriptsize]{haskell}
data Monoid a = Build_Monoid a (a -> a -> a)

mempty :: (Monoid a1) -> a1
mempty = ...
mappend :: (Monoid a1) -> a1 -> a1 -> a1
mappend = ...
monoidNat :: Monoid Nat
monoidNat = Build_Monoid O add

sumMon :: (Monoid a1) -> (List a1) -> a1
sumMon h xs = case xs of {
  ([]) -> mempty h;
  (:) x xs0 -> mappend h x (sumMon h xs0)}
\end{minted}
\end{minipage}
\end{alertblock}

\end{frame}

\begin{frame}[fragile]{Goals}
\begin{enumerate}
\item Writing Haskell within Agda (no need to cover the whole source language)
\item Verify your program using Agda's dependent types
\end{enumerate}
\pause
\textbf{New point} in the design space, enabled by:
\begin{itemize}
\item Agda very \textit{similar} to Haskell \hspace{.5cm}\agdaHsLove{}
\item Agda's \textit{dependent type system}
\item Agda's support for \textit{erasure}
\item[+] allows for \alert{intrinsic verification}!
\end{itemize}

\end{frame}

% SETUP
\AgdaNoSpaceAroundCode{}
\begin{code}[hide]
{-# OPTIONS --erase-record-parameters #-}

open import Haskell.Prelude hiding
  ( compare; LT; EQ; GT
  ; if_then_else_; id
  ; head; error
  ; Monoid; mempty; mappend
  ; ShowS; showString; showParen; defaultShowList; Show; show; showList; showsPrec
  ; f
  )

module P = Haskell.Prelude

{-# FOREIGN AGDA2HS
import Prelude as P hiding (compare, LT, EQ, GT)
#-}

data _≤_ : Nat → Nat → Set where
  zero-≤ : ∀ {n} → zero ≤ n
  suc-≤  : ∀ {m n} → m ≤ n → (suc m) ≤ (suc n)

data Comparison (@0 m n : Nat) : Set where
  LT  : (@0 pf : m ≤ n) → Comparison m n
  EQ  : (@0 pf : m ≡ n) → Comparison m n
  GT  : (@0 pf : n ≤ m) → Comparison m n
{-# COMPILE AGDA2HS Comparison #-}

Ordered : Ordering → Nat → Nat → Set
Ordered P.LT m n = m ≤ n
Ordered P.EQ m n = m ≡ n
Ordered P.GT m n = n ≤ m

<-correct-true : (m n : Nat) → (m < n) ≡ True → m ≤ n
<-correct-true zero    n       eq = zero-≤
<-correct-true (suc m) (suc n) eq = suc-≤ (<-correct-true m n eq)

<-correct-false : (m n : Nat) → (m < n) ≡ False → n ≤ m
<-correct-false m       zero    eq = zero-≤
<-correct-false (suc m) (suc n) eq = suc-≤ (<-correct-false m n eq)

==-correct-true : (m n : Nat) → (m == n) ≡ True → m ≡ n
==-correct-true zero zero eq = refl
==-correct-true (suc m) (suc n) eq rewrite ==-correct-true m n eq = refl

compare-correct : (m n : Nat) → Ordered (P.compare m n) m n
compare-correct m n with m < n in eq< | m == n in eq=
... | False | False = <-correct-false m n eq<
... | False | True  = ==-correct-true m n eq=
... | True  | _     = <-correct-true  m n eq<

compare : (m n : Nat) → Comparison m n
compare m n = aux (P.compare m n) (compare-correct m n)
  where
    aux : (o : Ordering) → @0 Ordered o m n → Comparison m n
    aux P.LT = LT
    aux P.EQ = EQ
    aux P.GT = GT

{-# COMPILE AGDA2HS compare #-}

variable
  A B C : Set
  x y z : A

postulate
  ⋯ TODO : A

\end{code}

\begin{frame}[fragile]{Tree example (extrinsic version)}

\begin{minipage}{.53\textwidth}%
\begin{code}[hide]
module Extrinsic where
\end{code}
\begin{code}
  data Tree : Set where
    Leaf  : Tree
    Node  : Nat → Tree → Tree → Tree
  {-# COMPILE AGDA2HS Tree #-}

  insert : Nat → Tree → Tree
  insert x Leaf = Node x Leaf Leaf
  insert x (Node y l r) =
    case compare x y of λ where
      (LT _) → Node y (insert x l) r
      (EQ _) → Node y l r
      (GT _) → Node y l (insert x r)
  {-# COMPILE AGDA2HS insert #-}
\end{code}
\end{minipage}\hspace{-1cm}\vrule\hspace{.5cm}
\begin{minipage}{.45\textwidth}%
\begin{minted}[fontsize=\small]{haskell}
data Tree = Leaf
          | Node Natural Tree Tree

insert :: Natural -> Tree -> Tree
insert x Leaf = Node x Leaf Leaf
insert x (Node y l r)
  = case compare x y of
        LT -> Node y (insert x l) r
        EQ -> Node y l r
        GT -> Node y l (insert x r)
\end{minted}
\end{minipage}

\end{frame}

\begin{frame}[fragile]{Tree example (extrinsic proofs)}

\begin{minipage}{.6\textwidth}%
\hspace{2cm}$\vdots$

\begin{code}
  @0 _≤_≤_ : Nat → Tree → Nat → Set
  l  ≤ Leaf          ≤ u  = l ≤ u
  l  ≤ Node x tˡ tʳ  ≤ u  = (l ≤ tˡ ≤ x) × (x ≤ tʳ ≤ u)

  @0 insert-correct : ∀ {t x l u} → l ≤ t ≤ u
    → l ≤ x → x ≤ u → l ≤ insert x t ≤ u
  insert-correct {Leaf} _ l≤x x≤u = l≤x , x≤u
  insert-correct {Node y tˡ tʳ} {x} (IHˡ , IHʳ) l≤x x≤u
    with  compare x y
  ... |  LT x≤y   = insert-correct IHˡ l≤x x≤y , IHʳ
  ... |  EQ refl  = IHˡ , IHʳ
  ... |  GT y≤x   = IHˡ , insert-correct IHʳ y≤x x≤u
\end{code}
\end{minipage}\vrule
\begin{minipage}{.4\textwidth}%
\end{minipage}

\end{frame}

\begin{frame}[fragile]{Tree example (intrinsic version)}

\hspace{-.5cm}
\begin{minipage}{.6\textwidth}%
\begin{code}
data Tree (@0 l u : Nat) : Set where
  Leaf  : (@0 pf : l ≤ u) → Tree l u
  Node  : (x : Nat) → Tree l x → Tree x u
    → Tree l u
{-# COMPILE AGDA2HS Tree #-}
insert : {@0 l u : Nat} (x : Nat) → Tree l u
  → @0 (l ≤ x) → @0 (x ≤ u) → Tree l u
insert x (Leaf _) l≤x x≤u =
  Node x (Leaf l≤x) (Leaf x≤u)
insert x (Node y l r) l≤x x≤u =
  case compare x y of λ where
    (LT x≤y)  → Node y (insert x l l≤x x≤y) r
    (EQ x≡y)  → Node y l r
    (GT y≤x)  → Node y l (insert x r y≤x x≤u)
{-# COMPILE AGDA2HS insert #-}
\end{code}
\end{minipage}\hspace{-1cm}\vrule\hspace{.25cm}
\begin{minipage}{.4\textwidth}%
\begin{minted}[fontsize=\small]{haskell}
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

\begin{frame}[fragile]{Primitives}

\begin{itemize}
\item Export lowercase type variables to feel like home:
\begin{code}
id : a → a
id x = x
\end{code}

\pause
\item Match Agda built-ins to Haskell built-ins:

e.g. \AgdaDatatype{Agda.Builtin.Nat} $\leftrightarrow$ \hs{Numeric.Natural}

\pause
\item If not available in Agda, define them:

\begin{code}
infix -2 if_then_else_
if_then_else_ : Bool → a → a → a
if False then x else y = y
if True  then x else y = x
\end{code}

\pause
\begin{alertblock}{REMEMBER}
We want to cover as many Haskell features as possible, not Agda features.
\end{alertblock}

\end{itemize}

\end{frame}

\begin{frame}[fragile]{Prelude}

Port Haskell's Prelude, staying faithful to the original functionality

What about \alert{partial} functions such as \hs{head}?
\pause
\begin{itemize}
\item[$\Rightarrow$] implement safe version with extra preconditions
\item[$\Rightarrow$] only allow calls to \hs{error} in unreachable cases:
\end{itemize}

\begin{minipage}{.59\textwidth}%
\begin{code}
error : (@0 i : ⊥) → String → a
error ()

head : (xs : List a) {@0 _ : NonEmpty xs} → a
head (x ∷ _)  = x
head [] {p}   = error i "head: empty list"
  where @0 i : ⊥
        i = case p of λ ()
\end{code}
\end{minipage}\hspace{-1cm}\vrule\hspace{.25cm}
\begin{minipage}{.4\textwidth}%
\begin{minted}[fontsize=\small]{haskell}
head :: [a] -> a
head (x : _) = x
head [] = error "head: empty list"
\end{minted}
\begin{alertblock}{Don't forget}
On the Haskell side, we can feed \hs{head} arbitrary input!
\end{alertblock}
\end{minipage}

\end{frame}

\begin{frame}[fragile]{Typeclasses}

Correspondence with Agda's \textbf{instance arguments}.
\begin{itemize}
\item class definitions $\sim$ record types
\item instance declarations $\sim$ record values
\item constraints $\sim$ instance arguments
\end{itemize}

\end{frame}

\begin{frame}[fragile]{Typeclasses: class definitions $\sim$ record types}

\begin{minipage}{.69\textwidth}%
\begin{code}
record Monoid (a : Set) : Set where
  field
    mempty   : a
    mappend  : a → a → a
    @0 left-identity   : mappend mempty x ≡ x
    @0 right-identity  : mappend x mempty ≡ x
    @0 associativity   : mappend (mappend x y) z
                       ≡ mappend x (mappend y z)
open Monoid {{...}} public
{-# COMPILE AGDA2HS Monoid class #-}
\end{code}
\end{minipage}\hspace{-1cm}\vrule\hspace{.1cm}
\begin{minipage}{.3\textwidth}%
\begin{minted}{haskell}
class Monoid a where
  mempty :: a
  mappend :: a -> a -> a
\end{minted}
\end{minipage}

\end{frame}

\begin{frame}[fragile]{Typeclasses: instance declarations $\sim$ record values}

\begin{minipage}{.53\textwidth}%
\begin{code}
instance
  MonoidNat : Monoid Nat
  MonoidNat = λ where
    .mempty       → 0
    .mappend i j  → i + j
    .left-identity   → ⋯
    .right-identity  → ⋯
    .associativity   → ⋯
{-# COMPILE AGDA2HS MonoidNat #-}
\end{code}
\end{minipage}\hspace{-.5cm}\vrule\hspace{.2cm}
\begin{minipage}{.45\textwidth}%
\begin{minted}{haskell}
instance Monoid Nat where
  mempty = 0
  mappend i j = i + j
\end{minted}
\end{minipage}

\end{frame}

\begin{frame}[fragile]{Typeclasses: constraints $\sim$ instance arguments}

\hspace{-.7cm}
\begin{minipage}{.59\textwidth}%
\begin{code}
sumMon : {{ Monoid a }} → List a → a
sumMon []        = mempty
sumMon (x ∷ xs)  = mappend x (sumMon xs)
{-# COMPILE AGDA2HS sumMon #-}
\end{code}
\end{minipage}\hspace{-1cm}\vrule\hspace{.2cm}
\begin{minipage}{.41\textwidth}%
\begin{minted}[fontsize=\footnotesize]{haskell}
sumMon :: Monoid a => [a] -> a
sumMon [] = mempty
sumMon (x : xs) = mappend x (sumMon xs)
\end{minted}
\end{minipage}

\end{frame}

\begin{frame}[fragile]{Default methods \& minimal complete definitions}

\hspace{-.8cm}
\begin{minipage}{.65\textwidth}%
\begin{code}[hide]
open import Haskell.Prim.Bool
open import Haskell.Prim.Foldable
open import Haskell.Prim.Maybe

ShowS : Set
ShowS = String → String
{-# COMPILE AGDA2HS ShowS #-}

showString : String → ShowS
showString = _++_
{-# COMPILE AGDA2HS showString #-}

showParen : Bool → ShowS → ShowS
showParen False s = s
showParen True  s = showString "(" ∘ s ∘ showString ")"
{-# COMPILE AGDA2HS showParen #-}

defaultShowList : (a → ShowS) → List a → ShowS
defaultShowList _     []       = showString "[]"
defaultShowList shows (x ∷ xs) = showString "[" ∘ foldl (λ s x → s ∘ showString "," ∘ shows x) (shows x) xs ∘ showString "]"
{-# COMPILE AGDA2HS defaultShowList #-}
\end{code}
\begin{AgdaAlign}
\begin{code}
record Show (a : Set) : Set where
  field  show       : a → String
         showsPrec  : Nat → a → ShowS
         showList   : List a → ShowS
record Show₁ (a : Set) : Set where
  field showsPrec : Nat → a → ShowS
\end{code}
\begin{code}[hide]
  show : a → String
\end{code}
\begin{code}
  show x = showsPrec 0 x ""
\end{code}
\begin{code}[hide]
  showList : List a → ShowS
\end{code}
\begin{code}
  showList = defaultShowList (showsPrec 0)
record Show₂ (a : Set) : Set where
  field show : a → String
\end{code}
\begin{code}[hide]
  showsPrec : Nat → a → ShowS
\end{code}
\begin{code}
  showsPrec _ x s = show x ++ s
\end{code}
\begin{code}[hide]
  showList : List a → ShowS
\end{code}
\begin{code}
  showList = defaultShowList (showsPrec 0)
open Show {{...}}
{-# COMPILE AGDA2HS Show class Show₁ Show₂ #-}
\end{code}
\end{AgdaAlign}
\end{minipage}\vrule\hspace{.1cm}
\begin{minipage}{.35\textwidth}%
\begin{minted}[fontsize=\footnotesize]{haskell}
class Show a where
  show :: a -> String
  showsPrec :: Nat -> a -> ShowS
  showList :: [a] -> ShowS
  {-# MINIMAL showsPrec | show #-}
  show x = showsPrec 0 x ""
  showList = defaultShowList
             (showsPrec 0)
  showsPrec _ x s = show x ++ s
\end{minted}
\end{minipage}

\end{frame}

\begin{frame}[fragile]{Minimal Instance}

\hspace{-1cm}
\begin{minipage}{.59\textwidth}%
\begin{code}
instance
  ShowMaybe : {{Show a}} → Show (Maybe a)
  ShowMaybe {a = a} = record {Show₁ s₁}
    where
      s₁ : Show₁ (Maybe a)
      s₁ .Show₁.showsPrec n = λ where
        Nothing   → showString "nothing"
        (Just x)  → showParen True
          ( showString "just " ∘ showsPrec 10 x )
{-# COMPILE AGDA2HS ShowMaybe #-}
\end{code}
\end{minipage}\hspace{-.6cm}\vrule\hspace{.05cm}
\begin{minipage}{.41\textwidth}%
\begin{minted}[fontsize=\footnotesize]{haskell}
instance (Show a)
      => Show (Maybe a) where
  showsPrec n = \case
    Nothing -> showString "nothing"
    (Just x) -> showParen True
      (showString "just " . showsPrec 10 x)
\end{minted}
\end{minipage}

\end{frame}

\begin{frame}[fragile]{IOG use case}

\begin{code}[hide]
-- open import Haskell.Prelude

sym : {@0 A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {@0 A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {@0 A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : {@0 A : Set} {x y : A} → (P : A → Set) → x ≡ y → P x → P y
subst P refl p = p

begin_ : {@0 A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_∎ : {@0 A : Set} → (x : A) → x ≡ x
x ∎ = refl

_=⟨_⟩_ : {@0 A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {@0 A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix 1 begin_
infix 3 _∎
infixr 2 _=⟨_⟩_
infixr 2 _=⟨⟩_

cong2 : {@0 A B C : Set} → (f : A → B → C)
  → {a a' : A} → a ≡ a' → {b b' : B}
  → b ≡ b' → f a b ≡ f a' b'
cong2 f refl refl = refl

variable @0 n n' n'' n′ n″ : Set
\end{code}

\begin{minipage}{.54\textwidth}

\hspace{-1cm}
\begin{code}
data Kind : Set where
  Star   :  Kind
  _:=>_  :  Kind → Kind → Kind
data Type (n : Set) : Set where
  TyVar     :  n → Type n
  TyFun     :  Type n → Type n → Type n
  TyForall  :  Kind → Type (Maybe n)
    → Type n
  TyLam     :  Type (Maybe n) → Type n
  TyApp     :  Type n → Type n → Kind
    → Type n
ren : (n → n' ) → Type n → Type n'
sub : (n → Type n' ) → Type n → Type n'
\end{code}
\begin{code}[hide]
{-# COMPILE AGDA2HS Kind #-}
{-# COMPILE AGDA2HS Type #-}
\end{code}
\end{minipage}\hspace{-.75cm}\vrule\hspace{.2cm}
\begin{minipage}{.45\textwidth}
\begin{minted}[fontsize=\footnotesize]{Haskell}
data Kind
  = Star
  | Kind :=> Kind

data Type n
  = TyVar n
  | TyFun (Type n) (Type n)
  | TyForall Kind (Type (Maybe n))
  | TyLam (Type (Maybe n))
  | TyApp (Type n) (Type n) Kind

ren :: (n -> n') -> Type n -> Type n'
sub :: (n -> Type n') -> Type n -> Type n'
\end{minted}
\end{minipage}

\end{frame}

\begin{frame}[fragile]{IOG use case: Laws}

\AgdaFunction{ren} is a \textit{functorial map} on \AgdaDatatype{Type}.
\begin{itemize}
\item \begin{code}[inline]
ren-id    : (ty : Type n) → ren id ty ≡ ty
\end{code}
\item \begin{code}[inline]
ren-comp  : (ty : Type n) (ρ : n → n'  ) (ρ' : n' → n'' )
          → ren (ρ' ∘ ρ) ty ≡ ren ρ' (ren ρ ty)
\end{code}
\end{itemize}

\pause

\AgdaFunction{sub} is a \textit{monadic bind} on \AgdaDatatype{Type}.
\begin{itemize}
\item \begin{code}[inline]
sub-id    : (t : Type n) → sub TyVar t ≡ t
\end{code}
\item \begin{code}[inline]
sub-var   : (x : n) (σ : n → Type n' ) → sub σ (TyVar x) ≡ σ x
\end{code}
\item \begin{code}[inline]
sub-comp  : (ty : Type n) (σ : n → Type n' ) (σ' : n' → Type n'' )
          → sub (sub σ' ∘ σ) ty ≡ sub σ' (sub σ ty)
\end{code}
\end{itemize}

\begin{code}[hide]
-- extend a renaming by a bound variable
ext : (n → n') → Maybe n → Maybe n'
ext _ Nothing  = Nothing
ext f (Just x) = Just (f x)

ren f (TyVar x) = TyVar (f x)
ren f (TyFun ty1 ty2) = TyFun (ren f ty1) (ren f ty2)
ren f (TyForall k ty) = TyForall k (ren (ext f) ty)
ren f (TyLam ty) = TyLam (ren (ext f) ty)
ren f (TyApp ty1 ty2 k) = TyApp (ren f ty1) (ren f ty2) k

{-# COMPILE AGDA2HS ren #-}

ext-cong : {ρ ρ' : n → n'} → (∀ x → ρ x ≡ ρ' x) → ∀ x → ext ρ x ≡ ext ρ' x
ext-cong p Nothing     = refl
ext-cong p (Just x)    = cong Just (p x)

ren-cong : {ρ ρ' : n → n'} → (∀ x → ρ x ≡ ρ' x) → ∀ t → ren ρ t ≡ ren ρ' t
ren-cong p (TyVar x)          = cong TyVar (p x)
ren-cong p (TyFun ty1 ty2)    = cong2 TyFun (ren-cong p ty1) (ren-cong p ty2)
ren-cong p (TyForall k ty)    = cong (TyForall k) (ren-cong (ext-cong p) ty)
ren-cong p (TyLam ty)         = cong TyLam (ren-cong (ext-cong p) ty)
ren-cong p (TyApp ty1 ty2 k)  =
  cong2 (λ ty1 ty2 → TyApp ty1 ty2 k) (ren-cong p ty1) (ren-cong p ty2)

ext-id : (x : Maybe n) → ext id x ≡ x
ext-id Nothing  = refl
ext-id (Just x) = refl

ren-id (TyVar _)          = refl
ren-id (TyFun ty1 ty2)    = cong2 TyFun (ren-id ty1) (ren-id ty2)
ren-id (TyForall k ty)    =
  cong (TyForall k) (trans (ren-cong ext-id ty) (ren-id ty))
ren-id (TyLam ty)         =
  cong TyLam (trans (ren-cong ext-id ty) (ren-id ty))
ren-id (TyApp ty1 ty2 k)  =
  cong2 (λ ty1 ty2 → TyApp ty1 ty2 k) (ren-id ty1) (ren-id ty2)

ext-comp : (x : Maybe n)(ρ : n → n')(ρ' : n' → n'')
         → ext (ρ' ∘ ρ) x ≡ ext ρ' (ext ρ x)
ext-comp Nothing  ρ ρ' = refl
ext-comp (Just x) ρ ρ' = refl

ren-comp (TyVar x)          ρ ρ' = refl
ren-comp (TyFun ty1 ty2)    ρ ρ' =
  cong2 TyFun (ren-comp ty1 ρ ρ') (ren-comp ty2 ρ ρ')
ren-comp (TyForall k ty)    ρ ρ' = cong
  (TyForall k)
  (trans (ren-cong (λ x → ext-comp x ρ ρ') ty)
         (ren-comp ty (ext ρ) (ext ρ')))
ren-comp (TyLam ty)         ρ ρ' = cong
  TyLam
  (trans (ren-cong (λ x → ext-comp x ρ ρ') ty)
         (ren-comp ty (ext ρ) (ext ρ')))
ren-comp (TyApp ty1 ty2 k)  ρ ρ' =
  cong2 (λ ty1 ty2 → TyApp ty1 ty2 k) (ren-comp ty1 ρ ρ') (ren-comp ty2 ρ ρ')

-- |Extend type substitutions.
exts : (n → Type n') → Maybe n → Type (Maybe n')
exts _ Nothing  = TyVar Nothing
exts s (Just i) = ren Just (s i)

-- |Simultaneous substitution of type variables.
sub s (TyVar i)             = s i
sub s (TyFun ty1 ty2)       =
  TyFun (sub s ty1) (sub s ty2)
sub s (TyForall k ty)       = TyForall k (sub (exts s) ty)
sub s (TyLam ty)            = TyLam (sub (exts s) ty)
sub s (TyApp ty1 ty2 k)     =
  TyApp (sub s ty1) (sub s ty2) k

{-# COMPILE AGDA2HS sub #-}

exts-cong : {σ σ' : n → Type n'} → (∀ x → σ x ≡ σ' x)
          → ∀ x → exts σ x ≡ exts σ' x
exts-cong p Nothing  = refl
exts-cong p (Just x) = cong (ren Just) (p x)

sub-cong : {σ σ' : n → Type n'} → (∀ x → σ x ≡ σ' x)
         → ∀ ty → sub σ ty ≡ sub σ' ty
sub-cong p (TyVar x)          = p x
sub-cong p (TyFun ty1 ty2)    = cong2 TyFun (sub-cong p ty1) (sub-cong p ty2)
sub-cong p (TyForall k ty)    = cong (TyForall k) (sub-cong (exts-cong p) ty)
sub-cong p (TyLam ty)         = cong TyLam (sub-cong (exts-cong p) ty)
sub-cong p (TyApp ty1 ty2 k)  =
  cong2 (λ ty1 ty2 → TyApp ty1 ty2 k) (sub-cong p ty1) (sub-cong p ty2)

exts-id : (x : Maybe n) → exts TyVar x ≡ TyVar x
exts-id Nothing  = refl
exts-id (Just x) = refl

sub-id (TyVar x)          = refl
sub-id (TyFun ty1 ty2)    = cong2 TyFun (sub-id ty1) (sub-id ty2)
sub-id (TyForall k ty)    = cong
  (TyForall k)
  (trans (sub-cong exts-id ty) (sub-id ty))
sub-id (TyLam ty)         = cong
  TyLam
  (trans (sub-cong exts-id ty) (sub-id ty))
sub-id (TyApp ty1 ty2 k)  = cong2
  (λ ty1 ty2 → TyApp ty1 ty2 k)
  (sub-id ty1)
  (sub-id ty2)

sub-var x σ = refl


exts-ext : (x : Maybe n)(ρ : n → n')(σ : n' → Type n'')
         → exts (σ ∘ ρ) x ≡ exts σ (ext ρ x)
exts-ext Nothing  σ ρ = refl
exts-ext (Just x) σ ρ = refl

sub-ren : (t : Type n)(ρ : n → n')(σ : n' → Type n'')
         → sub (σ ∘ ρ) t ≡ sub σ (ren ρ t)
sub-ren (TyVar x)          ρ σ = refl
sub-ren (TyFun ty1 ty2)    ρ σ =
  cong2 TyFun (sub-ren ty1 ρ σ) (sub-ren ty2 ρ σ)
sub-ren (TyForall k ty)    ρ σ = cong
  (TyForall k)
  (trans (sub-cong (λ x → exts-ext x ρ σ) ty)
         (sub-ren ty (ext ρ) (exts σ)))
sub-ren (TyLam ty)         ρ σ = cong
  TyLam
  (trans (sub-cong (λ x → exts-ext x ρ σ) ty)
         (sub-ren ty (ext ρ) (exts σ)))
sub-ren (TyApp ty1 ty2 k)  ρ σ =
  cong2 (λ ty1 ty2 → TyApp ty1 ty2 k) (sub-ren ty1 ρ σ) (sub-ren ty2 ρ σ)

ext-exts : (x : Maybe n)(σ : n → Type n')(ρ : n' → n'')
         → exts (ren ρ ∘ σ) x ≡ ren (ext ρ) (exts σ x)
ext-exts Nothing  σ ρ = refl
ext-exts (Just x) σ ρ = trans
  (sym (ren-comp (σ x) ρ Just))
  (ren-comp (σ x) Just (ext ρ))

ren-sub : (t : Type n)(σ : n → Type n')(ρ : n' → n'')
         → sub (ren ρ ∘ σ) t ≡ ren ρ (sub σ t)
ren-sub (TyVar x)          σ ρ = refl
ren-sub (TyFun ty1 ty2)    σ ρ =
  cong2 TyFun (ren-sub ty1 σ ρ) (ren-sub ty2 σ ρ)
ren-sub (TyForall k ty)    σ ρ = cong
  (TyForall k)
  (trans (sub-cong (λ x → ext-exts x σ ρ) ty)
         (ren-sub ty (exts σ) (ext ρ)))
ren-sub (TyLam ty)         σ ρ = cong
  TyLam
  (trans (sub-cong (λ x → ext-exts x σ ρ) ty)
         (ren-sub ty (exts σ) (ext ρ)))
ren-sub (TyApp ty1 ty2 k)  σ ρ =
  cong2 (λ ty1 ty2 → TyApp ty1 ty2 k) (ren-sub ty1 σ ρ) (ren-sub ty2 σ ρ)

exts-comp : (x : Maybe n)(σ : n → Type n')(σ' : n' → Type n'')
         → exts (sub σ' ∘ σ) x ≡ sub (exts σ') (exts σ x)
exts-comp Nothing     σ σ' = refl
exts-comp (Just x) σ σ' = trans
  (sym (ren-sub (σ x) σ' Just))
  (sub-ren (σ x) Just (exts σ'))

sub-comp (TyVar x)          σ σ' = refl
sub-comp (TyFun ty1 ty2)    σ σ' =
  cong2 TyFun (sub-comp ty1 σ σ') (sub-comp ty2 σ σ')
sub-comp (TyForall k ty)    σ σ' = cong
  (TyForall k)
  (trans (sub-cong (λ x → exts-comp x σ σ') ty)
         (sub-comp ty (exts σ) (exts σ')))
sub-comp (TyLam ty)         σ σ' = cong
  TyLam
  (trans (sub-cong (λ x → exts-comp x σ σ') ty)
         (sub-comp ty (exts σ) (exts σ')))
sub-comp (TyApp ty1 ty2 k)  σ σ' =
  cong2 (λ ty1 ty2 → TyApp ty1 ty2 k) (sub-comp ty1 σ σ') (sub-comp ty2 σ σ')
\end{code}

\end{frame}

\begin{frame}[fragile]{Correctness}

How do we know the translation is \textbf{sound}?
\begin{enumerate}
\item Trust the ported Prelude and defined primitives
\item Ensure all dependent types appear under \textit{erased} positions
\item Ensure source code also adheres to Haskell's naming conventions
  \begin{itemize}
  \item this check is actually relegated to GHC! \hspace{.5cm}\agdaHsLove{}
  \end{itemize}
\end{enumerate}

\begin{alertblock}{NOTE}
all functions are total $\Rightarrow$ evaluation order doesn't matter
\end{alertblock}

\end{frame}

\setbeamertemplate{headline}{\hfill\largeImg{agda2hs-qrcode}\hspace{0.2cm}\vspace{-4cm}}
\begin{frame}[fragile]{Implementation \hfill \alert{\small\texttt{https://github.com/agda/agda2hs}}}

\tikzset{
  every matrix/.style =
  { ampersand replacement = \&,
    matrix of nodes,
    nodes in empty cells },
  box/.style =
  { draw, rectangle,
    rounded corners = 1mm,
    minimum width  = 2cm,
    minimum height = 1cm },
  to/.style = {->, thick}
}

\begin{tikzpicture}
  \matrix (mat) [row sep = 1.2cm, every node/.style = {align=center}, font=\Large] {
    \node (src) {Agda Input}; \\
    \node[box] (agda) {Agda}; \\
    \node[box] (trans) {\agdatohs}; \\
    \node (hs) {Haskell}; \\
  };
  \path
  (src)
    edge[to]
    node[right] {surface syntax}
  (agda) (agda)
    edge[to]
    node[right] {(type-checked) internal core representation}
  (trans) (trans)
    edge[to, color=mLightBrown]
    node[right] {\hs{:: Agda.AST -> Agda.TC Haskell.AST}}
  (hs)
  ;
\end{tikzpicture}

\end{frame}
\setbeamertemplate{headline}{}

\begin{frame}[fragile]{Implementation: \AgdaKeyword{where} clauses}

\begin{minipage}{.33\textwidth}%
\textbf{\underline{Surface}}

\begin{code}[hide]
module Ex1 where
\end{code}
\begin{code}
  f : Nat → Nat
  f x = go
    where
      go = TODO
      -- may use x
\end{code}
\end{minipage}\hspace{-1cm}\vrule\hspace{.5cm}
\begin{minipage}{.33\textwidth}%
\textbf{\underline{Intermediate}}

\begin{code}[hide]
module Ex2 where
\end{code}
\begin{code}
  go : Nat → Nat
  go x = TODO

  f : Nat → Nat
  f x = go x
\end{code}
\end{minipage}\hspace{-1cm}\vrule\hspace{.5cm}
\begin{minipage}{.33\textwidth}%
\begin{center}\textbf{\underline{Output}}\end{center}

\begin{minted}{haskell}
f :: Natural -> Natural
f x = go
  where go = TODO
\end{minted}
\end{minipage}

\end{frame}

\begin{frame}[fragile]{Future work}

Still many unsupported Haskell features:
\begin{itemize}
\item GADTs
\onslide<2->{\alert{$\sim$ identify subset of dependent types}}
\item pattern guards, views
\onslide<2->{\alert{$\sim$ use \AgdaKeyword{with}-matching}}
\item 32-bit arithmetic
\onslide<2->{\alert{$\sim$ first add to Agda itself}}
\item Infinite data
\onslide<2->{\alert{$\sim$ coinductive types}}
\item Non-termination, general recursion
\onslide<2->{\alert{$\sim$ partiality/general monad}}
\end{itemize}

\onslide<3->{
Extra goodies:
\begin{itemize}
\item Generate \textbf{runtime checks} for decidable properties
\item \textbf{QuickCheck} postulated properties
\item \textsc{hs2agda}: inverse translation
$\Rightarrow$ streamline porting of \textbf{existing} libraries
\end{itemize}
}

\onslide<4->{
More \textbf{applications} $+$ \textbf{comparisons} with LiquidHaskell, \texttt{hs-to-coq}, etc..
}

\end{frame}

\setbeamertemplate{headline}{\hfill\largeImg{aim-qrcode}\hspace{0.2cm}\vspace{-6cm}}
\begin{frame}[fragile]{Shameless plug
\hfill \alert{\small\texttt{https://wiki.portal.chalmers.se/agda/Main/AIMXXXI}}}

\agdatohs was developed during the last two \textbf{Agda Implementors' Meetings}
\begin{itemize}
\item biannual event where Agda users of all levels hack on Agda, its ecosystem, etc..
\end{itemize}

\textbf{AIM XXXI} in Edinburgh November 10-16, will include:
\begin{itemize}
\item talks
\item coding sprints
\item EuroProofNet day dedicated to the topic of large formal libraries
\item a hike along the Scottish seaside ~ \img{.9em}{whisky}
\end{itemize}

\pause

\begin{center}
\largeImg{join}
\end{center}

\end{frame}
\setbeamertemplate{headline}{}

\setbeamertemplate{headline}{\vfill\largeImg{agda2hs-qrcode}\hfill\largeImg{aim-qrcode}}
\begin{frame}[standout]
Questions?
\end{frame}
\setbeamertemplate{headline}{}

\end{document}
