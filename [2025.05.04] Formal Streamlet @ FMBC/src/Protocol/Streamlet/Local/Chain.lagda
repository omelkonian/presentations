\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Base
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Local.Chain (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet.Block ⋯

-- exporting here because cannot declare in `Assumptions` record
-- * ERROR: Cannot use generalized variable from let-opened module: ⋯
variable
  p p′ : Pid
  txs txs′ : List Transaction
\end{code}

\newcommand\chain{%
\begin{code}
Chain = List Block
\end{code}
}

\begin{code}[hide]
variable ch ch′ : Chain

genesisChain = Chain ∋ []

instance HasEpoch-Chain = HasEpoch Chain ∋ λ where ._∙epoch → λ where
  []      → 0
  (b ∷ _) → b .epoch
\end{code}

\newcommand\connects{%
\begin{AgdaMultiCode}
\begin{code}
record _-connects-to-_ (b : Block) (ch : Chain) : Type where
\end{code}
\begin{code}[hide]
  constructor connects∶
\end{code}
\hspace{1em}\begin{minipage}{.5\textwidth}
\begin{code}
  field  hashesMatch    : b .parentHash  ≡  ch ♯
         epochAdvances  : b .epoch       >  ch ∙epoch
\end{code}
\end{minipage}
\end{AgdaMultiCode}
}

\newcommand\validChain{%
\AgdaNoSpaceAroundCode{}
\begin{AgdaMultiCode}
\begin{code}
data ValidChain : Chain → Type where
\end{code}

\vspace{-3mm}
\begin{minipage}[t]{0.35\textwidth}
 \begin{code}
  [] :
       ─────────────
       ValidChain []
 \end{code}
 \hfill
\end{minipage}%
\begin{minipage}[t]{0.49\textwidth}
\begin{code}
  _∷_⊣_ : ∀ b →
\end{code}

\vspace{-3mm}
\noindent
\begin{minipage}[t]{.38\textwidth}
\begin{code}
    ∙ ValidChain ch
\end{code}
\end{minipage}%
\hspace{3mm}
\begin{minipage}[t]{.5\textwidth}
\begin{code}
    ∙ b -connects-to- ch
\end{code}
\end{minipage}%
\begin{code}
    ────────────────────────────────────
    ValidChain (b ∷ ch)
\end{code}
\end{minipage}
\end{AgdaMultiCode}
\AgdaSpaceAroundCode{}
}

\begin{code}[hide]
open _-connects-to-_ public

variable vch vch′ : ValidChain ch

uncons-vc : ValidChain (b ∷ ch) → ValidChain ch
uncons-vc (_ ∷ p ⊣ _) = p

connects-to≡ :
  ∙ b -connects-to- ch
  ∙ b -connects-to- ch′
    ─────────────────────
    ch ≡ ch′
connects-to≡ {ch = ch} {ch′ = ch′} b↝ b↝′ = ♯-inj ch♯≡
  where
  ch♯≡ : ch ♯ ≡ ch′ ♯
  ch♯≡ = trans (sym $ b↝ .hashesMatch) (b↝′ .hashesMatch)

b≡→ch≡ :
  ∙ ValidChain (b  ∷ ch)
  ∙ ValidChain (b′ ∷ ch′)
  ∙ b ≡ b′
    ─────────────────────
    ch ≡ ch′
b≡→ch≡ (_ ∷ _ ⊣ b↝) (_ ∷ _ ⊣ b↝′) refl = connects-to≡ b↝ b↝′

ch≢→b≢ :
  ∙ ValidChain (b  ∷ ch)
  ∙ ValidChain (b′ ∷ ch′)
  ∙ ch ≢ ch′
    ─────────────────────
    b ≢ b′
ch≢→b≢ vch vch′ = _∘ b≡→ch≡ vch vch′

∣ch∣≢→b≢ :
  ∙ ValidChain (b  ∷ ch)
  ∙ ValidChain (b′ ∷ ch′)
  ∙ length ch ≢ length ch′
    ─────────────────────
    b ≢ b′
∣ch∣≢→b≢ vch vch′ len≢ = ch≢→b≢ vch vch′ λ where refl → len≢ refl

-- chainLen≤epoch :
--   ValidChain ch
--   ─────────────────────
--   ch ∙epoch ≥ length ch

advancingEpochs :
  ValidChain ch
  ───────────────────────────────────
  All (λ b → b .epoch ≤ ch ∙epoch) ch
advancingEpochs [] = []
advancingEpochs {ch = b ∷ ch} (.b ∷ vch ⊣ b↝) =
  Nat.≤-refl ∷ L.All.map (λ {b′} → QED {b′}) (advancingEpochs vch)
  where
  QED : ∀ {b′} → b′ .epoch ≤ ch ∙epoch → b′ .epoch ≤ b .epoch
  QED b≤ = Nat.≤-trans b≤ (Nat.<⇒≤ $ b↝ .epochAdvances)

connects-to-epoch< :
  ∙ ValidChain ch
  ∙ b ∈ ch
  ∙ b′ -connects-to- ch
    ─────────────────────
    b .epoch < b′ .epoch
connects-to-epoch< vch b∈ b↝ =
  Nat.≤-<-trans (L.All.lookup (advancingEpochs vch) b∈) (b↝ .epochAdvances)

connects-to∉ :
  ∙ ValidChain ch
  ∙ b -connects-to- ch
    ──────────────────
    b ∉ ch
connects-to∉ {ch = b′ ∷ ch}{b} vch b↝ b∈ = Nat.<⇒≱ e> e≤
  where
  e> : b .epoch > b′ .epoch
  e> = b↝ .epochAdvances

  e≤ : b .epoch ≤ b′ .epoch
  e≤ = L.All.lookup (advancingEpochs vch) b∈

connect-to∈ :
  ∙ ValidChain ch
  ∙ ValidChain ch′
  ∙ b ∈ ch
  ∙ b -connects-to- ch′
    ──────────────────────
    length ch′ ≤ length ch
connect-to∈ (_ ∷ _ ⊣ b↝′) _ (here refl) b↝
  rewrite connects-to≡ b↝ b↝′ = Nat.n≤1+n _
connect-to∈ (_ ∷ vch ⊣ _) vch′ (there b∈) b↝
  = Nat.m≤n⇒m≤1+n $ connect-to∈ vch vch′ b∈ b↝
\end{code}
