\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude hiding (_─_)
open import Hash

open import Protocol.Streamlet.Base
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Local.Step (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet.Block ⋯
open import Protocol.Streamlet.Message ⋯
open import Protocol.Streamlet.Local.Chain ⋯
open import Protocol.Streamlet.Local.State ⋯

open L.Any using (_─_)

_─¹_ : ∀ {A : Type}{P : A → Type} (xs : List A) → AnyFirst P xs  → List A
xs ─¹ p = xs ─ AnyFirst⇒Any p

_∈¹_ : ∀ {A : Type} → A → List A → Type
x ∈¹ xs = AnyFirst (x ≡_) xs

proposeBlock : LocalState → Message → LocalState
proposeBlock ls m = record ls
  { phase = Voted
  ; db    = m ∷ ls .db
  }

voteBlock : (ls : LocalState) → AnyFirst (m ≡_) (ls .inbox) → Message → LocalState
voteBlock {m} ls m∈ vote = record ls
  { db    = vote ∷ m ∷ ls .db
  ; phase = Voted
  ; inbox = ls .inbox ─¹ m∈
  }

registerVote : (ls : LocalState) → m ∈ ls .inbox → LocalState
registerVote {m} ls m∈ = record ls
  { db    = m ∷ ls .db
  ; inbox = ls .inbox L.Any.─ m∈
  }

finalize : Chain → Op₁ LocalState
finalize ch ls = record ls
  { final = ch}
      -- p ▷ e ⊢ ls —[ just m ]→ proposeBlock ls m
      -- p ▷ e ⊢ ls —[ just m ]→ voteBlock ls m∈ m
      -- p ▷ e ⊢ ls —[ nothing ]→ registerVote ls m∈
      -- p ▷ e ⊢ ls —[ nothing ]→ finalize ch ls

\end{code}

\newcommand\localStepType{%
\begin{code}
data _▷_⊢_—[_]→_ (p : Pid) (e : Epoch) (ls : LocalState) : Maybe Message → LocalState → Type
\end{code}
}

\newcommand\localStepPropose{%
\begin{AgdaMultiCode}
\hspace{-1cm}
\begin{code}
data _▷_⊢_—[_]→_ p e ls where

  ProposeBlock :
    let L  = epochLeader e
        b  = ⟨ ch ♯ , e , txs ⟩
        m  = Propose (sign p b)
    in
\end{code}

\vspace{-3mm}
\noindent
\begin{minipage}[t]{0.3\textwidth}
 \begin{code}
    ∙ ls .phase ≡ Ready
    ∙ p ≡ L
 \end{code}
 \hfill
\end{minipage}%
\begin{minipage}[t]{0.49\textwidth}
\begin{code}
    ∙ ch longest-notarized-chain-∈ ls .db
    ∙ ValidChain (b ∷ ch)
\end{code}
\end{minipage}%
\begin{code}
    ─────────────────────────────────────────────────────────────────
    p ▷ e ⊢ ls —[ just m ]→ record ls { phase = Voted; db = m ∷ ls .db }
\end{code}
\end{AgdaMultiCode}
}
\newcommand\localStepVote{%
\setlength{\mathindent}{0pt}
\begin{AgdaMultiCode}
\begin{code}
  VoteBlock :
    let L    = epochLeader e
        b    = ⟨ ch ♯ , e , txs ⟩
        sbᴸ  = sign L b
        mᴸ   = Propose sbᴸ; m    = Vote (sign p b)
    in
\end{code}

\vspace{-3mm}
\noindent
\begin{minipage}[t]{0.50\textwidth}
 \begin{code}
    ∀ (m∈ : mᴸ ∈¹ ls .inbox) →
    ∙ sbᴸ ∉ map _∙signedBlock (ls .db)
    ∙ ls .phase ≡ Ready
 \end{code}
 \hfill
\end{minipage}%
\begin{minipage}[t]{0.49\textwidth}
\begin{code}
    ∙ p ≢ L
    ∙ ch longest-notarized-chain-∈ ls .db
    ∙ ValidChain (b ∷ ch)
\end{code}
\end{minipage}%
\begin{code}
    ───────────────────────────────────────────────────────────────────────────────────────
    p ▷ e ⊢ ls —[ just m ]→ record ls { phase = Voted; db = m ∷ mᴸ ∷ ls .db; inbox = ls .inbox ─¹ m∈ }
\end{code}
\setlength{\mathindent}{4pt}
\end{AgdaMultiCode}
}

\newcommand\localStepRegister{%
\begin{code}
  RegisterVote : let m = Vote sb in
    ∀ (m∈ : m ∈ ls .inbox) →
    ∙ sb ∉ map _∙signedBlock (ls .db)
    ─────────────────────────────────────────────────────────────────────────
    p ▷ e ⊢ ls —[ nothing ]→ record ls { db = m ∷ ls .db; inbox = ls .inbox ─ m∈ }
\end{code}
}

\newcommand\localStepFinalize{%
\begin{AgdaMultiCode}
\begin{code}
  FinalizeBlock : ∀ ch b →
\end{code}

\vspace{-3mm}
\noindent
\begin{minipage}[t]{0.3\textwidth}
 \begin{code}
    ∙ ValidChain (b ∷ ch)
 \end{code}
 \hfill
\end{minipage}%
\begin{minipage}[t]{0.49\textwidth}
\begin{code}
    ∙ FinalizedChain (ls .db) ch b
\end{code}
\end{minipage}%
\begin{code}
    ─────────────────────────────────────────────────────────
    p ▷ e ⊢ ls —[ nothing ]→ record ls { final = ch }
\end{code}
\end{AgdaMultiCode}
}

\begin{code}[hide]
epochChange : Op₁ LocalState
epochChange ls = record ls
  { phase = Ready }

receiveMessage : Message → Op₁ LocalState
receiveMessage m ls = record ls
  { inbox = ls .inbox L.∷ʳ m }
\end{code}
