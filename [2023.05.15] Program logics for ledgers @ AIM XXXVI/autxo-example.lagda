\documentclass[main]{subfiles}
\begin{document}
\begin{frame}{Abstract UTxO: Example transaction graph}
\begin{code}[hide]
{-# OPTIONS --rewriting --allow-unsolved-metas #-} -- to avoid eta-expansions
open import Agda.Builtin.Equality.Rewrite

open import Prelude.Init; open SetAsType
open Nat hiding (_≥_)
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable hiding (auto)
open import Prelude.Lists hiding (_↦_)
open import Prelude.Lists.Dec
open import Prelude.Ord
open import Prelude.InferenceRules
open import Prelude.Lists using (_∥_≡_)
open import Prelude.Nary

open import Prelude.Bags
open import ValueSepUTxO.UTxO
open import ValueSepUTxO.Ledger hiding (⟦_⟧)
open import ValueSepUTxO.HoareLogic
open import ValueSepUTxO.HoareProperties
open import ValueSepUTxO.SL using () renaming (ℝ[FRAME] to [FRAME])
open import ValueSepUTxO.CSL using () renaming (ℝ[PAR] to [PAR])
\end{code}
\begin{code}
A B C D : Address
\end{code}
\begin{code}[hide]
A = 111; B = 222; C = 333; D = 444

postulate t₀ : Tx
t₀₀ = (t₀ ♯) at 0
t₀₁ = (t₀ ♯) at 1

postulate
  mkValidator : TxOutput → (TxInfo → DATA → Bool)
  in₁ : (mkValidator t₀₀) ♯ ≡ A
  in₂ : (mkValidator t₀₁) ♯ ≡ D
{-# REWRITE in₁ #-}
{-# REWRITE in₂ #-}

_—→⟨_∣_⟩_ : Address → Value → TxOutput → Address → Tx
A —→⟨ v ∣ or ⟩ B = record
  { inputs  = [ record { outputRef = or ; validator = mkValidator or; redeemer = 0 } ]
  ; outputs = [ v at B ]
  ; forge   = 0
  }

t₁ t₂ t₃ t₄ : Tx
-- t₀ = record {inputs = []; outputs = 1 at A ∷ 1 at D ∷ []; forge = 2}
t₁ = A —→⟨ 1 ∣ t₀₀ ⟩ B
t₂ = D —→⟨ 1 ∣ t₀₁ ⟩ C

t₁₀ = (t₁ ♯) at 0
t₂₀ = (t₂ ♯) at 0
postulate
  in₃ : (mkValidator t₁₀) ♯ ≡ B
  in₄ : (mkValidator t₂₀) ♯ ≡ C
{-# REWRITE in₃ #-}
{-# REWRITE in₄ #-}

t₃ = B —→⟨ 1 ∣ t₁₀ ⟩ A
t₄ = C —→⟨ 1 ∣ t₂₀ ⟩ D

postulate ⋯ : ∀ {A : Set ℓ} → A

auto : ⟦ t₁ , t₃ ⟧ ∥ ⟦ t₂ , t₄ ⟧ ≡ (L ∋ ⟦ t₁ , t₂ , t₃ , t₄ ⟧)
auto = keepˡ keepʳ keepˡ keepʳ []

open HoareReasoning
module _ A B {or} {_ : auto∶ A ≢ B} where postulate
  _↝_ : ℝ⟨ A ↦ 1 ∗ B ↦ 0 ⟩ [ A —→⟨ 1 ∣ or ⟩ B ] ⟨ A ↦ 0 ∗ B ↦ 1 ⟩
  _↜_ : ℝ⟨ A ↦ 0 ∗ B ↦ 1 ⟩ [ B —→⟨ 1 ∣ or ⟩ A ] ⟨ A ↦ 1 ∗ B ↦ 0 ⟩
\end{code}
\begin{code}
t₁-₄ = L ∋ ⟦ t₁ , t₂ , t₃ , t₄ ⟧
\end{code}
\tikzset{
  tx/.style =
  { draw           = gray
  , shape          = rectangle
  , align          = center
  , minimum width  = .5cm
  , minimum height = 1.5cm
  }
, mid/.style =
  { draw
  , yshift       = .5cm
  , shape        = circle
  , inner sep    = 0pt
  , minimum size = 4pt
  }
, arg/.style =
  { anchor = center
  , align  = left
  , font   = \scriptsize
  }
, to/.style =
  { -
  , bend left = 30
  , thick
  }
, every matrix/.style =
  { column sep            = 2.2cm
  , row    sep            = 1cm
  , ampersand replacement = \&
  }
}
\begin{tikzpicture}
  \matrix (mat) [matrix of nodes, nodes in empty cells] {
     \node[mid,red] (iAB) {}; \& \node[tx] (AB) {t₁};
  \& \node[mid,red] (iBA) {}; \& \node[tx] (BA) {t₃};
  \& \node[mid,red] (oBA) {}; \& \node (finAB) {};
  \\ \node[mid,red] (iDC) {}; \& \node[tx] (DC) {t₂};
  \& \node[mid,red] (iCD) {}; \& \node[tx] (CD) {t₄};
  \& \node[mid,red] (oCD) {}; \& \node (finCD) {};
  \\
  };
  \path
  (iAB) edge[to, red]
  (AB) node[below] {1 locked by A}
  (AB) edge[to, black]
  (iBA)
  (iBA) edge[to, red]
  (BA) node[below] {1 locked by B}
  (BA) edge[to, black]
  (oBA)
  (oBA) edge[to, red]
  (finAB) node[below] {1 locked by A}
  (iDC) edge[to, red]
  (DC) node[below] {1 locked by D}
  (DC) edge[to, black]
  (iCD)
  (iCD) edge[to, red]
  (CD) node[below] {1 locked by C}
  (CD) edge[to, black]
  (oCD)
  (oCD) edge[to, red]
  (finCD) node[below] {1 locked by D}
  ;
\end{tikzpicture}
\end{frame}
\begin{frame}[fragile]{Abstract UTxO: Example derivation (monolithic)}
\begin{code}
_ : ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩ t₁-₄ ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
_ = begin A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1   ~⟪ ∗↝ ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟨ t₁ ∶- [FRAME] (C ↦ 0 ∗ D ↦ 1) (A ↝ B) ⟩
          (A ↦ 0 ∗ B ↦ 1) ∗ C ↦ 0 ∗ D ↦ 1 ~⟪ ∗↔ ⟩
          (C ↦ 0 ∗ D ↦ 1) ∗ A ↦ 0 ∗ B ↦ 1 ~⟨ t₂ ∶- [FRAME] (A ↦ 0 ∗ B ↦ 1) (C ↜ D) ⟩
          (C ↦ 1 ∗ D ↦ 0) ∗ A ↦ 0 ∗ B ↦ 1 ~⟪ ∗↔ ⟩
          (A ↦ 0 ∗ B ↦ 1) ∗ C ↦ 1 ∗ D ↦ 0 ~⟨ t₃ ∶- [FRAME] (C ↦ 1 ∗ D ↦ 0) (A ↜ B) ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 1 ∗ D ↦ 0 ~⟪ ∗↔ ⟩
          (C ↦ 1 ∗ D ↦ 0) ∗ A ↦ 1 ∗ B ↦ 0 ~⟨ t₄ ∶- [FRAME] (A ↦ 1 ∗ B ↦ 0) (C ↝ D) ⟩
          (C ↦ 0 ∗ D ↦ 1) ∗ A ↦ 1 ∗ B ↦ 0 ~⟪ ∗↔ ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟪ ↜∗ ⟩
          A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1   ∎
\end{code}
\end{frame}
\begin{frame}{Abstract UTxO: Example derivation (modular)}
\begin{code}
_ : ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩ t₁-₄ ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
_ = begin A ↦ 1 ∗ B ↦ 0   ∗ C ↦ 0 ∗ D ↦ 1  ~⟪ ∗↝ ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1  ~⟨ t₁-₄ ∶- [PAR] auto H₁ H₂ ⟩++
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1  ~⟪ ↜∗ ⟩
          A ↦ 1 ∗ B ↦ 0   ∗ C ↦ 0 ∗ D ↦ 1  ∎
  where
    H₁ : ℝ⟨ A ↦ 1 ∗ B ↦ 0 ⟩ t₁ ∷ t₃ ∷ [] ⟨ A ↦ 1 ∗ B ↦ 0 ⟩
    H₁ = A ↦ 1 ∗ B ↦ 0 ~⟨ t₁ ∶- A ↝ B ⟩
         A ↦ 0 ∗ B ↦ 1 ~⟨ t₃ ∶- A ↜ B ⟩
         A ↦ 1 ∗ B ↦ 0 ∎

    H₂ : ℝ⟨ C ↦ 0 ∗ D ↦ 1 ⟩ t₂ ∷ t₄ ∷ [] ⟨ C ↦ 0 ∗ D ↦ 1 ⟩
    H₂ = C ↦ 0 ∗ D ↦ 1 ~⟨ t₂ ∶- C ↜ D ⟩
         C ↦ 1 ∗ D ↦ 0 ~⟨ t₄ ∶- C ↝ D ⟩
         C ↦ 0 ∗ D ↦ 1 ∎
\end{code}
\end{frame}
\end{document}
