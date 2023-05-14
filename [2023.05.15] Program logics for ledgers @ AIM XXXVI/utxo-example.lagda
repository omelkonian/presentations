\documentclass[main]{subfiles}
\begin{document}
\begin{frame}{UTxO: Example transaction graph}
\begin{code}[hide]
{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality.Rewrite

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable hiding (auto)
open import Prelude.Lists hiding (_↦_)
open import Prelude.Lists.Dec
open import Prelude.Apartness
open import Prelude.Nary

-- open import UTxOErr.Maps
open import Prelude.Maps
open import UTxOErr.UTxO
open import UTxOErr.Ledger hiding (⟦_⟧)
open import UTxOErr.HoareLogic
open import UTxOErr.HoareProperties
open import UTxOErr.SL using () renaming (ℝ[FRAME] to [FRAME])
-- open import UTxOErr.CSL using () renaming (ℝ[PAR] to [PAR])
open HoareReasoning
postulate
  [PAR] :
    l₁ ∥ l₂ ≡ l
    → l₁ ∥ l₂ ≡ l
    → ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
    → ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
    → ℝ⟨ P₁ ∗ P₂ ⟩ l ⟨ Q₁ ∗ Q₂ ⟩
\end{code}
\begin{code}
A B C D : Address
\end{code}
\begin{code}[hide]
A = 111; B = 222; C = 333; D = 444

postulate t₀ : Tx
t₀₀ = (t₀ ♯) indexed-at 0
t₀₁ = (t₀ ♯) indexed-at 1

postulate
  mkValidator : TxOutputRef → (TxInfo → DATA → Bool)
  in₁ : (mkValidator t₀₀) ♯ ≡ A
  in₂ : (mkValidator t₀₁) ♯ ≡ D
{-# REWRITE in₁ #-}
{-# REWRITE in₂ #-}

_—→⟨_∣_⟩_ : Address → Value → TxOutputRef → Address → Tx
A —→⟨ v ∣ or ⟩ B = record
  { inputs  = [ record { outputRef = or ; validator = mkValidator or; redeemer = 0 } ]
  ; outputs = [ 1 at B ]
  ; forge   = 0
  }

t₁ t₂ t₃ t₄ : Tx
-- t₀ = record {inputs = []; outputs = 1 at A ∷ 1 at D ∷ []; forge = 2}
t₁ = A —→⟨ 1 ∣ t₀₀ ⟩ B
t₂ = D —→⟨ 1 ∣ t₀₁ ⟩ C
postulate
  vt₁ : Resolved t₁; val₁ : T $ mkValidator t₀₀ (mkTxInfo t₁ vt₁) 0
  vt₂ : Resolved t₂; val₂ : T $ mkValidator t₀₁ (mkTxInfo t₂ vt₂) 0
t₁₀ = (t₁ ♯) indexed-at 0
t₂₀ = (t₂ ♯) indexed-at 0
postulate
  in₃ : (mkValidator t₁₀) ♯ ≡ B
  in₄ : (mkValidator t₂₀) ♯ ≡ C
{-# REWRITE in₃ #-}
{-# REWRITE in₄ #-}

t₃ = B —→⟨ 1 ∣ t₁₀ ⟩ A
t₄ = C —→⟨ 1 ∣ t₂₀ ⟩ D
postulate
  vt₃ : Resolved t₃; val₃ : T $ mkValidator t₁₀ (mkTxInfo t₃ vt₃) 0
  vt₄ : Resolved t₄; val₄ : T $ mkValidator t₂₀ (mkTxInfo t₄ vt₄) 0
t₃₀ = (t₃ ♯) indexed-at 0
t₄₀ = (t₄ ♯) indexed-at 0

postulate ⋯ : ∀ {A : Set ℓ} → A

auto : ⟦ t₁ , t₃ ⟧ ∥ ⟦ t₂ , t₄ ⟧ ≡ (L ∋ ⟦ t₁ , t₂ , t₃ , t₄ ⟧)
auto = keepˡ keepʳ keepˡ keepʳ []
\end{code}
\begin{code}
t₁-₄ = L ∋ ⟦ t₁ , t₂ , t₃ , t₄ ⟧
\end{code}
\vspace{1cm}
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
\begin{frame}[fragile]{UTxO: Example derivation (monolithic)}
\begin{code}
_ : ⟨ t₀₀ ↦ 1 at A ∗ t₀₁ ↦ 1 at D ⟩ t₁-₄ ⟨ t₃₀ ↦ 1 at A ∗ t₄₀ ↦ 1 at D ⟩
_ = begin t₀₀ ↦ 1 at A ∗ t₀₁ ↦ 1 at D ~⟨ t₁ ∶- [FRAME] (t₀₁ ↦ 1 at D) t₁♯ ⋯ ⟩
          t₁₀ ↦ 1 at B ∗ t₀₁ ↦ 1 at D ~⟪ ∗↔ ⟩
          t₀₁ ↦ 1 at D ∗ t₁₀ ↦ 1 at B ~⟨ t₂ ∶- [FRAME] (t₁₀ ↦ 1 at B) t₂♯ ⋯ ⟩
          t₂₀ ↦ 1 at C ∗ t₁₀ ↦ 1 at B ~⟪ ∗↔ ⟩
          t₁₀ ↦ 1 at B ∗ t₂₀ ↦ 1 at C ~⟨ t₃ ∶- [FRAME] (t₂₀ ↦ 1 at C) t₃♯ ⋯ ⟩
          t₃₀ ↦ 1 at A ∗ t₂₀ ↦ 1 at C ~⟪ ∗↔ ⟩
          t₂₀ ↦ 1 at C ∗ t₃₀ ↦ 1 at A ~⟨ t₄ ∶- [FRAME] (t₃₀ ↦ 1 at A) t₄♯ ⋯ ⟩
          t₄₀ ↦ 1 at D ∗ t₃₀ ↦ 1 at A ~⟪ ∗↔ ⟩
          t₃₀ ↦ 1 at A ∗ t₄₀ ↦ 1 at D ∎
  where postulate t₁♯ : [ t₁ ] ♯ (t₀₁ ↦ 1 at D)
                  t₂♯ : [ t₂ ] ♯ (t₁₀ ↦ 1 at B)
                  t₃♯ : [ t₃ ] ♯ (t₂₀ ↦ 1 at C)
                  t₄♯ : [ t₄ ] ♯ (t₃₀ ↦ 1 at A)
\end{code}
\end{frame}
\begin{frame}{UTxO: Example derivation (modular)}
\begin{code}
_ : ⟨ t₀₀ ↦ 1 at A ∗ t₀₁ ↦ 1 at D ⟩ t₁-₄ ⟨ t₃₀ ↦ 1 at A ∗ t₄₀ ↦ 1 at D ⟩
_ = begin t₀₀ ↦ 1 at A ∗ t₀₁ ↦ 1 at D ~⟨ t₁-₄ ∶- [PAR] ⋯ auto H₁ H₂ ⟩++
          t₃₀ ↦ 1 at A ∗ t₄₀ ↦ 1 at D ∎
  where
    H₁ : ⟨ t₀₀ ↦ 1 at A ⟩ t₁ ∷ t₃ ∷ [] ⟨ t₃₀ ↦ 1 at A ⟩
    H₁ = begin t₀₀ ↦ 1 at A ~⟨ t₁ ∶- ⋯ ⟩
               t₁₀ ↦ 1 at B ~⟨ t₃ ∶- ⋯ ⟩
               t₃₀ ↦ 1 at A ∎
    H₂ : ⟨ t₀₁ ↦ 1 at D ⟩ t₂ ∷ t₄ ∷ [] ⟨ t₄₀ ↦ 1 at D ⟩
    H₂ = begin t₀₁ ↦ 1 at D ~⟨ t₂ ∶- ⋯ ⟩
               t₂₀ ↦ 1 at C ~⟨ t₄ ∶- ⋯ ⟩
               t₄₀ ↦ 1 at D ∎
\end{code}
\end{frame}
\end{document}
