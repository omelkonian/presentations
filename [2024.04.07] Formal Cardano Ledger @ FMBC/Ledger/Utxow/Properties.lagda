\begin{code}[hide]
-- {-# OPTIONS --safe #-}

import Data.Maybe as M
open import Data.Product using (map₂)

open import Ledger.Prelude
open import Ledger.Crypto
open import Ledger.Abstract
open import Ledger.Transaction

module Ledger.Utxow.Properties
  (txs : _) (open TransactionStructure txs)
  (abs : AbstractFunctions txs) (open AbstractFunctions abs)
  where

open import Ledger.Utxow txs abs
open import Ledger.Utxo txs abs
\end{code}
\newcommand\utxowComp{%
\begin{AgdaAlign}
\begin{code}[hide]
instance
\end{code}
\begin{code}[inline]
  Computational-UTXOW : Computational _⊢_⇀⦇_,UTXOW⦈_
  Computational-UTXOW =
\end{code}~
\begin{code}[hide,inline]
    record {Go}
   where
     module Go
      Γ s tx (
\end{code}
\begin{code}[inline]
      let H , ⁇ H? = UTXOW-inductive-premises {tx}{s}{Γ}
\end{code}~
\begin{code}[hide,inline]
       )
\end{code}
\begin{code}[inline]
      where
\end{code}
\begin{code}[hide,inline]
      open Computational Computational-UTXO
        renaming (computeProof to computeProof'; completeness to completeness')
\end{code}
\begin{code}
      computeProof : Maybe $ ∃ (Γ ⊢ s ⇀⦇ tx ,UTXOW⦈_)
      computeProof = case H? of λ where
        (yes (p₁ , p₂ , p₃ , p₄ , p₅)) →
          map₂′ (UTXOW-inductive⋯ p₁ p₂ p₃ p₄ p₅) <$> computeProof' Γ s tx
        (no _) → nothing

      completeness : ∀ s' → Γ ⊢ s ⇀⦇ tx ,UTXOW⦈ s' → M.map proj₁ computeProof ≡ just s'
      completeness s' (UTXOW-inductive⋯ p₁ p₂ p₃ p₄ p₅ h)
        rewrite dec-yes H? (p₁ , p₂ , p₃ , p₄ , p₅) .proj₂
        with computeProof' Γ s tx | completeness' _ _ _ _ h
      ... | just _ | refl = refl
\end{code}
\end{AgdaAlign}
}

\newcommand\utxowStep{%
\begin{code}[inline]
utxowStep : UTxOEnv → UTxOState → Tx → Maybe UTxOState
utxowStep = compute Computational-UTXOW
\end{code}
\begin{code}[hide]
  where open Computational
\end{code}
\\
\begin{code}[inline]
{-# COMPILE GHC utxowStep #-}
\end{code}
}
