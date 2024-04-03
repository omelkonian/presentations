\begin{code}[hide]
-- {-# OPTIONS --safe #-}

open import Algebra.Morphism            using (module MonoidMorphisms; IsMagmaHomomorphism)
import Data.Nat as ℕ
open import Data.Nat.Properties         hiding (_≟_)
open import Data.Sign                   using (Sign)
open import Data.Integer as ℤ           using (ℤ; _⊖_)
open import Data.Integer.Ext            using (posPart; negPart)
import Data.Integer.Properties as ℤ
open import Relation.Binary             using (IsEquivalence)

open import Prelude; open Equivalence

open import Tactic.Cong                 using (cong!)
open import Tactic.EquationalReasoning  using (module ≡-Reasoning)
open import Tactic.MonoidSolver.NonNormalising using (solve-macro)
open Tactic.EquationalReasoning.≡-Reasoning {A = ℕ} (solve-macro (quoteTerm +-0-monoid))

open import Ledger.Prelude; open Properties; open Computational ⦃...⦄
open import Ledger.Abstract
open import Ledger.Transaction

module Ledger.Utxo.Properties
  (txs : _) (open TransactionStructure txs)
  (abs : AbstractFunctions txs) (open AbstractFunctions abs)
  where

open import Ledger.Utxo txs abs renaming (Computational-UTXO to Computational-UTXO')

instance
  _ = commMonoid
  _ = +-0-monoid

abstract
  Computational-UTXO : Computational _⊢_⇀⦇_,UTXO⦈_
  Computational-UTXO = Computational-UTXO'

private variable
  tx                               : Tx
  Γ                                : UTxOEnv
  utxoState utxoState'             : UTxOState
\end{code}

\begin{code}[hide]
UTXO-step : UTxOEnv → UTxOState → Tx → Maybe UTxOState
UTXO-step = compute

UTXO-step-computes-UTXO  :  UTXO-step Γ utxoState tx ≡ just utxoState' ⇔  Γ ⊢ utxoState ⇀⦇ tx ,UTXO⦈ utxoState'
UTXO-step-computes-UTXO = ≡-just⇔STS
\end{code}

\newcommand\pov{%
\begin{code}[hide]
pov : let open Tx; open TxBody; open UTxOState in ∀ {s s'} →
\end{code}
\begin{code}
  ∙ tx .body .txid ∉ mapˢ proj₁ (dom (s .utxo))
  ∙ Γ ⊢ s ⇀⦇ tx ,UTXO⦈ s'
    ────────────────────────────────
    getCoin s ≡ getCoin s'
\end{code}
\begin{code}[hide]
pov = TODO
  where postulate TODO : _
\end{code}
}
