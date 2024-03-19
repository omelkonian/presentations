{-# OPTIONS --safe #-}
module Tactic.MkRecord where

open import Prelude
open import PreludeMeta hiding (`_)

open import Class.Functor using (_<$>_)
open import Class.Monad
open import Class.MonadReader
open import Class.MonadError

mkRecordⁿ : List Term → Hole → TC ⊤
mkRecordⁿ xs hole = do
  def n [] ← inferType hole
    where _ → error [ strErr "[mkRecordⁿ] can only construct values of a defined name" ]
  record-type recCon _ ← getDefinition n
    where _ → error [ strErr "[mkRecordⁿ] can only construct records types" ]
  unify hole $ con recCon (vArg <$> xs)

mkRecord² : Term → Term → _
mkRecord² x y = mkRecordⁿ (x ∷ y ∷ [])

mkRecord³ : Term → Term → Term → _
mkRecord³ x y z = mkRecordⁿ (x ∷ y ∷ z ∷ [])

mkRecord⁴ : Term → Term → Term → Term → _
mkRecord⁴ x y z w = mkRecordⁿ (x ∷ y ∷ z ∷ w ∷ [])

mkRecord⁵ : Term → Term → Term → Term → Term → _
mkRecord⁵ x y z w k = mkRecordⁿ (x ∷ y ∷ z ∷ w ∷ k ∷ [])

macro
  ⟦_⟧ = mkRecordⁿ
  ⟦_⊗_⟧ = mkRecord²
  ⟦_⊗_⊗_⟧ = mkRecord³
  ⟦_⊗_⊗_⊗_⟧ = mkRecord⁴
  ⟦_⊗_⊗_⊗_⊗_⟧ = mkRecord⁵
infix -10
  ⟦_⊗_⟧
  ⟦_⊗_⊗_⟧
  ⟦_⊗_⊗_⊗_⟧
  ⟦_⊗_⊗_⊗_⊗_⟧

macro
  `_ : Term → Hole → TC ⊤
  (` t) hole = unify hole =<< quoteTC t

  _`∷_ : Term → List Term → Hole → TC ⊤
  (x `∷ y) hole = do
    `x ← quoteTC x
    `y ← quoteTC y
    unify hole $ con (quote _∷_) (vArg `x ∷ vArg `y ∷ [])
infixr 4 _`∷_

private

  record R : Set where
    field
      x : ℕ
      s : String

  _ = R ∋ ⟦ ` 0 ∷ ` "zero" ∷ [] ⟧
  _ = R ∋ ⟦ 0 `∷ "zero" `∷ [] ⟧
  _ = R ∋ ⟦ 0 ⊗ "zero" ⟧

  record Q : Set where
    field
      x : ℕ
      s : String
      y : ℕ
      w : String

  _ = Q ∋ ⟦ ` 0 ∷ ` "zero" ∷ ` 1 ∷ ` "one" ∷ [] ⟧
  _ = Q ∋ ⟦ 0 `∷ "zero" `∷ 1 `∷ "one" `∷ [] ⟧
  _ = Q ∋ ⟦ 0 ⊗ "zero" ⊗ 1 ⊗ "one" ⟧
