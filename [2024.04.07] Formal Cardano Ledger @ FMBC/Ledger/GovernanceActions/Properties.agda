open import Data.Nat.Properties using (+-0-commutativeMonoid; +-0-monoid)

open import Ledger.Prelude
open import Ledger.Types.GovStructure

module Ledger.GovernanceActions.Properties (gs : _) (open GovStructure gs) where

open import Ledger.GovernanceActions gs hiding (yes; no)

open EnactState

instance
  _ = +-0-monoid
  _ = +-0-commutativeMonoid

open Computational ⦃...⦄
postulate instance
  Computational-ENACT : Computational _⊢_⇀⦇_,ENACT⦈_
