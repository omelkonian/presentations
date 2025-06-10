# Decidable propositions appearing in the Jolteon protocol
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Decidability (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Jolteon.Decidability.Core ⋯ public
open import Protocol.Jolteon.Decidability.VoteSharesOf ⋯ public
open import Protocol.Jolteon.Decidability.HighestQC ⋯ public
open import Protocol.Jolteon.Decidability.AllTCs ⋯ public
open import Protocol.Jolteon.Decidability.Final ⋯ public
open import Protocol.Jolteon.Decidability.SmartConstructors ⋯ public
```
