# Proven properties of the Jolteon protocol
<!--
```agda
{-# OPTIONS --safe #-}
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Properties (⋯ : _) where
```
-->

```agda
open import Protocol.Jolteon.Properties.Core ⋯ public
open import Protocol.Jolteon.Properties.NoForging ⋯ public
open import Protocol.Jolteon.Properties.State ⋯ public
open import Protocol.Jolteon.Properties.Steps ⋯ public
open import Protocol.Jolteon.Properties.Votes ⋯ public
open import Protocol.Jolteon.Properties.QuorumIntersection ⋯ public
open import Protocol.Jolteon.Properties.NonConsecutiveBlocks ⋯ public
open import Protocol.Jolteon.Properties.Safety ⋯ public
open import Protocol.Jolteon.Properties.Slice ⋯ public
```
