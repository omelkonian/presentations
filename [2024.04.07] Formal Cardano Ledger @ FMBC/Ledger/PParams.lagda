We start with adjustable protocol parameters. In contrast to constants
such as the length of an \Epoch, these parameters can be changed while
the system is running via the governance mechanism. They can affect
various features of the system, such as minimum fees, maximum and
minimum sizes of certain components, and more.

The full specification contains well over 20 parameters, while we only
list a few. The maximum sizes should be self-explanatory, while
\minFeeA and \minFeeB are the coefficients of a polynomial used in the
\minFee function.

\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Agda.Primitive renaming (Set to Type)
open import Data.Product.Properties
open import Data.Nat.Properties using (m+1+n≢m)
open import Data.Rational using (ℚ)
open import Relation.Nullary.Decidable

open import Tactic.Derive.DecEq

open import Ledger.Prelude
open import Ledger.Epoch
open import Ledger.Crypto
open import Ledger.Script

module Ledger.PParams
  (crypto : Crypto )
  (es     : _) (open EpochStructure es)
  (ss     : ScriptStructure crypto es) (open ScriptStructure ss)
  where

private variable
  m n : ℕ

record Acnt : Type where
  field treasury reserves : Coin

data PParamGroup : Type where
  NetworkGroup EconomicGroup TechnicalGroup GovernanceGroup : PParamGroup
\end{code}
\begin{AgdaMultiCode}
\begin{code}[hide]
ProtVer = ℕ × ℕ

data pvCanFollow : ProtVer → ProtVer → Type where
  canFollowMajor : pvCanFollow (m , n) (m + 1 , 0)
  canFollowMinor : pvCanFollow (m , n) (m , n + 1)
\end{code}
\begin{code}[hide]
record DrepThresholds : Type where
  field P1 P2a P2b P3 P4 P5a P5b P5c P5d P6 : ℚ
\end{code}
\begin{code}[hide]
record PoolThresholds : Type where
  field Q1 Q2a Q2b Q4 : ℚ
\end{code}

\begin{code}
record PParams : Type where
\end{code}
\begin{code}[hide]
  field
\end{code}
\begin{code}
        maxBlockSize maxTxSize a b                     : ℕ
\end{code}
\begin{code}[hide]
        drepThresholds          : DrepThresholds
        poolThresholds          : PoolThresholds
\end{code}
\begin{code}[hide]
        govActionLifetime             : ℕ
        coinsPerUTxOWord              : Coin
        maxBlockExUnits maxTxExUnits  : ExUnits
        ccMinSize ccMaxTermLength                          : ℕ
        govActionDeposit drepDeposit                                         : Coin
        drepActivity                                                         : Epoch
        minUTxOValue poolDeposit  : Coin
        pv                                                                   : ProtVer
        prices                                     : Prices
        Emax                  : Epoch
        collateralPercentage  : ℕ
        costmdls              : CostModel
        maxHeaderSize maxValSize maxCollateralInputs : ℕ
\end{code}
\end{AgdaMultiCode}

\begin{code}[hide]
paramsWellFormed : PParams → Type
paramsWellFormed pp =
     0 ∉ fromList  ( maxBlockSize ∷ maxTxSize ∷ maxHeaderSize ∷ maxValSize
                   ∷ minUTxOValue ∷ poolDeposit ∷ collateralPercentage ∷ ccMaxTermLength
                   ∷ govActionLifetime ∷ govActionDeposit ∷ drepDeposit ∷ [] )
  ×  ℕtoEpoch govActionLifetime ≤ drepActivity
\end{code}
\begin{code}[hide]
  where open PParams pp
instance
  unquoteDecl DecEq-DrepThresholds = derive-DecEq
    ((quote DrepThresholds , DecEq-DrepThresholds) ∷ [])
  unquoteDecl DecEq-PoolThresholds = derive-DecEq
    ((quote PoolThresholds , DecEq-PoolThresholds) ∷ [])
  unquoteDecl DecEq-PParams        = derive-DecEq
    ((quote PParams , DecEq-PParams) ∷ [])

instance
  pvCanFollow? : ∀ {pv} {pv'} → Dec (pvCanFollow pv pv')
  pvCanFollow? {m , n} {pv} with pv ≟ (m + 1 , 0) | pv ≟ (m , n + 1)
  ... | no ¬p    | no ¬p₁   = no $ λ where canFollowMajor → ¬p  refl
                                           canFollowMinor → ¬p₁ refl
  ... | no ¬p    | yes refl = yes canFollowMinor
  ... | yes refl | no ¬p    = yes canFollowMajor
  ... | yes refl | yes p    = ⊥-elim $ m+1+n≢m m $ ×-≡,≡←≡ p .proj₁

record PParamsDiff : Type₁ where
  field UpdateT : Type
        updateGroups : UpdateT → ℙ PParamGroup
        applyUpdate : PParams → UpdateT → PParams
        ppdWellFormed : UpdateT → Bool
        ppdWellFormed⇒hasGroup : ∀ {u} → ppdWellFormed u ≡ true → updateGroups u ≢ ∅
        ppdWellFormed⇒WF       : ∀ {u} → ppdWellFormed u ≡ true → ∀ pp
                               → paramsWellFormed pp
                               → paramsWellFormed (applyUpdate pp u)

record GovParams : Type₁ where
  field ppUpd : PParamsDiff
  open PParamsDiff ppUpd renaming (UpdateT to PParamsUpdate) public
  field ppHashingScheme : isHashableSet PParams
  open isHashableSet ppHashingScheme renaming (THash to PPHash) public
  field ⦃ DecEq-UpdT ⦄ : DecEq PParamsUpdate
\end{code}
