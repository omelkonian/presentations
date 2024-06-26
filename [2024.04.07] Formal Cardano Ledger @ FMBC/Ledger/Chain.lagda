\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Agda.Primitive renaming (Set to Type)
open import Algebra
open import Data.Nat.Properties using (+-0-monoid; +-0-commutativeMonoid)

open import Ledger.Prelude; open Equivalence
open import Ledger.Transaction
open import Ledger.Abstract

open import Tactic.MkRecord

module Ledger.Chain
  (txs : _) (open TransactionStructure txs)
  (abs : AbstractFunctions txs) (open AbstractFunctions abs)
  where

open import Ledger.Gov govStructure
open import Ledger.Ledger txs abs
open import Ledger.Ratify txs
open import Ledger.Utxo txs abs
\end{code}

\newcommand\chain{%
\begin{minipage}{.35\textwidth}
\begin{code}
record Block : Type where
  field  ts    : List Tx
         slot  : Slot
\end{code}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}{.6\textwidth}
\begin{code}[hide]
record NewEpochEnv : Type where
  field  stakeDistrs : StakeDistrs
\end{code}
\begin{AgdaMultiCode}
\begin{code}
record   NewEpochState : Type where
\end{code}
\begin{code}[hide]
  constructor ⟦_⊗_⊗_⊗_⊗_⟧ⁿ
\end{code}
\begin{code}
  field  lastEpoch : Epoch; acnt : Acnt
         ls : LState; es : EnactState
         fut : RatifyState

record ChainState : Type where
  field newEpochState  : NewEpochState
\end{code}
\end{AgdaMultiCode}
\end{minipage}

\begin{code}[hide]
private variable
  s : ChainState
  b : Block
  ls' : LState
  nes : NewEpochState
  e : Epoch
  es' : EnactState
  govSt' : GovState
  d : Bool
  fut' : RatifyState

instance _ = +-0-monoid; _ = +-0-commutativeMonoid

-- The NEWEPOCH rule is actually multiple rules in one for the sake of simplicity:t also does what EPOCH used to do in previous eras
data _⊢_⇀⦇_,NEWEPOCH⦈_ : NewEpochEnv → NewEpochState → Epoch → NewEpochState → Type where
\end{code}
\begin{AgdaMultiCode}
\begin{code}[hide]
  NEWEPOCH-New :
    ∀ {Γ} → let
      open NewEpochState nes hiding (es)
      open RatifyState fut using (removed) renaming (es to esW)
      -- ^ this rolls over the future enact state into es
      open LState ls; open UTxOState utxoSt
      open CertState certState
      open PState pState; open DState dState; open GState gState
      open Acnt acnt

      trWithdrawals   = esW .EnactState.withdrawals
      totWithdrawals  = ∑[ x ← trWithdrawals ᶠᵐ ] x

      removedGovActions = flip concatMapˢ removed λ (gaid , gaSt) →
        mapˢ (GovActionState.returnAddr gaSt ,_)
             ((deposits ∣ ❴ GovActionDeposit gaid ❵) ˢ)
      govActionReturns = aggregate₊ $ mapˢ (λ (a , _ , d) → a , d) removedGovActions ᶠˢ

      es        = record esW { withdrawals = ∅ }
      retired   = retiring ⁻¹ e
      payout    = govActionReturns ∪⁺ trWithdrawals
      refunds   = pullbackMap payout (λ x → record { net = NetworkId ; stake = x }) (dom rewards)
      unclaimed = getCoin payout ∸ getCoin refunds

      govSt' = filter (λ x → ¿ proj₁ x ∉ mapˢ proj₁ removed ¿) govSt

      gState' = record gState { ccHotKeys = ccHotKeys ∣ ccCreds (es .EnactState.cc) }

      certState' = record certState {
        pState = record pState
          { pools = pools ∣ retired ᶜ ; retiring = retiring ∣ retired ᶜ };
        dState = record dState
          { rewards = rewards ∪⁺ refunds };
        gState = if not (null govSt') then gState' else record gState'
          { dreps = mapValues sucᵉ dreps }
        }
      utxoSt' = record utxoSt
        { fees = 0
        ; deposits = deposits ∣ mapˢ (proj₁ ∘ proj₂) removedGovActions ᶜ
        ; donations = 0
        }
      ls' = record ls
        { govSt = govSt' ; utxoSt = utxoSt' ; certState = certState' }
      acnt' = record acnt
        { treasury = treasury + fees + unclaimed + donations ∸ totWithdrawals }
    in
    ∙  e ≡ sucᵉ lastEpoch
    ∙  record { currentEpoch = e ; treasury = treasury ; GState gState ; NewEpochEnv Γ }
         ⊢ ⟦ es ⊗ ∅ ⊗ false ⟧ʳ ⇀⦇ govSt' ,RATIFY∗⦈ fut'
       ────────────────────────────────
       Γ ⊢ nes ⇀⦇ e ,NEWEPOCH⦈ ⟦ e ⊗ acnt' ⊗ ls' ⊗ es ⊗ fut' ⟧ⁿ

  NEWEPOCH-Not-New :
   ∀ {Γ} → let open NewEpochState nes in
    e ≢ sucᵉ lastEpoch
    ────────────────────────────────
    Γ ⊢ nes ⇀⦇ e ,NEWEPOCH⦈ nes
\end{code}
\end{AgdaMultiCode}

\begin{code}[hide]
-- TODO: do we still need this for anything?
maybePurpose : DepositPurpose → (DepositPurpose × Credential) → Coin → Maybe Coin
maybePurpose prps (prps' , _) c with prps ≟ prps'
... | yes _ = just c
... | no _ = nothing

maybePurpose-prop : ∀ {prps} {x} {y}
  → (m : (DepositPurpose × Credential) ⇀ Coin)
  → (x , y) ∈ dom ((mapMaybeWithKeyᵐ (maybePurpose prps) m) ˢ)
  → x ≡ prps
maybePurpose-prop {prps = prps} {x} {y} _ xy∈dom with to dom∈ xy∈dom
... | z , ∈mmwk with prps ≟ x | ∈-mapMaybeWithKey {f = maybePurpose prps} ∈mmwk
... | yes refl | _ = refl

filterPurpose : DepositPurpose → (DepositPurpose × Credential) ⇀ Coin → Credential ⇀ Coin
filterPurpose prps m = mapKeys proj₂ (mapMaybeWithKeyᵐ (maybePurpose prps) m)
  {λ where x∈dom y∈dom refl → cong (_, _)
                            $ trans (maybePurpose-prop {prps = prps} m x∈dom)
                            $ sym   (maybePurpose-prop {prps = prps} m y∈dom)}

govActionDeposits : LState → VDeleg ⇀ Coin
govActionDeposits ls =
  let open LState ls; open CertState certState; open PState pState
      open UTxOState utxoSt; open DState dState
   in foldl _∪⁺_ ∅ $ setToList $
    mapPartial
      (λ where (gaid , record { returnAddr = record {stake = c} }) → do
        vd ← lookupᵐ? voteDelegs c
        dep ← lookupᵐ? deposits (GovActionDeposit gaid)
        just ❴ vd , dep ❵ )
      (fromList govSt)

calculateStakeDistrs : LState → StakeDistrs
calculateStakeDistrs ls =
  let open LState ls; open CertState certState; open PState pState
      open UTxOState utxoSt; open DState dState
      spoDelegs = ∅ -- TODO
      drepDelegs = ∅ -- TODO
  in
  record
    { stakeDistr = govActionDeposits ls
    }
\end{code}
\hrule
\begin{AgdaMultiCode}
\begin{code}[hide]
open ChainState; open NewEpochState

mkNewEpochEnv : ChainState → NewEpochEnv
mkNewEpochEnv cs = record
  { stakeDistrs = calculateStakeDistrs (cs .newEpochState .ls) }

updateChainState : ChainState → NewEpochState → ChainState
updateChainState cs nes = record cs
  { newEpochState = record nes { ls = cs .newEpochState .ls } }

data  _⊢_⇀⦇_,CHAIN⦈_ : ⊤ → ChainState → Block → ChainState → Type where
\end{code}
\begin{code}
  CHAIN :
\end{code}
\begin{code}[hide]
    let open Block b; es = s .newEpochState .es; open EnactState es
    in
\end{code}
\begin{code}
      ∙  mkNewEpochEnv s ⊢ s .newEpochState ⇀⦇ epoch slot ,NEWEPOCH⦈ nes
      ∙  ⟦ slot ⊗ constitution .proj₁ .proj₂ ⊗ pparams .proj₁ ⊗ es ⟧ˡ
           ⊢ nes .ls ⇀⦇ ts ,LEDGER∗⦈ ls'
         ───────────────────────────────────────
         _  ⊢ s ⇀⦇ b ,CHAIN⦈ updateChainState s nes
\end{code}
\end{AgdaMultiCode}
}
