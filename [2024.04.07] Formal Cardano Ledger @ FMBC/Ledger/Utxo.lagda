\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Agda.Primitive renaming (Set to Type)
open import Algebra              using (CommutativeMonoid)
open import Data.Integer.Ext     using (posPart; negPart)
open import Data.Nat.Properties  using (+-0-monoid; +-0-commutativeMonoid)
import Data.Maybe as M
import Data.Sum.Relation.Unary.All as Sum

open import Tactic.Derive.DecEq

open import Ledger.Prelude
open import Ledger.Abstract
open import Ledger.Transaction

module Ledger.Utxo
  (txs : _) (open TransactionStructure txs)
  (abs : AbstractFunctions txs) (open AbstractFunctions abs)
  where

instance
  -- _ = TokenAlgebra.Value-CommutativeMonoid tokenAlgebra
  _ = +-0-monoid
  _ = +-0-commutativeMonoid
  _ = ExUnit-CommutativeMonoid

  HasCoin-Map : ∀ {A} → ⦃ DecEq A ⦄ → HasCoin (A ⇀ Coin)
  HasCoin-Map .getCoin s = indexedSumᵛ ⦃ +-0-commutativeMonoid ⦄ id (s ᶠᵐ)

isPhaseTwoScriptAddress : Tx → Addr → Bool
isPhaseTwoScriptAddress tx a =
  if isScriptAddr a then
    (λ {p} → if lookupScriptHash (getScriptHash a p) tx
                 then (λ {s} → isP2Script s)
                 else false)
  else
    false

totExUnits : Tx → ExUnits
totExUnits tx = indexedSumᵐ ⦃ ExUnit-CommutativeMonoid ⦄ (λ x → x .proj₂ .proj₂) (tx .wits .txrdmrs ᶠᵐ)
  where open Tx; open TxWitnesses

-- utxoEntrySizeWithoutVal = 27 words (8 bytes)
utxoEntrySizeWithoutVal : MemoryEstimate
utxoEntrySizeWithoutVal = 8

utxoEntrySize : TxOut → MemoryEstimate
utxoEntrySize utxo = utxoEntrySizeWithoutVal + size (getValue utxo)

open PParams
\end{code}


\begin{code}[hide]
module _ (let open Tx; open TxBody) where
\end{code}
\newcommand\utxoHelpers{%

Some of the functions used to define the UTXO and UTXOW state machines
are defined here. \inject is the function takes a \Coin and turns it
into a multi-asset \Value \cite{eutxoma}.

\begin{code}
  outs : TxBody → UTxO
  outs tx = mapKeys (tx .txid ,_) (tx .txouts)

  minfee : PParams → Tx → Coin
  minfee pp tx  = pp .a * tx .body .txsize + pp .b
\end{code}
\begin{code}[hide]
                + txscriptfee (pp .prices) (totExUnits tx)

  balance : UTxO → Value
  balance utxo = indexedSumᵛ ⦃ commMonoid ⦄ getValue (utxo ᶠᵐ)

  cbalance : UTxO → Coin
  cbalance utxo = coin (balance utxo)

  coinPolicies : ℙ ScriptHash
  coinPolicies = policies (inject 1)

  isAdaOnlyᵇ : Value → Bool
  isAdaOnlyᵇ v =
    if (policies v) ≡ᵉ coinPolicies then
      true
    else
      false

  data DepositPurpose : Type where
    CredentialDeposit  : Credential   → DepositPurpose
    PoolDeposit        : Credential   → DepositPurpose
    DRepDeposit        : Credential   → DepositPurpose
    GovActionDeposit   : GovActionID  → DepositPurpose

  certDeposit : PParams → DCert → Maybe (DepositPurpose × Coin)
  certDeposit _   (delegate c _ _ v)  = just (CredentialDeposit c , v)
  certDeposit pp  (regpool c _)       = just (PoolDeposit       c , pp .poolDeposit)
  certDeposit _   (regdrep c v _)     = just (DRepDeposit       c , v)
  certDeposit _   _                   = nothing

  certDepositᵐ : PParams → DCert → DepositPurpose ⇀ Coin
  certDepositᵐ pp cert = case certDeposit pp cert of λ where
    (just (p , v))  → ❴ p , v ❵
    nothing         → ∅

  propDepositᵐ : PParams → GovActionID → GovProposal → DepositPurpose ⇀ Coin
  propDepositᵐ pp gaid record { returnAddr = record { stake = c } }
    = ❴ GovActionDeposit gaid , pp .govActionDeposit ❵

  certRefund : DCert → Maybe DepositPurpose
  certRefund (dereg c)      = just (CredentialDeposit c)
  certRefund (deregdrep c)  = just (DRepDeposit       c)
  certRefund _              = nothing

  certRefundˢ : DCert → ℙ DepositPurpose
  certRefundˢ = partialToSet certRefund

data inInterval (slot : Slot) : (Maybe Slot × Maybe Slot) → Type where
  both   : ∀ {l r}  → l ≤ slot × slot ≤ r  →  inInterval slot (just l   , just r)
  lower  : ∀ {l}    → l ≤ slot             →  inInterval slot (just l   , nothing)
  upper  : ∀ {r}    → slot ≤ r             →  inInterval slot (nothing  , just r)
  none   :                                    inInterval slot (nothing  , nothing)
\end{code}
}
\begin{code}[hide]
-- Boolean implication
_=>ᵇ_ : Bool → Bool → Bool
a =>ᵇ b = if a then b else true

-- Boolean-valued inequalities on natural numbers
_≤ᵇ_ _≥ᵇ_ : ℕ → ℕ → Bool
m ≤ᵇ n = ¿ m ≤ n ¿ᵇ
_≥ᵇ_ = flip _≤ᵇ_

≟-∅ᵇ : {A : Type} ⦃ _ : DecEq A ⦄ → (X : ℙ A) → Bool
≟-∅ᵇ X = ¿ X ≡ ∅ ¿ᵇ
\end{code}
\newcommand\utxoFeesOK{%
\begin{code}
feesOK : PParams → Tx → UTxO → Bool
feesOK pp tx utxo = minfee pp tx ≤ᵇ txfee
                  ∧ not (≟-∅ᵇ (txrdmrs ˢ))
                  =>ᵇ ( allᵇ (λ (addr , _) → ¿ isVKeyAddr addr ¿) collateralRange
                      ∧ isAdaOnlyᵇ bal
                      ∧ (coin bal * 100) ≥ᵇ (txfee * pp .collateralPercentage)
                      ∧ not (≟-∅ᵇ collateral)
                      )
  where
    open Tx tx; open TxBody body; open TxWitnesses wits; open PParams pp
    collateralRange  = range    (utxo ∣ collateral)
    bal              = balance  (utxo ∣ collateral)
\end{code}
\footnotetext{\AgdaBound{m}~\AgdaFunction{∣}~\AgdaBound{X} denotes the restriction of the map \AgdaBound{m} to the subset \AgdaBound{X} of its domain.}
}
\begin{code}[hide]
instance
  unquoteDecl DecEq-DepositPurpose = derive-DecEq
    ((quote DepositPurpose , DecEq-DepositPurpose) ∷ [])

  HasCoin-UTxO : HasCoin UTxO
  HasCoin-UTxO .getCoin = cbalance
\end{code}

\AgdaTarget{UTxOEnv, UTxOState, \_⊢\_⇀⦇\_,UTXO⦈\_}
\newcommand\depositsAlias{%
\begin{code}
Deposits = DepositPurpose ⇀ Coin
\end{code}
}
\newcommand\utxo{%
\begin{minipage}{.4\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record   UTxOEnv : Type where
\end{code}
\begin{code}[hide]
  field
\end{code}
\begin{code}
    slot     : Slot
    pparams  : PParams
\end{code}
\begin{code}[hide]
    ppolicy  : Maybe ScriptHash
\end{code}
\depositsAlias{}
\end{AgdaMultiCode}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}{.4\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record   UTxOState : Type where
\end{code}
\begin{code}[hide]
  constructor ⟦_,_,_,_⟧ᵘ
  field
\end{code}
\begin{code}
    utxo            : UTxO
    deposits        : Deposits
    fees donations  : Coin
\end{code}
\end{AgdaMultiCode}
\end{minipage}
\hrule

\begin{code}[hide]
⟦_⟧ : {A : Type} → A → A
⟦_⟧ = id

instance
  Dec-inInterval : inInterval ⁇²
  Dec-inInterval {slot} {just x  , just y } .dec with x ≤? slot | slot ≤? y
  ... | no ¬p₁ | _      = no λ where (both (h₁ , h₂)) → ¬p₁ h₁
  ... | yes p₁ | no ¬p₂ = no λ where (both (h₁ , h₂)) → ¬p₂ h₂
  ... | yes p₁ | yes p₂ = yes (both (p₁ , p₂))
  Dec-inInterval {slot} {just x  , nothing} .dec with x ≤? slot
  ... | no ¬p = no  (λ where (lower h) → ¬p h)
  ... | yes p = yes (lower p)
  Dec-inInterval {slot} {nothing , just x } .dec with slot ≤? x
  ... | no ¬p = no  (λ where (upper h) → ¬p h)
  ... | yes p = yes (upper p)
  Dec-inInterval {slot} {nothing , nothing} .dec = yes none

  HasCoin-UTxOState : HasCoin UTxOState
  HasCoin-UTxOState .getCoin s = getCoin (UTxOState.utxo s)
                               + (UTxOState.fees s)
                               + getCoin (UTxOState.deposits s)
                               + UTxOState.donations s
\end{code}
\begin{code}[hide]
module _ (let open UTxOState; open TxBody) where
\end{code}
\newcommand\utxoStateUpdate{%
\begin{code}[hide]
  updateCertDeposits : PParams → List DCert → DepositPurpose ⇀ Coin
    → DepositPurpose ⇀ Coin
  updateCertDeposits pp [] deposits = deposits
  updateCertDeposits pp (cert ∷ certs) deposits
    =  updateCertDeposits pp certs deposits ∪⁺ certDepositᵐ pp cert
    ∣  certRefundˢ cert ᶜ

  updateProposalDeposits : PParams → TxId → List GovProposal → DepositPurpose ⇀ Coin
    → DepositPurpose ⇀ Coin
  updateProposalDeposits pp txid [] deposits = deposits
  updateProposalDeposits pp txid (prop ∷ props) deposits
    =   updateProposalDeposits pp txid props deposits
    ∪⁺  propDepositᵐ pp (txid , length props) prop

  updateDeposits : PParams → TxBody → DepositPurpose ⇀ Coin → DepositPurpose ⇀ Coin
  updateDeposits pp txb
    =  updateCertDeposits pp (txb .txcerts)
    ∘  updateProposalDeposits pp (txb .txid) (txb .txprop)

  depositsChange : PParams → TxBody → DepositPurpose ⇀ Coin → ℤ
  depositsChange pp txb deposits
    =  getCoin (updateDeposits pp txb deposits)
    ⊖  getCoin deposits

  depositRefunds : PParams → UTxOState → TxBody → Coin
  depositRefunds pp st txb = negPart (depositsChange pp txb (st .deposits))

  newDeposits : PParams → UTxOState → TxBody → Coin
  newDeposits pp st txb = posPart (depositsChange pp txb (st .deposits))
\end{code}
\begin{code}
  consumed : PParams → UTxOState → TxBody → Value
  consumed pp st txb
    =  balance (st .utxo ∣ txb .txins)
    +  txb .mint
    +  inject (depositRefunds pp st txb)

  produced : PParams → UTxOState → TxBody → Value
  produced pp st txb
    =  balance (outs txb)
    +  inject (txb .txfee)
    +  inject (newDeposits pp st txb)
    +  inject (txb .txdonation)
\end{code}
}
\begin{code}[hide]
open PParams

private variable
  Γ : UTxOEnv
  s : UTxOState
  tx : Tx
\end{code}
\begin{AgdaMultiCode}
\begin{code}[hide]
data  _⊢_⇀⦇_,UTXO⦈_ : UTxOEnv → UTxOState → Tx → UTxOState → Type where
\end{code}
\begin{code}[inline]
  UTXO-inductive :
\end{code}
\begin{code}[hide]
    let open Tx tx renaming (body to txb); open TxBody txb
        open UTxOEnv Γ renaming (pparams to pp)
        open UTxOState s
    in
      ∙  inInterval slot txvldt
\end{code}
\begin{code}
      ∙  txins ≢ ∅                               ∙ txins ⊆ dom utxo
      ∙  minfee pp tx ≤ txfee                    ∙ txsize ≤ maxTxSize pp
      ∙  consumed pp s txb ≡ produced pp s txb   ∙ coin mint ≡ 0
\end{code}
\begin{code}[hide]
      ∙  ∀[ (_ , txout) ∈ txouts .proj₁ ]  inject (utxoEntrySize txout * minUTxOValue pp) ≤ᵗ getValue txout
      ∙  ∀[ (_ , txout) ∈ txouts .proj₁ ]  serSize (getValue txout) ≤ maxValSize pp
      ∙  ∀[ (a , _) ∈ range txouts ]       Sum.All (const ⊤) (λ a → a .BootstrapAddr.attrsSize ≤ 64) a
      ∙  ∀[ (a , _) ∈ range txouts ]       netId a        ≡ networkId
      ∙  ∀[ a ∈ dom  txwdrls ]             a .RwdAddr.net ≡ networkId
\end{code}
\begin{code}
         ───────────────────────────────────────
\end{code}
\begin{minipage}{.17\textwidth}
\begin{code}
         Γ ⊢  s ⇀⦇ tx ,UTXO⦈
\end{code}
\end{minipage}
\begin{minipage}{.6\textwidth}
\begin{code}
              ⟦ (utxo ∣ txins ᶜ) ∪ˡ outs txb
              , updateDeposits pp txb deposits
              , fees + txfee
              , donations + txdonation ⟧ᵘ
\end{code}
\end{minipage}
\end{AgdaMultiCode}
\begin{code}[hide]
pattern UTXO-inductive⋯ tx Γ s x y z w k l m n o p q r
      = UTXO-inductive {tx}{Γ}{s} (x , y , z , w , k , l , m , n , o , p , q , r)
unquoteDecl UTXO-premises = genPremises UTXO-premises (quote UTXO-inductive)

instance
  Computational-UTXO : Computational _⊢_⇀⦇_,UTXO⦈_
  Computational-UTXO = record {Go}
    where module Go Γ s tx (let H , ⁇ H? = UTXO-premises {tx}{Γ}{s}) where

    computeProof = case H? of λ where
      (yes p) → just (-, UTXO-inductive p)
      (no _)  → nothing

    completeness : ∀ s' → Γ ⊢ s ⇀⦇ tx ,UTXO⦈ s' → _
    completeness s' (UTXO-inductive p) = QED
      where
      QED : map proj₁ computeProof ≡ just s'
      QED with H?
      ... | yes _ = refl
      ... | no ¬p = ⊥-elim $ ¬p p
\end{code}
}
