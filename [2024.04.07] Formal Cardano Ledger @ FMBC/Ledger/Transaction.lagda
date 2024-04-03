\begin{code}[hide]
{-# OPTIONS --safe #-}
--------------------------------------------------------------------------------
-- NOTE: Everything in this module is part of TransactionStructure
--------------------------------------------------------------------------------
module Ledger.Transaction where

open import Agda.Primitive renaming (Set to Type)
import Data.Maybe.Base as M

open import Ledger.Prelude

open import Ledger.Crypto
open import Ledger.Types.Epoch
open import Ledger.Types.GovStructure
import Ledger.PParams
import Ledger.Script
import Ledger.GovernanceActions
import Ledger.Deleg
import Ledger.TokenAlgebra
import Ledger.Address


open import Tactic.Derive.DecEq
open import MyDebugOptions
open import Relation.Nullary.Decidable using (⌊_⌋)

data Tag : Type where
  Spend Mint Cert Rewrd Vote Propose : Tag
unquoteDecl DecEq-Tag = derive-DecEq ((quote Tag , DecEq-Tag) ∷ [])

record TransactionStructure : Type₁ where
  field
\end{code}

\newcommand\txType{%
\begin{AgdaMultiCode}
\begin{code}
        Ix TxId : Type
\end{code}
\begin{code}[hide]
        AuxiliaryData : Type
        ⦃ DecEq-Ix   ⦄ : DecEq Ix
        ⦃ DecEq-TxId ⦄ : DecEq TxId
        adHashingScheme : isHashableSet AuxiliaryData
  open isHashableSet adHashingScheme renaming (THash to ADHash) public

  field globalConstants : _
  open GlobalConstants globalConstants public

  field crypto : _
  open Crypto crypto public
  open Ledger.TokenAlgebra ScriptHash public
  open Ledger.Address Network KeyHash ScriptHash public

  field epochStructure : _
  open EpochStructure epochStructure public
  open Ledger.Script crypto epochStructure public

  field scriptStructure : ScriptStructure
  open ScriptStructure scriptStructure public
  open Ledger.PParams crypto epochStructure scriptStructure public

  field govParams : _
  open GovParams govParams public

  field tokenAlgebra : TokenAlgebra
  open TokenAlgebra tokenAlgebra public

  field txidBytes : TxId → Ser
        networkId : Network

  govStructure : GovStructure
  govStructure = record
    -- TODO: figure out what to do with the hash
    { TxId = TxId; Network = Network; DocHash = ADHash
    ; crypto = crypto
    ; epochStructure = epochStructure
    ; scriptStructure = scriptStructure
    ; govParams = govParams
    }

  open Ledger.GovernanceActions govStructure hiding (Vote; yes; no; abstain) public
  open Ledger.Deleg             govStructure public
\end{code}
\begin{code}
  TxIn     = TxId × Ix
\end{code}
\begin{code}
  TxOut    = Addr × Value × Maybe DataHash
  UTxO     = TxIn ⇀ TxOut
\end{code}
\begin{code}[hide]
  Wdrl     = RwdAddr ⇀ Coin
  RdmrPtr  = Tag × Ix
\end{code}
\end{AgdaMultiCode}
\begin{code}[hide]
  ProposedPPUpdates  = KeyHash ⇀ PParamsUpdate
  Update             = ProposedPPUpdates × Epoch
\end{code}
\hrule
\begin{minipage}{.4\textwidth}
\begin{AgdaMultiCode}
\begin{code}
  record TxBody : Type where
\end{code}
\begin{code}[hide]
    field
\end{code}
\begin{code}
      txins       : ℙ TxIn
      txouts      : Ix ⇀ TxOut
      txfee       : Coin
      txvote      : List GovVote
      txprop      : List GovProposal
      txsize      : ℕ
      txid        : TxId
\end{code}
\begin{code}[hide]
      mint        : Value
      collateral  : ℙ TxIn
      reqSigHash     : ℙ KeyHash
      scriptIntHash  : Maybe ScriptHash
      txdonation     : Coin
      txup           : Maybe Update
      txADhash       : Maybe ADHash
      netwrk         : Maybe Network
      txvldt   : Maybe Slot × Maybe Slot
      txcerts  : List DCert
      txwdrls  : Wdrl
\end{code}
\end{AgdaMultiCode}
\end{minipage}
\begin{minipage}{.4\textwidth}
\begin{AgdaMultiCode}
\begin{code}
  record TxWitnesses : Type where
\end{code}
\begin{code}[hide,inline]
    field
\end{code}
\begin{code}
      vkSigs   : VKey ⇀ Sig
      scripts  : ℙ Script
\end{code}
\begin{code}[hide]
      txdats   : DataHash ⇀ Datum
      txrdmrs  : RdmrPtr  ⇀ Redeemer × ExUnits
\end{code}
\begin{code}[hide]
    scriptsP1 : ℙ P1Script
    scriptsP1 = mapPartial isInj₁ scripts
\end{code}
\begin{code}


  record Tx : Type where
\end{code}
\begin{code}[hide,inline]
    field
\end{code}
\begin{code}
      body     : TxBody
      wits     : TxWitnesses
\end{code}
\begin{code}[hide]
      txAD     : Maybe AuxiliaryData
\end{code}
\end{AgdaMultiCode}
\end{minipage}

\newcommand\scriptHelpers{%
\begin{code}
  getValue : TxOut → Value
  getValue (_ , v , _) = v

  txinsVKey : ℙ TxIn → UTxO → ℙ TxIn
  txinsVKey txins utxo = txins ∩ dom (utxo ↾' (isVKeyAddr ∘ proj₁))

  scriptOuts : UTxO → UTxO
  scriptOuts utxo = filterᵐ (λ (_ , addr , _) → isScriptAddr addr) utxo

  txinsScript : ℙ TxIn → UTxO → ℙ TxIn
  txinsScript txins utxo = txins ∩ dom (proj₁ (scriptOuts utxo))

  lookupScriptHash : ScriptHash → Tx → Maybe Script
  lookupScriptHash sh tx =
    if sh ∈ mapˢ proj₁ (m ˢ) then
      just (lookupᵐ m sh)
    else
      nothing
    where m = setToHashMap $ tx .Tx.wits .TxWitnesses.scripts

  isP2Script : Script → Bool
  isP2Script = is-just ∘ isInj₂
\end{code}
}
\begin{code}[hide]
  instance
    HasCoin-TxOut : HasCoin TxOut
    HasCoin-TxOut .getCoin = coin ∘ proj₁ ∘ proj₂
\end{code}
}
