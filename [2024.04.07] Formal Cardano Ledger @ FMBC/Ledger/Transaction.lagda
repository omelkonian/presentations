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
open import Ledger.Epoch
open import Ledger.GovStructure
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

A transaction is made up of a transaction body and a collection of
witnesses. Some key ingredients in the transaction body are:

\begin{itemize}
  \item A set of transaction inputs, each of which identifies an output from a previous transaction.
    A transaction input consists of a transaction id and an index to uniquely identify the output.
  \item An indexed collection of transaction outputs.
    The \TxOut type is an address paired with a coin value.
  \item A transaction fee. This value will be added to the fee pot.
  \item The size and the hash of the serialized form of the transaction that was included in the block.
    Cardano's serialization is not canonical, so any information that is necessary but lost
    during deserialisation must be preserved by attaching it to the data like this.
\end{itemize}

\begin{minipage}{.4\textwidth}
\begin{code}
        Ix TxId : Type
\end{code}
\end{minipage}
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
\hfill
\begin{minipage}{.4\textwidth}
\begin{code}
  TxIn     = TxId × Ix
  TxOut    = Addr × Value × Maybe DataHash
  UTxO     = TxIn ⇀ TxOut
\end{code}
\begin{code}[hide]
  Wdrl     = RwdAddr ⇀ Coin
  RdmrPtr  = Tag × Ix
\end{code}
\end{minipage}
\begin{code}[hide]
  ProposedPPUpdates  = KeyHash ⇀ PParamsUpdate
  Update             = ProposedPPUpdates × Epoch
\end{code}
\hrule
\begin{AgdaMultiCode}
\begin{code}
  record TxBody : Type where
\end{code}
\begin{code}[hide]
    field
\end{code}
\begin{minipage}{.45\textwidth}
\begin{code}
      txins       : ℙ TxIn
      txouts      : Ix ⇀ TxOut
      txfee       : Coin
\end{code}
\end{minipage}
\begin{minipage}{.35\textwidth}
\begin{code}
      txvote         : List GovVote
      txprop         : List GovProposal
      txsize         : ℕ
      txid           : TxId
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
\end{minipage}
\end{AgdaMultiCode}
\hrule

\begin{minipage}{.4\textwidth}
\begin{AgdaMultiCode}
\begin{code}
  record TxWitnesses : Type where
\end{code}
\begin{code}[hide]
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
\end{AgdaMultiCode}
\end{minipage}
\hfill
\begin{minipage}{.4\textwidth}
\begin{AgdaMultiCode}
\begin{code}[hide]
    scriptsP1 : ℙ P1Script
    scriptsP1 = mapPartial isInj₁ scripts
\end{code}
\begin{code}
  record Tx : Type where
\end{code}
\begin{code}[hide]
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
