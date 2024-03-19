\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Agda.Primitive renaming (Set to Type)
open import Ledger.Prelude
open import Ledger.Crypto
open import Ledger.Abstract
open import Ledger.Transaction

module Ledger.Utxow
  (txs : _) (open TransactionStructure txs)
  (abs : AbstractFunctions txs) (open AbstractFunctions abs)
  where
open import Ledger.Utxo txs abs
open import Ledger.ScriptValidation txs abs
\end{code}

\newcommand\utxowHelpers{%
\begin{code}
credsNeeded : Maybe ScriptHash → UTxO → TxBody → ℙ (ScriptPurpose × Credential)
credsNeeded p utxo txb
  =  mapˢ (λ (i , o) → (Spend i , payCred (proj₁ o))) ((utxo ∣ txins) ˢ)
  ∪  mapˢ (λ a → (Rwrd a , RwdAddr.stake a)) (dom $ txwdrls .proj₁)
  ∪  mapˢ (λ c → (Cert c , cwitness c)) (fromList txcerts)
  ∪  mapˢ (λ x → (Mint x , inj₂ x)) (policies mint)
  ∪  mapˢ (λ v → (Vote v , GovVote.credential v)) (fromList txvote)
  ∪  (if p then (λ {sh} → mapˢ (λ p → (Propose p , inj₂ sh)) (fromList txprop))
      else ∅)
  where open TxBody txb

witsVKeyNeeded : Maybe ScriptHash → UTxO → TxBody → ℙ KeyHash
witsVKeyNeeded sh = mapPartial isInj₁ ∘₂ mapˢ proj₂ ∘₂ credsNeeded sh

scriptsNeeded  : Maybe ScriptHash → UTxO → TxBody → ℙ ScriptHash
scriptsNeeded sh = mapPartial isInj₂ ∘₂ mapˢ proj₂ ∘₂ credsNeeded sh
\end{code}
}
\begin{code}[hide]
private variable
  Γ : UTxOEnv
  s s' : UTxOState
  tx : Tx
\end{code}

Transaction witnessing checks that all required signatures are present
and all required scripts accept the validity of the given
transaction. \AgdaBound{witsKeyHashes} and
\AgdaBound{witsScriptHashes} is the set of hashes of keys/scripts
included in the transaction.

\begin{AgdaMultiCode}
\begin{code}[hide]
data  _⊢_⇀⦇_,UTXOW⦈_ : UTxOEnv → UTxOState → Tx → UTxOState → Type where
\end{code}
\begin{code}
  UTXOW-inductive :
\end{code}
\begin{code}[hide]
    let open Tx tx renaming (body to txb); open TxBody txb; open TxWitnesses wits
        open UTxOState s; open UTxOEnv Γ
        witsKeyHashes     = mapˢ hash (dom vkSigs)
        witsScriptHashes  = mapˢ hash scripts
    in
\end{code}
\begin{code}
      ∙  witsVKeyNeeded ppolicy utxo txb ⊆ witsKeyHashes
      ∙  scriptsNeeded ppolicy utxo txb ≡ᵉ witsScriptHashes
      ∙  ∀[ (vk , σ) ∈ vkSigs ] isSigned vk (txidBytes txid) σ
      ∙  ∀[ s ∈ scriptsP1 ] validP1Script witsKeyHashes txvldt s
\end{code}
\begin{code}[hide]
      ∙  txADhash ≡ map hash txAD
\end{code}
\begin{code}
      ∙  Γ ⊢ s ⇀⦇ tx ,UTXO⦈ s'
         ────────────────────────────────
         Γ ⊢ s ⇀⦇ tx ,UTXOW⦈ s'
\end{code}
\end{AgdaMultiCode}
\begin{code}[hide]
pattern UTXOW-inductive⋯ p₁ p₂ p₃ p₄ p₅ h
      = UTXOW-inductive (p₁ , p₂ , p₃ , p₄ , p₅ , h)
unquoteDecl UTXOW-inductive-premises =
  genPremises UTXOW-inductive-premises (quote UTXOW-inductive)
\end{code}
