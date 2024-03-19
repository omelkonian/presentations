\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Ledger.Prelude
open import Agda.Primitive renaming (Set to Type)

open import Tactic.Derive.DecEq

module Ledger.Address
  (Network KeyHash ScriptHash : Type)
  ⦃ _ : DecEq Network ⦄ ⦃ _ : DecEq KeyHash ⦄ ⦃ _ : DecEq ScriptHash ⦄
  where
\end{code}

There are various types of addresses used for storing funds in the
UTxO set, which all contain a payment \Credential and optionally a
staking \Credential. \Addr is the union of all of those types. A
\Credential is a hash of a public key or script, types for which are
kept abstract. The most common type of address is a \BaseAddr which
must include a staking \Credential.

There is also a special type of address without a payment credential,
called a reward address. It is not used for interacting with the UTxO
set, but instead it is used to refer to reward accounts
\cite{chimeric}. It is not included in \Addr.

\begin{AgdaMultiCode}
\begin{code}
Credential = KeyHash ⊎ ScriptHash
\end{code}
\hrule
\begin{code}[hide]
data isVKey : Credential → Type where
  VKeyisVKey : (kh : KeyHash) → isVKey (inj₁ kh)
data isScript : Credential → Type where
  SHisScript : (sh : ScriptHash) → isScript (inj₂ sh)
\end{code}
\begin{minipage}{.4\textwidth}
\begin{code}
record BaseAddr : Type where
\end{code}
\begin{code}[hide]
  field
\end{code}
\begin{code}
    pay    : Credential
    stake  : Credential
\end{code}
\begin{code}[hide]
    net    : Network
\end{code}
\end{minipage}
\end{AgdaMultiCode}
\begin{code}[hide]
record BootstrapAddr : Type where
  field  net        : Network
         pay        : Credential
         attrsSize  : ℕ
\end{code}
\hfill
\begin{minipage}{.4\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record RwdAddr : Type where
\end{code}
\begin{code}[hide]
  field
\end{code}
\begin{code}
    stake  : Credential
\end{code}
\begin{code}[hide]
    net    : Network
\end{code}
\end{AgdaMultiCode}
\end{minipage}
\begin{code}[hide]
open BaseAddr; open BootstrapAddr; open BaseAddr; open BootstrapAddr
\end{code}
\begin{code}[hide]
VKeyBaseAddr         = Σ[ addr ∈ BaseAddr       ] isVKey    (addr .pay)
ScriptBaseAddr       = Σ[ addr ∈ BaseAddr       ] isScript  (addr .pay)
\end{code}
\hrule
\begin{code}[hide]
⋯ : Type
⋯ = BootstrapAddr
\end{code}
\begin{code}
Addr        = BaseAddr ⊎ ⋯
\end{code}
\AgdaTarget{payCred, isVKeyAddr}
\begin{code}[hide]
payCred       : Addr → Credential
\end{code}
\begin{code}[hide]
netId         : Addr → Network
isVKeyAddr    : Addr → Type
isScriptAddr  : Addr → Type
\end{code}
\begin{code}[hide]
isVKeyAddr       = isVKey ∘ payCred
isScriptAddr     = isScript ∘ payCred
isScriptRwdAddr  = isScript ∘ RwdAddr.stake
\end{code}
\begin{code}[hide]
payCred (inj₁ record {pay = pay}) = pay
payCred (inj₂ record {pay = pay}) = pay

netId (inj₁ record {net = net}) = net
netId (inj₂ record {net = net}) = net

instance
  Dec-isVKey : isVKey ⁇¹
  Dec-isVKey {x = c} .dec with c
  ... | inj₁ h = yes (VKeyisVKey h)
  ... | inj₂ _ = no  λ ()

  Dec-isScript : isScript ⁇¹
  Dec-isScript {x = x} .dec with x
  ... | inj₁ _ = no λ ()
  ... | inj₂ y = yes (SHisScript y)

_ = isVKey ⁇¹ ∋ it
_ = isVKeyAddr ⁇¹ ∋ it
_ = isScript ⁇¹ ∋ it
_ = isScriptAddr ⁇¹ ∋ it
_ = isScriptRwdAddr ⁇¹ ∋ it

getScriptHash : ∀ a → isScriptAddr a → ScriptHash
getScriptHash (inj₁ _) (SHisScript sh) = sh
getScriptHash (inj₂ _) (SHisScript sh) = sh

instance abstract
  unquoteDecl DecEq-BaseAddr DecEq-BootstrapAddr DecEq-RwdAddr = derive-DecEq
    ( (quote BaseAddr      , DecEq-BaseAddr)
    ∷ (quote BootstrapAddr , DecEq-BootstrapAddr)
    ∷ (quote RwdAddr       , DecEq-RwdAddr)
    ∷ [] )
\end{code}
