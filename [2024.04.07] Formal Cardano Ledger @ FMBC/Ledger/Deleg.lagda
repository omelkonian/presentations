\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Ledger.Prelude
open import Tactic.MkRecord
open import Ledger.GovStructure

module Ledger.Deleg (gs : _) (open GovStructure gs) where

open import Ledger.GovernanceActions gs
\end{code}
\begin{code}
record PoolParams : Set where
  field rewardAddr : Credential

data DCert : Set where
  delegate    : Credential → Maybe VDeleg → Maybe Credential → Coin → DCert
  dereg       : Credential → DCert
  regpool     : Credential → PoolParams → DCert
  retirepool  : Credential → Epoch → DCert
  regdrep     : Credential → Coin → Anchor → DCert
  deregdrep   : Credential → DCert
  ccreghot    : Credential → Maybe Credential → DCert

record CertEnv : Set where
\end{code}
\begin{code}[hide,inline]
  constructor ⟦_⊗_⊗_⊗_⟧ᶜ
\end{code}
\begin{code}
  field epoch  : Epoch
        pp     : PParams
        votes  : List GovVote
        wdrls  : RwdAddr ⇀ Coin

record DState : Set where
\end{code}
\begin{code}[hide,inline]
  constructor ⟦_⊗_⊗_⟧ᵈ
\end{code}
\begin{code}
  field
    voteDelegs   : Credential ⇀ VDeleg
    stakeDelegs  : Credential ⇀ Credential
    rewards      : Credential ⇀ Coin

record PState : Set where
\end{code}
\begin{code}[hide,inline]
  constructor ⟦_⊗_⟧ᵖ
\end{code}
\begin{code}
  field pools     : Credential ⇀ PoolParams
        retiring  : Credential ⇀ Epoch

record GState : Set where
\end{code}
\begin{code}[hide,inline]
  constructor ⟦_⊗_⟧ᵍ
\end{code}
\begin{code}
  field dreps      : Credential ⇀ Epoch
        ccHotKeys  : Credential ⇀ Maybe Credential

record CertState : Set where
\end{code}
\begin{code}[hide,inline]
  constructor ⟦_⊗_⊗_⟧ᶜ
\end{code}
\begin{code}
  field dState : DState
        pState : PState
        gState : GState

record DelegEnv : Set where
  field pparams  : PParams
        pools    : Credential ⇀ PoolParams

GovCertEnv  = CertEnv
PoolEnv     = PParams
\end{code}

\begin{code}[hide]
private variable
  an : Anchor
  dReps dReps' : Credential ⇀ Epoch
  pools : Credential ⇀ PoolParams
  vDelegs : Credential ⇀ VDeleg
  sDelegs : Credential ⇀ Credential
  retiring retiring' : Credential ⇀ Epoch
  ccKeys : Credential ⇀ Maybe Credential
  rwds : Credential ⇀ Coin
  dCert : DCert
  c c' : Credential
  mc : Maybe Credential
  mv : Maybe VDeleg
  d : Coin
  e : Epoch
  kh kh' : KeyHash
  mkh : Maybe KeyHash
  st st' : CertState
  stᵍ stᵍ' : GState
  stᵈ stᵈ' : DState
  stᵖ stᵖ' : PState
  Γ : CertEnv
  pp : PParams
  vs : List GovVote
  poolParams : PoolParams
  wdrls  : RwdAddr ⇀ Coin

module _ (open PParams) where
\end{code}
\newcommand\delegHelpers{%
\begin{code}
  cwitness : DCert → Credential
  cwitness (delegate c _ _ _)  = c
  cwitness (dereg c)           = c
  cwitness (regpool c _)       = c
  cwitness (retirepool c _)    = c
  cwitness (regdrep c _ _)     = c
  cwitness (deregdrep c)       = c
  cwitness (ccreghot c _)      = c

  getDRepVote : GovVote → Maybe Credential
  getDRepVote record { role = DRep ; credential = credential }  = just credential
  getDRepVote _                                                 = nothing
\end{code}
}

\begin{code}
data _⊢_⇀⦇_,DELEG⦈_ : DelegEnv → DState → DCert → DState → Set where
  DELEG-delegate :
    ∙ (c ∉ dom rwds → d ≡ pp .PParams.poolDeposit)
    ∙ (c ∈ dom rwds → d ≡ 0)
    ∙ mc ∈ mapˢ just (dom pools)
      ────────────────────────────────
      ⟦ pp ⊗ pools ⟧ ⊢  ⟦ vDelegs ⊗ sDelegs ⊗ rwds ⟧ ⇀⦇ delegate c mv mc d ,DELEG⦈
                        ⟦ insertIfJust c mv vDelegs ⊗ insertIfJust c mc sDelegs ⊗ rwds ∪ˡ ❴ c , 0 ❵ ⟧ᵈ

  DELEG-dereg :
    (c , 0) ∈ rwds
    ────────────────────────────────
    ⟦ pp ⊗ pools ⟧ ⊢  ⟦ vDelegs ⊗ sDelegs ⊗ rwds ⟧ ⇀⦇ dereg c ,DELEG⦈
                      ⟦ vDelegs ∣ ❴ c ❵ ᶜ ⊗ sDelegs ∣ ❴ c ❵ ᶜ ⊗ rwds ∣ ❴ c ❵ ᶜ ⟧ᵈ

data _⊢_⇀⦇_,POOL⦈_ : PoolEnv → PState → DCert → PState → Set where
  POOL-regpool : let open PParams pp ; open PoolParams poolParams in
    c ∉ dom pools
    ────────────────────────────────
    pp ⊢  ⟦ pools ⊗ retiring ⟧ ⇀⦇ regpool c poolParams ,POOL⦈
          ⟦ ❴ c , poolParams ❵ ∪ˡ pools ⊗ retiring ⟧ᵖ

  POOL-retirepool :
    pp ⊢  ⟦ pools ⊗ retiring ⟧ ⇀⦇ retirepool c e ,POOL⦈
          ⟦ pools ⊗ ❴ c , e ❵ ∪ˡ retiring ⟧ᵖ

data _⊢_⇀⦇_,GOVCERT⦈_ : GovCertEnv → GState → DCert → GState → Set where
  GOVCERT-regdrep : let open PParams pp in
    (d ≡ drepDeposit × c ∉ dom dReps) ⊎ (d ≡ 0 × c ∈ dom dReps)
    ────────────────────────────────
    ⟦ e ⊗ pp ⊗ vs ⊗ wdrls ⟧ᶜ ⊢  ⟦ dReps ⊗ ccKeys ⟧ᵍ ⇀⦇ regdrep c d an ,GOVCERT⦈
                                ⟦ ❴ c , e + drepActivity ❵ ∪ˡ dReps ⊗ ccKeys ⟧ᵍ

  GOVCERT-deregdrep :
    c ∈ dom dReps
    ────────────────────────────────
    Γ ⊢  ⟦ dReps ⊗ ccKeys ⟧ ⇀⦇ deregdrep c ,GOVCERT⦈
         ⟦ dReps ∣ ❴ c ❵ ᶜ ⊗ ccKeys ⟧ᵍ

  GOVCERT-ccreghot :
    (c , nothing) ∉ ccKeys
    ────────────────────────────────
    Γ ⊢  ⟦ dReps ⊗ ccKeys ⟧ ⇀⦇ ccreghot c mc ,GOVCERT⦈
         ⟦ dReps ⊗ ❴ c , mc ❵ ∪ˡ ccKeys ⟧ᵍ
\end{code}

\begin{code}
data _⊢_⇀⦇_,CERT⦈_ : CertEnv → CertState → DCert → CertState → Set where
  CERT-deleg :
    ⟦ pp ⊗ PState.pools stᵖ ⟧ ⊢ stᵈ ⇀⦇ dCert ,DELEG⦈ stᵈ'
    ────────────────────────────────
    ⟦ e ⊗ pp ⊗ vs ⊗ wdrls ⟧ ⊢ ⟦ stᵈ ⊗ stᵖ ⊗ stᵍ ⟧ ⇀⦇ dCert ,CERT⦈ ⟦ stᵈ' ⊗ stᵖ ⊗ stᵍ ⟧

  CERT-pool :
    pp ⊢ stᵖ ⇀⦇ dCert ,POOL⦈ stᵖ'
    ────────────────────────────────
    ⟦ e ⊗ pp ⊗ vs ⊗ wdrls ⟧ ⊢ ⟦ stᵈ ⊗ stᵖ ⊗ stᵍ ⟧ ⇀⦇ dCert ,CERT⦈ ⟦ stᵈ ⊗ stᵖ' ⊗ stᵍ ⟧

  CERT-vdel :
    Γ ⊢ stᵍ ⇀⦇ dCert ,GOVCERT⦈ stᵍ'
    ────────────────────────────────
    Γ ⊢ ⟦ stᵈ ⊗ stᵖ ⊗ stᵍ ⟧ ⇀⦇ dCert ,CERT⦈ ⟦ stᵈ ⊗ stᵖ ⊗ stᵍ' ⟧

data _⊢_⇀⦇_,CERTBASE⦈_ : CertEnv → CertState → ⊤ → CertState → Set where
  CERT-base :
    let open PParams pp; open CertState st; open GState gState; open DState dState
        refresh = mapPartial getDRepVote (fromList vs)
        wdrlCreds = mapˢ RwdAddr.stake (dom wdrls)
    in wdrlCreds ⊆ dom voteDelegs
    → mapˢ (map₁ RwdAddr.stake) (wdrls ˢ) ⊆ rewards ˢ
    ────────────────────────────────
    ⟦ e ⊗ pp ⊗ vs ⊗ wdrls ⟧ ⊢ st ⇀⦇ _ ,CERTBASE⦈ record st
      { gState = record gState
        { dreps = mapValueRestricted (const (e + drepActivity)) dreps refresh }
      ; dState = record dState { rewards = constMap wdrlCreds 0 ∪ˡ rewards } }

\end{code}
\begin{code}[hide]
_⊢_⇀⦇_,CERTS⦈_ : CertEnv → CertState → List DCert → CertState → Set
_⊢_⇀⦇_,CERTS⦈_ = ReflexiveTransitiveClosureᵇ _⊢_⇀⦇_,CERTBASE⦈_ _⊢_⇀⦇_,CERT⦈_

_⊢_⇀⦇_,CERT∗⦈_ = _⊢_⇀⦇_,CERTS⦈_
\end{code}
