{-# OPTIONS --safe #-}
open import Prelude
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Global.Trace.Extension (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Jolteon.Block ⋯
open import Protocol.Jolteon.Message ⋯
open import Protocol.Jolteon.Local.State ⋯
open import Protocol.Jolteon.Local.Step ⋯
open import Protocol.Jolteon.Global.State ⋯
open import Protocol.Jolteon.Global.Step ⋯

open import Protocol.Jolteon.Global.Trace.Core ⋯

extendRs : (Rs : Reachable s) → s′ ↞— s → Reachable s′
extendRs (_ , init , tr) tr′ = _ , init , ↞—-trans tr′ tr

_▷_ : GlobalState → LocalStepProperty → Type
s ▷ P = ∃ λ st →
          let p , t , ls , _ , _ = stepArgs st in
            t ≡ s .currentTime
          × s ＠ p ≡ ls
          × P st

▷-doStep : ∀ {P} → s ▷ P → GlobalState
▷-doStep {s = s} (st , _) = let p , t , _ , menv , ls′ = st .stepArgs in
  broadcast t menv (s ＠ p ≔ ls′)

_◁_ : LocalStepProperty → GlobalState → Type
P ◁ s′ = ∃ λ st → ∃ λ s →
          let p , t , ls , menv , ls′ = stepArgs st in
            t ≡ s .currentTime
          × s ＠ p ≡ ls
          × s′ ≡ broadcast t menv (s ＠ p ≔ ls′)
          × P st

-- ** extending an arbitrary (non-well-rooted) trace

record TraceExtension↞ {s}{s′} (s↠s′ : s′ ↞— s) : Type where
  constructor ⟨_,_,_,_⟩
  field
    s↓  : GlobalState
    s↠  : s↓ ↞— s
    ↠s′ : s′ ↞— s↓
    s↠s↓↠s′ : s↠s′ ≡ ↞—-trans ↠s′ s↠
open TraceExtension↞

trace↞◁ :  ∀ (tr : s′ ↞— s){P} →
  (trP : tr ∋⋯′ P) →
  ────────────────────────────────────────────────
  Σ (TraceExtension↞ tr) (λ trE → P ◁ trE .s↓)
trace↞◁ (s ⟨ Deliver tpm∈ ⟩←— tr) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← trace↞◁ tr trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ Deliver tpm∈ ⟩←— tr⟪) , refl ⟩ , p
trace↞◁ tr@(s′ ⟨ LocalStep st ∣ s ⟩←— _) (here px)
  = ⟨ s′ , tr , s′ ∎ , refl ⟩ , ( _ ⊢ st) , s , refl , refl , refl , px
trace↞◁ (s ⟨ LocalStep st ⟩←— tr) (there trP)
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← trace↞◁ tr trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ LocalStep st ⟩←— tr⟪) , refl ⟩ , p
trace↞◁ (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← trace↞◁ tr trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr⟪) , refl ⟩ , p
trace↞◁ (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← trace↞◁ tr trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr⟪) , refl ⟩ , p

-- ** extending a well-rooted trace

record TraceExtension (Rs : Reachable s) : Type where
  constructor ⟨_,_,_,_⟩
  field
    intState   : GlobalState
    reachable′ : Reachable intState
    extension  : s ↞— intState
    traceAgree : Rs ≡ extendRs reachable′ extension
open TraceExtension

traceRs◁ :  ∀ (Rs : Reachable s){P} →
  (trP : Rs ∋⋯ P) →
  ────────────────────────────────────────────────
  Σ (TraceExtension Rs) (λ trE → P ◁ intState trE)
traceRs◁ (_ , init , (s ⟨ Deliver tpm∈ ⟩←— tr)) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs◁ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ Deliver tpm∈ ⟩←— tr⟪) , refl ⟩ , p
traceRs◁ Rs@(_ , init , tr@(s′ ⟨ LocalStep st ∣ s ⟩←— _)) (here px)
 =   ⟨ s′ , Rs , s′ ∎ , refl ⟩ , ( _ ⊢ st) , s , refl , refl , refl , px
traceRs◁ (_ , init , (s ⟨ LocalStep st ⟩←— tr)) (there trP)
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs◁ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ LocalStep st ⟩←— tr⟪) , refl ⟩ , p
traceRs◁ (_ , init , (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr)) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs◁ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr⟪) , refl ⟩ , p
traceRs◁ (_ , init , (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr)) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs◁ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr⟪) , refl ⟩ , p

traceRs▷ :  ∀ (Rs : Reachable s){P} →
  (trP : Rs ∋⋯ P) →
  ────────────────────────────────────────────────
  Σ (TraceExtension Rs) (λ trE → intState trE ▷ P)
traceRs▷ (_ , init , (s ⟨ Deliver tpm∈ ⟩←— tr)) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs▷ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ Deliver tpm∈ ⟩←— tr⟪) , refl ⟩ , p
traceRs▷ (_ , init , (s′ ⟨ LocalStep st ∣ s ⟩←— tr)) (here px)   =
  ⟨ s , (_ , init , tr) , (s′ ⟨ LocalStep st ⟩←— s ∎) , refl ⟩ , ( _ ⊢ st) , refl , refl , px
traceRs▷ (_ , init , (s ⟨ LocalStep st     ⟩←— tr)) (there trP)
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs▷ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ LocalStep st ⟩←— tr⟪) , refl ⟩ , p
traceRs▷ (_ , init , (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr)) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs▷ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr⟪) , refl ⟩ , p
traceRs▷ (_ , init , (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr)) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs▷ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr⟪) , refl ⟩ , p

-- ** local steps

data IsLocal : ∃Step → Type where
  LocalStep : ∀ ⦃ _ : Honest p ⦄ {st : p ⦂ s .currentTime ⊢ s ＠ p — menv —→ ls′} →
    IsLocal (s , -, LocalStep st)

record _ᴸ←—_ (s′ s : GlobalState) : Type where
  constructor _⊣ᴸ_
  field {_p _menv _ls′} : _
        ⦃ hp ⦄ : Honest _p
  _ls  = s ＠ _p
  field localStep : _p ⦂ s .currentTime ⊢ _ls — _menv —→ _ls′
        s≡        : s′ ≡ broadcast (s .currentTime) _menv (s ＠ _p ≔ _ls′)

open _ᴸ←—_

instance
  Dec-IsLocal : IsLocal ⁇¹
  Dec-IsLocal {_ , _ , st} .dec with st
  ... | LocalStep _            = yes LocalStep
  ... | DishonestLocalStep _ _ = no λ ()
  ... | Deliver _              = no λ ()
  ... | WaitUntil _ _ _        = no λ ()

Local→Global : s′ ᴸ←— s → s′ ¹←— s
Local→Global st
  = subst (_¹←— _) (sym $ st .s≡)
  $ LocalStep (st . localStep)

Local→Global⇒IsLocal : ∀ {st : s′ ᴸ←— s} →
  IsLocal (-, -, Local→Global st)
Local→Global⇒IsLocal {st = _ ⊣ᴸ refl} = LocalStep

record ∃IsLocal : Type where
  constructor _,_
  field stl  : ∃Step
        .loc : IsLocal stl

∃IsLocal≡ : ∀ {r r′} →
  r .∃IsLocal.stl ≡ r′ .∃IsLocal.stl
  ──────────────────
  r ≡ r′
∃IsLocal≡ refl = refl

module _ (r : ∃IsLocal) (let stl , loc = r) where
  getLoc : IsLocal stl
  getLoc = recompute dec loc

  getP : Pid
  getP with stl | getLoc
  ... | _ , _ , LocalStep {p = p} _ | LocalStep = p

  getM : Maybe Envelope
  getM with stl | getLoc
  ... | _ , _ , LocalStep {menv = menv} _ | LocalStep = menv

  getL : LocalState
  getL with stl | getLoc
  ... | _ , _ , LocalStep {ls′ = ls′} _ | LocalStep = ls′

getP≡ : ∀ (st : s′ ᴸ←— s) →
  getP ((-, -, Local→Global st) , Local→Global⇒IsLocal) ≡ st ._p
getP≡ (_ ⊣ᴸ refl) = refl

getM≡ : ∀ (st : s′ ᴸ←— s) →
  getM ((-, -, Local→Global st) , Local→Global⇒IsLocal) ≡ st ._menv
getM≡ (_ ⊣ᴸ refl) = refl

getL≡ : ∀ (st : s′ ᴸ←— s) →
  getL ((-, -, Local→Global st) , Local→Global⇒IsLocal) ≡ st ._ls′
getL≡ (_ ⊣ᴸ refl) = refl

Local→Global-inj : ∀ (st st′ : s′ ᴸ←— s) →
  Local→Global st ≡ Local→Global st′
  ──────────────────────────────────
  st ≡ st′
Local→Global-inj {s′}{s} st@(_ ⊣ᴸ s≡) st′@(_ ⊣ᴸ s≡′) st≡ = QED
  where
  ∃st ∃st′ : ∃Step
  ∃st  = -, -, Local→Global st
  ∃st′ = -, -, Local→Global st′

  ∃st≡ : ∃st ≡ ∃st′
  ∃st≡ = cong (λ ◆ → s , s′ , ◆) st≡

  ∃stl ∃stl′ : ∃IsLocal
  ∃stl  = ∃st  , Local→Global⇒IsLocal
  ∃stl′ = ∃st′ , Local→Global⇒IsLocal

  ∃stl≡ : ∃stl ≡ ∃stl′
  ∃stl≡ = ∃IsLocal≡ ∃st≡

  p≡ : st ._p ≡ st′ ._p
  p≡ = subst (_≡ _) (getP≡ st) $ subst (_ ≡_) (getP≡ st′)
     $ cong getP ∃stl≡

  m≡ : st ._menv ≡ st′ ._menv
  m≡ = subst (_≡ _) (getM≡ st) $ subst (_ ≡_) (getM≡ st′)
     $ cong getM ∃stl≡

  l≡ : st ._ls′ ≡ st′ ._ls′
  l≡ = subst (_≡ _) (getL≡ st) $ subst (_ ≡_) (getL≡ st′)
     $ cong getL ∃stl≡

  QED : st ≡ st′
  QED with st ._p ≟ st′ ._p
  ... | no p≢ = ⊥-elim $ p≢ p≡
  ... | yes refl with st ._menv ≟ st′ ._menv
  ... | no m≢ = ⊥-elim $ m≢ m≡
  ... | yes refl with st ._ls′ ≟ st′ ._ls′
  ... | no l≢ = ⊥-elim $ l≢ l≡
  ... | yes refl with ⟫ s≡ | ⟫ s≡′ | ⟫ st≡
  ... | ⟫ refl | ⟫ refl | ⟫ refl = refl

-- ** (well-rooted) non-empty trace extension

_⟨_⟩←—ᴿ_ : ∀ s′ → s′ ¹←— s → Reachable s → Reachable s′
_ ⟨ st ⟩←—ᴿ (_ , s-init , tr) =
  (_ , s-init , (_ ⟨ st ⟩←— tr))

record TraceExtension⁺ {z} (Rz : Reachable z) : Type where
  constructor ⟨_,_,_,_⟩
  field
    {x y} : GlobalState
    Rx    : Reachable x
    y←x   : y ᴸ←— x
    z↞y   : z ↞— y

  y¹←x : y ¹←— x
  y¹←x = Local→Global y←x

  z↞x : z ↞— x
  z↞x = _ `—→⟨ y¹←x ⟩ z↞y

  Ry : Reachable y
  Ry = _ ⟨ y¹←x ⟩←—ᴿ Rx

  field
    Rz≡ : Rz ≡ extendRs Ry z↞y
    -- Rz≡ : Rz ≡ extendRs Rx z↞x

  step : Step
  step = _ ⊢ y←x ._ᴸ←—_.localStep

open TraceExtension⁺

private
  UIP : (p q : s ≡ s′) → p ≡ q
  UIP refl refl = refl

  open Prod hiding (,-injectiveʳ)

step≡-TE⁺ : ∀ {s} (Rs : Reachable s) (trE trE′ : TraceExtension⁺ Rs) →
  _≡_ {A = ∃ λ x → ∃ λ y → y ¹←— x} (-, -, y¹←x trE) (-, -, y¹←x trE′)
  ────────────────────────────────────────────────────────────────────
  step trE ≡ step trE′
step≡-TE⁺ Rs trE trE′ eq
  with refl ← ,-injectiveˡ eq
  with refl ← ,-injectiveˡ $ ,-injectiveʳ-≡ UIP eq refl
  with eq′  ← ,-injectiveʳ-≡ UIP (,-injectiveʳ-≡ UIP eq refl) refl
  with refl ← Local→Global-inj _ _ eq′
  = refl

traceRs⁺ : ∀ (Rs : Reachable s) {P} →
  (trP : Rs ∋⋯ P) →
  ────────────────────────────────
  Σ (TraceExtension⁺ Rs) (P ∘ TraceExtension⁺.step)
traceRs⁺ (_ , init , (s ⟨ Deliver tpm∈ ⟩←— tr)) trP
  with ⟨ s , Rs , tr , refl ⟩ , P ← traceRs⁺ (_ , init , tr) trP
     = ⟨ s , Rs , (_ ⟨ Deliver tpm∈ ⟩←— tr) , refl ⟩ , P
traceRs⁺ (_ , init , (s′ ⟨ LocalStep st ∣ s ⟩←— tr)) (here px)
 = ⟨ (_ , init , tr) , (st ⊣ᴸ refl) , (s′ ∎) , refl ⟩ , px
traceRs⁺ (_ , init , (_ ⟨ LocalStep  st ⟩←— tr)) (there trP)
  with ⟨ s , Rs , tr , refl ⟩ , P ← traceRs⁺ (_ , init , tr) trP
     = ⟨ s , Rs , (_ ⟨ LocalStep st ⟩←— tr) , refl ⟩ , P
traceRs⁺ (_ , init , (_ ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr)) trP
  with ⟨ s , Rs , tr , refl ⟩ , P ← traceRs⁺ (_ , init , tr) trP
     = ⟨ s , Rs , (_ ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr) , refl ⟩ , P
traceRs⁺ (_ , init , (_ ⟨ WaitUntil t <Δ now≤t ⟩←— tr)) trP
  with ⟨ s , Rs , tr , refl ⟩ , P ← traceRs⁺ (_ , init , tr) trP
     = ⟨ s , Rs , (_ ⟨ WaitUntil t <Δ now≤t ⟩←— tr) , refl ⟩ , P

{-
TraceExtension⁺⁻ : ∀ {Rs : Reachable s} → TraceExtension⁺ Rs → TraceExtension Rs
TraceExtension⁺⁻ tr@(⟨ Rs , st , sts , refl ⟩) =
  ⟨ tr .x , Rs , _ `—→⟨ Local→Global st ⟩ sts  , refl ⟩

TraceExtension⁺⁻⁺ : ∀ {Rs : Reachable s} → TraceExtension⁺ Rs → TraceExtension Rs
TraceExtension⁺⁻⁺ tr@(⟨ Rs , st@(_ ⊣ᴸ eq) , sts , refl ⟩) =
  ⟨ tr .y , _ ⟨ Local→Global st ⟩←—ᴿ Rs , sts  , {!refl!} ⟩
-}

{-
** TODO: traceRs ⇒ non-empty extension (traceRs⁺)

_≺_ : S → S → Type where
  ∼ non-reflexive transitive closure

  s′ ⁺↞— s
  ────────
  s ≺ s′

eventually: ≺-rec (traceRs⁺ st-proposes) Rs′ ...
-}
