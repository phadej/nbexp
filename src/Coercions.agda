module Coercions where

open import Data.Idx using (Idx; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.NP using (NP; []; _∷_; lookup; map)
open import Data.NP.Wk using (Wk; id; wk; skip; keep; wk-idx; _⨟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_ ; _,_)
open import Data.Bool using (Bool; true; false)

data Ty : Set where
  fun : Ty → Ty → Ty
  boo : Ty
  prd : Ty → Ty

Ctx : Set
Ctx = List Ty

variable
  A B C : Ty
  Γ Δ Ω : Ctx

Var : Ctx → Ty → Set
Var Γ A = Idx A Γ

data Co : Ty → Ty → Set where
  refl : Co A A
  sym  : Co A B → Co B A
  trans : Co A B → Co B C → Co A C
  prd : Co (fun A boo) (prd A)

data Tm (Γ : Ctx) : Ty → Set where
  var : Var Γ A → Tm Γ A
  app : Tm Γ (fun A B) → Tm Γ A → Tm Γ B
  lam : Tm (A ∷ Γ) B → Tm Γ (fun A B)
  yay : Tm Γ boo
  nay : Tm Γ boo
  coe : Tm Γ A → Co A B → Tm Γ B

{-
wkₓ : Wk Γ Δ → Var Γ A → Var Δ A
wkₓ = wk-idx

wkₜ : Wk Γ Δ → Tm Γ A → Tm Δ A
wkₜ δ (var x)     = var (wkₓ δ x)
wkₜ δ (app f t)   = app (wkₜ δ f) (wkₜ δ t)
wkₜ δ (lam t)     = lam (wkₜ (keep δ) t)
wkₜ δ (abs t)     = abs (wkₜ δ t)
wkₜ δ (inl t)     = inl (wkₜ δ t)
wkₜ δ (inr t)     = inr (wkₜ δ t)
wkₜ δ (eit t l r) = eit (wkₜ δ t) (wkₜ δ l) (wkₜ δ r)
wkₜ δ zer         = zer
wkₜ δ (suc t)     = suc (wkₜ δ t)
wkₜ δ (ind n z s) = ind (wkₜ δ n) (wkₜ δ z) (wkₜ δ s)
-}

data Nf° (Γ : Ctx) : Ty → Set
data Nf (Γ : Ctx) : Ty → Set
data Ne (Γ : Ctx) : Ty → Set

data Nf° Γ where
  coeₙ : Nf Γ A → Co A B → Nf° Γ B

data Nf Γ where
  lamₙ : Nf (A ∷ Γ) B → Nf Γ (fun A B)
  yayₙ : Nf Γ boo
  nayₙ : Nf Γ boo
  neuₙ : Ne Γ A → Nf Γ B

data Ne Γ where
  varₙ : Var Γ A → Co A B → Ne Γ B
  appₙ : Ne Γ (fun A B) → Nf Γ A → Ne Γ B

wkₙ : Wk Γ Δ → Nf Γ A → Nf Δ A
wkᵦ : Wk Γ Δ → Ne Γ A → Ne Δ A

wkₙ = {!!}
wkᵦ = {!!}

Sem′ : Ctx → Ty → Set
Sem  : Ctx → Ty → Set

-- Semantic values are either neutral terms, or meta-representation of introduction forms
Sem Γ A = Ne Γ A ⊎ Sem′ Γ A

Sem′ Γ (fun A B) = (Δ : Ctx) → Wk Γ Δ → Sem Δ A → Sem Δ B
Sem′ Γ boo       = Bool
Sem′ Γ (prd A)   = {!!}

wkₚ : Wk Γ Δ → Sem′ Γ A → Sem′ Δ A
wkₛ : Wk Γ Δ → Sem  Γ A → Sem  Δ A

wkₚ {A = fun A B} δ t        = λ Ω δ′ x → t Ω (δ ⨟ δ′) x
wkₚ {A = boo}     δ t = t
wkₚ {A = prd A}   δ t = {!!}

wkₛ δ (inj₁ t) = inj₁ (wkᵦ δ t)
wkₛ δ (inj₂ t) = inj₂ (wkₚ δ t)


raise : (A : Ty) → Ne Γ A → Sem Γ A
raise _ = inj₁

lower′ : (A : Ty) → Sem′ Γ A → Nf Γ A
lower  : (A : Ty) → Sem Γ A → Nf Γ A

lower′ {Γ = Γ} (fun A B) t     = lamₙ (lower B (t (A ∷ Γ) wk (raise A (varₙ zero refl))))
lower′         boo       false = nayₙ
lower′         boo       true  = yayₙ
lower′         (prd A)   t     = {!!}

lower _ (inj₁ t) = neuₙ t
lower A (inj₂ t) = lower′ A t


Env : Ctx → Ctx → Set
Env Γ Δ = NP (Sem Δ) Γ

wkₑₙᵥ : Wk Γ Δ → Env Ω Γ → Env Ω Δ
wkₑₙᵥ δ = map (wkₛ δ)


appₛ : Sem Γ (fun A B) → Sem Γ A → Sem Γ B
appₛ (inj₁ f) t = raise _ (appₙ f (lower _ t))
appₛ (inj₂ f) t = f _ id t

eval : Env Γ Δ → Tm Γ A → Sem Δ A
eval γ (var x)     = lookup γ x
-- elimination forms
eval γ (app f t)   = appₛ (eval γ f) (eval γ t)
eval γ (coe t x) = {!!}
-- introduction forms
eval γ (lam t)     = inj₂ λ Ω δ s → eval (s ∷ wkₑₙᵥ δ γ) t
eval γ yay = inj₂ true
eval γ nay = inj₂ false

