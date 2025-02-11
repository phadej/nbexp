module NbEXP.DB-NoEta where

open import Data.Idx using (Idx; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.NP using (NP; []; _∷_; lookup; map)
open import Data.NP.Wk using (Wk; id; wk; skip; keep; wk-idx; _⨟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)

data Ty : Set where
  emp : Ty
  fun : Ty → Ty → Ty
  sum : Ty → Ty → Ty

Ctx : Set
Ctx = List Ty

variable
  A B C : Ty
  Γ Δ Ω : Ctx

Var : Ctx → Ty → Set
Var Γ A = Idx A Γ

data Tm (Γ : Ctx) : Ty → Set where
  var : Var Γ A → Tm Γ A
  app : Tm Γ (fun A B) → Tm Γ A → Tm Γ B
  lam : Tm (A ∷ Γ) B → Tm Γ (fun A B)
  inl : Tm Γ A → Tm Γ (sum A B)
  inr : Tm Γ B → Tm Γ (sum A B)
  eit : Tm Γ (sum A B) → Tm (A ∷ Γ) C → Tm (B ∷ Γ) C → Tm Γ C
  abs : Tm Γ emp → Tm Γ A

wkₓ : Wk Γ Δ → Var Γ A → Var Δ A
wkₓ = wk-idx

wkₜ : Wk Γ Δ → Tm Γ A → Tm Δ A
wkₜ δ (var x)     = var (wkₓ δ x)
wkₜ δ (app f t)   = app (wkₜ δ f) (wkₜ δ t)
wkₜ δ (lam t)     = lam (wkₜ (keep δ) t)
wkₜ δ (inl t)     = inl (wkₜ δ t)
wkₜ δ (inr t)     = inr (wkₜ δ t)
wkₜ δ (eit e l r) = eit (wkₜ δ e) (wkₜ (keep δ) l) (wkₜ (keep δ) r)
wkₜ δ (abs t)     = abs (wkₜ δ t)

data Nf (Γ : Ctx) : Ty → Set
data Ne (Γ : Ctx) : Ty → Set

data Nf Γ where
  lamₙ : Nf (A ∷ Γ) B → Nf Γ (fun A B)
  inlₙ : Nf Γ A → Nf Γ (sum A B)
  inrₙ : Nf Γ B → Nf Γ (sum A B)
  neuₙ : Ne Γ A → Nf Γ A

data Ne Γ where
  varₙ : Var Γ A → Ne Γ A
  appₙ : Ne Γ (fun A B) → Nf Γ A → Ne Γ B
  eitₙ : Ne Γ (sum A B) → Nf (A ∷ Γ) C → Nf (B ∷ Γ) C → Ne Γ C
  absₙ : Ne Γ emp → Ne Γ A

wkₙ : Wk Γ Δ → Nf Γ A → Nf Δ A
wkᵦ : Wk Γ Δ → Ne Γ A → Ne Δ A

wkₙ δ (lamₙ t)     = lamₙ (wkₙ (keep δ) t)
wkₙ δ (neuₙ t)     = neuₙ (wkᵦ δ t)
wkₙ δ (inlₙ t)     = inlₙ (wkₙ δ t)
wkₙ δ (inrₙ t)     = inrₙ (wkₙ δ t)

wkᵦ δ (varₙ x)     = varₙ (wkₓ δ x)
wkᵦ δ (appₙ f t)   = appₙ (wkᵦ δ f) (wkₙ δ t)
wkᵦ δ (absₙ t)     = absₙ (wkᵦ δ t)
wkᵦ δ (eitₙ t l r) = eitₙ (wkᵦ δ t) (wkₙ (keep δ) l) (wkₙ (keep δ) r)

Sem′ : Ctx → Ty → Set
Sem  : Ctx → Ty → Set

-- Semantic values are either neutral terms, or meta-representation of introduction forms
Sem Γ A = Ne Γ A ⊎ Sem′ Γ A

Sem′ Γ emp       = ⊥
Sem′ Γ (fun A B) = (Δ : Ctx) → Wk Γ Δ → Sem Δ A → Sem Δ B
Sem′ Γ (sum A B) = Sem Γ A ⊎ Sem Γ B

wkₚ : Wk Γ Δ → Sem′ Γ A → Sem′ Δ A
wkₛ : Wk Γ Δ → Sem  Γ A → Sem  Δ A

wkₚ {A = emp}     δ t        = t
wkₚ {A = fun A B} δ t        = λ Ω δ′ x → t Ω (δ ⨟ δ′) x
wkₚ {A = sum A B} δ (inj₁ t) = inj₁ (wkₛ δ t)
wkₚ {A = sum A B} δ (inj₂ t) = inj₂ (wkₛ δ t)

wkₛ δ (inj₁ t) = inj₁ (wkᵦ δ t)
wkₛ δ (inj₂ t) = inj₂ (wkₚ δ t)

raise : (A : Ty) → Ne Γ A → Sem Γ A
raise _ = inj₁

lower′ : (A : Ty) → Sem′ Γ A → Nf Γ A
lower  : (A : Ty) → Sem Γ A → Nf Γ A

lower′     emp       ()
lower′ {Γ} (fun A B) t        = lamₙ (lower B (t (A ∷ Γ) wk (raise A (varₙ zero))))
lower′     (sum A B) (inj₁ t) = inlₙ (lower A t)
lower′     (sum A B) (inj₂ t) = inrₙ (lower B t)

lower _ (inj₁ t) = neuₙ t
lower A (inj₂ t) = lower′ A t

Env : Ctx → Ctx → Set
Env Γ Δ = NP (Sem Δ) Γ

wkₑₙᵥ : Wk Γ Δ → Env Ω Γ → Env Ω Δ
wkₑₙᵥ δ = map (wkₛ δ)

keepₑₙᵥ : Env Γ Δ → Env (A ∷ Γ) (A ∷ Δ)
keepₑₙᵥ {A = A} γ = raise A (varₙ zero) ∷ wkₑₙᵥ wk γ

appₛ : Sem Γ (fun A B) → Sem Γ A → Sem Γ B
appₛ (inj₁ f) t = inj₁ (appₙ f (lower _ t))
appₛ (inj₂ f) t = f _ id t

absₛ : Sem Γ emp → Sem Γ A
absₛ (inj₁ t) = inj₁ (absₙ t)
absₛ (inj₂ ())

eval : Env Γ Δ → Tm Γ A → Sem Δ A
eval γ (var x)     = lookup γ x
-- elimination forms
eval γ (app f t)   = appₛ (eval γ f) (eval γ t)
eval γ (abs t)     = absₛ (eval γ t)
eval γ (eit t l r) with eval γ t
... | inj₁ n        = inj₁ (eitₙ n (lower _ (eval (keepₑₙᵥ γ) l)) (lower _ (eval (keepₑₙᵥ γ) r)))
... | inj₂ (inj₁ t) = eval (t ∷ γ) l
... | inj₂ (inj₂ t) = eval (t ∷ γ) r
-- introduction forms
eval γ (lam t)     = inj₂ λ Ω δ s → eval (s ∷ wkₑₙᵥ δ γ) t
eval γ (inl t)     = inj₂ (inj₁ (eval γ t))
eval γ (inr t)     = inj₂ (inj₂ (eval γ t))
