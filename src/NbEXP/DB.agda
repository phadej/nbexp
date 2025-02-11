module NbEXP.DB where

open import Data.Idx using (Idx; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.NP using (NP; []; _∷_; lookup; map)
open import Data.NP.Wk using (Wk; id; wk; skip; keep; wk-idx; _⨟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

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
wkₜ δ (abs t)     = abs (wkₜ δ t)
wkₜ δ (inl t)     = inl (wkₜ δ t)
wkₜ δ (inr t)     = inr (wkₜ δ t)
wkₜ δ (eit t l r) = eit (wkₜ δ t) (wkₜ (keep δ) l) (wkₜ (keep δ) r)

-- indicator for types of allowed neutral terms
data N : Ty → Set where
  sumₙ : N (sum A B)
  empₙ : N emp
  -- functions are eta-expanded

data Nf (Γ : Ctx) : Ty → Set
data Ne (Γ : Ctx) : Ty → Set

data Nf Γ where
  lamₙ : Nf (A ∷ Γ) B → Nf Γ (fun A B)
  inlₙ : Nf Γ A → Nf Γ (sum A B)
  inrₙ : Nf Γ B → Nf Γ (sum A B)
  neuₙ : N A → Ne Γ A → Nf Γ A

data Ne Γ where
  varₙ : Var Γ A → Ne Γ A
  appₙ : Ne Γ (fun A B) → Nf Γ A → Ne Γ B
  eitₙ : Ne Γ (sum A B) → Nf (A ∷ Γ) C → Nf (B ∷ Γ) C → Ne Γ C

wkₙ : Wk Γ Δ → Nf Γ A → Nf Δ A
wkᵦ : Wk Γ Δ → Ne Γ A → Ne Δ A

wkₙ δ (lamₙ t)     = lamₙ (wkₙ (keep δ) t)
wkₙ δ (neuₙ a t)   = neuₙ a (wkᵦ δ t)
wkₙ δ (inlₙ t)     = inlₙ (wkₙ δ t)
wkₙ δ (inrₙ t)     = inrₙ (wkₙ δ t)

wkᵦ δ (varₙ x)     = varₙ (wkₓ δ x)
wkᵦ δ (appₙ f t)   = appₙ (wkᵦ δ f) (wkₙ δ t)
wkᵦ δ (eitₙ t l r) = eitₙ (wkᵦ δ t) (wkₙ (keep δ) l) (wkₙ (keep δ) r)

Sem : Ctx → Ty → Set
Sem Γ emp       = Ne Γ emp
Sem Γ (fun A B) = (Δ : Ctx) → Wk Γ Δ → Sem Δ A → Sem Δ B
Sem Γ (sum A B) = Ne Γ (sum A B) ⊎ (Sem Γ A ⊎ Sem Γ B)

wkₛ : Wk Γ Δ → Sem Γ A → Sem Δ A
wkₛ {A = emp}     δ t = wkᵦ δ t
wkₛ {A = fun A B} δ t = λ Ω δ′ x → t Ω (δ ⨟ δ′) x
wkₛ {A = sum A B} δ (inj₁ t)        = inj₁ (wkᵦ δ t)
wkₛ {A = sum A B} δ (inj₂ (inj₁ t)) = inj₂ (inj₁ (wkₛ δ t))
wkₛ {A = sum A B} δ (inj₂ (inj₂ t)) = inj₂ (inj₂ (wkₛ δ t))

appₛ : Sem Γ (fun A B) → Sem Γ A → Sem Γ B
appₛ f t = f _ id t

absₛ : Sem Γ emp → Sem Γ A
absₛ {A = emp}     t = t
absₛ {A = fun A B} t = λ Δ δ s → absₛ (wkᵦ δ t)
absₛ {A = sum A B} t = inj₂ (inj₂ (absₛ t))

Env : Ctx → Ctx → Set
Env Γ Δ = NP (Sem Δ) Γ

wkₑ : Wk Γ Δ → Env Ω Γ → Env Ω Δ
wkₑ δ = map (wkₛ δ)

-- Andreas Abel calls (section 2.3 of his Habilitationsschrift)
-- * lower: reification functions ↓ᵀ
-- * raise: reflection functions ↑ᵀ
--
-- I use lower and raise, as I like justified symbol names :)
-- https://github.com/timvieira/justified-variables
lower : (A : Ty) → Sem Γ A → Nf Γ A
raise : (A : Ty) → Ne Γ A → Sem Γ A

lower     emp       t               = neuₙ empₙ t
lower {Γ} (fun A B) t               = lamₙ (lower B (t (A ∷ Γ) wk (raise A (varₙ zero))))
lower     (sum A B) (inj₁ t)        = neuₙ sumₙ t
lower     (sum A B) (inj₂ (inj₁ t)) = inlₙ (lower A t)
lower     (sum A B) (inj₂ (inj₂ t)) = inrₙ (lower B t)

raise emp       t = t
raise (fun A B) t = λ Δ δ s → raise B (appₙ (wkᵦ δ t) (lower A s))
raise (sum A B) t = inj₁ t

keepₑ : Env Γ Δ → Env (A ∷ Γ) (A ∷ Δ)
keepₑ {A = A} γ = raise A (varₙ zero) ∷ wkₑ wk γ

eval : Env Γ Δ → Tm Γ A → Sem Δ A
eval γ (var x)     = lookup γ x
eval γ (lam t)     = λ Ω δ s → eval (s ∷ wkₑ δ γ) t
eval γ (app f t)   = appₛ (eval γ f) (eval γ t)
eval γ (abs t)     = absₛ (eval γ t)
eval γ (inl t)     = inj₂ (inj₁ (eval γ t))
eval γ (inr t)     = inj₂ (inj₂ (eval γ t))
eval γ (eit t l r) with eval γ t
... | inj₁ t = raise _ (eitₙ t (lower _ (eval (keepₑ γ) l)) (lower _ (eval (keepₑ γ) r)))
... | inj₂ (inj₁ t) = eval (t ∷ γ) l
... | inj₂ (inj₂ t) = eval (t ∷ γ) r

