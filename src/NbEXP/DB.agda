module NbEXP.DB where

open import Data.Idx using (Idx; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.NP using (NP; []; _∷_; lookup; map)
open import Data.NP.Wk using (Wk; id; wk; skip; keep; wk-idx; _⨟_)

data Ty : Set where
  emp : Ty
  fun : Ty → Ty → Ty

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
  abs : Tm Γ emp → Tm Γ A

wkₓ : Wk Γ Δ → Var Γ A → Var Δ A
wkₓ = wk-idx

wkₜ : Wk Γ Δ → Tm Γ A → Tm Δ A
wkₜ δ (var x)   = var (wkₓ δ x)
wkₜ δ (app f t) = app (wkₜ δ f) (wkₜ δ t)
wkₜ δ (lam t)   = lam (wkₜ (keep δ) t)
wkₜ δ (abs t)   = abs (wkₜ δ t)

data Nf (Γ : Ctx) : Ty → Set
data Ne (Γ : Ctx) : Ty → Set

data Nf Γ where
  lamₙ : Nf (A ∷ Γ) B → Nf Γ (fun A B)
  neuₙ : Ne Γ emp → Nf Γ emp

data Ne Γ where
  varₙ : Var Γ A → Ne Γ A
  appₙ : Ne Γ (fun A B) → Nf Γ A → Ne Γ B

wkₙ : Wk Γ Δ → Nf Γ A → Nf Δ A
wkᵦ : Wk Γ Δ → Ne Γ A → Ne Δ A

wkₙ δ (lamₙ t)   = lamₙ (wkₙ (keep δ) t)
wkₙ δ (neuₙ t)   = neuₙ (wkᵦ δ t)

wkᵦ δ (varₙ x)   = varₙ (wkₓ δ x)
wkᵦ δ (appₙ f t) = appₙ (wkᵦ δ f) (wkₙ δ t)

Sem : Ctx → Ty → Set
Sem Γ emp       = Ne Γ emp
Sem Γ (fun A B) = (Δ : Ctx) → Wk Γ Δ → Sem Δ A → Sem Δ B

wkₛ : Wk Γ Δ → Sem Γ A → Sem Δ A
wkₛ {A = emp}     δ t = wkᵦ δ t
wkₛ {A = fun A B} δ t = λ Ω δ′ x → t Ω (δ ⨟ δ′) x

appₛ : Sem Γ (fun A B) → Sem Γ A → Sem Γ B
appₛ f t = f _ id t

absₛ : Sem Γ emp → Sem Γ A
absₛ {A = emp}     t = t
absₛ {A = fun A B} t = λ Δ δ s → absₛ (wkᵦ δ t)

Env : Ctx → Ctx → Set
Env Γ Δ = NP (Sem Δ) Γ

wkₑ : Wk Γ Δ → Env Ω Γ → Env Ω Δ
wkₑ δ = map (wkₛ δ)

eval : Env Γ Δ → Tm Γ A → Sem Δ A
eval γ (var x)   = lookup γ x
eval γ (app f t) = appₛ (eval γ f) (eval γ t)
eval γ (lam t)   = λ Ω δ s → eval (s ∷ wkₑ δ γ) t
eval γ (abs t)   = absₛ (eval γ t)

-- Andreas Abel calls (section 2.3 of his Habilitationsschrift)
-- * lower: reification functions ↓ᵀ
-- * raise: reflection functions ↑ᵀ
--
-- I use lower and raise, as I like justified symbol names :)
-- https://github.com/timvieira/justified-variables
lower : (A : Ty) → Sem Γ A → Nf Γ A
raise : (A : Ty) → Ne Γ A → Sem Γ A

lower     emp       t = neuₙ t
lower {Γ} (fun A B) t = lamₙ (lower B (t (A ∷ Γ) wk (raise A (varₙ zero))))

raise emp       t = t
raise (fun A B) t = λ Δ δ s → raise B (appₙ (wkᵦ δ t) (lower A s))
