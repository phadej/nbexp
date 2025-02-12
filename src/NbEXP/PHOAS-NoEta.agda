module NbEXP.PHOAS-NoEta where

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)


data Ty : Set where
  emp : Ty
  fun : Ty → Ty → Ty
  sum : Ty → Ty → Ty

variable
  v : Ty → Set
  A B C : Ty

data Tm (v : Ty → Set) : Ty → Set where
  var : v A → Tm v A
  app : Tm v (fun A B) → Tm v A → Tm v B
  lam : (v A → Tm v B) → Tm v (fun A B)
  inl : Tm v A → Tm v (sum A B)
  inr : Tm v B → Tm v (sum A B)
  eit : Tm v (sum A B) → Tm v (fun A C) → Tm v (fun B C) → Tm v C
  abs : Tm v emp → Tm v A

data Nf (v : Ty → Set) : Ty → Set
data Ne (v : Ty → Set) : Ty → Set

data Ne v where
  varₙ : v A → Ne v A
  absₙ : Ne v emp → Ne v A
  appₙ : Ne v (fun A B) → Nf v A → Ne v B
  eitₙ : Ne v (sum A B) → Nf v (fun A C) → Nf v (fun B C) → Ne v C

data Nf v where
  neut : Ne v A → Nf v A
  lamₙ : (v A → Nf v B) → Nf v (fun A B)
  inlₙ : Nf v A → Nf v (sum A B)
  inrₙ : Nf v B → Nf v (sum A B)

Sem  : (Ty → Set) → Ty → Set
Sem′ : (Ty → Set) → Ty → Set

Sem v A = Ne v A ⊎ Sem′ v A

Sem′ v emp       = ⊥
Sem′ v (fun A B) = Sem v A → Sem v B
Sem′ v (sum A B) = Sem v A ⊎ Sem v B

raise : (A : Ty) → Ne v A → Sem v A
raise _ = inj₁

lower  : (A : Ty) → Sem  v A → Nf v A
lower′ : (A : Ty) → Sem′ v A → Nf v A

lower _ (inj₁ x) = neut x
lower A (inj₂ y) = lower′ A y

lower′ emp       ()
lower′ (fun A B) t        = lamₙ λ x → lower B (t (raise A (varₙ x)))
lower′ (sum A B) (inj₁ x) = inlₙ (lower A x)
lower′ (sum A B) (inj₂ y) = inrₙ (lower B y)

appₛ : Sem v (fun A B) → Sem v A → Sem v B
appₛ (inj₁ f) t = inj₁ (appₙ f (lower _ t))
appₛ (inj₂ f) t = f t

absₛ : Sem v emp → Sem v A
absₛ (inj₁ x) = inj₁ (absₙ x)
absₛ (inj₂ ())

eitₛ : Sem v (sum A B) → Sem v (fun A C) → Sem v (fun B C) → Sem v C
eitₛ (inj₁ c)        l r = inj₁ (eitₙ c (lower _ l) (lower _ r))
eitₛ (inj₂ (inj₁ x)) l r = appₛ l x
eitₛ (inj₂ (inj₂ y)) l r = appₛ r y

eval : Tm (Sem v) A → Sem v A
eval (var x)     = x
-- introduction forms
eval (lam t)     = inj₂ (λ x → eval (t x))
eval (inl t)     = inj₂ (inj₁ (eval t))
eval (inr t)     = inj₂ (inj₂ (eval t))
-- elimination forms
eval (app f t)   = appₛ (eval f) (eval t)
eval (abs t)     = absₛ (eval t)
eval (eit c l r) = eitₛ (eval c) (eval l) (eval r)

nf : Tm (Sem v) A → Nf v A
nf {A = A} t = lower A (eval t)

nf_parametric : ({v : Ty → Set} → Tm v A) -> ({v : Ty → Set} → Nf v A)
nf_parametric t = nf t

