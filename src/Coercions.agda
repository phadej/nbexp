module Coercions where

open import Data.Idx using (Idx; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.NP using (NP; []; _∷_; lookup; map)
open import Data.NP.Wk using (Wk; id; wk; skip; keep; wk-idx; _⨟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_ ; _,_)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

data Ty : Set where
  fun : Ty → Ty → Ty
  boo : Ty
  pre : Ty → Ty

Ctx : Set
Ctx = List Ty

variable
  A B C : Ty
  A₁ A₂ B₁ B₂ : Ty
  Γ Δ Ω : Ctx

Var : Ctx → Ty → Set
Var Γ A = Idx A Γ

data Co : Ty → Ty → Set where
  refl : Co A A
  sym  : Co A B → Co B A
  trans : Co A B → Co B C → Co A C
  pre : Co (fun A boo) (pre A)
  fun : Co A₁ A₂ → Co B₁ B₂ → Co (fun A₁ B₁) (fun A₂ B₂)
  fun₁ : Co (fun A₁ B₁) (fun A₂ B₂) → Co A₁ A₂
  fun₂ : Co (fun A₁ B₁) (fun A₂ B₂) → Co B₁ B₂

repr : Ty → Ty
repr (fun A B) = fun (repr A) (repr B)
repr boo       = boo
repr (pre A)   = fun (repr A) boo

fun-inj₁ : fun A₁ B₁ ≡ fun A₂ B₂ → A₁ ≡ A₂
fun-inj₁ refl = refl

fun-inj₂ : fun A₁ B₁ ≡ fun A₂ B₂ → B₁ ≡ B₂
fun-inj₂ refl = refl

coRepr : Co A B → repr A ≡ repr B
coRepr {A = A} {B = B} refl = refl
coRepr {A = A} {B = B} (sym co) = Eq.sym (coRepr co)
coRepr {A = A} {B = B} (trans co co₁) = Eq.trans (coRepr co) (coRepr co₁)
coRepr {A = A} {B = B} pre = refl
coRepr {A = A} {B = B} (fun co co₁) = Eq.cong₂ fun (coRepr co) (coRepr co₁)
coRepr {A = A} {B = B} (fun₁ co) = fun-inj₁ (coRepr co)
coRepr {A = A} {B = B} (fun₂ co) = fun-inj₂ (coRepr co)

impossible : Co boo (fun A B) → ⊥
impossible co with coRepr co
... | ()

data Tm (Γ : Ctx) : Ty → Set where
  var : Var Γ A → Tm Γ A
  app : Tm Γ (fun A B) → Tm Γ A → Tm Γ B
  lam : Tm (A ∷ Γ) B → Tm Γ (fun A B)
  yay : Tm Γ boo
  nay : Tm Γ boo
  coe : Tm Γ A → Co A B → Tm Γ B

wkₓ : Wk Γ Δ → Var Γ A → Var Δ A
wkₓ = wk-idx

{-
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

coe-lam : Nf° (A ∷ Γ) B → Nf° Γ (fun A B)
coe-lam (coeₙ t co) = coeₙ (lamₙ t) (fun refl co)

coe-nf : Nf° Γ A → Co A B → Nf° Γ B
coe-nf (coeₙ t co′) co = coeₙ t (trans co′ co)

coe-ne : Ne Γ A → Co A B → Ne Γ B
coe-ne (varₙ x co′) co = varₙ x (trans co′ co)
coe-ne (appₙ f t) co = appₙ (coe-ne f (fun refl co)) t

coe-app : Ne Γ (fun A B) → Nf° Γ A → Ne Γ B
coe-app f (coeₙ t co) = appₙ (coe-ne f (fun (sym co) refl)) t

wkₙ : Wk Γ Δ → Nf Γ A → Nf Δ A
wkᵦ : Wk Γ Δ → Ne Γ A → Ne Δ A

wkₙ δ (lamₙ t)    = lamₙ (wkₙ (keep δ) t)
wkₙ δ yayₙ        = yayₙ
wkₙ δ nayₙ        = nayₙ
wkₙ δ (neuₙ t)    = neuₙ (wkᵦ δ t)
wkᵦ δ (varₙ x co) = varₙ (wkₓ δ x) co
wkᵦ δ (appₙ f t)  = appₙ (wkᵦ δ f) (wkₙ δ t)

Sem′ : Ctx → Ty → Set
Sem  : Ctx → Ty → Set

-- Semantic values are either neutral terms, or meta-representation of introduction forms
{-# TERMINATING #-}
Sem Γ A = Ne Γ A ⊎ Σ Ty λ B → Sem′ Γ B × Co B A

Sem′ Γ (fun A B) = (Δ : Ctx) → Wk Γ Δ → Sem Δ A → Sem Δ B -- these need to be Sem°
Sem′ Γ boo       = Bool
Sem′ Γ (pre A)   = ⊥

coe-Sem : Sem Γ A → Co A B → Sem Γ B
coe-Sem (inj₁ t)             co = inj₁ (coe-ne t co)
coe-Sem (inj₂ (C , t , co′)) co = inj₂ (C , t , trans co′ co)

wkₚ : Wk Γ Δ → Sem′ Γ A → Sem′ Δ A
wkₛ : Wk Γ Δ → Sem  Γ A → Sem  Δ A

wkₚ {A = fun A B} δ t = λ Ω δ′ x → t Ω (δ ⨟ δ′) x
wkₚ {A = boo}     δ t = t
wkₚ {A = pre A}   δ t = t

wkₛ δ (inj₁ t) = inj₁ (wkᵦ δ t)
wkₛ δ (inj₂ (C , t , co)) = inj₂ (C , wkₚ δ t , co)

raise : (A : Ty) → Ne Γ A → Sem Γ A
raise _ = inj₁

{-# TERMINATING #-}
lower′ : (A : Ty) → Sem′ Γ A → Nf° Γ A
lower  : (A : Ty) → Sem Γ A → Nf° Γ A

lower′ {Γ = Γ} (fun A B) t     = coe-lam (lower B (t (A ∷ Γ) wk (raise A (varₙ zero refl))))
lower′         boo       false = coeₙ nayₙ refl
lower′         boo       true  = coeₙ yayₙ refl
lower′         (pre A)   ()

lower _ (inj₁ t) = coeₙ (neuₙ t) refl
lower A (inj₂ (C , t , co)) = coe-nf (lower′ C t) co

Env : Ctx → Ctx → Set
Env Γ Δ = NP (Sem Δ) Γ

wkₑₙᵥ : Wk Γ Δ → Env Ω Γ → Env Ω Δ
wkₑₙᵥ δ = map (wkₛ δ)

appₛ : Sem Γ (fun A B) → Sem Γ A → Sem Γ B
appₛ (inj₁ f)                    t = raise _ (coe-app f (lower _ t))
appₛ (inj₂ (fun A′ B′ , f , co)) t = coe-Sem (f _ id (coe-Sem t (sym (fun₁ co)))) (fun₂ co)
appₛ (inj₂ (boo , f , co)) t with impossible co
... | ()

eval : Env Γ Δ → Tm Γ A → Sem Δ A
eval γ (var x)     = lookup γ x
-- elimination forms
eval γ (app f t)   = appₛ (eval γ f) (eval γ t)
eval γ (coe t co) = coe-Sem (eval γ t) co
-- introduction forms
eval γ (lam t)     = inj₂ (_ , (λ Ω δ s → eval (s ∷ wkₑₙᵥ δ γ) t) , refl)
eval γ yay = inj₂ (_ , true , refl)
eval γ nay = inj₂ (_ , false , refl)

