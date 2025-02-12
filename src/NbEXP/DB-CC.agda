-- de Bruijn with commuting conversions (case of case)
--
-- Following ideas from
-- Normalization by Evaluation for Call-by-Push-Value and Polarized Lambda-Calculus
-- by Andreas Abel and Christian Sattler
--
-- Here normalization is done using case trees.
-- But it can also be done using continuation monad.
--
module NbEXP.DB-CC where

open import Data.Idx using (Idx; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.NP using (NP; []; _∷_; lookup; map)
open import Data.NP.Wk using (Wk; id; wk; skip; keep; wk-idx; _⨟_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _×_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Ty : Set where
  emp : Ty
  one : Ty
  fun : Ty → Ty → Ty
  sum : Ty → Ty → Ty

Ctx : Set
Ctx = List Ty

variable
  A B C D : Ty
  Γ Δ Ω : Ctx

Var : Ctx → Ty → Set
Var Γ A = Idx A Γ

data Tm (Γ : Ctx) : Ty → Set where
  var : Var Γ A → Tm Γ A
  app : Tm Γ (fun A B) → Tm Γ A → Tm Γ B
  lam : Tm (A ∷ Γ) B → Tm Γ (fun A B)
  tth : Tm Γ one
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
wkₜ _ tth         = tth
wkₜ δ (abs t)     = abs (wkₜ δ t)
wkₜ δ (inl t)     = inl (wkₜ δ t)
wkₜ δ (inr t)     = inr (wkₜ δ t)
wkₜ δ (eit t l r) = eit (wkₜ δ t) (wkₜ (keep δ) l) (wkₜ (keep δ) r)

data Nf (Γ : Ctx) : Ty → Set
data Ne (Γ : Ctx) : Ty → Set

-- in this variation we have commuting converisions:
-- F (eit t l r) ↝ eit t (F ∘ l) (F ∘ r)
--
-- in Haskell syntax that's pushing application into the case:
--
-- f (case x of A -> a; B -> b)
-- -->
-- case x of A -> f a; B -> f b
--
-- or case-of-case
--
-- case (case x of A -> l; B -> r) of C -> c; D -> d
-- -->
-- case x of
--   A -> case l of
--     C -> c
--     D -> d
--   B -> case l of
--     C -> c
--     D -> d
--
-- consequences: neutral terms are only "blocked" on variables or application terms.
-- ... and the only neutral terms which can occur are of empty type
--
data Nf Γ where
  lamₙ : Nf (A ∷ Γ) B → Nf Γ (fun A B)
  tthₙ : Nf Γ one
  inlₙ : Nf Γ A → Nf Γ (sum A B)
  inrₙ : Nf Γ B → Nf Γ (sum A B)
  eitₙ : Ne Γ (sum A B) → Nf (A ∷ Γ) C → Nf (B ∷ Γ) C → Nf Γ C
  absₙ : Ne Γ emp → Nf Γ C
  neuₙ : Ne Γ emp → Nf Γ emp

data Ne Γ where
  varₙ : Var Γ A → Ne Γ A
  appₙ : Ne Γ (fun A B) → Nf Γ A → Ne Γ B

wkₙ : Wk Γ Δ → Nf Γ A → Nf Δ A
wkᵦ : Wk Γ Δ → Ne Γ A → Ne Δ A

wkₙ δ (lamₙ t)     = lamₙ (wkₙ (keep δ) t)
wkₙ δ tthₙ         = tthₙ
wkₙ δ (neuₙ t)     = neuₙ (wkᵦ δ t)
wkₙ δ (inlₙ t)     = inlₙ (wkₙ δ t)
wkₙ δ (inrₙ t)     = inrₙ (wkₙ δ t)
wkₙ δ (absₙ t)     = absₙ (wkᵦ δ t)
wkₙ δ (eitₙ t l r) = eitₙ (wkᵦ δ t) (wkₙ (keep δ) l) (wkₙ (keep δ) r)

wkᵦ δ (varₙ x)     = varₙ (wkₓ δ x)
wkᵦ δ (appₙ f t)   = appₙ (wkᵦ δ f) (wkₙ δ t)

-- A very nice monad
data Tree (Γ : Ctx) (C : Ctx → Set) : Set where
  tip : C Γ → Tree Γ C
  pnc : Ne Γ emp → Tree Γ C
  brn : Ne Γ (sum A B) → Tree (A ∷ Γ) C → Tree (B ∷ Γ) C → Tree Γ C

map-tree : {F G : Ctx → Set} → (∀ {Δ} → F Δ → G Δ)  → Tree Γ F → Tree Γ G
map-tree f (tip x)     = tip (f x)
map-tree f (pnc x)     = pnc x
map-tree f (brn c l r) = brn c (map-tree f l) (map-tree f r)

map-tree′ : {F G : Ctx → Set} → (∀ Δ → Wk Γ Δ → F Δ → G Δ) → Tree Γ F → Tree Γ G
map-tree′ f (tip x)     = tip (f _ id x)
map-tree′ f (pnc x)     = pnc x
map-tree′ f (brn c l r) = brn c
  (map-tree′ (λ Ω δ′ → f Ω (wk ⨟ δ′)) l)
  (map-tree′ (λ Ω δ′ → f Ω (wk ⨟ δ′)) r)

join-tree : {F : Ctx → Set} → Tree Γ (λ Δ → Tree Δ F) → Tree Γ F
join-tree (pnc t)     = pnc t
join-tree (tip t)     = t
join-tree (brn c l r) = brn c (join-tree l) (join-tree r)

wk-tree : {F : Ctx → Set} → (∀ {Γ Δ} → Wk Γ Δ → F Γ → F Δ) → Wk Γ Δ → Tree Γ F → Tree Δ F
wk-tree f δ (tip t)     = tip (f δ t)
wk-tree f δ (pnc t)     = pnc (wkᵦ δ t)
wk-tree f δ (brn c l r) = brn (wkᵦ δ c) (wk-tree f (keep δ) l) (wk-tree f (keep δ) r)

Sem : Ctx → Ty → Set
Sem Γ emp       = Tree Γ (λ Δ → ⊥)
Sem Γ one       = ⊤
Sem Γ (fun A B) = (Δ : Ctx) → Wk Γ Δ → Sem Δ A → Sem Δ B
Sem Γ (sum A B) = Tree Γ (λ Δ → Sem Δ A ⊎ Sem Δ B)

wkₛ : Wk Γ Δ → Sem Γ A → Sem Δ A
wkₛ {A = emp}     δ t = wk-tree (λ { δ' () }) δ t
wkₛ {A = one}     _ t = t
wkₛ {A = fun A B} δ t = λ Ω δ′ x → t Ω (δ ⨟ δ′) x
wkₛ {A = sum A B} δ t = wk-tree (λ δ′ → Data.Sum.map (wkₛ δ′) (wkₛ δ′)) δ t

appₛ : Sem Γ (fun A B) → Sem Γ A → Sem Γ B
appₛ f t = f _ id t

eval-tree : Tree Γ (λ Δ → Sem Δ A) → Sem Γ A
eval-tree {A = emp}     t = join-tree t
eval-tree {A = one}     t = tt
eval-tree {A = sum A B} t = join-tree t
eval-tree {A = fun A B} t = λ Δ δ x →
  eval-tree {A = B} (
  map-tree′ (λ Ω δ′ f → f Ω id (wkₛ δ′ x)) (
  wk-tree (λ δ f Δ δ′ s → f Δ (δ ⨟ δ′) s) δ t))

absₛ : Sem Γ emp → Sem Γ A
absₛ {A = A} t = eval-tree {A = A} (map-tree (λ { () }) t)

eitₛ : Sem Γ (sum A B) → Sem Γ (fun A C) → Sem Γ (fun B C) → Sem Γ C
eitₛ c l r = eval-tree (map-tree′ (λ Δ δ x → [ l Δ δ , r Δ δ ]′ x) c)

Env : Ctx → Ctx → Set
Env Γ Δ = NP (Sem Δ) Γ

wkₑ : Wk Γ Δ → Env Ω Γ → Env Ω Δ
wkₑ δ = map (wkₛ δ)

lower : (A : Ty) → Sem Γ A → Nf Γ A
raise : (A : Ty) → Ne Γ A → Sem Γ A

lower-tree-emp : Tree Γ (λ Δ → ⊥) → Nf Γ emp
lower-tree-emp (tip ())
lower-tree-emp (pnc t)     = neuₙ t
lower-tree-emp (brn c l r) = eitₙ c (lower-tree-emp l) (lower-tree-emp r)

lower-tree-sum : Tree Γ (λ Δ → Sem Δ A ⊎ Sem Δ B) → Nf Γ (sum A B)
lower-tree-sum (tip (inj₁ x)) = inlₙ (lower _ x)
lower-tree-sum (tip (inj₂ y)) = inrₙ (lower _ y)
lower-tree-sum (pnc t)        = absₙ t
lower-tree-sum (brn t l r)    = eitₙ t (lower-tree-sum l) (lower-tree-sum r)

lower     emp       t = lower-tree-emp t
lower     one       _ = tthₙ
lower {Γ} (fun A B) t = lamₙ (lower B (t (A ∷ Γ) wk (raise A (varₙ zero))))
lower {Γ} (sum A B) t = lower-tree-sum t

raise emp       t = pnc t
raise one       t = tt
raise (fun A B) t = λ Δ δ s → raise B (appₙ (wkᵦ δ t) (lower A s))
raise (sum A B) t = brn t
  (tip (inj₁ (raise A (varₙ zero))))
  (tip (inj₂ (raise B (varₙ zero))))

eval : Env Γ Δ → Tm Γ A → Sem Δ A
eval γ (var x)     = lookup γ x
eval γ (lam t)     = λ Ω δ s → eval (s ∷ wkₑ δ γ) t
eval γ (app f t)   = appₛ (eval γ f) (eval γ t)
eval γ (abs t)     = absₛ (eval γ t)
eval γ tth         = tt
eval γ (inl t)     = tip (inj₁ (eval γ t))
eval γ (inr t)     = tip (inj₂ (eval γ t))
eval γ (eit t l r) = eitₛ (eval γ t)
  (λ Δ δ x → eval (x ∷ wkₑ δ γ) l)
  (λ Δ δ y → eval (y ∷ wkₑ δ γ) r)

env-Empty : Env [] []
env-Empty = []

module Demo where
  bool : Ty
  bool = sum one one

  false : Tm Γ bool
  false = inl tth

  true : Tm Γ bool
  true = inr tth

  ty : Ty
  ty = fun (sum bool bool) bool

  tm : Tm [] ty
  tm = lam (eit (eit (var zero) (var zero) (var zero)) true false)

  ev : Nf [] ty
  ev = lower {Γ = []} ty (eval env-Empty tm)

  ex : Nf [] ty
  ex = lamₙ
    (eitₙ (varₙ zero)
      (eitₙ (varₙ zero) (inrₙ tthₙ) (inlₙ tthₙ))
      (eitₙ (varₙ zero) (inrₙ tthₙ) (inlₙ tthₙ)))

  _ : ev ≡ ex
  _ = refl

