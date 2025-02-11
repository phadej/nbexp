module NbEXP.PHOAS where

data Ty : Set where
  emp : Ty
  fun : Ty → Ty → Ty

variable
  v : Ty → Set
  A B C : Ty

data Tm (v : Ty → Set) : Ty → Set where
  var : ∀ {a} → v a → Tm v a
  app : ∀ {a b} → Tm v (fun a b) → Tm v a → Tm v b
  lam : ∀ {a b} → (v a → Tm v b) → Tm v (fun a b)

data Nf (v : Ty → Set) : Ty → Set
data Ne (v : Ty → Set) : Ty → Set

data Ne v where
  nvar : v A → Ne v A
  napp : Ne v (fun A B) → Nf v A → Ne v B

data Nf v where
  neut : Ne v emp → Nf v emp
  nlam : (v A → Nf v B) → Nf v (fun A B)

Sem : (Ty → Set) → Ty → Set
Sem v emp       = Ne v emp
Sem v (fun A B) = Sem v A → Sem v B

eval : Tm (Sem v) A → Sem v A
eval (var x)   = x
eval (app f t) = eval f (eval t)
eval (lam t) x = eval (t x)

lower : (A : Ty) → Sem v A → Nf v A
raise : (A : Ty) → Ne v A → Sem v A

lower emp       s = neut s
lower (fun A B) s = nlam λ x → lower B (s (raise A (nvar x)))

raise emp       n   = n
raise (fun A B) n x = raise B (napp n (lower A x))

nf : Tm (Sem v) A → Nf v A
nf {A = A} t = lower A (eval t)

nf_parametric : ({v : Ty → Set} → Tm v A) -> ({v : Ty → Set} → Nf v A)
nf_parametric t = nf t
