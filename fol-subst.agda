open import Data.Nat
open import Relation.Binary.PropositionalEquality

variable m n l : ℕ

data Term : ℕ → Set where
  zero : Term (suc n)
  suc : Term n → Term (suc n)

variable t u : Term n

data Subst : ℕ → ℕ → Set where
  ε : Subst n 0
  _,_ : Subst m n → Term m → Subst m (suc n)

suc-subst : Subst m n → Subst (suc m) n
suc-subst ε = ε
suc-subst (ts , t) = suc-subst ts , suc t

id : Subst m m
id {zero} = ε
id {suc m} = (suc-subst (id {m})) , zero

subst-t : Term m → Subst n m → Term n
subst-t zero (us , u) = u
subst-t (suc t) (us , u) = subst-t t us

wk-t1 : Term n → Term (suc n)
wk-t1 t = subst-t t (suc-subst id)

subst-t1 : Term (suc n) → Term n → Term n
subst-t1 t u = subst-t t (id , u)

comp : Subst m l → Subst n m → Subst n l
comp ε us = ε
comp (ts , u) us = (comp ts us) , (subst-t u us)

{-
t [ suc vs ] ≡ suc (t [vs ])
suc-subst ts ∘ (us , t) ≡ ts ∘ us

t [ id ] ≡ t
t [ us ∘ vs ] ≡ t [ us ] [ vs ]

ts ∘ id ≡ ts
id ∘ ts ≡ ts
(ts ∘ us) ∘ vs ≡ ts ∘ (us ∘ vs)

-}


{-
wk-t : (l : ℕ) → Term (l + n) → Term (suc (l + n))
wk-t zero t = suc t
wk-t (suc l) zero = zero
wk-t (suc l) (suc t) = suc (wk-t l t)

subst-t : (l : ℕ) → Term (suc (l + n)) → Term n → Term (l + n)
subst-t zero zero u = u
subst-t zero (suc t) u = t
subst-t (suc l) zero u = zero
subst-t (suc l) (suc t) u = suc (subst-t l t u)

infix 15 _⇒_

data Form : ℕ → Set where
  _⇒_ : Form n → Form n → Form n
  ∀F : Form (suc n) → Form n
  P : Term n → Form n
--  R : Term n → Term n → Form n

wk-F : (l : ℕ) → Form (l + n) → Form (suc (l + n))
wk-F l (A ⇒ B) = wk-F l A ⇒ wk-F l B
wk-F l (∀F A) = ∀F (wk-F (suc l) A)
wk-F l (P t) = P (wk-t l t)

subst-F : (l : ℕ) → Form (suc (l + n)) → Term n → Form (l + n)
subst-F l (A ⇒ B) u = subst-F l A u ⇒ subst-F l B u
subst-F l (∀F A) u = ∀F (subst-F (suc l) A u)
subst-F l (P t) u = P (subst-t l t u)

infix 10 _▷_

data Con : ℕ → Set where
  • : Con n
  _▷_ : Con n → Form n → Con n

wk-C : (l : ℕ) → Con (l + n) → Con (suc (l + n))
wk-C l • = •
wk-C l (Γ ▷ A) = wk-C l Γ ▷ wk-F l A

variable Γ Δ : Con n
variable A B C : Form n

infix 5 _⊢_ 

data _⊢_ : Con n → Form n → Set where
  zero : Γ ▷ A ⊢ A
  suc : Γ ⊢ A → Γ ▷ B ⊢ A
  lam : Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B
  app : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  Lam : (wk-C zero Γ) ⊢ A → Γ ⊢ ∀F A
  App : Γ ⊢ ∀F A → (t : Term _) → Γ ⊢ subst-F zero A t

{-
-- (A ⇒ ∀ x . P x) ⇒ ∀ x . A → P x

-- A ≡ A [ wk ][ < t > ] 

wk-subst : subst l (wk l A) t ≡ t

wk-subst :  (A [ wk ]F) s[ < t > ]F ≡ A
wk-subst = {!!}

example : • ⊢ (A ⇒ (∀F (P zero))) ⇒ (∀F (A [ wk ]F) ⇒ P zero)
example {A = A} = lam (lam (App (app (suc zero) 
         (subst (λ X → (• ▷ A ⇒ ∀F (P zero)) ▷ ∀F (A [ wk ]F) ⊢ X)
           (wk-subst {A = A}) (App zero zero))) zero))


-- (∀ x ∀ y . A(x,y)) ⇒ ∀ y ∀ x . A(y,x)
-- (A ⇒ ∀ x . B(x)) ⇒ ∀ x . A ⇒ B(x)   
-- ∀ x y . A(x,y) ⇒ ∀ x . A(x,x)
-- ∀ x . A (x) ⇒ ∀ x y . A(x)
-- (((∀ x . A (x)) ⇒ B)⇒ B) ⇒ ∀ x . ((A (x) ⇒ B) ⇒ B)

-}

--eqq : (suc (suc (l + n))) ≡ suc l + suc n
eqq : (suc (l + n)) ≡ l + suc n
eqq = {!!}

eq : ∀ {t : Term (suc (l + n))}{u : Term n} →
--   subst-t {n = suc n} l (subst Term (eqq {l = l}{n = n})(wk-t {n = n} (suc l) t)) (wk-t zero u)
   subst-t {n = suc n} l (subst Term (eqq {l = (suc l)}{n = n})(wk-t {n = n} (suc l) t)) (wk-t zero u)
   ≡ {! subst-t l t   !} -- subst-t l (wk-t (suc l) t) u ≡ subst-t l t u
eq = {!!}
-}
