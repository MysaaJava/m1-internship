open import Data.Nat
open import Relation.Binary.PropositionalEquality

variable m n : ℕ

data Term : ℕ → Set where
  zero : Term (suc n)
  suc : Term n → Term (suc n)

variable t u : Term n

data Weak : ℕ → Set where
  wk : Weak (suc n)
  suc : Weak n → Weak (suc n)

data Subst : ℕ → Set where
  <_> : Term n → Subst n
  suc : Subst n → Subst (suc n)

_[_]t : Term n → Weak n → Term (suc n)
t [ wk ]t = suc t
zero [ suc w ]t = zero
suc t [ suc w ]t = suc (t [ w ]t)

{-
0  -> 0
1  -> 2
2  -> 3

suc wk


wk
0 -> 1
1 -> 2
2 -> 3
-}

_s[_]t : Term (suc n) → Subst n → Term n
zero s[ < u > ]t = u
suc t s[ < u > ]t = t
zero s[ suc s ]t = zero
suc t s[ suc s ]t = suc (t s[ s ]t)

{-
x,y,z  --> x,z
0,1,2  y => x,z ⊢ t 

x => x  0 => 0
y => t  1 => t
z => z  2 => 1


-}

infix 15 _⇒_

data Form : ℕ → Set where
  _⇒_ : Form n → Form n → Form n
  ∀F : Form (suc n) → Form n
  P : Term n → Form n
--  R : Term n → Term n → Form n

_[_]F : Form n → Weak n → Form (suc n)
(A ⇒ B) [ w ]F = (A [ w ]F) ⇒ (B [ w ]F)
∀F A [ w ]F = ∀F (A [ suc w ]F)
P a [ w ]F = P (a [ w ]t )

_s[_]F : Form (suc n) → Subst n → Form n
(A ⇒ B) s[ s ]F = (A s[ s ]F) ⇒ (B s[ s ]F)
∀F A s[ s ]F = ∀F (A s[ suc s ]F)
P a s[ s ]F = P (a s[ s ]t )

infix 10 _▷_

data Con : ℕ → Set where
  • : Con n
  _▷_ : Con n → Form n → Con n

_[_]C : Con n → Weak n → Con (suc n)
• [ w ]C = •
(Γ ▷ A) [ w ]C = (Γ [ w ]C) ▷ (A [ w ]F)

variable Γ Δ : Con n
variable A B C : Form n

infix 5 _⊢_ 

data _⊢_ : Con n → Form n → Set where
  zero : Γ ▷ A ⊢ A
  suc : Γ ⊢ A → Γ ▷ B ⊢ A
  lam : Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B
  app : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  Lam : Γ [ wk ]C ⊢ A → Γ ⊢ ∀F A
  App : Γ ⊢ ∀F A → (t : Term _) → Γ ⊢ A s[ < t > ]F

-- (A ⇒ ∀ x . P x) ⇒ ∀ x . A → P x

-- A ≡ A [ wk ][ < t > ] 

wk-subst :  (A [ wk ]F) s[ < t > ]F ≡ A
wk-subst = {!!}

example : • ⊢ (A ⇒ (∀F (P zero))) ⇒ (∀F (A [ wk ]F) ⇒ P zero)
example {A = A} = lam (lam (App (app (suc zero) 
         (subst (λ X → (• ▷ A ⇒ ∀F (P zero)) ▷ ∀F (A [ wk ]F) ⊢ X)
           (wk-subst {A = A}) (App zero zero))) zero))


