open import Data.Nat
open import Relation.Binary.PropositionalEquality

variable m n l : ℕ

data Term : ℕ → Set where
  zero : Term (suc n)
  suc : Term n → Term (suc n)

variable t u : Term n

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



-}
