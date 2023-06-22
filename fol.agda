open import Data.Nat
open import Relation.Binary.PropositionalEquality

variable m n l : ℕ

_$_ : {A B : Set} → (A → B) → A → B
f $ x = f x
infixr 1 _$_

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



-- A ≡ A [ wk ][ < t > ] 

wk-substt : {t : Term (l + n)} → subst-t l (wk-t l t) u ≡ t
wk-substt {zero} = refl
wk-substt {suc l} {t = zero} = refl
wk-substt {suc l} {n} {t = suc t} = cong (λ t → suc t) (wk-substt {l})

wk-substf : {A : Form (l + n)} → subst-F l (wk-F l A) u ≡ A
wk-substf {A = A ⇒ A₁} = cong₂ (λ B B₁ → B ⇒ B₁) wk-substf wk-substf
wk-substf {A = ∀F A} = cong (λ B → ∀F B) wk-substf
wk-substf {l = l} {A = P x} = cong (λ t → P t) (wk-substt {l})

-- (A ⇒ ∀ x . P x) ⇒ ∀ x . A → P x
example : • ⊢ (A ⇒ (∀F (P zero))) ⇒ (∀F (wk-F 0 A) ⇒ P zero)
example {A = A} = lam (lam (App (app (suc zero) (subst (λ Φ → (• ▷ A ⇒ ∀F (P zero)) ▷ ∀F (wk-F 0 A) ⊢ Φ) wk-substf (App zero zero))) zero))

-- (∀ x ∀ y . A(x,y)) ⇒ ∀ y ∀ x . A(y,x)
ex1 : {A : Form 2} → • ⊢ (∀F (∀F A)) ⇒ (∀F (∀F A))
ex1 = lam zero
-- (A ⇒ ∀ x . B(x)) ⇒ ∀ x . A ⇒ B(x)
-- y → ∀x B(x) ==> y → ∀ x B(y)
eq' : {l n : ℕ} → (l + suc n) ≡ (suc (l + n))
eq : {l n : ℕ} → (1 + (l + (suc n))) ≡ (suc (suc (l + n)))
--eq {zero} {zero} = refl
--eq {zero} {suc n} = cong suc (eq {l = 0})
--eq {suc l} = cong suc (eq {l = l})
lm-t : {l n : ℕ} → {t : Term (l + suc n)} → subst-t {n = suc n} l (subst Term (sym eq) (wk-t (suc l) (subst Term eq' t)) ) zero ≡ t
lm-F : {l n : ℕ} → {A : Form (l + suc n)} → subst-F {n = suc n} l (subst Form (sym eq) (wk-F (suc l) (subst Form eq' A)) ) zero ≡ A
lm-t {t = t} = {!!}
lm-F = {!!}
{-
lm-F : {A : Form 1} → subst-F 0 (wk-F 1 A) zero ≡ A
lm-F {A ⇒ A₁} = cong₂ (λ B B₁ → B ⇒ B₁) lm-F lm-F
lm-F {∀F A} = cong (λ B → ∀F B) {!lm-F!}
lm-F {P x} = cong (λ t → P t) lm-t
-}
ex2 : {A : Form 0} → {B : Form 1} → • ⊢ ((A ⇒ (∀F B)))⇒(∀F ((wk-F 0 A) ⇒ B))
ex2 {A = A} {B = B} = lam $ Lam $ lam $ subst (λ C → (• ▷ wk-F zero A ⇒ ∀F (wk-F 1 B)) ▷ wk-F 0 A ⊢ C) lm-F (((App (app (suc zero) zero) zero)))
-- lam (Lam (lam ( subst (λ Φ → (• ▷ wk-F zero A ⇒ ∀F (wk-F 1 B)) ▷ wk-F 0 A ⊢ Φ) (wk-substf {l = 0}) (App (app (suc (suc lm)) (app (suc zero) zero)) zero))))
-- ∀ x y . A(x,y) ⇒ ∀ x . A(x,x)
-- ∀ x . A (x) ⇒ ∀ x y . A(x)
-- (((∀ x . A (x)) ⇒ B)⇒ B) ⇒ ∀ x . ((A (x) ⇒ B) ⇒ B)


