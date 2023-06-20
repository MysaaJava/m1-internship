{-# OPTIONS --prop --rewriting #-}

module PropUtil where

  -- ⊥ is a data with no constructor
  -- ⊤ is a record with one always-available constructor
  data ⊥ : Prop where
  record ⊤ : Prop where
    constructor tt


  data _∨_ : Prop → Prop → Prop where
    inj₁ : {P Q : Prop} → P → P ∨ Q
    inj₂ : {P Q : Prop} → Q → P ∨ Q

  record _∧_ (P Q : Prop) : Prop where
    constructor ⟨_,_⟩
    field
      p : P
      q : Q
      
  infixr 10 _∧_
  infixr 11 _∨_

  -- ∧ elimination
  proj₁ : {P Q : Prop} → P ∧ Q → P
  proj₁ pq = _∧_.p pq
  proj₂ : {P Q : Prop} → P ∧ Q → Q
  proj₂ pq = _∧_.q pq

  -- ∨ elimination
  dis : {P Q S : Prop} → (P ∨ Q) → (P → S) → (Q → S) → S
  dis (inj₁ p) ps qs = ps p
  dis (inj₂ q) ps qs = qs q
  
  -- ¬ is a shorthand for « → ⊥ »
  ¬ : Prop → Prop
  ¬ P = P → ⊥

  -- ⊥ elimination
  case⊥ : {P : Prop} → ⊥ → P
  case⊥ ()
  
  -- ⇔ shorthand
  _⇔_ : Prop → Prop → Prop
  P ⇔ Q = (P → Q) ∧ (Q → P)


  -- Syntactic sugar for writing applications
  infixr 200 _$_
  _$_ : {T U : Prop} → (T → U) → T → U
  h $ t = h t

  open import Agda.Primitive
  postulate _≈_ : ∀{ℓ}{A : Set ℓ}(a : A) → A → Set ℓ
  {-# BUILTIN REWRITE _≈_ #-}
  infix 3 _≡_
  data _≡_ {ℓ}{A : Set ℓ}(a : A) : A → Prop ℓ where
    refl : a ≡ a

  ≡sym : {ℓ : Level} → {A : Set ℓ}→ {a a' : A} → a ≡ a' → a' ≡ a
  ≡sym refl = refl

  postulate ≡fun : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → {f g : A → B} → ((x : A) → (f x ≡ g x)) → f ≡ g
  postulate ≡fun' : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : A → Set ℓ'} → {f g : (a : A) → B a} → ((x : A) → (f x ≡ g x)) → f ≡ g

  postulate subst       : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Set ℓ'){a a' : A} → a ≡ a' → P a → P a'
  postulate substP      : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Prop ℓ'){a a' : A} → a ≡ a' → P a → P a'

  postulate substrefl   : ∀{ℓ}{A : Set ℓ}{ℓ'}{P : A → Set ℓ'}{a : A}{e : a ≡ a}{p : P a} → subst P e p ≈ p
  {-# REWRITE substrefl   #-}

  {-# BUILTIN EQUALITY _≡_ #-}

  data Nat : Set where
    zero : Nat
    succ : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}
  variable
    ℓ ℓ' : Level

  record _×_ (A : Set ℓ) (B : Set ℓ) : Set ℓ where
    constructor _,×_
    field
      a : A
      b : B

  record _×'_ (A : Set ℓ) (B : Prop ℓ) : Set ℓ where
    constructor _,×'_
    field
      a : A
      b : B

  record _×''_ (A : Set ℓ) (B : A → Prop ℓ') : Set (ℓ ⊔ ℓ') where
    constructor _,×''_
    field
      a : A
      b : B a

  proj×₁ : {A B : Set} → (A × B) → A
  proj×₁ p = _×_.a p
  proj×₂ : {A B : Set} → (A × B) → B
  proj×₂ p = _×_.b p

  proj×'₁ : {A : Set} → {B : Prop} → (A ×' B) → A
  proj×'₁ p = _×'_.a p
  proj×'₂ : {A : Set} → {B : Prop} → (A ×' B) → B
  proj×'₂ p = _×'_.b p

  proj×''₁ : {A : Set} → {B : A → Prop} → (A ×'' B) → A
  proj×''₁ p = _×''_.a p
  proj×''₂ : {A : Set} → {B : A → Prop} → (p : A ×'' B) → B (proj×''₁ p)
  proj×''₂ p = _×''_.b p

  
