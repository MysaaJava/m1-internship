{-# OPTIONS --prop #-}

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


  infix 3 _≡_
  data _≡_ {ℓ}{A : Set ℓ}(a : A) : A → Prop ℓ where
    refl : a ≡ a

  {-# BUILTIN EQUALITY _≡_ #-}

  data Nat : Set where
    zero : Nat
    succ : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}


  record _×_ (A : Set) (B : Set) : Set where
    constructor _,×_
    field
      a : A
      b : B

  record _×'_ (A : Set) (B : Prop) : Set where
    constructor _,×'_
    field
      a : A
      b : B

  record _×''_ (A : Set) (B : A → Prop) : Set where
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

  
