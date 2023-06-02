{-# OPTIONS --prop #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Primitive using (Level)

module FirstOrderLogic (TV : Set) (TV= : TV → TV → Bool) (F : Nat → Set) (R : Nat → Set) where

  open import PropUtil
  open import ListUtil

  mutual
    data Args : Nat → Set where
      zero : Args 0
      next : {n : Nat} → Args n → Term → Args (suc n)
    data Term : Set where
      Var : TV → Term
      Fun : {n : Nat} → F n → Args n → Term
      
  private
    variable
      n : Nat

  if : {ℓ : Level} → {T : Set ℓ} → Bool → T → T → T
  if true a b = a
  if false a b = b
  
  mutual
    [_/_]ᵗ : Term → TV → Term → Term
    [_/_]ᵃ : Term → TV → Args n → Args n
    [ t / x ]ᵗ (Var x') = if (TV= x x') t (Var x')
    [ t / x ]ᵗ (Fun f A) = Fun f ([ t / x ]ᵃ A)
    [ t / x ]ᵃ zero = zero
    [ t / x ]ᵃ (next A t₁) = next ([ t / x ]ᵃ A) ([ t / x ]ᵗ t₁)

  -- A ⊂sub B if B can be obtained with finite substitution from A
  data _⊂sub_ : Args n → Args n → Prop where
    zero : {A : Args n} → A ⊂sub A
    next : {A B : Args n} → {t : Term} → {x : TV} → A ⊂sub B → A ⊂sub ([ t / x ]ᵃ B)

  tran⊂sub : {A B C : Args n} → A ⊂sub B → B ⊂sub C → A ⊂sub C
  tran⊂sub zero h₂ = h₂
  tran⊂sub h₁ zero = h₁
  tran⊂sub h₁ (next h₂) = next (tran⊂sub h₁ h₂)

  data Form : Set where
    Rel : {n : Nat} → R n → (Args n) → Form
    _⇒_ : Form → Form → Form
    _∧∧_ : Form → Form → Form
    ⊤⊤   : Form
    ∀∀ : TV → Form → Form
    
  infixr 10 _∧∧_
  infixr 8 _⇒_
  
  Con = List Form

  private
    variable
      A   : Form
      A'  : Form
      B   : Form
      B'  : Form
      C   : Form
      Γ   : Con
      Γ'  : Con
      Γ'' : Con
      Δ   : Con
      Δ'  : Con
      x   : TV
      t   : Term

  [_/_] : Term → TV → Form → Form
  [ t / x ] (Rel r tz) = Rel r ([ t / x ]ᵃ tz)
  [ t / x ] (A ⇒ A₁) = ([ t / x ] A) ⇒ ([ t / x ] A₁)
  [ t / x ] (A ∧∧ A₁) = ([ t / x ] A) ∧∧ ([ t / x ] A₁)
  [ t / x ] ⊤⊤ = ⊤⊤
  [ t / x ] (∀∀ x₁ A) = if (TV= x x₁) A ([ t / x ] A)

  mutual
    _∉FVᵗ_ : TV → Term → Prop
    _∉FVᵃ_ : TV → Args n → Prop
    x ∉FVᵗ Var x₁ = if (TV= x x₁) ⊥ ⊤
    x ∉FVᵗ Fun f A = x ∉FVᵃ A
    x ∉FVᵃ zero = ⊤
    x ∉FVᵃ next A t = (x ∉FVᵃ A) ∧ (x ∉FVᵗ t)
  _∉FVᶠ_ : TV → Form → Prop
  x ∉FVᶠ Rel R A = x ∉FVᵃ A
  x ∉FVᶠ (A ⇒ A₁) = x ∉FVᶠ A ∧ x ∉FVᶠ A₁
  x ∉FVᶠ (A ∧∧ A₁) = x ∉FVᶠ A ∧ x ∉FVᶠ A₁
  x ∉FVᶠ ⊤⊤ = ⊤
  x ∉FVᶠ ∀∀ x₁ A = if (TV= x x₁) ⊤ (x ∉FVᶠ A)
  _∉FVᶜ_ : TV → Con → Prop
  x ∉FVᶜ [] = ⊤
  x ∉FVᶜ (A ∷ Γ) = x ∉FVᶠ A ∧ x ∉FVᶜ Γ
  
  data _⊢_ : Con → Form → Prop where
    zero : A ∈ Γ → Γ ⊢ A
    lam : (A ∷ Γ) ⊢ B → Γ ⊢ (A ⇒ B)
    app : Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
    andi : Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧∧ B
    ande₁ : Γ ⊢ A ∧∧ B → Γ ⊢ A
    ande₂ : Γ ⊢ A ∧∧ B → Γ ⊢ B
    true : Γ ⊢ ⊤⊤
    ∀-i : x ∉FVᶜ Γ → Γ ⊢ A → Γ ⊢ ∀∀ x A
    ∀-e : Γ ⊢ ∀∀ x A → Γ ⊢ [ t / x ] A 

  infix 5 _⊢_
