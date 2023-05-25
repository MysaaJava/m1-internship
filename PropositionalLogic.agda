{-# OPTIONS --prop #-}

module PropositionalLogic (PV : Set) where

  open import PropUtil
  open import Data.List using (List; _∷_; []) public

  data Form : Set where
    Var : PV → Form
    _⇒_ : Form → Form → Form
  
  infixr 8 _⇒_

  data _≡_ : {A : Set} → A → A → Prop where
    refl : {A : Set} → {x : A} → x ≡ x

  {- Contexts -}
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

  -- Definition of subcontexts (directly included)
  -- Similar definition : {Γ' : Con} → Γ ⊆ Γ' ++ Γ
  private
    data _⊆_ : Con → Con → Prop where
       zero⊆ : Γ ⊆ Γ
       next⊆ : Γ ⊆ Γ' → Γ ⊆ (A ∷ Γ')
    retro⊆ : {Γ Γ' : Con} → {A : Form} → (A ∷ Γ) ⊆ Γ' → Γ ⊆ Γ'
    retro⊆ {Γ' = []} () -- Impossible to have «A∷Γ ⊆ []»
    retro⊆ {Γ' = x ∷ Γ'} zero⊆ = next⊆ zero⊆
    retro⊆ {Γ' = x ∷ Γ'} (next⊆ h) = next⊆ (retro⊆ h)

  
  data _⊢_ : Con → Form → Prop where
    zero : (A ∷ Γ) ⊢ A
    next : Γ ⊢ A → (B ∷ Γ) ⊢ A
    lam : (A ∷ Γ) ⊢ B → Γ ⊢ (A ⇒ B)
    app : Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B

  infix 5 _⊢_

  -- Extension of ⊢ to contexts
  _⊢⁺_ : Con → Con → Prop
  Γ ⊢⁺ [] = ⊤
  Γ ⊢⁺ (F ∷ Γ') = (Γ ⊢ F) ∧ (Γ ⊢⁺ Γ')
  infix 5 _⊢⁺_
  
  -- This relation is reflexive
  private -- Lemma showing that the relation respects ⊆
    mon⊆≤ : Γ' ⊆ Γ → Γ ⊢⁺ Γ'
    mon⊆≤ {[]} sub = tt
    mon⊆≤ {x ∷ Γ} zero⊆ = ⟨ zero , mon⊆≤ (next⊆ zero⊆) ⟩
    mon⊆≤ {x ∷ Γ} (next⊆ sub) = ⟨ (next (proj₁ (mon⊆≤ sub)) ) , mon⊆≤ (next⊆ (retro⊆ sub)) ⟩

  refl⊢⁺ : Γ ⊢⁺ Γ
  refl⊢⁺ {[]} = tt
  refl⊢⁺ {x ∷ Γ} = ⟨ zero , mon⊆≤ (next⊆ zero⊆) ⟩

  -- A useful lemma, that we can add hypotheses 
  addhyp⊢⁺ : Γ ⊢⁺ Γ' → (A ∷ Γ) ⊢⁺ Γ'
  addhyp⊢⁺ {Γ' = []} h = tt
  addhyp⊢⁺ {Γ' = A ∷ Γ'} h = ⟨ next (proj₁ h) , addhyp⊢⁺ (proj₂ h) ⟩
    
  {--- Simple translation with in an Environment ---}

  Env = PV → Prop

  ⟦_⟧ᶠ : Form → Env → Prop
  ⟦ Var x ⟧ᶠ ρ = ρ x
  ⟦ A ⇒ B ⟧ᶠ ρ = (⟦ A ⟧ᶠ ρ) → (⟦ B ⟧ᶠ ρ)

  ⟦_⟧ᶜ : Con → Env → Prop
  ⟦ [] ⟧ᶜ ρ = ⊤
  ⟦ A ∷ Γ ⟧ᶜ ρ = (⟦ A ⟧ᶠ ρ) ∧ (⟦ Γ ⟧ᶜ ρ)

  ⟦_⟧ᵈ : Γ ⊢ A → {ρ : Env} → ⟦ Γ ⟧ᶜ ρ → ⟦ A ⟧ᶠ ρ
  ⟦ zero ⟧ᵈ p = proj₁ p
  ⟦ next th ⟧ᵈ p = ⟦ th ⟧ᵈ (proj₂ p)
  ⟦ lam th ⟧ᵈ = λ pₐ p₀ → ⟦ th ⟧ᵈ ⟨ p₀ , pₐ ⟩
  ⟦ app th₁ th₂ ⟧ᵈ = λ p → ⟦ th₁ ⟧ᵈ p (⟦ th₂ ⟧ᵈ p)


  {--- Combinatory Logic ---}

  data ⊢sk : Form → Prop where
    SS : ⊢sk ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    KK : ⊢sk (A ⇒ B ⇒ A)
    app : ⊢sk (A ⇒ B) → ⊢sk A → ⊢sk B

  data _⊢skC_ : Con → Form → Prop where
    zero : (A ∷ Γ) ⊢skC A
    next : Γ ⊢skC A → (B ∷ Γ) ⊢skC A
    SS : Γ ⊢skC ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    KK : Γ ⊢skC (A ⇒ B ⇒ A)
    app : Γ ⊢skC (A ⇒ B) → Γ ⊢skC A → Γ ⊢skC B


  -- combinatory gives the same proofs as classic
  ⊢⇔⊢sk : ([] ⊢ A) ⇔ ⊢sk A
  
  ⊢sk→⊢ :  ⊢sk A → ([] ⊢ A)
  ⊢sk→⊢ SS = lam (lam (lam ( app (app (next (next zero)) zero) (app (next zero) zero))))
  ⊢sk→⊢ KK = lam (lam (next zero))
  ⊢sk→⊢ (app x x₁) = app (⊢sk→⊢ x) (⊢sk→⊢ x₁)

  skC→sk : [] ⊢skC A → ⊢sk A
  skC→sk SS = SS
  skC→sk KK = KK
  skC→sk (app d e) = app (skC→sk d) (skC→sk e)


  lam-sk : (A ∷ Γ) ⊢skC B → Γ ⊢skC (A ⇒ B)
  lam-sk-zero : Γ ⊢skC (A ⇒ A)
  lam-sk-zero {A = A} = app (app SS KK) (KK {B = A})
  lam-sk zero = lam-sk-zero
  lam-sk (next x) = app KK x
  lam-sk SS = app KK SS
  lam-sk KK = app KK KK
  lam-sk (app x₁ x₂) = app (app SS (lam-sk x₁)) (lam-sk x₂)

  ⊢→⊢skC : Γ ⊢ A → Γ ⊢skC A
  ⊢→⊢skC zero = zero
  ⊢→⊢skC (next x) = next (⊢→⊢skC x)
  ⊢→⊢skC (lam x) = lam-sk (⊢→⊢skC x)
  ⊢→⊢skC (app x x₁) = app (⊢→⊢skC x) (⊢→⊢skC x₁)

  ⊢⇔⊢sk = ⟨ (λ x → skC→sk (⊢→⊢skC x)) , ⊢sk→⊢ ⟩
