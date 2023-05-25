{-# OPTIONS --prop #-}

module Normalization (PV : Set) where

  open import PropUtil
  open import PropositionalLogic PV
  open import PropositionalKripke PV

  private
    variable
      A  : Form
      B  : Form
      F  : Form
      G  : Form
      Γ  : Con
      Γ' : Con
      x  : PV

  -- ⊢⁰ are neutral forms
  -- ⊢* are normal forms
  mutual
    data _⊢⁰_ : Con → Form → Prop where
      zero : (A ∷ Γ) ⊢⁰ A
      next : Γ ⊢⁰ A → (B ∷ Γ) ⊢⁰ A
      app : Γ ⊢⁰ (A ⇒ B) → Γ ⊢* A → Γ ⊢⁰ B
    data _⊢*_ : Con → Form → Prop where
      neu⁰ : Γ ⊢⁰ Var x → Γ ⊢* Var x
      lam : (A ∷ Γ) ⊢* B → Γ ⊢* (A ⇒ B)

  ⊢⁰→⊢ : Γ ⊢⁰ F → Γ ⊢ F
  ⊢*→⊢ : Γ ⊢* F → Γ ⊢ F
  ⊢⁰→⊢ zero = zero
  ⊢⁰→⊢ (next h) = next (⊢⁰→⊢ h)
  ⊢⁰→⊢ (app h x) = app (⊢⁰→⊢ h) (⊢*→⊢ x)
  ⊢*→⊢ (neu⁰ x) = ⊢⁰→⊢ x
  ⊢*→⊢ (lam h) = lam (⊢*→⊢ h)

  private
    data _⊆_ : Con → Con → Prop where
       zero⊆ : Γ ⊆ Γ
       next⊆ : Γ ⊆ Γ' → Γ ⊆ (A ∷ Γ')
    retro⊆ : {Γ Γ' : Con} → {A : Form} → (A ∷ Γ) ⊆ Γ' → Γ ⊆ Γ'
    retro⊆ {Γ' = []} () -- Impossible to have «A∷Γ ⊆ []»
    retro⊆ {Γ' = x ∷ Γ'} zero⊆ = next⊆ zero⊆
    retro⊆ {Γ' = x ∷ Γ'} (next⊆ h) = next⊆ (retro⊆ h)


  -- Extension of ⊢⁰ to contexts
  _⊢⁺⁰_ : Con → Con → Prop
  Γ ⊢⁺⁰ [] = ⊤
  Γ ⊢⁺⁰ (F ∷ Γ') = (Γ ⊢⁰ F) ∧ (Γ ⊢⁺⁰ Γ')
  infix 5 _⊢⁺⁰_
  
  -- This relation is reflexive
  private -- Lemma showing that the relation respects ⊆
    mon⊆≤⁰ : Γ' ⊆ Γ → Γ ⊢⁺⁰ Γ'
    mon⊆≤⁰ {[]} sub = tt
    mon⊆≤⁰ {x ∷ Γ} zero⊆ = ⟨ zero , mon⊆≤⁰ (next⊆ zero⊆) ⟩
    mon⊆≤⁰ {x ∷ Γ} (next⊆ sub) = ⟨ (next (proj₁ (mon⊆≤⁰ sub)) ) , mon⊆≤⁰ (next⊆ (retro⊆ sub)) ⟩

  refl⊢⁺⁰ : Γ ⊢⁺⁰ Γ
  refl⊢⁺⁰ {[]} = tt
  refl⊢⁺⁰ {x ∷ Γ} = ⟨ zero , mon⊆≤⁰ (next⊆ zero⊆) ⟩

  -- A useful lemma, that we can add hypotheses 
  addhyp⊢⁺⁰ : Γ ⊢⁺⁰ Γ' → (A ∷ Γ) ⊢⁺⁰ Γ'
  addhyp⊢⁺⁰ {Γ' = []} h = tt
  addhyp⊢⁺⁰ {Γ' = A ∷ Γ'} h = ⟨ next (proj₁ h) , addhyp⊢⁺⁰ (proj₂ h) ⟩


  {- We use a slightly different Universal Kripke Model -}
  module UniversalKripke⁰ where
    Worlds = Con
    _≤_ : Con → Con → Prop
    Γ ≤ Η = Η ⊢⁺⁰ Γ
    _⊩_ : Con → PV → Prop
    Γ ⊩ x = Γ ⊢⁰ Var x

    refl≤ = refl⊢⁺⁰

    -- Proving transitivity
    halftran≤* : {Γ Γ' : Con} → {F : Form} → Γ ⊢⁺⁰ Γ' → Γ' ⊢* F → Γ ⊢* F
    halftran≤⁰ : {Γ Γ' : Con} → {F : Form} → Γ ⊢⁺⁰ Γ' → Γ' ⊢⁰ F → Γ ⊢⁰ F
    halftran≤* h⁺ (neu⁰ x) = neu⁰ (halftran≤⁰ h⁺ x)
    halftran≤* h⁺ (lam h) = lam (halftran≤* ⟨ zero , addhyp⊢⁺⁰ h⁺ ⟩ h)
    halftran≤⁰ h⁺ zero = proj₁ h⁺
    halftran≤⁰ h⁺ (next h) = halftran≤⁰ (proj₂ h⁺) h
    halftran≤⁰ h⁺ (app h h') = app (halftran≤⁰ h⁺ h) (halftran≤* h⁺ h')
    tran≤ : {Γ Γ' Γ'' : Con} → Γ ≤ Γ' → Γ' ≤ Γ'' → Γ ≤ Γ''
    tran≤ {[]} h h' = tt
    tran≤ {x ∷ Γ} h h' = ⟨ halftran≤⁰ h' (proj₁ h) , tran≤ (proj₂ h) h' ⟩

    mon⊩ : {w w' : Con} → w ≤ w' → {x : PV} → w ⊩ x → w' ⊩ x
    mon⊩ h h' = halftran≤⁰ h h'

  
  ⊢*Var : Γ ⊢* Var x → Γ ⊢⁰ Var x
  ⊢*Var (neu⁰ x) = x

  UK⁰ : Kripke
  UK⁰ = record {UniversalKripke⁰}
  open Kripke UK⁰
  open UniversalKripke⁰ using (halftran≤⁰)

  -- quote
  ⊩ᶠ→⊢ : {F : Form} → {Γ : Con} → Γ ⊩ᶠ F → Γ ⊢* F
  -- unquote
  ⊢→⊩ᶠ : {F : Form} → {Γ : Con} → Γ ⊢⁰ F → Γ ⊩ᶠ F

  ⊢→⊩ᶠ {Var x} h = h
  ⊢→⊩ᶠ {F ⇒ F₁} h {Γ'} iq hF = ⊢→⊩ᶠ {F₁} (app {Γ'} {F} {F₁} (halftran≤⁰ iq h) (⊩ᶠ→⊢ hF))
  ⊩ᶠ→⊢ {Var x} h = neu⁰ h
  ⊩ᶠ→⊢ {F ⇒ F₁} {Γ} h = lam (⊩ᶠ→⊢ (h (addhyp⊢⁺⁰ refl⊢⁺⁰) (⊢→⊩ᶠ {F} {F ∷ Γ} zero)))

  
--⊩ᶠ→⊢ {F ⇒ G} {Γ} h =  lam (⊩ᶠ→⊢ {G} (h (addhyp⊢⁺ refl⊢⁺) (⊢→⊩ᶠ {F} {F ∷ Γ} zero)))
  
  {-
  ⊩ᶠ→⊢ {F} zero = neu⁰ zero
  ⊩ᶠ→⊢ {Var x} (next h) = neu⁰ (next {!!})
  ⊩ᶠ→⊢ {F ⇒ G} (next h) = neu⁰ (next {!!})
  ⊩ᶠ→⊢ {F ⇒ G} (lam h) = lam (⊩ᶠ→⊢ h)
  ⊩ᶠ→⊢ {Var x} (app h h₁) = neu⁰ (app {!⊩ᶠ→⊢ h!} (⊩ᶠ→⊢ h₁))
  ⊩ᶠ→⊢ {F ⇒ G} (app h h₁) = neu⁰ (app {!!} (⊩ᶠ→⊢ h₁))
  -}

  {-
  ⊩ᶠ→⊢ {Var x} zero = neu⁰ zero
  ⊩ᶠ→⊢ {Var x} (next h) = neu⁰ (next (⊢*Var (⊩ᶠ→⊢ {Var x} h)))
  ⊩ᶠ→⊢ {Var x} (app {A = A} h h₁) = {!!}
  -- neu⁰ (app {A = A} {!!} (⊩ᶠ→⊢ (CompletenessProof.⊢→⊩ᶠ h₁)))
  ⊩ᶠ→⊢ {F ⇒ G} {Γ} h = lam (⊩ᶠ→⊢ {G} (h (addhyp⊢⁺ refl⊢⁺) (⊢→⊩ᶠ {F} {F ∷ Γ} zero)))
  -}


