{-# OPTIONS --prop #-}

module PropositionalKripke (PV : Set) where

  open import PropUtil
  open import PropositionalLogic PV

  private
    variable
      x : PV
      y : PV
      F : Form
      G : Form
      Γ : Con
      Γ' : Con
      Η : Con
      Η' : Con
  
  record Kripke : Set₁ where
    field
      Worlds : Set₀
      _≤_ : Worlds → Worlds → Prop
      refl≤ : {w : Worlds} → w ≤ w
      tran≤ : {a b c : Worlds} → a ≤ b → b ≤ c → a ≤ c
      _⊩_ : Worlds → PV → Prop
      mon⊩ : {a b : Worlds} → a ≤ b → {p : PV} → a ⊩ p → b ⊩ p

    private
      variable
        w : Worlds
        w' : Worlds
        w₁ : Worlds
        w₂ : Worlds
        w₃ : Worlds
    
    {- Extending ⊩ to Formulas and Contexts -}
    _⊩ᶠ_ : Worlds → Form → Prop
    w ⊩ᶠ Var x = w ⊩ x
    w ⊩ᶠ (fp ⇒ fq) = {w' : Worlds} → w ≤ w' → w' ⊩ᶠ fp → w' ⊩ᶠ fq

    _⊩ᶜ_ : Worlds → Con → Prop
    w ⊩ᶜ [] = ⊤
    w ⊩ᶜ (p ∷ c) = (w ⊩ᶠ p) ∧ (w ⊩ᶜ c)
    
    -- The extensions are monotonous
    mon⊩ᶠ : w ≤ w' → w ⊩ᶠ F → w' ⊩ᶠ F
    mon⊩ᶠ {F = Var x} ww' wF = mon⊩ ww' wF
    mon⊩ᶠ {F = F ⇒ G} ww' wF w'w'' w''F = wF (tran≤ ww' w'w'') w''F

    mon⊩ᶜ : w ≤ w' → w ⊩ᶜ Γ → w' ⊩ᶜ Γ
    mon⊩ᶜ {Γ = []} ww' wΓ = wΓ
    mon⊩ᶜ {Γ = F ∷ Γ} ww' wΓ = ⟨ mon⊩ᶠ {F = F}  ww' (proj₁ wΓ) , mon⊩ᶜ ww' (proj₂ wΓ) ⟩

    {- General operator matching the shape of ⊢ -}
    _⊫_ : Con → Form → Prop
    Γ ⊫ F = {w : Worlds} → w ⊩ᶜ Γ → w ⊩ᶠ F

    {- Soundness -}
    ⟦_⟧ : Γ ⊢ F → Γ ⊫ F
    ⟦ zero ⟧ = proj₁
    ⟦ next p ⟧ = λ x → ⟦ p ⟧ (proj₂ x)
    ⟦ lam p ⟧ = λ wΓ w≤ w'A → ⟦ p ⟧ ⟨ w'A , mon⊩ᶜ w≤ wΓ ⟩
    ⟦ app p p₁ ⟧ wΓ = ⟦ p ⟧ wΓ refl≤ (⟦ p₁ ⟧ wΓ)




  
  {- Universal Kripke -}

  module UniversalKripke where
    Worlds = Con
    _≤_ : Con → Con → Prop
    Γ ≤ Η = Η ⊢⁺ Γ
    _⊩_ : Con → PV → Prop
    Γ ⊩ x = Γ ⊢ Var x

    refl≤ = refl⊢⁺

    -- Proving transitivity
    halftran≤ : {Γ Γ' : Con} → {F : Form} → Γ ⊢⁺ Γ' → Γ' ⊢ F → Γ ⊢ F
    halftran≤ h⁺ zero = proj₁ h⁺
    halftran≤ h⁺ (next h) = halftran≤ (proj₂ h⁺) h
    halftran≤ h⁺ (lam h) = lam (halftran≤ ⟨ zero , addhyp⊢⁺ h⁺ ⟩ h)
    halftran≤ h⁺ (app h h') = app (halftran≤ h⁺ h) (halftran≤ h⁺ h')
    tran≤ : {Γ Γ' Γ'' : Con} → Γ ≤ Γ' → Γ' ≤ Γ'' → Γ ≤ Γ''
    tran≤ {[]} h h' = tt
    tran≤ {x ∷ Γ} h h' = ⟨ halftran≤ h' (proj₁ h) , tran≤ (proj₂ h) h' ⟩

    mon⊩ : {w w' : Con} → w ≤ w' → {x : PV} → w ⊩ x → w' ⊩ x
    mon⊩ h h' = halftran≤ h h' 

  UK : Kripke
  UK = record {UniversalKripke}

  module CompletenessProof where
    open Kripke UK
    open UniversalKripke using (halftran≤)

    ⊩ᶠ→⊢ : {F : Form} → {Γ : Con} → Γ ⊩ᶠ F → Γ ⊢ F
    ⊢→⊩ᶠ : {F : Form} → {Γ : Con} → Γ ⊢ F → Γ ⊩ᶠ F
    ⊢→⊩ᶠ {Var x} h = h
    ⊢→⊩ᶠ {F ⇒ F₁} h {Γ'} iq hF = ⊢→⊩ᶠ {F₁} (app {Γ'} {F} {F₁} (lam (app (halftran≤ (addhyp⊢⁺ iq) h) zero)) (⊩ᶠ→⊢ hF))
    ⊩ᶠ→⊢ {Var x} h = h
    ⊩ᶠ→⊢ {F ⇒ F₁} {Γ} h = lam (⊩ᶠ→⊢ (h (addhyp⊢⁺ refl⊢⁺) (⊢→⊩ᶠ {F} {F ∷ Γ} zero)))

    completeness : {F : Form} → [] ⊫ F → [] ⊢ F
    completeness {F} ⊫F = ⊩ᶠ→⊢ (⊫F tt)

    {- Normalization -}
    norm : [] ⊢ F → [] ⊢ F
    norm x = completeness (⟦ x ⟧)
    -- norm is identity ?!
    idnorm : norm x ≡ x
    idnorm = ?
    -- autonorm : (P₁ P₂ : Prop) → (x₁ : P₁) → (norm x₁ : P₂) → P₁ ≡⊢ P₂
    -- βηnorm : (P₁ P₂ : Prop) → (x₁ : P₁) → (norm x₁ : P₂) → (x₂ : P₂) → norm x₁ ≡ x₂ → P₁ ≡⊢ P₂

    -- autonorm P = {!!}
    --βηnorm P₁ P₂ = ?
