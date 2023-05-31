{-# OPTIONS --prop #-}

module PropositionalKripke (PV : Set) where

  open import ListUtil
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
    w ⊩ᶠ (fp ∧∧ fq) = w ⊩ᶠ fp ∧ w ⊩ᶠ fq
    
    _⊩ᶜ_ : Worlds → Con → Prop
    w ⊩ᶜ [] = ⊤
    w ⊩ᶜ (p ∷ c) = (w ⊩ᶠ p) ∧ (w ⊩ᶜ c)
    
    -- The extensions are monotonous
    mon⊩ᶠ : w ≤ w' → w ⊩ᶠ F → w' ⊩ᶠ F
    mon⊩ᶠ {F = Var x} ww' wF = mon⊩ ww' wF
    mon⊩ᶠ {F = F ⇒ G} ww' wF w'w'' w''F = wF (tran≤ ww' w'w'') w''F
    mon⊩ᶠ {F = F ∧∧ G} ww' ⟨ wF , wG ⟩ = ⟨ mon⊩ᶠ {F = F} ww' wF , mon⊩ᶠ {F = G} ww' wG ⟩

    mon⊩ᶜ : w ≤ w' → w ⊩ᶜ Γ → w' ⊩ᶜ Γ
    mon⊩ᶜ {Γ = []} ww' wΓ = wΓ
    mon⊩ᶜ {Γ = F ∷ Γ} ww' wΓ = ⟨ mon⊩ᶠ {F = F}  ww' (proj₁ wΓ) , mon⊩ᶜ ww' (proj₂ wΓ) ⟩

    {- General operator matching the shape of ⊢ -}
    _⊫_ : Con → Form → Prop
    Γ ⊫ F = {w : Worlds} → w ⊩ᶜ Γ → w ⊩ᶠ F

    {- Soundness -}
    ⟦_⟧ : Γ ⊢ F → Γ ⊫ F
    ⟦ zero zero∈ ⟧ wΓ = proj₁ wΓ
    ⟦ zero (next∈ h) ⟧ wΓ = ⟦ zero h ⟧ (proj₂ wΓ)
    ⟦ lam p ⟧ = λ wΓ w≤ w'A → ⟦ p ⟧ ⟨ w'A , mon⊩ᶜ w≤ wΓ ⟩
    ⟦ app p p₁ ⟧ wΓ = ⟦ p ⟧ wΓ refl≤ (⟦ p₁ ⟧ wΓ)
    ⟦ andi p₁ p₂ ⟧ = {!!}
    ⟦ ande₁ p ⟧ = {!!}
    ⟦ ande₂ p ⟧ = {!!}



  

  module CompletenessProof where
  
    -- First, we define the Universal Kripke Model with (⊢⁺)⁻¹ as world order
    UK : Kripke
    UK = record {
      Worlds = Con;
      _≤_ = λ x y → y ⊢⁺ x;
      refl≤ = refl⊢⁺;
      tran≤ = λ ΓΓ' Γ'Γ'' → tran⊢⁺ Γ'Γ'' ΓΓ';
      _⊩_ = λ Γ x → Γ ⊢ Var x;
      mon⊩ = λ ba bx → halftran⊢⁺ ba bx
      }
    open Kripke UK
  
    -- Now we can prove that ⊩ᶠ and ⊢ act in the same way
    ⊩ᶠ→⊢ : {F : Form} → {Γ : Con} → Γ ⊩ᶠ F → Γ ⊢ F
    ⊢→⊩ᶠ : {F : Form} → {Γ : Con} → Γ ⊢ F → Γ ⊩ᶠ F
    ⊢→⊩ᶠ {Var x} h = h
    ⊢→⊩ᶠ {F ⇒ F₁} h {Γ'} iq hF = ⊢→⊩ᶠ {F₁} (app {Γ'} {F} {F₁} (lam (app (halftran⊢⁺ (addhyp⊢⁺ (right∈* refl∈*) iq) h) (zero zero∈))) (⊩ᶠ→⊢ hF))
    ⊢→⊩ᶠ {F ∧∧ G} h = {!!}
    ⊩ᶠ→⊢ {Var x} h = h
    ⊩ᶠ→⊢ {F ⇒ F₁} {Γ} h = lam (⊩ᶠ→⊢ (h (addhyp⊢⁺ (right∈* refl∈*) refl⊢⁺) (⊢→⊩ᶠ {F} {F ∷ Γ} (zero zero∈))))
    ⊩ᶠ→⊢ {F ∧∧ G} ⟨ hF , hG ⟩ = {!!}

    -- Finally, we can deduce completeness of the Kripke model
    completeness : {F : Form} → [] ⊫ F → [] ⊢ F
    completeness {F} ⊫F = ⊩ᶠ→⊢ (⊫F tt)

  module NormalizationProof where
    
    -- First we define the Universal model with (⊢⁰⁺)⁻¹ as world order
    -- It is slightly different from the last Model, but proofs are the same
    UK⁰ : Kripke
    UK⁰ = record {
      Worlds = Con;
      _≤_ = λ x y → y ⊢⁰⁺ x;
      refl≤ = refl⊢⁰⁺;
      tran≤ = λ ΓΓ' Γ'Γ'' → tran⊢⁰⁺ Γ'Γ'' ΓΓ';
      _⊩_ = λ Γ x → Γ ⊢⁰ Var x;
      mon⊩ = λ ba bx → halftran⊢⁰⁺⁰ ba bx
      }
    open Kripke UK⁰

    -- We can now prove the normalization, i.e. the quote and function exists
    -- The mutual proofs are exactly the same as the ones used in completeness
    -- quote
    ⊩ᶠ→⊢ : {F : Form} → {Γ : Con} → Γ ⊩ᶠ F → Γ ⊢* F
    -- unquote
    ⊢→⊩ᶠ : {F : Form} → {Γ : Con} → Γ ⊢⁰ F → Γ ⊩ᶠ F
  
    ⊢→⊩ᶠ {Var x} h = h
    ⊢→⊩ᶠ {F ⇒ F₁} h {Γ'} iq hF = ⊢→⊩ᶠ {F₁} (app {Γ'} {F} {F₁} (halftran⊢⁰⁺⁰ iq h) (⊩ᶠ→⊢ hF))
    ⊢→⊩ᶠ {F ∧∧ G} h = ?
    ⊩ᶠ→⊢ {Var x} h = neu⁰ h
    ⊩ᶠ→⊢ {F ⇒ F₁} {Γ} h = lam (⊩ᶠ→⊢ (h (addhyp⊢⁰⁺ (right∈* refl∈*) refl⊢⁰⁺) (⊢→⊩ᶠ {F} {F ∷ Γ} (zero zero∈))))
    ⊩ᶠ→⊢ {F ∧∧ G} h = {!!}

  module OtherProofs where

    -- We will try to define the Kripke models using the following embeddings

    -- Strongest is using the ⊢⁺ relation directly

    -- -> See module CompletenessProof

    -- We can also use the relation ⊢⁰⁺, which is compatible with ⊢⁰ and ⊢*

    -- -> See module NormalizationProof
  
    
  
    {- Renamings : ∈* -}
    UK∈* : Kripke
    UK∈* = record {
      Worlds = Con;
      _≤_ = _∈*_;
      refl≤ = refl∈*;
      tran≤ = tran∈*;
      _⊩_ = λ Γ x → Γ ⊢ Var x;
      mon⊩ = λ x x₁ → addhyp⊢ x x₁
      }
    {-
    {- Weakening anywhere, order preserving, duplication authorized : ⊂⁺ -}
    UK⊂⁺ : Kripke
    UK⊂⁺ = record {
      Worlds = Con;
      _≤_ = _⊂⁺_;
      refl≤ = refl⊂⁺;
      tran≤ = tran⊂⁺;
      _⊩_ = λ Γ x → Γ ⊢ Var x;
      mon⊩ = λ x x₁ → addhyp⊢ x x₁
      }
    -}
    {- Weakening anywhere, no duplication, order preserving : ⊂ -}
    

    {- Weakening at the end : ⊆-}

    -- This is exactly our relation ⊆ 
