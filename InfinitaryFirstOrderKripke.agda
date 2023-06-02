{-# OPTIONS --prop #-}

open import Agda.Builtin.Nat

module InfinitaryFirstOrderKripke (Term : Set) (R : Nat → Set) where

  open import ListUtil
  open import PropUtil
  open import InfinitaryFirstOrderLogic Term R

  private
    variable
      x : Term
      y : Term
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
      _⊩_[_] : Worlds → {n : Nat} → R n → Args n → Prop
      mon⊩ : {a b : Worlds} → a ≤ b → {n : Nat} → {r : R n} → {A : Args n} → a ⊩ r [ A ] → b ⊩ r [ A ]

    private
      variable
        w : Worlds
        w' : Worlds
        w₁ : Worlds
        w₂ : Worlds
        w₃ : Worlds
    
    {- Extending ⊩ to Formulas and Contexts -}
    _⊩ᶠ_ : Worlds → Form → Prop
    w ⊩ᶠ (Rel r A) = w ⊩ r [ A ]
    w ⊩ᶠ (fp ⇒ fq) = {w' : Worlds} → w ≤ w' → w' ⊩ᶠ fp → w' ⊩ᶠ fq
    w ⊩ᶠ (fp ∧∧ fq) = w ⊩ᶠ fp ∧ w ⊩ᶠ fq
    w ⊩ᶠ ⊤⊤ = ⊤
    w ⊩ᶠ ∀∀ F = { t : Term } → w ⊩ᶠ F t
    
    _⊩ᶜ_ : Worlds → Con → Prop
    w ⊩ᶜ [] = ⊤
    w ⊩ᶜ (p ∷ c) = (w ⊩ᶠ p) ∧ (w ⊩ᶜ c)
    
    -- The extensions are monotonous
    mon⊩ᶠ : w ≤ w' → w ⊩ᶠ F → w' ⊩ᶠ F
    mon⊩ᶠ {F = Rel r A} ww' wF = mon⊩ ww' wF
    mon⊩ᶠ {F = F ⇒ G} ww' wF w'w'' w''F = wF (tran≤ ww' w'w'') w''F
    mon⊩ᶠ {F = F ∧∧ G} ww' ⟨ wF , wG ⟩ = ⟨ mon⊩ᶠ {F = F} ww' wF , mon⊩ᶠ {F = G} ww' wG ⟩
    mon⊩ᶠ {F = ⊤⊤} ww' wF = tt
    mon⊩ᶠ {F = ∀∀ F} ww' wF {t} = mon⊩ᶠ {F = F t} ww' (wF {t})
  
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
    ⟦ andi p₁ p₂ ⟧ wΓ = ⟨ (⟦ p₁ ⟧ wΓ) , (⟦ p₂ ⟧ wΓ) ⟩
    ⟦ ande₁ p ⟧ wΓ = proj₁ $ ⟦ p ⟧ wΓ
    ⟦ ande₂ p ⟧ wΓ = proj₂ $ ⟦ p ⟧ wΓ
    ⟦ true ⟧ wΓ = tt
    ⟦ ∀i p ⟧ wΓ {t} = ⟦ p {t} ⟧ wΓ
    ⟦ ∀e p {t} ⟧ wΓ = ⟦ p ⟧ wΓ {t}
