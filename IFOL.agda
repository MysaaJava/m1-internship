{-# OPTIONS --prop --rewriting #-}

open import PropUtil

module IFOL (Term : Set) (R : Nat → Set) where

  open import ListUtil

  data Args : Nat → Set where
    zero : Args 0
    next : {n : Nat} → Args n → Term → Args (succ n)
    
  data Form : Set where
    Rel : {n : Nat} → R n → (Args n) → Form
    _⇒_ : Form → Form → Form
    _∧∧_ : Form → Form → Form
    ∀∀ : (Term → Form) → Form
    ⊤⊤ : Form
    
  infixr 10 _∧∧_
  infixr 8 _⇒_


  Con = List Form

  -- Proofs

  private
    variable
      A B : Form
      Γ Γ' Γ'' Δ : Con
      n : Nat
      r : R n
      ts : Args n

  data _⊢_ : Con → Form → Prop where
    zero : A ∈ Γ → Γ ⊢ A
    lam : (A ∷ Γ) ⊢ B → Γ ⊢ (A ⇒ B)
    app : Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
    andi : Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A ∧∧ B)
    ande₁ : Γ ⊢ (A ∧∧ B) → Γ ⊢ A
    ande₂ : Γ ⊢ (A ∧∧ B) → Γ ⊢ B
    true : Γ ⊢ ⊤⊤
    ∀i : {F : Term → Form} → ({t : Term} → Γ ⊢ F t) → Γ ⊢ (∀∀ F)
    ∀e : {F : Term → Form} → Γ ⊢ (∀∀ F) → ( {t : Term} → Γ ⊢ (F t) )



  -- We can add hypotheses to a proof
  addhyp⊢ : Γ ∈* Γ' → Γ ⊢ A → Γ' ⊢ A
  addhyp⊢ s (zero x) = zero (mon∈∈* x s)
  addhyp⊢ s (lam h) = lam (addhyp⊢ (both∈* s) h)
  addhyp⊢ s (app h h₁) = app (addhyp⊢ s h) (addhyp⊢ s h₁)
  addhyp⊢ s (andi h₁ h₂) = andi (addhyp⊢ s h₁) (addhyp⊢ s h₂)
  addhyp⊢ s (ande₁ h) = ande₁ (addhyp⊢ s h)
  addhyp⊢ s (ande₂ h) = ande₂ (addhyp⊢ s h)
  addhyp⊢ s (true) = true
  addhyp⊢ s (∀i h) = ∀i (addhyp⊢ s h)
  addhyp⊢ s (∀e h) = ∀e (addhyp⊢ s h)

  -- Extension of ⊢ to contexts
  _⊢⁺_ : Con → Con → Prop
  Γ ⊢⁺ [] = ⊤
  Γ ⊢⁺ (F ∷ Γ') = (Γ ⊢ F) ∧ (Γ ⊢⁺ Γ')
  infix 5 _⊢⁺_

  -- We show that the relation respects ∈*

  mon∈*⊢⁺ : Γ' ∈* Γ → Γ ⊢⁺ Γ'
  mon∈*⊢⁺ zero∈* = tt
  mon∈*⊢⁺ (next∈* x h) = ⟨ (zero x) , (mon∈*⊢⁺ h) ⟩

  -- The relation respects ⊆
  mon⊆⊢⁺ : Γ' ⊆ Γ → Γ ⊢⁺ Γ'
  mon⊆⊢⁺ h = mon∈*⊢⁺ (⊆→∈* h)

  -- The relation is reflexive
  refl⊢⁺ : Γ ⊢⁺ Γ
  refl⊢⁺ {[]} = tt
  refl⊢⁺ {x ∷ Γ} = ⟨ zero zero∈ , mon⊆⊢⁺ (next⊆ zero⊆) ⟩

  -- We can add hypotheses to to a proof
  addhyp⊢⁺ : Γ ∈* Γ' → Γ ⊢⁺ Γ'' → Γ' ⊢⁺ Γ''
  addhyp⊢⁺ {Γ'' = []} s h = tt
  addhyp⊢⁺ {Γ'' = x ∷ Γ''} s ⟨ Γx , ΓΓ'' ⟩ = ⟨ addhyp⊢ s Γx , addhyp⊢⁺ s ΓΓ'' ⟩
  
  -- The relation respects ⊢
  halftran⊢⁺ : {Γ Γ' : Con} → {F : Form} → Γ ⊢⁺ Γ' → Γ' ⊢ F → Γ ⊢ F
  halftran⊢⁺ {Γ' = F ∷ Γ'} h⁺ (zero zero∈) = proj₁ h⁺
  halftran⊢⁺ {Γ' = F ∷ Γ'} h⁺ (zero (next∈ x)) = halftran⊢⁺ (proj₂ h⁺) (zero x)
  halftran⊢⁺ h⁺ (lam h) = lam (halftran⊢⁺ ⟨ (zero zero∈) , (addhyp⊢⁺ (right∈* refl∈*) h⁺) ⟩ h)
  halftran⊢⁺ h⁺ (app h h₁) = app (halftran⊢⁺ h⁺ h) (halftran⊢⁺ h⁺ h₁)
  halftran⊢⁺ h⁺ (andi hf hg) = andi (halftran⊢⁺ h⁺ hf) (halftran⊢⁺ h⁺ hg)
  halftran⊢⁺ h⁺ (ande₁ hfg) = ande₁ (halftran⊢⁺ h⁺ hfg)
  halftran⊢⁺ h⁺ (ande₂ hfg) = ande₂ (halftran⊢⁺ h⁺ hfg)
  halftran⊢⁺ h⁺ (true) = true
  halftran⊢⁺ h⁺ (∀i h) = ∀i (halftran⊢⁺ h⁺ h)
  halftran⊢⁺ h⁺ (∀e h {t}) = ∀e (halftran⊢⁺ h⁺ h)

  -- The relation is transitive
  tran⊢⁺ : {Γ Γ' Γ'' : Con} → Γ ⊢⁺ Γ' → Γ' ⊢⁺ Γ'' → Γ ⊢⁺ Γ''
  tran⊢⁺ {Γ'' = []} h h' = tt
  tran⊢⁺ {Γ'' = x ∷ Γ*} h h' = ⟨ halftran⊢⁺ h (proj₁ h') , tran⊢⁺ h (proj₂ h') ⟩

 

  {--- DEFINITIONS OF ⊢⁰ and ⊢* ---}

  -- ⊢⁰ are neutral forms
  -- ⊢* are normal forms
  data _⊢⁰_ : Con → Form → Prop
  data _⊢*_ : Con → Form → Prop
  data _⊢⁰_ where
    zero : A ∈ Γ → Γ ⊢⁰ A
    app : Γ ⊢⁰ (A ⇒ B) → Γ ⊢* A → Γ ⊢⁰ B
    ande₁ : Γ ⊢⁰ A ∧∧ B → Γ ⊢⁰ A
    ande₂ : Γ ⊢⁰ A ∧∧ B → Γ ⊢⁰ B
    ∀e : {F : Term → Form} → Γ ⊢⁰ (∀∀ F) → ( {t : Term} → Γ ⊢⁰ (F t) )
  data _⊢*_ where
    neu⁰ : Γ ⊢⁰ Rel r ts → Γ ⊢* Rel r ts
    lam : (A ∷ Γ) ⊢* B → Γ ⊢* (A ⇒ B)
    andi : Γ ⊢* A → Γ ⊢* B → Γ ⊢* (A ∧∧ B)
    ∀i : {F : Term → Form} → ({t : Term} → Γ ⊢* F t) → Γ ⊢* ∀∀ F
    true : Γ ⊢* ⊤⊤
  infix 5 _⊢⁰_
  infix 5 _⊢*_


-- We can add hypotheses to a proof
  addhyp⊢⁰ : Γ ∈* Γ' → Γ ⊢⁰ A → Γ' ⊢⁰ A
  addhyp⊢* : Γ ∈* Γ' → Γ ⊢* A → Γ' ⊢* A
  addhyp⊢⁰ s (zero x) = zero (mon∈∈* x s)
  addhyp⊢⁰ s (app h h₁) = app (addhyp⊢⁰ s h) (addhyp⊢* s h₁)
  addhyp⊢⁰ s (ande₁ h) = ande₁ (addhyp⊢⁰ s h)
  addhyp⊢⁰ s (ande₂ h) = ande₂ (addhyp⊢⁰ s h)
  addhyp⊢⁰ s (∀e h {t}) = ∀e (addhyp⊢⁰ s h) {t}
  addhyp⊢* s (neu⁰ x) = neu⁰ (addhyp⊢⁰ s x)
  addhyp⊢* s (lam h) = lam (addhyp⊢* (both∈* s) h)
  addhyp⊢* s (andi h₁ h₂) = andi (addhyp⊢* s h₁) (addhyp⊢* s h₂)
  addhyp⊢* s true = true
  addhyp⊢* s (∀i h) = ∀i (addhyp⊢* s h)

  -- Extension of ⊢⁰ to contexts
  -- i.e. there is a neutral proof for any element
  _⊢⁰⁺_ : Con → Con → Prop
  Γ ⊢⁰⁺ [] = ⊤
  Γ ⊢⁰⁺ (F ∷ Γ') = (Γ ⊢⁰ F) ∧ (Γ ⊢⁰⁺ Γ')
  infix 5 _⊢⁰⁺_

  -- The relation respects ∈*

  mon∈*⊢⁰⁺ : Γ' ∈* Γ → Γ ⊢⁰⁺ Γ'
  mon∈*⊢⁰⁺ zero∈* = tt
  mon∈*⊢⁰⁺ (next∈* x h) = ⟨ (zero x) , (mon∈*⊢⁰⁺ h) ⟩

  -- The relation respects ⊆
  mon⊆⊢⁰⁺ : Γ' ⊆ Γ → Γ ⊢⁰⁺ Γ'
  mon⊆⊢⁰⁺ h = mon∈*⊢⁰⁺ (⊆→∈* h)

  -- This relation is reflexive
  refl⊢⁰⁺ : Γ ⊢⁰⁺ Γ
  refl⊢⁰⁺ {[]} = tt
  refl⊢⁰⁺ {x ∷ Γ} = ⟨ zero zero∈ , mon⊆⊢⁰⁺ (next⊆ zero⊆) ⟩

  -- A useful lemma, that we can add hypotheses 
  addhyp⊢⁰⁺ : Γ ∈* Γ' → Γ ⊢⁰⁺ Γ'' → Γ' ⊢⁰⁺ Γ''
  addhyp⊢⁰⁺ {Γ'' = []} s h = tt
  addhyp⊢⁰⁺ {Γ'' = A ∷ Γ'} s ⟨ Γx , ΓΓ'' ⟩ = ⟨ addhyp⊢⁰ s Γx , addhyp⊢⁰⁺ s ΓΓ'' ⟩

  -- The relation preserves ⊢⁰ and ⊢*
  halftran⊢⁰⁺* : {Γ Γ' : Con} → {F : Form} → Γ ⊢⁰⁺ Γ' → Γ' ⊢* F → Γ ⊢* F
  halftran⊢⁰⁺⁰ : {Γ Γ' : Con} → {F : Form} → Γ ⊢⁰⁺ Γ' → Γ' ⊢⁰ F → Γ ⊢⁰ F
  halftran⊢⁰⁺* h⁺ (neu⁰ x) = neu⁰ (halftran⊢⁰⁺⁰ h⁺ x)
  halftran⊢⁰⁺* h⁺ (lam h) = lam (halftran⊢⁰⁺* ⟨ zero zero∈ , addhyp⊢⁰⁺ (right∈* refl∈*) h⁺ ⟩ h)
  halftran⊢⁰⁺* h⁺ (andi h₁ h₂) = andi (halftran⊢⁰⁺* h⁺ h₁) (halftran⊢⁰⁺* h⁺ h₂)
  halftran⊢⁰⁺* h⁺ true = true
  halftran⊢⁰⁺* h⁺ (∀i h) = ∀i (halftran⊢⁰⁺* h⁺ h)
  halftran⊢⁰⁺⁰ {Γ' = x ∷ Γ'} h⁺ (zero zero∈) = proj₁ h⁺
  halftran⊢⁰⁺⁰ {Γ' = x ∷ Γ'} h⁺ (zero (next∈ h)) = halftran⊢⁰⁺⁰ (proj₂ h⁺) (zero h)
  halftran⊢⁰⁺⁰ h⁺ (app h h') = app (halftran⊢⁰⁺⁰ h⁺ h) (halftran⊢⁰⁺* h⁺ h')
  halftran⊢⁰⁺⁰ h⁺ (ande₁ h) = ande₁ (halftran⊢⁰⁺⁰ h⁺ h)
  halftran⊢⁰⁺⁰ h⁺ (ande₂ h) = ande₂ (halftran⊢⁰⁺⁰ h⁺ h)
  halftran⊢⁰⁺⁰ h⁺ (∀e h {t}) = ∀e (halftran⊢⁰⁺⁰ h⁺ h)

  -- The relation is transitive
  tran⊢⁰⁺ : {Γ Γ' Γ'' : Con} → Γ ⊢⁰⁺ Γ' → Γ' ⊢⁰⁺ Γ'' → Γ ⊢⁰⁺ Γ''
  tran⊢⁰⁺ {Γ'' = []} h h' = tt
  tran⊢⁰⁺ {Γ'' = x ∷ Γ} h h' = ⟨ halftran⊢⁰⁺⁰ h (proj₁ h') , tran⊢⁰⁺ h (proj₂ h') ⟩

