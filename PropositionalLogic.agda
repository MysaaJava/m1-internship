{-# OPTIONS --prop #-}

module PropositionalLogic (PV : Set) where

  open import PropUtil
  open import ListUtil
  
  data Form : Set where
    Var : PV → Form
    _⇒_ : Form → Form → Form
    _∧∧_ : Form → Form → Form

  infixr 10 _∧∧_
  infixr 8 _⇒_

  {- Contexts -}
  Con = List Form

  private
    variable
      A   : Form
      A'  : Form
      B   : Form
      B'  : Form
      C   : Form
      F   : Form
      G   : Form
      Γ   : Con
      Γ'  : Con
      Γ'' : Con
      x   : PV



  {--- DEFINITION OF ⊢ ---}
  
  data _⊢_ : Con → Form → Prop where
    zero : A ∈ Γ → Γ ⊢ A
    lam : (A ∷ Γ) ⊢ B → Γ ⊢ (A ⇒ B)
    app : Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
    andi : Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧∧ B
    ande₁ : Γ ⊢ A ∧∧ B → Γ ⊢ A
    ande₂ : Γ ⊢ A ∧∧ B → Γ ⊢ B

  infix 5 _⊢_
  
  zero⊢ : (A ∷ Γ) ⊢ A
  zero⊢ = zero zero∈
  one⊢ : (B ∷ A ∷ Γ) ⊢ A
  one⊢ = zero (next∈ zero∈)

  -- We can add hypotheses to a proof
  addhyp⊢ : Γ ∈* Γ' → Γ ⊢ A → Γ' ⊢ A
  addhyp⊢ s (zero x) = zero (mon∈∈* x s)
  addhyp⊢ s (lam h) = lam (addhyp⊢ (both∈* s) h)
  addhyp⊢ s (app h h₁) = app (addhyp⊢ s h) (addhyp⊢ s h₁)
  addhyp⊢ s (andi h₁ h₂) = andi (addhyp⊢ s h₁) (addhyp⊢ s h₂)
  addhyp⊢ s (ande₁ h) = ande₁ (addhyp⊢ s h)
  addhyp⊢ s (ande₂ h) = ande₂ (addhyp⊢ s h)

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
  refl⊢⁺ {x ∷ Γ} = ⟨ zero⊢ , mon⊆⊢⁺ (next⊆ zero⊆) ⟩

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

  -- The relation is transitive
  tran⊢⁺ : {Γ Γ' Γ'' : Con} → Γ ⊢⁺ Γ' → Γ' ⊢⁺ Γ'' → Γ ⊢⁺ Γ''
  tran⊢⁺ {Γ'' = []} h h' = tt
  tran⊢⁺ {Γ'' = x ∷ Γ*} h h' = ⟨ halftran⊢⁺ h (proj₁ h') , tran⊢⁺ h (proj₂ h') ⟩

  

  {--- DEFINITIONS OF ⊢⁰ and ⊢* ---}

  -- ⊢⁰ are neutral forms
  -- ⊢* are normal forms
  mutual
    data _⊢⁰_ : Con → Form → Prop where
      zero :  A ∈ Γ → Γ ⊢⁰ A
      app : Γ ⊢⁰ (A ⇒ B) → Γ ⊢* A → Γ ⊢⁰ B
      ande₁ : Γ ⊢⁰ A ∧∧ B → Γ ⊢⁰ A
      ande₂ : Γ ⊢⁰ A ∧∧ B → Γ ⊢⁰ B
    data _⊢*_ : Con → Form → Prop where
      neu⁰ : Γ ⊢⁰ Var x → Γ ⊢* Var x
      lam : (A ∷ Γ) ⊢* B → Γ ⊢* (A ⇒ B)
      andi : Γ ⊢* A → Γ ⊢* B → Γ ⊢* (A ∧∧ B)
  infix 5 _⊢⁰_
  infix 5 _⊢*_

  -- Both are tighter than ⊢
  ⊢⁰→⊢ : Γ ⊢⁰ F → Γ ⊢ F
  ⊢*→⊢ : Γ ⊢* F → Γ ⊢ F
  ⊢⁰→⊢ (zero h) = zero h
  ⊢⁰→⊢ (app h x) = app (⊢⁰→⊢ h) (⊢*→⊢ x)
  ⊢⁰→⊢ (ande₁ h) = ande₁ (⊢⁰→⊢ h)
  ⊢⁰→⊢ (ande₂ h) = ande₂ (⊢⁰→⊢ h)
  ⊢*→⊢ (neu⁰ x) = ⊢⁰→⊢ x
  ⊢*→⊢ (lam h) = lam (⊢*→⊢ h)
  ⊢*→⊢ (andi h₁ h₂) = andi (⊢*→⊢ h₁) (⊢*→⊢ h₂)

  -- We can add hypotheses to a proof
  addhyp⊢⁰ : Γ ∈* Γ' → Γ ⊢⁰ A → Γ' ⊢⁰ A
  addhyp⊢* : Γ ∈* Γ' → Γ ⊢* A → Γ' ⊢* A
  addhyp⊢⁰ s (zero x) = zero (mon∈∈* x s)
  addhyp⊢⁰ s (app h h₁) = app (addhyp⊢⁰ s h) (addhyp⊢* s h₁)
  addhyp⊢⁰ s (ande₁ h) = ande₁ (addhyp⊢⁰ s h)
  addhyp⊢⁰ s (ande₂ h) = ande₂ (addhyp⊢⁰ s h)
  addhyp⊢* s (neu⁰ x) = neu⁰ (addhyp⊢⁰ s x)
  addhyp⊢* s (lam h) = lam (addhyp⊢* (both∈* s) h)
  addhyp⊢* s (andi h₁ h₂) = andi (addhyp⊢* s h₁) (addhyp⊢* s h₂)

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
  halftran⊢⁰⁺⁰ {Γ' = x ∷ Γ'} h⁺ (zero zero∈) = proj₁ h⁺
  halftran⊢⁰⁺⁰ {Γ' = x ∷ Γ'} h⁺ (zero (next∈ h)) = halftran⊢⁰⁺⁰ (proj₂ h⁺) (zero h)
  halftran⊢⁰⁺⁰ h⁺ (app h h') = app (halftran⊢⁰⁺⁰ h⁺ h) (halftran⊢⁰⁺* h⁺ h')
  halftran⊢⁰⁺⁰ h⁺ (ande₁ h) = ande₁ (halftran⊢⁰⁺⁰ h⁺ h)
  halftran⊢⁰⁺⁰ h⁺ (ande₂ h) = ande₂ (halftran⊢⁰⁺⁰ h⁺ h)

  -- The relation is transitive
  tran⊢⁰⁺ : {Γ Γ' Γ'' : Con} → Γ ⊢⁰⁺ Γ' → Γ' ⊢⁰⁺ Γ'' → Γ ⊢⁰⁺ Γ''
  tran⊢⁰⁺ {Γ'' = []} h h' = tt
  tran⊢⁰⁺ {Γ'' = x ∷ Γ} h h' = ⟨ halftran⊢⁰⁺⁰ h (proj₁ h') , tran⊢⁰⁺ h (proj₂ h') ⟩




  {--- Simple translation with in an Environment ---}

  Env = PV → Prop

  ⟦_⟧ᶠ : Form → Env → Prop
  ⟦ Var x ⟧ᶠ ρ = ρ x
  ⟦ A ⇒ B ⟧ᶠ ρ = (⟦ A ⟧ᶠ ρ) → (⟦ B ⟧ᶠ ρ)
  ⟦ A ∧∧ B ⟧ᶠ ρ = (⟦ A ⟧ᶠ ρ) ∧ (⟦ B ⟧ᶠ ρ)

  ⟦_⟧ᶜ : Con → Env → Prop
  ⟦ [] ⟧ᶜ ρ = ⊤
  ⟦ A ∷ Γ ⟧ᶜ ρ = (⟦ A ⟧ᶠ ρ) ∧ (⟦ Γ ⟧ᶜ ρ)

  ⟦_⟧ᵈ : Γ ⊢ A → {ρ : Env} → ⟦ Γ ⟧ᶜ ρ → ⟦ A ⟧ᶠ ρ
  ⟦_⟧ᵈ {x ∷ Γ} (zero zero∈) p = proj₁ p
  ⟦_⟧ᵈ {x ∷ Γ} (zero (next∈ h)) p = ⟦ zero h ⟧ᵈ (proj₂ p)
  ⟦ lam th ⟧ᵈ = λ pₐ p₀ → ⟦ th ⟧ᵈ ⟨ p₀ , pₐ ⟩
  ⟦ app th₁ th₂ ⟧ᵈ = λ p → ⟦ th₁ ⟧ᵈ p (⟦ th₂ ⟧ᵈ p)
  ⟦ andi hf hg ⟧ᵈ = λ p → ⟨ ⟦ hf ⟧ᵈ p , ⟦ hg ⟧ᵈ p ⟩
  ⟦ ande₁ hfg ⟧ᵈ = λ p → proj₁ (⟦ hfg ⟧ᵈ p)
  ⟦ ande₂ hfg ⟧ᵈ = λ p → proj₂ (⟦ hfg ⟧ᵈ p)





  {--- Combinatory Logic ---}

  data ⊢sk : Form → Prop where
    SS : ⊢sk ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    KK : ⊢sk (A ⇒ B ⇒ A)
    ANDi : ⊢sk (A ⇒ B ⇒ (A ∧∧ B))
    ANDe₁ : ⊢sk ((A ∧∧ B) ⇒ A)
    ANDe₂ : ⊢sk ((A ∧∧ B) ⇒ B)
    app : ⊢sk (A ⇒ B) → ⊢sk A → ⊢sk B

  data _⊢skC_ : Con → Form → Prop where
    zero : A ∈ Γ → Γ ⊢skC A
    SS : Γ ⊢skC ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    KK : Γ ⊢skC (A ⇒ B ⇒ A)
    ANDi : Γ ⊢skC (A ⇒ B ⇒ (A ∧∧ B))
    ANDe₁ : Γ ⊢skC ((A ∧∧ B) ⇒ A)
    ANDe₂ : Γ ⊢skC ((A ∧∧ B) ⇒ B)
    app : Γ ⊢skC (A ⇒ B) → Γ ⊢skC A → Γ ⊢skC B

  -- combinatory gives the same proofs as classic
  ⊢⇔⊢sk : ([] ⊢ A) ⇔ ⊢sk A
  
  ⊢sk→⊢ :  ⊢sk A → ([] ⊢ A)
  ⊢sk→⊢ SS = lam (lam (lam ( app (app (zero $ next∈ $ next∈ zero∈) (zero zero∈)) (app (zero $ next∈ $ zero∈) (zero zero∈)))))
  ⊢sk→⊢ KK = lam (lam (zero $ next∈ $ zero∈))
  ⊢sk→⊢ ANDi = lam (lam (andi (zero $ next∈ $ zero∈) (zero zero∈)))
  ⊢sk→⊢ ANDe₁ = lam (ande₁ (zero zero∈))
  ⊢sk→⊢ ANDe₂ = lam (ande₂ (zero zero∈))
  ⊢sk→⊢ (app x x₁) = app (⊢sk→⊢ x) (⊢sk→⊢ x₁)

  skC→sk : [] ⊢skC A → ⊢sk A
  skC→sk SS = SS
  skC→sk KK = KK
  skC→sk ANDi = ANDi
  skC→sk ANDe₁ = ANDe₁
  skC→sk ANDe₂ = ANDe₂
  skC→sk (app d e) = app (skC→sk d) (skC→sk e)


  lam-sk : (A ∷ Γ) ⊢skC B → Γ ⊢skC (A ⇒ B)
  lam-sk-zero : Γ ⊢skC (A ⇒ A)
  lam-sk-zero {A = A} = app (app SS KK) (KK {B = A})
  lam-sk (zero zero∈) = lam-sk-zero
  lam-sk (zero (next∈ h)) = app KK (zero h)
  lam-sk SS = app KK SS
  lam-sk KK = app KK KK
  lam-sk ANDi = app KK (app (app SS (app (app SS (app KK SS)) (app (app SS (app KK KK)) (app (app SS (app KK ANDi)) (lam-sk-zero))))) (app KK lam-sk-zero))
  lam-sk ANDe₁ = app KK (app (app SS (app KK ANDe₁)) lam-sk-zero)
  lam-sk ANDe₂ = app KK (app (app SS (app KK ANDe₂)) lam-sk-zero)
  lam-sk (app x₁ x₂) = app (app SS (lam-sk x₁)) (lam-sk x₂)

  
  ⊢→⊢skC : Γ ⊢ A → Γ ⊢skC A
  ⊢→⊢skC (zero h) = zero h
  ⊢→⊢skC (lam x) = lam-sk (⊢→⊢skC x)
  ⊢→⊢skC (app x x₁) = app (⊢→⊢skC x) (⊢→⊢skC x₁)
  ⊢→⊢skC (andi x y) = app (app ANDi (⊢→⊢skC x)) (⊢→⊢skC y)
  ⊢→⊢skC (ande₁ x) = app ANDe₁ (⊢→⊢skC x)
  ⊢→⊢skC (ande₂ x) = app ANDe₂ (⊢→⊢skC x)

  ⊢⇔⊢sk = ⟨ (λ x → skC→sk (⊢→⊢skC x)) , ⊢sk→⊢ ⟩
