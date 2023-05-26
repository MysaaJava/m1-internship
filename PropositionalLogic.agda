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
      x   : PV



  {--- DEFINITION OF ⊢ ---}
  
  data _⊢_ : Con → Form → Prop where
    zero : (A ∷ Γ) ⊢ A
    next : Γ ⊢ A → (B ∷ Γ) ⊢ A
    lam : (A ∷ Γ) ⊢ B → Γ ⊢ (A ⇒ B)
    app : Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
    andi : Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧∧ B
    ande₁ : Γ ⊢ A ∧∧ B → Γ ⊢ A
    ande₂ : Γ ⊢ A ∧∧ B → Γ ⊢ B

  infix 5 _⊢_

  -- Extension of ⊢ to contexts
  _⊢⁺_ : Con → Con → Prop
  Γ ⊢⁺ [] = ⊤
  Γ ⊢⁺ (F ∷ Γ') = (Γ ⊢ F) ∧ (Γ ⊢⁺ Γ')
  infix 5 _⊢⁺_

  -- The relation respects ⊆
  mon⊆⊢⁺ : Γ' ⊆ Γ → Γ ⊢⁺ Γ'
  mon⊆⊢⁺ {[]} sub = tt
  mon⊆⊢⁺ {x ∷ Γ} zero⊆ = ⟨ zero , mon⊆⊢⁺ (next⊆ zero⊆) ⟩
  mon⊆⊢⁺ {x ∷ Γ} (next⊆ sub) = ⟨ (next (proj₁ (mon⊆⊢⁺ sub)) ) , mon⊆⊢⁺ (next⊆ (retro⊆ sub)) ⟩

  -- The relation is reflexive
  refl⊢⁺ : Γ ⊢⁺ Γ
  refl⊢⁺ {[]} = tt
  refl⊢⁺ {x ∷ Γ} = ⟨ zero , mon⊆⊢⁺ (next⊆ zero⊆) ⟩

  -- We can add hypotheses to the left 
  addhyp⊢⁺ : Γ ⊢⁺ Γ' → (A ∷ Γ) ⊢⁺ Γ'
  addhyp⊢⁺ {Γ' = []} h = tt
  addhyp⊢⁺ {Γ' = A ∷ Γ'} h = ⟨ next (proj₁ h) , addhyp⊢⁺ (proj₂ h) ⟩

  -- The relation respects ⊢
  halftran⊢⁺ : {Γ Γ' : Con} → {F : Form} → Γ ⊢⁺ Γ' → Γ' ⊢ F → Γ ⊢ F
  halftran⊢⁺ h⁺ zero = proj₁ h⁺
  halftran⊢⁺ h⁺ (next h) = halftran⊢⁺ (proj₂ h⁺) h
  halftran⊢⁺ h⁺ (lam h) = lam (halftran⊢⁺ ⟨ zero , addhyp⊢⁺ h⁺ ⟩ h)
  halftran⊢⁺ h⁺ (app h h') = app (halftran⊢⁺ h⁺ h) (halftran⊢⁺ h⁺ h')
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
      zero : (A ∷ Γ) ⊢⁰ A
      next : Γ ⊢⁰ A → (B ∷ Γ) ⊢⁰ A
      app : Γ ⊢⁰ (A ⇒ B) → Γ ⊢* A → Γ ⊢⁰ B
    data _⊢*_ : Con → Form → Prop where
      neu⁰ : Γ ⊢⁰ Var x → Γ ⊢* Var x
      lam : (A ∷ Γ) ⊢* B → Γ ⊢* (A ⇒ B)
  infix 5 _⊢⁰_
  infix 5 _⊢*_

  -- Both are tighter than ⊢
  ⊢⁰→⊢ : Γ ⊢⁰ F → Γ ⊢ F
  ⊢*→⊢ : Γ ⊢* F → Γ ⊢ F
  ⊢⁰→⊢ zero = zero
  ⊢⁰→⊢ (next h) = next (⊢⁰→⊢ h)
  ⊢⁰→⊢ (app h x) = app (⊢⁰→⊢ h) (⊢*→⊢ x)
  ⊢*→⊢ (neu⁰ x) = ⊢⁰→⊢ x
  ⊢*→⊢ (lam h) = lam (⊢*→⊢ h)

  -- Extension of ⊢⁰ to contexts
  -- i.e. there is a neutral proof for any element
  _⊢⁰⁺_ : Con → Con → Prop
  Γ ⊢⁰⁺ [] = ⊤
  Γ ⊢⁰⁺ (F ∷ Γ') = (Γ ⊢⁰ F) ∧ (Γ ⊢⁰⁺ Γ')
  infix 5 _⊢⁰⁺_
  
  -- The relation respects ⊆
  mon⊆⊢⁰⁺ : Γ' ⊆ Γ → Γ ⊢⁰⁺ Γ'
  mon⊆⊢⁰⁺ {[]} sub = tt
  mon⊆⊢⁰⁺ {x ∷ Γ} zero⊆ = ⟨ zero , mon⊆⊢⁰⁺ (next⊆ zero⊆) ⟩
  mon⊆⊢⁰⁺ {x ∷ Γ} (next⊆ sub) = ⟨ (next (proj₁ (mon⊆⊢⁰⁺ sub)) ) , mon⊆⊢⁰⁺ (next⊆ (retro⊆ sub)) ⟩

  -- This relation is reflexive
  refl⊢⁰⁺ : Γ ⊢⁰⁺ Γ
  refl⊢⁰⁺ {[]} = tt
  refl⊢⁰⁺ {x ∷ Γ} = ⟨ zero , mon⊆⊢⁰⁺ (next⊆ zero⊆) ⟩

  -- A useful lemma, that we can add hypotheses 
  addhyp⊢⁰⁺ : Γ ⊢⁰⁺ Γ' → (A ∷ Γ) ⊢⁰⁺ Γ'
  addhyp⊢⁰⁺ {Γ' = []} h = tt
  addhyp⊢⁰⁺ {Γ' = A ∷ Γ'} h = ⟨ next (proj₁ h) , addhyp⊢⁰⁺ (proj₂ h) ⟩

  -- The relation preserves ⊢⁰ and ⊢*
  halftran⊢⁰⁺* : {Γ Γ' : Con} → {F : Form} → Γ ⊢⁰⁺ Γ' → Γ' ⊢* F → Γ ⊢* F
  halftran⊢⁰⁺⁰ : {Γ Γ' : Con} → {F : Form} → Γ ⊢⁰⁺ Γ' → Γ' ⊢⁰ F → Γ ⊢⁰ F
  halftran⊢⁰⁺* h⁺ (neu⁰ x) = neu⁰ (halftran⊢⁰⁺⁰ h⁺ x)
  halftran⊢⁰⁺* h⁺ (lam h) = lam (halftran⊢⁰⁺* ⟨ zero , addhyp⊢⁰⁺ h⁺ ⟩ h)
  halftran⊢⁰⁺⁰ h⁺ zero = proj₁ h⁺
  halftran⊢⁰⁺⁰ h⁺ (next h) = halftran⊢⁰⁺⁰ (proj₂ h⁺) h
  halftran⊢⁰⁺⁰ h⁺ (app h h') = app (halftran⊢⁰⁺⁰ h⁺ h) (halftran⊢⁰⁺* h⁺ h')

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
  ⟦ zero ⟧ᵈ p = proj₁ p
  ⟦ next th ⟧ᵈ p = ⟦ th ⟧ᵈ (proj₂ p)
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
    zero : (A ∷ Γ) ⊢skC A
    next : Γ ⊢skC A → (B ∷ Γ) ⊢skC A
    SS : Γ ⊢skC ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    KK : Γ ⊢skC (A ⇒ B ⇒ A)
    ANDi : Γ ⊢skC (A ⇒ B ⇒ (A ∧∧ B))
    ANDe₁ : Γ ⊢skC ((A ∧∧ B) ⇒ A)
    ANDe₂ : Γ ⊢skC ((A ∧∧ B) ⇒ B)
    app : Γ ⊢skC (A ⇒ B) → Γ ⊢skC A → Γ ⊢skC B

  -- combinatory gives the same proofs as classic
  ⊢⇔⊢sk : ([] ⊢ A) ⇔ ⊢sk A
  
  ⊢sk→⊢ :  ⊢sk A → ([] ⊢ A)
  ⊢sk→⊢ SS = lam (lam (lam ( app (app (next (next zero)) zero) (app (next zero) zero))))
  ⊢sk→⊢ KK = lam (lam (next zero))
  ⊢sk→⊢ ANDi = lam (lam (andi (next zero) zero))
  ⊢sk→⊢ ANDe₁ = lam (ande₁ zero)
  ⊢sk→⊢ ANDe₂ = lam (ande₂ zero)
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
  lam-sk zero = lam-sk-zero
  lam-sk (next x) = app KK x
  lam-sk SS = app KK SS
  lam-sk KK = app KK KK
  lam-sk ANDi = app KK (app (app SS (app (app SS (app KK SS)) (app (app SS (app KK KK)) (app (app SS (app KK ANDi)) (lam-sk-zero))))) (app KK lam-sk-zero))
  lam-sk ANDe₁ = app KK (app (app SS (app KK ANDe₁)) lam-sk-zero)
  lam-sk ANDe₂ = app KK (app (app SS (app KK ANDe₂)) lam-sk-zero)
  lam-sk (app x₁ x₂) = app (app SS (lam-sk x₁)) (lam-sk x₂)

  
  ⊢→⊢skC : Γ ⊢ A → Γ ⊢skC A
  ⊢→⊢skC zero = zero
  ⊢→⊢skC (next x) = next (⊢→⊢skC x)
  ⊢→⊢skC (lam x) = lam-sk (⊢→⊢skC x)
  ⊢→⊢skC (app x x₁) = app (⊢→⊢skC x) (⊢→⊢skC x₁)
  ⊢→⊢skC (andi x y) = app (app ANDi (⊢→⊢skC x)) (⊢→⊢skC y)
  ⊢→⊢skC (ande₁ x) = app ANDe₁ (⊢→⊢skC x)
  ⊢→⊢skC (ande₂ x) = app ANDe₂ (⊢→⊢skC x)

  ⊢⇔⊢sk = ⟨ (λ x → skC→sk (⊢→⊢skC x)) , ⊢sk→⊢ ⟩
