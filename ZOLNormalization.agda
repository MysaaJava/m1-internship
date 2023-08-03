{-# OPTIONS --prop --rewriting #-}

module ZOLNormalization (PV : Set) where

  open import ListUtil hiding (zero)
  open import PropUtil hiding (zero)
  open import ZOL PV using (Form; Var; _⇒_; _∧∧_; ⊤⊤; Con)

  open import ZOLKripke PV using (Kripke)

  record Preorder (T : Set₀) : Set₁ where
    constructor order
    field
      _≤_ : T → T → Prop
      refl≤ : {a : T} → a ≤ a
      tran≤ : {a b c : T} → a ≤ b → b ≤ c → a ≤ c

  [_]ᵒᵖ : {T : Set₀} → Preorder T → Preorder T
  [_]ᵒᵖ o = order (λ a b → (Preorder._≤_ o) b a) (Preorder.refl≤ o) (λ h₁ h₂ → (Preorder.tran≤ o) h₂ h₁)

  record NormalAndNeutral : Set₁ where
    field
      _⊢⁰_ : Con → Form → Prop
      _⊢*_ : Con → Form → Prop
      zero : {Γ : Con} → {F : Form} → (F ∷ Γ) ⊢⁰ F
      app : {Γ : Con} → {F G : Form} → Γ ⊢⁰ (F ⇒ G) → Γ ⊢* F → Γ ⊢⁰ G
      ande₁ : {Γ : Con} → {F G : Form} → Γ ⊢⁰ (F ∧∧ G) → Γ ⊢⁰ F
      ande₂ : {Γ : Con} → {F G : Form} → Γ ⊢⁰ (F ∧∧ G) → Γ ⊢⁰ G
      neu⁰ : {Γ : Con} → {x : PV} → Γ ⊢⁰ Var x → Γ ⊢* Var x
      lam : {Γ : Con} → {F G : Form} → (F ∷ Γ) ⊢* G → Γ ⊢* (F ⇒ G)
      andi : {Γ : Con} → {F G : Form} → Γ ⊢* F → Γ ⊢* G → Γ ⊢* (F ∧∧ G)
      true : {Γ : Con} → Γ ⊢* ⊤⊤

  record NormalizationFrame : Set₁ where
    field
      o : Preorder Con
      nn : NormalAndNeutral
      retro : {Γ Δ : Con} → {F : Form} → (Preorder._≤_ o) Γ Δ → (Preorder._≤_ o) Γ (F ∷ Δ)
      ⊢tran : {Γ Δ : Con} → {F : Form} → (Preorder._≤_ o) Γ Δ → (NormalAndNeutral._⊢⁰_ nn) Γ F → (NormalAndNeutral._⊢⁰_ nn) Δ F

    open Preorder o
    open NormalAndNeutral nn

    all : Con → PV → Prop
    all Γ x = ⊤
  
    UK : Kripke
    UK = record {
       Worlds = Con;
       _≤_ = _≤_;
       refl≤ = refl≤;
       tran≤ = tran≤;
       _⊩_ = λ Γ x → Γ ⊢⁰ Var x;
       mon⊩ = λ Γ h → ⊢tran Γ h
       }

    open Kripke UK
    
    -- q is quote, u is unquote
    q : {F : Form} → {Γ : Con} → Γ ⊩ᶠ F → Γ ⊢* F
    u : {F : Form} → {Γ : Con} → Γ ⊢⁰ F → Γ ⊩ᶠ F
  
    u {Var x} h = h
    u {F ⇒ F₁} h {Γ'} iq hF = {!!}
    --u {F ⇒ F₁} h {Γ'} iq hF = u {F₁} (app {Γ'} {F} {F₁} (⊢tran iq h) (q hF))
    u {F ∧∧ G} h = ⟨ (u {F} (ande₁ h)) , (u {G} (ande₂ h)) ⟩
    u {⊤⊤} h = tt
    
    q {Var x} h = neu⁰ h
    q {F ⇒ F₁} {Γ} h = lam (q (h (retro (Preorder.refl≤ o)) (u {F} {F ∷ Γ} zero)))
    q {F ∧∧ G} ⟨ hF , hG ⟩ = andi (q {F} hF) (q {G} hG)
    q {⊤⊤} h = true



  module NormalizationTests where

    {- Now using our records -}
    open import ZOL PV hiding (Form; Var; _⇒_; Con)


    ClassicNN : NormalAndNeutral
    ClassicNN = record
      {
      _⊢⁰_ = _⊢⁰_ ;
      _⊢*_ = _⊢*_ ;
      zero = zero zero∈ ;
      app = app ;
      ande₁ = ande₁;
      ande₂ = ande₂ ;
      neu⁰ = neu⁰ ;
      lam = lam;
      andi = andi;
      true = true
      }

    BiggestNN : NormalAndNeutral
    BiggestNN = record
      {
      _⊢⁰_ = _⊢_ ;
      _⊢*_ = _⊢_ ;
      zero = zero zero∈ ;
      app = app ;
      ande₁ = ande₁ ;
      ande₂ = ande₂ ;
      neu⁰ = λ x → x ;
      lam = lam ;
      andi = andi ;
      true = true
      }

    PO⊢⁺  = [ order {Con} _⊢⁺_  refl⊢⁺  tran⊢⁺  ]ᵒᵖ
    PO⊢⁰⁺ = [ order {Con} _⊢⁰⁺_ refl⊢⁰⁺ tran⊢⁰⁺ ]ᵒᵖ
    PO∈*  = order {Con} _∈*_  refl∈*  tran∈*
    PO⊂⁺  = order {Con} _⊂⁺_  refl⊂⁺  tran⊂⁺
    PO⊂   = order {Con} _⊂_   refl⊂   tran⊂
    PO⊆   = order {Con} _⊆_   refl⊆   tran⊆
    
    -- Completeness Proofs
    Frame⊢ : NormalizationFrame
    Frame⊢ = record
      {
      o = PO⊢⁺ ;
      nn = BiggestNN ;
      retro = λ s → addhyp⊢⁺ (right∈* refl∈*) s ;
      ⊢tran = halftran⊢⁺
      }

    Frame⊢⁰ : NormalizationFrame
    Frame⊢⁰ = record
      {
      o = PO⊢⁰⁺ ;
      nn = ClassicNN ;
      retro = λ s → addhyp⊢⁰⁺ (right∈* refl∈*) s ;
      ⊢tran = halftran⊢⁰⁺⁰
      }

    Frame∈* : NormalizationFrame
    Frame∈* = record
      {
      o = PO∈* ;
      nn = ClassicNN ;
      retro = right∈* ;
      ⊢tran = λ s h → halftran⊢⁰⁺⁰ (mon∈*⊢⁰⁺ s) h
      }

    Frame⊂⁺ : NormalizationFrame
    Frame⊂⁺ = record
      {
      o = PO⊂⁺ ;
      nn = ClassicNN ;
      retro = next⊂⁺ ;
      ⊢tran = λ s h → halftran⊢⁰⁺⁰ (mon∈*⊢⁰⁺ $ ⊂⁺→∈* s) h
      }

    Frame⊂ : NormalizationFrame
    Frame⊂ = record
      {
      o = PO⊂ ;
      nn = ClassicNN ;
      retro = next⊂ ;
      ⊢tran = λ s h → halftran⊢⁰⁺⁰ (mon∈*⊢⁰⁺ $ ⊂⁺→∈* $ ⊂→⊂⁺ s) h
      }

    Frame⊆ : NormalizationFrame
    Frame⊆ = record
      {
      o = PO⊆ ;
      nn = ClassicNN ;
      retro = next⊆ ;
      ⊢tran =  λ s h → halftran⊢⁰⁺⁰ (mon∈*⊢⁰⁺ $ ⊂⁺→∈* $ ⊂→⊂⁺ $ ⊆→⊂ s) h
      }

    
