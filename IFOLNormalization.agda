{-# OPTIONS --prop --rewriting #-}

open import PropUtil hiding (zero)

module IFOLNormalization (Term : Set) (R : Nat → Set) where

  open import ListUtil hiding (zero)
  open import IFOL Term R using (Form; Args; Rel; _⇒_; _∧∧_; ⊤⊤; ∀∀; Con)

  open import IFOLKripke Term R using (Kripke)

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
      ∀e : {Γ : Con} → {F : Term → Form} → Γ ⊢⁰ (∀∀ F) → ( {t : Term} → Γ ⊢⁰ (F t) )
      neu⁰ : {Γ : Con} → {n : Nat} → {r : R n} → {A : Args n} → Γ ⊢⁰ Rel r A → Γ ⊢* Rel r A
      lam : {Γ : Con} → {F G : Form} → (F ∷ Γ) ⊢* G → Γ ⊢* (F ⇒ G)
      andi : {Γ : Con} → {F G : Form} → Γ ⊢* F → Γ ⊢* G → Γ ⊢* (F ∧∧ G)
      ∀i : {Γ : Con} → {F : Term → Form} → ({t : Term} → Γ ⊢* F t) → Γ ⊢* ∀∀ F
      true : {Γ : Con} → Γ ⊢* ⊤⊤

  record NormalizationFrame : Set₁ where
    field
      o : Preorder Con
      nn : NormalAndNeutral
      retro : {Γ Δ : Con} → {F : Form} → (Preorder._≤_ o) Γ Δ → (Preorder._≤_ o) Γ (F ∷ Δ)
      ⊢tran : {Γ Δ : Con} → {F : Form} → (Preorder._≤_ o) Γ Δ → (NormalAndNeutral._⊢⁰_ nn) Γ F → (NormalAndNeutral._⊢⁰_ nn) Δ F

    open Preorder o
    open NormalAndNeutral nn

  
    UK : Kripke
    UK = record {
       Worlds = Con;
       _≤_ = _≤_;
       refl≤ = refl≤;
       tran≤ = tran≤;
       _⊩_[_] = λ Γ r A → Γ ⊢⁰ Rel r A;
       mon⊩ = λ Γ h → ⊢tran Γ h
       }

    open Kripke UK
    
    -- q is quote, u is unquote
    q : {F : Form} → {Γ : Con} → Γ ⊩ᶠ F → Γ ⊢* F
    u : {F : Form} → {Γ : Con} → Γ ⊢⁰ F → Γ ⊩ᶠ F
  
    u {Rel r A} h = h
    u {F ⇒ F₁} h {Γ'} iq hF = u {F₁} (app {Γ'} {F} {F₁} (⊢tran iq h) (q hF))
    u {F ∧∧ G} h = ⟨ (u {F} (ande₁ h)) , (u {G} (ande₂ h)) ⟩
    u {⊤⊤} h = tt
    u {∀∀ F} h {t} = u {F t} (∀e h {t})
    
    q {Rel r A} h = neu⁰ h
    q {F ⇒ F₁} {Γ} h = lam (q (h (retro (Preorder.refl≤ o)) (u {F} {F ∷ Γ} zero)))
    q {F ∧∧ G} ⟨ hF , hG ⟩ = andi (q {F} hF) (q {G} hG)
    q {⊤⊤} h = true
    q {∀∀ F} h = ∀i λ {t} → q {F t} h


  module NormalizationTests where

    {- Now using our records -}
    open import IFOL Term R hiding (Form; _⇒_; Con)


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
      lam = lam ;
      andi = andi ;
      true = true ;
      ∀i = ∀i ;
      ∀e = ∀e
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
      true = true ;
      ∀i = ∀i ;
      ∀e = ∀e
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

    
