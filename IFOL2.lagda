\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import PropUtil
 
module IFOL2 where

  open import Agda.Primitive
  open import ListUtil

  variable
    ℓ¹ ℓ² ℓ³ ℓ⁴ ℓ⁵ : Level
    
  record IFOL (TM : Set) : Set (lsuc (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓ⁴)) where
    infixr 10 _∘_
    field
      
      -- We first make the base category with its terminal object
      Con : Set ℓ¹
      Sub : Con → Con → Prop ℓ² -- It makes a category
      _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
      id : {Γ : Con} → Sub Γ Γ
      ◇ : Con -- The terminal object of the category
      ε : {Γ : Con} → Sub Γ ◇ -- The morphism from any object to the terminal
      
      -- Functor Con → Set called For
      For : Con → Set ℓ³
      _[_]f : {Γ Δ : Con} → For Γ → Sub Δ Γ → For Δ -- Action on morphisms
      []f-id : {Γ : Con} → {F : For Γ} → F [ id {Γ} ]f ≡ F
      []f-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {F : For Γ}
        → F [ β ∘ α ]f ≡ (F [ β ]f) [ α ]f

      -- Functor Con × For → Prop called Pf or ⊢
      Pf : (Γ : Con) → For Γ → Prop ℓ⁴
      -- Action on morphisms
      _[_]p : {Γ Δ : Con} → {F : For Γ} → Pf Γ F → (σ : Sub Δ Γ) → Pf Δ (F [ σ ]f)
      -- Equalities below are useless because Γ ⊢ F is in prop
      -- []p-id : {Γ : Con} → {F : For Γ} → {prf : Γ ⊢ F}
      --  → prf [ id {Γ} ]p ≡ prf
      -- []p-∘ : {Γ Δ Ξ : Con}{α : Sub Ξ Δ}{β : Sub Δ Γ}{F : For Γ}{prf : Γ ⊢ F}
      --  → prf [ α ∘ β ]p ≡ (prf [ β ]p) [ α ]p

      -- → Prop⁺
      _▹ₚ_ : (Γ : Con) → For Γ → Con
      πₚ¹ : {Γ Δ : Con}{F : For Γ} → Sub Δ (Γ ▹ₚ F) → Sub Δ Γ
      πₚ² : {Γ Δ : Con}{F : For Γ} → (σ : Sub Δ (Γ ▹ₚ F)) → Pf Δ (F [ πₚ¹ σ ]f)
      _,ₚ_ : {Γ Δ : Con}{F : For Γ} → (σ : Sub Δ Γ) → Pf Δ (F [ σ ]f) → Sub Δ (Γ ▹ₚ F)
      -- Equality below is useless because Pf Γ F is in Prop
      -- πₚ²∘,ₚ : {Γ Δ : Con}{σ : Sub Δ Γ}{F : For Γ}{prf : Pf Δ (F [ σ ]f)}
      -- → πₚ² (σ ,ₚ prf) ≡ prf

      
      {-- FORMULAE CONSTRUCTORS --}
      -- Formulas with relation on terms
      R : {Γ : Con} → (t u : TM) → For Γ
      R[] : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t u : TM}
        → (R t u) [ σ ]f ≡ R t u

      -- Implication
      _⇒_ : {Γ : Con} → For Γ → For Γ → For Γ
      []f-⇒ : {Γ Δ : Con} → {F G : For Γ} → {σ : Sub Δ Γ}
        → (F ⇒ G) [ σ ]f ≡ (F [ σ ]f) ⇒ (G [ σ ]f)

      -- Forall
      ∀∀ : {Γ : Con} → (TM → For Γ) → For Γ
      []f-∀∀ : {Γ Δ : Con} → {F : TM → For Γ} → {σ : Sub Δ Γ}
        → (∀∀ F) [ σ ]f ≡ (∀∀ (λ t → (F t) [ σ ]f))

      {-- PROOFS CONSTRUCTORS --}
      -- Again, we don't have to write the _[_]p equalities as Proofs are in Prop
      
      -- Lam & App
      lam : {Γ : Con}{F G : For Γ} → Pf (Γ ▹ₚ F) (G [ πₚ¹ id ]f) → Pf Γ (F ⇒ G)
      app : {Γ : Con}{F G : For Γ} → Pf Γ (F ⇒ G) → Pf Γ F → Pf Γ G

      -- ∀i and ∀e
      ∀i : {Γ : Con}{A : TM → For Γ} → ((t : TM) → Pf Γ (A t)) → Pf Γ (∀∀ A)
      ∀e : {Γ : Con}{A : TM → For Γ} → Pf Γ (∀∀ A) → (t : TM) → Pf Γ (A t)

  record Mapping (TM : Set) (S : IFOL {ℓ¹} {ℓ²} {ℓ³} {ℓ⁴} TM) (D : IFOL {ℓ¹} {ℓ²} {ℓ³} {ℓ⁴} TM) : Set (lsuc (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓ⁴)) where
    field
      
      -- We first make the base category with its final object
      mCon : (IFOL.Con S) → (IFOL.Con D)
      mSub : {Δ : (IFOL.Con S)}{Γ : (IFOL.Con S)} → (IFOL.Sub S Δ Γ) → (IFOL.Sub D (mCon Δ) (mCon Γ))
      mFor : {Γ : (IFOL.Con S)} → (IFOL.For S Γ) → (IFOL.For D (mCon Γ))
      mPf : {Γ : (IFOL.Con S)} {A : IFOL.For S Γ} → IFOL.Pf S Γ A → IFOL.Pf D (mCon Γ) (mFor A)


  record Morphism (TM : Set)(S : IFOL {ℓ¹} {ℓ²} {ℓ³} {ℓ⁴} TM) (D : IFOL {ℓ¹} {ℓ²} {ℓ³} {ℓ⁴} TM) : Set (lsuc (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓ⁴)) where
    field m : Mapping TM S D
    mCon = Mapping.mCon m
    mSub = Mapping.mSub m
    mFor = Mapping.mFor m
    mPf   = Mapping.mPf m
    field
      e◇ : mCon (IFOL.◇ S) ≡ IFOL.◇ D
      e[]f : {Γ Δ : IFOL.Con S}{A : IFOL.For S Γ}{σ : IFOL.Sub S Δ Γ} → mFor (IFOL._[_]f S A σ) ≡ IFOL._[_]f D (mFor A) (mSub σ)
      -- Proofs are in prop, so some equations are not needed
      --[]p : {Γ Δ : IFOL.Con S}{A : IFOL.For S Γ}{pf : IFOL._⊢_ S Γ A}{σ : IFOL.Sub S Δ Γ} → mPf (IFOL._[_]p S pf σ) ≡ IFOL._[_]p D (mPf pf) (mSub σ)
      e▹ₚ : {Γ : IFOL.Con S}{A : IFOL.For S Γ} → mCon (IFOL._▹ₚ_ S Γ A) ≡ IFOL._▹ₚ_ D (mCon Γ) (mFor A)
      --πₚ² : {Γ Δ : IFOL.Con S}{A : IFOL.For S Γ}{σ : IFOL.Sub S Δ (IFOL._▹ₚ_ S Γ A)} → mPf (IFOL.πₚ² S σ) ≡ IFOL.πₚ¹ D (subst (IFOL.Sub D (mCon Δ)) ▹ₚ (mSub σ))
      eR : {Γ : IFOL.Con S}{t u : TM} → mFor {Γ} (IFOL.R S t u) ≡ IFOL.R D t u
      e⇒ : {Γ : IFOL.Con S}{A B : IFOL.For S Γ} → mFor (IFOL._⇒_ S A B) ≡ IFOL._⇒_ D (mFor A) (mFor B)
      e∀∀ : {Γ : IFOL.Con S}{A : TM → IFOL.For S Γ} → mFor (IFOL.∀∀ S A) ≡ IFOL.∀∀ D (λ t → (mFor (A t)))
      -- No equation needed for lam, app, ∀i, ∀e as their output are in prop
\end{code}
