\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}

open import PropUtil
 
module ZOL2 where

  open import Agda.Primitive
  open import ListUtil

  variable
    ℓ¹ ℓ² ℓ³ ℓ⁴ : Level
    ℓ¹' ℓ²' ℓ³' ℓ⁴' : Level
    
  record ZOL : Set (lsuc (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓ⁴)) where
    infixr 10 _∘_
    field
    
      --# We first make the base category with its terminal object
      Con : Set ℓ¹
      Sub : Con → Con → Prop ℓ² -- It makes a posetal category
      _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
      id : {Γ : Con} → Sub Γ Γ
      ◇ : Con -- The terminal object of the category
      ε : {Γ : Con} → Sub Γ ◇ -- The morphism from any object to the terminal

      --# Categorical equations don't need to be stated as the category is *posetal*
      --∘-ass : {Γ Δ Ξ Ψ : Con}{α : Sub Γ Δ}{β : Sub Δ Ξ}{γ : Sub Ξ Ψ}
      --idl : {Γ Δ : Con} {σ : Sub Γ Δ} →  (id {Δ}) ∘ σ ≡ σ
      --idr : {Γ Δ : Con} {σ : Sub Γ Δ} →  σ ∘ (id {Γ}) ≡ σ
      --  → (γ ∘ β) ∘ α ≡ γ ∘ (β ∘ α)
      --ε-u : {Γ : Con} → {σ : Sub Γ ◇} → σ ≡ ε {Γ}

      --# Functor Con → Set called For
      For : Con → Set ℓ³
      _[_]f : {Γ Δ : Con} → For Γ → Sub Δ Γ → For Δ -- Action on morphisms
      []f-id : {Γ : Con} → {F : For Γ} → F [ id {Γ} ]f ≡ F
      []f-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {F : For Γ}
        → F [ β ∘ α ]f ≡ (F [ β ]f) [ α ]f

      --# Functor Con × For → Prop called Pf or ⊢
      Pf : (Γ : Con) → For Γ → Prop ℓ⁴
      -- Action on morphisms
      _[_]p : {Γ Δ : Con} → {F : For Γ} → Pf Γ F → (σ : Sub Δ Γ) → Pf Δ (F [ σ ]f)
      -- Equalities below are useless because Pf Γ F is in prop
      -- []p-id : {Γ : Con} → {F : For Γ} → {prf : Pf Γ F}
      --  → prf [ id {Γ} ]p ≡ prf
      -- []p-∘ : {Γ Δ Ξ : Con}{α : Sub Ξ Δ}{β : Sub Δ Γ}{F : For Γ}{prf : Pf Γ F}
      --  → prf [ α ∘ β ]p ≡ (prf [ β ]p) [ α ]p

      --# → Prop⁺
      _▹ₚ_ : (Γ : Con) → For Γ → Con
      πₚ¹ : {Γ Δ : Con}{F : For Γ} → Sub Δ (Γ ▹ₚ F) → Sub Δ Γ
      πₚ² : {Γ Δ : Con}{F : For Γ} → (σ : Sub Δ (Γ ▹ₚ F)) → Pf Δ (F [ πₚ¹ σ ]f)
      _,ₚ_ : {Γ Δ : Con}{F : For Γ} → (σ : Sub Δ Γ) → Pf Δ (F [ σ ]f) → Sub Δ (Γ ▹ₚ F)
      --# Equality below are useless because Pf and Sub are in Prop 
      --,ₚ∘πₚ : {Γ Δ : Con}{F : For Γ}{σ : Sub Δ (Γ ▹ₚ F)} → (πₚ¹ σ) ,ₚ (πₚ² σ) ≡ σ
      --πₚ¹∘,ₚ : {Γ Δ : Con}{σ : Sub Δ Γ}{F : For Γ}{prf : Pf Δ (F [ σ ]f)}
      --  → πₚ¹ (σ ,ₚ prf) ≡ σ
      -- πₚ²∘,ₚ : {Γ Δ : Con}{σ : Sub Δ Γ}{F : For Γ}{prf : Pf Δ (F [ σ ]f)}
      -- → πₚ² (σ ,ₚ prf) ≡ prf
      --,ₚ∘ : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{F : For Ξ}{prf : Pf Γ (F [ σ ]f)}
      --  → (σ ,ₚ prf) ∘ δ ≡ (σ ∘ δ) ,ₚ (substP (Pf Δ) (≡sym []f-∘) (prf [ δ ]p))

      --#
      {-- FORMULAE CONSTRUCTORS --}

      --# i formula
      ι : {Γ : Con} → For Γ
      []f-ι : {Γ Δ : Con} {σ : Sub Δ Γ}→ ι [ σ ]f ≡ ι
 
      --# Implication
      _⇒_ : {Γ : Con} → For Γ → For Γ → For Γ
      []f-⇒ : {Γ Δ : Con} → {F G : For Γ} → {σ : Sub Δ Γ}
        → (F ⇒ G) [ σ ]f ≡ (F [ σ ]f) ⇒ (G [ σ ]f)

      --#
      {-- PROOFS CONSTRUCTORS --}
      -- Again, we don't have to write the _[_]p equalities as Proofs are in Prop

      --# Lam & App
      lam : {Γ : Con}{F G : For Γ} → Pf (Γ ▹ₚ F) (G [ πₚ¹ id ]f) → Pf Γ (F ⇒ G)
      app : {Γ : Con}{F G : For Γ} → Pf Γ (F ⇒ G) → Pf Γ F → Pf Γ G

      --#

  record Mapping (S : ZOL {ℓ¹} {ℓ²} {ℓ³} {ℓ⁴}) (D : ZOL {ℓ¹'} {ℓ²'} {ℓ³'} {ℓ⁴'}) : Set (lsuc (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓ⁴ ⊔ ℓ¹' ⊔ ℓ²' ⊔ ℓ³' ⊔ ℓ⁴')) where
    field

      --#
      mCon : (ZOL.Con S) → (ZOL.Con D)
      mSub : {Δ : (ZOL.Con S)}{Γ : (ZOL.Con S)} →
        (ZOL.Sub S Δ Γ) → (ZOL.Sub D (mCon Δ) (mCon Γ))
      mFor : {Γ : (ZOL.Con S)} → (ZOL.For S Γ) → (ZOL.For D (mCon Γ))
      mPf : {Γ : (ZOL.Con S)} {A : ZOL.For S Γ}
        → ZOL.Pf S Γ A → ZOL.Pf D (mCon Γ) (mFor A)
      --#

  record Morphism (S : ZOL {ℓ¹} {ℓ²} {ℓ³} {ℓ⁴}) (D : ZOL {ℓ¹'} {ℓ²'} {ℓ³'} {ℓ⁴'}) : Set (lsuc (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓ⁴ ⊔ ℓ¹' ⊔ ℓ²' ⊔ ℓ³' ⊔ ℓ⁴')) where
    field m : Mapping S D
    mCon = Mapping.mCon m
    mSub = Mapping.mSub m
    mFor = Mapping.mFor m
    mPf  = Mapping.mPf m
    field
      --#
      e◇ : mCon (ZOL.◇ S) ≡ ZOL.◇ D
      e[]f : {Γ Δ : ZOL.Con S}{A : ZOL.For S Γ}{σ : ZOL.Sub S Δ Γ} →
        mFor (ZOL._[_]f S A σ) ≡ ZOL._[_]f D (mFor A) (mSub σ)
      e▹ₚ : {Γ : ZOL.Con S}{A : ZOL.For S Γ} →
        mCon (ZOL._▹ₚ_ S Γ A) ≡ ZOL._▹ₚ_ D (mCon Γ) (mFor A)
      eι : {Γ : ZOL.Con S} → mFor (ZOL.ι S {Γ}) ≡ ZOL.ι D {mCon Γ}
      e⇒ : {Γ : ZOL.Con S}{A B : ZOL.For S Γ} →
        mFor (ZOL._⇒_ S A B) ≡ ZOL._⇒_ D (mFor A) (mFor B)
      -- No equation needed for lam, app, ∀i, ∀e as their output are in prop
      --#
      
  record TrNat {S : ZOL {ℓ¹} {ℓ²} {ℓ³} {ℓ⁴}} {D : ZOL {ℓ¹'} {ℓ²'} {ℓ³'} {ℓ⁴'}} (a : Mapping S D) (b : Mapping S D) : Set (lsuc (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓ⁴ ⊔ ℓ¹' ⊔ ℓ²' ⊔ ℓ³' ⊔ ℓ⁴')) where
    field
      f : (Γ : ZOL.Con S) → ZOL.Sub D (Mapping.mCon a Γ) (Mapping.mCon b Γ)
      -- Unneeded because Sub are in prop
      --eq : (Γ Δ : ZOL.Con S)(σ : ZOL.Sub S Γ Δ) → (ZOL._∘_ D (f Δ) (Mapping.mSub a σ)) ≡ (ZOL._∘_ D (Mapping.mSub b σ) (f Γ))

  _∘TrNat_ : {S : ZOL {ℓ¹} {ℓ²} {ℓ³} {ℓ⁴}}{D : ZOL {ℓ¹'} {ℓ²'} {ℓ³'} {ℓ⁴'}}{a b c : Mapping S D} → TrNat a b → TrNat b c → TrNat a c
  _∘TrNat_ {D = D} α β = record { f = λ Γ → ZOL._∘_ D (TrNat.f β Γ) (TrNat.f α Γ) }

  idTrNat : {S : ZOL {ℓ¹} {ℓ²} {ℓ³} {ℓ⁴}}{D : ZOL {ℓ¹'} {ℓ²'} {ℓ³'} {ℓ⁴'}}{a : Mapping S D} → TrNat a a
  idTrNat {D = D} = record { f = λ Γ → ZOL.id D }
  
\end{code}
