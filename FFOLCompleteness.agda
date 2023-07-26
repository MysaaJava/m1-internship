{-# OPTIONS --prop --rewriting #-}

open import PropUtil

module FFOLCompleteness where

  open import Agda.Primitive
  open import FFOL
  open import ListUtil

  record Family : Set (lsuc (ℓ¹)) where
    field
      World : Set ℓ¹
      _≤_ : World → World → Prop
      ≤refl : {w : World} → w ≤ w
      ≤tran : {w w' w'' : World} → w ≤ w' → w' ≤ w'' → w ≤ w'
      TM : World → Set ℓ¹
      TM≤ : {w w' : World} → w ≤ w' → TM w → TM w'
      REL : (w : World) → TM w → TM w → Prop ℓ¹
      REL≤ : {w w' : World} → {t u : TM w} → (eq : w ≤ w') → REL w t u → REL w' (TM≤ eq t) (TM≤ eq u)
    infixr 10 _∘_
    Con = World → Set ℓ¹
    Sub : Con → Con → Set ℓ¹
    Sub Δ Γ = (w : World) → Δ w → Γ w
    _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
    α ∘ β = λ w γ → α w (β w γ)
    id : {Γ : Con} → Sub Γ Γ
    id = λ w γ → γ
    ◇ : Con -- The initial object of the category
    ◇ = λ w → ⊤ₛ
    ε : {Γ : Con} → Sub Γ ◇ -- The morphism from the initial to any object
    ε w Γ = ttₛ
                                                                    
    -- Functor Con → Set called Tm
    Tm : Con → Set ℓ¹
    Tm Γ = (w : World) → (Γ w) → TM w
    _[_]t : {Γ Δ : Con} → Tm Γ → Sub Δ Γ → Tm Δ -- The functor's action on morphisms
    t [ σ ]t = λ w → λ γ → t w (σ w γ)

    -- Tm⁺
    _▹ₜ : Con → Con
    Γ ▹ₜ = λ w → (Γ w) × (TM w)
    πₜ¹ : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Sub Δ Γ
    πₜ¹ σ = λ w → λ x → proj×₁ (σ w x)
    πₜ² : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Tm Δ
    πₜ² σ = λ w → λ x → proj×₂ (σ w x) 
    _,ₜ_ : {Γ Δ : Con} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹ₜ)
    σ ,ₜ t = λ w → λ x → (σ w x) ,× (t w x)
                                                                      
    -- Functor Con → Set called For
    For : Con → Set (lsuc ℓ¹)
    For Γ = (w : World) → (Γ w) → Prop ℓ¹
    _[_]f : {Γ Δ : Con} → For Γ → Sub Δ Γ → For Δ -- The functor's action on morphisms
    F [ σ ]f = λ w → λ x → F w (σ w x)

    -- Formulas with relation on terms
    R : {Γ : Con} → Tm Γ → Tm Γ → For Γ
    R t u = λ w → λ γ → REL w (t w γ) (u w γ)

                                                                                                        
    -- Proofs
    _⊢_ : (Γ : Con) → For Γ → Prop ℓ¹
    Γ ⊢ F = ∀ w (γ : Γ w) →  F w γ
    _[_]p : {Γ Δ : Con} → {F : For Γ} → Γ ⊢ F → (σ : Sub Δ Γ) → Δ ⊢ (F [ σ ]f) -- The functor's action on morphisms
    prf [ σ ]p = λ w → λ γ → prf w (σ w γ)
    -- Equalities below are useless because Γ ⊢ F is in prop
    -- []p-id : {Γ : Con} → {F : For Γ} → {prf : Γ ⊢ F} → prf [ id {Γ} ]p ≡ prf
    -- []p-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {F : For Γ} → {prf : Γ ⊢ F} → prf [ α ∘ β ]p ≡ (prf [ β ]p) [ α ]p
                                                                                                                               
    -- → Prop⁺
    _▹ₚ_ : (Γ : Con) → For Γ → Con
    Γ ▹ₚ F = λ w → (Γ w) ×'' (F w)
    πₚ¹ : {Γ Δ : Con} → {F : For Γ} → Sub Δ (Γ ▹ₚ F) → Sub Δ Γ
    πₚ¹ σ w δ = proj×''₁ (σ w δ)
    πₚ² : {Γ Δ : Con} → {F : For Γ} → (σ : Sub Δ (Γ ▹ₚ F)) → Δ ⊢ (F [ πₚ¹ σ ]f)
    πₚ² σ w δ = proj×''₂ (σ w δ)
    _,ₚ_ : {Γ Δ : Con} → {F : For Γ} → (σ : Sub Δ Γ) → Δ ⊢ (F [ σ ]f) → Sub Δ (Γ ▹ₚ F)
    _,ₚ_ {F = F} σ pf w δ = (σ w δ) ,×'' pf w δ
    
                                                                                                      
                                                                                                      
    -- Implication
    _⇒_ : {Γ : Con} → For Γ → For Γ → For Γ
    F ⇒ G = λ w → λ γ → (∀ w' → w ≤ w' → (F w γ) → (G w γ))
    
    -- Forall
    ∀∀ : {Γ : Con} → For (Γ ▹ₜ) → For Γ
    ∀∀ F = λ w → λ γ → ∀ t → F w (γ ,× t)
                                                                                                                           
    -- Lam & App
    lam : {Γ : Con} → {F : For Γ} → {G : For Γ} → (Γ ▹ₚ F) ⊢ (G [ πₚ¹ id ]f) → Γ ⊢ (F ⇒ G)
    lam prf = λ w γ w' s h → prf w (γ ,×'' h)
    app : {Γ : Con} → {F G : For Γ} → Γ ⊢ (F ⇒ G) → Γ ⊢ F → Γ ⊢ G
    app prf prf' = λ w γ → prf w γ w ≤refl (prf' w γ)
    -- Again, we don't write the _[_]p equalities as everything is in Prop
                                                                      
    -- ∀i and ∀e
    ∀i : {Γ : Con} → {F : For (Γ ▹ₜ)} → (Γ ▹ₜ) ⊢ F → Γ ⊢ (∀∀ F)
    ∀i p w γ = λ t → p w (γ ,× t)
    ∀e : {Γ : Con} → {F : For (Γ ▹ₜ)} → Γ ⊢ (∀∀ F) → {t : Tm Γ} → Γ ⊢ ( F [(id {Γ}) ,ₜ t ]f)
    ∀e p {t} w γ = p w γ (t w γ)


    tod : FFOL
    tod = record
      { Con = Con
      ; Sub = Sub
      ; _∘_ = _∘_
      ; ∘-ass = refl
      ; id = id
      ; idl = refl
      ; idr = refl
      ; ◇ = ◇
      ; ε = ε
      ; ε-u = refl
      ; Tm = Tm
      ; _[_]t = _[_]t
      ; []t-id = refl
      ; []t-∘ = refl
      ; _▹ₜ = _▹ₜ
      ; πₜ¹ = πₜ¹
      ; πₜ² = πₜ²
      ; _,ₜ_ = _,ₜ_
      ; πₜ²∘,ₜ = refl
      ; πₜ¹∘,ₜ = refl
      ; ,ₜ∘πₜ = refl
      ; ,ₜ∘ = refl
      ; For = For
      ; _[_]f = _[_]f
      ; []f-id = refl
      ; []f-∘ = refl
      ; _⊢_ = _⊢_
      ; _[_]p = _[_]p
      ; _▹ₚ_ = _▹ₚ_
      ; πₚ¹ = πₚ¹
      ; πₚ² = πₚ²
      ; _,ₚ_ = _,ₚ_
      ; ,ₚ∘πₚ = refl
      ; πₚ¹∘,ₚ = refl
      ; ,ₚ∘ = refl
      ; _⇒_ = _⇒_
      ; []f-⇒ = refl
      ; ∀∀ = ∀∀
      ; []f-∀∀ = refl
      ; lam = lam
      ; app = app
      ; ∀i = ∀i
      ; ∀e = ∀e
      ; R = R
      ; R[] = refl
      }

  record Presheaf : Set (lsuc (ℓ¹)) where
    field
      World : Set ℓ¹
      _-w->_ : World → World → Set ℓ¹ -- arrows
      -w->id : {w : World} → w -w-> w -- id arrow
      _∘-w->_ : {w w' w'' : World} → w -w-> w' → w' -w-> w'' → w -w-> w'' -- arrow composition
      -w->ass : {w w' w'' w''' : World}{a : w -w-> w'}{b : w' -w-> w''}{c : w'' -w-> w'''}
        → ((a ∘-w-> b) ∘-w-> c) ≡ (a ∘-w-> (b ∘-w-> c))
      -w->idl : {w w' : World} → {a : w -w-> w'} → (-w->id {w}) ∘-w-> a ≡ a
      -w->idr : {w w' : World} → {a : w -w-> w'} → a ∘-w-> (-w->id {w'}) ≡ a
      TM : World → Set ℓ¹
      TM≤ : {w w' : World} → w -w-> w' → TM w' → TM w
      REL : (w : World) → TM w → TM w → Prop ℓ¹
      REL≤ : {w w' : World} → {t u : TM w'} → (eq : w -w-> w') → REL w' t u → REL w (TM≤ eq t) (TM≤ eq u)
    infixr 10 _∘_
    Con = World → Set ℓ¹
    Sub : Con → Con → Set ℓ¹
    Sub Δ Γ = (w : World) → Δ w → Γ w
    _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
    α ∘ β = λ w γ → α w (β w γ)
    id : {Γ : Con} → Sub Γ Γ
    id = λ w γ → γ
    ◇ : Con -- The initial object of the category
    ◇ = λ w → ⊤ₛ
    ε : {Γ : Con} → Sub Γ ◇ -- The morphism from the initial to any object
    ε w Γ = ttₛ
                                                                    
    -- Functor Con → Set called Tm
    Tm : Con → Set ℓ¹
    Tm Γ = (w : World) → (Γ w) → TM w
    _[_]t : {Γ Δ : Con} → Tm Γ → Sub Δ Γ → Tm Δ -- The functor's action on morphisms
    t [ σ ]t = λ w → λ γ → t w (σ w γ)

    -- Tm⁺
    _▹ₜ : Con → Con
    Γ ▹ₜ = λ w → (Γ w) × (TM w)
    πₜ¹ : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Sub Δ Γ
    πₜ¹ σ = λ w → λ x → proj×₁ (σ w x)
    πₜ² : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Tm Δ
    πₜ² σ = λ w → λ x → proj×₂ (σ w x) 
    _,ₜ_ : {Γ Δ : Con} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹ₜ)
    σ ,ₜ t = λ w → λ x → (σ w x) ,× (t w x)
                                                                      
    -- Functor Con → Set called For
    For : Con → Set (lsuc ℓ¹)
    For Γ = (w : World) → (Γ w) → Prop ℓ¹
    _[_]f : {Γ Δ : Con} → For Γ → Sub Δ Γ → For Δ -- The functor's action on morphisms
    F [ σ ]f = λ w → λ x → F w (σ w x)

    -- Formulas with relation on terms
    R : {Γ : Con} → Tm Γ → Tm Γ → For Γ
    R t u = λ w → λ γ → REL w (t w γ) (u w γ)

                                                                                                        
    -- Proofs
    _⊢_ : (Γ : Con) → For Γ → Prop ℓ¹
    Γ ⊢ F = ∀ w (γ : Γ w) →  F w γ
    _[_]p : {Γ Δ : Con} → {F : For Γ} → Γ ⊢ F → (σ : Sub Δ Γ) → Δ ⊢ (F [ σ ]f) -- The functor's action on morphisms
    prf [ σ ]p = λ w → λ γ → prf w (σ w γ)
    -- Equalities below are useless because Γ ⊢ F is in prop
    -- []p-id : {Γ : Con} → {F : For Γ} → {prf : Γ ⊢ F} → prf [ id {Γ} ]p ≡ prf
    -- []p-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {F : For Γ} → {prf : Γ ⊢ F} → prf [ α ∘ β ]p ≡ (prf [ β ]p) [ α ]p
                                                                                                                               
    -- → Prop⁺
    _▹ₚ_ : (Γ : Con) → For Γ → Con
    Γ ▹ₚ F = λ w → (Γ w) ×'' (F w)
    πₚ¹ : {Γ Δ : Con} → {F : For Γ} → Sub Δ (Γ ▹ₚ F) → Sub Δ Γ
    πₚ¹ σ w δ = proj×''₁ (σ w δ)
    πₚ² : {Γ Δ : Con} → {F : For Γ} → (σ : Sub Δ (Γ ▹ₚ F)) → Δ ⊢ (F [ πₚ¹ σ ]f)
    πₚ² σ w δ = proj×''₂ (σ w δ)
    _,ₚ_ : {Γ Δ : Con} → {F : For Γ} → (σ : Sub Δ Γ) → Δ ⊢ (F [ σ ]f) → Sub Δ (Γ ▹ₚ F)
    _,ₚ_ {F = F} σ pf w δ = (σ w δ) ,×'' pf w δ
    
                                                                                                      
                                                                                                      
    -- Implication
    _⇒_ : {Γ : Con} → For Γ → For Γ → For Γ
    F ⇒ G = λ w → λ γ → (∀ w' → w -w-> w' → (F w γ) → (G w γ))
    
    -- Forall
    ∀∀ : {Γ : Con} → For (Γ ▹ₜ) → For Γ
    ∀∀ F = λ w → λ γ → ∀ t → F w (γ ,× t)
                                                                                                                           
    -- Lam & App
    lam : {Γ : Con} → {F : For Γ} → {G : For Γ} → (Γ ▹ₚ F) ⊢ (G [ πₚ¹ id ]f) → Γ ⊢ (F ⇒ G)
    lam prf = λ w γ w' s h → prf w (γ ,×'' h)
    app : {Γ : Con} → {F G : For Γ} → Γ ⊢ (F ⇒ G) → Γ ⊢ F → Γ ⊢ G
    app prf prf' = λ w γ → prf w γ w -w->id (prf' w γ)
    -- Again, we don't write the _[_]p equalities as everything is in Prop
    
    -- ∀i and ∀e
    ∀i : {Γ : Con} → {F : For (Γ ▹ₜ)} → (Γ ▹ₜ) ⊢ F → Γ ⊢ (∀∀ F)
    ∀i p w γ = λ t → p w (γ ,× t)
    ∀e : {Γ : Con} → {F : For (Γ ▹ₜ)} → Γ ⊢ (∀∀ F) → {t : Tm Γ} → Γ ⊢ ( F [(id {Γ}) ,ₜ t ]f)
    ∀e p {t} w γ = p w γ (t w γ)


    tod : FFOL
    tod = record
      { Con = Con
      ; Sub = Sub
      ; _∘_ = _∘_
      ; ∘-ass = refl
      ; id = id
      ; idl = refl
      ; idr = refl
      ; ◇ = ◇
      ; ε = ε
      ; ε-u = refl
      ; Tm = Tm
      ; _[_]t = _[_]t
      ; []t-id = refl
      ; []t-∘ = refl
      ; _▹ₜ = _▹ₜ
      ; πₜ¹ = πₜ¹
      ; πₜ² = πₜ²
      ; _,ₜ_ = _,ₜ_
      ; πₜ²∘,ₜ = refl
      ; πₜ¹∘,ₜ = refl
      ; ,ₜ∘πₜ = refl
      ; ,ₜ∘ = refl
      ; For = For
      ; _[_]f = _[_]f
      ; []f-id = refl
      ; []f-∘ = refl
      ; _⊢_ = _⊢_
      ; _[_]p = _[_]p
      ; _▹ₚ_ = _▹ₚ_
      ; πₚ¹ = πₚ¹
      ; πₚ² = πₚ²
      ; _,ₚ_ = _,ₚ_
      ; ,ₚ∘πₚ = refl
      ; πₚ¹∘,ₚ = refl
      ; ,ₚ∘ = refl
      ; _⇒_ = _⇒_
      ; []f-⇒ = refl
      ; ∀∀ = ∀∀
      ; []f-∀∀ = refl
      ; lam = lam
      ; app = app
      ; ∀i = ∀i
      ; ∀e = ∀e
      ; R = R
      ; R[] = refl
      }

  module U where

    import FFOLInitial as I

    psh : Presheaf
    psh = record
            { World = I.Con
            ; _-w->_ = I.Sub
            ; -w->id = I.id
            ; _∘-w->_ = λ σ σ' → σ' I.∘ σ
            ; -w->ass = ≡sym I.∘-ass
            ; -w->idl = I.idr
            ; -w->idr = I.idl
            ; TM = λ Γ → I.Tm (I.Con.t Γ)
            ; TM≤ =  λ σ t → t I.[ I.Sub.t σ ]t
            ; REL = λ Γ t u → I.Pf (I.Con.t Γ) (I.Con.p Γ) (I.R t u)
            ; REL≤ = λ s pf → (pf I.[ I.Sub.t s ]pₜ) I.[ I.Sub.p s ]p
            }

    open Presheaf psh public


  -- Completeness proof

  -- We first build our universal Kripke model
  
  module ComplenessProof where
    
    -- We have a model, we construct the Universal Presheaf model of this model
    import FFOLInitial as I

    
