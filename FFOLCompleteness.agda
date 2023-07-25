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
      Arr : World → World → Set ℓ¹ -- arrows
      id-a : {w : World} → Arr w w -- id arrow
      _∘a_ : {w w' w'' : World} → Arr w w' → Arr w' w'' → Arr w w'' -- arrow composition
      ∘a-ass : {w w' w'' w''' : World}{a : Arr w w'}{b : Arr w' w''}{c : Arr w'' w'''}
        → ((a ∘a b) ∘a c) ≡ (a ∘a (b ∘a c))
      idl-a : {w w' : World} → {a : Arr w w'} → (id-a {w}) ∘a a ≡ a
      idr-a : {w w' : World} → {a : Arr w w'} → a ∘a (id-a {w'}) ≡ a
      TM : World → Set ℓ¹
      TM≤ : {w w' : World} → Arr w w' → TM w' → TM w
      REL : (w : World) → TM w → TM w → Prop ℓ¹
      REL≤ : {w w' : World} → {t u : TM w'} → (eq : Arr w w') → REL w' t u → REL w (TM≤ eq t) (TM≤ eq u)
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
    F ⇒ G = λ w → λ γ → (∀ w' → Arr w w' → (F w γ) → (G w γ))
    
    -- Forall
    ∀∀ : {Γ : Con} → For (Γ ▹ₜ) → For Γ
    ∀∀ F = λ w → λ γ → ∀ t → F w (γ ,× t)
                                                                                                                           
    -- Lam & App
    lam : {Γ : Con} → {F : For Γ} → {G : For Γ} → (Γ ▹ₚ F) ⊢ (G [ πₚ¹ id ]f) → Γ ⊢ (F ⇒ G)
    lam prf = λ w γ w' s h → prf w (γ ,×'' h)
    app : {Γ : Con} → {F G : For Γ} → Γ ⊢ (F ⇒ G) → Γ ⊢ F → Γ ⊢ G
    app prf prf' = λ w γ → prf w γ w id-a (prf' w γ)
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

  record Presheaf' : Set (lsuc (ℓ¹)) where
    field
      World : Set ℓ¹
      Arr : World → World → Set ℓ¹ -- arrows
      id-a : {w : World} → Arr w w -- id arrow
      _∘a_ : {w w' w'' : World} → Arr w w' → Arr w' w'' → Arr w w'' -- arrow composition
      ∘a-ass : {w w' w'' w''' : World}{a : Arr w w'}{b : Arr w' w''}{c : Arr w'' w'''}
        → ((a ∘a b) ∘a c) ≡ (a ∘a (b ∘a c))
      idl-a : {w w' : World} → {a : Arr w w'} → (id-a {w}) ∘a a ≡ a
      idr-a : {w w' : World} → {a : Arr w w'} → a ∘a (id-a {w'}) ≡ a
      TM : World → Set ℓ¹
      TM≤ : {w w' : World} → Arr w w' → TM w' → TM w
      REL : (w : World) → TM w → TM w → Set ℓ¹
      REL≤ : {w w' : World} → {t u : TM w'} → (eq : Arr w w') → REL w' t u → REL w (TM≤ eq t) (TM≤ eq u)

    {-
    -- Now we try to interpret formulæ and contexts
    import FFOLInitial as I
    _⊩ᶠ_  : World → (I.For I.◇t) → Set ℓ¹
    w ⊩ᶠ I.R t u = REL w {!!} {!!}
    w ⊩ᶠ (A I.⇒ B) = ∀ (w' : World) → Arr w w' → w' ⊩ᶠ A → w' ⊩ᶠ B
    w ⊩ᶠ I.∀∀ A = ∀ (t : TM w) → {!!}
    -}



  record Kripke : Set (lsuc (ℓ¹)) where
    field
      World : Set ℓ¹
      Arr : World → World → Prop ℓ¹ -- arrows
      id-a : {w : World} → Arr w w -- id arrow
      _∘a_ : {w w' w'' : World} → Arr w w' → Arr w' w'' → Arr w w'' -- arrow composition
      -- associativity and id rules are trivial cause arrows are in prop
      TM : World → Set ℓ¹
      TM≤ : {w w' : World} → Arr w w' → TM w' → TM w
      REL : (w : World) → TM w → TM w → Prop ℓ¹
      REL≤ : {w w' : World} → {t u : TM w'} → (eq : Arr w w') → REL w' t u → REL w (TM≤ eq t) (TM≤ eq u)


  -- Completeness proof

  -- We first build our universal Kripke model
  
  module ComplenessProof where
    
    -- We have a model, we construct the Universal Presheaf model of this model
    import FFOLInitial as I

    UniversalPresheaf : Kripke
    UniversalPresheaf = record
       { World = (Γₜ : I.Cont) → I.Conp Γₜ
       ; Arr = λ w₁ w₂ → (Γₜ : I.Cont) → (I.Pf* Γₜ (w₂ Γₜ) (w₁ Γₜ))
       ; id-a = λ {w} Γₜ → I.Pf*-id
       ; _∘a_ = λ σ₁ σ₂ Γₜ → I.Pf*-∘ (σ₁ Γₜ) (σ₂ Γₜ)
       --; ∘a-ass = λ {w} → ≡fun' (λ Γₜ → ≡sym (I.∘ₚ-ass {Γₚ = w Γₜ}))
       --; idl-a = λ {w} {w'} → ≡fun' (λ Γₜ → I.idrₚ {Γₚ = w Γₜ} {Δₚ = w' Γₜ})
       --; idr-a = λ {w} {w'} → ≡fun' (λ Γₜ → I.idlₚ {Γₚ = w Γₜ} {Δₚ = w' Γₜ})
       ; TM = λ w → (Γₜ : I.Cont) → (I.Tm Γₜ)
       ; TM≤ = λ σ t → t
       ; REL = λ w t u → (Γₜ : I.Cont) → I.Pf Γₜ (w Γₜ) (I.R (t Γₜ) (u Γₜ))
       ; REL≤ = λ σ pf → λ Γₜ → I.Pf*Pf {!!} (pf Γₜ)
       }

    -- I.xx are from initial, xx are from up
    open Kripke UniversalPresheaf

    -- We now create the forcing relation for our Universal presheaf
    -- We need the world to depend of a term context (i guess), so i think i cannot make it so
    -- the forcing relation works for every Kripke Model.
    _⊩f_ : (w : World) → {Γₜ : I.Cont} → I.For Γₜ → Prop₁
    _⊩f_ w {Γₜ} (I.R t v) = I.Pf Γₜ (w Γₜ) (I.R t v)
    w ⊩f (A I.⇒ B) = ∀ w' → Arr w w' → w' ⊩f A → w' ⊩f B
    w ⊩f I.∀∀ A = w ⊩f A

    ⊩f-mon : {w w' : World} → Arr w w' → {Γₜ : I.Cont} → {A : I.For Γₜ} → w ⊩f A → w' ⊩f A
    ⊩f-mon s {Γₜ} {I.R t v} wh = I.Pf*Pf (s Γₜ) wh
    ⊩f-mon s {A = A I.⇒ B} wh w'' s' w''h = wh w'' (s ∘a s' ) w''h
    ⊩f-mon s {A = I.∀∀ A} wh = ⊩f-mon s {A = A} wh

    ⊩fPf : {Γₜ : I.Cont}{w : World}{A : I.For Γₜ} → w ⊩f A → I.Pf Γₜ (w Γₜ) A
    ⊩fPf {A = I.R t v} pf = pf
    ⊩fPf {A = A I.⇒ A₁} pf = {!I.app!}
    ⊩fPf {A = I.∀∀ A} pf = I.p∀∀i (substP (λ X → I.Pf _ X A) {!!} (⊩fPf pf))


    _⊩c_ : (w : World) → {Γₜ : I.Cont} → I.Conp Γₜ → Prop₁
    w ⊩c I.◇p = ⊤
    w ⊩c (Γₚ I.▹p⁰ A) = (w ⊩c Γₚ) ∧ (w ⊩f A)

    ⊩c-mon : {w w' : World} → Arr w w' → {Γₜ : I.Cont} → {Γₚ : I.Conp Γₜ} → w ⊩c Γₚ → w' ⊩c Γₚ
    ⊩c-mon s {Γₚ = I.◇p} wh = tt
    ⊩c-mon s {Γₜ} {Γₚ = Γₚ I.▹p⁰ A} wh = ⟨ (⊩c-mon s (proj₁ wh)) , ⊩f-mon s {Γₜ} {A} (proj₂ wh) ⟩

    ⊩cPf* : {Γₜ : I.Cont}{w : World}{Γₚ : I.Conp Γₜ} → w ⊩c Γₚ → I.Pf* Γₜ (w Γₜ) Γₚ
    ⊩cPf* {Γₚ = I.◇p} h = tt
    ⊩cPf* {Γₚ = Γₚ I.▹p⁰ x} h = ⟨ (⊩cPf* (proj₁ h)) , {!proj₂ h!} ⟩

    _⊫_ : {Γₜ : I.Cont} → (I.Conp Γₜ) → I.For Γₜ → Prop₁
    Γₚ ⊫ A = ∀ w → w ⊩c Γₚ → w ⊩f A
    
    -- Now we want to show universality of this model, that is
    -- if you have a proof in UP, you have the same in I.
    
    u : {Γₜ : I.Cont}{Γₚ : I.Conp Γₜ}{A : I.For Γₜ} → I.Pf Γₜ Γₚ A → Γₚ ⊫ A
    q : {Γₜ : I.Cont}{Γₚ : I.Conp Γₜ}{A : I.For Γₜ} → Γₚ ⊫ A → I.Pf Γₜ Γₚ A

    u {A = I.R t s} pf w wh = {!!}
    u {A = A I.⇒ B} pf w wh w' s w'h  = u {A = B} (I.app pf (q λ w'' w''h → {!!})) w' (⊩c-mon s wh)
    u {A = I.∀∀ A} pf w wh = {!!}
    q {A = I.R t s} h = {!!}
    q {A = A I.⇒ B} h = {!!}
    q {A = I.∀∀ A} h = {!!}
