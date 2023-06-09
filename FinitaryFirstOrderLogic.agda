{-# OPTIONS --prop #-}

open import PropUtil

module FinitaryFirstOrderLogic (Term : Set) (R : Nat → Set) where

  open import Agda.Primitive
  open import ListUtil

  variable
    ℓ¹ ℓ² ℓ³ : Level
    
  record FFOL : Set (lsuc (ℓ¹ ⊔ ℓ² ⊔ ℓ³)) where
    infixr 10 _∘_
    field
      Con : Set ℓ¹
      Sub : Con → Con → Set -- It makes a posetal category
      _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
      id : {Γ : Con} → Sub Γ Γ
      ◇ : Con -- The initial object of the category
      ε : {Γ : Con} → Sub ◇ Γ -- The morphism from the initial to any object

      -- Functor Con → Set called Tm
      Tm : Con → Set ℓ²
      _[_]t : {Γ Δ : Con} → Tm Γ → Sub Δ Γ → Tm Δ -- The functor's action on morphisms
      []t-id : {Γ : Con} → {x : Tm Γ} → x [ id {Γ} ]t ≡ x
      []t-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {t : Tm Γ} → t [ β ∘ α ]t ≡ (t [ β ]t) [ α ]t

      -- Tm⁺
      _▹ₜ : Con → Con
      πₜ¹ : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Sub Δ Γ
      πₜ² : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Tm Δ
      _,ₜ_ : {Γ Δ : Con} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹ₜ)
      πₜ²∘,ₜ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm Δ} → πₜ² (σ ,ₜ t) ≡ t
      πₜ¹∘,ₜ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm Δ} → πₜ¹ (σ ,ₜ t) ≡ σ
      ,ₜ∘πₜ : {Γ Δ : Con} → {σ : Sub Δ (Γ ▹ₜ)} → (πₜ¹ σ) ,ₜ (πₜ² σ) ≡ σ

      -- Functor Con → Set called For
      For : Con → Set ℓ³
      _[_]f : {Γ Δ : Con} → For Γ → Sub Δ Γ → For Δ -- The functor's action on morphisms
      []f-id : {Γ : Con} → {F : For Γ} → F [ id {Γ} ]f ≡ F
      []f-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {F : For Γ} → F [ β ∘ α ]f ≡ (F [ β ]f) [ α ]f

      -- Proofs
      _⊢_ : (Γ : Con) → For Γ → Prop
      --_[_]p : {Γ Δ : Con} → {F : For Γ} → Γ ⊢ F → (σ : Sub Δ Γ) → Δ ⊢ (F [ σ ]f) -- The functor's action on morphisms
      -- Equalities below are useless because Γ ⊢ F is in prop
      -- []p-id : {Γ : Con} → {F : For Γ} → {prf : Γ ⊢ F} → prf [ id {Γ} ]p ≡ prf
      -- []p-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {F : For Γ} → {prf : Γ ⊢ F} → prf [ α ∘ β ]p ≡ (prf [ β ]p) [ α ]p

      -- → Prop⁺
      _▹ₚ_ : (Γ : Con) → For Γ → Con
      πₚ¹ : {Γ Δ : Con} → {F : For Γ} → Sub Δ (Γ ▹ₚ F) → Sub Δ Γ
      πₚ² : {Γ Δ : Con} → {F : For Γ} → (σ : Sub Δ (Γ ▹ₚ F)) → Δ ⊢ (F [ πₚ¹ σ ]f)
      _,ₚ_ : {Γ Δ : Con} → {F : For Γ} → (σ : Sub Δ Γ) → Δ ⊢ (F [ σ ]f) → Sub Δ (Γ ▹ₚ F)
      -- Equalities below are useless because Γ ⊢ F is in Prop
      ,ₚ∘πₚ : {Γ Δ : Con} → {F : For Γ} → {σ : Sub Δ (Γ ▹ₚ F)} → (πₚ¹ σ) ,ₚ (πₚ² σ) ≡ σ
      πₚ¹∘,ₚ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {F : For Γ} → {prf : Δ ⊢ (F [ σ ]f)} → πₚ¹ (σ ,ₚ prf) ≡ σ
      -- πₚ²∘,ₚ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {F : For Γ} → {prf : Δ ⊢ (F [ σ ]f)} → πₚ² (σ ,ₚ prf) ≡ prf


      -- Implication
      _⇒_ : {Γ : Con} → For Γ → For Γ → For Γ
      []f-⇒ : {Γ Δ : Con} → {F G : For Γ} → {σ : Sub Δ Γ} → (F ⇒ G) [ σ ]f ≡ (F [ σ ]f) ⇒ (G [ σ ]f)

      -- Forall
      ∀∀ : {Γ : Con} → For (Γ ▹ₜ) → For Γ
      []f-∀∀ : {Γ Δ : Con} → {F : For (Γ ▹ₜ)} → {σ : Sub Δ Γ} → {t : Tm Γ} → (∀∀ F) [ σ ]f ≡ (∀∀ (F [ (σ ∘ πₜ¹ id) ,ₜ πₜ² id ]f))

      -- Lam & App
      lam : {Γ : Con} → {F : For Γ} → {G : For Γ} → (Γ ▹ₚ F) ⊢ (G [ πₚ¹ id ]f) → Γ ⊢ (F ⇒ G)
      app : {Γ : Con} → {F G : For Γ} → Γ ⊢ (F ⇒ G) → Γ ⊢ F → Γ ⊢ G
      -- Again, we don't write the _[_]p equalities as everything is in Prop

      -- ∀i and ∀e
      ∀i : {Γ : Con} → {F : For (Γ ▹ₜ)} → (Γ ▹ₜ) ⊢ F → Γ ⊢ (∀∀ F)
      ∀e : {Γ : Con} → {F : For (Γ ▹ₜ)} → Γ ⊢ (∀∀ F) → {t : Tm Γ} → Γ ⊢ ( F [(id {Γ}) ,ₜ t ]f)

  module Tarski (TM : Set) where
    infixr 10 _∘_
    Con = Set
    Sub : Con → Con → Set
    Sub Γ Δ = (Γ → Δ) -- It makes a posetal category
    _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
    f ∘ g = λ x → f (g x)
    id : {Γ : Con} → Sub Γ Γ
    id = λ x → x
    data ◇ : Con where
    ε : {Γ : Con} → Sub ◇ Γ -- The morphism from the initial to any object
    ε ()
                                                                    
    -- Functor Con → Set called Tm
    Tm : Con → Set
    Tm Γ = Γ → TM
    _[_]t : {Γ Δ : Con} → Tm Γ → Sub Δ Γ → Tm Δ -- The functor's action on morphisms
    t [ σ ]t = λ x → t (σ x)
    []t-id : {Γ : Con} → {x : Tm Γ} → x [ id {Γ} ]t ≡ x
    []t-id = refl
    []t-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {t : Tm Γ} → t [ β ∘ α ]t ≡ (t [ β ]t) [ α ]t
    []t-∘ {α = α} {β} {t} = refl {_} {_} {λ z → t (β (α z))}
                                                                                                       
    -- Tm⁺
    _▹ₜ : Con → Con
    Γ ▹ₜ = Γ × TM
    πₜ¹ : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Sub Δ Γ
    πₜ¹ σ = λ x → proj×₁ (σ x)
    πₜ² : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Tm Δ
    πₜ² σ = λ x → proj×₂ (σ x) 
    _,ₜ_ : {Γ Δ : Con} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹ₜ)
    σ ,ₜ t = λ x → (σ x) ,× (t x)
    πₜ²∘,ₜ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm Δ} → πₜ² (σ ,ₜ t) ≡ t
    πₜ²∘,ₜ {σ = σ} {t} = refl {a = t}
    πₜ¹∘,ₜ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm Δ} → πₜ¹ (σ ,ₜ t) ≡ σ
    πₜ¹∘,ₜ = refl
    ,ₜ∘πₜ : {Γ Δ : Con} → {σ : Sub Δ (Γ ▹ₜ)} → (πₜ¹ σ) ,ₜ (πₜ² σ) ≡ σ
    ,ₜ∘πₜ = refl
                                                                       
    -- Functor Con → Set called For
    For : Con → Set₁
    For Γ = Γ → Prop
    _[_]f : {Γ Δ : Con} → For Γ → Sub Δ Γ → For Δ
    F [ σ ]f = λ x → F (σ x)
    []f-id : {Γ : Con} → {F : For Γ} → F [ id {Γ} ]f ≡ F
    []f-id = refl
    []f-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {F : For Γ} → F [ β ∘ α ]f ≡ (F [ β ]f) [ α ]f
    []f-∘ = refl
                                                                                                        
    -- Proofs
    _⊢_ : (Γ : Con) → For Γ → Prop
    Γ ⊢ F = ∀ (γ : Γ) → F γ
    _[_]p : {Γ Δ : Con} → {F : For Γ} → Γ ⊢ F → (σ : Sub Δ Γ) → Δ ⊢ (F [ σ ]f)
    prf [ σ ]p = λ γ → prf (σ γ)
    -- Two rules are irrelevent beccause Γ ⊢ F is in Prop

    -- → Prop⁺
    _▹ₚ_ : (Γ : Con) → For Γ → Con
    Γ ▹ₚ F = Γ ×'' F
    πₚ¹ : {Γ Δ : Con} → {F : For Γ} → Sub Δ (Γ ▹ₚ F) → Sub Δ Γ
    πₚ¹ σ δ = proj×''₁ (σ δ)
    πₚ² : {Γ Δ : Con} → {F : For Γ} → (σ : Sub Δ (Γ ▹ₚ F)) → Δ ⊢ (F [ πₚ¹ σ ]f)
    πₚ² σ δ = proj×''₂ (σ δ)
    _,ₚ_ : {Γ Δ : Con} → {F : For Γ} → (σ : Sub Δ Γ) → Δ ⊢ (F [ σ ]f) → Sub Δ (Γ ▹ₚ F)
    _,ₚ_ {F = F} σ pf δ = (σ δ) ,×'' pf δ
    ,ₚ∘πₚ : {Γ Δ : Con} → {F : For Γ} → {σ : Sub Δ (Γ ▹ₚ F)} → (πₚ¹ σ) ,ₚ (πₚ² σ) ≡ σ
    ,ₚ∘πₚ = refl
    πₚ¹∘,ₚ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {F : For Γ} → {prf : Δ ⊢ (F [ σ ]f)} → πₚ¹ {Γ} {Δ} {F} (σ ,ₚ prf) ≡ σ
    πₚ¹∘,ₚ = refl                                                                 
                                                                                                      
    -- Implication
    _⇒_ : {Γ : Con} → For Γ → For Γ → For Γ
    F ⇒ G = λ γ → (F γ) → (G γ)
    []f-⇒ : {Γ Δ : Con} → {F G : For Γ} → {σ : Sub Δ Γ} → (F ⇒ G) [ σ ]f ≡ (F [ σ ]f) ⇒ (G [ σ ]f)
    []f-⇒ = refl
                                                                                               
    -- Forall
    ∀∀ : {Γ : Con} → For (Γ ▹ₜ) → For Γ
    ∀∀ {Γ} F = λ (γ : Γ) → (∀ (t : TM) → F (γ ,× t))
    []f-∀∀ : {Γ Δ : Con} → {F : For (Γ ▹ₜ)} → {σ : Sub Δ Γ} → {t : Tm Γ} → (∀∀ F) [ σ ]f ≡ (∀∀ (F [ (σ ∘ πₜ¹ id) ,ₜ πₜ² id ]f))
    []f-∀∀ {Γ} {Δ} {F} {σ} {t} = refl
                                                                                                                                        
    -- Lam & App
    lam : {Γ : Con} → {F : For Γ} → {G : For Γ} → (Γ ▹ₚ F) ⊢ (G [ πₚ¹ id ]f) → Γ ⊢ (F ⇒ G)
    lam pf = λ γ x → pf (γ ,×'' x)
    app : {Γ : Con} → {F G : For Γ} → Γ ⊢ (F ⇒ G) → Γ ⊢ F → Γ ⊢ G
    app pf pf' = λ γ → pf γ (pf' γ)
    -- Again, we don't write the _[_]p equalities as everything is in Prop

    -- ∀i and ∀e
    ∀i : {Γ : Con} → {F : For (Γ ▹ₜ)} → (Γ ▹ₜ) ⊢ F → Γ ⊢ (∀∀ F)
    ∀i p γ = λ t → p (γ ,× t)
    ∀e : {Γ : Con} → {F : For (Γ ▹ₜ)} → Γ ⊢ (∀∀ F) → {t : Tm Γ} → Γ ⊢ ( F [(id {Γ}) ,ₜ t ]f)
    ∀e p {t} γ = p γ (t γ)

    tod : FFOL
    tod = record
            { Con = Con
            ; Sub = Sub
            ; _∘_ = _∘_
            ; id = id
            ; ◇ = ◇
            ; ε = ε
            ; Tm = Tm
            ; _[_]t = _[_]t
            ; []t-id = []t-id
            ; []t-∘ = λ {Γ} {Δ} {Ξ} {α} {β} {t} → []t-∘ {Γ} {Δ} {Ξ} {α} {β} {t}
            ; _▹ₜ = _▹ₜ
            ; πₜ¹ = πₜ¹
            ; πₜ² = πₜ²
            ; _,ₜ_ = _,ₜ_
            ; πₜ²∘,ₜ = λ {Γ} {Δ} {σ} → πₜ²∘,ₜ {Γ} {Δ} {σ}
            ; πₜ¹∘,ₜ = λ {Γ} {Δ} {σ} {t} → πₜ¹∘,ₜ {Γ} {Δ} {σ} {t}
            ; ,ₜ∘πₜ = ,ₜ∘πₜ
            ; For = For
            ; _[_]f = _[_]f
            ; []f-id = []f-id
            ; []f-∘ = λ {Γ} {Δ} {Ξ} {α} {β} {F} → []f-∘ {Γ} {Δ} {Ξ} {α} {β} {F}
            ; _⊢_ = _⊢_
            ; _▹ₚ_ = _▹ₚ_
            ; πₚ¹ = πₚ¹
            ; πₚ² = πₚ²
            ; _,ₚ_ = _,ₚ_
            ; ,ₚ∘πₚ = ,ₚ∘πₚ
            ; πₚ¹∘,ₚ = λ {Γ} {Δ} {F} {σ} {p} → πₚ¹∘,ₚ {Γ} {Δ} {F} {σ} {p}
            ; _⇒_ = _⇒_
            ; []f-⇒ = λ {Γ} {F} {G} {σ} → []f-⇒ {Γ} {F} {G} {σ}
            ; ∀∀ = ∀∀
            ; []f-∀∀ = λ {Γ} {Δ} {F} {σ} {t} → []f-∀∀ {Γ} {Δ} {F} {σ} {t}
            ; lam = lam
            ; app = app
            ; ∀i = ∀i
            ; ∀e = ∀e
            }
  {-
  module M where
  
    data Con : Set
    data For : Con → Set
    data _⊢_ : (Γ : Con) → For Γ → Prop
    
    data Con where
      ◇ : Con 
     _▹ₜ : Con → Con
      _▹ₚ_ : (Γ : Con) → (A : For Γ) → Con
    data Sub : Con → Con → Set where
      id : {Γ : Con} → Sub Γ Γ
      next▹ₜ : {Γ Δ : Con} → Sub Δ Γ → Sub Δ (Γ ▹ₜ)
      next▹ₚ : {Γ Δ : Con} → {A : For Γ} → Sub Δ Γ → Sub Δ (Γ ▹ₚ A)
      _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
    ε : {Γ : Con} → Sub ◇ Γ
    ε {◇} = id
    ε {Γ ▹ₜ} = next▹ₜ ε
    ε {Γ ▹ₚ A} = next▹ₚ ε
      
    
    data For where
      _⇒_ : {Γ : Con} → For Γ → For Γ → For Γ
      ∀∀ : {Γ : Con} → For (Γ ▹ₜ) → For Γ
    infixr 10 _∘_
                                                                    
    -- Functor Con → Set called Tm
    data Tm : Con → Set where
      zero : {Γ : Con} → Tm (Γ ▹ₜ)
      next : {Γ : Con} → Tm Γ → Tm (Γ ▹ₜ)
    _[_]t : {Γ Δ : Con} → Tm Γ → Sub Δ Γ → Tm Δ -- The functor's action on morphisms
    []t-id : {Γ : Con} → {x : Tm Γ} → x [ id {Γ} ]t ≡ x
    []t-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {t : Tm Γ} → t [ β ∘ α ]t ≡ (t [ β ]t) [ α ]t
                                                                                                       
    -- Tm⁺
    πₜ¹ : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Sub Δ Γ
    πₜ² : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Tm Δ
    _,ₜ_ : {Γ Δ : Con} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹ₜ)
    πₜ²∘,ₜ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm Δ} → πₜ² (σ ,ₜ t) ≡ t
    πₜ¹∘,ₜ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm Δ} → πₜ¹ (σ ,ₜ t) ≡ σ
    ,ₜ∘πₜ : {Γ Δ : Con} → {σ : Sub Δ (Γ ▹ₜ)} → (πₜ¹ σ) ,ₜ (πₜ² σ) ≡ σ
    
    -- Functor Con → Set called For
    _[_]f : {Γ Δ : Con} → For Γ → Sub Δ Γ → For Δ -- The functor's action on morphisms
    []f-id : {Γ : Con} → {F : For Γ} → F [ id {Γ} ]f ≡ F
    []f-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {F : For Γ} → F [ β ∘ α ]f ≡ (F [ β ]f) [ α ]f
                                                                                                        
    -- Proofs
    _[_]p : {Γ Δ : Con} → {F : For Γ} → Γ ⊢ F → (σ : Sub Δ Γ) → Δ ⊢ (F [ σ ]f) -- The functor's action on morphisms
                                                                                                                               
    -- → Prop⁺
    πₚ¹ : {Γ Δ : Con} → {F : For Γ} → Sub Δ (Γ ▹ₚ F) → Sub Δ Γ
    πₚ² : {Γ Δ : Con} → {F : For Γ} → (σ : Sub Δ (Γ ▹ₚ F)) → Δ ⊢ (F [ πₚ¹ σ ]f)
    _,ₚ_ : {Γ Δ : Con} → {F : For Γ} → (σ : Sub Δ Γ) → Δ ⊢ (F [ σ ]f) → Sub Δ (Γ ▹ₚ F)
    ,ₚ∘πₚ : {Γ Δ : Con} → {F : For Γ} → {σ : Sub Δ (Γ ▹ₚ F)} → (πₚ¹ σ) ,ₚ (πₚ² σ) ≡ σ
    πₚ¹∘,ₚ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {F : For Γ} → {prf : Δ ⊢ (F [ σ ]f)} → πₚ¹ (σ ,ₚ prf) ≡ σ
                                                                                                      
                                                                                                      
    -- Implication
    []f-⇒ : {Γ Δ : Con} → {F G : For Γ} → {σ : Sub Δ Γ} → (F ⇒ G) [ σ ]f ≡ (F [ σ ]f) ⇒ (G [ σ ]f)
                                                                                               
    -- Forall
    []f-∀∀ : {Γ Δ : Con} → {F : For (Γ ▹ₜ)} → {σ : Sub Δ Γ} → {t : Tm Γ} → (∀∀ F) [ σ ]f ≡ (∀∀ (F [ ((id {Γ}) ,ₜ t) ∘ σ ∘(πₜ¹ (id {Δ ▹ₜ}))]f))
                                                                                                                                        
    -- Lam & App
    lam : {Γ : Con} → {F : For Γ} → {G : For Γ} → (Γ ▹ₚ F) ⊢ (G [ πₚ¹ id ]f) → Γ ⊢ (F ⇒ G)
    app : {Γ : Con} → {F G : For Γ} → Γ ⊢ (F ⇒ G) → Γ ⊢ F → Γ ⊢ G
    -- Again, we don't write the _[_]p equalities as everything is in Prop
                                                                      
    -- ∀i and ∀e
    ∀i : {Γ : Con} → {F : For (Γ ▹ₜ)} → (Γ ▹ₜ) ⊢ F → Γ ⊢ (∀∀ F)
    ∀e : {Γ : Con} → {F : For (Γ ▹ₜ)} → Γ ⊢ (∀∀ F) → {t : Tm Γ} → Γ ⊢ ( F [(id {Γ}) ,ₜ t ]f)
  mod : FFOL
  mod = record {M}
  -}

--  tod : FFOL
--  tod = record {Tarski Term}

{-
  module FOL (x : Abs) where

    open Abs x

    variable
      Γ Δ : Con
  
    data Form : Con → Set where
      _⇒_ : Form Γ → Form Γ → Form Γ
      
    infixr 8 _⇒_

    vv : Set
    vv = Nat

    record λcalculus : Set₁ where
      field
        Con : Set
        Sub : Con → Con → Set -- Prop makes a posetal category
        _=s_ : {Γ Δ : Con} →  Sub Γ Δ → Sub Γ Δ → Prop
        _∘_ : {Γ Δ Ξ : Con} → Sub Γ Δ → Sub Δ Ξ → Sub Γ Ξ
        id : {Γ : Con} → Sub Γ Γ
        ◇ : Con
        ε : {Γ : Con} → Sub ◇ Γ
        
        Tm : Con → Set
        _=t_ : {Γ : Con} → Tm Γ → Tm Γ → Prop
        _[_] : {Γ Δ : Con} → Tm Δ → Sub Γ Δ → Tm Γ
        [∘] : {Γ Δ Ξ : Con} → {σ : Sub Γ Δ} → {δ : Sub Δ Ξ} → {t : Tm Ξ} → (t [ (σ ∘ δ) ]) =t ((t [ δ ]) [ σ ])
        [id] : {Γ : Con} → {t : Tm Γ} → (t [ id {Γ} ]) =t t

        app : {Γ : Con} → Tm Γ → Tm Γ → Tm Γ
        app[] : {Γ Δ : Con} → {σ : Sub Γ Δ} → {x y : Tm Δ} → ((app x y) [ σ ]) =t (app (x [ σ ]) (y [ σ ]))

        _▻_ : (Γ : Con) → Tm Γ → Con
        π₁₁ : {Γ Δ : Con} → {t : Tm Γ} → Sub Δ (Γ ▻ t) → (Sub Δ Γ)
        π₁₂ : {Γ Δ : Con} → {t : Tm Γ} → Sub Δ (Γ ▻ t) → (Tm (Γ ▻ t))
        π₂ : {Γ Δ : Con} → {t : Tm Γ} → Sub Δ Γ → Tm (Γ ▻ t) → Sub Δ (Γ ▻ t)

        inj1 : {Γ Δ : Con} → {t : Tm Γ} → {σ : Sub Δ (Γ ▻ t)} → (π₂ (π₁₁ σ) (π₁₂ σ)) =s σ
        inj2 : {Γ Δ : Con} → {t : Tm Γ} → {σ : Sub Δ Γ} → {x : Tm (Γ ▻ t)} → (π₁₁ (π₂ σ x) =s σ) ∧ (π₁₂ (π₂ σ x) =t x )

        lam : {Γ : Con} → {t : Tm Γ} → Tm (Γ ▻ t) → Tm Γ
--        lam[] : {Γ Δ : Con} → {t : Tm Γ} → {σ : Sub Δ Γ} → {x : Tm (Γ ▻ t)} → ((lam x) [ σ ]) =t (lam (x [ σ ∘ (π₂ (id {Γ}) x) ]))




    data λterm : Set where
      lam : (λterm → λterm) → λterm
      app : λterm → λterm → λterm

    E : λterm
    E = app (lam (λ x → app x x)) (lam (λ x → app x x))

    data _→β_ : λterm → λterm → Prop where
      βrule : {t : λterm → λterm} → {x : λterm} → (app (lam t) x) →β (t x)
--      βtran : {x y z : λterm} → x →β y → y →β z → x →β z
      βcong1 : {x y z : λterm} → x →β y → app x z →β app y z
      βcong2 : {x y z : λterm} → x →β y → app z x →β app z y
      βcong3 : {t : λterm → λterm} → ({x y : λterm} → x →β y → t x →β t y) → lam t →β lam t


    thm : E →β E
    thm = βrule

    
   

    -- Proofs
  
    private
      variable
        A B : Form Γ
  
    data ⊢ : Form Γ → Prop where
      lam : (⊢ A → ⊢ B) → ⊢ (A ⇒ B)
      app : ⊢ (A ⇒ B) → (⊢ A → ⊢ B)
  


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

-}
