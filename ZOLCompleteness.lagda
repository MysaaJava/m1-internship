\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import PropUtil

module ZOLCompleteness where

  open import Agda.Primitive
  open import ZOL2
  open import ListUtil

  record Kripke : Set (lsuc (ℓ¹)) where
    field
      World : Set ℓ¹
      _-w->_ : World → World → Prop ℓ¹ -- arrows
      -w->id : {w : World} → w -w-> w -- id arrow
      _∘-w->_ : {w w' w'' : World} → w -w-> w' → w' -w-> w'' → w -w-> w'' -- arrow composition

      Ι : World → Prop ℓ¹
      Ι≤ : {w w' : World} → w -w-> w' → Ι w → Ι w'
      
    infixr 10 _∘_

    Con : Set (lsuc ℓ¹)
    Con = (World → Prop ℓ¹) ×'' (λ Γ → {w w' : World} → (w -w-> w')→ Γ w → Γ w')
    Sub : Con → Con → Prop ℓ¹
    Sub Δ Γ = (w : World) → (proj×''₁ Δ) w → (proj×''₁ Γ) w
    _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
    α ∘ β = λ w γ → α w (β w γ)
    id : {Γ : Con} → Sub Γ Γ
    id = λ w γ → γ
    ◇ : Con -- The initial object of the category
    ◇ = (λ w → ⊤) ,×'' (λ _ _ → tt)
    ε : {Γ : Con} → Sub Γ ◇ -- The morphism from the initial to any object
    ε w Γ = tt
                                                                    
    -- Functor Con → Set called For
    For : Set (lsuc ℓ¹)
    For = (World → Prop ℓ¹) ×'' (λ F → {w w' : World} → (w -w-> w')→ F w → F w')
                                                                                                        
    -- Proofs
    Pf : (Γ : Con) → For → Prop ℓ¹
    Pf Γ F = ∀ w (γ : (proj×''₁ Γ) w) →  (proj×''₁ F) w
    _[_]p : {Γ Δ : Con} → {F : For} → Pf Γ F → (σ : Sub Δ Γ) → Pf Δ F -- The functor's action on morphisms
    prf [ σ ]p = λ w → λ γ → prf w (σ w γ)
    -- Equalities below are useless because Γ ⊢ F is in prop
    -- []p-id : {Γ : Con} → {F : For Γ} → {prf : Γ ⊢ F} → prf [ id {Γ} ]p ≡ prf
    -- []p-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {F : For Γ} → {prf : Γ ⊢ F} → prf [ α ∘ β ]p ≡ (prf [ β ]p) [ α ]p

    
    -- → Prop⁺
    _▹ₚ_ : (Γ : Con) → For → Con
    Γ ▹ₚ F = (λ w → (proj×''₁ Γ) w ∧ (proj×''₁ F) w) ,×'' λ s γ → ⟨ proj×''₂ Γ s (proj₁ γ) , proj×''₂ F s (proj₂ γ) ⟩
    
    πₚ¹ : {Γ Δ : Con} → {F : For} → Sub Δ (Γ ▹ₚ F) → Sub Δ Γ
    πₚ¹ σ w δ = proj₁ (σ w δ)
    πₚ² : {Γ Δ : Con} → {F : For} → (σ : Sub Δ (Γ ▹ₚ F)) → Pf Δ F
    πₚ² σ w δ = proj₂ (σ w δ)
    _,ₚ_ : {Γ Δ : Con} → {F : For} → (σ : Sub Δ Γ) → Pf Δ F → Sub Δ (Γ ▹ₚ F)
    (σ ,ₚ pf) w δ = ⟨ (σ w δ) , pf w δ ⟩
                                                                                                      

    -- Base formula
    ι : For
    ι = (λ w → Ι w) ,×'' λ s f → Ι≤ s f
    
    -- Implication
    _⇒_ : For → For → For
    (F ⇒ G) = (λ w → {w' : World} → (s : w -w-> w') → ((proj×''₁ F) w') → ((proj×''₁ G) w')) ,×'' λ s f s' f' → f (s ∘-w-> s') f'
                                                                                                            
    -- Lam & App
    lam : {Γ : Con} → {F : For} → {G : For} → Pf (Γ ▹ₚ F) G → Pf Γ (F ⇒ G)
    lam {Γ} pf w γ {w'} s x = pf w' ⟨ proj×''₂ Γ s γ , x ⟩
    --lam prf = λ w γ w' s h → prf w (γ , h)
    app : {Γ : Con} → {F G : For} → Pf Γ (F ⇒ G) → Pf Γ F → Pf Γ G
    app pf pf' w γ = pf w γ -w->id (pf' w γ)
    -- Again, we don't write the _[_]p equalities as everything is in Prop
    
    zol : ZOL
    zol = record
            { Con = Con
            ; Sub = Sub
            ; _∘_ = λ {Γ}{Δ}{Ξ} σ δ → _∘_ {Γ}{Δ}{Ξ} σ δ
            ; id =  λ {Γ} → id {Γ}
            ; ◇ = ◇
            ; ε = λ {Γ} → ε {Γ}
            ; For = λ Γ → For
            ; _[_]f = λ A σ → A
            ; []f-id = refl
            ; []f-∘ = refl
            ; Pf = Pf
            ; _[_]p = λ {Γ}{Δ}{F} pf σ → _[_]p {Γ}{Δ}{F} pf σ
            ; _▹ₚ_ = _▹ₚ_
            ; πₚ¹ = λ {Γ}{Δ}{F}σ → πₚ¹ {Γ}{Δ}{F} σ
            ; πₚ² = λ {Γ}{Δ}{F}σ → πₚ² {Γ}{Δ}{F} σ
            ; _,ₚ_ = λ {Γ}{Δ}{F} σ pf → _,ₚ_ {Γ}{Δ}{F}σ pf
            ; ι = ι
            ; []f-ι = refl
            ; _⇒_ = _⇒_
            ; []f-⇒ = refl
            ; lam = λ {Γ}{F}{G} pf → lam {Γ}{F}{G} pf
            ; app = λ {Γ}{F}{G} pf pf' → app {Γ}{F}{G} pf pf'
            }

  module U where

    import ZOLInitial as I

    U : Kripke
    U = record
        { World = I.Con
        ; _-w->_ = λ Γ Δ → I.Sub Δ Γ
        ; -w->id = I.id
        ; _∘-w->_ = λ σ σ' → σ I.∘ σ'
        ; Ι = λ Γ → I.Pf Γ I.ι
        ; Ι≤ = λ s pf → pf I.[ s ]p
        }

    open Kripke U

    y : Mapping I.zol zol
    y = record
      { mCon = λ Γ → (λ Δ → I.Sub Δ Γ) ,×'' λ σ δ → δ I.∘ σ
      ; mSub = λ σ Ξ δ → σ I.∘ δ
      ; mFor = λ A → (λ Ξ → I.Pf Ξ A) ,×'' λ σ pf → pf I.[ σ ]p
      ; mPf = λ pf Ξ σ → pf I.[ σ ]p
      }
    m : Morphism I.zol zol
    m = I.InitialMorphism.mor zol

    q : (Γ : I.Con) → Sub (Morphism.mCon m Γ) (Mapping.mCon y Γ)
    u : (Γ : I.Con) → Sub (Mapping.mCon y Γ) (Morphism.mCon m Γ)

    ⟦_⟧c = Morphism.mCon m
    ⟦_,_⟧f = λ A Γ →  Morphism.mFor m {Γ} A
    
    q⁰ : {F : I.For} → {Γ Γ₀ : I.Con} → proj×''₁ ⟦ F , Γ₀ ⟧f Γ → I.Pf Γ F
    u⁰ : {F : I.For} → {Γ Γ₀ : I.Con} → I.Pf Γ F → proj×''₁ ⟦ F , Γ₀ ⟧f Γ

    q⁰ {I.ι} {Γ} h = h
    q⁰ {A I.⇒ B} {Γ} h = I.lam (q⁰ {B} (h (I.πₚ¹ I.id) (u⁰ {A} (I.var I.pvzero))))
    u⁰ {I.ι} {Γ} pf = pf
    u⁰ {A I.⇒ B} {Γ} pf iq hF  = u⁰ {B} (I.app (pf I.[ iq ]p) (q⁰ hF) )
    

    q I.◇ w γ = I.ε
    q (Γ I.▹ₚ A) w γ = (q Γ w (proj₁ γ) I.,ₚ q⁰ (proj₂ γ))
    u I.◇ w σ = tt
    u (Γ I.▹ₚ A) w σ = ⟨ (u Γ w (I.πₚ¹ σ)) , u⁰ (I.πₚ² σ) ⟩
    
    ηq : TrNat (Morphism.m m) y
    ηq = record { f = q }
    ηu : TrNat y (Morphism.m m)
    ηu = record { f = u }

    eq : ηu ∘TrNat ηq ≡ idTrNat
    eq = refl

    realCompleteness : {Γ Δ : I.Con} → ({Ξ : I.Con} → (proj×''₁ ⟦ Γ ⟧c) Ξ → (proj×''₁ ⟦ Δ ⟧c) Ξ )  → I.Sub Γ Δ
    realCompleteness {Γ} {Δ} f = q Δ Γ (f {Γ} (u Γ Γ I.id))

\end{code}
