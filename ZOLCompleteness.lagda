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
      Ι≤ : {w w' : World} → w -w-> w' → Ι w' → Ι w
      
    infixr 10 _∘_

    Con : Set (lsuc ℓ¹)
    Con = World → Prop ℓ¹
    Sub : Con → Con → Prop ℓ¹
    Sub Δ Γ = (w : World) → Δ w → Γ w
    _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
    α ∘ β = λ w γ → α w (β w γ)
    id : {Γ : Con} → Sub Γ Γ
    id = λ w γ → γ
    ◇ : Con -- The initial object of the category
    ◇ = λ w → ⊤
    ε : {Γ : Con} → Sub Γ ◇ -- The morphism from the initial to any object
    ε w Γ = tt
                                                                    
                                                               
    -- Functor Con → Set called For
    For : Con → Set (lsuc ℓ¹)
    For Γ = (w : World) → (Γ w) → Prop ℓ¹
    _[_]f : {Γ Δ : Con} → For Γ → Sub Δ Γ → For Δ -- The functor's action on morphisms
    F [ σ ]f = λ w → λ x → F w (σ w x)
                                                                                                        
    -- Proofs
    Pf : (Γ : Con) → For Γ → Prop ℓ¹
    Pf Γ F = ∀ w (γ : Γ w) →  F w γ
    _[_]p : {Γ Δ : Con} → {F : For Γ} → Pf Γ F → (σ : Sub Δ Γ) → Pf Δ (F [ σ ]f) -- The functor's action on morphisms
    prf [ σ ]p = λ w → λ γ → prf w (σ w γ)
    -- Equalities below are useless because Γ ⊢ F is in prop
    -- []p-id : {Γ : Con} → {F : For Γ} → {prf : Γ ⊢ F} → prf [ id {Γ} ]p ≡ prf
    -- []p-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {F : For Γ} → {prf : Γ ⊢ F} → prf [ α ∘ β ]p ≡ (prf [ β ]p) [ α ]p
                                                                                                                               
    -- → Prop⁺
    _▹ₚ_ : (Γ : Con) → For Γ → Con
    Γ ▹ₚ F = λ w → Γ w ×p F w
    πₚ¹ : {Γ Δ : Con} → {F : For Γ} → Sub Δ (Γ ▹ₚ F) → Sub Δ Γ
    πₚ¹ σ w δ = proj×p₁ (σ w δ)
    πₚ² : {Γ Δ : Con} → {F : For Γ} → (σ : Sub Δ (Γ ▹ₚ F)) → Pf Δ (F [ πₚ¹ σ ]f)
    πₚ² σ w δ = proj×p₂ (σ w δ)
    _,ₚ_ : {Γ Δ : Con} → {F : For Γ} → (σ : Sub Δ Γ) → Pf Δ (F [ σ ]f) → Sub Δ (Γ ▹ₚ F)
    (σ ,ₚ pf) w δ = (σ w δ) ,×p pf w δ
                                                                                                      

    -- Base formula
    ι : {Γ : Con} → For Γ
    ι = λ w → λ γ → Ι w
    
    -- Implication
    _⇒_ : {Γ : Con} → For Γ → For Γ → For Γ
    (F ⇒ G) w γ = {w' : World} → (s : w -w-> w') → (F w' {!s γ!}) → (G w' {!!})
                                                                                                            
    -- Lam & App
    lam : {Γ : Con} → {F : For Γ} → {G : For Γ} → Pf (Γ ▹ₚ F) (G [ πₚ¹ id ]f) → Pf Γ (F ⇒ G)
    --lam prf = λ w γ w' s h → prf w (γ ,×p h)
    app : {Γ : Con} → {F G : For Γ} → Pf Γ (F ⇒ G) → Pf Γ F → Pf Γ G
    --app prf prf' = λ w γ → prf w γ w -w->id (prf' w γ)
    -- Again, we don't write the _[_]p equalities as everything is in Prop
    
    zol : ZOL
    zol = record
            { Con = Con
            ; Sub = Sub
            ; _∘_ = _∘_
            ; id = id
            ; ◇ = ◇
            ; ε = ε
            ; For = For
            ; _[_]f = _[_]f
            ; []f-id = refl
            ; []f-∘ = refl
            ; Pf = Pf
            ; _[_]p = _[_]p
            ; _▹ₚ_ = _▹ₚ_
            ; πₚ¹ = πₚ¹
            ; πₚ² = πₚ²
            ; _,ₚ_ = _,ₚ_
            ; ι = ι
            ; []f-ι = refl
            ; _⇒_ = _⇒_
            ; []f-⇒ = refl
            ; lam = lam
            ; app = app
            }

\end{code}
  module U where

    import ZOLInitial as I

    U : Kripke
    U = record
        { World = I.Con
        ; _-w->_ = I.Sub
        ; -w->id = I.id
        ; _∘-w->_ = λ σ σ' → σ' I.∘ σ
        ; Ι = λ Γ → I.Pf Γ I.ι
        ; Ι≤ = λ s pf → pf I.[ s ]p
        }

    open Kripke U

    y : Mapping I.zol zol
    y = record
      { mCon = λ Γ Δ → I.Sub Δ Γ
      ; mSub = λ σ Ξ δ → σ I.∘ δ
      ; mFor = λ A Ξ σ → I.Pf Ξ A
      ; mPf = λ pf Ξ σ → pf I.[ σ ]p
      }
    m : Morphism I.zol zol
    m = I.InitialMorphism.mor zol

    u : (Γ : I.Con) → Sub (Morphism.mCon m Γ) (Mapping.mCon y Γ)
    q : (Γ : I.Con) → Sub (Mapping.mCon y Γ) (Morphism.mCon m Γ)

    ⟦_⟧c = Morphism.mCon m
    ⟦_,_⟧f = λ A Γ →  Morphism.mFor m {Γ} A

    ⟦⟧f-mon : {Γ : I.Con}{A : I.For}{w w' : World}{γ : ⟦ Γ ⟧c w}{γ' : ⟦ Γ ⟧c w'} → w -w-> w' → ⟦ A , Γ ⟧f w' γ' → ⟦ A , Γ ⟧f w γ
    ⟦⟧f-mon {A = I.ι} s h = Ι≤ s h
    ⟦⟧f-mon {A = A I.⇒ B} s h w'' s' h' = {!h!}

    ⟦⟧c-mon : {Γ : I.Con}{w w' : I.Con} → w -w-> w' → ⟦ Γ ⟧c w → ⟦ Γ ⟧c w'
    ⟦⟧c-mon s h = {!!}

    q⁰ : {F : I.For} → {Γ : I.Con} → Pf ⟦ Γ ⟧c ⟦ F , Γ ⟧f → I.Pf Γ F
    u⁰ : {F : I.For} → {Γ : I.Con} → I.Pf Γ F → Pf ⟦ Γ ⟧c ⟦ F , Γ ⟧f
    
    u⁰ {I.ι} h w γ = {!!}
    u⁰ {A I.⇒ B} h Γ' γ Γ'' iq hF = u⁰ {B} (I.app {A = A} h (q⁰ (λ Ξ γ' → {!hF!}))) {!!} γ --{Γ'} iq hF = u {F₁} (app {Γ'} {F} {F₁} (⊢tran iq h) (q hF))
    
    q⁰ {I.ι} {Γ} h = h Γ {!!}
    q⁰ {A I.⇒ B} {Γ} h = I.lam (q⁰ (λ w γ → {!h ? ? ? (I.πₚ¹ I.id)!})) --lam (q (h (retro (Preorder.refl≤ o)) (u {F} {F ∷ Γ} zero)))
  
    u I.◇ Δ x = I.ε
    u (Γ I.▹ₚ I.ι) Δ (Γu ,×p Au) = u Γ Δ Γu I.,ₚ Au
    --u (Γ I.▹ₚ (A I.⇒ B)) Δ (Γu ,×p ABu) = (u Γ Δ Γu) I.,ₚ I.lam (I.πₚ² (u (Γ I.▹ₚ B) (Δ I.▹ₚ A) ({!!} ,×p {!!})))
    u (Γ I.▹ₚ (A I.⇒ B)) Δ (Γu ,×p ABu) = (u Γ Δ Γu) I.,ₚ {!!}
    q .I.◇ Δ I.ε = tt
    q (Γ I.▹ₚ I.ι) Δ σ = (q Γ Δ (I.πₚ¹ σ)) ,×p I.πₚ² σ
    q (Γ I.▹ₚ (A I.⇒ B)) Δ σ = (q Γ Δ (I.πₚ¹ σ)) ,×p {!!}

    {-
    u {Var x} h = h
    u {F ⇒ F₁} h {Γ'} iq hF = u {F₁} (app {Γ'} {F} {F₁} (⊢tran iq h) (q hF))
    u {F ∧∧ G} h = ⟨ (u {F} (ande₁ h)) , (u {G} (ande₂ h)) ⟩
    u {⊤⊤} h = tt
    
    q {Var x} h = neu⁰ h
    q {F ⇒ F₁} {Γ} h = lam (q (h (retro (Preorder.refl≤ o)) (u {F} {F ∷ Γ} zero)))
    q {F ∧∧ G} ⟨ hF , hG ⟩ = andi (q {F} hF) (q {G} hG)
    q {⊤⊤} h = true
    -}
    
    ηu : TrNat (Morphism.m m) y
    ηu = record { f = u }
    ηq : TrNat y (Morphism.m m)
    ηq = record { f = q }

    eq : ηu ∘TrNat ηq ≡ idTrNat
    eq = {!!}


    -- Transformation naturelle
    

\end{code}


  -- Completeness proof

  -- We first build our universal Kripke model
  
  module ComplenessProof where
    
    -- We have a model, we construct the Universal Presheaf model of this model
    import ZOLInitial as I

\end{code} 
