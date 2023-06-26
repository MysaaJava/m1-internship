{-# OPTIONS --prop #-}

open import PropUtil

module FinitaryFirstOrderLogic (F : Nat → Set) (R : Nat → Set) where

  open import Agda.Primitive
  open import ListUtil

  variable
    ℓ¹ ℓ² ℓ³ ℓ⁴ ℓ⁵ : Level
    
  record FFOL (F : Nat → Set) (R : Nat → Set) : Set (lsuc (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓ⁴ ⊔ ℓ⁵)) where
    infixr 10 _∘_
    infixr 5 _⊢_
    field
      Con : Set ℓ¹
      Sub : Con → Con → Set ℓ⁵ -- It makes a posetal category
      _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
      id : {Γ : Con} → Sub Γ Γ
      ◇ : Con -- The initial object of the category
      ε : {Γ : Con} → Sub Γ ◇ -- The morphism from the initial to any object

      -- Functor Con → Set called Tm
      Tm : Con → Set ℓ²
      _[_]t : {Γ Δ : Con} → Tm Γ → Sub Δ Γ → Tm Δ -- The functor's action on morphisms
      []t-id : {Γ : Con} → {x : Tm Γ} → x [ id {Γ} ]t ≡ x
      []t-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {t : Tm Γ} → t [ β ∘ α ]t ≡ (t [ β ]t) [ α ]t

      -- Term extension with functions
      fun : {Γ : Con} → {n : Nat} → F n → Array (Tm Γ) n → Tm Γ
      fun[] : {Γ Δ : Con} → {σ : Sub Δ Γ} → {n : Nat} → {f : F n} → {tz : Array (Tm Γ) n} → (fun f tz) [ σ ]t ≡ fun f (map (λ t → t [ σ ]t) tz)

      -- Tm⁺
      _▹ₜ : Con → Con
      πₜ¹ : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Sub Δ Γ
      πₜ² : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Tm Δ
      _,ₜ_ : {Γ Δ : Con} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹ₜ)
      πₜ²∘,ₜ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm Δ} → πₜ² (σ ,ₜ t) ≡ t
      πₜ¹∘,ₜ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm Δ} → πₜ¹ (σ ,ₜ t) ≡ σ
      ,ₜ∘πₜ : {Γ Δ : Con} → {σ : Sub Δ (Γ ▹ₜ)} → (πₜ¹ σ) ,ₜ (πₜ² σ) ≡ σ
      ,ₜ∘ : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{t : Tm Γ} → (σ ,ₜ t) ∘ δ ≡ (σ ∘ δ) ,ₜ (t [ δ ]t)

      -- Functor Con → Set called For
      For : Con → Set ℓ³
      _[_]f : {Γ Δ : Con} → For Γ → Sub Δ Γ → For Δ -- The functor's action on morphisms
      []f-id : {Γ : Con} → {F : For Γ} → F [ id {Γ} ]f ≡ F
      []f-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {F : For Γ} → F [ β ∘ α ]f ≡ (F [ β ]f) [ α ]f

      -- Formulas with relation on terms
      rel : {Γ : Con} → {n : Nat} → R n → Array (Tm Γ) n → For Γ
      rel[] : {Γ Δ : Con} → {σ : Sub Δ Γ} → {n : Nat} → {r : R n} → {tz : Array (Tm Γ) n} → (rel r tz) [ σ ]f ≡ rel r (map (λ t → t [ σ ]t) tz)

      -- Proofs
      _⊢_ : (Γ : Con) → For Γ → Prop ℓ⁴
      _[_]p : {Γ Δ : Con} → {F : For Γ} → Γ ⊢ F → (σ : Sub Δ Γ) → Δ ⊢ (F [ σ ]f) -- The functor's action on morphisms
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
      ,ₚ∘ : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{F : For Ξ}{prf : Γ ⊢ (F [ σ ]f)} → (σ ,ₚ prf) ∘ δ ≡ (σ ∘ δ) ,ₚ (substP (λ F → Δ ⊢ F) (≡sym []f-∘) (prf [ δ ]p))


      -- Implication
      _⇒_ : {Γ : Con} → For Γ → For Γ → For Γ
      []f-⇒ : {Γ Δ : Con} → {F G : For Γ} → {σ : Sub Δ Γ} → (F ⇒ G) [ σ ]f ≡ (F [ σ ]f) ⇒ (G [ σ ]f)

      -- Forall
      ∀∀ : {Γ : Con} → For (Γ ▹ₜ) → For Γ
      []f-∀∀ : {Γ Δ : Con} → {F : For (Γ ▹ₜ)} → {σ : Sub Δ Γ} → (∀∀ F) [ σ ]f ≡ (∀∀ (F [ (σ ∘ πₜ¹ id) ,ₜ πₜ² id ]f))

      -- Lam & App
      lam : {Γ : Con} → {F : For Γ} → {G : For Γ} → (Γ ▹ₚ F) ⊢ (G [ πₚ¹ id ]f) → Γ ⊢ (F ⇒ G)
      app : {Γ : Con} → {F G : For Γ} → Γ ⊢ (F ⇒ G) → Γ ⊢ F → Γ ⊢ G
      -- Again, we don't write the _[_]p equalities as everything is in Prop

      -- ∀i and ∀e
      ∀i : {Γ : Con} → {F : For (Γ ▹ₜ)} → (Γ ▹ₜ) ⊢ F → Γ ⊢ (∀∀ F)
      ∀e : {Γ : Con} → {F : For (Γ ▹ₜ)} → Γ ⊢ (∀∀ F) → {t : Tm Γ} → Γ ⊢ ( F [(id {Γ}) ,ₜ t ]f)


    -- Examples
    -- Proof utils
    forall-in : {Γ Δ : Con} {σ : Sub Γ Δ} {A : For (Δ ▹ₜ)} → Γ ⊢ ∀∀ (A [ (σ ∘ πₜ¹ id) ,ₜ πₜ² id ]f) → Γ ⊢ (∀∀ A [ σ ]f)
    forall-in {Γ = Γ} f = substP (λ F → Γ ⊢ F) (≡sym ([]f-∀∀)) f
    wkₜ : {Γ : Con} → Sub (Γ ▹ₜ) Γ
    wkₜ = πₜ¹ id
    0ₜ : {Γ : Con} → Tm (Γ ▹ₜ)
    0ₜ = πₜ² id
    1ₜ : {Γ : Con} → Tm (Γ ▹ₜ ▹ₜ)
    1ₜ = πₜ² (πₜ¹ id)
    wkₚ : {Γ : Con} {A : For Γ} → Sub (Γ ▹ₚ A) Γ
    wkₚ = πₚ¹ id
    0ₚ : {Γ : Con} {A : For Γ} → Γ ▹ₚ A ⊢ A [ πₚ¹ id ]f
    0ₚ = πₚ² id

    --  Examples
    ex0 : {A :  For ◇} → ◇ ⊢ (A ⇒ A)
    ex0 {A = A} = lam 0ₚ
    {-
    ex1 : {A : For (◇ ▹ₜ)} → ◇ ⊢ ((∀∀ A) ⇒ (∀∀ A))
    -- πₚ¹ id is adding an unused variable (syntax's llift)
    ex1 {A = A} = lam (forall-in (∀i (substP (λ σ → ((◇ ▹ₚ ∀∀ A) ▹ₜ) ⊢ (A [ σ ]f)) {!!} {!!})))
    -- (∀ x ∀ y . A(y,x)) ⇒ ∀ x ∀ y . A(x,y)
    -- translation is (∀ ∀ A(0,1)) => (∀ ∀ A(1,0))
    ex1' : {A : For (◇ ▹ₜ ▹ₜ)} → ◇ ⊢ ((∀∀ (∀∀ A)) ⇒ ∀∀ (∀∀ ( A [ (ε ,ₜ 0ₜ) ,ₜ 1ₜ ]f)))
    ex1' = {!!}
    -- (A ⇒ ∀ x . B(x)) ⇒ ∀ x . A ⇒ B(x)
    ex2 : {A : For ◇} → {B : For (◇ ▹ₜ)} → ◇ ⊢ ((A ⇒ (∀∀ B)) ⇒ (∀∀ ((A [ wkₜ ]f) ⇒ B)))
    ex2 = {!!}
    -- ∀ x y . A(x,y) ⇒ ∀ x . A(x,x)
    -- For simplicity, I swiched positions of parameters of A (somehow...)
    ex3 : {A : For (◇ ▹ₜ ▹ₜ)} → ◇ ⊢ ((∀∀ (∀∀ A)) ⇒ (∀∀ (A [ id ,ₜ 0ₜ ]f)))
    ex3 = {!!}
    -- ∀ x . A (x) ⇒ ∀ x y . A(x)
    ex4 : {A : For (◇ ▹ₜ)} → ◇ ⊢ ((∀∀ A) ⇒ (∀∀ (∀∀ (A [ ε ,ₜ 1ₜ ]f))))
    ex4 = {!!}
    -- (((∀ x . A (x)) ⇒ B)⇒ B) ⇒ ∀ x . ((A (x) ⇒ B) ⇒ B)
    ex5 : {A : For (◇ ▹ₜ)} → {B : For ◇} → ◇ ⊢ ((((∀∀ A) ⇒ B) ⇒ B) ⇒ (∀∀ ((A ⇒ (B [ wkₜ ]f)) ⇒ (B [ wkₜ ]f))))
    ex5 = {!!}
    -}

  record Tarski : Set₁ where
    field
      TM : Set
      REL : (n : Nat) → R n → (Array TM n → Prop)
      FUN : (n : Nat) → F n → (Array TM n → TM)
    infixr 10 _∘_
    Con = Set
    Sub : Con → Con → Set
    Sub Γ Δ = (Γ → Δ) -- It makes a posetal category
    _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
    f ∘ g = λ x → f (g x)
    id : {Γ : Con} → Sub Γ Γ
    id = λ x → x
    record ◇ : Con where
      constructor ◇◇
    ε : {Γ : Con} → Sub Γ ◇ -- The morphism from the initial to any object
    ε Γ = ◇◇
                                                                    
    -- Functor Con → Set called Tm
    Tm : Con → Set
    Tm Γ = Γ → TM
    _[_]t : {Γ Δ : Con} → Tm Γ → Sub Δ Γ → Tm Δ -- The functor's action on morphisms
    t [ σ ]t = λ γ → t (σ γ)
    []t-id : {Γ : Con} → {x : Tm Γ} → x [ id {Γ} ]t ≡ x
    []t-id = refl
    []t-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {t : Tm Γ} → t [ β ∘ α ]t ≡ (t [ β ]t) [ α ]t
    []t-∘ {α = α} {β} {t} = refl {_} {_} {λ z → t (β (α z))}

    _[_]tz : {Γ Δ : Con} → {n : Nat} → Array (Tm Γ) n → Sub Δ Γ → Array (Tm Δ) n
    tz [ σ ]tz = map (λ s → s [ σ ]t) tz
    []tz-∘  : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {n : Nat} → {tz : Array (Tm Γ) n} → tz [ β ∘ α ]tz ≡ tz [ β ]tz [ α ]tz
    []tz-∘ {tz = zero} = refl
    []tz-∘ {α = α} {β = β} {tz = next x tz} = substP (λ tz' → (next ((x [ β ]t) [ α ]t) tz') ≡ (((next x tz) [ β ]tz) [ α ]tz)) (≡sym ([]tz-∘ {α = α} {β = β} {tz = tz})) refl
    []tz-id : {Γ : Con} → {n : Nat} → {tz : Array (Tm Γ) n} → tz [ id ]tz ≡ tz
    []tz-id {tz = zero} = refl
    []tz-id {tz = next x tz} = substP (λ tz' → next x tz' ≡ next x tz) (≡sym ([]tz-id {tz = tz})) refl
    thm : {Γ Δ : Con} → {n : Nat} → {tz : Array (Tm Γ) n} → {σ : Sub Δ Γ} → {δ : Δ} → map (λ t → t δ) (tz [ σ ]tz) ≡ map (λ t → t (σ δ)) tz
    thm {tz = zero} = refl
    thm {tz = next x tz} {σ} {δ} = substP (λ tz' → (next (x (σ δ)) (map (λ t → t δ) (map (λ s γ → s (σ γ)) tz))) ≡ (next (x (σ δ)) tz')) (thm {tz = tz}) refl

    -- Term extension with functions
    fun : {Γ : Con} → {n : Nat} → F n → Array (Tm Γ) n → Tm Γ
    fun {n = n} f tz = λ γ → FUN n f (map (λ t → t γ) tz)
    fun[] : {Γ Δ : Con} → {σ : Sub Δ Γ} → {n : Nat} → {f : F n} → {tz : Array (Tm Γ) n} → (fun f tz) [ σ ]t ≡ fun f (tz [ σ ]tz)
    fun[] {σ = σ} {n = n} {f = f} {tz = tz} = ≡fun (λ γ → (substP (λ x → (FUN n f) x ≡ (FUN n f) (map (λ t → t γ) (tz [ σ ]tz))) thm refl))
    
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
    ,ₜ∘ : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{t : Tm Γ} → (σ ,ₜ t) ∘ δ ≡ (σ ∘ δ) ,ₜ (t [ δ ]t)
    ,ₜ∘ = refl
                                                                       
    -- Functor Con → Set called For
    For : Con → Set₁
    For Γ = Γ → Prop
    _[_]f : {Γ Δ : Con} → For Γ → Sub Δ Γ → For Δ
    F [ σ ]f = λ x → F (σ x)
    []f-id : {Γ : Con} → {F : For Γ} → F [ id {Γ} ]f ≡ F
    []f-id = refl
    []f-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {F : For Γ} → F [ β ∘ α ]f ≡ (F [ β ]f) [ α ]f
    []f-∘ = refl

    -- Formulas with relation on terms
    rel : {Γ : Con} → {n : Nat} → R n → Array (Tm Γ) n → For Γ
    rel {n = n} r tz = λ γ → REL n r (map (λ t → t γ) tz)
    rel[] : {Γ Δ : Con} → {σ : Sub Δ Γ} → {n : Nat} → {r : R n} → {tz : Array (Tm Γ) n} → (rel r tz) [ σ ]f ≡ rel r (tz [ σ ]tz)
    rel[] {σ = σ} {n = n} {r = r} {tz = tz} = ≡fun (λ γ → (substP (λ x → (REL n r) x ≡ (REL n r) (map (λ t → t γ) (tz [ σ ]tz))) thm refl))
                                                                                                     
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
    ,ₚ∘ : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{F : For Ξ}{prf : Γ ⊢ (F [ σ ]f)} →
      (_,ₚ_  {F = F} σ prf) ∘ δ ≡ (σ ∘ δ) ,ₚ (substP (λ F → Δ ⊢ F) (≡sym ([]f-∘ {α = δ} {β = σ} {F = F})) (prf [ δ ]p))
    ,ₚ∘ {Γ} {Δ} {Ξ} {σ} {δ} {F} {prf} = refl
                                                                                                      
    -- Implication
    _⇒_ : {Γ : Con} → For Γ → For Γ → For Γ
    F ⇒ G = λ γ → (F γ) → (G γ)
    []f-⇒ : {Γ Δ : Con} → {F G : For Γ} → {σ : Sub Δ Γ} → (F ⇒ G) [ σ ]f ≡ (F [ σ ]f) ⇒ (G [ σ ]f)
    []f-⇒ = refl
                                                                                               
    -- Forall
    ∀∀ : {Γ : Con} → For (Γ ▹ₜ) → For Γ
    ∀∀ {Γ} F = λ (γ : Γ) → (∀ (t : TM) → F (γ ,× t))
    []f-∀∀ : {Γ Δ : Con} → {F : For (Γ ▹ₜ)} → {σ : Sub Δ Γ} → (∀∀ F) [ σ ]f ≡ (∀∀ (F [ (σ ∘ πₜ¹ id) ,ₜ πₜ² id ]f))
    []f-∀∀ {Γ} {Δ} {F} {σ} = refl
                                                                                                                                        
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

    tod : FFOL F R
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
            ; ,ₜ∘ = λ {Γ} {Δ} {Ξ} {σ} {δ} {t} → ,ₜ∘ {Γ} {Δ} {Ξ} {σ} {δ} {t}
            ; For = For
            ; _[_]f = _[_]f
            ; []f-id = []f-id
            ; []f-∘ = λ {Γ} {Δ} {Ξ} {α} {β} {F} → []f-∘ {Γ} {Δ} {Ξ} {α} {β} {F}
            ; _⊢_ = _⊢_
            ; _[_]p = _[_]p
            ; _▹ₚ_ = _▹ₚ_
            ; πₚ¹ = πₚ¹
            ; πₚ² = πₚ²
            ; _,ₚ_ = _,ₚ_
            ; ,ₚ∘πₚ = ,ₚ∘πₚ
            ; πₚ¹∘,ₚ = λ {Γ} {Δ} {F} {σ} {p} → πₚ¹∘,ₚ {Γ} {Δ} {F} {σ} {p}
            ; ,ₚ∘ = λ {Γ} {Δ} {Ξ} {σ} {δ} {F} {prf} → ,ₚ∘ {Γ} {Δ} {Ξ} {σ} {δ} {F} {prf}
            ; _⇒_ = _⇒_
            ; []f-⇒ = λ {Γ} {F} {G} {σ} → []f-⇒ {Γ} {F} {G} {σ}
            ; ∀∀ = ∀∀
            ; []f-∀∀ = λ {Γ} {Δ} {F} {σ} → []f-∀∀ {Γ} {Δ} {F} {σ}
            ; lam = lam
            ; app = app
            ; ∀i = ∀i
            ; ∀e = ∀e
            ; fun = fun
            ; fun[] = fun[]
            ; rel = rel
            ; rel[] = rel[]
            }


    -- (∀ x ∀ y . A(x,y)) ⇒ ∀ y ∀ x . A(y,x)
    -- both sides are ∀ ∀ A (0,1)
    ex1 : {A : For (◇ ▹ₜ ▹ₜ)} → ◇ ⊢ ((∀∀ (∀∀ A)) ⇒ (∀∀ (∀∀ A)))
    ex1 _ hyp = hyp
    -- (A ⇒ ∀ x . B(x)) ⇒ ∀ x . A ⇒ B(x)
    ex2 : {A : For ◇} → {B : For (◇ ▹ₜ)} → ◇ ⊢ ((A ⇒ (∀∀ B)) ⇒ (∀∀ ((A [ πₜ¹ id ]f) ⇒ B)))
    ex2 _ h t h' = h h' t
    -- ∀ x y . A(x,y) ⇒ ∀ x . A(x,x)
    -- For simplicity, I swiched positions of parameters of A (somehow...)
    ex3 : {A : For (◇ ▹ₜ ▹ₜ)} → ◇ ⊢ ((∀∀ (∀∀ A)) ⇒ (∀∀ (A [ id ,ₜ (πₜ² id) ]f)))
    ex3 _ h t = h t t
    -- ∀ x . A (x) ⇒ ∀ x y . A(x)
    ex4 : {A : For (◇ ▹ₜ)} → ◇ ⊢ ((∀∀ A) ⇒ (∀∀ (∀∀ (A [ ε ,ₜ (πₜ² (πₜ¹ id)) ]f))))
    ex4 {A} ◇◇ x t t' = x t
    -- (((∀ x . A (x)) ⇒ B)⇒ B) ⇒ ∀ x . ((A (x) ⇒ B) ⇒ B)
    ex5 : {A : For (◇ ▹ₜ)} → {B : For ◇} → ◇ ⊢ ((((∀∀ A) ⇒ B) ⇒ B) ⇒ (∀∀ ((A ⇒ (B [ πₜ¹ id ]f)) ⇒ (B [ πₜ¹ id ]f))))
    ex5 ◇◇ h t h' = h (λ h'' → h' (h'' t))

  record Kripke : Set₁ where
    field
      World : Set
      _≤_ : World → World → Prop
      ≤refl : {w : World} → w ≤ w
      ≤tran : {w w' w'' : World} → w ≤ w' → w' ≤ w'' → w ≤ w'
      TM : Set
      REL : (n : Nat) → R n → Array TM n → World → Prop
      RELmon : {n : Nat} → {r : R n} → {x : Array TM n} → {w w' : World} → REL n r x w → REL n r x w'
      FUN : (n : Nat) → F n → Array TM n → TM
    infixr 10 _∘_
    Con = World → Set
    Sub : Con → Con → Set
    Sub Δ Γ = (w : World) → Δ w → Γ w
    _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
    α ∘ β = λ w γ → α w (β w γ)
    id : {Γ : Con} → Sub Γ Γ
    id = λ w γ → γ
    record ◇⁰ : Set where
      constructor ◇◇⁰
    ◇ : Con -- The initial object of the category
    ◇ = λ w → ◇⁰
    ε : {Γ : Con} → Sub Γ ◇ -- The morphism from the initial to any object
    ε w Γ = ◇◇⁰
                                                                    
    -- Functor Con → Set called Tm
    Tm : Con → Set
    Tm Γ = (w : World) → (Γ w) → TM
    _[_]t : {Γ Δ : Con} → Tm Γ → Sub Δ Γ → Tm Δ -- The functor's action on morphisms
    t [ σ ]t = λ w → λ γ → t w (σ w γ)
    []t-id : {Γ : Con} → {x : Tm Γ} → x [ id {Γ} ]t ≡ x
    []t-id = refl
    []t-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {t : Tm Γ} → t [ β ∘ α ]t ≡ (t [ β ]t) [ α ]t
    []t-∘ = refl


    _[_]tz : {Γ Δ : Con} → {n : Nat} → Array (Tm Γ) n → Sub Δ Γ → Array (Tm Δ) n
    tz [ σ ]tz = map (λ s → s [ σ ]t) tz
    []tz-∘  : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {n : Nat} → {tz : Array (Tm Γ) n} → tz [ β ∘ α ]tz ≡ tz [ β ]tz [ α ]tz
    []tz-∘ {tz = zero} = refl
    []tz-∘ {α = α} {β = β} {tz = next x tz} = substP (λ tz' → (next ((x [ β ]t) [ α ]t) tz') ≡ (((next x tz) [ β ]tz) [ α ]tz)) (≡sym ([]tz-∘ {α = α} {β = β} {tz = tz})) refl
    []tz-id : {Γ : Con} → {n : Nat} → {tz : Array (Tm Γ) n} → tz [ id ]tz ≡ tz
    []tz-id {tz = zero} = refl
    []tz-id {tz = next x tz} = substP (λ tz' → next x tz' ≡ next x tz) (≡sym ([]tz-id {tz = tz})) refl
    thm : {Γ Δ : Con} → {n : Nat} → {tz : Array (Tm Γ) n} → {σ : Sub Δ Γ} → {w : World} → {δ : Δ w} → map (λ t → t w δ) (tz [ σ ]tz) ≡ map (λ t → t w (σ w δ)) tz
    thm {tz = zero} = refl
    thm {tz = next x tz} {σ} {w} {δ} = substP (λ tz' → (next (x w (σ w δ)) (map (λ t → t w δ) (map (λ s w γ → s w (σ w γ)) tz))) ≡ (next (x w (σ w δ)) tz')) (thm {tz = tz}) refl -- substP (λ tz' → (next (x w (σ w δ)) (map (λ t → t δ) (map (λ s γ → s w (σ w γ)) tz))) ≡ (next (x w (σ w δ)) tz')) (thm {tz = tz}) refl

    
    -- Term extension with functions
    fun : {Γ : Con} → {n : Nat} → F n → Array (Tm Γ) n → Tm Γ
    fun {n = n} f tz = λ w γ → FUN n f (map (λ t → t w γ) tz)
    fun[] : {Γ Δ : Con} → {σ : Sub Δ Γ} → {n : Nat} → {f : F n} → {tz : Array (Tm Γ) n} → (fun f tz) [ σ ]t ≡ fun f (map (λ t → t [ σ ]t) tz)
    fun[] {Γ = Γ} {Δ = Δ} {σ = σ} {n = n} {f = f} {tz = tz} = ≡fun' λ w → ≡fun λ γ → substP ((λ x → (FUN n f) x ≡ (FUN n f) (map (λ t → t w γ) (tz [ σ ]tz)))) (thm {tz = tz}) refl
                                                                                                                                          
    -- Tm⁺
    _▹ₜ : Con → Con
    Γ ▹ₜ = λ w → (Γ w) × TM
    πₜ¹ : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Sub Δ Γ
    πₜ¹ σ = λ w → λ x → proj×₁ (σ w x)
    πₜ² : {Γ Δ : Con} → Sub Δ (Γ ▹ₜ) → Tm Δ
    πₜ² σ = λ w → λ x → proj×₂ (σ w x) 
    _,ₜ_ : {Γ Δ : Con} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹ₜ)
    σ ,ₜ t = λ w → λ x → (σ w x) ,× (t w x)
    πₜ²∘,ₜ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm Δ} → πₜ² (σ ,ₜ t) ≡ t
    πₜ²∘,ₜ {σ = σ} {t} = refl {a = t}
    πₜ¹∘,ₜ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm Δ} → πₜ¹ (σ ,ₜ t) ≡ σ
    πₜ¹∘,ₜ = refl
    ,ₜ∘πₜ : {Γ Δ : Con} → {σ : Sub Δ (Γ ▹ₜ)} → (πₜ¹ σ) ,ₜ (πₜ² σ) ≡ σ
    ,ₜ∘πₜ = refl
    ,ₜ∘ : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{t : Tm Γ} → (σ ,ₜ t) ∘ δ ≡ (σ ∘ δ) ,ₜ (t [ δ ]t)
    ,ₜ∘ = refl
                                                                    
    -- Functor Con → Set called For
    For : Con → Set₁
    For Γ = (w : World) → (Γ w) → Prop
    _[_]f : {Γ Δ : Con} → For Γ → Sub Δ Γ → For Δ -- The functor's action on morphisms
    F [ σ ]f = λ w → λ x → F w (σ w x)
    []f-id : {Γ : Con} → {F : For Γ} → F [ id {Γ} ]f ≡ F
    []f-id = refl
    []f-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {F : For Γ} → F [ β ∘ α ]f ≡ (F [ β ]f) [ α ]f
    []f-∘ = refl
                                                                                                        
    -- Formulas with relation on terms
    rel : {Γ : Con} → {n : Nat} → R n → Array (Tm Γ) n → For Γ
    rel {n = n} r tz = λ w → λ γ → (REL n r) (map (λ t → t w γ) tz) w
    rel[] : {Γ Δ : Con} → {σ : Sub Δ Γ} → {n : Nat} → {r : R n} → {tz : Array (Tm Γ) n} → (rel r tz) [ σ ]f ≡ rel r (map (λ t → t [ σ ]t) tz)
    rel[] {σ = σ} {n = n} {r = r} {tz = tz} = ≡fun' ( λ w →  ≡fun (λ γ → (substP (λ x → (REL n r) x w ≡ (REL n r) (map (λ t → t w γ) (tz [ σ ]tz)) w) thm refl)))
    
                                                                                                                                          
    -- Proofs
    _⊢_ : (Γ : Con) → For Γ → Prop
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
    ,ₚ∘πₚ : {Γ Δ : Con} → {F : For Γ} → {σ : Sub Δ (Γ ▹ₚ F)} → (πₚ¹ σ) ,ₚ (πₚ² σ) ≡ σ
    ,ₚ∘πₚ = refl
    πₚ¹∘,ₚ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {F : For Γ} → {prf : Δ ⊢ (F [ σ ]f)} → πₚ¹ {Γ} {Δ} {F} (σ ,ₚ prf) ≡ σ
    πₚ¹∘,ₚ = refl
    ,ₚ∘ : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{F : For Ξ}{prf : Γ ⊢ (F [ σ ]f)} →
      (_,ₚ_  {F = F} σ prf) ∘ δ ≡ (σ ∘ δ) ,ₚ (substP (λ F → Δ ⊢ F) (≡sym ([]f-∘ {α = δ} {β = σ} {F = F})) (prf [ δ ]p))
    ,ₚ∘ {Γ} {Δ} {Ξ} {σ} {δ} {F} {prf} = refl
    
                                                                                                      
                                                                                                      
    -- Implication
    _⇒_ : {Γ : Con} → For Γ → For Γ → For Γ
    F ⇒ G = λ w → λ γ → (∀ w' → w ≤ w' → (F w γ) → (G w γ))
    []f-⇒ : {Γ Δ : Con} → {F G : For Γ} → {σ : Sub Δ Γ} → (F ⇒ G) [ σ ]f ≡ (F [ σ ]f) ⇒ (G [ σ ]f)
    []f-⇒ = refl
    
    -- Forall
    ∀∀ : {Γ : Con} → For (Γ ▹ₜ) → For Γ
    ∀∀ F = λ w → λ γ → ∀ t → F w (γ ,× t)
    []f-∀∀ : {Γ Δ : Con} → {F : For (Γ ▹ₜ)} → {σ : Sub Δ Γ} → (∀∀ F) [ σ ]f ≡ (∀∀ (F [ (σ ∘ πₜ¹ id) ,ₜ πₜ² id ]f))
    []f-∀∀ = refl
                                                                                                                           
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


    tod : FFOL F R
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
      ; ,ₜ∘ = λ {Γ} {Δ} {Ξ} {σ} {δ} {t} → ,ₜ∘ {Γ} {Δ} {Ξ} {σ} {δ} {t}
      ; For = For
      ; _[_]f = _[_]f
      ; []f-id = []f-id
      ; []f-∘ = λ {Γ} {Δ} {Ξ} {α} {β} {F} → []f-∘ {Γ} {Δ} {Ξ} {α} {β} {F}
      ; _⊢_ = _⊢_
      ; _[_]p = _[_]p
      ; _▹ₚ_ = _▹ₚ_
      ; πₚ¹ = πₚ¹
      ; πₚ² = πₚ²
      ; _,ₚ_ = _,ₚ_
      ; ,ₚ∘πₚ = ,ₚ∘πₚ
      ; πₚ¹∘,ₚ = λ {Γ} {Δ} {F} {σ} {p} → πₚ¹∘,ₚ {Γ} {Δ} {F} {σ} {p}
      ; ,ₚ∘ = λ {Γ} {Δ} {Ξ} {σ} {δ} {F} {prf} → ,ₚ∘ {Γ} {Δ} {Ξ} {σ} {δ} {F} {prf}
      ; _⇒_ = _⇒_
      ; []f-⇒ = λ {Γ} {F} {G} {σ} → []f-⇒ {Γ} {F} {G} {σ}
      ; ∀∀ = ∀∀
      ; []f-∀∀ = λ {Γ} {Δ} {F} {σ} → []f-∀∀ {Γ} {Δ} {F} {σ}
      ; lam = lam
      ; app = app
      ; ∀i = ∀i
      ; ∀e = ∀e
      ; fun = fun
      ; fun[] = fun[]
      ; rel = rel
      ; rel[] = rel[]
      }


  -- Completeness proof

  -- We first build our universal Kripke model
  
  
