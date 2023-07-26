{-# OPTIONS --prop --rewriting #-}

open import PropUtil
 
module FFOL where

  open import Agda.Primitive
  open import ListUtil

  variable
    ℓ¹ ℓ² ℓ³ ℓ⁴ ℓ⁵ : Level
    
  record FFOL : Set (lsuc (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓ⁴ ⊔ ℓ⁵)) where
    infixr 10 _∘_
    infixr 5 _⊢_
    field
      
      -- We first make the base category with its final object
      Con : Set ℓ¹
      Sub : Con → Con → Set ℓ⁵ -- It makes a category
      _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
      ∘-ass : {Γ Δ Ξ Ψ : Con}{α : Sub Γ Δ}{β : Sub Δ Ξ}{γ : Sub Ξ Ψ} → (γ ∘ β) ∘ α ≡ γ ∘ (β ∘ α)
      id : {Γ : Con} → Sub Γ Γ
      idl : {Γ Δ : Con} {σ : Sub Γ Δ} →  (id {Δ}) ∘ σ ≡ σ
      idr : {Γ Δ : Con} {σ : Sub Γ Δ} →  σ ∘ (id {Γ}) ≡ σ
      ◇ : Con -- The terminal object of the category
      ε : {Γ : Con} → Sub Γ ◇ -- The morphism from any object to the terminal
      ε-u : {Γ : Con} → {σ : Sub Γ ◇} → σ ≡ ε {Γ}

      -- Functor Con → Set called Tm
      Tm : Con → Set ℓ²
      _[_]t : {Γ Δ : Con} → Tm Γ → Sub Δ Γ → Tm Δ -- The functor's action on morphisms
      []t-id : {Γ : Con} → {x : Tm Γ} → x [ id {Γ} ]t ≡ x
      []t-∘ : {Γ Δ Ξ : Con} → {α : Sub Ξ Δ} → {β : Sub Δ Γ} → {t : Tm Γ} → t [ β ∘ α ]t ≡ (t [ β ]t) [ α ]t

      -- Tm : Set⁺
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

      -- Functor Con × For → Prop called Pf or ⊢
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
      ,ₚ∘πₚ : {Γ Δ : Con} → {F : For Γ} → {σ : Sub Δ (Γ ▹ₚ F)} → (πₚ¹ σ) ,ₚ (πₚ² σ) ≡ σ
      πₚ¹∘,ₚ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {F : For Γ} → {prf : Δ ⊢ (F [ σ ]f)} → πₚ¹ (σ ,ₚ prf) ≡ σ
      -- Equality below is useless because Γ ⊢ F is in Prop
      -- πₚ²∘,ₚ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {F : For Γ} → {prf : Δ ⊢ (F [ σ ]f)} → πₚ² (σ ,ₚ prf) ≡ prf
      ,ₚ∘ : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{F : For Ξ}{prf : Γ ⊢ (F [ σ ]f)} → (σ ,ₚ prf) ∘ δ ≡ (σ ∘ δ) ,ₚ (substP (λ F → Δ ⊢ F) (≡sym []f-∘) (prf [ δ ]p))

      
      {-- FORMULAE CONSTRUCTORS --}
      -- Formulas with relation on terms
      R : {Γ : Con} → (t u : Tm Γ) → For Γ
      R[] : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t u : Tm Γ} → (R t u) [ σ ]f ≡ R (t [ σ ]t) (u [ σ ]t)

      -- Implication
      _⇒_ : {Γ : Con} → For Γ → For Γ → For Γ
      []f-⇒ : {Γ Δ : Con} → {F G : For Γ} → {σ : Sub Δ Γ} → (F ⇒ G) [ σ ]f ≡ (F [ σ ]f) ⇒ (G [ σ ]f)

      -- Forall
      ∀∀ : {Γ : Con} → For (Γ ▹ₜ) → For Γ
      []f-∀∀ : {Γ Δ : Con} → {F : For (Γ ▹ₜ)} → {σ : Sub Δ Γ} → (∀∀ F) [ σ ]f ≡ (∀∀ (F [ (σ ∘ πₜ¹ id) ,ₜ πₜ² id ]f))

      {-- PROOFS CONSTRUCTORS --}
      -- Again, we don't have to write the _[_]p equalities as Proofs are in Prop
      
      -- Lam & App
      lam : {Γ : Con} → {F : For Γ} → {G : For Γ} → (Γ ▹ₚ F) ⊢ (G [ πₚ¹ id ]f) → Γ ⊢ (F ⇒ G)
      app : {Γ : Con} → {F G : For Γ} → Γ ⊢ (F ⇒ G) → Γ ⊢ F → Γ ⊢ G

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

  record Mapping (S : FFOL {ℓ¹} {ℓ²} {ℓ³} {ℓ⁴} {ℓ⁵}) (D : FFOL {ℓ¹} {ℓ²} {ℓ³} {ℓ⁴} {ℓ⁵}) : Set (lsuc (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓ⁴ ⊔ ℓ⁵)) where
    field
      
      -- We first make the base category with its final object
      mCon : (FFOL.Con S) → (FFOL.Con D)
      mSub : {Δ : (FFOL.Con S)}{Γ : (FFOL.Con S)} → (FFOL.Sub S Δ Γ) → (FFOL.Sub D (mCon Δ) (mCon Γ))
      mTm : {Γ : (FFOL.Con S)} → (FFOL.Tm S Γ) → (FFOL.Tm D (mCon Γ))
      mFor : {Γ : (FFOL.Con S)} → (FFOL.For S Γ) → (FFOL.For D (mCon Γ))
      m⊢ : {Γ : (FFOL.Con S)} {A : FFOL.For S Γ} → FFOL._⊢_ S Γ A → FFOL._⊢_ D (mCon Γ) (mFor A)


  record Morphism (S : FFOL {ℓ¹} {ℓ²} {ℓ³} {ℓ⁴} {ℓ⁵}) (D : FFOL {ℓ¹} {ℓ²} {ℓ³} {ℓ⁴} {ℓ⁵}) : Set (lsuc (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓ⁴ ⊔ ℓ⁵)) where
    field m : Mapping S D
    mCon = Mapping.mCon m
    mSub = Mapping.mSub m
    mTm  = Mapping.mTm  m
    mFor = Mapping.mFor m
    m⊢   = Mapping.m⊢ m
    field
      e∘ : {Γ Δ Ξ : FFOL.Con S}{δ : FFOL.Sub S Δ Ξ}{σ : FFOL.Sub S Γ Δ} → mSub (FFOL._∘_ S δ σ) ≡ FFOL._∘_ D (mSub δ) (mSub σ)
      eid : {Γ : FFOL.Con S} → mSub (FFOL.id S {Γ}) ≡ FFOL.id D {mCon Γ}
      e◇ : mCon (FFOL.◇ S) ≡ FFOL.◇ D
      eε : {Γ : FFOL.Con S} → mSub (FFOL.ε S {Γ}) ≡ subst (FFOL.Sub D (mCon Γ)) (≡sym e◇) (FFOL.ε D {mCon Γ})
      e[]t : {Γ Δ : FFOL.Con S}{t : FFOL.Tm S Γ}{σ : FFOL.Sub S Δ Γ} → mTm (FFOL._[_]t S t σ) ≡ FFOL._[_]t D (mTm t) (mSub σ)
      e▹ₜ : {Γ : FFOL.Con S} → mCon (FFOL._▹ₜ S Γ) ≡ FFOL._▹ₜ D (mCon Γ)
      eπₜ¹ : {Γ Δ : FFOL.Con S}{σ : FFOL.Sub S Δ (FFOL._▹ₜ S Γ)} → mSub (FFOL.πₜ¹ S σ) ≡ FFOL.πₜ¹ D (subst (FFOL.Sub D (mCon Δ)) e▹ₜ (mSub σ))
      eπₜ² : {Γ Δ : FFOL.Con S}{σ : FFOL.Sub S Δ (FFOL._▹ₜ S Γ)} → mTm (FFOL.πₜ² S σ) ≡ FFOL.πₜ² D (subst (FFOL.Sub D (mCon Δ)) e▹ₜ (mSub σ))
      e,ₜ : {Γ Δ : FFOL.Con S}{σ : FFOL.Sub S Δ Γ}{t : FFOL.Tm S Δ} → mSub (FFOL._,ₜ_ S σ t) ≡ subst (FFOL.Sub D (mCon Δ)) (≡sym e▹ₜ) (FFOL._,ₜ_ D (mSub σ) (mTm t))
      e[]f : {Γ Δ : FFOL.Con S}{A : FFOL.For S Γ}{σ : FFOL.Sub S Δ Γ} → mFor (FFOL._[_]f S A σ) ≡ FFOL._[_]f D (mFor A) (mSub σ)
      -- Proofs are in prop, so no equation needed
      --[]p : {Γ Δ : FFOL.Con S}{A : FFOL.For S Γ}{pf : FFOL._⊢_ S Γ A}{σ : FFOL.Sub S Δ Γ} → m⊢ (FFOL._[_]p S pf σ) ≡ FFOL._[_]p D (m⊢ pf) (mSub σ)
      e▹ₚ : {Γ : FFOL.Con S}{A : FFOL.For S Γ} → mCon (FFOL._▹ₚ_ S Γ A) ≡ FFOL._▹ₚ_ D (mCon Γ) (mFor A)
      eπₚ¹ : {Γ Δ : FFOL.Con S}{A : FFOL.For S Γ}{σ : FFOL.Sub S Δ (FFOL._▹ₚ_ S Γ A)} → mSub (FFOL.πₚ¹ S σ) ≡ FFOL.πₚ¹ D (subst (FFOL.Sub D (mCon Δ)) e▹ₚ (mSub σ))
      --πₚ² : {Γ Δ : FFOL.Con S}{A : FFOL.For S Γ}{σ : FFOL.Sub S Δ (FFOL._▹ₚ_ S Γ A)} → m⊢ (FFOL.πₚ² S σ) ≡ FFOL.πₚ¹ D (subst (FFOL.Sub D (mCon Δ)) ▹ₚ (mSub σ))
      e,ₚ : {Γ Δ : FFOL.Con S}{A : FFOL.For S Γ}{σ : FFOL.Sub S Δ Γ}{pf : FFOL._⊢_ S Δ (FFOL._[_]f S A σ)}
        → mSub (FFOL._,ₚ_ S σ pf) ≡ subst (FFOL.Sub D (mCon Δ)) (≡sym e▹ₚ) (FFOL._,ₚ_ D (mSub σ) (substP (FFOL._⊢_ D (mCon Δ)) e[]f (m⊢ pf)))
      eR : {Γ : FFOL.Con S}{t u : FFOL.Tm S Γ} → mFor (FFOL.R S t u) ≡ FFOL.R D (mTm t) (mTm u)
      e⇒ : {Γ : FFOL.Con S}{A B : FFOL.For S Γ} → mFor (FFOL._⇒_ S A B) ≡ FFOL._⇒_ D (mFor A) (mFor B)
      e∀∀ : {Γ : FFOL.Con S}{A : FFOL.For S (FFOL._▹ₜ S Γ)} → mFor (FFOL.∀∀ S A) ≡ FFOL.∀∀ D (subst (FFOL.For D) e▹ₜ (mFor A))
      -- No equation needed for lam, app, ∀i, ∀e as their output are in prop

  record Tarski : Set₁ where
    field
      TM : Set
      REL : TM → TM → Prop
    infixr 10 _∘_
    Con = Set
    Sub : Con → Con → Set
    Sub Γ Δ = (Γ → Δ) -- It makes a posetal category
    _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
    f ∘ g = λ x → f (g x)
    id : {Γ : Con} → Sub Γ Γ
    id = λ x → x
    ε : {Γ : Con} → Sub Γ ⊤ₛ -- The morphism from the initial to any object
    ε Γ = ttₛ
    ε-u : {Γ : Con} → {σ : Sub Γ ⊤ₛ} → σ ≡ ε {Γ}
    ε-u = refl

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

    R : {Γ : Con} → Tm Γ → Tm Γ → For Γ
    R t u = λ γ → REL (t γ) (u γ)
    R[] : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t u : Tm Γ} → (R t u) [ σ ]f ≡ R (t [ σ ]t) (u [ σ ]t)
    R[] {σ = σ} = cong₂ R refl refl

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

    tod : FFOL
    tod = record
            { Con = Con
            ; Sub = Sub
            ; _∘_ = _∘_
            ; ∘-ass = refl
            ; id = id
            ; idl = refl
            ; idr = refl
            ; ◇ = ⊤ₛ
            ; ε = ε
            ; ε-u = refl
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
            ; R = R
            ; R[] = λ {Γ} {Δ} {σ} {t} {u} →  R[] {Γ} {Δ} {σ} {t} {u}
            }


    -- (∀ x ∀ y . A(x,y)) ⇒ ∀ y ∀ x . A(y,x)
    -- both sides are ∀ ∀ A (0,1)
    ex1 : {A : For (⊤ₛ ▹ₜ ▹ₜ)} → ⊤ₛ ⊢ ((∀∀ (∀∀ A)) ⇒ (∀∀ (∀∀ A)))
    ex1 _ hyp = hyp
    -- (A ⇒ ∀ x . B(x)) ⇒ ∀ x . A ⇒ B(x)
    ex2 : {A : For ⊤ₛ} → {B : For (⊤ₛ ▹ₜ)} → ⊤ₛ ⊢ ((A ⇒ (∀∀ B)) ⇒ (∀∀ ((A [ πₜ¹ id ]f) ⇒ B)))
    ex2 _ h t h' = h h' t
    -- ∀ x y . A(x,y) ⇒ ∀ x . A(x,x)
    -- For simplicity, I swiched positions of parameters of A (somehow...)
    ex3 : {A : For (⊤ₛ ▹ₜ ▹ₜ)} → ⊤ₛ ⊢ ((∀∀ (∀∀ A)) ⇒ (∀∀ (A [ id ,ₜ (πₜ² id) ]f)))
    ex3 _ h t = h t t
    -- ∀ x . A (x) ⇒ ∀ x y . A(x)
    ex4 : {A : For (⊤ₛ ▹ₜ)} → ⊤ₛ ⊢ ((∀∀ A) ⇒ (∀∀ (∀∀ (A [ ε ,ₜ (πₜ² (πₜ¹ id)) ]f))))
    ex4 {A} ◇◇ x t t' = x t
    -- (((∀ x . A (x)) ⇒ B)⇒ B) ⇒ ∀ x . ((A (x) ⇒ B) ⇒ B)
    ex5 : {A : For (⊤ₛ ▹ₜ)} → {B : For ⊤ₛ} → ⊤ₛ ⊢ ((((∀∀ A) ⇒ B) ⇒ B) ⇒ (∀∀ ((A ⇒ (B [ πₜ¹ id ]f)) ⇒ (B [ πₜ¹ id ]f))))
    ex5 ◇◇ h t h' = h (λ h'' → h' (h'' t))
