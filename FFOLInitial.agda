{-# OPTIONS --prop #-}

open import PropUtil

module FFOLInitial where

  open import FinitaryFirstOrderLogic
  open import Agda.Primitive
  open import ListUtil

  -- First definition of terms and term contexts --
  data Cont : Set₁ where
    ◇t : Cont
    _▹t⁰ : Cont → Cont
  variable
    Γₜ Δₜ Ξₜ : Cont
  data TmVar : Cont → Set₁ where
    tvzero : TmVar (Γₜ ▹t⁰)
    tvnext : TmVar Γₜ → TmVar (Γₜ ▹t⁰)
    
  data Tm : Cont → Set₁ where
    var : TmVar Γₜ → Tm Γₜ
    
  -- Now we can define formulæ
  data For : Cont → Set₁ where
    r : Tm Γₜ → Tm Γₜ → For Γₜ
    _⇒_ : For Γₜ → For Γₜ → For Γₜ
    ∀∀  : For (Γₜ ▹t⁰) → For Γₜ

  -- Then we define term substitutions, and the application of them on terms and formulæ
  data Subt : Cont → Cont → Set₁ where
    εₜ : Subt Γₜ ◇t
    wk▹t : Subt Δₜ Γₜ → Tm Δₜ → Subt Δₜ (Γₜ ▹t⁰)
    
  -- We subst on terms
  _[_]t : Tm Γₜ → Subt Δₜ Γₜ → Tm Δₜ
  var tvzero [ wk▹t σ t ]t = t
  var (tvnext tv) [ wk▹t σ t ]t = var tv [ σ ]t
  
  -- We define liftings on term variables
  -- A term of n variables is a term of n+1 variables
  -- Same for a term array
  liftt : Tm Γₜ → Tm (Γₜ ▹t⁰)
  
  liftt (var tv) = var (tvnext tv)
  
  -- From a substition into n variables, we get a substitution into n+1 variables which don't use the last one
  llift : Subt Δₜ Γₜ → Subt (Δₜ ▹t⁰) Γₜ
  llift εₜ = εₜ
  llift (wk▹t σ t) = wk▹t (llift σ) (liftt t)
  llift-liftt : {tv : TmVar Γₜ} → {σ : Subt Δₜ Γₜ} → liftt (var tv [ σ ]t) ≡ var tv [ llift σ ]t
  llift-liftt {tv = tvzero} {σ = wk▹t σ x} = refl
  llift-liftt {tv = tvnext tv} {σ = wk▹t σ x} = llift-liftt {tv = tv} {σ = σ}
  
  -- From a substitution into n variables, we construct a substitution from n+1 variables to n+1 variables which maps it to itself
  -- i.e. 0 -> 0 and for all i ->(old) σ(i) we get i+1 -> σ(i)+1
  lift : Subt Δₜ Γₜ → Subt (Δₜ ▹t⁰) (Γₜ ▹t⁰)
  lift σ = wk▹t (llift σ) (var tvzero)

  
  -- We subst on formulæ
  _[_]f : For Γₜ → Subt Δₜ Γₜ → For Δₜ
  (r t u) [ σ ]f = r (t [ σ ]t) (u [ σ ]t)
  (A ⇒ B) [ σ ]f = (A [ σ ]f) ⇒ (B [ σ ]f)
  (∀∀ A) [ σ ]f = ∀∀ (A [ lift σ ]f)
                                 
  -- We now can define identity on term substitutions       
  idₜ : Subt Γₜ Γₜ
  idₜ {◇t} = εₜ
  idₜ {Γₜ ▹t⁰} = lift (idₜ {Γₜ})

  _∘ₜ_ : Subt Δₜ Γₜ → Subt Ξₜ Δₜ → Subt Ξₜ Γₜ
  εₜ ∘ₜ β = εₜ
  wk▹t α x ∘ₜ β = wk▹t (α ∘ₜ β) (x [ β ]t)


  -- We have the access functions from the algebra, in restricted versions
  πₜ¹ : Subt Δₜ (Γₜ ▹t⁰) → Subt Δₜ Γₜ
  πₜ¹ (wk▹t σₜ t) = σₜ
  πₜ² : Subt Δₜ (Γₜ ▹t⁰) → Tm Δₜ
  πₜ² (wk▹t σₜ t) = t
  _,ₜ_ : Subt Δₜ Γₜ → Tm Δₜ → Subt Δₜ (Γₜ ▹t⁰)
  σₜ ,ₜ t = wk▹t σₜ t
  
  -- And their equalities (the fact that there are reciprocical)
  πₜ²∘,ₜ : {σₜ : Subt Δₜ Γₜ} → {t : Tm Δₜ} → πₜ² (σₜ ,ₜ t) ≡ t
  πₜ²∘,ₜ = refl
  πₜ¹∘,ₜ : {σₜ : Subt Δₜ Γₜ} → {t : Tm Δₜ} → πₜ¹ (σₜ ,ₜ t) ≡ σₜ
  πₜ¹∘,ₜ = refl
  ,ₜ∘πₜ : {σₜ : Subt Δₜ (Γₜ ▹t⁰)} → (πₜ¹ σₜ) ,ₜ (πₜ² σₜ) ≡ σₜ
  ,ₜ∘πₜ {σₜ = wk▹t σₜ t} = refl

  -- We can also prove the substitution equalities
  []t-id : {t : Tm Γₜ} → t [ idₜ {Γₜ} ]t ≡ t
  []t-id {Γₜ ▹t⁰} {var tvzero} = refl
  []t-id {Γₜ ▹t⁰} {var (tvnext tv)} = substP (λ t → t ≡ var (tvnext tv)) (llift-liftt {tv = tv} {σ = idₜ}) (substP (λ t → liftt t ≡ var (tvnext tv)) (≡sym ([]t-id {t = var tv})) refl)
  []t-∘ : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → {t : Tm Γₜ} → t [ β ∘ₜ α ]t ≡ (t [ β ]t) [ α ]t
  []t-∘ {α = α} {β = wk▹t β t} {t = var tvzero} = refl
  []t-∘ {α = α} {β = wk▹t β t} {t = var (tvnext tv)} = []t-∘ {t = var tv}
  []f-id : {F : For Γₜ} → F [ idₜ {Γₜ} ]f ≡ F
  []f-id {F = r t u} = cong₂ r []t-id []t-id
  []f-id {F = F ⇒ G} = cong₂ _⇒_ []f-id []f-id
  []f-id {F = ∀∀ F} = cong ∀∀ []f-id
  llift-∘ : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → llift (β ∘ₜ α) ≡ (llift β ∘ₜ lift α)
  liftt[] : {α : Subt Δₜ Γₜ} → {t : Tm Γₜ} → liftt (t [ α ]t) ≡ (liftt t [ lift α ]t)
  llift-∘ {β = εₜ} = refl
  llift-∘ {β = wk▹t β t} = cong₂ wk▹t llift-∘ (liftt[] {t = t})
  liftt[] {α = wk▹t α t} {var tvzero} = refl
  liftt[] {α = wk▹t α t} {var (tvnext tv)} = liftt[] {t = var tv}
  lift-∘ : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → lift (β ∘ₜ α) ≡ (lift β) ∘ₜ (lift α)
  lift-∘ {α = α} {β = εₜ} = refl
  lift-∘ {α = α} {β = wk▹t β t} = cong₂ wk▹t (cong₂ wk▹t llift-∘ (liftt[] {t = t})) refl
  []f-∘ : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → {F : For Γₜ} → F [ β ∘ₜ α ]f ≡ (F [ β ]f) [ α ]f
  []f-∘ {α = α} {β = β} {F = r t u} = cong₂ r ([]t-∘ {α = α} {β = β} {t = t}) ([]t-∘ {α = α} {β = β} {t = u})
  []f-∘ {F = F ⇒ G} = cong₂ _⇒_ []f-∘ []f-∘
  []f-∘ {F = ∀∀ F} = cong ∀∀ (≡tran (cong (λ σ → F [ σ ]f) lift-∘) []f-∘)
  R[] : {σ : Subt Δₜ Γₜ} → {t u : Tm Γₜ} → (r t u) [ σ ]f ≡ r (t [ σ ]t) (u [ σ ]t)
  R[] = refl


  data Conp : Cont → Set₁ -- pu tit in Prop
  variable
    Γₚ : Conp Γₜ
    Δₚ : Conp Δₜ
    Ξₚ : Conp Ξₜ
  
  data Conp where
    ◇p : Conp Γₜ
    _▹p⁰_ : Conp Γₜ → For Γₜ → Conp Γₜ
    
  record Con : Set₁ where
    constructor con
    field
      t : Cont
      p : Conp t

  ◇ : Con
  ◇ = con ◇t ◇p

  
  _▹p_ : (Γ : Con) → For (Con.t Γ) → Con
  Γ ▹p A = con (Con.t Γ) (Con.p Γ ▹p⁰ A)
  
  variable
    Γ Δ Ξ : Con
    
                                     
                                              
  -- We can add term, that will not be used in the formulæ already present
  -- (that's why we use llift)
  _▹tp : Conp Γₜ → Conp (Γₜ ▹t⁰)
  ◇p ▹tp = ◇p
  (Γₚ ▹p⁰ A) ▹tp = (Γₚ ▹tp) ▹p⁰ (A [ llift idₜ ]f)
  
  _▹t : Con → Con
  Γ ▹t = con ((Con.t Γ) ▹t⁰) (Con.p Γ ▹tp)
                                        
  data PfVar : (Γ : Con) → For (Con.t Γ) → Set₁ where
    pvzero : {A : For (Con.t Γ)} → PfVar (Γ ▹p A) A
    pvnext : {A B : For (Con.t Γ)} → PfVar Γ A → PfVar (Γ ▹p B) A
                                                                
  data Pf : (Γ : Con) → For (Con.t Γ) → Prop₁ where
    var : {A : For (Con.t Γ)} → PfVar Γ A → Pf Γ A
    app : {A B : For (Con.t Γ)} → Pf Γ (A ⇒ B) → Pf Γ A → Pf Γ B
    lam : {A B : For (Con.t Γ)} → Pf (Γ ▹p A) B → Pf Γ (A ⇒ B)
    p∀∀e : {A : For ((Con.t Γ) ▹t⁰)} → {t : Tm (Con.t Γ)} → Pf Γ (∀∀ A) → Pf Γ (A [ wk▹t idₜ t ]f)
    p∀∀i : {A : For (Con.t (Γ ▹t))} → Pf (Γ ▹t) A → Pf Γ (∀∀ A)

    
  data Sub : Con → Con → Set₁
  subt : Sub Δ Γ → Subt (Con.t Δ) (Con.t Γ)
  data Sub where
    εₚ : Subt (Con.t Δ) (Con.t Γ) → Sub Δ (con (Con.t Γ) ◇p) -- Γₜ → Δₜ ≡≡> (Γₜ,◇p) → (Δₜ,Δₚ)
    -- If i tell you by what you should replace a missing proof of A, then you can
    -- prove anything that uses a proof of A
    _,ₚ_ : {A : For (Con.t Γ)} → (σ : Sub Δ Γ) →  Pf Δ (A [ subt σ ]f) → Sub Δ (Γ ▹p A)
  subt (εₚ σₜ) = σₜ
  subt (σ ,ₚ pf) = subt σ
  
  πₚ¹ : {Γ Δ : Con} → {F : For (Con.t Γ)} → Sub Δ (Γ ▹p F) → Sub Δ Γ
  πₚ¹ (σ ,ₚ pf) = σ
  πₚ² : {Γ Δ : Con} → {F : For (Con.t Γ)} → (σ : Sub Δ (Γ ▹p F)) → Pf Δ (F [ subt (πₚ¹ σ) ]f)
  πₚ² (σ ,ₚ pf) = pf

  -- An order on contexts, where we can only change positions
  infixr 5 _∈ₚ_ _∈ₚ*_
  data _∈ₚ_ : For Γₜ → Conp Γₜ → Set₁ where
    zero∈ₚ : {A : For Γₜ} → A ∈ₚ Γₚ ▹p⁰ A
    next∈ₚ : {A B : For Γₜ} → A ∈ₚ Γₚ → A ∈ₚ Γₚ ▹p⁰ B
  data _∈ₚ*_ : Conp Γₜ → Conp Γₜ → Set₁ where
    zero∈ₚ* : ◇p ∈ₚ* Γₚ
    next∈ₚ* : {A : For Γₜ} → A ∈ₚ Δₚ → Γₚ ∈ₚ* Δₚ → (Γₚ ▹p⁰ A) ∈ₚ* Δₚ
  -- Allows to grow ∈ₚ* to the right
  right∈ₚ* :{A : For Δₜ} → Γₚ ∈ₚ* Δₚ → Γₚ ∈ₚ* (Δₚ ▹p⁰ A)
  right∈ₚ* zero∈ₚ* = zero∈ₚ*
  right∈ₚ* (next∈ₚ* x h) = next∈ₚ* (next∈ₚ x) (right∈ₚ* h)
  both∈ₚ* : {A : For Γₜ} → Γₚ ∈ₚ* Δₚ → (Γₚ ▹p⁰ A) ∈ₚ* (Δₚ ▹p⁰ A)
  both∈ₚ* zero∈ₚ* = next∈ₚ* zero∈ₚ zero∈ₚ*
  both∈ₚ* (next∈ₚ* x h) = next∈ₚ* zero∈ₚ (next∈ₚ* (next∈ₚ x) (right∈ₚ* h))
  refl∈ₚ* : Γₚ ∈ₚ* Γₚ
  refl∈ₚ* {Γₚ = ◇p} = zero∈ₚ*
  refl∈ₚ* {Γₚ = Γₚ ▹p⁰ x} = both∈ₚ* refl∈ₚ*

  ∈ₚ▹tp : {A : For Δₜ} → A ∈ₚ Δₚ → A [ llift idₜ ]f ∈ₚ (Δₚ ▹tp)
  ∈ₚ▹tp zero∈ₚ = zero∈ₚ
  ∈ₚ▹tp (next∈ₚ x) = next∈ₚ (∈ₚ▹tp x)
  ∈ₚ*▹tp : Γₚ ∈ₚ* Δₚ → (Γₚ ▹tp) ∈ₚ* (Δₚ ▹tp)
  ∈ₚ*▹tp zero∈ₚ* = zero∈ₚ*
  ∈ₚ*▹tp (next∈ₚ* x s) = next∈ₚ* (∈ₚ▹tp x) (∈ₚ*▹tp s)

  -- Todo fuse both concepts (remove ∈ₚ)
  var→∈ₚ : {A : For Γₜ} → (x : PfVar (con Γₜ Γₚ) A) → A ∈ₚ Γₚ
  ∈ₚ→var : {A : For Γₜ} → A ∈ₚ Γₚ → PfVar (con Γₜ Γₚ) A
  var→∈ₚ pvzero = zero∈ₚ
  var→∈ₚ (pvnext x) = next∈ₚ (var→∈ₚ x)
  ∈ₚ→var zero∈ₚ = pvzero
  ∈ₚ→var (next∈ₚ s) = pvnext (∈ₚ→var s)
  mon∈ₚ∈ₚ* : {A : For Γₜ} → A ∈ₚ Γₚ → Γₚ ∈ₚ* Δₚ → A ∈ₚ Δₚ
  mon∈ₚ∈ₚ* zero∈ₚ (next∈ₚ* x x₁) = x
  mon∈ₚ∈ₚ* (next∈ₚ s) (next∈ₚ* x x₁) = mon∈ₚ∈ₚ* s x₁
  liftpₚ : {Δₚ Ξₚ : Conp Δₜ} {A : For Δₜ}  → Δₚ ∈ₚ* Ξₚ → Pf (con Δₜ Δₚ) A → Pf (con Δₜ Ξₚ) A
  liftpₚ s (var x) = var (∈ₚ→var (mon∈ₚ∈ₚ* (var→∈ₚ x) s))
  liftpₚ s (app pf pf₁) = app (liftpₚ s pf) (liftpₚ s pf₁)
  liftpₚ s (lam pf) = lam (liftpₚ (both∈ₚ* s) pf)
  liftpₚ s (p∀∀e pf) = p∀∀e (liftpₚ s pf)
  liftpₚ s (p∀∀i pf) = p∀∀i (liftpₚ (∈ₚ*▹tp s) pf)
  lliftₚ : {Δₚ Ξₚ : Conp Δₜ} →  Δₚ ∈ₚ* Ξₚ → Sub (con Δₜ Δₚ) Γ → Sub (con Δₜ Ξₚ) Γ
  lliftₚ≡subt : {σ : Sub (con Δₜ Δₚ) Γ} → {s : Δₚ ∈ₚ* Ξₚ} → subt (lliftₚ s σ) ≡ subt σ
  lliftₚ≡subt {σ = εₚ x} = {!refl!}
  lliftₚ≡subt {σ = σ ,ₚ x} = {!lliftₚ≡subt {σ = σ}!}
  lliftₚ {Γ = Γ} _ (εₚ σₜ) = εₚ {Γ = Γ} σₜ
  lliftₚ {Δₜ = Δₜ} {Δₚ = Δₚ} s (_,ₚ_ {A = A} σ pf) = lliftₚ s σ ,ₚ liftpₚ s (substP (λ σₜ → Pf (con Δₜ Δₚ) (A [ σₜ ]f)) (≡sym (lliftₚ≡subt {σ = σ} {s = s})) pf)
  
  llift' : {A : For (Con.t Δ)} → Sub Δ Γ → Sub (Δ ▹p A) Γ
  llift' s = lliftₚ (right∈ₚ* refl∈ₚ*) s

  _[_]p : {Γ Δ : Con} → {F : For (Con.t Γ)} → Pf Γ F → (σ : Sub Δ Γ) → Pf Δ (F [ subt σ ]f) -- The functor's action on morphisms
  var pvzero [ σ ,ₚ pf ]p = pf
  var (pvnext pv) [ σ ,ₚ pf ]p = var pv [ σ ]p
  app pf pf₁ [ σ ]p = app (pf [ σ ]p) (pf₁ [ σ ]p)
  lam pf [ σ ]p = lam (pf [ llift' {!σ!} ,ₚ var pvzero ]p)
  p∀∀e pf [ σ ]p = {!p∀∀e!}
  p∀∀i pf [ σ ]p = p∀∀i {!!}
  _∘_ : Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
  εₚ σₜ ∘ β = {!!}
  (α ,ₚ pf) ∘ β = {!!}
  
  -- Equalities below are useless because Γ ⊢ F is in Prop
  ,ₚ∘πₚ : {Γ Δ : Con} → {F : For (Con.t Γ)} → {σ : Sub Δ (Γ ▹p F)} → (πₚ¹ σ) ,ₚ (πₚ² σ) ≡ σ
  πₚ¹∘,ₚ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {F : For (Con.t Γ)} → {prf : Pf Δ (F [ subt σ ]f)} → πₚ¹ (σ ,ₚ prf) ≡ σ
  -- πₚ²∘,ₚ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {F : For Γ} → {prf : Δ ⊢ (F [ σ ]f)} → πₚ² (σ ,ₚ prf) ≡ prf
  ,ₚ∘ : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{F : For (Con.t Ξ)}{prf : Pf Γ (F [ subt σ ]f)} → (σ ,ₚ prf) ∘ δ ≡ (σ ∘ δ) ,ₚ (substP (λ F → Pf Δ F) (≡sym {!!}) (prf [ δ ]p))




  -- lifts
  --liftpt : Pf Δ (A [ subt σ ]f) → Pf Δ ((A [ llift idₜ ]f) [ subt (σ ,ₜ t) ]f)
  {-
  -- The functions made for accessing the terms of Sub, needed for the algebra
  πₜ¹ : {Γ Δ : Con} → Sub Δ (Γ ▹t) → Sub Δ Γ
  πₜ¹ σ = {!!}
  πₜ² : {Γ Δ : Con} → Sub Δ (Γ ▹t) → Tm (Con.t Δ)
  πₜ² σ = {!!}
  _,ₜ_ : {Γ Δ : Con} → Sub Δ Γ → Tm (Con.t Δ) → Sub Δ (Γ ▹t)
  llift∘,ₜ : {σ : Sub Δ Γ} → {A : For (Con.t Γ)} → {t : Tm (Con.t Δ)} → (A [ llift idₜ ]f) [ subt (σ ,ₜ t) ]f ≡ A [ subt σ ]f
  llift∘,ₜ {A = rel x x₁} = {!!}
  llift∘,ₜ {A = A ⇒ A₁} = {!!}
  llift∘,ₜ {A = ∀∀ A} = {!substrefl!}
  (εₚ σₜ) ,ₜ t = εₚ (wk▹t σₜ t)
  _,ₜ_ {Γ = ΓpA} {Δ = Δ} (wk▹p σ pf) t = wk▹p (σ ,ₜ t) (substP (λ a → Pf Δ a) llift∘,ₜ {!pf!})
  πₚ¹ : {A : Con.t Γ} → Sub Δ (Γ ▹p A) → Sub Δ Γ
  πₚ¹ Γₚ (wk▹p Γₚ' σ pf) = σ
  πₚ² : {A : Con.t Γ} → (σ : Sub Δ (Γ ▹p A)) → Pf Δ (A [ subt (πₚ¹ (Con.p Γ) σ) ]f)
  πₚ² Γₚ (wk▹p Γₚ' σ pf) = pf
  _,ₚ_ : {A : Con.t Γ} → (σ : Sub Δ Γ) → Pf Δ (A [ subt σ ]f) → Sub Δ (Γ ▹p A)
  _,ₚ_ = wk▹p
  -}
  

  {-
  -- We subst on proofs
  _,ₚ_ : {F : For (Con.t Γ)} → (σ : Sub Δ Γ) → Pf Δ (F [ subt σ ]f) → Sub Δ (Γ ▹p F)
  _,ₚ_ {Γ} σ pf = wk▹p (Con.p Γ) σ pf
  sub▹p : (σ : Sub (con Δₜ Δₚ) (con Γₜ Γₚ)) → Sub (con Δₜ (Δₚ ▹p⁰ (A [ subt σ ]f))) (con Γₜ (Γₚ ▹p⁰ A))
  p[] : Pf Γ A → (σ : Sub Δ Γ) → Pf Δ (A [ subt σ ]f)
  sub▹p Γₚ (εₚ σₜ) = wk▹p Γₚ (εₚ σₜ) (var pvzero)
  sub▹p Γₚ (wk▹p p σ pf) = {!!}
  test : (σ : Sub Δ Γ) → Sub (Δ ▹p (A [ subt σ ]f)) (Γ ▹p A)
  p[] Γₚ (var pvzero) (wk▹p p σ pf) = pf
  p[] Γₚ (var (pvnext pv)) (wk▹p p σ pf) = p[] Γₚ (var pv) σ 
  p[] Γₚ (app pf pf') σ = app (p[] Γₚ pf σ) (p[] Γₚ pf' σ)
  p[] Γₚ (lam pf) σ = lam (p[] {!\!} {!!} (sub▹p {!!} {!σ!}))
  -}
  
  {-
  idₚ : Subp Γₚ Γₚ
  idₚ {Γₚ = ◇p} = εₚ
  idₚ {Γₚ = Γₚ ▹p⁰ A} = wk▹p Γₚ (liftₚ Γₚ idₚ) (var pvzero)
                                                    
  ε : Sub Γ ◇
  ε = sub εₜ εₚ
             
  id : Sub Γ Γ
  id = sub idₜ idₚ
               
  _∘ₜ_ : Subt Δₜ Ξₜ → Subt Γₜ Δₜ → Subt Γₜ Ξₜ
  εₜ ∘ₜ εₜ = εₜ
  εₜ ∘ₜ wk▹t β x = εₜ
  (wk▹t α t) ∘ₜ β = wk▹t (α ∘ₜ β) (t [ β ]t)
                                         
  _∘ₚ_ : Subp Δₚ Ξₚ → Subp Γₚ Δₚ → Subp Γₚ Ξₚ
  εₚ ∘ₚ βₚ = εₚ
  wk▹p p αₚ x ∘ₚ βₚ = {!wk▹p ? ? ?!}
  
  _∘_ : Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
  sub αₜ αₚ ∘ (sub βₜ βₚ) = sub (αₜ ∘ₜ βₜ) {!!}
  -}
    
  imod : FFOL {lsuc lzero} {lsuc lzero} {lsuc lzero} {lsuc lzero}
  imod = record
    { Con = Con
    ; Sub = Sub
    ; _∘_ = {!!}
    ; id = {!!}
    ; ◇ = ◇
    ; ε = {!!}
    ; Tm = λ Γ → Tm (Con.t Γ)
    ; _[_]t = λ t σ → t [ subt σ ]t
    ; []t-id = {!!}
    ; []t-∘ = {!!}
    ; _▹ₜ = _▹t
    ; πₜ¹ = {!!}
    ; πₜ² = {!!}
    ; _,ₜ_ = {!!}
    ; πₜ²∘,ₜ = {!!}
    ; πₜ¹∘,ₜ = {!!}
    ; ,ₜ∘πₜ = {!!}
    ; ,ₜ∘ = {!!}
    ; For = λ Γ → For (Con.t Γ)
    ; _[_]f = λ A σ → A [ subt σ ]f
    ; []f-id = λ {Γ} {F} → []f-id {Con.t Γ} {F}
    ; []f-∘ = {!λ {Γ Δ Ξ} {α} {β} {F} → []f-∘ {Con.t Γ} {Con.t Δ} {Con.t Ξ} {Sub.t α} {Sub.t β} {F}!}
    ; R = r
    ; R[] = {!!}
    ; _⊢_ = λ Γ A → Pf Γ A
    ; _[_]p = {!!}
    ; _▹ₚ_ = _▹p_
    ; πₚ¹ = {!!}
    ; πₚ² = {!!}
    ; _,ₚ_ = {!!}
    ; ,ₚ∘πₚ = {!!}
    ; πₚ¹∘,ₚ = {!!}
    ; ,ₚ∘ = {!!}
    ; _⇒_ = _⇒_
    ; []f-⇒ = {!!}
    ; ∀∀ = ∀∀
    ; []f-∀∀ = {!!}
    ; lam = {!!}
    ; app = app
    ; ∀i = {!!}
    ; ∀e = {!!}
    }

