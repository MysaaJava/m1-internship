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
    _,ₜ_ : Subt Δₜ Γₜ → Tm Δₜ → Subt Δₜ (Γₜ ▹t⁰)
    
  -- We subst on terms
  _[_]t : Tm Γₜ → Subt Δₜ Γₜ → Tm Δₜ
  var tvzero [ σ ,ₜ t ]t = t
  var (tvnext tv) [ σ ,ₜ t ]t = var tv [ σ ]t
  
  -- We define liftings on term variables
  -- A term of n variables is a term of n+1 variables
  -- Same for a term array
  wkₜt : Tm Γₜ → Tm (Γₜ ▹t⁰)
  
  wkₜt (var tv) = var (tvnext tv)
  
  -- From a substition into n variables, we get a substitution into n+1 variables which don't use the last one
  wkₜσt : Subt Δₜ Γₜ → Subt (Δₜ ▹t⁰) Γₜ
  wkₜσt εₜ = εₜ
  wkₜσt (σ ,ₜ t) = (wkₜσt σ) ,ₜ (wkₜt t)
  wkₜσt-wkₜt : {tv : TmVar Γₜ} → {σ : Subt Δₜ Γₜ} → wkₜt (var tv [ σ ]t) ≡ var tv [ wkₜσt σ ]t
  wkₜσt-wkₜt {tv = tvzero} {σ = σ ,ₜ x} = refl
  wkₜσt-wkₜt {tv = tvnext tv} {σ = σ ,ₜ x} = wkₜσt-wkₜt {tv = tv} {σ = σ}
  
  -- From a substitution into n variables, we construct a substitution from n+1 variables to n+1 variables which maps it to itself
  -- i.e. 0 -> 0 and for all i ->(old) σ(i) we get i+1 -> σ(i)+1
  liftₜσ : Subt Δₜ Γₜ → Subt (Δₜ ▹t⁰) (Γₜ ▹t⁰)
  liftₜσ σ = (wkₜσt σ) ,ₜ (var tvzero)

  
  -- We subst on formulæ
  _[_]f : For Γₜ → Subt Δₜ Γₜ → For Δₜ
  (r t u) [ σ ]f = r (t [ σ ]t) (u [ σ ]t)
  (A ⇒ B) [ σ ]f = (A [ σ ]f) ⇒ (B [ σ ]f)
  (∀∀ A) [ σ ]f = ∀∀ (A [ liftₜσ σ ]f)
                                 
  -- We now can define identity on term substitutions       
  idₜ : Subt Γₜ Γₜ
  idₜ {◇t} = εₜ
  idₜ {Γₜ ▹t⁰} = liftₜσ (idₜ {Γₜ})

  _∘ₜ_ : Subt Δₜ Γₜ → Subt Ξₜ Δₜ → Subt Ξₜ Γₜ
  εₜ ∘ₜ β = εₜ
  (α ,ₜ x) ∘ₜ β = (α ∘ₜ β) ,ₜ (x [ β ]t)


  -- We have the access functions from the algebra, in restricted versions
  πₜ¹ : Subt Δₜ (Γₜ ▹t⁰) → Subt Δₜ Γₜ
  πₜ¹ (σₜ ,ₜ t) = σₜ
  πₜ² : Subt Δₜ (Γₜ ▹t⁰) → Tm Δₜ
  πₜ² (σₜ ,ₜ t) = t
  
  -- And their equalities (the fact that there are reciprocical)
  πₜ²∘,ₜ : {σₜ : Subt Δₜ Γₜ} → {t : Tm Δₜ} → πₜ² (σₜ ,ₜ t) ≡ t
  πₜ²∘,ₜ = refl
  πₜ¹∘,ₜ : {σₜ : Subt Δₜ Γₜ} → {t : Tm Δₜ} → πₜ¹ (σₜ ,ₜ t) ≡ σₜ
  πₜ¹∘,ₜ = refl
  ,ₜ∘πₜ : {σₜ : Subt Δₜ (Γₜ ▹t⁰)} → (πₜ¹ σₜ) ,ₜ (πₜ² σₜ) ≡ σₜ
  ,ₜ∘πₜ {σₜ = σₜ ,ₜ t} = refl

  -- We can also prove the substitution equalities
  []t-id : {t : Tm Γₜ} → t [ idₜ {Γₜ} ]t ≡ t
  []t-id {Γₜ ▹t⁰} {var tvzero} = refl
  []t-id {Γₜ ▹t⁰} {var (tvnext tv)} = substP (λ t → t ≡ var (tvnext tv)) (wkₜσt-wkₜt {tv = tv} {σ = idₜ}) (substP (λ t → wkₜt t ≡ var (tvnext tv)) (≡sym ([]t-id {t = var tv})) refl)
  []t-∘ : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → {t : Tm Γₜ} → t [ β ∘ₜ α ]t ≡ (t [ β ]t) [ α ]t
  []t-∘ {α = α} {β = β ,ₜ t} {t = var tvzero} = refl
  []t-∘ {α = α} {β = β ,ₜ t} {t = var (tvnext tv)} = []t-∘ {t = var tv}
  []f-id : {F : For Γₜ} → F [ idₜ {Γₜ} ]f ≡ F
  []f-id {F = r t u} = cong₂ r []t-id []t-id
  []f-id {F = F ⇒ G} = cong₂ _⇒_ []f-id []f-id
  []f-id {F = ∀∀ F} = cong ∀∀ []f-id
  wkₜσt-∘ : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → wkₜσt (β ∘ₜ α) ≡ (wkₜσt β ∘ₜ liftₜσ α)
  wkₜt[] : {α : Subt Δₜ Γₜ} → {t : Tm Γₜ} → wkₜt (t [ α ]t) ≡ (wkₜt t [ liftₜσ α ]t)
  wkₜσt-∘ {β = εₜ} = refl
  wkₜσt-∘ {β = β ,ₜ t} = cong₂ _,ₜ_ wkₜσt-∘ (wkₜt[] {t = t})
  wkₜt[] {α = α ,ₜ t} {var tvzero} = refl
  wkₜt[] {α = α ,ₜ t} {var (tvnext tv)} = wkₜt[] {t = var tv}
  liftₜσ-∘ : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → liftₜσ (β ∘ₜ α) ≡ (liftₜσ β) ∘ₜ (liftₜσ α)
  liftₜσ-∘ {α = α} {β = εₜ} = refl
  liftₜσ-∘ {α = α} {β = β ,ₜ t} = cong₂ _,ₜ_ (cong₂ _,ₜ_ wkₜσt-∘ (wkₜt[] {t = t})) refl
  []f-∘ : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → {F : For Γₜ} → F [ β ∘ₜ α ]f ≡ (F [ β ]f) [ α ]f
  []f-∘ {α = α} {β = β} {F = r t u} = cong₂ r ([]t-∘ {α = α} {β = β} {t = t}) ([]t-∘ {α = α} {β = β} {t = u})
  []f-∘ {F = F ⇒ G} = cong₂ _⇒_ []f-∘ []f-∘
  []f-∘ {F = ∀∀ F} = cong ∀∀ (≡tran (cong (λ σ → F [ σ ]f) liftₜσ-∘) []f-∘)
  R[] : {σ : Subt Δₜ Γₜ} → {t u : Tm Γₜ} → (r t u) [ σ ]f ≡ r (t [ σ ]t) (u [ σ ]t)
  R[] = refl

  wk[,] : {t : Tm Γₜ}{u : Tm Δₜ}{β : Subt Δₜ Γₜ} → (wkₜt t) [ β ,ₜ u ]t ≡ t [ β ]t
  wk[,] {t = var tvzero} = refl
  wk[,] {t = var (tvnext tv)} = refl
  wk∘, : {α : Subt Γₜ Δₜ}{β : Subt Ξₜ Γₜ}{t : Tm Ξₜ} → (wkₜσt α) ∘ₜ (β ,ₜ t) ≡ (α ∘ₜ β)
  wk∘, {α = εₜ} = refl
  wk∘, {α = α ,ₜ t} {β = β} = cong₂ _,ₜ_ (wk∘, {α = α}) (wk[,] {t = t} {β = β})
  σ-idl : {α : Subt Δₜ Γₜ} → idₜ ∘ₜ α ≡ α
  σ-idl {α = εₜ} = refl
  σ-idl {α = α ,ₜ x} = cong₂ _,ₜ_ (≡tran wk∘, σ-idl) refl
  σ-idr : {α : Subt Δₜ Γₜ} → α ∘ₜ idₜ ≡ α
  σ-idr {α = εₜ} = refl
  σ-idr {α = α ,ₜ x} = cong₂ _,ₜ_ σ-idr []t-id

  data Conp : Cont → Set₁ -- pu tit in Prop
  variable
    Γₚ Γₚ' : Conp Γₜ
    Δₚ Δₚ' : Conp Δₜ
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
  -- (that's why we use wkₜσt)
  _▹tp : Conp Γₜ → Conp (Γₜ ▹t⁰)
  ◇p ▹tp = ◇p
  (Γₚ ▹p⁰ A) ▹tp = (Γₚ ▹tp) ▹p⁰ (A [ wkₜσt idₜ ]f)
  
  _▹t : Con → Con
  Γ ▹t = con ((Con.t Γ) ▹t⁰) (Con.p Γ ▹tp)
                                        
  data PfVar : (Γ : Con) → For (Con.t Γ) → Set₁ where
    pvzero : {A : For (Con.t Γ)} → PfVar (Γ ▹p A) A
    pvnext : {A B : For (Con.t Γ)} → PfVar Γ A → PfVar (Γ ▹p B) A
                                                                
  data Pf : (Γ : Con) → For (Con.t Γ) → Prop₁ where
    var : {A : For (Con.t Γ)} → PfVar Γ A → Pf Γ A
    app : {A B : For (Con.t Γ)} → Pf Γ (A ⇒ B) → Pf Γ A → Pf Γ B
    lam : {A B : For (Con.t Γ)} → Pf (Γ ▹p A) B → Pf Γ (A ⇒ B)
    p∀∀e : {A : For ((Con.t Γ) ▹t⁰)} → {t : Tm (Con.t Γ)} → Pf Γ (∀∀ A) → Pf Γ (A [ idₜ ,ₜ t ]f)
    p∀∀i : {A : For (Con.t (Γ ▹t))} → Pf (Γ ▹t) A → Pf Γ (∀∀ A)


  data Subp : {Δₜ : Cont} → Conp Δₜ → Conp Δₜ → Set₁ where
    εₚ : Subp Δₚ ◇p
    _,ₚ_ : {A : For Δₜ} → (σ : Subp Δₚ Δₚ') → Pf (con Δₜ Δₚ) A → Subp Δₚ (Δₚ' ▹p⁰ A)


  _[_]c : Conp Γₜ → Subt Δₜ Γₜ → Conp Δₜ
  ◇p [ σₜ ]c = ◇p
  (Γₚ ▹p⁰ A) [ σₜ ]c = (Γₚ [ σₜ ]c) ▹p⁰ (A [ σₜ ]f)
  
  record Sub (Γ : Con) (Δ : Con) : Set₁ where
    constructor sub
    field
      t : Subt (Con.t Γ) (Con.t Δ)
      p : Subp {Con.t Γ} (Con.p Γ) ((Con.p Δ) [ t ]c)

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

  ∈ₚ▹tp : {A : For Δₜ} → A ∈ₚ Δₚ → A [ wkₜσt idₜ ]f ∈ₚ (Δₚ ▹tp)
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

  ∈ₚ*→Sub : Δₚ ∈ₚ* Δₚ' → Subp {Δₜ} Δₚ' Δₚ
  ∈ₚ*→Sub zero∈ₚ* = εₚ
  ∈ₚ*→Sub (next∈ₚ* x s) = ∈ₚ*→Sub s ,ₚ var (∈ₚ→var x)

  idₚ : Subp {Δₜ} Δₚ Δₚ
  idₚ = ∈ₚ*→Sub refl∈ₚ*

  wkₚp : {A : For Δₜ} → Δₚ ∈ₚ* Δₚ' → Pf (con Δₜ Δₚ) A → Pf (con Δₜ Δₚ') A
  wkₚp s (var pv) = var (∈ₚ→var (mon∈ₚ∈ₚ* (var→∈ₚ pv) s))
  wkₚp s (app pf pf₁) = app (wkₚp s pf) (wkₚp s pf₁)
  wkₚp s (lam {A = A} pf) = lam (wkₚp (both∈ₚ* s) pf)
  wkₚp s (p∀∀e pf) = p∀∀e (wkₚp s pf)
  wkₚp s (p∀∀i pf) = p∀∀i (wkₚp (∈ₚ*▹tp s) pf)
  lliftₚ : {Γₚ : Conp Δₜ} → Δₚ ∈ₚ* Δₚ' → Subp {Δₜ} Δₚ Γₚ → Subp {Δₜ} Δₚ' Γₚ
  lliftₚ s εₚ = εₚ
  lliftₚ s (σₚ ,ₚ pf) = lliftₚ s σₚ ,ₚ wkₚp s pf











  lem3 : {α : Subt Γₜ Δₜ} → {β : Subt Ξₜ Γₜ} → α ∘ₜ (wkₜσt β) ≡ wkₜσt (α ∘ₜ β)
  lem3 {α = εₜ} = refl
  lem3 {α = α ,ₜ var tv} = cong₂ _,ₜ_ (lem3 {α = α}) (≡sym (wkₜσt-wkₜt {tv = tv}))
  lem7 : {σ : Subt Δₜ Γₜ} → ((Δₚ ▹tp) [ liftₜσ σ ]c) ≡ ((Δₚ [ σ ]c) ▹tp)
  lem7 {Δₚ = ◇p} = refl
  lem7 {Δₚ = Δₚ ▹p⁰ A} = cong₂ _▹p⁰_ lem7 (≡tran² (≡sym []f-∘) (cong (λ σ → A [ σ ]f) (≡tran² (≡sym wkₜσt-∘) (cong wkₜσt (≡tran σ-idl (≡sym σ-idr))) (≡sym lem3))) []f-∘)
  lem8 : {σ : Subt Δₜ Γₜ} {t : Tm Γₜ} → ((wkₜσt σ ∘ₜ (idₜ ,ₜ (t [ σ ]t))) ,ₜ (t [ σ ]t)) ≡ ((idₜ ∘ₜ σ) ,ₜ (t [ σ ]t))
  lem8 = cong₂ _,ₜ_ (≡tran² wk∘, σ-idr (≡sym σ-idl)) refl

  _[_]pvₜ : {A : For Δₜ} → PfVar (con Δₜ Δₚ) A → (σ : Subt Γₜ Δₜ) → PfVar (con Γₜ (Δₚ [ σ ]c)) (A [ σ ]f)
  _[_]pₜ : {A : For Δₜ} → Pf (con Δₜ Δₚ) A → (σ : Subt Γₜ Δₜ) → Pf (con Γₜ (Δₚ [ σ ]c)) (A [ σ ]f)
  pvzero [ σ ]pvₜ = pvzero
  pvnext pv [ σ ]pvₜ = pvnext (pv [ σ ]pvₜ)
  var pv [ σ ]pₜ = var (pv [ σ ]pvₜ)
  app pf pf' [ σ ]pₜ = app (pf [ σ ]pₜ) (pf' [ σ ]pₜ)
  lam pf [ σ ]pₜ = lam (pf [ σ ]pₜ)
  _[_]pₜ {Δₚ = Δₚ} {Γₜ = Γₜ} (p∀∀e {A = A} {t = t} pf) σ = substP (λ F → Pf (con Γₜ (Δₚ [ σ ]c)) F) (≡tran² (≡sym []f-∘) (cong (λ σ → A [ σ ]f) (lem8 {t = t})) ([]f-∘)) (p∀∀e {t = t [ σ ]t} (pf [ σ ]pₜ))
  _[_]pₜ {Γₜ = Γₜ} (p∀∀i pf) σ = p∀∀i (substP (λ Ξₚ → Pf (con (Γₜ ▹t⁰) (Ξₚ)) _) lem7 (pf [ liftₜσ σ ]pₜ))
  






  lem9 : (Δₚ [ wkₜσt idₜ ]c) ≡ (Δₚ ▹tp)
  lem9 {Δₚ = ◇p} = refl
  lem9 {Δₚ = Δₚ ▹p⁰ x} = cong₂ _▹p⁰_ lem9 refl
  wkₜσₚ : Subp {Δₜ} Δₚ' Δₚ → Subp {Δₜ ▹t⁰} (Δₚ' ▹tp) (Δₚ ▹tp)
  wkₜσₚ εₚ = εₚ
  wkₜσₚ {Δₜ = Δₜ} (_,ₚ_ {A = A} σₚ pf) = (wkₜσₚ σₚ) ,ₚ substP (λ Ξₚ → Pf (con (Δₜ ▹t⁰) Ξₚ) (A [ wkₜσt idₜ ]f)) lem9 (_[_]pₜ {Γₜ = Δₜ ▹t⁰} pf (wkₜσt idₜ))

  _[_]p : {A : For Δₜ} → Pf (con Δₜ Δₚ) A → (σ : Subp {Δₜ} Δₚ' Δₚ) → Pf (con Δₜ Δₚ') A
  var pvzero [ σ ,ₚ pf ]p = pf
  var (pvnext pv) [ σ ,ₚ pf ]p = var pv [ σ ]p
  app pf pf₁ [ σ ]p = app (pf [ σ ]p) (pf₁ [ σ ]p)
  lam pf [ σ ]p = lam (pf [ lliftₚ (right∈ₚ* refl∈ₚ*) σ ,ₚ var pvzero ]p) 
  p∀∀e pf [ σ ]p = p∀∀e (pf [ σ ]p)
  p∀∀i pf [ σ ]p = p∀∀i (pf [ wkₜσₚ σ ]p)


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
    ; _[_]t = λ t σ → t [ {!!} ]t
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
    ; _[_]f = λ A σ → A [ {!!} ]f
    ; []f-id = λ {Γ} {F} → {!!}
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

