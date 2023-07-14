{-# OPTIONS --prop --rewriting #-}

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
  lem3 : {α : Subt Γₜ Δₜ} → {β : Subt Ξₜ Γₜ} → α ∘ₜ (wkₜσt β) ≡ wkₜσt (α ∘ₜ β)
  lem3 {α = εₜ} = refl
  lem3 {α = α ,ₜ var tv} = cong₂ _,ₜ_ (lem3 {α = α}) (≡sym (wkₜσt-wkₜt {tv = tv}))
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
  ∘ₜ-ass : {Γₜ Δₜ Ξₜ Ψₜ : Cont}{α : Subt Γₜ Δₜ}{β : Subt Δₜ Ξₜ}{γ : Subt Ξₜ Ψₜ} → (γ ∘ₜ β) ∘ₜ α ≡ γ ∘ₜ (β ∘ₜ α)
  ∘ₜ-ass {α = α} {β} {εₜ} = refl
  ∘ₜ-ass {α = α} {β} {γ ,ₜ x} = cong₂ _,ₜ_ ∘ₜ-ass (≡sym ([]t-∘ {t = x}))
  []f-∀∀ : {A : For (Γₜ ▹t⁰)} → {σₜ : Subt Δₜ Γₜ} → (∀∀ A) [ σₜ ]f ≡ (∀∀ (A [ (σₜ ∘ₜ πₜ¹ idₜ) ,ₜ πₜ² idₜ ]f))
  []f-∀∀ {A = A} = cong ∀∀ (cong (_[_]f A) (cong₂ _,ₜ_ (≡tran (cong wkₜσt (≡sym σ-idr)) (≡sym lem3)) refl))


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

  []c-id : Γₚ [ idₜ ]c ≡ Γₚ
  []c-id {Γₚ = ◇p} = refl
  []c-id {Γₚ = Γₚ ▹p⁰ x} = cong₂ _▹p⁰_ []c-id []f-id

  []c-∘ : {α : Subt Δₜ Ξₜ} {β : Subt Γₜ Δₜ} {Ξₚ : Conp Ξₜ} → Ξₚ [ α ∘ₜ β ]c ≡ (Ξₚ [ α ]c) [ β ]c 
  []c-∘ {α = α} {β = β} {◇p} = refl
  []c-∘ {α = α} {β = β} {Ξₚ ▹p⁰ A} = cong₂ _▹p⁰_ []c-∘ []f-∘

  
  record Sub (Γ : Con) (Δ : Con) : Set₁ where
    constructor sub
    field
      t : Subt (Con.t Γ) (Con.t Δ)
      p : Subp {Con.t Γ} (Con.p Γ) ((Con.p Δ) [ t ]c)

  -- An order on contexts, where we can only change positions
  infixr 5 _∈ₚ*_
  data _∈ₚ*_ : Conp Γₜ → Conp Γₜ → Set₁ where
    zero∈ₚ* : ◇p ∈ₚ* Γₚ
    next∈ₚ* : {A : For Δₜ} → PfVar (con Δₜ Δₚ) A → Δₚ' ∈ₚ* Δₚ → (Δₚ' ▹p⁰ A) ∈ₚ* Δₚ
  -- Allows to grow ∈ₚ* to the right
  right∈ₚ* :{A : For Δₜ} → Γₚ ∈ₚ* Δₚ → Γₚ ∈ₚ* (Δₚ ▹p⁰ A)
  right∈ₚ* zero∈ₚ* = zero∈ₚ*
  right∈ₚ* (next∈ₚ* x h) = next∈ₚ* (pvnext x) (right∈ₚ* h)
  both∈ₚ* : {A : For Γₜ} → Γₚ ∈ₚ* Δₚ → (Γₚ ▹p⁰ A) ∈ₚ* (Δₚ ▹p⁰ A)
  both∈ₚ* zero∈ₚ* = next∈ₚ* pvzero zero∈ₚ*
  both∈ₚ* (next∈ₚ* x h) = next∈ₚ* pvzero (next∈ₚ* (pvnext x) (right∈ₚ* h))
  refl∈ₚ* : Γₚ ∈ₚ* Γₚ
  refl∈ₚ* {Γₚ = ◇p} = zero∈ₚ*
  refl∈ₚ* {Γₚ = Γₚ ▹p⁰ x} = both∈ₚ* refl∈ₚ*

  ∈ₚ▹tp : {A : For Δₜ} → PfVar (con Δₜ Δₚ) A → PfVar (con Δₜ Δₚ ▹t) (A [ wkₜσt idₜ ]f)
  ∈ₚ▹tp pvzero = pvzero
  ∈ₚ▹tp (pvnext x) = pvnext (∈ₚ▹tp x)
  ∈ₚ*▹tp : Γₚ ∈ₚ* Δₚ → (Γₚ ▹tp) ∈ₚ* (Δₚ ▹tp)
  ∈ₚ*▹tp zero∈ₚ* = zero∈ₚ*
  ∈ₚ*▹tp (next∈ₚ* x s) = next∈ₚ* (∈ₚ▹tp x) (∈ₚ*▹tp s)

  mon∈ₚ∈ₚ* : {A : For Δₜ} → PfVar (con Δₜ Δₚ') A → Δₚ' ∈ₚ* Δₚ → PfVar (con Δₜ Δₚ) A
  mon∈ₚ∈ₚ* pvzero (next∈ₚ* x x₁) = x
  mon∈ₚ∈ₚ* (pvnext s) (next∈ₚ* x x₁) = mon∈ₚ∈ₚ* s x₁

  ∈ₚ*→Sub : Δₚ ∈ₚ* Δₚ' → Subp {Δₜ} Δₚ' Δₚ
  ∈ₚ*→Sub zero∈ₚ* = εₚ
  ∈ₚ*→Sub (next∈ₚ* x s) = ∈ₚ*→Sub s ,ₚ var x

  idₚ : Subp {Δₜ} Δₚ Δₚ
  idₚ = ∈ₚ*→Sub refl∈ₚ*

  wkₚp : {A : For Δₜ} → Δₚ ∈ₚ* Δₚ' → Pf (con Δₜ Δₚ) A → Pf (con Δₜ Δₚ') A
  wkₚp s (var pv) = var (mon∈ₚ∈ₚ* pv s)
  wkₚp s (app pf pf₁) = app (wkₚp s pf) (wkₚp s pf₁)
  wkₚp s (lam {A = A} pf) = lam (wkₚp (both∈ₚ* s) pf)
  wkₚp s (p∀∀e pf) = p∀∀e (wkₚp s pf)
  wkₚp s (p∀∀i pf) = p∀∀i (wkₚp (∈ₚ*▹tp s) pf)
  lliftₚ : {Γₚ : Conp Δₜ} → Δₚ ∈ₚ* Δₚ' → Subp {Δₜ} Δₚ Γₚ → Subp {Δₜ} Δₚ' Γₚ
  lliftₚ s εₚ = εₚ
  lliftₚ s (σₚ ,ₚ pf) = lliftₚ s σₚ ,ₚ wkₚp s pf










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
  
  _[_]σₚ : Subp {Δₜ} Δₚ Δₚ' → (σ : Subt Γₜ Δₜ) → Subp {Γₜ} (Δₚ [ σ ]c) (Δₚ' [ σ ]c)
  εₚ [ σₜ ]σₚ = εₚ
  (σₚ ,ₚ pf) [ σₜ ]σₚ = (σₚ [ σₜ ]σₚ) ,ₚ (pf [ σₜ ]pₜ)


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


  _∘ₚ_ : {Γₚ Δₚ Ξₚ : Conp Δₜ} → Subp {Δₜ} Δₚ Ξₚ → Subp {Δₜ} Γₚ Δₚ → Subp {Δₜ} Γₚ Ξₚ
  εₚ ∘ₚ β = εₚ
  (α ,ₚ pf) ∘ₚ β = (α ∘ₚ β) ,ₚ (pf [ β ]p)
  idlₚ : {Γₚ Δₚ : Conp Γₜ} {σₚ : Subp Γₚ Δₚ} → (idₚ {Δₚ = Δₚ}) ∘ₚ σₚ ≡ σₚ
  idlₚ {Δₚ = ◇p} = ?
  idlₚ {Δₚ = Δₚ ▹p⁰ x} = ?
  idrₚ : {Γₚ Δₚ : Conp Γₜ} {σₚ : Subp Γₚ Δₚ} →  σₚ ∘ₚ (idₚ {Δₚ = Γₚ}) ≡ σₚ
  idrₚ = {!!}  

  id : Sub Γ Γ
  id {Γ} = sub idₜ (subst (Subp _) (≡sym []c-id) idₚ)
  _∘_ : Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
  sub αₜ αₚ ∘ sub βₜ βₚ = sub (αₜ ∘ₜ βₜ) (subst (Subp _) (≡sym []c-∘) (αₚ [ βₜ ]σₚ) ∘ₚ βₚ)
  idl : {Γ Δ : Con} {σ : Sub Γ Δ} →  (id {Δ}) ∘ σ ≡ σ
  idl {σ = sub σₜ σₚ} = cong₂' sub σ-idl {!!}
  idr : {Γ Δ : Con} {σ : Sub Γ Δ} →  σ ∘ (id {Γ}) ≡ σ
  idr {σ = sub σₜ σₚ} = cong₂' sub σ-idr {!!}
  {-
  ∘ₚ-ass :
    {Γₜ Δₜ Ξₜ Ψₜ : Cont}{Γₚ : Conp Γₜ}{Δₚ : Conp Δₜ}{Ξₚ : Conp Ξₜ}{Ψₚ : Conp Ψₜ}
    {αₜ : Subt Γₜ Δₜ}{βₜ : Subt Δₜ Ξₜ}{γₜ : Subt Ξₜ Ψₜ}{γₚ : Subp Ξₚ (Ψₚ [ γₜ ]c)}{βₚ : Subp Δₚ (Ξₚ [ βₜ ]c)}{αₚ : Subp Γₚ (Δₚ [ αₜ ]c)}
    {eq₁ : Subp (Δₚ [ αₜ ]c) ((Ψₚ [ γₜ ∘ₜ βₜ ]c)[ αₜ ]c) ≡ Subp (Δₚ [ αₜ ]c) (Ψₚ [ (γₜ ∘ₜ βₜ) ∘ₜ αₜ ]c)}
    {eq₂ : Subp (Ξₚ [ βₜ ]c) ((Ψₚ [ γₜ ]c)[ βₜ ]c) ≡  Subp (Ξₚ [ βₜ ]c) (Ψₚ [ γₜ ∘ₜ βₜ ]c)}
    {eq₃ : Subp (Ξₚ [ βₜ ∘ₜ αₜ ]c) ((Ψₚ [ γₜ ]c) [ βₜ ∘ₜ αₜ ]c) ≡ {!Subp (Ξₚ [ βₜ ∘ₜ αₜ ]c) (Ψₚ [ γₜ ∘ₜ (βₜ ∘ₜ αₜ) ]c)!}}
    {eq₄ : Subp (Δₚ [ αₜ ]c) ((Ξₚ [ βₜ ]c) [ αₜ ]c) ≡ Subp (Δₚ [ αₜ ]c) (Ξₚ [ βₜ ∘ₜ αₜ ]c)}
    → (coe eq₁ (((coe eq₂ (γₚ [ βₜ ]σₚ)) ∘ₚ βₚ) [ αₜ ]σₚ) ∘ₚ αₚ) ≡ (coe eq₃ (γₚ [ βₜ ∘ₜ αₜ ]σₚ)) ∘ₚ ((coe eq₄ (βₚ [ αₜ ]σₚ) ∘ₚ αₚ))
  -}
  postulate ∘-ass : {Γ Δ Ξ Ψ : Con}{α : Sub Γ Δ}{β : Sub Δ Ξ}{γ : Sub Ξ Ψ} → (γ ∘ β) ∘ α ≡ γ ∘ (β ∘ α)
  -- ∘-ass {Γ}{Δ}{Ξ}{Ψ}{α = sub αₜ αₚ} {β = sub βₜ βₚ} {γ = sub γₜ γₚ} = {!Subp (Con.p Ξ [ βₜ ∘ₜ αₜ ]c) (Con.p Ψ [ γₜ ∘ₜ (βₜ ∘ₜ αₜ) ]c)!}


  -- SUB-ization

  lemA : {σₜ : Subt Γₜ Δₜ}{t : Tm Γₜ} → (Γₚ ▹tp) [ σₜ ,ₜ t ]c ≡  Γₚ [ σₜ ]c
  lemA {Γₚ = ◇p} = refl
  lemA {Γₚ = Γₚ ▹p⁰ t} = cong₂ _▹p⁰_ lemA (≡tran (≡sym []f-∘) (cong (λ σ → t [ σ ]f) (≡tran wk∘, σ-idl)))
  πₜ¹* : {Γ Δ : Con} → Sub Δ (Γ ▹t) → Sub Δ Γ
  πₜ¹* (sub (σₜ ,ₜ t) σₚ) = sub σₜ (subst (Subp _) lemA σₚ)
  πₜ²* : {Γ Δ : Con} → Sub Δ (Γ ▹t) → Tm (Con.t Δ)
  πₜ²* (sub (σₜ ,ₜ t) σₚ) = t
  _,ₜ*_ : {Γ Δ : Con} → Sub Δ Γ → Tm (Con.t Δ) → Sub Δ (Γ ▹t)
  (sub σₜ σₚ) ,ₜ* t = sub (σₜ ,ₜ t) (subst (Subp _) (≡sym lemA) σₚ)
  πₜ²∘,ₜ* : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm (Con.t Δ)} → πₜ²* (σ ,ₜ* t) ≡ t
  πₜ²∘,ₜ* = refl
  πₜ¹∘,ₜ* : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm (Con.t Δ)} → πₜ¹* (σ ,ₜ* t) ≡ σ
  πₜ¹∘,ₜ* {Γ}{Δ}{σ}{t} = cong (sub (Sub.t σ)) coeaba
  ,ₜ∘πₜ* : {Γ Δ : Con} → {σ : Sub Δ (Γ ▹t)} → (πₜ¹* σ) ,ₜ* (πₜ²* σ) ≡ σ
  ,ₜ∘πₜ* {Γ} {Δ} {sub (σₜ ,ₜ t) σₚ} = cong (sub (σₜ ,ₜ t)) coeaba
  ,ₜ∘* : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{t : Tm (Con.t Γ)} → (σ ,ₜ* t) ∘ δ ≡ (σ ∘ δ) ,ₜ* (t [ Sub.t δ ]t)
  lemE : {σₜ : Subt Γₜ Ξₜ}{σₚ : Subp Γₚ (Ξₚ [ σₜ ]c)} {δₜ : Subt Δₜ Γₜ} → (coe _ σₚ [ δₜ ]σₚ) ≡ coe _ (σₚ [ δₜ ]σₚ)
  lemE {δₜ = δₜ} = coecong {eq = refl} {eq' = refl} (λ ξₚ → ξₚ [ δₜ ]σₚ)
  lemF : {Γα Γβ : Conp Δₜ}{δₜ : Subt Δₜ Γₜ}{δₚ : Subp Δₚ (Γₚ [ δₜ ]c)} → (eq : Γβ ≡ Γα) → (ξ : Subp (Γₚ [ δₜ ]c) Γβ) → coe (cong (Subp Δₚ) eq) (ξ ∘ₚ δₚ) ≡ coe (cong (Subp _) eq) ξ ∘ₚ δₚ
  lemF refl ξ = ≡tran coerefl (cong₂ _∘ₚ_ (≡sym coerefl) refl)
  --lemG : {Γα Γβ : Conp Δₜ}{σₜ : Subt Γₜ Ξₜ}{δₜ : Subt Δₜ Γₜ} → (eq : Γβ ≡ Γα) → (ξ : Subp Γₚ (Ξₚ [ σₜ ]c)) → coe refl (ξ [ δₜ ]σₚ) ≡ (coe refl ξ) [ δₜ ]σₚ
  --lemG eq ε= {!!}
  substf : {ℓ ℓ' : Level}{A : Set ℓ}{P : A → Set ℓ'}{Q : A → Set ℓ'}{a b c d : A}{eqa : a ≡ a}{eqb : b ≡ b}{eqcd : c ≡ d}{eqdc : d ≡ c}{f : P a → P b}{g : P b → Q c}{x : P a} → g (subst P eqb (f (subst P eqa x))) ≡ subst Q eqdc (subst Q eqcd (g (f x)))
  substf {P = P} {Q = Q} {eqcd = refl} {f = f} {g = g} = ≡tran² (cong g (≡tran (substrefl {P = P} {e = refl}) (cong f (substrefl {P = P} {e = refl})))) (≡sym (substrefl {P = Q} {e = refl})) (≡sym (substrefl {P = Q} {e = refl}))
  
  ,ₜ∘* {Γ} {Δ} {Ξ} {sub σₜ σₚ} {sub δₜ δₚ} {t} = cong (sub ((σₜ ∘ₜ δₜ) ,ₜ (t [ δₜ ]t)))
    (substfgpoly
      {P = Subp {Con.t Δ} (Con.p Δ)}
      {Q = Subp {Con.t Δ} ((Con.p Γ) [ δₜ ]c)}
      {R = Subp {Con.t Γ} (Con.p Γ)}
      {F = λ X → X [ δₜ ]c}
      {eq₁ = ≡sym lemA}
      {eq₂ = ≡sym []c-∘}
      {eq₃ = ≡sym []c-∘}
      {eq₄ = ≡sym lemA}
      {g = λ σₚ → σₚ ∘ₚ δₚ}
      {f = λ σₚ → σₚ [ δₜ ]σₚ}
      {x = σₚ})

  πₚ¹* : {Γ Δ : Con} {A : For (Con.t Γ)} → Sub Δ (Γ ▹p A) → Sub Δ Γ
  πₚ¹* (sub σₜ (σₚ ,ₚ pf)) = sub σₜ σₚ
  πₚ² : {Γ Δ : Con} {F : For (Con.t Γ)} (σ : Sub Δ (Γ ▹p F)) → Pf Δ (F [ Sub.t (πₚ¹* σ) ]f)
  πₚ² (sub σₜ (σₚ ,ₚ pf)) = pf
  _,ₚ*_ : {Γ Δ : Con} {F : For (Con.t Γ)} (σ : Sub Δ Γ) → Pf Δ (F [ Sub.t σ ]f) → Sub Δ (Γ ▹p F)
  sub σₜ σₚ ,ₚ* pf = sub σₜ (σₚ ,ₚ pf)

  ,ₚ∘πₚ : {Γ Δ : Con} → {F : For (Con.t Γ)} → {σ : Sub Δ (Γ ▹p F)} → (πₚ¹* σ) ,ₚ* (πₚ² σ) ≡ σ
  ,ₚ∘πₚ {σ = sub σₜ (σₚ ,ₚ p)} = refl
  --funlol : {Γₜ Δₜ : Cont}{Γₚ : Conp Γₜ}{Δₚ : Conp Δₜ}{Ξₚ : Conp Ξₜ}{σₜ : Subt Γₜ Ξₜ}{δₜ : Subt Δₜ Γₜ}{δₚ : Subp Δₚ (Γₚ [ δₜ ]c)}{A : For Ξₜ}{prf : Pf (con Δₜ (Γₚ [ δₜ ]c)) ((A [ σₜ ∘ₜ δₜ ]f))} → Subp {Δₜ} (Γₚ [ δₜ ]c) ((Ξₚ [ σₜ ∘ₜ δₜ ]c) ▹p⁰ ((A [ σₜ ]f) [ δₜ ]f)) → Subp {Δₜ} (Δₚ) ((Ξₚ [ σₜ ∘ₜ δₜ ]c) ▹p⁰ (A [ σₜ ∘ₜ δₜ ]f))
  --funlol {Γₚ = Γₚ} {Ξₚ = Ξₚ} {σₜ = σₜ} {δₜ = δₜ} {δₚ = δₚ} {prf = prf} (ξ ,ₚ pf) = ((subst (λ X → Subp (Γₚ [ δₜ ]c) ((Ξₚ [ σₜ ∘ₜ δₜ ]c) ▹p⁰ X)) (≡sym []f-∘) ξ) ,ₚ ?) ∘ₚ δₚ
  postulate ,ₚ∘ : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{F : For (Con.t Ξ)}{prf : Pf Γ (F [ Sub.t σ ]f)} → (σ ,ₚ* prf) ∘ δ ≡ (σ ∘ δ) ,ₚ* (substP (λ F → Pf Δ F) (≡sym []f-∘) ((prf [ Sub.t δ ]pₜ) [ Sub.p δ ]p))
  {-,ₚ∘ {Γ = Γ} {Δ = Δ} {σ = sub σₜ σₚ} {sub δₜ δₚ} {F = A} {prf} = cong (sub (σₜ ∘ₜ δₜ)) (cong {!funlol!} 
    (substfpoly
      {P = λ X → Subp (Con.p Γ [ δₜ ]c) (X ▹p⁰ ((A [ σₜ ]f) [ δₜ ]f))}
      {R = λ X → Subp (Con.p Γ [ δₜ ]c) X}
      {eq = ≡sym []c-∘}
      {f = λ ξ → ξ ,ₚ (prf [ δₜ ]pₜ)}
      {x = σₚ [ δₜ ]σₚ}
    ))
  -}
  --_,ₜ_ : {Γ Δ : Con} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹t)
  --πₜ²∘,ₜ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm Δ} → πₜ² (σ ,ₜ t) ≡ t
  --πₜ¹∘,ₜ : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm Δ} → πₜ¹ (σ ,ₜ t) ≡ σ
  --,ₜ∘πₜ : {Γ Δ : Con} → {σ : Sub Δ (Γ ▹ₜ)} → (πₜ¹ σ) ,ₜ (πₜ² σ) ≡ σ
  --,ₜ∘ : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{t : Tm Γ} → (σ ,ₜ t) ∘ δ ≡ (σ ∘ δ) ,ₜ (t [ δ ]t)

--  lemB : ∀{ℓ}{A : Set ℓ}{ℓ'}{P : A → Set ℓ'}{a a' : A}{e : a ≡ a'}{p : P a}{p' : P a'} → p' ≡ p → subst P e p' ≡ p
  
  lemC : {σₜ : Subt Δₜ Γₜ}{t : Tm Δₜ} → (Γₚ ▹tp) [ σₜ ,ₜ t ]c ≡ Γₚ [ σₜ ]c
  lemC {Γₚ = ◇p} = refl
  lemC {Γₚ = Γₚ ▹p⁰ x} = cong₂ _▹p⁰_ lemC (≡tran (≡sym []f-∘) (cong (λ σ → x [ σ ]f) (≡tran wk∘, σ-idl)))

  lemD : {A : For (Con.t Γ)}{σ : Sub Δ (Γ ▹p A)} → Sub.t (πₚ¹* σ) ≡ Sub.t σ
  lemD {σ = sub σₜ (σₚ ,ₚ pf)} = refl

    
  imod : FFOL {lsuc lzero} {lsuc lzero} {lsuc lzero} {lsuc lzero}
  imod = record
    { Con = Con
    ; Sub = Sub
    ; _∘_ = _∘_
    ; ∘-ass = ∘-ass
    ; id = id
    ; idl = {!!}
    ; idr = {!!}
    ; ◇ = ◇
    ; ε = sub εₜ εₚ
    ; ε-u = {!!}
    ; Tm = λ Γ → Tm (Con.t Γ)
    ; _[_]t = λ t σ → t [ Sub.t σ ]t
    ; []t-id = []t-id
    ; []t-∘ = λ {Γ}{Δ}{Ξ}{α}{β}{t} → []t-∘ {α = Sub.t α} {β = Sub.t β} {t = t}
    ; _▹ₜ = _▹t
    ; πₜ¹ = πₜ¹*
    ; πₜ² = πₜ²*
    ; _,ₜ_ = _,ₜ*_
    ; πₜ²∘,ₜ = refl
    ; πₜ¹∘,ₜ = πₜ¹∘,ₜ*
    ; ,ₜ∘πₜ = ,ₜ∘πₜ*
    ; ,ₜ∘ = ,ₜ∘*
    ; For = λ Γ → For (Con.t Γ)
    ; _[_]f = λ A σ → A [ Sub.t σ ]f
    ; []f-id = []f-id
    ; []f-∘ = []f-∘
    ; R = r
    ; R[] = refl
    ; _⊢_ = λ Γ A → Pf Γ A
    ; _[_]p = λ {Γ}{Δ}{F} pf σ → (pf [ Sub.t σ ]pₜ) [ Sub.p σ ]p
    ; _▹ₚ_ = _▹p_
    ; πₚ¹ = πₚ¹*
    ; πₚ² = πₚ²
    ; _,ₚ_ = _,ₚ*_
    ; ,ₚ∘πₚ = ,ₚ∘πₚ
    ; πₚ¹∘,ₚ = refl
    ; ,ₚ∘ = λ {Γ}{Δ}{Ξ}{σ}{δ}{F}{prf} → ,ₚ∘ {prf = prf}
    ; _⇒_ = _⇒_
    ; []f-⇒ = refl
    ; ∀∀ = ∀∀
    ; []f-∀∀ = []f-∀∀
    ; lam = λ {Γ}{F}{G} pf → substP (λ H → Pf Γ (F ⇒ H)) (≡tran (cong (_[_]f G) (lemD {σ = id})) []f-id) (lam pf)
    ; app = app
    ; ∀i = p∀∀i
    ; ∀e = λ {Γ} {F} pf {t} → p∀∀e pf
    }

