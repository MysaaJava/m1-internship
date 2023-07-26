{-# OPTIONS --prop --rewriting #-}

open import PropUtil

module FFOLInitial where

  open import FFOL
  open import Agda.Primitive
  open import ListUtil

  {-- TERM CONTEXTS - TERMS - FORMULAE - TERM SUBSTITUTIONS --}

  -- Term contexts are isomorphic to Nat
  data Cont : Set₁ where
    ◇t : Cont
    _▹t⁰ : Cont → Cont
    
  variable
    Γₜ Δₜ Ξₜ : Cont

  -- A term variable is a de-bruijn variable, TmVar n ≈ ⟦0,n-1⟧
  data TmVar : Cont → Set₁ where
    tvzero : TmVar (Γₜ ▹t⁰)
    tvnext : TmVar Γₜ → TmVar (Γₜ ▹t⁰)

  -- For now, we only have term variables (no function symbol)
  data Tm : Cont → Set₁ where
    var : TmVar Γₜ → Tm Γₜ
    
  -- Now we can define formulæ
  data For : Cont → Set₁ where
    R : Tm Γₜ → Tm Γₜ → For Γₜ
    _⇒_ : For Γₜ → For Γₜ → For Γₜ
    ∀∀  : For (Γₜ ▹t⁰) → For Γₜ




  -- Then we define term substitutions
  data Subt : Cont → Cont → Set₁ where
    εₜ : Subt Γₜ ◇t
    _,ₜ_ : Subt Δₜ Γₜ → Tm Δₜ → Subt Δₜ (Γₜ ▹t⁰)
    
  -- We write down the access functions from the algebra, in restricted versions
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

    
  -- We now define the action of term substitutions on terms
  _[_]t : Tm Γₜ → Subt Δₜ Γₜ → Tm Δₜ
  var tvzero [ σ ,ₜ t ]t = t
  var (tvnext tv) [ σ ,ₜ t ]t = var tv [ σ ]t
  
  -- We define weakenings of the term-context for terms
  -- «A term of n variables can be seen as a term of n+1 variables»
  wkₜt : Tm Γₜ → Tm (Γₜ ▹t⁰)
  wkₜt (var tv) = var (tvnext tv)
  
  -- From a substition into n variables, we get a substitution into n+1 variables which don't use the last one
  wkₜσₜ : Subt Δₜ Γₜ → Subt (Δₜ ▹t⁰) Γₜ
  wkₜσₜ εₜ = εₜ
  wkₜσₜ (σ ,ₜ t) = (wkₜσₜ σ) ,ₜ (wkₜt t)
  
  -- From a substitution into n variables, we construct a substitution from n+1 variables to n+1 variables which maps it to itself
  -- i.e. 0 -> 0 and for all i ->(old) σ(i) we get i+1 -> σ(i)+1
  lfₜσₜ : Subt Δₜ Γₜ → Subt (Δₜ ▹t⁰) (Γₜ ▹t⁰)
  lfₜσₜ σ = (wkₜσₜ σ) ,ₜ (var tvzero)

  -- We show how wkₜt and interacts with [_]t
  wkₜ[]t : {α : Subt Δₜ Γₜ} → {t : Tm Γₜ} →  wkₜt (t [ α ]t) ≡ (wkₜt t [ lfₜσₜ α ]t)
  wkₜ[]t {α = α ,ₜ t} {var tvzero} = refl
  wkₜ[]t {α = α ,ₜ t} {var (tvnext tv)} = wkₜ[]t {t = var tv}
  
  -- We can now subst on formulæ
  _[_]f : For Γₜ → Subt Δₜ Γₜ → For Δₜ
  (R t u) [ σ ]f = R (t [ σ ]t) (u [ σ ]t)
  (A ⇒ B) [ σ ]f = (A [ σ ]f) ⇒ (B [ σ ]f)
  (∀∀ A) [ σ ]f = ∀∀ (A [ lfₜσₜ σ ]f)




  -- We now can define identity and composition of term substitutions       
  idₜ : Subt Γₜ Γₜ
  idₜ {◇t} = εₜ
  idₜ {Γₜ ▹t⁰} = lfₜσₜ (idₜ {Γₜ})
  _∘ₜ_ : Subt Δₜ Γₜ → Subt Ξₜ Δₜ → Subt Ξₜ Γₜ
  εₜ ∘ₜ β = εₜ
  (α ,ₜ x) ∘ₜ β = (α ∘ₜ β) ,ₜ (x [ β ]t)

  -- We now have to show all their equalities (idₜ and ∘ₜ respect []t, []f, wkₜ, lfₜ, categorical rules

  -- Substitution for terms
  []t-id : {t : Tm Γₜ} → t [ idₜ {Γₜ} ]t ≡ t
  []t-id {Γₜ ▹t⁰} {var tvzero} = refl
  []t-id {Γₜ ▹t⁰} {var (tvnext tv)} = substP (λ t → t ≡ var (tvnext tv)) (wkₜ[]t {t = var tv}) (substP (λ t → wkₜt t ≡ var (tvnext tv)) (≡sym ([]t-id {t = var tv})) refl)
  []t-∘ : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → {t : Tm Γₜ} → t [ β ∘ₜ α ]t ≡ (t [ β ]t) [ α ]t
  []t-∘ {α = α} {β = β ,ₜ t} {t = var tvzero} = refl
  []t-∘ {α = α} {β = β ,ₜ t} {t = var (tvnext tv)} = []t-∘ {t = var tv}
  
  -- Weakenings and liftings of substitutions
  wkₜσₜ-∘ₜl : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → wkₜσₜ (β ∘ₜ α) ≡ (wkₜσₜ β ∘ₜ lfₜσₜ α)
  wkₜσₜ-∘ₜl {β = εₜ} = refl
  wkₜσₜ-∘ₜl {β = β ,ₜ t} = cong₂ _,ₜ_ wkₜσₜ-∘ₜl (wkₜ[]t {t = t})
  wkₜσₜ-∘ₜr : {α : Subt Γₜ Δₜ} → {β : Subt Ξₜ Γₜ} → α ∘ₜ (wkₜσₜ β) ≡ wkₜσₜ (α ∘ₜ β)
  wkₜσₜ-∘ₜr {α = εₜ} = refl
  wkₜσₜ-∘ₜr {α = α ,ₜ var tv} = cong₂ _,ₜ_ (wkₜσₜ-∘ₜr {α = α}) (≡sym (wkₜ[]t {t = var tv}))
  lfₜσₜ-∘ : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → lfₜσₜ (β ∘ₜ α) ≡ (lfₜσₜ β) ∘ₜ (lfₜσₜ α)
  lfₜσₜ-∘ {α = α} {β = εₜ} = refl
  lfₜσₜ-∘ {α = α} {β = β ,ₜ t} = cong₂ _,ₜ_ (cong₂ _,ₜ_ wkₜσₜ-∘ₜl (wkₜ[]t {t = t})) refl

  -- Cancelling a weakening with a ,ₜ
  wkₜ[,]t : {t : Tm Γₜ}{u : Tm Δₜ}{β : Subt Δₜ Γₜ} → (wkₜt t) [ β ,ₜ u ]t ≡ t [ β ]t
  wkₜ[,]t {t = var tvzero} = refl
  wkₜ[,]t {t = var (tvnext tv)} = refl
  wkₜ∘ₜ,ₜ : {α : Subt Γₜ Δₜ}{β : Subt Ξₜ Γₜ}{t : Tm Ξₜ} → (wkₜσₜ α) ∘ₜ (β ,ₜ t) ≡ (α ∘ₜ β)
  wkₜ∘ₜ,ₜ {α = εₜ} = refl
  wkₜ∘ₜ,ₜ {α = α ,ₜ t} {β = β} = cong₂ _,ₜ_ (wkₜ∘ₜ,ₜ {α = α}) (wkₜ[,]t {t = t} {β = β})
  
  -- Categorical rules are respected by idₜ and ∘ₜ
  idlₜ : {α : Subt Δₜ Γₜ} → idₜ ∘ₜ α ≡ α
  idlₜ {α = εₜ} = refl
  idlₜ {α = α ,ₜ x} = cong₂ _,ₜ_ (≡tran wkₜ∘ₜ,ₜ idlₜ) refl
  idrₜ : {α : Subt Δₜ Γₜ} → α ∘ₜ idₜ ≡ α
  idrₜ {α = εₜ} = refl
  idrₜ {α = α ,ₜ x} = cong₂ _,ₜ_ idrₜ []t-id
  ∘ₜ-ass : {Γₜ Δₜ Ξₜ Ψₜ : Cont}{α : Subt Γₜ Δₜ}{β : Subt Δₜ Ξₜ}{γ : Subt Ξₜ Ψₜ} → (γ ∘ₜ β) ∘ₜ α ≡ γ ∘ₜ (β ∘ₜ α)
  ∘ₜ-ass {α = α} {β} {εₜ} = refl
  ∘ₜ-ass {α = α} {β} {γ ,ₜ x} = cong₂ _,ₜ_ ∘ₜ-ass (≡sym ([]t-∘ {t = x}))
  
  -- Unicity of the terminal morphism
  εₜ-u : {σₜ : Subt Γₜ ◇t} → σₜ ≡ εₜ
  εₜ-u {σₜ = εₜ} = refl

  -- Substitution for formulæ
  []f-id : {F : For Γₜ} → F [ idₜ {Γₜ} ]f ≡ F
  []f-id {F = R t u} = cong₂ R []t-id []t-id
  []f-id {F = F ⇒ G} = cong₂ _⇒_ []f-id []f-id
  []f-id {F = ∀∀ F} = cong ∀∀ []f-id
  []f-∘ : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → {F : For Γₜ} → F [ β ∘ₜ α ]f ≡ (F [ β ]f) [ α ]f
  []f-∘ {α = α} {β = β} {F = R t u} = cong₂ R ([]t-∘ {α = α} {β = β} {t = t}) ([]t-∘ {α = α} {β = β} {t = u})
  []f-∘ {F = F ⇒ G} = cong₂ _⇒_ []f-∘ []f-∘
  []f-∘ {F = ∀∀ F} = cong ∀∀ (≡tran (cong (λ σ → F [ σ ]f) lfₜσₜ-∘) []f-∘)

  -- Substitution for formulæ constructors
  -- we omit []f-R and []f-⇒ as they are directly refl
  []f-∀∀ : {A : For (Γₜ ▹t⁰)} → {σₜ : Subt Δₜ Γₜ} → (∀∀ A) [ σₜ ]f ≡ (∀∀ (A [ (σₜ ∘ₜ πₜ¹ idₜ) ,ₜ πₜ² idₜ ]f))
  []f-∀∀ {A = A} = cong ∀∀ (cong (_[_]f A) (cong₂ _,ₜ_ (≡tran (cong wkₜσₜ (≡sym idrₜ)) (≡sym wkₜσₜ-∘ₜr)) refl))








  -- We can now define proof contexts, which are indexed by a term context
  -- i.e. we know which terms a proof context can use
  data Conp : Cont → Set₁ where
    ◇p : Conp Γₜ
    _▹p⁰_ : Conp Γₜ → For Γₜ → Conp Γₜ
  
  variable
    Γₚ Γₚ' : Conp Γₜ
    Δₚ Δₚ' : Conp Δₜ
    Ξₚ Ξₚ' : Conp Ξₜ

  -- The actions of Subt's is extended to contexts
  _[_]c : Conp Γₜ → Subt Δₜ Γₜ → Conp Δₜ
  ◇p [ σₜ ]c = ◇p
  (Γₚ ▹p⁰ A) [ σₜ ]c = (Γₚ [ σₜ ]c) ▹p⁰ (A [ σₜ ]f)
  -- This Conp is indeed a functor
  []c-id : Γₚ [ idₜ ]c ≡ Γₚ
  []c-id {Γₚ = ◇p} = refl
  []c-id {Γₚ = Γₚ ▹p⁰ x} = cong₂ _▹p⁰_ []c-id []f-id
  []c-∘ : {α : Subt Δₜ Ξₜ} {β : Subt Γₜ Δₜ} {Ξₚ : Conp Ξₜ} → Ξₚ [ α ∘ₜ β ]c ≡ (Ξₚ [ α ]c) [ β ]c 
  []c-∘ {α = α} {β = β} {◇p} = refl
  []c-∘ {α = α} {β = β} {Ξₚ ▹p⁰ A} = cong₂ _▹p⁰_ []c-∘ []f-∘


  -- We can also add a term that will not be used in the formulæ already present
  -- (that's why we use wkₜσₜ)
  _▹tp : Conp Γₜ → Conp (Γₜ ▹t⁰)
  Γ ▹tp = Γ [ wkₜσₜ idₜ ]c
  -- We show how it interacts with ,ₜ and lfₜσₜ
  ▹tp,ₜ : {σₜ : Subt Γₜ Δₜ}{t : Tm Γₜ} → (Γₚ ▹tp) [ σₜ ,ₜ t ]c ≡  Γₚ [ σₜ ]c
  ▹tp,ₜ {Γₚ = Γₚ} = ≡tran (≡sym []c-∘) (cong (λ ξ → Γₚ [ ξ ]c) (≡tran wkₜ∘ₜ,ₜ idlₜ))
  ▹tp-lfₜ : {σ : Subt Δₜ Γₜ} → ((Δₚ ▹tp) [ lfₜσₜ σ ]c) ≡ ((Δₚ [ σ ]c) ▹tp)
  ▹tp-lfₜ {Δₚ = Δₚ} = ≡tran² (≡sym []c-∘) (cong (λ ξ → Δₚ [ ξ ]c) (≡tran² (≡sym wkₜσₜ-∘ₜl) (cong wkₜσₜ (≡tran idlₜ (≡sym idrₜ))) (≡sym wkₜσₜ-∘ₜr))) []c-∘



  -- With those contexts, we have everything to define proofs
  data PfVar : (Γₜ : Cont) → (Γₚ : Conp Γₜ) → For Γₜ → Prop₁ where
    pvzero : {A : For Γₜ} → PfVar Γₜ (Γₚ ▹p⁰ A) A
    pvnext : {A B : For Γₜ} → PfVar Γₜ Γₚ A → PfVar Γₜ (Γₚ ▹p⁰ B) A
                                                                
  data Pf : (Γₜ : Cont) → (Γₚ : Conp Γₜ) → For Γₜ → Prop₁ where
    var : {A : For Γₜ} → PfVar Γₜ Γₚ A → Pf Γₜ Γₚ A
    app : {A B : For Γₜ} → Pf Γₜ Γₚ (A ⇒ B) → Pf Γₜ Γₚ A → Pf Γₜ Γₚ B
    lam : {A B : For Γₜ} → Pf Γₜ (Γₚ ▹p⁰ A) B → Pf Γₜ Γₚ (A ⇒ B)
    p∀∀e : {A : For (Γₜ ▹t⁰)} → {t : Tm Γₜ} → Pf Γₜ Γₚ (∀∀ A) → Pf Γₜ Γₚ (A [ idₜ ,ₜ t ]f)
    p∀∀i : {A : For (Γₜ ▹t⁰)} → Pf (Γₜ ▹t⁰) (Γₚ ▹tp) A → Pf Γₜ Γₚ (∀∀ A)


  



  

  -- We now can create Renamings, a subcategory from (Conp,Subp) that
  -- A renaming from a context Γₚ to a context Δₚ means that when they are seen as lists,
  -- that every element of Γₚ is an element of Δₚ
  -- In other words, we can prove Γₚ from Δₚ using only proof variables (var)
  data Ren : Conp Γₜ → Conp Γₜ → Set₁ where
    zeroRen : Ren ◇p Γₚ
    leftRen : {A : For Δₜ} → PfVar Δₜ Δₚ A → Ren Δₚ' Δₚ → Ren (Δₚ' ▹p⁰ A) Δₚ
    
  -- We now show how we can extend renamings
  rightRen :{A : For Δₜ} → Ren Γₚ Δₚ → Ren Γₚ (Δₚ ▹p⁰ A)
  rightRen zeroRen = zeroRen
  rightRen (leftRen x h) = leftRen (pvnext x) (rightRen h)
  bothRen : {A : For Γₜ} → Ren Γₚ Δₚ → Ren (Γₚ ▹p⁰ A) (Δₚ ▹p⁰ A)
  bothRen zeroRen = leftRen pvzero zeroRen
  bothRen (leftRen x h) = leftRen pvzero (leftRen (pvnext x) (rightRen h))
  reflRen : Ren Γₚ Γₚ
  reflRen {Γₚ = ◇p} = zeroRen
  reflRen {Γₚ = Γₚ ▹p⁰ x} = bothRen reflRen

  -- We can extend renamings with term variables
  PfVar▹tp : {A : For Δₜ} → PfVar Δₜ Δₚ A → PfVar (Δₜ ▹t⁰) (Δₚ ▹tp) (A [ wkₜσₜ idₜ ]f)
  PfVar▹tp pvzero = pvzero
  PfVar▹tp (pvnext x) = pvnext (PfVar▹tp x)
  Ren▹tp : Ren Γₚ Δₚ → Ren (Γₚ ▹tp) (Δₚ ▹tp)
  Ren▹tp zeroRen = zeroRen
  Ren▹tp (leftRen x s) = leftRen (PfVar▹tp x) (Ren▹tp s)

  -- Renamings can be used to (strongly) weaken proofs
  wkᵣpv : {A : For Δₜ} → Ren Δₚ' Δₚ → PfVar Δₜ Δₚ' A → PfVar Δₜ Δₚ A
  wkᵣpv (leftRen x x₁) pvzero = x
  wkᵣpv (leftRen x x₁) (pvnext s) = wkᵣpv x₁ s
  wkᵣp : {A : For Δₜ} → Ren Δₚ Δₚ' → Pf Δₜ Δₚ A → Pf Δₜ Δₚ' A
  wkᵣp s (var pv) = var (wkᵣpv s pv)
  wkᵣp s (app pf pf₁) = app (wkᵣp s pf) (wkᵣp s pf₁)
  wkᵣp s (lam {A = A} pf) = lam (wkᵣp (bothRen s) pf)
  wkᵣp s (p∀∀e pf) = p∀∀e (wkᵣp s pf)
  wkᵣp s (p∀∀i pf) = p∀∀i (wkᵣp (Ren▹tp s) pf)


  -- But we need something stronger than just renamings
  -- introducing: Proof substitutions
  -- They are basicly a list of proofs for the formulæ contained in
  -- the goal context.
  -- It is not defined between all contexts, only those with the same term context
  data Subp : {Δₜ : Cont} → Conp Δₜ → Conp Δₜ → Set₁ where
    εₚ : Subp Δₚ ◇p
    _,ₚ_ : {A : For Δₜ} → (σ : Subp Δₚ Δₚ') → Pf Δₜ Δₚ A → Subp Δₚ (Δₚ' ▹p⁰ A)
  -- They are indeed stronger than renamings
  Ren→Sub : Ren Δₚ Δₚ' → Subp {Δₜ} Δₚ' Δₚ
  Ren→Sub zeroRen = εₚ
  Ren→Sub (leftRen x s) = Ren→Sub s ,ₚ var x


  -- From a substition into n variables, we get a substitution into n+1 variables which don't use the last one
  wkₚσₚ : {Δₜ : Cont} {Δₚ Γₚ : Conp Δₜ}{A : For Δₜ} → Subp {Δₜ} Δₚ Γₚ → Subp {Δₜ} (Δₚ ▹p⁰ A) Γₚ
  wkₚσₚ εₚ = εₚ
  wkₚσₚ (σₚ ,ₚ pf) = (wkₚσₚ σₚ) ,ₚ wkᵣp (rightRen reflRen) pf
  
  -- From a substitution into n variables, we construct a substitution from n+1 variables to n+1 variables which maps it to itself
  -- i.e. 0 -> 0 and for all i ->(old) σ(i) we get i+1 -> σ(i)+1
  lfₚσₚ : {Δₜ : Cont}{Δₚ Γₚ : Conp Δₜ}{A : For Δₜ} → Subp {Δₜ} Δₚ Γₚ → Subp {Δₜ} (Δₚ ▹p⁰ A) (Γₚ ▹p⁰ A)
  lfₚσₚ σ = (wkₚσₚ σ) ,ₚ (var pvzero)

  
  





  _[_]pvₜ : {A : For Δₜ} → PfVar Δₜ Δₚ A → (σ : Subt Γₜ Δₜ) → PfVar Γₜ (Δₚ [ σ ]c) (A [ σ ]f)
  pvzero [ σ ]pvₜ = pvzero
  pvnext pv [ σ ]pvₜ = pvnext (pv [ σ ]pvₜ)
  _[_]pₜ : {A : For Δₜ} → Pf Δₜ Δₚ A → (σ : Subt Γₜ Δₜ) → Pf Γₜ (Δₚ [ σ ]c) (A [ σ ]f)
  var pv [ σ ]pₜ = var (pv [ σ ]pvₜ)
  app pf pf' [ σ ]pₜ = app (pf [ σ ]pₜ) (pf' [ σ ]pₜ)
  lam pf [ σ ]pₜ = lam (pf [ σ ]pₜ)
  _[_]pₜ {Δₚ = Δₚ} {Γₜ = Γₜ} (p∀∀e {A = A} {t = t} pf) σ = substP (λ F → Pf Γₜ (Δₚ [ σ ]c) F) (≡tran² (≡sym []f-∘) (cong (λ σ → A [ σ ]f) (cong₂ _,ₜ_ (≡tran² wkₜ∘ₜ,ₜ idrₜ (≡sym idlₜ)) refl)) ([]f-∘)) (p∀∀e {t = t [ σ ]t} (pf [ σ ]pₜ))
  _[_]pₜ {Γₜ = Γₜ} (p∀∀i pf) σ = p∀∀i (substP (λ Ξₚ → Pf (Γₜ ▹t⁰) (Ξₚ) _) ▹tp-lfₜ (pf [ lfₜσₜ σ ]pₜ))
  
  _[_]σₚ : Subp {Δₜ} Δₚ Δₚ' → (σ : Subt Γₜ Δₜ) → Subp {Γₜ} (Δₚ [ σ ]c) (Δₚ' [ σ ]c)
  εₚ [ σₜ ]σₚ = εₚ
  (σₚ ,ₚ pf) [ σₜ ]σₚ = (σₚ [ σₜ ]σₚ) ,ₚ (pf [ σₜ ]pₜ)

  wkₜσₚ : Subp {Δₜ} Δₚ' Δₚ → Subp {Δₜ ▹t⁰} (Δₚ' ▹tp) (Δₚ ▹tp)
  wkₜσₚ εₚ = εₚ
  wkₜσₚ {Δₜ = Δₜ} (_,ₚ_ {A = A} σₚ pf) = (wkₜσₚ σₚ) ,ₚ substP (λ Ξₚ → Pf (Δₜ ▹t⁰) Ξₚ (A [ wkₜσₜ idₜ ]f)) refl (_[_]pₜ {Γₜ = Δₜ ▹t⁰} pf (wkₜσₜ idₜ))
  wkₚ[] : {σₜ : Subt Γₜ Δₜ} {σₚ : Subp Δₚ Δₚ'} {A : For Δₜ} → (wkₚσₚ {A = A} σₚ) [ σₜ ]σₚ ≡ wkₚσₚ (σₚ [ σₜ ]σₚ)
  wkₚ[] {σₚ = εₚ} = refl
  wkₚ[] {σₚ = σₚ ,ₚ x} = cong (λ ξ → ξ ,ₚ _) (wkₚ[] {σₚ = σₚ})

  _[_]p : {A : For Δₜ} → Pf Δₜ Δₚ A → (σ : Subp {Δₜ} Δₚ' Δₚ) → Pf Δₜ Δₚ' A
  var pvzero [ σ ,ₚ pf ]p = pf
  var (pvnext pv) [ σ ,ₚ pf ]p = var pv [ σ ]p
  app pf pf₁ [ σ ]p = app (pf [ σ ]p) (pf₁ [ σ ]p)
  lam pf [ σ ]p = lam (pf [ wkₚσₚ σ ,ₚ var pvzero ]p) 
  p∀∀e pf [ σ ]p = p∀∀e (pf [ σ ]p)
  p∀∀i pf [ σ ]p = p∀∀i (pf [ wkₜσₚ σ ]p)







  -- We can now define identity and composition on proof substitutions
  idₚ : Subp {Δₜ} Δₚ Δₚ
  idₚ {Δₚ = ◇p} = εₚ
  idₚ {Δₚ = Δₚ ▹p⁰ x} = lfₚσₚ (idₚ {Δₚ = Δₚ})
  _∘ₚ_ : {Γₚ Δₚ Ξₚ : Conp Δₜ} → Subp {Δₜ} Δₚ Ξₚ → Subp {Δₜ} Γₚ Δₚ → Subp {Δₜ} Γₚ Ξₚ
  εₚ ∘ₚ β = εₚ
  (α ,ₚ pf) ∘ₚ β = (α ∘ₚ β) ,ₚ (pf [ β ]p)

  -- And now we have to show all their equalities
  
  idₚ[] : {σₜ : Subt Γₜ Δₜ} → ((idₚ {Δₜ} {Δₚ}) [ σₜ ]σₚ) ≡ idₚ {Γₜ} {Δₚ [ σₜ ]c}
  idₚ[] {Δₚ = ◇p} = refl
  idₚ[] {Δₚ = Δₚ ▹p⁰ A} = cong (λ ξ → ξ ,ₚ var pvzero) (≡tran wkₚ[] (cong wkₚσₚ idₚ[]))

  -- Cancelling a wkₚσₚ with a ,ₚ
  wkₚ∘, : {Δₜ : Cont}{Γₚ Δₚ Ξₚ : Conp Δₜ}{α : Subp {Δₜ} Γₚ Δₚ}{β : Subp {Δₜ} Ξₚ Γₚ}{A : For Δₜ}{pf : Pf Δₜ Ξₚ A} → (wkₚσₚ α) ∘ₚ (β ,ₚ pf) ≡ (α ∘ₚ β)
  wkₚ∘, {α = εₚ} = refl
  wkₚ∘, {α = α ,ₚ pf} {β = β} {pf = pf'} = cong (λ ξ → ξ ,ₚ (pf [ β ]p)) wkₚ∘,

  -- Categorical rules
  idlₚ : {Γₚ Δₚ : Conp Γₜ} {σₚ : Subp Γₚ Δₚ} → (idₚ {Δₚ = Δₚ}) ∘ₚ σₚ ≡ σₚ
  idlₚ {Δₚ = ◇p} {εₚ} = refl
  idlₚ {Δₚ = Δₚ ▹p⁰ pf} {σₚ ,ₚ pf'} = cong (λ ξ → ξ ,ₚ pf') (≡tran wkₚ∘, (idlₚ {σₚ = σₚ}))
  idrₚ : {Γₚ Δₚ : Conp Γₜ} {σₚ : Subp Γₚ Δₚ} →  σₚ ∘ₚ (idₚ {Δₚ = Γₚ}) ≡ σₚ
  idrₚ {σₚ = εₚ} = refl
  idrₚ {σₚ = σₚ ,ₚ prf} = cong (λ X → X ,ₚ prf) (idrₚ {σₚ = σₚ})
  ∘ₚ-ass : {Γₚ Δₚ Ξₚ Ψₚ : Conp Γₜ}{αₚ : Subp Γₚ Δₚ}{βₚ : Subp Δₚ Ξₚ}{γₚ : Subp Ξₚ Ψₚ} → (γₚ ∘ₚ βₚ) ∘ₚ αₚ ≡ γₚ ∘ₚ (βₚ ∘ₚ αₚ)
  ∘ₚ-ass {γₚ = εₚ} = refl
  ∘ₚ-ass {αₚ = αₚ} {βₚ} {γₚ ,ₚ x} = cong (λ ξ → ξ ,ₚ (x [ βₚ ∘ₚ αₚ ]p)) ∘ₚ-ass

  -- Unicity of the terminal morphism
  εₚ-u : {Γₚ : Conp Γₜ} → {σ : Subp Γₚ ◇p} → σ ≡ εₚ {Δₚ = Γₚ}
  εₚ-u {σ = εₚ} = refl

  -- Term substitution for proof substitutions
  []σₚ-id : {σₚ : Subp {Δₜ} Δₚ Δₚ'} → coe (cong₂ Subp []c-id []c-id) (σₚ [ idₜ ]σₚ) ≡ σₚ
  []σₚ-id {σₚ = εₚ} = εₚ-u
  []σₚ-id {Δₜ}{Δₚ}{Δₚ' ▹p⁰ A} {σₚ = σₚ ,ₚ x} =
    substP (λ ξ → coe (cong₂ Subp []c-id []c-id) (ξ ,ₚ (x [ idₜ ]pₜ)) ≡ (σₚ ,ₚ x))
    (≡sym (coeshift []σₚ-id))
    (≡sym (coeshift {eq = cong₂ Subp (≡sym []c-id) (≡sym []c-id)}
    (substfpoly⁴
      {A = ((Conp Δₜ) × (Conp Δₜ)) × (For Δₜ)}
      {P = λ W → Subp (proj×₁ (proj×₁ W)) ((proj×₂ (proj×₁ W)) ▹p⁰ (proj×₂ W))}
      {R = λ W → Subp (proj×₁ (proj×₁ W)) (proj×₂ (proj×₁ W))}
      {Q = λ W → Pf Δₜ (proj×₁ (proj×₁ W)) (proj×₂ W)}
      {α = (Δₚ ,× Δₚ') ,× A}
      {eq = ×≡ (×≡ (≡sym []c-id) (≡sym []c-id)) (≡sym []f-id)}
      {f = λ {W} ξ pf → _,ₚ_ ξ pf}{x = σₚ}{y = x}
    )))
    
  []σₚ-∘ : {Ξₚ Ξₚ' : Conp Ξₜ}{α : Subt Δₜ Ξₜ} {β : Subt Γₜ Δₜ} {σₚ : Subp {Ξₜ} Ξₚ Ξₚ'}
    → coe (cong₂ Subp (≡sym []c-∘) (≡sym []c-∘)) ((σₚ [ α ]σₚ) [ β ]σₚ) ≡ σₚ [ α ∘ₜ β ]σₚ 
  []σₚ-∘ {σₚ = εₚ} = εₚ-u
  []σₚ-∘ {Ξₜ}{Δₜ}{Γₜ}{Ξₚ}{Δₚ' ▹p⁰ A}{α}{β}{σₚ = σₚ ,ₚ pf} =
    substP (λ ξ → coe (cong₂ Subp (≡sym []c-∘) (≡sym []c-∘)) (ξ ,ₚ ((pf [ α ]pₜ) [ β ]pₜ)) ≡ ((σₚ [ α ∘ₜ β ]σₚ) ,ₚ (pf [ α ∘ₜ β ]pₜ))) (≡sym (coeshift []σₚ-∘))
    (≡sym (coeshift {eq = cong₂ Subp []c-∘ []c-∘}
    (substfpoly⁴
      {A = ((Conp Γₜ) × (Conp Γₜ)) × (For Γₜ)}
      {P = λ W → Subp (proj×₁ (proj×₁ W)) ((proj×₂ (proj×₁ W)) ▹p⁰ (proj×₂ W))}
      {R = λ W → Subp (proj×₁ (proj×₁ W)) (proj×₂ (proj×₁ W))}
      {Q = λ W → Pf Γₜ (proj×₁ (proj×₁ W)) (proj×₂ W)}
      {eq = ×≡ (×≡ []c-∘ []c-∘) []f-∘}
      {f = λ {W} ξ pf → _,ₚ_ ξ pf}{x = σₚ [ α ∘ₜ β ]σₚ}{y = pf [ α ∘ₜ β ]pₜ})
    ))

  -- How ∘ₚ and ∘ₜ interact to make associativity (to be proven later for Sub)
  
  ∘ₚₜ-ass⁰ :
    {Γₜ Δₜ : Cont}{Γₚ : Conp Γₜ}{Δₚ : Conp Δₜ}{Ξₚ : Conp Δₜ}{Ψₚ : Conp Δₜ}
    {αₜ : Subt Γₜ Δₜ}{γₚ : Subp Ξₚ Ψₚ}{βₚ : Subp Δₚ Ξₚ}{αₚ : Subp Γₚ (Δₚ [ αₜ ]c)}
    → ((γₚ ∘ₚ βₚ) [ αₜ ]σₚ) ∘ₚ αₚ ≡ (γₚ [ αₜ ]σₚ) ∘ₚ ((βₚ [ αₜ ]σₚ) ∘ₚ αₚ)
  ∘ₚₜ-ass⁰ {γₚ = εₚ} = refl
  ∘ₚₜ-ass⁰ {αₜ = αₜ}{γₚ ,ₚ x}{βₚ}{αₚ} = cong (λ ξ → ξ ,ₚ (((x [ βₚ ]p) [ αₜ ]pₜ) [ αₚ ]p)) (∘ₚₜ-ass⁰ {γₚ = γₚ})
  
  ∘ₚₜ-ass : 
    {Γₜ Δₜ Ξₜ Ψₜ : Cont}{Γₚ : Conp Γₜ}{Δₚ : Conp Δₜ}{Ξₚ : Conp Ξₜ}{Ψₚ : Conp Ψₜ}
    {αₜ : Subt Γₜ Δₜ}{βₜ : Subt Δₜ Ξₜ}{γₜ : Subt Ξₜ Ψₜ}{γₚ : Subp Ξₚ (Ψₚ [ γₜ ]c)}{βₚ : Subp Δₚ (Ξₚ [ βₜ ]c)}{αₚ : Subp Γₚ (Δₚ [ αₜ ]c)}
    {eq₁ : Subp Γₚ (Ψₚ [ (γₜ ∘ₜ βₜ) ∘ₜ αₜ ]c) ≡ Subp Γₚ (Ψₚ [ γₜ ∘ₜ (βₜ ∘ₜ αₜ) ]c)}
    {eq₂ : Subp (Δₚ [ αₜ ]c) ((Ψₚ [ γₜ ∘ₜ βₜ ]c) [ αₜ ]c) ≡ Subp (Δₚ [ αₜ ]c) (Ψₚ [ (γₜ ∘ₜ βₜ) ∘ₜ αₜ ]c)}
    {eq₃ : Subp (Ξₚ [ βₜ ∘ₜ αₜ ]c) ((Ψₚ [ γₜ ]c) [ βₜ ∘ₜ αₜ ]c) ≡ Subp (Ξₚ [ βₜ ∘ₜ αₜ ]c) (Ψₚ [ γₜ ∘ₜ (βₜ ∘ₜ αₜ) ]c)}
    {eq₄ : Subp (Δₚ [ αₜ ]c) ((Ξₚ [ βₜ ]c) [ αₜ ]c) ≡ Subp (Δₚ [ αₜ ]c) (Ξₚ [ βₜ ∘ₜ αₜ ]c)}
    {eq₅ : Subp (Ξₚ [ βₜ ]c) ((Ψₚ [ γₜ ]c) [ βₜ ]c) ≡ Subp (Ξₚ [ βₜ ]c) (Ψₚ [ γₜ ∘ₜ βₜ ]c)}
    → coe eq₁ ((coe eq₂ (((coe eq₅ (γₚ [ βₜ ]σₚ)) ∘ₚ βₚ) [ αₜ ]σₚ)) ∘ₚ αₚ) ≡ (coe eq₃ (γₚ [ βₜ ∘ₜ αₜ ]σₚ)) ∘ₚ ((coe eq₄ (βₚ [ αₜ ]σₚ)) ∘ₚ αₚ)
  ∘ₚₜ-ass {Γₜ}{Δₜ}{Ξₜ}{Ψₜ}{Γₚ}{Δₚ}{Ξₚ}{Ψₚ}{αₜ = αₜ}{βₜ}{γₜ}{γₚ}{βₚ}{αₚ}{eq₁}{eq₂}{eq₃}{eq₄}{eq₅} =
    substP (λ X → coe eq₁ ((coe eq₂ (((coe eq₅ (γₚ [ βₜ ]σₚ)) ∘ₚ βₚ) [ αₜ ]σₚ)) ∘ₚ αₚ) ≡ (coe eq₃ X) ∘ₚ ((coe eq₄ (βₚ [ αₜ ]σₚ)) ∘ₚ αₚ)) []σₚ-∘ (
    ≡tran⁵
    (cong (coe eq₁) (≡tran (
      ≡sym (substfpoly
        {R = λ X → Subp (Δₚ [ αₜ ]c) X}
        {eq = ≡sym []c-∘}
        {f = λ ξ → ξ ∘ₚ αₚ}
        {x = ((coe eq₅ (γₚ [ βₜ ]σₚ)) ∘ₚ βₚ) [ αₜ ]σₚ}))
      (cong (coe (cong (λ z → Subp Γₚ z) (≡sym []c-∘)))
      (≡sym (substfpoly
        {R = λ X → Subp (Ξₚ [ βₜ ]c) X}
        {eq = ≡sym []c-∘}
        {f = λ ξ → ((ξ ∘ₚ βₚ) [ αₜ ]σₚ) ∘ₚ αₚ}
        {x = γₚ [ βₜ ]σₚ}
      )))
      ))
    (≡tran coecoe-coe coecoe-coe)
    (cong (coe  (≡tran (cong (λ z → Subp Γₚ (z [ αₜ ]c)) (≡sym []c-∘)) (≡tran (cong (λ z → Subp Γₚ z) (≡sym []c-∘)) eq₁))) ∘ₚₜ-ass⁰)
    (≡sym coecoe-coe)
    (cong (coe (cong (λ z → Subp Γₚ z) (≡sym []c-∘))) (substppoly
      {A = (Conp Γₜ) × (Conp Γₜ)}
      {R = λ W → Subp (proj×₁ W) (proj×₂ W)}
      {Q = λ W → Subp (Δₚ [ αₜ ]c) (proj×₁ W)}
      {eq = ×≡ (≡sym []c-∘) (≡sym []c-∘)}
      {f = λ x y → x ∘ₚ (y ∘ₚ αₚ)}
      {x = (γₚ [ βₜ ]σₚ) [ αₜ ]σₚ}
      {y = βₚ [ αₜ ]σₚ}
    ))(substfpoly
      {R = λ X → Subp (Ξₚ [ βₜ ∘ₜ αₜ ]c) X}
      {eq = ≡sym []c-∘}
      {f = λ {τ} ξ → (ξ ∘ₚ ((coe eq₄ (βₚ [ αₜ ]σₚ)) ∘ₚ αₚ))}
      {x = (coe (cong₂ Subp (≡sym []c-∘) (≡sym []c-∘)) ((γₚ [ βₜ ]σₚ) [ αₜ ]σₚ))}
    ))












  -- We can now merge the two notions of contexts, substitutions, and everything
  record Con : Set₁ where
    constructor con
    field
      t : Cont
      p : Conp t
      
  variable
    Γ Δ Ξ : Con
    
  record Sub (Γ : Con) (Δ : Con) : Set₁ where
    constructor sub
    field
      t : Subt (Con.t Γ) (Con.t Δ)
      p : Subp {Con.t Γ} (Con.p Γ) ((Con.p Δ) [ t ]c)

  -- (Con,Sub) is a category with an initial object
  id : Sub Γ Γ
  id {Γ} = sub idₜ (subst (Subp _) (≡sym []c-id) idₚ)
  _∘_ : Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
  sub αₜ αₚ ∘ sub βₜ βₚ = sub (αₜ ∘ₜ βₜ) (subst (Subp _) (≡sym []c-∘) (αₚ [ βₜ ]σₚ) ∘ₚ βₚ)
  idl : {Γ Δ : Con} {σ : Sub Γ Δ} →  (id {Δ}) ∘ σ ≡ σ
  idl {Δ = Δ} {σ = sub σₜ σₚ} =
    cong₂' sub idlₜ (≡tran²
    (substfpoly
      {α = ((Con.p Δ) [ idₜ ∘ₜ σₜ ]c)}
      {β = ((Con.p Δ) [ σₜ ]c)}
      {eq = cong (λ ξ → Con.p Δ [ ξ ]c) idlₜ}
      {f = λ {Ξₚ} ξ → _∘ₚ_ {Ξₚ = Ξₚ} ξ σₚ}
    ) (
    cong₂ _∘ₚ_ (≡tran³
      coecoe-coe
      (substfpoly
        {eq = []c-id}
        {f = λ {Ξₚ} ξ → _[_]σₚ {Δₚ = Con.p Δ} {Δₚ' = Ξₚ} ξ σₜ}
      )
      (cong (λ ξ → ξ [ σₜ ]σₚ) coeaba)
      idₚ[]
    ) refl)
    idlₚ)
  idr : {Γ Δ : Con} {σ : Sub Γ Δ} →  σ ∘ (id {Γ}) ≡ σ
  idr {Γ} {Δ} {σ = sub σₜ σₚ} =
    cong₂' sub idrₜ (≡tran⁴
      (cong (coe _) (≡sym (
        substfpoly
        {eq = ≡sym ([]c-∘ {α = σₜ} {β = idₜ}{Ξₚ = Con.p Δ})}
        {f = λ {Ξₚ} ξ → _∘ₚ_ {Ξₚ = Ξₚ} ξ (coe (cong (Subp (Con.p Γ)) (≡sym []c-id)) idₚ)}
        {x = σₚ [ idₜ ]σₚ})))
      coecoe-coe
      (substP
          (λ X → coe  (≡tran (cong (Subp (Con.p Γ)) (≡sym []c-∘))
          (cong (λ z → Subp (Con.p Γ) (Con.p Δ [ z ]c)) idrₜ))
          (X ∘ₚ coe (cong (Subp (Con.p Γ)) (≡sym []c-id)) idₚ)
          ≡ (coe (cong₂ Subp []c-id []c-id) (σₚ [ idₜ ]σₚ) ∘ₚ idₚ))
      ((coeaba {eq1 = (cong₂ Subp []c-id []c-id)}{eq2 = ≡sym (cong₂ Subp []c-id []c-id)}))
      ((coep∘
        {p = λ {Γₚ}{Δₚ}{Ξₚ} x y → _∘ₚ_ {Δₚ = Γₚ} x y}
        {eq1 = refl}
        {eq2 = ≡sym []c-id}
        {eq3 = ≡sym []c-id}
      )))
      idrₚ
      []σₚ-id)
  ∘-ass : {Γ Δ Ξ Ψ : Con}{α : Sub Γ Δ}{β : Sub Δ Ξ}{γ : Sub Ξ Ψ} → (γ ∘ β) ∘ α ≡ γ ∘ (β ∘ α)
  ∘-ass {Γ}{Δ}{Ξ}{Ψ}{α = sub αₜ αₚ} {β = sub βₜ βₚ} {γ = sub γₜ γₚ} = cong₂' sub ∘ₜ-ass ∘ₚₜ-ass

  ◇ : Con
  ◇ = con ◇t ◇p


  -- We have our two context extension operators
  _▹t : Con → Con
  Γ ▹t = con ((Con.t Γ) ▹t⁰) (Con.p Γ ▹tp)
  _▹p_ : (Γ : Con) → For (Con.t Γ) → Con
  Γ ▹p A = con (Con.t Γ) (Con.p Γ ▹p⁰ A)


  

  -- We define the access function from the algebra, but defined for fully-featured substitutions
  -- For term substitutions
  πₜ¹* : {Γ Δ : Con} → Sub Δ (Γ ▹t) → Sub Δ Γ
  πₜ¹* (sub (σₜ ,ₜ t) σₚ) = sub σₜ (subst (Subp _) ▹tp,ₜ σₚ)
  πₜ²* : {Γ Δ : Con} → Sub Δ (Γ ▹t) → Tm (Con.t Δ)
  πₜ²* (sub (σₜ ,ₜ t) σₚ) = t
  _,ₜ*_ : {Γ Δ : Con} → Sub Δ Γ → Tm (Con.t Δ) → Sub Δ (Γ ▹t)
  (sub σₜ σₚ) ,ₜ* t = sub (σₜ ,ₜ t) (subst (Subp _) (≡sym ▹tp,ₜ) σₚ)
  -- And the equations
  πₜ²∘,ₜ* : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm (Con.t Δ)} → πₜ²* (σ ,ₜ* t) ≡ t
  πₜ²∘,ₜ* = refl
  πₜ¹∘,ₜ* : {Γ Δ : Con} → {σ : Sub Δ Γ} → {t : Tm (Con.t Δ)} → πₜ¹* (σ ,ₜ* t) ≡ σ
  πₜ¹∘,ₜ* {Γ}{Δ}{σ}{t} = cong (sub (Sub.t σ)) coeaba
  ,ₜ∘πₜ* : {Γ Δ : Con} → {σ : Sub Δ (Γ ▹t)} → (πₜ¹* σ) ,ₜ* (πₜ²* σ) ≡ σ
  ,ₜ∘πₜ* {Γ} {Δ} {sub (σₜ ,ₜ t) σₚ} = cong (sub (σₜ ,ₜ t)) coeaba
  ,ₜ∘* : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{t : Tm (Con.t Γ)} → (σ ,ₜ* t) ∘ δ ≡ (σ ∘ δ) ,ₜ* (t [ Sub.t δ ]t)
  ,ₜ∘* {Γ} {Δ} {Ξ} {sub σₜ σₚ} {sub δₜ δₚ} {t} = cong (sub ((σₜ ∘ₜ δₜ) ,ₜ (t [ δₜ ]t)))
    (substfgpoly
      {P = Subp {Con.t Δ} (Con.p Δ)}
      {Q = Subp {Con.t Δ} ((Con.p Γ) [ δₜ ]c)}
      {R = Subp {Con.t Γ} (Con.p Γ)}
      {F = λ X → X [ δₜ ]c}
      {eq₁ = ≡sym ▹tp,ₜ}
      {eq₂ = ≡sym []c-∘}
      {eq₃ = ≡sym []c-∘}
      {eq₄ = ≡sym ▹tp,ₜ}
      {g = λ σₚ → σₚ ∘ₚ δₚ}
      {f = λ σₚ → σₚ [ δₜ ]σₚ}
      {x = σₚ})

  -- And for proof substitutions
  πₚ¹* : {Γ Δ : Con} {A : For (Con.t Γ)} → Sub Δ (Γ ▹p A) → Sub Δ Γ
  πₚ¹* (sub σₜ (σₚ ,ₚ pf)) = sub σₜ σₚ
  πₚ²* : {Γ Δ : Con} {F : For (Con.t Γ)} (σ : Sub Δ (Γ ▹p F)) → Pf (Con.t Δ) (Con.p Δ) (F [ Sub.t (πₚ¹* σ) ]f)
  πₚ²* (sub σₜ (σₚ ,ₚ pf)) = pf
  _,ₚ*_ : {Γ Δ : Con} {F : For (Con.t Γ)} (σ : Sub Δ Γ) → Pf (Con.t Δ) (Con.p Δ) (F [ Sub.t σ ]f) → Sub Δ (Γ ▹p F)
  sub σₜ σₚ ,ₚ* pf = sub σₜ (σₚ ,ₚ pf)
  -- And the equations
  ,ₚ∘πₚ : {Γ Δ : Con} → {F : For (Con.t Γ)} → {σ : Sub Δ (Γ ▹p F)} → (πₚ¹* σ) ,ₚ* (πₚ²* σ) ≡ σ
  ,ₚ∘πₚ {σ = sub σₜ (σₚ ,ₚ p)} = refl
  ,ₚ∘ : {Γ Δ Ξ : Con}{σ : Sub Γ Ξ}{δ : Sub Δ Γ}{F : For (Con.t Ξ)}{prf : Pf (Con.t Γ) (Con.p Γ) (F [ Sub.t σ ]f)}
      → (σ ,ₚ* prf) ∘ δ ≡ (σ ∘ δ) ,ₚ* (substP (λ F → Pf (Con.t Δ) (Con.p Δ) F) (≡sym []f-∘) ((prf [ Sub.t δ ]pₜ) [ Sub.p δ ]p))
  ,ₚ∘ {Γ}{Δ}{Ξ}{σ = sub σₜ σₚ} {sub δₜ δₚ} {F = A} {prf} =
    cong (λ ξ → sub (σₜ ∘ₜ δₜ) (ξ ∘ₚ δₚ)) (
    substfpoly⁴
      {P = λ W → Subp (Con.p Γ [ δₜ ]c) ((proj×₁ W) ▹p⁰ (proj×₂ W))}
      {R = λ W → Subp (Con.p Γ [ δₜ ]c) (proj×₁ W)}
      {Q = λ W → Pf (Con.t Δ) (Con.p Γ [ δₜ ]c) (proj×₂ W)}
      {α = ((Con.p Ξ [ σₜ ]c) [ δₜ ]c) ,× ((A [ σₜ ]f) [ δₜ ]f)}
      {eq = cong₂ _,×_ (≡sym []c-∘) (≡sym []f-∘)}
      {f = λ ξ p → ξ ,ₚ p}
      {x = σₚ [ δₜ ]σₚ}{y = prf [ δₜ ]pₜ}
    ) 
  
  
  lemD : {A : For (Con.t Γ)}{σ : Sub Δ (Γ ▹p A)} → Sub.t (πₚ¹* σ) ≡ Sub.t σ
  lemD {σ = sub σₜ (σₚ ,ₚ pf)} = refl


  -- and FINALLY, we compile everything into an implementation of the FFOL record
    
  ffol : FFOL {lsuc lzero} {lsuc lzero} {lsuc lzero} {lsuc lzero}
  ffol = record
    { Con = Con
    ; Sub = Sub
    ; _∘_ = _∘_
    ; ∘-ass = ∘-ass
    ; id = id
    ; idl = idl
    ; idr = idr
    ; ◇ = ◇
    ; ε = sub εₜ εₚ
    ; ε-u = cong₂' sub εₜ-u εₚ-u
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
    ; R = R
    ; R[] = refl
    ; _⊢_ = λ Γ A → Pf (Con.t Γ) (Con.p Γ) A
    ; _[_]p = λ pf σ → (pf [ Sub.t σ ]pₜ) [ Sub.p σ ]p
    ; _▹ₚ_ = _▹p_
    ; πₚ¹ = πₚ¹*
    ; πₚ² = πₚ²*
    ; _,ₚ_ = _,ₚ*_
    ; ,ₚ∘πₚ = ,ₚ∘πₚ
    ; πₚ¹∘,ₚ = refl
    ; ,ₚ∘ = λ {Γ}{Δ}{Ξ}{σ}{δ}{F}{prf} → ,ₚ∘ {prf = prf}
    ; _⇒_ = _⇒_
    ; []f-⇒ = refl
    ; ∀∀ = ∀∀
    ; []f-∀∀ = []f-∀∀
    ; lam = λ {Γ}{F}{G} pf → substP (λ H → Pf (Con.t Γ) (Con.p Γ) (F ⇒ H)) (≡tran (cong (_[_]f G) (lemD {σ = id})) []f-id) (lam pf)
    ; app = app
    ; ∀i = p∀∀i
    ; ∀e = λ {Γ} {F} pf {t} → p∀∀e pf
    }


  -- We define normal and neutral forms
  data Ne : (Γₜ : Cont) → (Γₚ : Conp Γₜ) → For Γₜ → Prop₁
  data Nf : (Γₜ : Cont) → (Γₚ : Conp Γₜ) → For Γₜ → Prop₁
  data Ne where
    var : {A : For Γₜ} → PfVar Γₜ Γₚ A → Ne Γₜ Γₚ A
    app : {A B : For Γₜ} → Ne Γₜ Γₚ (A ⇒ B) → Nf Γₜ Γₚ A → Ne Γₜ Γₚ B
    p∀∀e : {A : For (Γₜ ▹t⁰)} → {t : Tm Γₜ} → Ne Γₜ Γₚ (∀∀ A) → Ne Γₜ Γₚ (A [ idₜ ,ₜ t ]f)
  data Nf where
    R : {t u : Tm Γₜ} → Ne Γₜ Γₚ (R t u) → Nf Γₜ Γₚ (R t u)
    lam : {A B : For Γₜ} → Nf Γₜ (Γₚ ▹p⁰ A) B → Nf Γₜ Γₚ (A ⇒ B)
    p∀∀i : {A : For (Γₜ ▹t⁰)} → Nf (Γₜ ▹t⁰) (Γₚ ▹tp) A → Nf Γₜ Γₚ (∀∀ A)


  Pf* : (Γₜ : Cont) → Conp Γₜ → Conp Γₜ → Prop₁
  Pf* Γₜ Γₚ ◇p = ⊤
  Pf* Γₜ Γₚ (Γₚ' ▹p⁰ A) = (Pf* Γₜ Γₚ Γₚ') ∧ (Pf Γₜ Γₚ A)

  Sub→Pf* : {Γₜ : Cont} {Γₚ Γₚ' : Conp Γₜ} →  Subp {Γₜ} Γₚ Γₚ' → Pf* Γₜ Γₚ Γₚ'
  Sub→Pf* εₚ = tt
  Sub→Pf* (σₚ ,ₚ pf) = ⟨ (Sub→Pf* σₚ) , pf ⟩
  Pf*-id : {Γₜ : Cont} {Γₚ : Conp Γₜ} → Pf* Γₜ Γₚ Γₚ
  Pf*-id = Sub→Pf* idₚ

  Pf*▹p : {Γₜ : Cont}{Γₚ Γₚ' : Conp Γₜ}{A : For Γₜ} → Pf* Γₜ Γₚ Γₚ' → Pf* Γₜ (Γₚ ▹p⁰ A) Γₚ'
  Pf*▹p {Γₚ' = ◇p} s = tt
  Pf*▹p {Γₚ' = Γₚ' ▹p⁰ x} s = ⟨ (Pf*▹p (proj₁ s)) , (wkᵣp (rightRen reflRen) (proj₂ s)) ⟩
  Pf*▹tp : {Γₜ : Cont}{Γₚ Γₚ' : Conp Γₜ} → Pf* Γₜ Γₚ Γₚ' → Pf* (Γₜ ▹t⁰) (Γₚ ▹tp) (Γₚ' ▹tp)
  Pf*▹tp {Γₚ' = ◇p} s = tt
  Pf*▹tp {Γₚ' = Γₚ' ▹p⁰ A} s = ⟨ Pf*▹tp (proj₁ s) , (proj₂ s) [ wkₜσₜ idₜ ]pₜ ⟩

  Pf*Pf : {Γₜ : Cont} {Γₚ Γₚ' : Conp Γₜ} {A : For Γₜ} → Pf* Γₜ Γₚ Γₚ' → Pf Γₜ Γₚ' A → Pf Γₜ Γₚ A
  Pf*Pf s (var pvzero) = proj₂ s
  Pf*Pf s (var (pvnext pv)) = Pf*Pf (proj₁ s) (var pv)
  Pf*Pf s (app p p') = app (Pf*Pf s p) (Pf*Pf s p')
  Pf*Pf s (lam p) = lam (Pf*Pf (⟨ (Pf*▹p s) , (var pvzero) ⟩) p)
  Pf*Pf s (p∀∀e p) = p∀∀e (Pf*Pf s p)
  Pf*Pf s (p∀∀i p) = p∀∀i (Pf*Pf (Pf*▹tp s) p)

  Pf*-∘ : {Γₜ : Cont} {Γₚ Δₚ Ξₚ : Conp Γₜ} → Pf* Γₜ Δₚ Ξₚ → Pf* Γₜ Γₚ Δₚ → Pf* Γₜ Γₚ Ξₚ
  Pf*-∘ {Ξₚ = ◇p} α β = tt
  Pf*-∘ {Ξₚ = Ξₚ ▹p⁰ A} α β = ⟨ Pf*-∘ (proj₁ α) β , Pf*Pf β (proj₂ α) ⟩


  module InitialMorphism (M : FFOL {lsuc lzero} {lsuc lzero} {lsuc lzero} {lsuc lzero} {lsuc lzero}) where
    {-# TERMINATING #-}
    mCon : Con → (FFOL.Con M)
    mFor : {Γ : Con} → (For (Con.t Γ)) → (FFOL.For M (mCon Γ))
    mTm : {Γ : Con} → (Tm (Con.t Γ)) → (FFOL.Tm M (mCon Γ))
    mSub : {Δ : Con}{Γ : Con} → Sub Δ Γ → (FFOL.Sub M (mCon Δ) (mCon Γ))
    m⊢ : {Γ : Con} {A : For (Con.t Γ)} → Pf (Con.t Γ) (Con.p Γ) A → FFOL._⊢_ M (mCon Γ) (mFor A)
    
    e▹ₜ : {Γ : Con} → mCon (con (Con.t Γ ▹t⁰) (Con.p Γ [ wkₜσₜ idₜ ]c)) ≡ FFOL._▹ₜ M (mCon Γ)
    e▹ₚ : {Γ : Con}{A : For (Con.t Γ)} → mCon (Γ ▹p A) ≡ FFOL._▹ₚ_ M (mCon Γ) (mFor A)
    e[]f : {Γ Δ : Con}{A : For (Con.t Γ)}{σ : Sub Δ Γ} → mFor (A [ Sub.t σ ]f) ≡ FFOL._[_]f M (mFor A) (mSub σ)

    mCon (con ◇t ◇p) = FFOL.◇ M
    mCon (con (Γₜ ▹t⁰) ◇p) = FFOL._▹ₜ M (mCon (con Γₜ ◇p))
    mCon (con Γₜ (Γₚ ▹p⁰ A)) = FFOL._▹ₚ_ M (mCon (con Γₜ Γₚ)) (mFor {con Γₜ Γₚ} A)
    mSub {Γ = con ◇t ◇p} (sub εₜ εₚ) = FFOL.ε M
    mSub {Γ = con (Γₜ ▹t⁰) ◇p} (sub (σₜ ,ₜ t) εₚ) = FFOL._,ₜ_ M (mSub (sub σₜ εₚ)) (mTm t)
    mSub {Δ = Δ} {Γ = con Γₜ (Γₚ ▹p⁰ A)} (sub σₜ (σₚ ,ₚ pf)) = subst (FFOL.Sub M (mCon Δ)) (≡sym e▹ₚ) (FFOL._,ₚ_ M (mSub (sub σₜ σₚ)) (substP (FFOL._⊢_ M (mCon Δ)) e[]f (m⊢ pf)))

    -- Zero is (πₜ² id)
    mTm {con (Γₜ ▹t⁰) ◇p} (var tvzero) = FFOL.πₜ² M (FFOL.id M)
    -- N+1 is wk[tm N]
    mTm {con (Γₜ ▹t⁰) ◇p} (var (tvnext tv)) = (FFOL._[_]t M (mTm (var tv)) (FFOL.πₜ¹ M (FFOL.id M)))
    -- If we have a formula in context, we proof-weaken the term (should not change a thing)
    mTm {con (Γₜ ▹t⁰) (Γₚ ▹p⁰ A)} (var tv) = FFOL._[_]t M (mTm {con (Γₜ ▹t⁰) Γₚ} (var tv)) (FFOL.πₚ¹ M (FFOL.id M))
    
    mFor (R t u) = FFOL.R M (mTm t) (mTm u)
    mFor (A ⇒ B) = FFOL._⇒_ M (mFor A) (mFor B)
    mFor {Γ} (∀∀ A) = FFOL.∀∀ M (subst (FFOL.For M) (e▹ₜ {Γ = Γ}) (mFor {Γ = Γ ▹t} A))

    e▹ₜ {con Γₜ ◇p} = refl
    e▹ₜ {con Γₜ (Γₚ ▹p⁰ A)} = ≡tran²
      (cong₂' (FFOL._▹ₚ_ M) (e▹ₜ {con Γₜ Γₚ}) (cong (subst (FFOL.For M) (e▹ₜ {Γ = con Γₜ Γₚ})) (e[]f {A = A}{σ = πₜ¹* id})))
      (substP (λ X → (M FFOL.▹ₚ (M FFOL.▹ₜ) (mCon (con Γₜ Γₚ))) X ≡ (M FFOL.▹ₜ) ((M FFOL.▹ₚ mCon (con Γₜ Γₚ)) (mFor A)))
        (≡tran
          (coeshift {!!})
          (cong (λ X → subst (FFOL.For M) _ (FFOL._[_]f M (mFor A) (mSub (sub (wkₜσₜ idₜ) X)))) (≡sym (coecoe-coe {eq1 = ?} {x = idₚ {Δₚ = Γₚ}}))))
        {!!})
      (cong (M FFOL.▹ₜ) (≡sym (e▹ₚ {con Γₜ Γₚ})))
    -- substP (λ X → FFOL._▹ₚ_ M X (mFor {Γ = ?} (A [ wkₜσₜ idₜ ]f)) ≡ (FFOL._▹ₜ M (mCon (con Γₜ (Γₚ ▹p⁰ A))))) (≡sym (e▹ₜ {Γ = con Γₜ Γₚ})) ?
    


    {-
    

    m⊢ {Γ}{A}(var pvzero) = {!substP (λ X → FFOL._⊢_ M X (mFor A)) (≡sym e▹ₚ) ?!}
    m⊢ (var (pvnext pv)) = {!!}
    m⊢ (app pf pf') = FFOL.app M (m⊢ pf) (m⊢ pf')
    m⊢ (lam pf) = FFOL.lam M {!m⊢ pf!}
    m⊢ (p∀∀e pf) = {!FFOL.∀e M (m⊢ pf)!}
    m⊢ {Γ}{∀∀ A}(p∀∀i pf) = FFOL.∀i M (substP (λ X → FFOL._⊢_ M X (subst (FFOL.For M) (≡sym e▹ₜ) (mFor A))) e▹ₜ {!m⊢ pf!})

    e[]f = {!!}
    

    e∘ : {Γ Δ Ξ : Con}{δ : Sub Δ Ξ}{σ : Sub Γ Δ} → mSub (δ ∘ σ) ≡ FFOL._∘_ M (mSub δ) (mSub σ)
    e∘ = {!!}
    eid : {Γ : Con} → mSub (id {Γ}) ≡ FFOL.id M {mCon Γ}
    eid = {!!}
    e◇ : mCon ◇ ≡ FFOL.◇ M
    e◇ = {!!}
    eε : {Γ : Con} → mSub (sub (εₜ {Con.t Γ}) (εₚ {Con.t Γ} {Con.p Γ})) ≡ subst (FFOL.Sub M (mCon Γ)) (≡sym e◇) (FFOL.ε M {mCon Γ})
    eε = {!!}
    e[]t : {Γ Δ : Con}{t : Tm (Con.t Γ)}{σ : Sub Δ Γ} → mTm (t [ Sub.t σ ]t) ≡ FFOL._[_]t M (mTm t) (mSub σ)
    e[]t = {!!}
    eπₜ¹ : {Γ Δ : Con}{σ : Sub Δ (Γ ▹t)} → mSub (πₜ¹* σ) ≡ FFOL.πₜ¹ M (subst (FFOL.Sub M (mCon Δ)) e▹ₜ (mSub σ))
    eπₜ¹ = {!!}
    eπₜ² : {Γ Δ : Con}{σ : Sub Δ (Γ ▹t)} → mTm (πₜ²* σ) ≡ FFOL.πₜ² M (subst (FFOL.Sub M (mCon Δ)) e▹ₜ (mSub σ))
    eπₜ² = {!!}
    e,ₜ : {Γ Δ : Con}{σ : Sub Δ Γ}{t : Tm (Con.t Δ)} → mSub (σ ,ₜ* t) ≡ subst (FFOL.Sub M (mCon Δ)) (≡sym e▹ₜ) (FFOL._,ₜ_ M (mSub σ) (mTm t))
    e,ₜ = {!!}
    -- Proofs are in prop, so no equation needed
    --[]p : {Γ Δ : Con}{A : For Γ}{pf : FFOL._⊢_ S Γ A}{σ : FFOL.Sub S Δ Γ} → m⊢ (FFOL._[_]p S pf σ) ≡ FFOL._[_]p M (m⊢ pf) (mSub σ)
    e▹ₚ = {!!}
    eπₚ¹ : {Γ Δ : Con}{A : For (Con.t Γ)}{σ : Sub Δ (Γ ▹p A)} → mSub (πₚ¹* σ) ≡ FFOL.πₚ¹ M (subst (FFOL.Sub M (mCon Δ)) e▹ₚ (mSub σ))
    eπₚ¹ = {!!}
    --πₚ² : {Γ Δ : Con}{A : For Γ}{σ : Sub Δ (Γ ▹p A)} → m⊢ (πₚ²* σ) ≡ FFOL.πₚ¹ M (subst (FFOL.Sub M (mCon Δ)) e▹ₚ (mSub σ))
    e,ₚ : {Γ Δ : Con}{A : For (Con.t Γ)}{σ : Sub Δ Γ}{pf : Pf (Con.t Δ) (Con.p Δ) (A [ Sub.t σ ]f)}
      → mSub (σ ,ₚ* pf) ≡ subst (FFOL.Sub M (mCon Δ)) (≡sym e▹ₚ) (FFOL._,ₚ_ M (mSub σ) (substP (FFOL._⊢_ M (mCon Δ)) e[]f (m⊢ pf)))
    e,ₚ = {!!}
    eR : {Γ : Con}{t u : Tm (Con.t Γ)} → mFor (R t u) ≡ FFOL.R M (mTm t) (mTm u)
    eR = {!!}
    e⇒ : {Γ : Con}{A B : For (Con.t Γ)} → mFor (A ⇒ B) ≡ FFOL._⇒_ M (mFor A) (mFor B)
    e⇒ = {!!}
    e∀∀ : {Γ : Con}{A : For ((Con.t Γ) ▹t⁰)} → mFor (∀∀ A) ≡ FFOL.∀∀ M (subst (FFOL.For M) e▹ₜ (mFor A))
    e∀∀ = {!!}
    -}
    m : Mapping ffol M
    m = record { mCon = mCon ; mSub = mSub ; mTm = mTm ; mFor = mFor ; m⊢ = m⊢ }
    
  --mor : (M : FFOL) → Morphism ffol M
  --mor M = record {InitialMorphism M}





















