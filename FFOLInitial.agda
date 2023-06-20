{-# OPTIONS --prop #-}

open import PropUtil

module FFOLInitial (F : Nat → Set) (R : Nat → Set) where

  open import FinitaryFirstOrderLogic F R
  open import Agda.Primitive
  open import ListUtil

  variable
    n : Nat

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
    fun : F n → Array (Tm Γₜ) n → Tm Γₜ

  -- Now we can define formulæ
  data For : Cont → Set₁ where
    rel : R n → Array (Tm Γₜ) n → For Γₜ
    _⇒_ : For Γₜ → For Γₜ → For Γₜ
    ∀∀  : For (Γₜ ▹t⁰) → For Γₜ

  -- Then we define term substitutions, and the application of them on terms and formulæ
  data Subt : Cont → Cont → Set₁ where
    εₜ : Subt Γₜ ◇t
    wk▹t : Subt Δₜ Γₜ → Tm Δₜ → Subt Δₜ (Γₜ ▹t⁰)
    
  -- We subst on terms
  _[_]t : Tm Γₜ → Subt Δₜ Γₜ → Tm Δₜ
  _[_]tz : Array (Tm Γₜ) n → Subt Δₜ Γₜ → Array (Tm Δₜ) n                                         
  var tvzero [ wk▹t σ t ]t = t
  var (tvnext tv) [ wk▹t σ t ]t = var tv [ σ ]t
  fun f tz [ σ ]t = fun f (tz [ σ ]tz)
  zero [ σ ]tz = zero
  next t tz [ σ ]tz = next (t [ σ ]t) (tz [ σ ]tz)

  -- We define liftings on term variables
  -- A term of n variables is a term of n+1 variables
  liftt : Tm Γₜ → Tm (Γₜ ▹t⁰)
  -- Same for a term array
  lifttz : Array (Tm Γₜ) n → Array (Tm (Γₜ ▹t⁰)) n
  liftt (var tv) = var (tvnext tv)
  liftt (fun f tz) = fun f (lifttz tz)
  lifttz zero = zero
  lifttz (next t tz) = next (liftt t) (lifttz tz)
  -- From a substitution into n variables, we construct a substitution from n+1 variables to n+1 variables which maps it to itself
  -- i.e. 0 -> 0 and for all i ->(old) σ(i) we get i+1 -> σ(i)+1
  lift : Subt Δₜ Γₜ → Subt (Δₜ ▹t⁰) (Γₜ ▹t⁰)
  lift εₜ = wk▹t εₜ (var tvzero)
  lift (wk▹t σ t) = wk▹t (lift σ) (liftt t)
  -- From a substition into n variables, we get a substitution into n+1 variables which don't use the last one
  llift : Subt Δₜ Γₜ → Subt (Δₜ ▹t⁰) Γₜ
  llift εₜ = εₜ
  llift (wk▹t σ t) = wk▹t (llift σ) (liftt t)
  
  -- We subst on formulæ
  _[_]f : For Γₜ → Subt Δₜ Γₜ → For Δₜ
  (rel r tz) [ σ ]f = rel r ((map (λ t → t [ σ ]t) tz))
  (A ⇒ B) [ σ ]f = (A [ σ ]f) ⇒ (B [ σ ]f)
  (∀∀ A) [ σ ]f = ∀∀ (A [ lift σ ]f)
                                 
  -- We now can define identity on term substitutions       
  idₜ : Subt Γₜ Γₜ
  idₜ {◇t} = εₜ
  idₜ {Γₜ ▹t⁰} = lift idₜ

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
  lem1 : lift (idₜ {Γₜ}) ≡ wk▹t {!!} {!!}
  []t-id : {t : Tm Γₜ} → t [ idₜ {Γₜ} ]t ≡ t
  []tz-id : {tz : Array (Tm Γₜ) n} → tz [ idₜ {Γₜ} ]tz ≡ tz
  []t-id {◇t ▹t⁰} {var tvzero} = refl
  []t-id {(Γₜ ▹t⁰) ▹t⁰} {var tv} = {!!}
  []t-id {Γₜ} {fun f tz} = substP (λ tz' → fun f tz' ≡ fun f tz) (≡sym []tz-id) refl
  []tz-id {tz = zero} = refl
  []tz-id {tz = next x tz} = substP (λ tz' → (next (x [ idₜ ]t) tz') ≡ next x tz) (≡sym []tz-id) (substP (λ x' → next x' tz ≡ next x tz) (≡sym []t-id) refl)
  []t-∘ : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → {t : Tm Γₜ} → t [ β ∘ₜ α ]t ≡ (t [ β ]t) [ α ]t
  []t-∘ {α = α} {β = β} {t = t} = {!!}
  fun[] : {σ : Subt Δₜ Γₜ} → {f : F n} → {tz : Array (Tm Γₜ) n} → (fun f tz) [ σ ]t ≡ fun f (map (λ t → t [ σ ]t) tz)
  []f-id : {F : For Γₜ} → F [ idₜ {Γₜ} ]f ≡ F
  []f-∘ : {α : Subt Ξₜ Δₜ} → {β : Subt Δₜ Γₜ} → {F : For Γₜ} → F [ β ∘ₜ α ]f ≡ (F [ β ]f) [ α ]f
  rel[] : {σ : Subt Δₜ Γₜ} → {r : R n} → {tz : Array (Tm Γₜ) n} → (rel r tz) [ σ ]f ≡ rel r (map (λ t → t [ σ ]t) tz)


  






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
    
    --p∀∀e : {A : For Γ} → Pf Γ (∀∀ A) → Pf Γ (A [ t , id ])
    --p∀∀i : {A : For (Γ ▹t)} → Pf (Γ [?]) A → Pf Γ (∀∀ A)
  data Sub : Con → Con → Set₁
  subt : Sub Δ Γ → Subt (Con.t Δ) (Con.t Γ)
  data Sub where
    εₚ : Subt (Con.t Δ) Γₜ → Sub Δ (con Γₜ ◇p) -- Γₜ → Δₜ ≡≡> (Γₜ,◇p) → (Δₜ,Δₚ)
    -- If i tell you by what you should replace a missing proof of A, then you can
    -- prove anything that uses a proof of A
    wk▹p : {A : For (Con.t Γ)} → (σ : Sub Δ Γ) →  Pf Δ (A [ subt σ ]f) → Sub Δ (Γ ▹p A)
  subt (εₚ σₜ) = σₜ
  subt (wk▹p σ pf) = subt σ

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
    
  imod : FFOL {lsuc lzero} {lsuc lzero} {lsuc lzero} {lsuc lzero} F R
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
    ; fun = fun
    ; fun[] = {!!}
    ; _▹ₜ = _▹t
    ; πₜ¹ = {!!}
    ; πₜ² = {!!}
    ; _,ₜ_ = {!!}
    ; πₜ²∘,ₜ = {!!}
    ; πₜ¹∘,ₜ = {!!}
    ; ,ₜ∘πₜ = {!!}
    ; For = λ Γ → For (Con.t Γ)
    ; _[_]f = λ A σ → A [ subt σ ]f
    ; []f-id = {!!}
    ; []f-∘ = {!!}
    ; rel = rel
    ; rel[] = {!!}
    ; _⊢_ = λ Γ A → Pf Γ A
    ; _▹ₚ_ = _▹p_
    ; πₚ¹ = {!!}
    ; πₚ² = {!!}
    ; _,ₚ_ = {!!}
    ; ,ₚ∘πₚ = {!!}
    ; πₚ¹∘,ₚ = {!!}
    ; _⇒_ = _⇒_
    ; []f-⇒ = {!!}
    ; ∀∀ = ∀∀
    ; []f-∀∀ = {!!}
    ; lam = {!!}
    ; app = app
    ; ∀i = {!!}
    ; ∀e = {!!}
    }

