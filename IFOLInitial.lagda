\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import PropUtil

module IFOLInitial (TM : Set) where

  open import IFOL2
  open import Agda.Primitive
  open import ListUtil

  --#
  data For : Set where
    R : TM → TM → For
    _⇒_ : For → For → For
    ∀∀ : (TM → For) → For
  --#
  
  data Con : Set where
    ◇ : Con
    _▹ₚ_ : Con → For → Con

  variable
    Γ Δ Ξ : Con
    A B : For

  data PfVar : Con → For → Prop where
    pvzero : PfVar (Γ ▹ₚ A) A
    pvnext : PfVar Γ A → PfVar (Γ ▹ₚ B) A
  --#
  data Pf : Con → For → Prop where
    var : PfVar Γ A → Pf Γ A
    lam : Pf (Γ ▹ₚ A) B → Pf Γ (A ⇒ B)
    app : Pf Γ (A ⇒ B) → Pf Γ A → Pf Γ B
    ∀i : {A : TM → For} → ((t : TM) → Pf Γ (A t)) → Pf Γ (∀∀ A)
    ∀e : {A : TM → For} → Pf Γ (∀∀ A) → (t : TM) → Pf Γ (A t)
  --#


  data Ren : Con → Con → Prop where
    ε : Ren Γ ◇
    _,ₚR_ : Ren Δ Γ → PfVar Δ A → Ren Δ (Γ ▹ₚ A)

  rightR : Ren Δ Γ → Ren (Δ ▹ₚ A) Γ
  rightR ε = ε
  rightR (σ ,ₚR pv) = (rightR σ) ,ₚR (pvnext pv)

  idR : Ren Γ Γ
  idR {◇} = ε
  idR {Γ ▹ₚ A} = (rightR (idR {Γ})) ,ₚR pvzero
  
  data Sub : Con → Con → Prop where
    ε : Sub Γ ◇
    _,ₚ_ : Sub Δ Γ → Pf Δ A → Sub Δ (Γ ▹ₚ A)

  πₚ¹ : Sub Δ (Γ ▹ₚ A) → Sub Δ Γ
  πₚ² : Sub Δ (Γ ▹ₚ A) → Pf Δ A
  πₚ¹ (σ ,ₚ pf) = σ
  πₚ² (σ ,ₚ pf) = pf

  SubR : Ren Γ Δ → Sub Γ Δ
  SubR ε = ε
  SubR (σ ,ₚR pv) = SubR σ ,ₚ var pv
  
  id : Sub Γ Γ
  id = SubR idR

  _[_]pvr : PfVar Γ A → Ren Δ Γ → PfVar Δ A
  pvzero [ _ ,ₚR pv ]pvr = pv
  pvnext pv [ σ ,ₚR _ ]pvr = pv [ σ ]pvr
  _[_]pr : Pf Γ A → Ren Δ Γ → Pf Δ A
  var pv [ σ ]pr = var (pv [ σ ]pvr)
  lam pf [ σ ]pr = lam (pf [ (rightR σ) ,ₚR pvzero ]pr)
  app pf pf' [ σ ]pr = app (pf [ σ ]pr) (pf' [ σ ]pr)
  ∀i fpf [ σ ]pr = ∀i (λ t → (fpf t) [ σ ]pr)
  ∀e pf t [ σ ]pr = ∀e (pf [ σ ]pr) t

  wkSub : Sub Δ Γ → Sub (Δ ▹ₚ A) Γ
  wkSub ε = ε
  wkSub (σ ,ₚ pf) = (wkSub σ) ,ₚ (pf [ rightR idR ]pr)

  _[_]p : Pf Γ A → Sub Δ Γ → Pf Δ A
  var pvzero [ _ ,ₚ pf ]p = pf
  var (pvnext pv) [ σ ,ₚ _ ]p = var pv [ σ ]p
  lam pf [ σ ]p = lam (pf [ wkSub σ ,ₚ var pvzero ]p)
  app pf pf' [ σ ]p = app (pf [ σ ]p) (pf' [ σ ]p)
  ∀i fpf [ σ ]p = ∀i (λ t → (fpf t) [ σ ]p)
  ∀e pf t [ σ ]p = ∀e (pf [ σ ]p) t

  _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
  ε ∘ β = ε
  (α ,ₚ pf) ∘ β = (α ∘ β) ,ₚ (pf [ β ]p)


  ifol : IFOL TM
  ifol = record
          { Con = Con
          ; Sub = Sub
          ; _∘_ = _∘_
          ; id = id
          ; ◇ = ◇
          ; ε = ε
          ; For = λ Γ → For
          ; _[_]f = λ A σ → A
          ; []f-id = refl
          ; []f-∘ = refl
          ; Pf = Pf
          ; _[_]p = _[_]p
          ; _▹ₚ_ = _▹ₚ_
          ; πₚ¹ = πₚ¹
          ; πₚ² = πₚ²
          ; _,ₚ_ = _,ₚ_
          ; R = R
          ; _⇒_ = _⇒_
          ; ∀∀ = ∀∀
          ; R[] = refl
          ; []f-⇒ = refl
          ; []f-∀∀ = refl
          ; lam = lam
          ; app = app
          ; ∀i = ∀i
          ; ∀e = ∀e
          }

  module InitialMorphism (M : IFOL {ℓ¹}{ℓ²}{ℓ³}{ℓ⁴} TM) where
  
      mCon : Con → (IFOL.Con M)
      mFor : {Γ : Con} → For → (IFOL.For M (mCon Γ))

      mCon ◇ = IFOL.◇ M
      mCon (Γ ▹ₚ A) = IFOL._▹ₚ_ M (mCon Γ) (mFor {Γ} A)
      mFor {Γ} (R t u) = IFOL.R M t u
      mFor {Γ} (A ⇒ B) = IFOL._⇒_ M (mFor {Γ} A) (mFor {Γ} B)
      mFor {Γ} (∀∀ A) = IFOL.∀∀ M (λ t → mFor {Γ} (A t))
      

      mSub : {Δ : Con}{Γ : Con} → Sub Δ Γ → (IFOL.Sub M (mCon Δ) (mCon Γ))
      mPf : {Γ : Con} {A : For} → Pf Γ A → IFOL.Pf M (mCon Γ) (mFor {Γ} A)

      e[]f⁰ : {Γ : Con}{A B : For} → mFor {Γ ▹ₚ B} A ≡ IFOL._[_]f M (mFor {Γ} A) (IFOL.πₚ¹ M (IFOL.id M))
      e[]f⁰ {A = R t u} = ≡sym (IFOL.R[] M)
      e[]f⁰ {A = A ⇒ B} = ≡sym (≡tran ( IFOL.[]f-⇒ M) (cong₂ (IFOL._⇒_ M) (≡sym (e[]f⁰ {A = A})) (≡sym (e[]f⁰ {A = B}))))
      e[]f⁰ {Γ}{A = ∀∀ A} = ≡sym (≡tran (IFOL.[]f-∀∀ M {F = λ t → mFor {Γ} (A t)}) (cong (IFOL.∀∀ M) (≡fun (λ t → ≡sym (e[]f⁰ {Γ} {A = A t})))))

      e[]f : {Γ Δ : Con}{A : For}{σ : Sub Δ Γ} → mFor {Δ} A ≡ IFOL._[_]f M (mFor {Γ} A) (mSub σ)
      e[]f {A = R t u} {σ} = ≡sym (IFOL.R[] M)
      e[]f {A = A ⇒ B} {σ} = ≡sym (≡tran ( IFOL.[]f-⇒ M) (cong₂ (IFOL._⇒_ M) (≡sym (e[]f {A = A} {σ})) (≡sym (e[]f {A = B} {σ}))))
      e[]f {Γ}{A = ∀∀ A} {σ} = ≡sym (≡tran (IFOL.[]f-∀∀ M {F = λ t → mFor {Γ} (A t)}) (cong (IFOL.∀∀ M) (≡fun (λ t → ≡sym (e[]f {Γ} {A = A t} {σ})))))

      mPf {A = A} (var (pvzero {Γ})) = substP (IFOL.Pf M _) (≡sym (e[]f⁰ {Γ} {A} {A})) (IFOL.πₚ² M (IFOL.id M))
      mPf {A = A} (var (pvnext {Γ} {B = B} pv)) = substP (IFOL.Pf M _) (≡sym (e[]f⁰ {Γ} {A} {B})) (IFOL._[_]p M (mPf (var pv)) (IFOL.πₚ¹ M (IFOL.id M)))
      mPf {Γ} (lam {A = A} {B} pf) = IFOL.lam M (substP (IFOL.Pf M _) (e[]f⁰ {Γ} {B} {A}) (mPf pf))
      mPf (app pf pf') = IFOL.app M (mPf pf) (mPf pf')
      mPf (∀i pf) = IFOL.∀i M (λ t → mPf (pf t))
      mPf (∀e pf t) = IFOL.∀e M (mPf pf) t

      mSub ε = IFOL.ε M
      mSub (_,ₚ_ {Δ} {Γ = Γ} {A} σ pf) = IFOL._,ₚ_ M (mSub σ) (substP (IFOL.Pf M _) (e[]f {Γ} {Δ} {A} {σ}) (mPf pf))

      mor : Morphism TM ifol M
      mor = record {
        m = record {
          mCon = mCon
          ; mSub = mSub
          ; mFor = λ {Γ} A → mFor {Γ} A
          ; mPf = mPf
        }
        ; e◇ = refl
        ; e▹ₚ = refl
        ; e[]f = λ {Γ}{Δ}{A}{σ} → e[]f {Γ}{Δ}{A}{σ}
        ; eR = refl
        ; e∀∀ = refl
        ; e⇒ = refl
        }

  module InitialMorphismUniqueness {M : IFOL {lzero} {lzero} {lzero} {lzero} TM} {m : Morphism TM ifol M} where

    open InitialMorphism M
    mCon≡ : {Γ : Con} → mCon Γ ≡ (Morphism.mCon m Γ)
    mFor≡ : {Γ : Con} {A : For} → mFor {Γ} A ≡ subst (IFOL.For M) (≡sym mCon≡) (Morphism.mFor m {Γ} A)
    
    mCon≡ {◇} = ≡sym (Morphism.e◇ m)
    mCon≡ {Γ ▹ₚ A} = ≡sym (≡tran (Morphism.e▹ₚ m) (cong₂' (IFOL._▹ₚ_ M) (≡sym mCon≡) (≡sym mFor≡)))
    mFor≡ {Γ} {A ⇒ B} = ≡sym (≡tran²
      (cong (subst (IFOL.For M) (≡sym mCon≡)) (Morphism.e⇒ m))
      (substppoly {eq = ≡sym (mCon≡ {Γ})} {f = λ {ξ} X Y → IFOL._⇒_ M {ξ} X Y})
      (cong₂ (IFOL._⇒_ M) (≡sym (mFor≡ {Γ} {A})) (≡sym (mFor≡ {Γ} {B}))))
    mFor≡ {Γ} {R t u} = ≡sym (≡tran (cong (subst (IFOL.For M) (≡sym mCon≡)) (Morphism.eR m)) (substpoly {f = λ {ξ} → IFOL.R M {ξ} t u} {eq = ≡sym mCon≡}))
    mFor≡ {Γ} {∀∀ A} = ≡sym (≡tran³
      (cong (subst (IFOL.For M) (≡sym mCon≡)) (Morphism.e∀∀ m))
      (substfpoly {eq = ≡sym mCon≡}{f = λ {ξ} X → IFOL.∀∀ M {ξ} X}{x = λ t → Mapping.mFor (Morphism.m m) {Γ} (A t)})
      (cong (IFOL.∀∀ M) (≡sym coefun'))
      (cong (IFOL.∀∀ M) (≡fun λ t → ≡sym (mFor≡ {Γ} {A t}))))
      
      
    -- Those two lines are not needed as those sorts are in Prop
    --mSub≡ : {Δ : Con}{Γ : Con}{σ : Sub Δ Γ} → mSub {Δ} {Γ} σ ≡ Morphism.mSub m {Δ} {Γ} σ
    --mPf≡ : {Γ : Con} {A : For}{p : Pf Γ A} → mPf {Γ} {A} p ≡ Morphism.mPf m {Γ} {A} p

\end{code}
