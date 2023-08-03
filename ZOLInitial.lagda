\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import PropUtil

module ZOLInitial where

  open import ZOL2
  open import Agda.Primitive
  open import ListUtil

  data For : Set where
    ι : For
    _⇒_ : For → For → For

  data Con : Set where
    ◇ : Con
    _▹ₚ_ : Con → For → Con

  variable
    Γ Δ Ξ : Con
    A B : For

  data PfVar : Con → For → Prop where
    pvzero : PfVar (Γ ▹ₚ A) A
    pvnext : PfVar Γ A → PfVar (Γ ▹ₚ B) A
  data Pf : Con → For → Prop where
    var : PfVar Γ A → Pf Γ A
    lam : Pf (Γ ▹ₚ A) B → Pf Γ (A ⇒ B)
    app : Pf Γ (A ⇒ B) → Pf Γ A → Pf Γ B

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

  wkSub : Sub Δ Γ → Sub (Δ ▹ₚ A) Γ
  wkSub ε = ε
  wkSub (σ ,ₚ pf) = (wkSub σ) ,ₚ (pf [ rightR idR ]pr)

  _[_]p : Pf Γ A → Sub Δ Γ → Pf Δ A
  var pvzero [ _ ,ₚ pf ]p = pf
  var (pvnext pv) [ σ ,ₚ _ ]p = var pv [ σ ]p
  lam pf [ σ ]p = lam (pf [ wkSub σ ,ₚ var pvzero ]p)
  app pf pf' [ σ ]p = app (pf [ σ ]p) (pf' [ σ ]p)

  _∘_ : {Γ Δ Ξ : Con} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
  ε ∘ β = ε
  (α ,ₚ pf) ∘ β = (α ∘ β) ,ₚ (pf [ β ]p)





  zol : ZOL
  zol = record
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
          ; ι = ι
          ; []f-ι = refl
          ; _⇒_ = _⇒_
          ; []f-⇒ = refl
          ; lam = lam
          ; app = app
          }

  module InitialMorphism (M : ZOL {lzero} {lzero} {lzero} {lzero}) where
  
      mCon : Con → (ZOL.Con M)
      mFor : {Γ : Con} → For → (ZOL.For M (mCon Γ))

      mCon ◇ = ZOL.◇ M
      mCon (Γ ▹ₚ A) = ZOL._▹ₚ_ M (mCon Γ) (mFor {Γ} A)
      mFor {Γ} ι = ZOL.ι M
      mFor {Γ} (A ⇒ B) = ZOL._⇒_ M (mFor {Γ} A) (mFor {Γ} B)


      mSub : {Δ : Con}{Γ : Con} → Sub Δ Γ → (ZOL.Sub M (mCon Δ) (mCon Γ))
      mPf : {Γ : Con} {A : For} → Pf Γ A → ZOL.Pf M (mCon Γ) (mFor {Γ} A)

      e[]f⁰ : {Γ : Con}{A B : For} → mFor {Γ ▹ₚ B} A ≡ ZOL._[_]f M (mFor {Γ} A) (ZOL.πₚ¹ M (ZOL.id M))
      e[]f⁰ {A = ι} = ≡sym (ZOL.[]f-ι M)
      e[]f⁰ {A = A ⇒ B} = ≡sym (≡tran (ZOL.[]f-⇒ M) (cong₂ (ZOL._⇒_ M) (≡sym (e[]f⁰ {A = A})) (≡sym (e[]f⁰ {A = B}))))
      
      e[]f : {Γ Δ : Con}{A : For}{σ : Sub Δ Γ} → mFor {Δ} A ≡ ZOL._[_]f M (mFor {Γ} A) (mSub σ)
      e[]f {A = ι} = ≡sym (ZOL.[]f-ι M)
      e[]f {Γ} {Δ} {A = A ⇒ B} {σ} = ≡sym (≡tran (ZOL.[]f-⇒ M) (cong₂ (ZOL._⇒_ M) (≡sym (e[]f {A = A}{σ})) (≡sym (e[]f {A = B}{σ}))))
      


      mPf {A = A} (var (pvzero {Γ})) = substP (ZOL.Pf M _) (≡sym (e[]f⁰ {Γ} {A} {A})) (ZOL.πₚ² M (ZOL.id M))
      mPf {A = A} (var (pvnext {Γ} {B = B} pv)) = substP (ZOL.Pf M _) (≡sym (e[]f⁰ {Γ} {A} {B})) (ZOL._[_]p M (mPf (var pv)) (ZOL.πₚ¹ M (ZOL.id M)))
      mPf {Γ} (lam {A = A} {B} pf) = ZOL.lam M (substP (ZOL.Pf M _) (e[]f⁰ {Γ} {B} {A}) (mPf pf))
      mPf (app pf pf') = ZOL.app M (mPf pf) (mPf pf')

      mSub ε = ZOL.ε M
      mSub (_,ₚ_ {Δ} {Γ = Γ} {A} σ pf) = ZOL._,ₚ_ M (mSub σ) (substP (ZOL.Pf M _) (e[]f {Γ} {Δ} {A} {σ}) (mPf pf))

      mor : Morphism zol M
      mor = record {
        m = record {
          mCon = mCon
          ; mSub = mSub
          ; mFor = λ {Γ} A → mFor {Γ} A
          ; mPf = mPf
        }
        ; e◇ = refl
        ; e[]f = λ {Γ}{Δ}{A}{σ} → e[]f {A = A} {σ}
        ; e▹ₚ = refl
        ; eι = refl
        ; e⇒ = refl
        }

  module InitialMorphismUniqueness {M : ZOL {lzero} {lzero} {lzero} {lzero}} {m : Morphism zol M} where

    open InitialMorphism M
    mCon≡ : {Γ : Con} → mCon Γ ≡ (Morphism.mCon m Γ)
    mFor≡ : {Γ : Con} {A : For} → mFor {Γ} A ≡ subst (ZOL.For M) (≡sym mCon≡) (Morphism.mFor m {Γ} A)
    
    mCon≡ {◇} = ≡sym (Morphism.e◇ m)
    mCon≡ {Γ ▹ₚ A} = ≡sym (≡tran (Morphism.e▹ₚ m) (cong₂' (ZOL._▹ₚ_ M) (≡sym mCon≡) (≡sym mFor≡)))
    mFor≡ {Γ} {ι} = ≡sym (≡tran
      (cong (subst (ZOL.For M) (≡sym mCon≡)) (Morphism.eι m))
      (substpoly {f = λ {Ξ} → ZOL.ι M {Ξ}} {eq = ≡sym mCon≡})
      )
    mFor≡ {Γ} {A ⇒ B} = ≡sym (≡tran²
      (cong (subst (ZOL.For M) (≡sym mCon≡)) (Morphism.e⇒ m))
      (substppoly {eq = ≡sym (mCon≡ {Γ})} {f = λ {ξ} X Y → ZOL._⇒_ M {ξ} X Y})
      (cong₂ (ZOL._⇒_ M) (≡sym (mFor≡ {Γ} {A})) (≡sym (mFor≡ {Γ} {B}))))
      
    -- Those two lines are not needed as those sorts are in Prop
    --mSub≡ : {Δ : Con}{Γ : Con}{σ : Sub Δ Γ} → mSub {Δ} {Γ} σ ≡ Morphism.mSub m {Δ} {Γ} σ
    --mPf≡ : {Γ : Con} {A : For}{p : Pf Γ A} → mPf {Γ} {A} p ≡ Morphism.mPf m {Γ} {A} p

\end{code}
