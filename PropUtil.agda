{-# OPTIONS --prop --rewriting #-}

module PropUtil where

  open import Agda.Primitive
  variable ℓ ℓ' : Level
  
  data ⊥ₛ : Set where
  record ⊤ₛ : Set ℓ where
    constructor ttₛ


  -- ⊥ is a data with no constructor
  -- ⊤ is a record with one always-available constructor
  data ⊥ : Prop where
  record ⊤ : Prop where
    constructor tt


  data _∨_ : Prop → Prop → Prop where
    inj₁ : {P Q : Prop} → P → P ∨ Q
    inj₂ : {P Q : Prop} → Q → P ∨ Q

  record _∧_ (P Q : Prop) : Prop where
    constructor ⟨_,_⟩
    field
      p : P
      q : Q
      
  infixr 10 _∧_
  infixr 11 _∨_

  -- ∧ elimination
  proj₁ : {P Q : Prop} → P ∧ Q → P
  proj₁ pq = _∧_.p pq
  proj₂ : {P Q : Prop} → P ∧ Q → Q
  proj₂ pq = _∧_.q pq

  -- ∨ elimination
  dis : {P Q S : Prop} → (P ∨ Q) → (P → S) → (Q → S) → S
  dis (inj₁ p) ps qs = ps p
  dis (inj₂ q) ps qs = qs q
  
  -- ¬ is a shorthand for « → ⊥ »
  ¬ : Prop → Prop
  ¬ P = P → ⊥

  -- ⊥ elimination
  case⊥ : {P : Prop} → ⊥ → P
  case⊥ ()
  
  -- ⇔ shorthand
  _⇔_ : Prop → Prop → Prop
  P ⇔ Q = (P → Q) ∧ (Q → P)


  -- Syntactic sugar for writing applications
  infixr 200 _$_
  _$_ : {T U : Prop} → (T → U) → T → U
  h $ t = h t






  postulate _≈_ : ∀{ℓ}{A : Set ℓ}(a : A) → A → Set ℓ
  infix 3 _≡_
  data _≡_ {ℓ}{A : Set ℓ}(a : A) : A → Prop ℓ where
    refl : a ≡ a
  {-# BUILTIN REWRITE _≡_ #-}

  ≡sym : {ℓ : Level} → {A : Set ℓ}→ {a a' : A} → a ≡ a' → a' ≡ a
  ≡sym refl = refl


  ≡tran : {ℓ : Level} {A : Set ℓ} → {a a' a'' : A} → a ≡ a' → a' ≡ a'' → a ≡ a''
  ≡tran² : {ℓ : Level} {A : Set ℓ} → {a₀ a₁ a₂ a₃ : A} → a₀ ≡ a₁ → a₁ ≡ a₂ → a₂ ≡ a₃ → a₀ ≡ a₃
  ≡tran³ : {ℓ : Level} {A : Set ℓ} → {a₀ a₁ a₂ a₃ a₄ : A} → a₀ ≡ a₁ → a₁ ≡ a₂ → a₂ ≡ a₃ → a₃ ≡ a₄ → a₀ ≡ a₄
  ≡tran⁴ : {ℓ : Level} {A : Set ℓ} → {a₀ a₁ a₂ a₃ a₄ a₅ : A} → a₀ ≡ a₁ → a₁ ≡ a₂ → a₂ ≡ a₃ → a₃ ≡ a₄ → a₄ ≡ a₅ → a₀ ≡ a₅
  ≡tran  refl refl = refl
  ≡tran² refl refl refl = refl
  ≡tran³ refl refl refl refl = refl
  ≡tran⁴ refl refl refl refl refl = refl

  cong : {ℓ ℓ' : Level}{A : Set ℓ}{B : Set ℓ'} → (f : A → B) → {a a' : A} → a ≡ a' → f a ≡ f a'
  cong f refl = refl
  cong₂ : {ℓ ℓ' ℓ'' : Level}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''} → (f : A → B → C) → {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
  cong₂ f refl refl = refl
  cong₃ : {ℓ ℓ' ℓ'' ℓ''' : Level}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} → (f : A → B → C → D) → {a a' : A} {b b' : B}{c c' : C} → a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl
  
  -- We can make a proof-irrelevant substitution
  substP      : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Prop ℓ'){a a' : A} → a ≡ a' → P a → P a'
  substP P refl h = h


  postulate coe : ∀{ℓ}{A B : Set ℓ} → A ≡ B → A → B
  postulate coerefl : ∀{ℓ}{A : Set ℓ}{eq : A ≡ A}{a : A} → coe eq a ≡ a
  
  postulate ≡fun : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → {f g : A → B} → ((x : A) → (f x ≡ g x)) → f ≡ g
  postulate ≡fun' : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : A → Set ℓ'} → {f g : (a : A) → B a} → ((x : A) → (f x ≡ g x)) → f ≡ g

  coeaba : {ℓ : Level}{A B : Set ℓ}{eq1 : A ≡ B}{eq2 : B ≡ A}{a : A} → coe eq2 (coe eq1 a) ≡ a
  coeaba {eq1 = refl} = ≡tran coerefl coerefl

  coefgcong : {ℓ : Level}{A B C D : Set ℓ}{aa : A ≡ A}{dd : D ≡ D}{cb : C ≡ B}{f : B → A}{g : D → C}{x : D} → f (coe cb (g (coe dd x))) ≡ coe aa (f (coe cb (g x)))
  coefgcong {cb = refl} {f} {g} = ≡tran (cong f (cong (coe _) (cong g coerefl))) (≡sym coerefl)

  coecong : {ℓ : Level}{A B : Set ℓ}{eq : B ≡ B}{eq' : A ≡ A}(f : A → B){x : A} → (f (coe eq' x)) ≡ (coe eq (f x))

  coecong f = ≡tran (cong f coerefl) (≡sym coerefl)

  coe-f : {ℓ : Level}{A B C D : Set ℓ} → (A → B) → A ≡ C → B ≡ D → C → D
  coe-f f ac bd x = coe bd (f (coe (≡sym ac) x))
  coewtf : {ℓ : Level}{A B C D E F G H : Set ℓ}{ab : A ≡ B}{cd : C ≡ D}{ef : E ≡ F}{gh : G ≡ H}{f : F → B}{g : H → E}{x : G} →
              {fd : F ≡ D} → f (coe ef (g (coe gh x))) ≡ coe ab ((coe-f f fd (≡sym ab)) (coe cd ((coe-f g (≡sym gh) (≡tran² ef fd (≡sym cd))) x)))
  coewtf {ab = refl} {refl} {refl} {refl} {f} {g} {fd = refl} = ≡tran (cong f (cong (coe _) (≡sym coeaba))) (≡sym coeaba)

  subst : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Set ℓ'){a a' : A} → a ≡ a' → P a → P a'
  subst P eq p = coe (cong P eq) p

  --{-# REWRITE transprefl   #-}

  coereflrefl : {ℓ : Level}{A : Set ℓ}{eq eq' : A ≡ A}{a : A} → coe eq (coe eq' a) ≡ a
  coereflrefl = ≡tran coerefl coerefl

  substrefl   : ∀{ℓ}{A : Set ℓ}{ℓ'}{P : A → Set ℓ'}{a : A}{e : a ≡ a}{p : P a} → subst P e p ≡ p
  substrefl = coerefl
  --{-# REWRITE substrefl   #-}
  substreflrefl : {ℓ ℓ' : Level}{A : Set ℓ}{P : A → Set ℓ'}{a : A}{e : a ≡ a}{p : P a} → subst P e (subst P e p) ≡ p
  substreflrefl {P = P} {a} {e} {p} = ≡tran (substrefl {P = P} {a = a} {e = e} {p = subst P e p}) (substrefl {P = P} {a = a} {e = e} {p = p})

  cong₂' : {ℓ ℓ' ℓ'' : Level}{A : Set ℓ}{B : A → Set ℓ'}{C : Set ℓ''} → (f : (a : A) → B a → C) → {a a' : A} {b : B a} {b' : B a'} → (eq : a ≡ a') → subst B eq b ≡ b' → f a b ≡ f a' b'
  cong₂' f {a} refl refl = cong (f a) (≡sym coerefl)
  
  congsubst : {ℓ ℓ' : Level}{A : Set ℓ}{P : A → Set ℓ'}{a a' : A}{e : a ≡ a}{p : P a}{p' : P a} → p ≡ p' → subst P e p ≡ subst P e p'
  congsubst {P = P} {e = refl} h = cong (subst P refl) h

  substfpoly : {ℓ ℓ' : Level}{A : Set ℓ}{P R : A → Set ℓ'}{α β : A}
    {eq : α ≡ β} {f : {ξ : A} → R ξ → P ξ} {x : R α}
    → coe (cong P eq) (f {α} x) ≡ f (coe (cong R eq) x)
  substfpoly {eq = refl} {f} = ≡tran coerefl (cong f (≡sym coerefl))

  substfgpoly : {ℓ ℓ' : Level}{A B : Set ℓ} {P Q : A → Set ℓ'} {R : B → Set ℓ'} {F : B → A} {α β : A} {ε φ : B}
       {eq₁ : α ≡ β} {eq₂ : F ε ≡ α} {eq₃ : F φ ≡ β} {eq₄ : ε ≡ φ}
       {g : {a : A} → Q a → P a} {f : {b : B} → R b → Q (F b)} {x : R ε}
    → g {β} (subst Q eq₃ (f {φ} (subst R eq₄ x))) ≡ subst P eq₁ (g {α} (subst Q eq₂ (f {ε} x)))
  substfgpoly {P = P} {Q} {R} {eq₁ = refl} {refl} {refl} {refl} {g} {f} = ≡tran³ (cong g (substrefl {P = Q} {e = refl})) (cong g (cong f (substrefl {P = R} {e = refl}))) (cong g (≡sym (substrefl {P = Q} {e = refl}))) (≡sym (substrefl {P = P} {e = refl}))

  {-# BUILTIN EQUALITY _≡_ #-}











  data Nat : Set where
    zero : Nat
    succ : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}

  record _×_ (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
    constructor _,×_
    field
      a : A
      b : B

  record _×'_ (A : Set ℓ) (B : Prop ℓ') : Set (ℓ ⊔ ℓ') where
    constructor _,×'_
    field
      a : A
      b : B

  record _×''_ (A : Set ℓ) (B : A → Prop ℓ') : Set (ℓ ⊔ ℓ') where
    constructor _,×''_
    field
      a : A
      b : B a

  proj×₁ : {ℓ ℓ' : Level}{A : Set ℓ}{B : Set ℓ'} → (A × B) → A
  proj×₁ p = _×_.a p
  proj×₂ : {ℓ ℓ' : Level}{A : Set ℓ}{B : Set ℓ'} → (A × B) → B
  proj×₂ p = _×_.b p

  proj×'₁ : {ℓ ℓ' : Level}{A : Set ℓ}{B : Prop ℓ'} → (A ×' B) → A
  proj×'₁ p = _×'_.a p
  proj×'₂ : {ℓ ℓ' : Level}{A : Set ℓ}{B : Prop ℓ'} → (A ×' B) → B
  proj×'₂ p = _×'_.b p

  proj×''₁ : {ℓ ℓ' : Level}{A : Set ℓ}{B : A → Prop ℓ'} → (A ×'' B) → A
  proj×''₁ p = _×''_.a p
  proj×''₂ : {ℓ ℓ' : Level}{A : Set ℓ}{B : A → Prop ℓ'} → (p : A ×'' B) → B (proj×''₁ p)
  proj×''₂ p = _×''_.b p

  
