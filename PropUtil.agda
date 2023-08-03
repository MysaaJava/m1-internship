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
  record ⊤ : Prop ℓ where
    constructor tt


  data _∨_ : Prop → Prop → Prop where
    inj₁ : {P Q : Prop} → P → P ∨ Q
    inj₂ : {P Q : Prop} → Q → P ∨ Q

  record _∧_ (P Q : Prop ℓ) : Prop ℓ where
    constructor ⟨_,_⟩
    field
      p : P
      q : Q
      
  infixr 10 _∧_
  infixr 11 _∨_

  -- ∧ elimination
  proj₁ : {P Q : Prop ℓ} → P ∧ Q → P
  proj₁ pq = _∧_.p pq
  proj₂ : {P Q : Prop ℓ} → P ∧ Q → Q
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
  ≡tran⁵ : {ℓ : Level} {A : Set ℓ} → {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : A} → a₀ ≡ a₁ → a₁ ≡ a₂ → a₂ ≡ a₃ → a₃ ≡ a₄ → a₄ ≡ a₅ → a₅ ≡ a₆ → a₀ ≡ a₆
  ≡tran⁶ : {ℓ : Level} {A : Set ℓ} → {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : A} → a₀ ≡ a₁ → a₁ ≡ a₂ → a₂ ≡ a₃ → a₃ ≡ a₄ → a₄ ≡ a₅ → a₅ ≡ a₆ → a₆ ≡ a₇ → a₀ ≡ a₇
  ≡tran⁷ : {ℓ : Level} {A : Set ℓ} → {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : A} → a₀ ≡ a₁ → a₁ ≡ a₂ → a₂ ≡ a₃ → a₃ ≡ a₄ → a₄ ≡ a₅ → a₅ ≡ a₆ → a₆ ≡ a₇ → a₇ ≡ a₈ → a₀ ≡ a₈
  ≡tran  refl refl = refl
  ≡tran² refl refl refl = refl
  ≡tran³ refl refl refl refl = refl
  ≡tran⁴ refl refl refl refl refl = refl
  ≡tran⁵ refl refl refl refl refl refl = refl
  ≡tran⁶ refl refl refl refl refl refl refl = refl
  ≡tran⁷ refl refl refl refl refl refl refl refl = refl

  cong : {ℓ ℓ' : Level}{A : Set ℓ}{B : Set ℓ'} → (f : A → B) → {a a' : A} → a ≡ a' → f a ≡ f a'
  cong f refl = refl
  cong₂ : {ℓ ℓ' ℓ'' : Level}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''} → (f : A → B → C) → {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
  cong₂ f refl refl = refl
  cong₃ : {ℓ ℓ' ℓ'' ℓ''' : Level}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} → (f : A → B → C → D) → {a a' : A} {b b' : B}{c c' : C} → a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl
  
  -- We can make a proof-irrelevant substitution
  substP      : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Prop ℓ'){a a' : A} → a ≡ a' → P a → P a'
  substP P refl h = h
  substPP      : ∀{ℓ}{A B : Set ℓ}{Q : A → Prop ℓ}{ℓ'}(P : {k : A} → Q k → Prop ℓ'){a a' : A}{x : Q a}
    → (eq : a ≡ a') → P x → P (substP Q eq x)
  substPP P refl h = h
  substP² : ∀{ℓ ℓ' ℓ'' : Level}{A : Set ℓ}{B : Set ℓ'}(P : A → B → Prop ℓ''){a a' : A}{b b' : B} → a ≡ a' → b ≡ b' → P a b → P a' b'
  substP² P refl refl p = p


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

  coecoe-coe : {ℓ : Level}{A B C : Set ℓ}{eq1 : B ≡ A}{eq2 : C ≡ B}{x : C} → coe eq1 (coe eq2 x) ≡ coe (≡tran eq2 eq1) x
  coecoe-coe {eq1 = refl} {refl} = coerefl

  coe-f : {ℓ : Level}{A B C D : Set ℓ} → (A → B) → A ≡ C → B ≡ D → C → D
  coe-f f ac bd x = coe bd (f (coe (≡sym ac) x))
  coewtf : {ℓ : Level}{A B C D E F G H : Set ℓ}{ab : A ≡ B}{cd : C ≡ D}{ef : E ≡ F}{gh : G ≡ H}{f : F → B}{g : H → E}{x : G} →
              {fd : F ≡ D} → f (coe ef (g (coe gh x))) ≡ coe ab ((coe-f f fd (≡sym ab)) (coe cd ((coe-f g (≡sym gh) (≡tran² ef fd (≡sym cd))) x)))
  coewtf {ab = refl} {refl} {refl} {refl} {f} {g} {fd = refl} = ≡tran (cong f (cong (coe _) (≡sym coeaba))) (≡sym coeaba)

  coeshift : {ℓ : Level}{A B : Set ℓ}{x : A} {y : B} {eq : A ≡ B} → coe eq x ≡ y → x ≡ coe (≡sym eq) y
  coeshift {eq=refl} refl = ≡sym coeaba

  subst : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Set ℓ'){a a' : A} → a ≡ a' → P a → P a'
  subst P eq p = coe (cong P eq) p
  subst² : ∀{ℓ ℓ' ℓ'' : Level}{A : Set ℓ}{B : Set ℓ'}(P : A → B → Set ℓ''){a a' : A}{b b' : B} → a ≡ a' → b ≡ b' → P a b → P a' b'
  subst² P eq eq' p = coe (cong₂ P eq eq') p
  subst¹P : ∀{ℓ ℓ' ℓ'' : Level}{A : Set ℓ}{B : Prop ℓ'}(P : A → B → Set ℓ''){a a' : A}{b : B} → a ≡ a' → P a b → P a' b
  subst¹P P {b = b} eq p = coe (cong (λ x → P x b) eq) p
  
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

  substpoly : {ℓ ℓ' : Level}{A : Set ℓ}{P : A → Set ℓ'}{f : {ξ : A} → P ξ}
    {α β : A}{eq : α ≡ β}
    → subst P eq (f {α}) ≡ f {β}
  substpoly {eq = refl} = coerefl

  substfpoly : {ℓ ℓ' : Level}{A : Set ℓ}{P R : A → Set ℓ'}{α β : A}
    {eq : α ≡ β} {f : {ξ : A} → R ξ → P ξ} {x : R α}
    → coe (cong P eq) (f {α} x) ≡ f (coe (cong R eq) x)
  substfpoly {eq = refl} {f} = ≡tran coerefl (cong f (≡sym coerefl))
  
  substppoly : {ℓ ℓ' ℓ'' ℓ''' : Level}{A : Set ℓ}{P : A → Set ℓ'}{R : A → Set ℓ''}{Q : A → Set ℓ'''}{α β : A}
    {eq : α ≡ β}{f : {ξ : A} → R ξ → Q ξ → P ξ} {x : R α} {y : Q α}
    → coe (cong P eq) (f {α} x y) ≡ f {β} (coe (cong R eq) x) (coe (cong Q eq) y)
  substppoly {eq = refl} {f}{x}{y} = ≡tran coerefl (cong₂ f (≡sym coerefl) (≡sym coerefl))
  
  substfpoly⁴ : {ℓ ℓ' ℓ'' : Level}{A : Set ℓ}{P R : A → Set ℓ'}{Q : A → Prop ℓ''}{α β : A}
    {eq : α ≡ β} {f : {ξ : A} → R ξ → Q ξ → P ξ} {x : R α} {y : Q α}
    → coe (cong P eq) (f {α} x y) ≡ f {β} (coe (cong R eq) x) (substP Q eq y)
  substfpoly⁴ {eq = refl} {f}{x}{y} = ≡tran² coerefl (cong (λ x → f x y) (≡sym coerefl)) refl
  substfgpoly : {ℓ ℓ' : Level}{A B : Set ℓ} {P Q : A → Set ℓ'} {R : B → Set ℓ'} {F : B → A} {α β : A} {ε φ : B}
       {eq₁ : α ≡ β} {eq₂ : F ε ≡ α} {eq₃ : F φ ≡ β} {eq₄ : ε ≡ φ}
       {g : {a : A} → Q a → P a} {f : {b : B} → R b → Q (F b)} {x : R ε}
    → g {β} (subst Q eq₃ (f {φ} (subst R eq₄ x))) ≡ subst P eq₁ (g {α} (subst Q eq₂ (f {ε} x)))
  substfgpoly {P = P} {Q} {R} {eq₁ = refl} {refl} {refl} {refl} {g} {f} = ≡tran³ (cong g (substrefl {P = Q} {e = refl})) (cong g (cong f (substrefl {P = R} {e = refl}))) (cong g (≡sym (substrefl {P = Q} {e = refl}))) (≡sym (substrefl {P = P} {e = refl}))

  {-# BUILTIN EQUALITY _≡_ #-}

  coep² : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {A : Set ℓ₁} {R : A → Set ℓ₂}{T : A → Set ℓ₃}{S : A → Set ℓ₄}{α β : A}
    {p : {ξ : A} → R ξ → T ξ → S ξ}{x : R α}{y : T α}{eq : α ≡ β}
    → subst S (≡sym eq) (p {β} (subst R eq x) (subst T eq y)) ≡ p {α} x y
  coep² {S = S}{p = p}{x}{y}{refl} = ≡tran (substrefl {P = S} {e = refl}) (cong₂ p (substrefl {a = x} {e = refl}) (substrefl {a = y} {e = refl}))
  coep²'' : {ℓ ℓ' : Level} {A : Set ℓ} {R S : A → Set ℓ'}{T : A → Prop ℓ'}{α β : A}
    {p : {ξ : A} → R ξ → T ξ → S ξ}{x : R α}{y : T α}{eq : α ≡ β}
    → subst S (≡sym eq) (p {β} (subst R eq x) (substP T eq y)) ≡ p {α} x y
  coep²'' {S = S}{p = p}{x}{y}{refl} = ≡tran (substrefl {P = S} {e = refl}) (cong (λ X → p X y) (substrefl {a = x} {e = refl}))
  coep²' : {ℓ ℓ' : Level} {A : Set ℓ} {R T S : A → Set ℓ'}{α β : A}
    {p : {ξ : A} → R ξ → T ξ → S ξ}{x : R β}{y : T α}{eq : α ≡ β}
    → subst S (≡sym eq) (p {β} x (subst T eq y)) ≡ p {α} (subst R (≡sym eq) x) y
  coep²' {S = S}{p = p}{x}{y}{refl} = ≡tran (substrefl {P = S} {e = refl}) (cong₂ p (≡sym (substrefl {a = x} {e = refl})) (substrefl {a = y} {e = refl}))

  coep∘ : {ℓ ℓ' : Level}{A : Set ℓ} {R : A → A → Set ℓ'} {α β γ δ ε φ : A}
        {p : {x y z : A} → R x y → R z x → R z y}{x : R β γ}{y : R α β}
        {eq1 : α ≡ δ} {eq2 : β ≡ ε} {eq3 : γ ≡ φ} →
        coe (cong₂ R (≡sym eq1) (≡sym eq3)) (p (coe (cong₂ R eq2 eq3) x) (coe (cong₂ R eq1 eq2) y)) ≡ p x y
  coep∘ {p = p}{eq1 = refl}{refl}{refl} = ≡tran coerefl (cong₂ p coerefl coerefl)
  coep∘-helper = λ {ℓ ℓ' ℓ'' : Level}{B : Set ℓ}{A : B → Set ℓ''} {R : (b : B) → A b → A b → Set ℓ'}
    {b₁ b₂ : B} {α γ : A b₁} {δ φ : A b₂}
        {eq0 : b₁ ≡ b₂}{eqa : subst A eq0 α ≡ δ}{eqb : subst A eq0 γ ≡ φ}
     → (≡tran² (cong (R b₂ δ) (≡sym eqb)) (cong (λ X → R b₂ X (subst A eq0 γ)) (≡sym eqa)) (≡tran (≡sym (substrefl {P = λ X → Set ℓ'}{a = R b₂ (subst A eq0 α) (subst A eq0 γ)}{e = refl})) (coep² {p = λ {t} x y → R t x y}{eq = eq0})))
  coep∘-helper-coe : {ℓ ℓ' ℓ'' : Level}{B : Set ℓ}{A : B → Set ℓ''} {R : (b : B) → A b → A b → Set ℓ'}
    {b₁ b₂ : B} {α γ : A b₁} {δ φ : A b₂}
        {eq0 : b₁ ≡ b₂}{eqa : subst A eq0 α ≡ δ}{eqb : subst A eq0 γ ≡ φ} → {a : R b₂ δ φ}{a' : R b₁ α γ} → coe (coep∘-helper {eq0 = eq0} {eqa = eqa} {eqb = eqb}) a ≡ a
  coep∘-helper-coe {eq0 = refl}{refl}{refl} = coerefl


  coefun : {ℓ : Level}{A B C : Set ℓ}{f : B → C}{eq : A ≡ B}
    → f ≡ coe (cong (λ X → X → C) eq) (λ (x : A) → f (coe eq x))
  coefun {f = f} {eq = refl} = ≡tran (≡fun (λ x → cong f (≡sym (coerefl {eq = refl})))) (≡sym (coerefl {eq = refl}))
  coefun' : {ℓ : Level}{A B C : Set ℓ}{f : A → B}{eq : B ≡ C}
    → (λ (x : A) → coe eq (f x)) ≡ coe (cong (λ X → A → X) eq) (λ (x : A) → f x)
  coefun' {f = f} {eq = refl} = ≡tran (≡fun (λ x → coerefl)) (≡sym coerefl)







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

  record _×ᵈ_ (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
    constructor _,×ᵈ_
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

  proj×ᵈ₁ : {ℓ ℓ' : Level}{A : Set ℓ}{B : A → Set ℓ'} → (A ×ᵈ B) → A
  proj×ᵈ₁ p = _×ᵈ_.a p
  proj×ᵈ₂ : {ℓ ℓ' : Level}{A : Set ℓ}{B : A → Set ℓ'} → (p : A ×ᵈ B) → (B (proj×ᵈ₁ p))
  proj×ᵈ₂ p = _×ᵈ_.b p
  

  ×≡ : {A : Set ℓ}{B : Set ℓ'}{a a' : A}{b b' : B} →  a ≡ a' → b ≡ b' → a ,× b ≡ a' ,× b'
  ×≡ refl refl = refl

  ×ᵈ≡ : {A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}{b' : B a'} →  (eq : a ≡ a') → subst B eq b ≡ b' → a ,×ᵈ b ≡ a' ,×ᵈ b'
  ×ᵈ≡ {B = B} {a = a}{b = b} refl refl = cong₂' _,×ᵈ_ refl refl
