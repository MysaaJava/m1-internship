{-# OPTIONS --prop #-}
module prop where


open import Agda.Builtin.String using (String)
open import Data.String.Properties using (_==_)
open import Data.List using (List; _∷_; [])


{- Prop -}

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
-- ¬ is a shorthand for « → ⊥ »
¬ : Prop → Prop
¬ P = P → ⊥
case⊥ : {P : Prop} → ⊥ → P
case⊥ ()
-- ∨ elimination
dis : {P Q S : Prop} → (P ∨ Q) → (P → S) → (Q → S) → S
dis (inj₁ p) ps qs = ps p
dis (inj₂ q) ps qs = qs q


_⇔_ : Prop → Prop → Prop
P ⇔ Q = (P → Q) ∧ (Q → P)


data Form : Set where
  Var : String → Form
  _[⇒]_ : Form → Form → Form
  
infixr 8 _[⇒]_

data _≡_ : {A : Set} → A → A → Prop where
  refl : {A : Set} → {x : A} → x ≡ x

Con = List Form

variable
  A : Form
  B : Form
  C : Form
  F : Form
  G : Form
  Γ : Con
  Η : Con
  x : String
  y : String

data _⊢_ : Con → Form → Prop where
     zero : (F ∷ Γ) ⊢ F
     succ : Γ ⊢ F → (G ∷ Γ) ⊢ F
     lam : (F ∷ Γ) ⊢ G → Γ ⊢ (F [⇒] G)
     app : Γ ⊢ (F [⇒] G) → Γ ⊢ F → Γ ⊢ G

infixr 5 _⊢_

d-C : [] ⊢ ((Var "Q") [⇒] (Var "R")) [⇒] ((Var "P") [⇒] (Var "Q")) [⇒] (Var "P") [⇒] (Var "R")
d-C = lam (lam (lam (app (succ (succ zero)) (app (succ zero) zero))))

Env = String → Prop

⟦_⟧F : Form → Env → Prop
⟦ Var x ⟧F ρ = ρ x
⟦ A [⇒] B ⟧F ρ = (⟦ A ⟧F ρ) → (⟦ B ⟧F ρ)

⟦_⟧C : Con → Env → Prop
⟦ [] ⟧C ρ = ⊤
⟦ A ∷ Γ ⟧C ρ = (⟦ A ⟧F ρ) ∧ (⟦ Γ ⟧C ρ)

⟦_⟧d : Γ ⊢ F → {ρ : Env} → ⟦ Γ ⟧C ρ → ⟦ F ⟧F ρ
⟦ zero ⟧d p = proj₁ p
⟦ succ th ⟧d p = ⟦ th ⟧d (proj₂ p)
⟦ lam th ⟧d = λ pₐ p₀ → ⟦ th ⟧d ⟨ p₀ , pₐ ⟩
⟦ app th₁ th₂ ⟧d = λ p → ⟦ th₁ ⟧d p (⟦ th₂ ⟧d p)

ρ₀ : Env
ρ₀ "P" = ⊥
ρ₀ "Q" = ⊤
ρ₀ _ = ⊥

cex-d : ([] ⊢ (((Var "P") [⇒] (Var "Q")) [⇒] (Var "P"))) → ⊥
cex-d h = ⟦ h ⟧d {ρ₀} tt λ x → tt

data ⊢sk : Form → Prop where
  SS : ⊢sk ((A [⇒] B [⇒] C) [⇒] (A [⇒] B) [⇒] A [⇒] C)
  KK : ⊢sk (A [⇒] B [⇒] A)
  app : ⊢sk (A [⇒] B) → ⊢sk A → ⊢sk B

thm : ([] ⊢ A) ⇔ ⊢sk A
thm₁ :  ⊢sk A → ([] ⊢ A)
thm₁ SS = lam (lam (lam ( app (app (succ (succ zero)) zero) (app (succ zero) zero))))
thm₁ KK = lam (lam (succ zero))
thm₁ (app x x₁) = app (thm₁ x) (thm₁ x₁)

data _⊢skC_ : Con → Form → Prop where
  zero : (A ∷ Γ) ⊢skC A
  suc : Γ ⊢skC A → (B ∷ Γ) ⊢skC A
  SS : Γ ⊢skC ((A [⇒] B [⇒] C) [⇒] (A [⇒] B) [⇒] A [⇒] C)
  KK : Γ ⊢skC (A [⇒] B [⇒] A)
  app : Γ ⊢skC (A [⇒] B) → Γ ⊢skC A → Γ ⊢skC B

skC→sk : [] ⊢skC A → ⊢sk A
skC→sk SS = SS
skC→sk KK = KK
skC→sk (app d e) = app (skC→sk d) (skC→sk e)


lam-sk : (A ∷ Γ) ⊢skC B → Γ ⊢skC (A [⇒] B)
lam-sk-zero : Γ ⊢skC (A [⇒] A)
lam-sk-zero {A = A} = app (app SS KK) (KK {B = A})
lam-sk zero = lam-sk-zero
lam-sk (suc x) = app KK x
lam-sk SS = app KK SS
lam-sk KK = app KK KK
lam-sk (app x₁ x₂) = app (app SS (lam-sk x₁)) (lam-sk x₂)

⊢→⊢skC : Γ ⊢ A → Γ ⊢skC A
⊢→⊢skC zero = zero
⊢→⊢skC (succ x) = suc (⊢→⊢skC x)
⊢→⊢skC (lam x) = lam-sk (⊢→⊢skC x)
⊢→⊢skC (app x x₁) = app (⊢→⊢skC x) (⊢→⊢skC x₁)

thm = ⟨ (λ x → skC→sk (⊢→⊢skC x)) , thm₁ ⟩


Pierce = {P Q : Prop} → ((P → Q) → P) → P
TND : Prop → Prop
TND P = P ∨ (¬ P)

P→TND : Pierce → {P : Prop} → TND P
nnTND : {P : Prop} → ¬ (¬ (P ∨ ¬ P))
nnTND ntnd = ntnd (inj₂ λ p → ntnd (inj₁ p))
P→TND pierce {P} = pierce {TND P} {⊥} (λ p → case⊥ (nnTND p))



{- Kripke Models -}

record Kripke : Set₁ where
  field
    Worlds : Set₀
    _≤_ : Worlds → Worlds → Prop
    refl≤ : {w : Worlds} → w ≤ w
    tran≤ : {a b c : Worlds} → a ≤ b → b ≤ c → a ≤ c
    _⊩_ : Worlds → String → Prop
    mon⊩ : {a b : Worlds} → a ≤ b → {p : String} → a ⊩ p → b ⊩ p
  {- Extending ⊩ to Formulas and Contexts -}
  _⊩ᶠ_ : Worlds → Form → Prop
  w ⊩ᶠ Var x = w ⊩ x
  w ⊩ᶠ (fp [⇒] fq) = {w' : Worlds} → w ≤ w' → w' ⊩ᶠ fp → w' ⊩ᶠ fq
  mon⊩ᶠ : {a b : Worlds} → a ≤ b → a ⊩ᶠ A → b ⊩ᶠ A
  mon⊩ᶠ {Var x} ab aA = mon⊩ ab aA
  mon⊩ᶠ {A [⇒] A₁} ab aA bc cA = aA (tran≤ ab bc) cA
  _⊩ᶜ_ : Worlds → Con → Prop
  w ⊩ᶜ [] = ⊤
  w ⊩ᶜ (p ∷ c) = (w ⊩ᶠ p) ∧ (w ⊩ᶜ c)
  mon⊩ᶜ : {a b : Worlds} → a ≤ b → a ⊩ᶜ Γ → b ⊩ᶜ Γ
  mon⊩ᶜ {[]} ab aΓ = aΓ
  mon⊩ᶜ {A ∷ Γ} ab aΓ = ⟨ mon⊩ᶠ {A} ab (proj₁ aΓ) , mon⊩ᶜ ab (proj₂ aΓ) ⟩
  _⊫_ : Con → Form → Prop
  Γ ⊫ F = {w : Worlds} → w ⊩ᶜ Γ → w ⊩ᶠ F
  {- Soundness -}
  ⟦_⟧ : Γ ⊢ A → Γ ⊫ A
  ⟦ zero ⟧ = proj₁
  ⟦ succ p ⟧ = λ x → ⟦ p ⟧ (proj₂ x)
  ⟦ lam p ⟧ = λ wΓ w≤ w'A → ⟦ p ⟧ ⟨ w'A , mon⊩ᶜ w≤ wΓ ⟩
  ⟦ app p p₁ ⟧ wΓ = ⟦ p ⟧ wΓ refl≤ (⟦ p₁ ⟧ wΓ)

{- Pierce is not provable -}

module PierceWorld where
  data Worlds : Set where
    w₁ w₂ : Worlds
  data _≤_ : Worlds → Worlds → Prop where
    w₁₁ : w₁ ≤ w₁
    w₁₂ : w₁ ≤ w₂
    w₂₂ : w₂ ≤ w₂
  data _⊩_ : Worlds → String → Prop where
    w₂A : w₂ ⊩ "A"

  refl≤ : {w : Worlds} → w ≤ w
  refl≤ {w₁} = w₁₁
  refl≤ {w₂} = w₂₂
  tran≤ : {w w' w'' : Worlds} → w ≤ w' → w' ≤ w'' → w ≤ w''
  tran≤ w₁₁ z = z
  tran≤ w₁₂ w₂₂ = w₁₂
  tran≤ w₂₂ w₂₂ = w₂₂
  mon⊩ : {a b : Worlds} → a ≤ b → {p : String} → a ⊩ p → b ⊩ p
  mon⊩ w₂₂ w₂A = w₂A
  
PierceW : Kripke
PierceW = record {PierceWorld}

FaultyPierce : Form 
FaultyPierce = (((Var "A" [⇒] Var "B") [⇒] Var "A") [⇒] Var "A")

{- Pierce formula is false in world 1 -}
Pierce⊥w₁ : ¬(Kripke._⊩ᶠ_ PierceW PierceWorld.w₁ FaultyPierce)
PierceHypw₁ : Kripke._⊩ᶠ_ PierceW PierceWorld.w₁ ((Var "A" [⇒] Var "B") [⇒] Var "A")
NotAw₁ : ¬(Kripke._⊩ᶠ_ PierceW PierceWorld.w₁ (Var "A"))
NotAw₁ ()
NotBw₂ : ¬(Kripke._⊩ᶠ_ PierceW PierceWorld.w₂ (Var "B"))
NotBw₂ ()
NotABw₁ : ¬(Kripke._⊩ᶠ_ PierceW PierceWorld.w₁ (Var "A" [⇒] Var "B"))
NotABw₁ h = NotBw₂ (h PierceWorld.w₁₂ PierceWorld.w₂A)
PierceHypw₁ PierceWorld.w₁₁ x = case⊥ (NotABw₁ x)
PierceHypw₁ PierceWorld.w₁₂ x = PierceWorld.w₂A
Pierce⊥w₁ h = case⊥ (NotAw₁ (h PierceWorld.w₁₁ PierceHypw₁))
{- Pierce formula is true in world 2 -}
Pierce⊤w₂ : Kripke._⊩ᶠ_ PierceW PierceWorld.w₂ FaultyPierce
Pierce⊤w₂ PierceWorld.w₂₂ h₂ = PierceWorld.w₂A
PierceImpliesw₁ : ([] ⊢ FaultyPierce) → (Kripke._⊩ᶠ_ PierceW PierceWorld.w₁ FaultyPierce)
PierceImpliesw₁ h = Kripke.⟦_⟧ PierceW h {PierceWorld.w₁} tt
NotProvable : ¬([] ⊢ FaultyPierce)
NotProvable h = Pierce⊥w₁ (PierceImpliesw₁ h)

{- Universal Kripke -}
-- Extension of ⊢ to contexts
_⊢⁺_ : Con → Con → Prop
Γ ⊢⁺ [] = ⊤
Γ ⊢⁺ (F ∷ Γ') = (Γ ⊢ F) ∧ (Γ ⊢⁺ Γ')

module UniversalKripke where
  Worlds = Con
  _≤_ : Con → Con → Prop
  Γ ≤ Η = Η ⊢⁺ Γ
  _⊩_ : Con → String → Prop
  Γ ⊩ x = Γ ⊢ Var x

  data _⊆_ : Con → Con → Prop where
    zero⊆ : Γ ⊆ Γ
    next⊆ : Γ ⊆ Η → Γ ⊆ (F ∷ Η)
  retro⊆ : {Γ Γ' : Con} → {F : Form} → (F ∷ Γ) ⊆ Γ' → Γ ⊆ Γ'
  retro⊆ {Γ' = []} () -- Impossible to have «F∷Γ ⊆ []»
  retro⊆ {Γ' = x ∷ Γ'} zero⊆ = next⊆ zero⊆
  retro⊆ {Γ' = x ∷ Γ'} (next⊆ h) = next⊆ (retro⊆ h)
  mon⊆≤ : {Γ Γ' : Con} → Γ' ⊆ Γ → Γ ⊢⁺ Γ'
  mon⊆≤ {[]} zero⊆ = tt
  mon⊆≤ {x ∷ Γ} zero⊆ = ⟨ zero , mon⊆≤ (next⊆ zero⊆) ⟩
  mon⊆≤ {x ∷ Γ} {[]} (next⊆ sub) = tt
  mon⊆≤ {x ∷ Γ} {y ∷ Γ'} (next⊆ sub) = ⟨ succ (proj₁ (mon⊆≤ sub)) , mon⊆≤ (next⊆ (retro⊆ sub)) ⟩

  refl≤ : {Γ : Con} → Γ ⊢⁺ Γ
  refl≤ = mon⊆≤ zero⊆
  addhyp : {Γ Γ' : Con} → {F : Form} → Γ ⊢⁺ Γ' → (F ∷ Γ) ⊢⁺ Γ'
  addhyp {Γ' = []} h = tt
  addhyp {Γ' = x ∷ Γ'} h = ⟨ succ (proj₁ h) , addhyp (proj₂ h) ⟩
  halftran≤ : {Γ Γ' : Con} → {F : Form} → Γ ⊢⁺ Γ' → Γ' ⊢ F → Γ ⊢ F
  halftran≤ h⁺ zero = proj₁ h⁺
  halftran≤ h⁺ (succ h) = halftran≤ (proj₂ h⁺) h
  halftran≤ h⁺ (lam h) = lam (halftran≤ ⟨ zero , addhyp h⁺ ⟩ h)
  halftran≤ h⁺ (app h h') = app (halftran≤ h⁺ h) (halftran≤ h⁺ h')
  tran≤ : {Γ Γ' Γ'' : Con} → Γ ≤ Γ' → Γ' ≤ Γ'' → Γ ≤ Γ''
  tran≤ {[]} h h' = tt
  tran≤ {x ∷ Γ} h h' = ⟨ halftran≤ h' (proj₁ h) , tran≤ (proj₂ h) h' ⟩
  
  mon⊩ : {w w' : Con} → w ≤ w' → {x : String} → w ⊩ x → w' ⊩ x
  mon⊩ h h' = halftran≤ h h' 
  
UK : Kripke
UK = record {UniversalKripke}

module CompletenessProof where
  open Kripke UK
  open UniversalKripke using (mon⊆≤ ; zero⊆ ; next⊆ ; halftran≤ ; addhyp)

  ⊩ᶠ→⊢ : {F : Form} → {Γ : Con} → Γ ⊩ᶠ F → Γ ⊢ F
  ⊢→⊩ᶠ : {F : Form} → {Γ : Con} → Γ ⊢ F → Γ ⊩ᶠ F
  ⊢→⊩ᶠ {Var x} h = h
  ⊢→⊩ᶠ {F [⇒] F₁} h {Γ'} iq hF = ⊢→⊩ᶠ {F₁} (app {Γ'} {F} {F₁} (lam (app (halftran≤ (addhyp iq) h) zero)) (⊩ᶠ→⊢ hF))
  ⊩ᶠ→⊢ {Var x} h = h
  ⊩ᶠ→⊢ {F [⇒] F₁} {Γ} h = lam (⊩ᶠ→⊢ (h (mon⊆≤ (next⊆ zero⊆)) (⊢→⊩ᶠ {F} {F ∷ Γ} zero)))

  completeness : {F : Form} → [] ⊫ F → [] ⊢ F
  completeness {F} ⊫F = ⊩ᶠ→⊢ (⊫F tt)













