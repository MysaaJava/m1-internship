{-# OPTIONS --prop #-}
module prop where


open import Agda.Builtin.String using (String)
open import Data.String.Properties using (_==_)
open import Data.List using (List; _∷_; [])



d-C : [] ⊢ ((Var "Q") [⇒] (Var "R")) [⇒] ((Var "P") [⇒] (Var "Q")) [⇒] (Var "P") [⇒] (Var "R")
d-C = lam (lam (lam (app (succ (succ zero)) (app (succ zero) zero))))


ρ₀ : Env
ρ₀ "P" = ⊥
ρ₀ "Q" = ⊤
ρ₀ _ = ⊥

cex-d : ([] ⊢ (((Var "P") [⇒] (Var "Q")) [⇒] (Var "P"))) → ⊥
cex-d h = ⟦ h ⟧d {ρ₀} tt λ x → tt



Pierce = {P Q : Prop} → ((P → Q) → P) → P
TND : Prop → Prop
TND P = P ∨ (¬ P)

P→TND : Pierce → {P : Prop} → TND P
nnTND : {P : Prop} → ¬ (¬ (P ∨ ¬ P))
nnTND ntnd = ntnd (inj₂ λ p → ntnd (inj₁ p))
P→TND pierce {P} = pierce {TND P} {⊥} (λ p → case⊥ (nnTND p))



{- Kripke Models -}


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














