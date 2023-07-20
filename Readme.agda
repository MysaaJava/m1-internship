{-# OPTIONS --prop --rewriting #-}

module Readme where

-- We will use String as propositional variables
postulate String : Set
{-# BUILTIN STRING String #-}

open import PropUtil
open import ListUtil

-- We can use the basic propositional logic
open import ZOL String

-- Here is an example of a propositional formula and its proof
-- The formula is (Q → R) → (P → Q) → P → R
zol-ex : [] ⊢ ((Var "Q") ⇒ (Var "R")) ⇒ ((Var "P") ⇒ (Var "Q")) ⇒ (Var "P") ⇒ (Var "R")
zol-ex = lam (lam (lam (app (zero $ next∈ $ next∈ zero∈) (app (zero $ next∈ zero∈) (zero zero∈)))))

-- We can with the basic interpretation ⟦_⟧ prove that some formulæ are not provable
-- For example, we can disprove (P → Q) → P 's provability as we can construct an
-- environnement where the statement doesn't hold
ρ₀ : Env
ρ₀ "P" = ⊥
ρ₀ "Q" = ⊤
ρ₀ _ = ⊥
zol-cex : ([] ⊢ (((Var "P") ⇒ (Var "Q")) ⇒ (Var "P"))) → ⊥
zol-cex h = ⟦ h ⟧ᵈ {ρ₀} tt λ x → tt

-- But this is not enough to show the non-provability of every non-provable statement.
-- Let's take as an example Pierce formula : ((P → Q) → P) → P
-- This statement is equivalent to the law of excluded middle (Tertium Non Datur)
-- We show that fact in Agda's proposition system

Pierce = {P Q : Prop} → ((P → Q) → P) → P
TND : Prop → Prop
TND P = P ∨ (¬ P)

-- Lemma: The double negation of the TND is always true
-- (You cannot show that having neither a proposition nor its negation is impossible
nnTND : {P : Prop} → ¬ (¬ (P ∨ ¬ P))
nnTND ntnd = ntnd (inj₂ λ p → ntnd (inj₁ p))
P→TND : Pierce → {P : Prop} → TND P
P→TND pierce {P} = pierce {TND P} {⊥} (λ p → case⊥ (nnTND p))
TND→P : ({P : Prop} → TND P) → Pierce
TND→P tnd {P} {Q} pqp = dis (tnd {P}) (λ p → p) (λ np → pqp (λ p → case⊥ (np p)))


-- So we have to use a model that is more powerful : Kripke models
-- With those models, one can describe a frame in which the pierce formula doesn't hold
-- As we have that any proven formula is *true* in a kripke model, this shows
-- that the Pierce formula cannot be proven

-- We import the general definition of Kripke models
open import ZOLKripke String

-- We will now create a specific Kripke model in which Pierce formula doesn't hold

module PierceDisproof where
  
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
  open Kripke PierceW
  open PierceWorld using (w₁ ; w₂ ; w₁₁ ; w₁₂ ; w₂₂ ; w₂A)
  
  -- Now we can write the «instance» of the Pierce formula which doesn't hold in our world
  PierceF : Form 
  PierceF = (((Var "A" ⇒ Var "B") ⇒ Var "A") ⇒ Var "A")
  
  -- Now we show that it does not hold in w₁ but holds in w₂
  Pierce⊥w₁ : ¬(w₁ ⊩ᶠ PierceF)
  Pierce⊤w₂ : w₂ ⊩ᶠ PierceF
  
  -- A does not hold in w₁
  NotAw₁ : ¬(w₁ ⊩ᶠ (Var "A"))
  NotAw₁ ()
  -- B does not hold in w₂ while A holds
  NotBw₂ : ¬(w₂ ⊩ᶠ (Var "B"))
  NotBw₂ ()
  -- Therefore, (A → B) does not hold in w₁
  NotABw₁ : ¬(w₁ ⊩ᶠ (Var "A" ⇒ Var "B"))
  NotABw₁ h = NotBw₂ (h w₁₂ w₂A)
  -- So the hypothesis of the pierce formula does hold in w₁
  -- as its premice does not hold in w₁ and its conclusion does hold in w₂
  PierceHypw₁ : w₁ ⊩ᶠ ((Var "A" ⇒ Var "B") ⇒ Var "A")
  PierceHypw₁ w₁₁ x = case⊥ (NotABw₁ x)
  PierceHypw₁ w₁₂ x = w₂A
  -- So, as the conclusion of the pierce formula does not hold in w₁, the pierce formula doesn't hold.
  Pierce⊥w₁ h = case⊥ (NotAw₁ (h w₁₁ PierceHypw₁))
  -- Finally, the formula holds in w₂ as its conclusion is true
  Pierce⊤w₂ w₂₂ h₂ = w₂A

  -- So, if pierce formula would be provable, it would hold in w₁, which it doesn't
  -- therefore it is not provable CQFD
  PierceNotProvable : ¬([] ⊢ PierceF)
  PierceNotProvable h = Pierce⊥w₁ (⟦ h ⟧ {w₁} tt)
  
  
module GeneralizationInZOL where

  -- With Kripke models, we can even prove completeness of ZOL
  -- Using the Universal Kripke Model
  
  -- With a slightly different universal model (using normal and neutral forms),
  -- we can make a normalization proof
  
  -- This normalization proof has first been made in the biggest Kripke model possible
  -- that is, the one using the relation ⊢⁰⁺
  -- But we can also prove it with tighter relations: ∈*, ⊂⁺, ⊂, ⊆

  -- As all those proofs are really similar, we created a NormalizationFrame structure
  -- that computes most of the proofs with only a few lemmas
  open import ZOLNormalization String

  -- We now have access to quote and unquote functions with this
  u1 = NormalizationFrame.u NormalizationTests.Frame⊢
  q1 = NormalizationFrame.q NormalizationTests.Frame⊢
  u2 = NormalizationFrame.u NormalizationTests.Frame⊢⁰
  q2 = NormalizationFrame.q NormalizationTests.Frame⊢⁰
  u3 = NormalizationFrame.u NormalizationTests.Frame∈*
  q3 = NormalizationFrame.q NormalizationTests.Frame∈*
  u4 = NormalizationFrame.u NormalizationTests.Frame⊂⁺
  q4 = NormalizationFrame.q NormalizationTests.Frame⊂⁺
  u5 = NormalizationFrame.u NormalizationTests.Frame⊂
  q5 = NormalizationFrame.q NormalizationTests.Frame⊂
  u6 = NormalizationFrame.u NormalizationTests.Frame⊆
  q6 = NormalizationFrame.q NormalizationTests.Frame⊆

module GeneralizationInIFOL where

  -- We also did implement infinitary first order logic
  -- (i.e. ∀ is like an infinitary ∧)
  -- The proofs works the same with only little modifications

  open import IFOLNormalization String (λ n → String)

  u1 = NormalizationFrame.u NormalizationTests.Frame⊢
  q1 = NormalizationFrame.q NormalizationTests.Frame⊢
  u2 = NormalizationFrame.u NormalizationTests.Frame⊢⁰
  q2 = NormalizationFrame.q NormalizationTests.Frame⊢⁰
  u3 = NormalizationFrame.u NormalizationTests.Frame∈*
  q3 = NormalizationFrame.q NormalizationTests.Frame∈*
  u4 = NormalizationFrame.u NormalizationTests.Frame⊂⁺
  q4 = NormalizationFrame.q NormalizationTests.Frame⊂⁺
  u5 = NormalizationFrame.u NormalizationTests.Frame⊂
  q5 = NormalizationFrame.q NormalizationTests.Frame⊂
  u6 = NormalizationFrame.u NormalizationTests.Frame⊆
  q6 = NormalizationFrame.q NormalizationTests.Frame⊆


module NormalizationInFFOL where

  -- We also did an implementation of the negative fragment
  -- of finitary first order logic (∀ is defined with context extension)

  -- The algebra has been written in this file
  -- There is also the class of Tarski models, written as an example
  open import FFOL

  -- We have also written the syntax (initial model)
  -- (a lot of transport hell, but i did it !)
  open import FFOLInitial

  -- And now, we can finally write the class of Family and Presheaf models
  -- and we can make the proof of completeness of the latter.
  open import FFOLCompleteness



