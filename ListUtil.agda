{-# OPTIONS --prop #-}

module ListUtil where

  open import Data.List using (List; _∷_; []) public

  private
    variable
      T : Set₀
      L : List T
      L' : List T
      A : T
      B : T


  -- Definition of sublists
  -- Similar definition : {L L' : List T} → L ⊆ L' ++ L
  data _⊆_ : List T → List T → Prop where
    zero⊆ : L ⊆ L
    next⊆ : L ⊆ L' → L ⊆ (A ∷ L')

  -- One useful lemma
  retro⊆ : {L L' : List T} → {A : T} → (A ∷ L) ⊆ L' → L ⊆ L'
  retro⊆ {L' = []} () -- Impossible to have «A∷L ⊆ []»
  retro⊆ {L' = B ∷ L'} zero⊆ = next⊆ zero⊆
  retro⊆ {L' = B ∷ L'} (next⊆ h) = next⊆ (retro⊆ h)

