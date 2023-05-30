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


  -- Definition of list appartenance
  -- The definition uses reflexivity and never any kind of equality
  infix 3 _∈_
  data _∈_ : T → List T → Prop where
    zero∈ : A ∈ A ∷ L
    next∈ : A ∈ L → A ∈ B ∷ L

  {- RELATIONS BETWEEN LISTS -}

  -- We have the following relations
  --        ↗ ⊂⁰ ↘
  -- ⊆ → ⊂ → ⊂⁺ → ∈*
  infix 4 _⊆_ _⊂_ _⊂⁺_ _⊂⁰_ _∈*_
  {- ⊆ : We can remove elements but only from the head of the list -}
  -- Similar definition : {L L' : List T} → L ⊆ L' ++ L
  data _⊆_ : List T → List T → Prop where
    zero⊆ : L ⊆ L
    next⊆ : L ⊆ L' → L ⊆ (A ∷ L')

  -- One useful lemma
  retro⊆ : {L L' : List T} → {A : T} → (A ∷ L) ⊆ L' → L ⊆ L'
  retro⊆ {L' = []} () -- Impossible to have «A∷L ⊆ []»
  retro⊆ {L' = B ∷ L'} zero⊆ = next⊆ zero⊆
  retro⊆ {L' = B ∷ L'} (next⊆ h) = next⊆ (retro⊆ h)

  {- ⊂ : We can remove elements anywhere on the list, no duplicates, no reordering -}
  data _⊂_ : List T → List T → Prop where
    zero⊂ : [] ⊂ L
    both⊂ : L ⊂ L' → (A ∷ L) ⊂ (A ∷ L')
    next⊂ : L ⊂ L' → L ⊂ (A ∷ L')
    
  {- ⊂⁰ : We can remove elements and reorder the list, as long as we don't duplicate the elements -}
  -----> We do not have unicity of derivation ([A,A] ⊂⁰ [A,A] can be prove by identity or by swapping its two elements
  --> We could do with some counting function, but ... it would not be nice, would it ?
  data _⊂⁰_ : List T → List T → Prop where
    zero⊂⁰ : _⊂⁰_ {T} [] []
    next⊂⁰ : L ⊂⁰ L' → L ⊂⁰ A ∷ L'
    both⊂⁰ : L ⊂⁰ L' → A ∷ L ⊂⁰ A ∷ L'
    swap⊂⁰ : L ⊂⁰ A ∷ B ∷ L' → L ⊂⁰ B ∷ A ∷ L'
    error  : L ⊂⁰ L'
    -- TODOTODOTODOTODO Fix this definition
  {- ⊂⁺ : We can remove and duplicate elements, as long as we don't change the order -}
  data _⊂⁺_ : List T → List T → Prop where
    zero⊂⁺ : _⊂⁺_ {T} [] []
    next⊂⁺ : L ⊂⁺ L' → L ⊂⁺ A ∷ L'
    dup⊂⁺ : A ∷ L ⊂⁺ L' → A ∷ L ⊂⁺ A ∷ L'
  {- ∈* : We can remove or duplicate elements and we can change their order -}
  -- The weakest of all relations on lists
  -- L ∈* L' if all elements of L exists in L' (no consideration for order nor duplication)
  data _∈*_ : List T → List T → Prop where
    zero∈* : [] ∈* L
    next∈* : A ∈ L → L' ∈* L → (A ∷ L') ∈* L

  -- Founding principle
  mon∈∈* : A ∈ L → L ∈* L' → A ∈ L'
  mon∈∈* zero∈ (next∈* x hl) = x
  mon∈∈* (next∈ ha) (next∈* x hl) = mon∈∈* ha hl

  -- We show that the relation is reflexive and is implied by ⊆
  refl∈* : L ∈* L
  ⊆→∈* : L ⊆ L' → L ∈* L'
  refl∈* {L = []} = zero∈*
  refl∈* {L = x ∷ L} = next∈* zero∈ (⊆→∈* (next⊆ zero⊆))
  ⊆→∈* zero⊆ = refl∈*
  ⊆→∈* {L = []} (next⊆ h) = zero∈*
  ⊆→∈* {L = x ∷ L} (next⊆ h) = next∈* (next∈ (mon∈∈* zero∈ (⊆→∈* h))) (⊆→∈* (retro⊆ (next⊆ h)))

  -- Allows to grow ∈* to the right
  right∈* : L ∈* L' → L ∈* (A ∷ L')
  right∈* zero∈* = zero∈*
  right∈* (next∈* x h) = next∈* (next∈ x) (right∈* h)

  -- Allows to grow ∈* from both sides
  both∈* : L ∈* L' → (A ∷ L) ∈* (A ∷ L')
  both∈* zero∈* = next∈* zero∈ zero∈*
  both∈* (next∈* x h) = next∈* zero∈ (next∈* (next∈ x) (right∈* h))
