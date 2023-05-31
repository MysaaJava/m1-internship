{-# OPTIONS --prop #-}

module ListUtil where

  open import Data.List using (List; _∷_; []) public

  private
    variable
      T : Set₀
      L : List T
      L' : List T
      L'' : List T
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

  refl⊆ : L ⊆ L
  refl⊆ = zero⊆

  tran⊆ : L ⊆ L' → L' ⊆ L'' → L ⊆ L''
  tran⊆ zero⊆ h2 = h2
  tran⊆ (next⊆ h1) h2 = tran⊆ h1 (retro⊆ h2)
  
  {- ⊂ : We can remove elements anywhere on the list, no duplicates, no reordering -}
  data _⊂_ : List T → List T → Prop where
    zero⊂ : [] ⊂ L
    both⊂ : L ⊂ L' → (A ∷ L) ⊂ (A ∷ L')
    next⊂ : L ⊂ L' → L ⊂ (A ∷ L')

  ⊆→⊂ : L ⊆ L' → L ⊂ L'
  refl⊂ : L ⊂ L
  ⊆→⊂ {L = []} h = zero⊂
  ⊆→⊂ {L = x ∷ L} zero⊆ = both⊂ (refl⊂)
  ⊆→⊂ {L = x ∷ L} (next⊆ h) = next⊂ (⊆→⊂ h)
  refl⊂ = ⊆→⊂ refl⊆

  tran⊂ : L ⊂ L' → L' ⊂ L'' → L ⊂ L''
  tran⊂ zero⊂ h2 = zero⊂
  tran⊂ (both⊂ h1) (both⊂ h2) = both⊂ (tran⊂ h1 h2)
  tran⊂ (both⊂ h1) (next⊂ h2) = next⊂ (tran⊂ (both⊂ h1) h2)
  tran⊂ (next⊂ h1) (both⊂ h2) = next⊂ (tran⊂ h1 h2)
  tran⊂ (next⊂ h1) (next⊂ h2) = next⊂ (tran⊂ (next⊂ h1) h2)
  
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
    dup⊂⁺ : L ⊂⁺ A ∷ L' → A ∷ L ⊂⁺ A ∷ L'

  ⊂→⊂⁺ : L ⊂ L' → L ⊂⁺ L'
  ⊂→⊂⁺ {L' = []} zero⊂ = zero⊂⁺
  ⊂→⊂⁺ {L' = x ∷ L'} zero⊂ = next⊂⁺ (⊂→⊂⁺ zero⊂)
  ⊂→⊂⁺ (both⊂ h) = dup⊂⁺ (next⊂⁺ (⊂→⊂⁺ h))
  ⊂→⊂⁺ (next⊂ h) = next⊂⁺ (⊂→⊂⁺ h)
  refl⊂⁺ : L ⊂⁺ L
  refl⊂⁺ = ⊂→⊂⁺ refl⊂
  tran⊂⁺ : L ⊂⁺ L' → L' ⊂⁺ L'' → L ⊂⁺ L''
  tran⊂⁺ zero⊂⁺ zero⊂⁺ = zero⊂⁺
  tran⊂⁺ zero⊂⁺ (next⊂⁺ h2) = next⊂⁺ h2
  tran⊂⁺ (next⊂⁺ h1) (next⊂⁺ h2) = next⊂⁺ (tran⊂⁺ (next⊂⁺ h1) h2)
  tran⊂⁺ (next⊂⁺ h1) (dup⊂⁺ h2) = tran⊂⁺ h1 h2
  tran⊂⁺ (dup⊂⁺ h1) (next⊂⁺ h2) = next⊂⁺ (tran⊂⁺ (dup⊂⁺ h1) h2)
  tran⊂⁺ (dup⊂⁺ h1) (dup⊂⁺ h2) = dup⊂⁺ (tran⊂⁺ h1 (dup⊂⁺ h2))

  retro⊂⁺ : A ∷ L ⊂⁺ L' → L ⊂⁺ L'
  retro⊂⁺ (next⊂⁺ h) = next⊂⁺ (retro⊂⁺ h)
  retro⊂⁺ (dup⊂⁺ h) = h
  
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
  ⊂⁺→∈* : L ⊂⁺ L' → L ∈* L'
  refl∈* {L = []} = zero∈*
  refl∈* {L = x ∷ L} = next∈* zero∈ (⊂⁺→∈* (next⊂⁺ refl⊂⁺))
  ⊂⁺→∈* zero⊂⁺ = refl∈*
  ⊂⁺→∈* {L = []} (next⊂⁺ h) = zero∈*
  ⊂⁺→∈* {L = x ∷ L} (next⊂⁺ h) = next∈* (next∈ (mon∈∈* zero∈ (⊂⁺→∈* h))) (⊂⁺→∈* (retro⊂⁺ (next⊂⁺ h)))
  ⊂⁺→∈* (dup⊂⁺ h) = next∈* zero∈ (⊂⁺→∈* h)

  -- Allows to grow ∈* to the right
  right∈* : L ∈* L' → L ∈* (A ∷ L')
  right∈* zero∈* = zero∈*
  right∈* (next∈* x h) = next∈* (next∈ x) (right∈* h)

  both∈* : L ∈* L' → (A ∷ L) ∈* (A ∷ L')
  both∈* zero∈* = next∈* zero∈ zero∈*
  both∈* (next∈* x h) = next∈* zero∈ (next∈* (next∈ x) (right∈* h))

  tran∈* : L ∈* L' → L' ∈* L'' → L ∈* L''
  tran∈* {L = []} = λ x x₁ → zero∈*
  tran∈* {L = x ∷ L} (next∈* x₁ h1) h2 = next∈* (mon∈∈* x₁ h2) (tran∈* h1 h2)

  ⊆→∈* : L ⊆ L' → L ∈* L'
  ⊆→∈* h = ⊂⁺→∈* (⊂→⊂⁺ (⊆→⊂ h))
