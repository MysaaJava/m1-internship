{-# OPTIONS --prop #-}

open import Agda.Builtin.Nat

module FirstOrderLogic (TV : Set) (F : Nat → Set) (R : Nat → Set) where

  open import PropUtil
  open import ListUtil

  mutual
    data FArgs : Nat → Set where
      zero : FArgs 0
      next : {n : Nat} → FArgs n → Term → FArgs (suc n)
    data Term : Set where
      Var : TV → Term
      Fun : {n : Nat} → F n → FArgs n → Term
      
  data RArgs : Nat → Set where
    zero : RArgs 0
    next : {n : Nat} → RArgs n → Term → RArgs (suc n)
    
  data Form : Set where
    Rel : {n : Nat} → R n → (RArgs n) → Form
    _⇒_ : Form → Form → Form
    _∧∧_ : Form → Form → Form
    _∀∀_ : TV → Form → Form
    
  infixr 10 _∧∧_
  infixr 8 _⇒_

