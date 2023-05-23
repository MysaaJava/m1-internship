module test3 where

open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)

+-assoc : Set
+-assoc = ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z

open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (refl; cong)

+-assoc-proof : +-assoc

+-assoc-proof zero y z = refl
+-assoc-proof (suc x') y z = cong suc (+-assoc-proof x' y z) 

