module intro where

open import Data.Nat using (ℕ; zero; suc; _+_)

data Greeting : Set where
    hello : Greeting

greet : Greeting
greet = hello

data Vec (A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

infixr 5 _∷_

open import Relation.Binary.PropositionalEquality using (refl; cong; _≡_)

+-assoc : Set
+-assoc = ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z

+-assoc-proof : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z

 zero y z = refl
+-assoc-proof (suc x) y z = cong suc (+-assoc-proof x y z)
