module sets where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

postulate
    𝕊 : Set
    _∈_ : 𝕊 → 𝕊 → Set
infix 50 _∈_

data List (A : Set) : Set where
  nil  : List A
  _a_ : (x : A) → (y : List A) → List A

data Eq : 𝕊 → 𝕊 → Set where
    _≃_ : (x y z : 𝕊) → z ∈ x ≡ z ∈ y → Eq x y

infixr 50 _≃_
