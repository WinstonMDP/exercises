module sets where

postulate
    𝕊 : Set
    _∈_ : 𝕊 → 𝕊 → Set
infix 50 _∈_

data _And_ : Set → Set → Set where
    _and_ : (x y : Set) → x And y
infixl 40 _And_
infixl 40 _and_

data _≡_ : Set → Set → Set where
    eql : (a b : Set) → a → b And b → a → a ≡ b
infixr 25 _≡_

data _==_ : 𝕊 → 𝕊 → Set where
    eqr : (x y z : 𝕊) → z ∈ x ≡ z ∈ y → x == y
infixr 50 _==_

postulate
    eq_ax : (x y : 𝕊) → (x == y) → (z : 𝕊) → (x ∈ z ≡ y ∈ z)

data ∃ : (x : Set) → (z : x → Set) → Set where
    exists : (x : Set) → (y : x) → (z : x → Set) → z y → ∃ x z

postulate
    pair_ax : (x y : 𝕊) → ∃ 𝕊 λ { z → x ∈ z And y ∈ z }
    ∪ : 𝕊 → 𝕊
    ∪_def : (x y : 𝕊) → x ∈ ∪ y ≡ ∃ 𝕊 λ { z → x ∈ z And z ∈ y }

data _⊆_ : 𝕊 → 𝕊 → Set where
    subseteq : (x y : 𝕊) → ((z : 𝕊) → z ∈ x → z ∈ y) → x ⊆ y
infixr 50 _⊆_

first_proof : (x y : 𝕊) → x ⊆ y → (∪ x) ⊆ (∪ y)
first_proof x y (subseteq x y z) = subseteq (∪ x) (∪ y) λ w i → {!!}
