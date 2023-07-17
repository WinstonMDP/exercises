module sets where

data _and_ : Set → Set → Set where
    _∧_ : {x y : Set} → x → y → x and y
infixl 40 _and_
infixl 40 _∧_

data _≡_ : Set → Set → Set where
    eq : {x y : Set} → (x → y) and (y → x) → x ≡ y
infixr 30 _≡_

straight : {x y : Set} → x ≡ y → x → y
straight (eq (z ∧ w)) = z

back : {x y : Set} → x ≡ y → y → x
back (eq (z ∧ w)) = w

data ∃ : {x : Set} → (z : x → Set) → Set where
    exists : {x : Set} → (y : x) → (z : x → Set) → z y → ∃ z

postulate
    𝕊 : Set
    _∈_ : 𝕊 → 𝕊 → Set
infix 50 _∈_

postulate
    _==_ : 𝕊 → 𝕊 → Set
    ==-def : (x y z : 𝕊) → ((z ∈ x ≡ z ∈ y) ≡ x == y)
infixr 50 _==_

postulate
    eq_ax : (x y : 𝕊) → (x == y) → (z : 𝕊) → (x ∈ z ≡ y ∈ z)
    pair_ax : (x y : 𝕊) → ∃ λ { z → x ∈ z and y ∈ z }
    ∪ : 𝕊 → 𝕊
    ∪-def : (x y : 𝕊) → (∃ λ { z → x ∈ z and z ∈ y }) ≡ x ∈ ∪ y
    _⊆_ : 𝕊 → 𝕊 → Set
    ⊆-def : (x y : 𝕊) → ((z : 𝕊) → z ∈ x → z ∈ y) ≡ x ⊆ y 
infixr 50 _⊆_
 
th-1 : (x y : 𝕊) → x ⊆ y → (∪ x) ⊆ (∪ y)
th-1 x y z = straight (⊆-def (∪ x) (∪ y)) λ w i → straight (∪-def w y) (lm-1 w (back (∪-def w x) i))
    where lm-1 : (a : 𝕊) → ∃ (λ { z → a ∈ z and z ∈ x }) → ∃ (λ { z → a ∈ z and z ∈ y })
          lm-1 a (exists b _ (c ∧ d)) = exists b (λ { z → a ∈ z and z ∈ y }) (c ∧ (back (⊆-def x y) z b d))
