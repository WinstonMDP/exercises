module sets where

data _and_ : Set → Set → Set where
    and-def : {x y : Set} → x → y → x and y
infixl 40 _and_

data _≡_ : Set → Set → Set where
    ≡-def : {x y : Set} → (x → y) and (y → x) → x ≡ y
infixr 30 _≡_

straight : {x y : Set} → x ≡ y → x → y
straight (≡-def (and-def z _)) = z

back : {x y : Set} → x ≡ y → y → x
back (≡-def (and-def _ z)) = z

data ∃ : {x : Set} → (z : x → Set) → Set where
    ∃-def : {x : Set} → (y : x) → (z : x → Set) → z y → ∃ z
    
postulate
    𝕊 : Set
    _∈_ : 𝕊 → 𝕊 → Set
infix 50 _∈_

data _==_ : 𝕊 → 𝕊 → Set where
    ==-def : (x y z : 𝕊) → (z ∈ x ≡ z ∈ y) → x == y
infixr 50 _==_

postulate
    eq_ax : (x y : 𝕊) → (x == y) → (z : 𝕊) → (x ∈ z ≡ y ∈ z)
    pair_ax : (x y : 𝕊) → ∃ λ { z → x ∈ z and y ∈ z }
    ∪ : 𝕊 → 𝕊
    ∪-def : (x y : 𝕊) → (∃ λ { z → x ∈ z and z ∈ y }) ≡ x ∈ ∪ y

data _⊆_ : 𝕊 → 𝕊 → Set where
    ⊆-def : (x y : 𝕊) → ((z : 𝕊) → z ∈ x → z ∈ y) → x ⊆ y 
infixr 50 _⊆_
 
th-1 : (x y : 𝕊) → x ⊆ y → (∪ x) ⊆ (∪ y)
th-1 x y (⊆-def _ _ z) = ⊆-def (∪ x) (∪ y) λ w i → straight (∪-def w y) (lm-1 w (back (∪-def w x) i))
    where lm-1 : (a : 𝕊) → ∃ (λ { α → a ∈ α and α ∈ x }) → ∃ (λ { α → a ∈ α and α ∈ y })
          lm-1 a (∃-def b _ (and-def c d)) = ∃-def b (λ f → a ∈ f and f ∈ y) (and-def c (z b d))
