module sets where

postulate
    𝕊 : Set
    _∈_ : 𝕊 → 𝕊 → Set
infix 50 _∈_

data _and_ : Set → Set → Set where
    _∧_ : {x y : Set} → x → y → x and y
infixl 40 _and_
infixl 40 _∧_

data _≡_ : Set → Set → Set where
    eq : {x y : Set} → (x → y) and (y → x) → x ≡ y
infixr 30 _≡_

data ∃ : {x : Set} → (z : x → Set) → Set where
    exists : {x : Set} → (y : x) → (z : x → Set) → z y → ∃ z

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

straight : {x y : Set} → x ≡ y → x → y
straight (eq (z ∧ w)) = z

back : {x y : Set} → x ≡ y → y → x
back (eq (z ∧ w)) = w
 
third-proof : (x y : 𝕊) → x ⊆ y → (∪ x) ⊆ (∪ y)
third-proof x y z = third λ q r → straight (∪-def q y) (forth q r)
    where first : (z₁ : 𝕊) → z₁ ∈ x → z₁ ∈ y
          first = back (⊆-def x y) z
          second : (a : 𝕊) → a ∈ ∪ x → ∃ (λ { z → a ∈ z and z ∈ x })
          second a = back (∪-def a x)
          third : ((z₁ : 𝕊) → z₁ ∈ ∪ x → z₁ ∈ ∪ y) → ∪ x ⊆ ∪ y
          third = straight (⊆-def (∪ x) (∪ y))
          forth : (a : 𝕊) → a ∈ ∪ x → ∃ (λ { z → a ∈ z and z ∈ y })
          forth a b = forth-second forth-first
              where forth-first : _
                    forth-first = second a b
                    forth-second : ∃ (λ { z → a ∈ z and z ∈ x }) → ∃ (λ { z → a ∈ z and z ∈ y })
                    forth-second (exists α β (γ ∧ δ)) = exists α (λ { z → a ∈ z and z ∈ y }) (γ ∧ (first α δ))
