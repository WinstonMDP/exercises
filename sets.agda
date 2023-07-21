module sets where

data _and_ : Set → Set → Set where
    and-def : {x y : Set} → x → y → x and y
infixl 40 _and_
and-left : {x y : Set} → x and y → x
and-left (and-def z _) = z
         
and-right : {x y : Set} → x and y → y
and-right (and-def _ z) = z

data _≡_ : Set → Set → Set where
    ≡-def : {x y : Set} → (x → y) and (y → x) → x ≡ y
infixr 30 _≡_

straight : {x y : Set} → x ≡ y → x → y
straight (≡-def (and-def z _)) = z

back : {x y : Set} → x ≡ y → y → x
back (≡-def (and-def _ z)) = z

data ∃ : {x : Set} → (y : x → Set) → Set where
    ∃-def : {x : Set} → (y : x → Set) → (z : x) → y z → ∃ y

∃-element : {x : Set} → {y : x → Set} → ∃ y → x
∃-element (∃-def _ z _) = z

∃-application : {x : Set} → {y : x → Set} → (z : ∃ y) → y (∃-element z)
∃-application (∃-def _ _ w) = w

data ⊥ : Set where

data ¬ : Set → Set where
    ¬-def : (x : Set) → (x → ⊥) → ¬ x

to-⊥ : {x : Set} → ¬ x → x → ⊥
to-⊥ (¬-def _ y) = y
    
data _or_ : Set → Set → Set where
    or-def-l : (x y : Set) → x → x or y
    or-def-r : (x y : Set) → y → x or y
infixl 30 _or_
    
or-absorption : (x : Set) → x or x → x
or-absorption _ (or-def-l _ _ y) = y
or-absorption _ (or-def-r _ _ y) = y
    
postulate
    𝕊 : Set
    _∈_ : 𝕊 → 𝕊 → Set
infix 50 _∈_

data _==_ : 𝕊 → 𝕊 → Set where
    ==-def : (x y z : 𝕊) → (z ∈ x ≡ z ∈ y) → x == y
infixr 50 _==_

data _⊆_ : 𝕊 → 𝕊 → Set where
    ⊆-def : (x y : 𝕊) → ((z : 𝕊) → z ∈ x → z ∈ y) → x ⊆ y 
infix 50 _⊆_

postulate
    eq-ax : (x y : 𝕊) → x == y → (z : 𝕊) → x ∈ z ≡ y ∈ z
    pair-ax : (x y : 𝕊) → ∃ λ z → x ∈ z and y ∈ z and ((w : 𝕊) → w ∈ z → w == x or w == y)
    ∪ : 𝕊 → 𝕊 -- union axiom
    ∪-def : (x y : 𝕊) → (∃ λ z → x ∈ z and z ∈ y) ≡ x ∈ ∪ y
    𝓟 : 𝕊 → 𝕊 -- power axiom
    𝓟-def : (x y : 𝕊) → x ⊆ y ≡ x ∈ (𝓟 y)
    foundation-ax : (x : 𝕊) → ∃ (λ y → y ∈ x) → ∃ λ y → y ∈ x and ((z : 𝕊) → z ∈ x → ¬(z ∈ y))
    
th-1 : (x y : 𝕊) → x ⊆ y → (∪ x) ⊆ (∪ y)
th-1 x y (⊆-def _ _ z) = ⊆-def (∪ x) (∪ y) λ w i → straight (∪-def w y) (lm-1 w (back (∪-def w x) i))
    where lm-1 : (a : 𝕊) → ∃ (λ α → a ∈ α and α ∈ x) → ∃ λ α → a ∈ α and α ∈ y
          lm-1 a (∃-def .(λ α → a ∈ α and α ∈ x) b (and-def c d)) = ∃-def (λ α → a ∈ α and α ∈ y) b (and-def c (z b d))

th-2 : (x : 𝕊) → x ⊆ 𝓟 (∪ x)
th-2 x = ⊆-def x (𝓟 (∪ x)) λ y z → straight (𝓟-def y (∪ x)) (⊆-def y (∪ x) λ w i → straight (∪-def w x) (∃-def (λ j → w ∈ j and j ∈ x) y (and-def i z)))

th-3 : (x : 𝕊) → ∪ x ⊆ x → ∪ (𝓟 x) ⊆ 𝓟 x
th-3 x (⊆-def .(∪ x) .x y) =
    ⊆-def (∪ (𝓟 x)) (𝓟 x) λ z w → straight (𝓟-def z x) (⊆-def z x (λ i j → y i (straight (∪-def i x) (∃-def (λ α → i ∈ α and α ∈ x) z (and-def j (lm-2 z (back (∪-def z (𝓟 x)) w)))))))
    where lm-1 : (a b : 𝕊) → a ⊆ b → (c : 𝕊) → c ∈ a → c ∈ b
          lm-1 _ _ (⊆-def _ _ e) c f = e c f
          lm-2 : (z : 𝕊) → ∃ (λ α → z ∈ α and α ∈ 𝓟 x) → z ∈ x 
          lm-2 z (∃-def .(λ α → z ∈ α and α ∈ 𝓟 x) a (and-def b c)) = lm-1 a x ((back (𝓟-def a x)) c) z b

x-∈-x-⊥ : (x : 𝕊) → ¬(x ∈ x)
x-∈-x-⊥ x = {!!}

set-of-all-sets-⊥ : ¬(∃ λ x → (y : 𝕊) → y ∈ x)
set-of-all-sets-⊥ = ¬-def (∃ (λ x → (y : 𝕊) → y ∈ x)) λ { (∃-def .(λ x → (y : 𝕊) → y ∈ x) z w) → to-⊥ (x-∈-x-⊥ z) (w z) }
