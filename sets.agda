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

to : {x y : Set} → x ≡ y → x → y
to (≡-def (and-def z _)) = z

back : {x y : Set} → x ≡ y → y → x
back (≡-def (and-def _ z)) = z

data ∃ : {x : Set} → (x → Set) → Set where
    ∃-def : {x : Set} → (y : x → Set) → (z : x) → y z → ∃ y

∃-element : {x : Set} → {y : x → Set} → ∃ y → x
∃-element (∃-def _ z _) = z

∃-application : {x : Set} → {y : x → Set} → (z : ∃ y) → y (∃-element z)
∃-application (∃-def _ _ w) = w

data ⊥ : Set where

data ¬ : Set → Set where
    ¬-def : (x : Set) → (x → ⊥) → ¬ x

¬-to-⊥ : {x : Set} → ¬ x → x → ⊥
¬-to-⊥ (¬-def _ y) = y
    
data _or_ : Set → Set → Set where
    or-def-left : (x y : Set) → x → x or y
    or-def-right : (x y : Set) → y → x or y
infixl 35 _or_

or-absorption : {x : Set} → x or x → x
or-absorption (or-def-left _ _ y) = y
or-absorption (or-def-right _ _ y) = y

or-both-application : {x y : Set} → (x or y) → {z : Set → Set} → {w : Set → Set} → (x → z x) and (y → w y) → (z x or w y)
or-both-application {x} {y} (or-def-left .x .y i) {z} {w} (and-def j _) = or-def-left (z x) (w y) (j i)
or-both-application {x} {y} (or-def-right .x .y i) {z} {w} (and-def _ j) = or-def-right (z x) (w y) (j i)

∘ : {x y z : Set} → (y → z) → (x → y) → (x → z)
∘ w i = λ j → w (i j)   

postulate
    𝕊 : Set
    _∈_ : 𝕊 → 𝕊 → Set
infix 50 _∈_

data _==_ : 𝕊 → 𝕊 → Set where
    ==-def : (x y : 𝕊) → ((z : 𝕊) → z ∈ x ≡ z ∈ y) → x == y
infixr 50 _==_

==-logic-eq : {x y : 𝕊} → x == y → (z : 𝕊) → z ∈ x ≡ z ∈ y
==-logic-eq (==-def _ _ x) = x

data _⊆_ : 𝕊 → 𝕊 → Set where
    ⊆-def : (x y : 𝕊) → ((z : 𝕊) → z ∈ x → z ∈ y) → x ⊆ y 
infix 50 _⊆_

⊆-to : (x y : 𝕊) → x ⊆ y → ((z : 𝕊) → z ∈ x → z ∈ y)
⊆-to _ _ (⊆-def _ _ z) = z

postulate
    eq-ax : (x y : 𝕊) → x == y → (z : 𝕊) → x ∈ z ≡ y ∈ z
    pair-ax : (x y : 𝕊) → ∃ λ z → x ∈ z and y ∈ z and ((w : 𝕊) → w ∈ z → w == x or w == y)
    ∪ : 𝕊 → 𝕊 -- union axiom
    ∪-def : (x y : 𝕊) → (∃ λ z → x ∈ z and z ∈ y) ≡ x ∈ ∪ y
    𝓟 : 𝕊 → 𝕊 -- power axiom
    𝓟-def : (x y : 𝕊) → x ⊆ y ≡ x ∈ (𝓟 y)
    foundation-ax : (x : 𝕊) → ∃ (λ y → y ∈ x) → ∃ λ y → y ∈ x and ((z : 𝕊) → z ∈ x → ¬(z ∈ y))
    subsets-ax : (x : 𝕊) → (y : 𝕊 → Set) → ∃ λ z → (w : 𝕊) → w ∈ z ≡ w ∈ x and y w

pair-ax-∈ : {x y z : 𝕊} → z ∈ ∃-element (pair-ax x y) → z == x or z == y
pair-ax-∈ {x} {y} {z} w = and-right (∃-application (pair-ax x y)) z w
    
data 𝕊-∃! : (𝕊 → Set) → Set where
    𝕊-∃!-def : (x : 𝕊 → Set) → (y : 𝕊) → x y → ((z : 𝕊) → x z → y == z) → 𝕊-∃! x

𝕊-∃!-∃ : {x : 𝕊 → Set} → 𝕊-∃! x → ∃ x
𝕊-∃!-∃ (𝕊-∃!-def x y z _) = ∃-def x y z

data be-∅ : 𝕊 → Set where
    be-∅-def : (x : 𝕊) → (y : (z : 𝕊) → ¬(z ∈ x)) → be-∅ x

-- ∅ : 𝕊
-- ∅ = {!!}

-- ∃-element (subsets-ax ∅ λ x → ⊥)

-- ∅-𝕊-∃! : 𝕊-∃! λ x → be-∅ x
-- ∅-𝕊-∃! = {!!}
    
union : 𝕊 → 𝕊 → 𝕊
union x y = ∪ (∃-element (pair-ax x y))

union-def : (x y z : 𝕊) → z ∈ (union x y) ≡ z ∈ x or z ∈ y
union-def x y z = ≡-def (
                      and-def (λ w → lm-2 w (pair-ax-∈ (and-right (lm-1 w))))
                      λ {
                          (or-def-left _ _ w) → to
                                                    (∪-def z (∃-element (pair-ax x y)))
                                                    (∃-def (λ i → z ∈ i and i ∈ ∃-element (pair-ax x y)) x (and-def w ((∘ and-left and-left) (∃-application (pair-ax x y)))));
                          (or-def-right _ _ w) → to
                                                     (∪-def z (∃-element (pair-ax x y)))
                                                     (∃-def (λ i → z ∈ i and i ∈ ∃-element (pair-ax x y)) y (and-def w (∘ and-right and-left (∃-application (pair-ax x y)))))
                      }
                  )
    where lm-1 : (w : z ∈ (union x y)) → z ∈ ∃-element (back (∪-def z (∃-element (pair-ax x y))) w) and ∃-element (back (∪-def z (∃-element (pair-ax x y))) w) ∈ ∃-element (pair-ax x y)
          lm-1 w = ∃-application (back (∪-def z (∃-element (pair-ax x y))) w)
          lm-2 : (w : z ∈ (union x y)) → ∃-element (back (∪-def z (∃-element (pair-ax x y))) w) == x or ∃-element (back (∪-def z (∃-element (pair-ax x y))) w) == y → z ∈ x or z ∈ y
          lm-2 w i = or-both-application i (and-def (∘ (λ j → to (j z) (and-left (lm-1 w))) ==-logic-eq ) (∘ (λ j → to (j z) (and-left (lm-1 w))) ==-logic-eq))

th-1 : (x y : 𝕊) → x ⊆ y → (∪ x) ⊆ (∪ y)
th-1 x y (⊆-def _ _ z) = ⊆-def (∪ x) (∪ y) λ w i → to (∪-def w y) (lm-1 w (back (∪-def w x) i))
    where lm-1 : (a : 𝕊) → ∃ (λ α → a ∈ α and α ∈ x) → ∃ λ α → a ∈ α and α ∈ y
          lm-1 a (∃-def .(λ α → a ∈ α and α ∈ x) b (and-def c d)) = ∃-def (λ α → a ∈ α and α ∈ y) b (and-def c (z b d))

th-2 : (x : 𝕊) → x ⊆ 𝓟 (∪ x)
th-2 x = ⊆-def x (𝓟 (∪ x)) λ y z → to (𝓟-def y (∪ x)) (⊆-def y (∪ x) λ w i → to (∪-def w x) (∃-def (λ j → w ∈ j and j ∈ x) y (and-def i z)))

th-3 : (x : 𝕊) → ∪ x ⊆ x → ∪ (𝓟 x) ⊆ 𝓟 x
th-3 x (⊆-def .(∪ x) .x y) =
    ⊆-def (∪ (𝓟 x)) (𝓟 x) λ z w → to (𝓟-def z x) (⊆-def z x (λ i j → y i (to (∪-def i x) (∃-def (λ α → i ∈ α and α ∈ x) z (and-def j (lm-1 z (back (∪-def z (𝓟 x)) w)))))))
    where lm-1 : (z : 𝕊) → ∃ (λ α → z ∈ α and α ∈ 𝓟 x) → z ∈ x 
          lm-1 z (∃-def .(λ α → z ∈ α and α ∈ 𝓟 x) a (and-def b c)) = ⊆-to a x ((back (𝓟-def a x)) c) z b

x-∈-x-⊥ : (x : 𝕊) → ¬(x ∈ x)
x-∈-x-⊥ x = ¬-def (x ∈ x) λ y → ¬-to-⊥ (and-right (∃-application (foundation-ax (∃-element (pair-ax x x)) (∃-def (λ z → z ∈ ∃-element (pair-ax x x)) x lm-1))) x lm-1) (lm-3 y)
    where lm-1 : x ∈ ∃-element (pair-ax x x)
          lm-1 = and-left (and-left (∃-application (pair-ax x x)))
          lm-2 : ∃-element (foundation-ax (∃-element (pair-ax x x)) (∃-def (λ z → z ∈ ∃-element (pair-ax x x)) x lm-1)) == x
          lm-2 = or-absorption (
                     (and-right (∃-application (pair-ax x x)))
                     (∃-element (foundation-ax (∃-element (pair-ax x x)) (∃-def (λ z → z ∈ ∃-element (pair-ax x x)) x lm-1)))
                     (and-left (∃-application (foundation-ax (∃-element (pair-ax x x)) (∃-def (λ z → z ∈ ∃-element (pair-ax x x)) x lm-1))))
                 )
          lm-3 : (x ∈ x) → x ∈ ∃-element (foundation-ax (∃-element (pair-ax x x)) (∃-def (λ z → z ∈ ∃-element (pair-ax x x)) x lm-1))
          lm-3 y = back (==-logic-eq lm-2 x) y


set-of-all-sets-⊥ : ¬(∃ λ x → (y : 𝕊) → y ∈ x)
set-of-all-sets-⊥ = ¬-def (∃ (λ x → (y : 𝕊) → y ∈ x)) λ { (∃-def .(λ x → (y : 𝕊) → y ∈ x) z w) → ¬-to-⊥ (x-∈-x-⊥ z) (w z) }
