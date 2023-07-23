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

and-double : {x : Set} → x ≡ x and x
and-double = ≡-def (and-def (λ y → and-def y y) λ { (and-def y _) → y })

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

⊥-to-everything : {x : Set} → ⊥ → x
⊥-to-everything ()
       
data ¬ : Set → Set where
    ¬-def : {x : Set} → (x → ⊥) → ¬ x

¬-to-⊥ : {x : Set} → ¬ x → x → ⊥
¬-to-⊥ (¬-def y) = y

data _or_ : Set → Set → Set where
    or-def-left : {x y : Set} → x → x or y
    or-def-right : {x y : Set} → y → x or y
infixl 35 _or_

or-both-application : {x y : Set} → (x or y) → {z : Set → Set} → {w : Set → Set} → (x → z x) and (y → w y) → (z x or w y)
or-both-application {x} {y} (or-def-left i) {z} {w} (and-def j _) = or-def-left {z x} {w y} (j i)
or-both-application {x} {y} (or-def-right i) {z} {w} (and-def _ j) = or-def-right {z x} {w y} (j i)

or-double : {x : Set} → x ≡ x or x
or-double {x} = ≡-def (and-def (λ y → or-def-left y) λ { (or-def-left y) → y ; (or-def-right y) → y })

∘ : {x y z : Set} → (y → z) → (x → y) → (x → z)
∘ w i = λ j → w (i j)   

postulate
    𝕊 : Set
    _∈_ : 𝕊 → 𝕊 → Set
infix 50 _∈_

data _==_ : 𝕊 → 𝕊 → Set where
    ==-def : {x y : 𝕊} → ((z : 𝕊) → z ∈ x ≡ z ∈ y) → x == y
infixr 50 _==_

==-logic-eq : {x y : 𝕊} → x == y → (z : 𝕊) → z ∈ x ≡ z ∈ y
==-logic-eq (==-def x) = x

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

pair : 𝕊 → 𝕊 → 𝕊
pair x y = ∃-element (pair-ax x y)

pair-∈ : {x y z : 𝕊} → z ∈ pair x y → z == x or z == y
pair-∈ {x} {y} {z} w = and-right (∃-application (pair-ax x y)) z w

pair-left-∈ : {x y : 𝕊} → x ∈ pair x y
pair-left-∈ {x} {y} = ∘ and-left and-left (∃-application (pair-ax x y))

pair-right-∈ : {x y : 𝕊} → y ∈ pair x y
pair-right-∈ {x} {y} = ∘ and-right and-left (∃-application (pair-ax x y))

singleton : 𝕊 → 𝕊
singleton x = pair x x

singleton-∈ : {x y : 𝕊} → y ∈ singleton x → y == x
singleton-∈ z = back or-double (pair-∈ z)

singleton-single-∈ : {x : 𝕊} → x ∈ singleton x
singleton-single-∈ {x} = pair-left-∈

data 𝕊-∃! : (𝕊 → Set) → Set where
    𝕊-∃!-def : (x : 𝕊 → Set) → (y : 𝕊) → x y → ((z : 𝕊) → x z → y == z) → 𝕊-∃! x

𝕊-∃!-∃ : {x : 𝕊 → Set} → 𝕊-∃! x → ∃ x
𝕊-∃!-∃ (𝕊-∃!-def x y z _) = ∃-def x y z

union : 𝕊 → 𝕊 → 𝕊
union x y = ∪ (pair x y)

union-def : (x y z : 𝕊) → z ∈ (union x y) ≡ z ∈ x or z ∈ y
union-def x y z = ≡-def (
                      and-def
                      (λ w → lm-2 w (pair-∈ (and-right (lm-1 w))))
                      λ {
                          (or-def-left w) → to
                                                (∪-def z (pair x y))
                                                (∃-def (λ i → z ∈ i and i ∈ pair x y) x (and-def w pair-left-∈));
                          (or-def-right w) → to
                                                 (∪-def z (pair x y))
                                                 (∃-def (λ i → z ∈ i and i ∈ pair x y) y (and-def w pair-right-∈))})
    where lm-1 : (w : z ∈ union x y) → z ∈ ∃-element (back (∪-def z (pair x y)) w) and ∃-element (back (∪-def z (pair x y)) w) ∈ pair x y
          lm-1 w = ∃-application (back (∪-def z (pair x y)) w)
          lm-2 : (w : z ∈ union x y) → ∃-element (back (∪-def z (pair x y)) w) == x or ∃-element (back (∪-def z (pair x y)) w) == y → z ∈ x or z ∈ y
          lm-2 w i = or-both-application i (and-def (∘ (λ j → to (j z) (and-left (lm-1 w))) ==-logic-eq) (∘ (λ j → to (j z) (and-left (lm-1 w))) ==-logic-eq))

∅ : 𝕊

postulate
    infinity-ax : ∃ λ x → ∅ ∈ x and ((y : 𝕊) → y ∈ x → (union y (singleton y)) ∈ x)

∅ = ∃-element (subsets-ax (∃-element infinity-ax) λ _ → ⊥)

∅-empty : (x : 𝕊) → ¬ (x ∈ ∅)
∅-empty x = ¬-def λ y → and-right (to (∃-application (subsets-ax (∃-element infinity-ax) (λ _ → ⊥)) x) y)

∅-𝕊-∃! : 𝕊-∃! λ x → (y : 𝕊) → ¬(y ∈ x)
∅-𝕊-∃! = 𝕊-∃!-def
             (λ x → (y : 𝕊) → ¬ (y ∈ x))
             ∅
             (λ y → ¬-def λ z → ¬-to-⊥ (∅-empty y) z)
             λ y z → ==-def λ w → ≡-def (and-def (λ i → ⊥-to-everything (¬-to-⊥ (∅-empty w) i)) λ i → ⊥-to-everything (¬-to-⊥ (z w) i))
    
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
x-∈-x-⊥ x = ¬-def λ y → ¬-to-⊥ (and-right (∃-application (foundation-ax (singleton x) (∃-def (λ z → z ∈ singleton x) x singleton-single-∈))) x singleton-single-∈) (lm-3 y)
    where lm-2 : ∃-element (foundation-ax (singleton x) (∃-def (λ z → z ∈ singleton x) x singleton-single-∈)) == x
          lm-2 = (back or-double) (
                     (and-right (∃-application (pair-ax x x)))
                     (∃-element (foundation-ax (singleton x) (∃-def (λ z → z ∈ singleton x) x singleton-single-∈)))
                     (and-left (∃-application (foundation-ax (singleton x) (∃-def (λ z → z ∈ singleton x) x singleton-single-∈)))))
          lm-3 : (x ∈ x) → x ∈ ∃-element (foundation-ax (singleton x) (∃-def (λ z → z ∈ singleton x) x singleton-single-∈))
          lm-3 y = back (==-logic-eq lm-2 x) y

set-of-all-sets-⊥ : ¬(∃ λ x → (y : 𝕊) → y ∈ x)
set-of-all-sets-⊥ = ¬-def λ { (∃-def .(λ x → (y : 𝕊) → y ∈ x) z w) → ¬-to-⊥ (x-∈-x-⊥ z) (w z) }
