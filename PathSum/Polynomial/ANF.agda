------------------------------------------------------------------------
-- Presentations of groups
--
-- Boolean polynomials in algebraic normal form, as data that computes
--
-- A path-sum of the hidden shift circuit is known by its values: its
-- phase modulo 1 is ½F and its outputs modulo 2 are G, for Boolean
-- functions F and G of the path variables (PathSum.HiddenShift.Track).
-- Following a reduction of it means computing derivatives of F and
-- substituting into F and G, and checking that a derivative has the
-- shape [HH] asks for.  At a fixed instance those are identities
-- between Boolean expressions in some twenty variables, too many for
-- truth tables.  This module represents Boolean functions by their
-- algebraic normal form (the Reed-Muller expansion, a polynomial over
-- Z₂ in multilinear form) as a sparse binary tree,
--
--   𝟘,  𝟙 (no variables),  node p q = p ⊕ x₀ q (p, q in the others),
--
-- with the operations a reduction needs -- ⊕, ∧, the variables,
-- setting a variable to a constant (restrict, read as insertᵃ),
-- adding an unused variable (weaken, read through punchIn),
-- substituting a polynomial for a variable (substitute) -- each with
-- its value at every point (eval-…).  Every operation builds through
-- node′, which never makes node 𝟘 𝟘, so a polynomial built from them
-- is the unique normal form of its function, and an identity between
-- two such Boolean functions can be checked by computing both normal
-- forms and comparing them (eqᴿ, sound by eqᴿ-sound).  Uniqueness of
-- the normal form is not proved: it is what makes the checks
-- succeed, not what makes them sound.  The same goes for witness,
-- which looks for a point where a polynomial is 1 (witness-sound).
--
-- Nothing here is about path-sums; PathSum.HiddenShift.Stuck uses it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Polynomial.ANF where

open import Data.Bool.Base using
  (Bool; true; false; _∧_; _∨_; _xor_; if_then_else_)
open import Data.Bool.Properties using
  (xor-assoc; xor-comm; xor-identityʳ; xor-same; ∧-zeroʳ; ∧-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc; punchIn)
open import Data.Fin.Subset using (Subset; ⊥; inside; outside)
open import Data.Vec.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.Linear using (par; par-⊥)
open import PathSum.Reorder using (insertᵃ)

private
  variable
    k n : ℕ

  -- A bit in front of an assignment.

  extend : Bool → (Fin k → Bool) → Fin (suc k) → Bool
  extend b ρ zero    = b
  extend b ρ (suc i) = ρ i


------------------------------------------------------------------------
-- The normal forms

-- p ⊕ x₀ q, the first variable at the root.

data RM : ℕ → Set where
  𝟘    : RM k
  𝟙    : RM 0
  node : RM k → RM k → RM (suc k)

evalᴿ : RM k → (Fin k → Bool) → Bool
evalᴿ 𝟘          ρ = false
evalᴿ 𝟙          ρ = true
evalᴿ (node p q) ρ =
  evalᴿ p (λ i → ρ (suc i)) xor (ρ zero ∧ evalᴿ q (λ i → ρ (suc i)))

-- The value reads the point only through its values.

evalᴿ-cong : (p : RM k) {ρ ρ′ : Fin k → Bool} → (∀ i → ρ i ≡ ρ′ i) →
             evalᴿ p ρ ≡ evalᴿ p ρ′
evalᴿ-cong 𝟘          h = refl
evalᴿ-cong 𝟙          h = refl
evalᴿ-cong (node p q) h = cong₂ _xor_ (evalᴿ-cong p (λ i → h (suc i)))
  (cong₂ _∧_ (h zero) (evalᴿ-cong q (λ i → h (suc i))))

-- The smart constructor: node 𝟘 𝟘 is 𝟘.

node′ : RM k → RM k → RM (suc k)
node′ 𝟘          𝟘          = 𝟘
node′ 𝟘          𝟙          = node 𝟘 𝟙
node′ 𝟘          (node a b) = node 𝟘 (node a b)
node′ 𝟙          q          = node 𝟙 q
node′ (node a b) q          = node (node a b) q

eval-node′ : (p q : RM k) (ρ : Fin (suc k) → Bool) →
             evalᴿ (node′ p q) ρ ≡ evalᴿ (node p q) ρ
eval-node′ 𝟘          𝟘          ρ = sym (∧-zeroʳ (ρ zero))
eval-node′ 𝟘          𝟙          ρ = refl
eval-node′ 𝟘          (node a b) ρ = refl
eval-node′ 𝟙          q          ρ = refl
eval-node′ (node a b) q          ρ = refl


------------------------------------------------------------------------
-- Sum and product

infixl 6 _⊕ᴿ_
infixl 7 _∧ᴿ_

_⊕ᴿ_ : RM k → RM k → RM k
𝟘        ⊕ᴿ q        = q
𝟙        ⊕ᴿ 𝟘        = 𝟙
𝟙        ⊕ᴿ 𝟙        = 𝟘
node a b ⊕ᴿ 𝟘        = node a b
node a b ⊕ᴿ node c d = node′ (a ⊕ᴿ c) (b ⊕ᴿ d)

-- (a ⊕ x₀b)(c ⊕ x₀d) = ac ⊕ x₀(ad ⊕ bc ⊕ bd), as x₀x₀ = x₀.

_∧ᴿ_ : RM k → RM k → RM k
𝟘        ∧ᴿ q        = 𝟘
𝟙        ∧ᴿ q        = q
node a b ∧ᴿ 𝟘        = 𝟘
node a b ∧ᴿ node c d =
  node′ (a ∧ᴿ c) (((a ∧ᴿ d) ⊕ᴿ (b ∧ᴿ c)) ⊕ᴿ (b ∧ᴿ d))

private
  -- Four bits added in two orders.

  medial : ∀ a b c d → (a xor b) xor (c xor d) ≡ (a xor c) xor (b xor d)
  medial false false false false = refl
  medial false false false true  = refl
  medial false false true  false = refl
  medial false false true  true  = refl
  medial false true  false false = refl
  medial false true  false true  = refl
  medial false true  true  false = refl
  medial false true  true  true  = refl
  medial true  false false false = refl
  medial true  false false true  = refl
  medial true  false true  false = refl
  medial true  false true  true  = refl
  medial true  true  false false = refl
  medial true  true  false true  = refl
  medial true  true  true  false = refl
  medial true  true  true  true  = refl

  -- The product of two expansions, with x₀ at 1.

  expand : ∀ a b c d → (a xor b) ∧ (c xor d) ≡
                       (a ∧ c) xor (((a ∧ d) xor (b ∧ c)) xor (b ∧ d))
  expand false false false false = refl
  expand false false false true  = refl
  expand false false true  false = refl
  expand false false true  true  = refl
  expand false true  false false = refl
  expand false true  false true  = refl
  expand false true  true  false = refl
  expand false true  true  true  = refl
  expand true  false false false = refl
  expand true  false false true  = refl
  expand true  false true  false = refl
  expand true  false true  true  = refl
  expand true  true  false false = refl
  expand true  true  false true  = refl
  expand true  true  true  false = refl
  expand true  true  true  true  = refl

  -- Either value of x₀.

  product : ∀ r a b c d →
            (a xor (r ∧ b)) ∧ (c xor (r ∧ d)) ≡
            (a ∧ c) xor (r ∧ (((a ∧ d) xor (b ∧ c)) xor (b ∧ d)))
  product true  a b c d = expand a b c d
  product false a b c d = trans
    (cong₂ _∧_ (xor-identityʳ a) (xor-identityʳ c))
    (sym (xor-identityʳ (a ∧ c)))

eval-⊕ᴿ : (p q : RM k) (ρ : Fin k → Bool) →
          evalᴿ (p ⊕ᴿ q) ρ ≡ evalᴿ p ρ xor evalᴿ q ρ
eval-⊕ᴿ 𝟘          q          ρ = refl
eval-⊕ᴿ 𝟙          𝟘          ρ = refl
eval-⊕ᴿ 𝟙          𝟙          ρ = refl
eval-⊕ᴿ (node a b) 𝟘          ρ = sym (xor-identityʳ _)
eval-⊕ᴿ (node a b) (node c d) ρ = trans
  (eval-node′ (a ⊕ᴿ c) (b ⊕ᴿ d) ρ)
  (trans (cong₂ _xor_ (eval-⊕ᴿ a c ρ′)
           (trans (cong (ρ zero ∧_) (eval-⊕ᴿ b d ρ′))
                  (∧-distribˡ-xor′ (ρ zero) (evalᴿ b ρ′) (evalᴿ d ρ′))))
         (medial (evalᴿ a ρ′) (evalᴿ c ρ′)
                 (ρ zero ∧ evalᴿ b ρ′) (ρ zero ∧ evalᴿ d ρ′)))
  where
  ρ′ : Fin _ → Bool
  ρ′ i = ρ (suc i)

  ∧-distribˡ-xor′ : ∀ r u v → r ∧ (u xor v) ≡ (r ∧ u) xor (r ∧ v)
  ∧-distribˡ-xor′ true  u v = refl
  ∧-distribˡ-xor′ false u v = refl

eval-∧ᴿ : (p q : RM k) (ρ : Fin k → Bool) →
          evalᴿ (p ∧ᴿ q) ρ ≡ evalᴿ p ρ ∧ evalᴿ q ρ
eval-∧ᴿ 𝟘          q          ρ = refl
eval-∧ᴿ 𝟙          q          ρ = refl
eval-∧ᴿ (node a b) 𝟘          ρ = sym (∧-zeroʳ _)
eval-∧ᴿ (node a b) (node c d) ρ = trans
  (eval-node′ (a ∧ᴿ c) (((a ∧ᴿ d) ⊕ᴿ (b ∧ᴿ c)) ⊕ᴿ (b ∧ᴿ d)) ρ)
  (trans (cong₂ _xor_ (eval-∧ᴿ a c ρ′)
           (cong (ρ zero ∧_)
             (trans (eval-⊕ᴿ ((a ∧ᴿ d) ⊕ᴿ (b ∧ᴿ c)) (b ∧ᴿ d) ρ′)
               (cong₂ _xor_
                 (trans (eval-⊕ᴿ (a ∧ᴿ d) (b ∧ᴿ c) ρ′)
                        (cong₂ _xor_ (eval-∧ᴿ a d ρ′) (eval-∧ᴿ b c ρ′)))
                 (eval-∧ᴿ b d ρ′)))))
         (sym (product (ρ zero) (evalᴿ a ρ′) (evalᴿ b ρ′)
                       (evalᴿ c ρ′) (evalᴿ d ρ′))))
  where
  ρ′ : Fin _ → Bool
  ρ′ i = ρ (suc i)


------------------------------------------------------------------------
-- Constants and variables

one : ∀ k → RM k
one zero    = 𝟙
one (suc k) = node (one k) 𝟘

eval-one : ∀ k (ρ : Fin k → Bool) → evalᴿ (one k) ρ ≡ true
eval-one zero    ρ = refl
eval-one (suc k) ρ = trans
  (cong₂ _xor_ (eval-one k (λ i → ρ (suc i))) (∧-zeroʳ (ρ zero))) refl

lit : Bool → RM k
lit false = 𝟘
lit true  = one _

eval-lit : ∀ b (ρ : Fin k → Bool) → evalᴿ (lit b) ρ ≡ b
eval-lit false ρ = refl
eval-lit true  ρ = eval-one _ ρ

var : Fin k → RM k
var {suc k} zero    = node 𝟘 (one k)
var {suc k} (suc i) = node (var i) 𝟘

eval-var : (i : Fin k) (ρ : Fin k → Bool) → evalᴿ (var i) ρ ≡ ρ i
eval-var {suc k} zero    ρ = trans
  (cong (ρ zero ∧_) (eval-one k (λ i → ρ (suc i)))) (∧-identityʳ (ρ zero))
eval-var {suc k} (suc i) ρ = trans
  (cong₂ _xor_ (eval-var i (λ l → ρ (suc l))) (∧-zeroʳ (ρ zero)))
  (xor-identityʳ (ρ (suc i)))


------------------------------------------------------------------------
-- Setting a variable, adding one, substituting for one

-- p with the variable at j set to b: the value at y is that of p at y
-- with b inserted at j.

restrict : Fin (suc k) → Bool → RM (suc k) → RM k
restrict         j       b     𝟘          = 𝟘
restrict         zero    false (node p q) = p
restrict         zero    true  (node p q) = p ⊕ᴿ q
restrict {zero}  (suc ()) b    (node p q)
restrict {suc k} (suc j) b     (node p q) =
  node′ (restrict j b p) (restrict j b q)

eval-restrict : (j : Fin (suc k)) (b : Bool) (p : RM (suc k))
                (ρ : Fin k → Bool) →
                evalᴿ (restrict j b p) ρ ≡ evalᴿ p (insertᵃ j b ρ)
eval-restrict         j       b     𝟘          ρ = refl
eval-restrict         zero    false (node p q) ρ = sym (xor-identityʳ _)
eval-restrict         zero    true  (node p q) ρ = eval-⊕ᴿ p q ρ
eval-restrict {zero}  (suc ()) b    (node p q) ρ
eval-restrict {suc k} (suc j) b     (node p q) ρ = trans
  (eval-node′ (restrict j b p) (restrict j b q) ρ)
  (cong₂ _xor_ (eval-restrict j b p (λ i → ρ (suc i)))
               (cong (ρ zero ∧_) (eval-restrict j b q (λ i → ρ (suc i)))))

-- p with an unused variable inserted at i: read through punchIn i.

weaken : Fin (suc k) → RM k → RM (suc k)
weaken         zero    r          = node′ r 𝟘
weaken {zero}  (suc ()) r
weaken {suc k} (suc i) 𝟘          = 𝟘
weaken {suc k} (suc i) (node p q) = node′ (weaken i p) (weaken i q)

eval-weaken : (i : Fin (suc k)) (r : RM k) (ρ : Fin (suc k) → Bool) →
              evalᴿ (weaken i r) ρ ≡ evalᴿ r (λ v → ρ (punchIn i v))
eval-weaken         zero    r          ρ = trans (eval-node′ r 𝟘 ρ)
  (trans (cong (evalᴿ r (λ v → ρ (suc v)) xor_) (∧-zeroʳ (ρ zero)))
         (xor-identityʳ _))
eval-weaken {zero}  (suc ()) r ρ
eval-weaken {suc k} (suc i) 𝟘          ρ = refl
eval-weaken {suc k} (suc i) (node p q) ρ = trans
  (eval-node′ (weaken i p) (weaken i q) ρ)
  (cong₂ _xor_ (eval-weaken i p (λ v → ρ (suc v)))
               (cong (ρ zero ∧_) (eval-weaken i q (λ v → ρ (suc v)))))

-- The derivative in the variable at j: p with it set, plus p with it
-- clear.

derivᴿ : Fin (suc k) → RM (suc k) → RM k
derivᴿ j p = restrict j true p ⊕ᴿ restrict j false p

eval-derivᴿ : (j : Fin (suc k)) (p : RM (suc k)) (ρ : Fin k → Bool) →
              evalᴿ (derivᴿ j p) ρ ≡
              evalᴿ p (insertᵃ j true ρ) xor evalᴿ p (insertᵃ j false ρ)
eval-derivᴿ j p ρ = trans (eval-⊕ᴿ (restrict j true p) (restrict j false p) ρ)
  (cong₂ _xor_ (eval-restrict j true p ρ) (eval-restrict j false p ρ))

-- r substituted for the variable at i: p = p₀ ⊕ x_i ∂p, so it is
-- p₀ ⊕ r ∂p.

substitute : Fin (suc k) → RM k → RM (suc k) → RM k
substitute i r p = restrict i false p ⊕ᴿ (r ∧ᴿ derivᴿ i p)

private
  pick : ∀ c a t → a xor (c ∧ (t xor a)) ≡ (if c then t else a)
  pick false a t = xor-identityʳ a
  pick true  a t = trans (cong (a xor_) (xor-comm t a))
    (trans (sym (xor-assoc a a t)) (cong (_xor t) (xor-same a)))

  insert-if : (i : Fin (suc k)) (p : RM (suc k)) (ρ : Fin k → Bool) →
              ∀ c → (if c then evalᴿ p (insertᵃ i true ρ)
                          else evalᴿ p (insertᵃ i false ρ)) ≡
                    evalᴿ p (insertᵃ i c ρ)
  insert-if i p ρ true  = refl
  insert-if i p ρ false = refl

eval-substitute : (i : Fin (suc k)) (r : RM k) (p : RM (suc k))
                  (ρ : Fin k → Bool) →
                  evalᴿ (substitute i r p) ρ ≡
                  evalᴿ p (insertᵃ i (evalᴿ r ρ) ρ)
eval-substitute i r p ρ = trans
  (eval-⊕ᴿ (restrict i false p) (r ∧ᴿ derivᴿ i p) ρ)
  (trans (cong₂ _xor_ (eval-restrict i false p ρ)
           (trans (eval-∧ᴿ r (derivᴿ i p) ρ)
                  (cong (evalᴿ r ρ ∧_) (eval-derivᴿ i p ρ))))
    (trans (pick (evalᴿ r ρ) (evalᴿ p (insertᵃ i false ρ))
                 (evalᴿ p (insertᵃ i true ρ)))
           (insert-if i p ρ (evalᴿ r ρ))))


------------------------------------------------------------------------
-- Checking identities

-- Equality of normal forms, as a Boolean.

eqᴿ : RM k → RM k → Bool
eqᴿ 𝟘          𝟘          = true
eqᴿ 𝟘          𝟙          = false
eqᴿ 𝟘          (node c d) = false
eqᴿ 𝟙          𝟘          = false
eqᴿ 𝟙          𝟙          = true
eqᴿ (node a b) 𝟘          = false
eqᴿ (node a b) (node c d) = eqᴿ a c ∧ eqᴿ b d

private
  ∧-true : ∀ {a b} → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
  ∧-true {true} {true} _ = refl , refl

eqᴿ-sound : (p q : RM k) → eqᴿ p q ≡ true → p ≡ q
eqᴿ-sound 𝟘          𝟘          _ = refl
eqᴿ-sound 𝟙          𝟙          _ = refl
eqᴿ-sound (node a b) (node c d) e =
  cong₂ node (eqᴿ-sound a c (proj₁ (∧-true e)))
             (eqᴿ-sound b d (proj₂ (∧-true e)))
eqᴿ-sound 𝟘          𝟙          ()
eqᴿ-sound 𝟘          (node c d) ()
eqᴿ-sound 𝟙          𝟘          ()
eqᴿ-sound (node a b) 𝟘          ()

-- A conjunction over Fin n, and its meaning.

allFin : (Fin n → Bool) → Bool
allFin {zero}  f = true
allFin {suc n} f = f zero ∧ allFin (λ i → f (suc i))

allFin-sound : (f : Fin n → Bool) → allFin f ≡ true → ∀ i → f i ≡ true
allFin-sound {suc n} f e zero    = proj₁ (∧-true {f zero} e)
allFin-sound {suc n} f e (suc i) =
  allFin-sound (λ l → f (suc l)) (proj₂ (∧-true {f zero} e)) i

-- A disjunction over Fin n, and a witness for it.

anyFin : (Fin n → Bool) → Bool
anyFin {zero}  f = false
anyFin {suc n} f = f zero ∨ anyFin (λ i → f (suc i))

anyFin-sound : (f : Fin n → Bool) → anyFin f ≡ true →
               Σ (Fin n) (λ i → f i ≡ true)
anyFin-sound {suc n} f e = go (f zero) refl e
  where
  go : ∀ b → f zero ≡ b → b ∨ anyFin (λ i → f (suc i)) ≡ true →
       Σ (Fin (suc n)) (λ i → f i ≡ true)
  go true  z _ = zero , z
  go false z r with anyFin-sound (λ i → f (suc i)) r
  ... | i , fi = suc i , fi

-- A point where a polynomial is 1, if the search finds one: 1 needs
-- no variables, and p ⊕ x₀q is 1 at x₀ = 0 where p is, and at x₀ = 1
-- where p ⊕ q is.

private
  choose : Maybe (Fin k → Bool) → Maybe (Fin k → Bool) →
           Maybe (Fin (suc k) → Bool)
  choose (just ρ) _        = just (extend false ρ)
  choose nothing  (just ρ) = just (extend true ρ)
  choose nothing  nothing  = nothing

witness : RM k → Maybe (Fin k → Bool)
witness 𝟘          = nothing
witness 𝟙          = just (λ ())
witness (node p q) = choose (witness p) (witness (p ⊕ᴿ q))

witness-sound : (p : RM k) {ρ : Fin k → Bool} → witness p ≡ just ρ →
                evalᴿ p ρ ≡ true
witness-sound 𝟙 refl = refl
witness-sound (node p q) e =
  go (witness p) refl (witness (p ⊕ᴿ q)) refl e
  where
  go : ∀ a → witness p ≡ a → ∀ b → witness (p ⊕ᴿ q) ≡ b →
       ∀ {σ} → choose a b ≡ just σ → evalᴿ (node p q) σ ≡ true
  go (just σ) wa b wb refl =
    trans (xor-identityʳ (evalᴿ p σ)) (witness-sound p wa)
  go nothing  wa (just σ) wb refl =
    trans (sym (eval-⊕ᴿ p q σ)) (witness-sound (p ⊕ᴿ q) wb)
  go nothing  wa nothing  wb ()
witness-sound 𝟘 ()

-- So a found point.

Found : Maybe (Fin k → Bool) → Bool
Found (just _) = true
Found nothing  = false

found : (p : RM k) → Found (witness p) ≡ true →
        Σ (Fin k → Bool) (λ ρ → evalᴿ p ρ ≡ true)
found {k} p e = go (witness p) refl e
  where
  go : ∀ a → witness p ≡ a → Found a ≡ true →
       Σ (Fin k → Bool) (λ ρ → evalᴿ p ρ ≡ true)
  go (just ρ) w _  = ρ , witness-sound p w
  go nothing  w ()


------------------------------------------------------------------------
-- Affine normal forms

-- A normal form of degree at most 1 is c ⊕ ⨁_{i ∈ β} x_i; linᴿ reads c
-- and β off it, and finds nothing for a normal form of higher degree:
-- p ⊕ x₀q is affine when p is and q is a constant.

private
  lin-node′ : Bool → Bool → Bool × Subset k →
              Maybe (Bool × Subset (suc k))
  lin-node′ true  _     (c , β) = just (c , outside ∷ β)
  lin-node′ false true  (c , β) = just (c , inside ∷ β)
  lin-node′ false false _       = nothing

  lin-node : Maybe (Bool × Subset k) → RM k →
             Maybe (Bool × Subset (suc k))
  lin-node nothing   q = nothing
  lin-node (just cβ) q = lin-node′ (eqᴿ q 𝟘) (eqᴿ q (one _)) cβ

linᴿ : RM k → Maybe (Bool × Subset k)
linᴿ 𝟘          = just (false , ⊥)
linᴿ 𝟙          = just (true , [])
linᴿ (node p q) = lin-node (linᴿ p) q

private
  -- (c ⊕ P) ⊕ r = c ⊕ (r ⊕ P).

  rearrange : ∀ c P r → (c xor P) xor r ≡ c xor (r xor P)
  rearrange c P r = trans (xor-assoc c P r) (cong (c xor_) (xor-comm P r))

linᴿ-sound : (p : RM k) {c : Bool} {β : Subset k} →
             linᴿ p ≡ just (c , β) → ∀ ρ → evalᴿ p ρ ≡ c xor par β ρ
linᴿ-sound 𝟘 refl ρ = sym (par-⊥ ρ)
linᴿ-sound 𝟙 refl ρ = refl
linᴿ-sound {suc k} (node p q) e ρ = go (linᴿ p) refl e
  where
  ρ′ : Fin k → Bool
  ρ′ i = ρ (suc i)

  go′ : ∀ (c′ : Bool) (β′ : Subset k) → evalᴿ p ρ′ ≡ c′ xor par β′ ρ′ →
        ∀ z o → eqᴿ q 𝟘 ≡ z → eqᴿ q (one k) ≡ o → ∀ {c β} →
        lin-node′ z o (c′ , β′) ≡ just (c , β) →
        evalᴿ (node p q) ρ ≡ c xor par β ρ
  go′ c′ β′ hp true  o ez eo refl = trans
    (cong₂ _xor_ hp (cong (ρ zero ∧_)
      (trans (cong (λ t → evalᴿ t ρ′) (eqᴿ-sound q 𝟘 ez)) refl)))
    (trans (cong ((c′ xor par β′ ρ′) xor_) (∧-zeroʳ (ρ zero)))
           (xor-identityʳ (c′ xor par β′ ρ′)))
  go′ c′ β′ hp false true  ez eo refl = trans
    (cong₂ _xor_ hp (cong (ρ zero ∧_)
      (trans (cong (λ t → evalᴿ t ρ′) (eqᴿ-sound q (one k) eo))
             (eval-one k ρ′))))
    (trans (cong ((c′ xor par β′ ρ′) xor_) (∧-identityʳ (ρ zero)))
           (rearrange c′ (par β′ ρ′) (ρ zero)))
  go′ c′ β′ hp false false ez eo ()

  go : ∀ a → linᴿ p ≡ a → ∀ {c β} → lin-node a q ≡ just (c , β) →
       evalᴿ (node p q) ρ ≡ c xor par β ρ
  go nothing          lp ()
  go (just (c′ , β′)) lp e′ =
    go′ c′ β′ (linᴿ-sound p lp ρ′) (eqᴿ q 𝟘) (eqᴿ q (one k)) refl refl e′
