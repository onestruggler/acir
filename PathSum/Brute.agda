------------------------------------------------------------------------
-- Presentations of groups
--
-- Equivalence of path-sums by brute force
--
-- Definition 2.3 compares two operators entry by entry, and there are
-- finitely many entries: 2^n inputs, 2^n outputs, and H integer
-- coordinates of each amplitude in Z[ζ].  So equivalence is decidable
-- by evaluating them all (≋?), and a closed instance is proved or
-- refuted by computing that decision (≋-by-eval, ≋-refute).
--
-- This is not the paper's method and has nothing to do with it.  The
-- cost is exponential in both the inputs and the path variables:
-- 4^n entries, each a sum over 2^m paths of polynomials evaluated over
-- all 2^(n+m) monomials.  Nothing here is polynomial-time.  The one
-- economy is that a normalisation both sides share is cancelled
-- before an entry is compared (scaled?), since √2^j multiplies the
-- cost of reading a coordinate by 2^j.  The decider serves two
-- purposes: an independent cross-check of facts proved by reduction,
-- and a check of claims of the paper that no formalised rule proves
-- yet.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Brute (M₀ : ℕ) where

open import Data.Bool.Base using (if_then_else_)
open import Data.Fin.Properties using (all?)
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using ([_,_]′)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong₂)
open import Relation.Nullary.Decidable using
  (Dec; yes; no; True; False; map′; toWitness; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base using (PathSum; phase)
open import PathSum.Cyclotomic M₀ using
  (Amp; _≐_; 0ᴬ; zpow; √2·-map; √2·-injective; scale; scale-map;
   Σᴮ-cong)
open import PathSum.Decide M₀ using (search)
open import PathSum.Denotation M₀ using
  (Assign; amp; _≋_; hits-≗³; amp-≗)
open import PathSum.Polynomial.Properties using (eval-cong)

private
  variable
    n k k′ m m′ : ℕ


------------------------------------------------------------------------
-- Searching all assignments

private
  -- Only the values of the input are read.  (PathSum.PartialIsometry
  -- has this too.)  The implicit assignments of hits-≗³ and eval-cong
  -- are not inferable through `hits`, so they are given.

  amp-≗ˣ : (ξ : PathSum n k m) {x x′ : Assign n} →
           (∀ i → x i ≡ x′ i) → ∀ z → amp ξ x z ≐ amp ξ x′ z
  amp-≗ˣ ξ {x} {x′} x≗x′ z = Σᴮ-cong (λ y i →
    cong₂ (λ b e → (if b then zpow e else 0ᴬ) i)
      (hits-≗³ ξ {x} {x′} {y} {y} {z} {z} x≗x′ (λ _ → refl) (λ _ → refl))
      (eval-cong (phase ξ) {x} {x′} {y} {y} x≗x′ (λ _ → refl)))

  -- A decidable property that reads assignments only through their
  -- values holds everywhere or fails somewhere (PathSum.Decide.search).
  -- The two outcomes are told apart by [_,_]′, not by `with`, since
  -- the property will mention amp.

  every? : {P : Assign n → Set} → (∀ x → Dec (P x)) →
           (∀ {x x′} → (∀ i → x i ≡ x′ i) → P x → P x′) →
           Dec (∀ x → P x)
  every? {P = P} P? resp =
    [ yes , (λ (x , ¬p) → no (λ h → ¬p (h x))) ]′ (search P P? resp)


------------------------------------------------------------------------
-- Every entry, every coordinate

-- Two amplitudes, coordinate by coordinate.

coords? : (a b : Amp) → Dec (a ≐ b)
coords? a b = all? (λ i → a i ≟ℤ b i)

-- √2^j′ a against √2^j b.  A common factor √2 is cancelled first
-- (√2· is injective), so each side is multiplied only by what the
-- other lacks.  That matters for the cost: a coordinate of √2^j a
-- reads 2^j coordinates of a, and nothing is memoised.

scaled? : ∀ j j′ (a b : Amp) → Dec (scale j′ a ≐ scale j b)
scaled? zero    j′       a b = coords? (scale j′ a) b
scaled? (suc j) zero     a b = coords? a (scale (suc j) b)
scaled? (suc j) (suc j′) a b =
  map′ √2·-map (√2·-injective (scale j′ a) (scale j b))
       (scaled? j j′ a b)

-- One entry of definition 2.3, cleared of denominators.

entry? : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) (x z : Assign n) →
         Dec (scale k′ (amp ξ x z) ≐ scale k (amp ζ x z))
entry? {k = k} {k′ = k′} ξ ζ x z = scaled? k k′ (amp ξ x z) (amp ζ x z)

≋? : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) → Dec (ξ ≋ ζ)
≋? {k = k} {k′ = k′} ξ ζ =
  every? (λ x → every? (λ z → entry? ξ ζ x z) (resp-z x)) resp-x
  where
  Entry : Assign _ → Assign _ → Set
  Entry x z = scale k′ (amp ξ x z) ≐ scale k (amp ζ x z)

  resp-z : ∀ x {z z′} → (∀ w → z w ≡ z′ w) → Entry x z → Entry x z′
  resp-z x z≗z′ e i =
    trans (sym (scale-map k′ (amp-≗ ξ x z≗z′) i))
          (trans (e i) (scale-map k (amp-≗ ζ x z≗z′) i))

  resp-x : ∀ {x x′} → (∀ i → x i ≡ x′ i) →
           (∀ z → Entry x z) → ∀ z → Entry x′ z
  resp-x x≗x′ h z i =
    trans (sym (scale-map k′ (amp-≗ˣ ξ x≗x′ z) i))
          (trans (h z i) (scale-map k (amp-≗ˣ ζ x≗x′ z) i))

-- A closed instance, proved or refuted by computing the decision.

≋-by-eval : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
            {True (≋? ξ ζ)} → ξ ≋ ζ
≋-by-eval ξ ζ {t} = toWitness {a? = ≋? ξ ζ} t

≋-refute : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
           {False (≋? ξ ζ)} → ¬ (ξ ≋ ζ)
≋-refute ξ ζ {f} = toWitnessFalse {a? = ≋? ξ ζ} f
