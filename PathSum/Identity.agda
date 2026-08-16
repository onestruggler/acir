------------------------------------------------------------------------
-- Presentations of groups
--
-- When a fully reduced path-sum is the identity
--
-- Corollary 4.4 reduces a path-sum until no path variable is left,
-- and stops: `Reduces` says the sum has been exhausted, not that what
-- remains is the identity.  This module supplies the missing test.  A
-- path-sum with no path variables has a single path, so its
-- amplitude from x to z is either 0 -- when the outputs miss z -- or
-- the single power ζ^P(x) of the phase, and comparing that with the
-- identity's is comparing coordinates in Z[ζ].
--
-- The four results below are the four ways the comparison can go: the
-- outputs miss, the normalisation is not spent, the phase does not
-- vanish, and everything holds.  Together they decide the question,
-- the three refutations covering the complement of the criterion.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Identity (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (toℕ)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_; ∣m∣n⇒∣m-n)
open import Data.Integer.Properties using (+-comm; +-identityʳ; +-inverseˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _<_; s≤s; z≤n)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base
open import PathSum.Cyclotomic M₀
open import PathSum.Denotation M₀
open import PathSum.Order M
open import PathSum.Polynomial
open import PathSum.Polynomial.Properties using (eval-≈)

import Relation.Binary.PropositionalEquality as Eq

open +-*-Solver using (solve; con; _:+_; _:-_; _:=_)

private
  variable
    n k : ℕ


------------------------------------------------------------------------
-- Powers of ζ against normalisations

private
  -- Rotating commutes with multiplying by √2.

  rot-√2 : ∀ e a → rot e (√2· a) ≐ √2· (rot e a)
  rot-√2 e a i = trans (rot-+ᴬ e (rot (+ c) a) (rot (- (+ c)) a) i)
                       (cong₂ _+_ (swap (+ c)) (swap (- (+ c))))
    where
    swap : ∀ d → rot e (rot d a) i ≡ rot d (rot e a) i
    swap d = trans (rot-comp e d a i)
      (trans (rot-exp a (+-comm e d) i) (sym (rot-comp d e a i)))

  -- Rotating ζ^e by -e gives ζ^0.

  rot-back : ∀ e → rot (- e) (zpow e) ≐ zpow 0ℤ
  rot-back e i =
    trans (rot-zpow (- e) e i) (cong (λ z → zpow z i) (+-inverseˡ e))

  -- √2^j ζ^0 is never zero.

  scale-zpow0≢0 : ∀ j → ¬ (scale j (zpow 0ℤ) ≐ 0ᴬ)
  scale-zpow0≢0 zero    eq = zpow-0≢0ᴬ eq
  scale-zpow0≢0 (suc j) eq = scale-zpow0≢0 j
    (√2·-injective (scale j (zpow 0ℤ)) 0ᴬ
      (λ i → trans (eq i) (sym (√2·-0ᴬ i))))

  -- Nor is a power of ζ ever √2^j for j at least one.  Rotating it
  -- back to ζ^0 turns the claim into one about ζ^0 itself: at an odd
  -- normalisation ζ^0 would be √2 times something, whose square is
  -- twice something, and at an even one it would be twice something
  -- outright.  Both are refuted by a coordinate of ζ^0 being odd.

  zpow≢scale : ∀ (e : ℤ) j → ¬ (zpow e ≐ scale (suc j) (zpow 0ℤ))
  zpow≢scale e zero eq =
    2·≢scale-zpow0 (zpow (- e)) 1 (s≤s (s≤s z≤n)) two
    where
    rotated : zpow 0ℤ ≐ √2· (zpow (- e))
    rotated i = trans (sym (rot-back e i))
      (trans (rot-map (- e) eq i)
        (trans (rot-√2 (- e) (zpow 0ℤ) i)
          (√2·-map (λ i′ → trans (rot-zpow (- e) 0ℤ i′)
            (cong (λ z → zpow z i′) (+-identityʳ (- e)))) i)))

    two : ((+ 2) ·ᴬ zpow (- e)) ≐ scale 1 (zpow 0ℤ)
    two i = trans (sym (√2·-twice (zpow (- e)) i))
                  (√2·-map (λ i′ → sym (rotated i′)) i)
  zpow≢scale e (suc j) eq =
    2·≢scale-zpow0 (rot (- e) (scale j (zpow 0ℤ))) 0 (s≤s z≤n) two
    where
    two : ((+ 2) ·ᴬ rot (- e) (scale j (zpow 0ℤ))) ≐ scale 0 (zpow 0ℤ)
    two i = trans (sym (rot-·ᴬ (- e) (+ 2) (scale j (zpow 0ℤ)) i))
      (trans (sym (rot-map (- e)
        (λ i′ → trans (eq i′) (√2·-twice (scale j (zpow 0ℤ)) i′)) i))
        (rot-back e i))

  -- A coefficient of 1 means the exponent is a multiple of N.

  χ≡1 : ∀ z → χ z ≡ 1ℤ → (+ N) ∣ z
  χ≡1 z eq = aux ((+ N) ∣? z) ((+ N) ∣? (z - (+ H)))
    where
    aux : Dec ((+ N) ∣ z) → Dec ((+ N) ∣ (z - (+ H))) → (+ N) ∣ z
    aux (yes d) _       = d
    aux (no ¬d) (yes b) = contradiction (trans (sym (χ--1 ¬d b)) eq) λ ()
    aux (no ¬d) (no ¬b) = contradiction (trans (sym (χ-0 ¬d ¬b)) eq) λ ()


------------------------------------------------------------------------
-- The single path of a path-sum with no path variables

private
  if-true : {b : Bool} {a : Amp} → b ≡ true → (if b then a else 0ᴬ) ≐ a
  if-true refl _ = refl

  if-false : {b : Bool} {a : Amp} → b ≡ false → (if b then a else 0ᴬ) ≐ 0ᴬ
  if-false refl _ = refl

  if-cong : {b b′ : Bool} {a a′ : Amp} → b ≡ b′ → a ≐ a′ →
            (if b then a else 0ᴬ) ≐ (if b′ then a′ else 0ᴬ)
  if-cong {b = true}  {true}  _  h i = h i
  if-cong {b = false} {false} _  _ i = refl

  -- Missing the state kills the amplitude, hitting it leaves ζ^P.

  amp-miss : (ξ : PathSum n k 0) (x z : Assign n) →
             (∀ y → hits ξ x y z ≡ false) → amp ξ x z ≐ 0ᴬ
  amp-miss ξ x z miss = if-false (miss (λ ()))

  amp-hit : (ξ : PathSum n k 0) (x z : Assign n) (y : Assign 0) →
            hits ξ x y z ≡ true → amp ξ x z ≐ zpow (eval (phase ξ) x y)
  amp-hit ξ x z y hit = if-true hit


------------------------------------------------------------------------
-- The criterion

-- Outputs that are the inputs modulo 2 and a phase that vanishes
-- modulo 2^M, at no normalisation, make the identity.

id-if : (ξ : PathSum n 0 0) →
        (∀ w → out ξ w ≈[ + 2 ] μ x[ w ]) →
        phase ξ ≈[ pow M ] 0ᴾ →
        ξ ≋ idPS
id-if ξ eqf eqP x z =
  if-cong (hits-cong ξ idPS eqf x (λ ()) z)
          (zpow-cong {eval (phase ξ) x (λ ())} {eval (phase idPS) x (λ ())}
                     (eval-≈ (phase ξ) (phase idPS) eqP x (λ ())))


------------------------------------------------------------------------
-- The three refutations

-- The outputs miss the input they should return: the diagonal
-- amplitude is 0, and the identity's is √2^k ζ^0, which is not.

not-id-out : (ξ : PathSum n k 0) (x : Assign n) →
             (∀ y → hits ξ x y x ≡ false) → ¬ (ξ ≋ idPS)
not-id-out {k = k} ξ x miss ξ≋id = scale-zpow0≢0 k
  (λ i → trans (sym (scale-map k (amp-idPS x) i))
               (trans (sym (ξ≋id x x i)) (amp-miss ξ x x miss i)))

-- The normalisation is not spent: a power of ζ is not √2^(1+k).

not-id-norm : (ξ : PathSum n (suc k) 0) (x : Assign n) (y : Assign 0) →
              hits ξ x y x ≡ true → ¬ (ξ ≋ idPS)
not-id-norm {k = k} ξ x y hit ξ≋id =
  zpow≢scale (eval (phase ξ) x y) k
    (λ i → trans (sym (amp-hit ξ x x y hit i))
                 (trans (ξ≋id x x i) (scale-map (suc k) (amp-idPS x) i)))

-- The phase does not vanish at some input: ζ^P(x) is then not ζ^0,
-- their coefficients at the same coordinate being 1 and χ (P x).

not-id-phase : (ξ : PathSum n 0 0) (x : Assign n) (y : Assign 0) →
               hits ξ x y x ≡ true →
               ¬ (pow M ∣ eval (phase ξ) x y) → ¬ (ξ ≋ idPS)
not-id-phase ξ x y hit ¬d ξ≋id = ¬d
  (Eq.subst ((+ N) ∣_) (shape (eval (phase ξ) x y) index)
    (∣m∣n⇒∣m-n (χ≡1 _ at-P) (χ≡1 _ at-0)))
  where
  -- The coordinate ζ^0 is known at.

  index : ℤ
  index = + toℕ 0ᶠ

  same : zpow (eval (phase ξ) x y) ≐ zpow 0ℤ
  same i = trans (sym (amp-hit ξ x x y hit i))
                 (trans (ξ≋id x x i) (amp-idPS x i))

  at-P : χ (eval (phase ξ) x y - index) ≡ 1ℤ
  at-P = trans (same 0ᶠ) zpow0-at-0

  at-0 : χ (0ℤ - index) ≡ 1ℤ
  at-0 = zpow0-at-0

  shape : ∀ u v → (u - v) - (0ℤ - v) ≡ u
  shape = solve 2 (λ u v → (u :- v) :- (con 0ℤ :- v) := u) refl
