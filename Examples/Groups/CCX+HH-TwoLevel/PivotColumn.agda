------------------------------------------------------------------------
-- Presentations of groups
--
-- The pivot column of an orthogonal matrix s with pivot p, as the
-- edges at a level use it: v = col s p = w / 2ᵏ with k the least
-- denominator exponent, the entries of w beyond p are 0, and
-- Σₓ wₓ² = 4ᵏ (Norm).  So if k = 0, w is ±e_m (Lemma 3.3), and if
-- k > 0, w has four odd entries a < b < c < d first (Step.Quad).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D ; oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (col ; ColOrth)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (pivot ; level)

module Examples.Groups.CCX+HH-TwoLevel.PivotColumn {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p) where

import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base using (Vec)
open import Relation.Nullary.Decidable using (recompute)

open import Examples.Groups.CCX+HH-TwoLevel.Lde
open import Examples.Groups.CCX+HH-TwoLevel.Norm using (sq ; Σℕ ; lde0)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.Syllable using (syl)
open import Examples.Groups.CCX+HH-TwoLevel.Step using (pivot-zero> ; col-norm ; odd⇒≤ ; Quad ; quad-exists)
open import Examples.Groups.CCX+HH-TwoLevel.States {n} using (syl-of ; level-of)

------------------------------------------------------------------------
-- The representation

v : Vec D n
v = col s p

W : Vec ℤ n
W = num v

v≡ : v ≡ scV (lde v) W
v≡ = lde-eq v

min : Minimal (lde v) W
min = lde-min v

syl≡ : syl s ≡ sylData p (lde v) W
syl≡ = syl-of s ps (lde v) W v≡ min

lvl : level s ≡ (suc (toℕ p) , lde v , nodd W)
lvl = level-of s ps (lde v) W v≡ min

------------------------------------------------------------------------
-- The facts that come from orthogonality, recomputed

zero> : ∀ x → p < x → W ! x ≡ + 0
zero> x px = recompute (W ! x ℤP.≟ + 0) (pivot-zero> o ps x px)

norm : Σℕ (λ x → sq (W ! x)) ≡ 4 ℕ.^ lde v
norm = recompute (Σℕ (λ x → sq (W ! x)) ℕP.≟ 4 ℕ.^ lde v) (col-norm o p)

-- Odd entries lie at or below the pivot.
odd≤ : ∀ {x} → Odd (W ! x) → x ≤ p
odd≤ = odd⇒≤ {p = p} {W} zero>

------------------------------------------------------------------------
-- k = 0: a unit ±1 at the first odd entry m, and 0 elsewhere

unit : lde v ≡ 0 →
       ∃ λ m → firstOdd W ≡ just m × Unit1 (W ! m) × (∀ y → y ≢ m → W ! y ≡ + 0) × m ≤ p
unit k0 = go (lde0 W (≡.trans norm (≡.cong (4 ℕ.^_) k0)))
  where
  go : (∃ λ m → Unit1 (W ! m) × (∀ y → y ≢ m → W ! y ≡ + 0)) →
       ∃ λ m → firstOdd W ≡ just m × Unit1 (W ! m) × (∀ y → y ≢ m → W ! y ≡ + 0) × m ≤ p
  go (m , um , rest) = m , fo , um , rest , odd≤ (unit-odd um)
    where
    fo : firstOdd W ≡ just m
    fo = firstOdd-char W (unit-odd um) (λ x x<m → ≡.cong oddℤ (rest x (λ e → FinP.<-irrefl e x<m)))

------------------------------------------------------------------------
-- k > 0: the first four odd entries

quad : ∀ {K′} → lde v ≡ suc K′ → Quad W
quad {K′} ks = quad-exists K′ W (≡.subst (λ k → Minimal k W) ks min) (≡.trans norm (≡.cong (4 ℕ.^_) ks))
