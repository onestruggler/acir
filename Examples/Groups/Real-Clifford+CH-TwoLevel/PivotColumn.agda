------------------------------------------------------------------------
-- Presentations of groups
--
-- The pivot column of an orthogonal matrix s with pivot p, as the
-- edges at a level use it: v = col s p = w / √2ᵏ with k the least
-- denominator exponent, the entries of w beyond p are 0, Σₓ Aₓ = 2ᵏ
-- and Σₓ Bₓ = 0 (Norm).  So w has an odd entry; if k = 0 it is ±1,
-- the only nonzero entry; if k > 0 its residue class has another.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; oddᶻ ; rbit ; _≟ᶻ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (col ; ColOrth)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; level)

module Examples.Groups.Real-Clifford+CH-TwoLevel.PivotColumn {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p) where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
import Data.Integer.Properties as ℤP
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Nullary.Decidable using (recompute)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (tri-elim)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm using (NA ; NB ; Σℕ ; Σℤ ; lde0)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable using (syl)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step using (pivot-zero> ; col-norm ; col-normB ; odd⇒≤)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (syl-of ; level-of)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.EdgeTools {n} using (Unit1 ; unit-odd)

------------------------------------------------------------------------
-- The representation

v : Vec D n
v = col s p

W : Vec Z n
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

zero> : ∀ x → p < x → W ! x ≡ ZR.0#
zero> x px = recompute (W ! x ≟ᶻ ZR.0#) (pivot-zero> o ps x px)

norm : Σℕ (λ x → NA (W ! x)) ≡ 2 ℕ.^ lde v
norm = recompute (Σℕ (λ x → NA (W ! x)) ℕP.≟ 2 ℕ.^ lde v) (col-norm o p)

normB : Σℤ (λ x → NB (W ! x)) ≡ + 0
normB = recompute (Σℤ (λ x → NB (W ! x)) ℤP.≟ + 0) (col-normB o p)

-- Odd entries lie at or below the pivot.
odd≤ : ∀ {x} → Odd (W ! x) → x ≤ p
odd≤ = odd⇒≤ {p = p} {W} zero>

------------------------------------------------------------------------
-- k = 0: a unit ±1 at the first odd entry m, and 0 elsewhere

unit : lde v ≡ 0 →
       ∃ λ m → firstOdd W ≡ just m × Unit1 (W ! m) × (∀ y → y ≢ m → W ! y ≡ ZR.0#) × m ≤ p
unit k0 = go (lde0 W (≡.trans norm (≡.cong (2 ℕ.^_) k0)))
  where
  go : (∃ λ m → Unit1 (W ! m) × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) →
       ∃ λ m → firstOdd W ≡ just m × Unit1 (W ! m) × (∀ y → y ≢ m → W ! y ≡ ZR.0#) × m ≤ p
  go (m , um , rest) = m , fo , um , rest , odd≤ (unit-odd um)
    where
    fo : firstOdd W ≡ just m
    fo = firstOdd-char W (unit-odd um) (λ x x<m → ≡.cong oddᶻ (rest x (λ e → FinP.<-irrefl e x<m)))

------------------------------------------------------------------------
-- k > 0: the first odd entry and the next one in its class

some-odd : ∀ {K′} → lde v ≡ suc K′ → ∃ λ x → Odd (W ! x)
some-odd {K′} ks = minimal (≡.subst (λ k → Minimal k W) ks min)
  where
  minimal : Minimal (suc K′) W → ∃ λ x → Odd (W ! x)
  minimal (inj₁ ())
  minimal (inj₂ x) = x

first : ∀ {K′} → lde v ≡ suc K′ → ∃ λ j → firstOdd W ≡ just j
first ks = go (firstOdd W) ≡.refl
  where
  go : (r : Maybe (Fin n)) → firstOdd W ≡ r → ∃ λ j → firstOdd W ≡ just j
  go nothing fo = ⊥-elim (Odd⇒¬Even {W ! proj₁ (some-odd ks)} (proj₂ (some-odd ks)) (firstOdd-nothing W fo (proj₁ (some-odd ks))))
  go (just j) fo = j , fo
