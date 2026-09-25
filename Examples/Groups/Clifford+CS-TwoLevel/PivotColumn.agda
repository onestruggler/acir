------------------------------------------------------------------------
-- Presentations of groups
--
-- The pivot column of a column-orthonormal matrix s with pivot p, as
-- the Main Lemma uses it: v = col s p = w / γᵏ with k the least
-- denominator exponent, the entries of w beyond p are 0, and
-- Σₓ |wₓ|² = 2ᵏ.  So w has an odd entry; if k = 0 it is a unit, the
-- only nonzero entry, and if k > 0 there is a second one.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (D ; Z ; module ZR ; ⅈᶻ ; _^ᶻ_ ; oddℕ ; oddᶻ)
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics using (col ; ColOrth)
open import Examples.Groups.Clifford+CS-TwoLevel.Pivot using (pivot ; level)

module Examples.Groups.Clifford+CS-TwoLevel.PivotColumn {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p) where

open import Data.Bool.Base using (false ; _∧_)
open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute ; does ; dec-true)

open import Instances using (_≟_ ; DEℤ)
open import Quantum.Synthesis.Ring using (DecEqCplx)

open import Word.Base using (Word)
open import Examples.Groups.Clifford+CS-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (first-nothing ; count ; count-one)
open import Examples.Groups.Clifford+CS-TwoLevel.Norm using (Nℕ ; Σℕ ; Unit ; lde0 ; evenodd)
open import Examples.Groups.Clifford+CS-TwoLevel.Column
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.Clifford+CS-TwoLevel.Syllable using (syl)
open import Examples.Groups.Clifford+CS-TwoLevel.Step using (pivot-zero> ; col-norm ; odd⇒≤)
open import Examples.Groups.Clifford+CS-TwoLevel.MainTools {n} using (syl-of ; level-of)

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
-- The facts that come from column-orthonormality, recomputed

zero> : ∀ x → p < x → W ! x ≡ ZR.0#
zero> x px = recompute (W ! x ≟ ZR.0#) (pivot-zero> o ps x px)

norm : Σℕ (λ x → Nℕ (W ! x)) ≡ 2 ℕ.^ lde v
norm = recompute (Σℕ (λ x → Nℕ (W ! x)) ℕP.≟ 2 ℕ.^ lde v) (col-norm o p)

-- Odd entries lie at or below the pivot.
odd≤ : ∀ {x} → Odd (W ! x) → x ≤ p
odd≤ = odd⇒≤ {p = p} {W} zero>

------------------------------------------------------------------------
-- The odd entries

-- k = 0: a unit at the first odd entry m, and 0 elsewhere.
unit : lde v ≡ 0 →
       ∃ λ m → firstOdd W ≡ just m × ∃ λ t → t ℕ.< 4 × W ! m ≡ ⅈᶻ ^ᶻ t × (∀ y → y ≢ m → W ! y ≡ ZR.0#)
unit k0 = go (lde0 W (≡.trans norm (≡.cong (2 ℕ.^_) k0)))
  where
  go : (∃ λ m → Unit (W ! m) × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) →
       ∃ λ m → firstOdd W ≡ just m × ∃ λ t → t ℕ.< 4 × W ! m ≡ ⅈᶻ ^ᶻ t × (∀ y → y ≢ m → W ! y ≡ ZR.0#)
  go (m , (t , t<4 , um) , rest) = m , fo , t , t<4 , um , rest
    where
    fo : firstOdd W ≡ just m
    fo = firstOdd-char W (≡.subst Odd (≡.sym um) (unit-odd t t<4))
           (λ x x<m → ≡.cong oddᶻ (rest x (λ e → FinP.<-irrefl e x<m)))

-- There is an odd entry.
some-odd : ∃ λ x → Odd (W ! x)
some-odd = from (lde v) ≡.refl
  where
  from : ∀ k → lde v ≡ k → ∃ λ x → Odd (W ! x)
  from zero k0 = at (unit k0)
    where
    at : (∃ λ m → firstOdd W ≡ just m × ∃ λ t → t ℕ.< 4 × W ! m ≡ ⅈᶻ ^ᶻ t × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) →
         ∃ λ x → Odd (W ! x)
    at (m , fo , _) = m , proj₁ (firstOdd-spec W fo)
  from (suc k) ks = minimal (≡.subst (λ k → Minimal k W) ks min)
    where
    minimal : Minimal (suc k) W → ∃ λ x → Odd (W ! x)
    minimal (inj₁ ())
    minimal (inj₂ x) = x

-- The first odd entry.
first : ∃ λ j → firstOdd W ≡ just j
first = go (firstOdd W) ≡.refl
  where
  go : (r : Maybe (Fin n)) → firstOdd W ≡ r → ∃ λ j → firstOdd W ≡ just j
  go nothing fo = ⊥-elim (Odd⇒¬Even {W ! proj₁ some-odd} (proj₂ some-odd) (firstOdd-nothing W fo (proj₁ some-odd)))
  go (just j) fo = j , fo

-- k > 0: the second odd entry, by "evenodd".
second : ∀ {K′ j} → lde v ≡ suc K′ → firstOdd W ≡ just j → ∃ λ ℓ → nextOdd j W ≡ just ℓ
second {K′} {j} ks fo = go (nextOdd j W) ≡.refl
  where
  go : (r : Maybe (Fin n)) → nextOdd j W ≡ r → ∃ λ ℓ → nextOdd j W ≡ just ℓ
  go (just ℓ) nx = ℓ , nx
  go nothing nx =
    ⊥-elim (odd1 (≡.trans (≡.sym (≡.cong oddℕ cnt)) (evenodd K′ W (≡.trans norm (≡.cong (2 ℕ.^_) ks)))))
    where
    odd1 : oddℕ 1 ≡ false → ⊥
    odd1 ()
    others : ∀ x → x ≢ j → oddᶻ (W ! x) ≡ false
    others x x≢j = at (FinP.<-cmp x j)
      where
      at : Tri (x < j) (x ≡ j) (j < x) → oddᶻ (W ! x) ≡ false
      at (tri< x<j _ _) = proj₂ (firstOdd-spec W fo) x x<j
      at (tri≈ _ x≡j _) = ⊥-elim (x≢j x≡j)
      at (tri> _ _ j<x) = ≡.trans (≡.sym (≡.cong (_∧ oddᶻ (W ! x)) (dec-true (j FinP.<? x) j<x)))
                            (first-nothing (λ y → does (j FinP.<? y) ∧ oddᶻ (W ! y)) nx x)
    cnt : count (λ x → oddᶻ (W ! x)) ≡ 1
    cnt = count-one (λ x → oddᶻ (W ! x)) j (proj₁ (firstOdd-spec W fo)) others
