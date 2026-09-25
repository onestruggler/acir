------------------------------------------------------------------------
-- Presentations of groups
--
-- The pivot column of a column-orthonormal matrix s with pivot p, as
-- the Main Lemma uses it: v = col s p = w / δᵏ with k the least
-- δ-exponent, the entries of w beyond p are 0, and Σₓ Aₓ = Pₖ
-- (Norm).  So w has an odd entry; if k = 0 it is a unit, the
-- only nonzero entry, and if k > 0 there is a second one.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring using (D ; Z ; module ZR ; ωᶻ ; _^ᶻ_ ; oddℕ ; oddᶻ ; _≟ᶻ_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (col ; ColOrth)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Pivot using (pivot ; level)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.PivotColumn {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p) where

open import Data.Bool.Base using (false ; _∧_)
open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
import Data.Integer.Properties as ℤP
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute ; does ; dec-true)


open import Word.Base using (Word)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (first-nothing ; count ; count-one ; count-three)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Norm using (NA ; Σℕ ; Unit ; lde0 ; evenodd ; P)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Column
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syllable using (syl)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Step using (pivot-zero> ; col-norm ; odd⇒≤)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.MainTools {n} using (syl-of ; level-of)

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
zero> x px = recompute (W ! x ≟ᶻ ZR.0#) (pivot-zero> o ps x px)

norm : + Σℕ (λ x → NA (W ! x)) ≡ P (lde v)
norm = recompute (+ Σℕ (λ x → NA (W ! x)) ℤP.≟ P (lde v)) (col-norm o p)

-- Odd entries lie at or below the pivot.
odd≤ : ∀ {x} → Odd (W ! x) → x ≤ p
odd≤ = odd⇒≤ {p = p} {W} zero>

------------------------------------------------------------------------
-- The odd entries

-- k = 0: a unit at the first odd entry m, and 0 elsewhere.
unit : lde v ≡ 0 →
       ∃ λ m → firstOdd W ≡ just m × ∃ λ t → t ℕ.< 8 × W ! m ≡ ωᶻ ^ᶻ t × (∀ y → y ≢ m → W ! y ≡ ZR.0#)
unit k0 = go (lde0 W (≡.trans norm (≡.cong P k0)))
  where
  go : (∃ λ m → Unit (W ! m) × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) →
       ∃ λ m → firstOdd W ≡ just m × ∃ λ t → t ℕ.< 8 × W ! m ≡ ωᶻ ^ᶻ t × (∀ y → y ≢ m → W ! y ≡ ZR.0#)
  go (m , (t , t<8 , um) , rest) = m , fo , t , t<8 , um , rest
    where
    fo : firstOdd W ≡ just m
    fo = firstOdd-char W (≡.subst Odd (≡.sym um) (unit-odd t t<8))
           (λ x x<m → ≡.cong oddᶻ (rest x (λ e → FinP.<-irrefl e x<m)))

-- There is an odd entry.
some-odd : ∃ λ x → Odd (W ! x)
some-odd = from (lde v) ≡.refl
  where
  from : ∀ k → lde v ≡ k → ∃ λ x → Odd (W ! x)
  from zero k0 = at (unit k0)
    where
    at : (∃ λ m → firstOdd W ≡ just m × ∃ λ t → t ℕ.< 8 × W ! m ≡ ωᶻ ^ᶻ t × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) →
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
    ⊥-elim (odd1 (≡.trans (≡.sym (≡.cong oddℕ cnt)) (evenodd K′ W (≡.trans norm (≡.cong P ks)))))
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

-- k > 0 and three odd entries j < ℓ < c, the first three: there is a
-- fourth, by "evenodd".
third : ∀ {K′ j ℓ c} → lde v ≡ suc K′ → firstOdd W ≡ just j → nextOdd j W ≡ just ℓ → ℓ < c → Odd (W ! c) →
        (∀ x → ℓ < x → x < c → Even (W ! x)) → ∃ λ d → nextOdd c W ≡ just d
third {K′} {j} {ℓ} {c} ks fo nx ℓc oc btw = go (nextOdd c W) ≡.refl
  where
  jℓ : j < ℓ
  jℓ = proj₁ (nextOdd-spec W nx)
  go : (r : Maybe (Fin n)) → nextOdd c W ≡ r → ∃ λ d → nextOdd c W ≡ just d
  go (just d) nx′ = d , nx′
  go nothing nx′ =
    ⊥-elim (odd3 (≡.trans (≡.sym (≡.cong oddℕ cnt)) (evenodd K′ W (≡.trans norm (≡.cong P ks)))))
    where
    odd3 : oddℕ 3 ≡ false → ⊥
    odd3 ()
    others : ∀ x → x ≢ j → x ≢ ℓ → x ≢ c → oddᶻ (W ! x) ≡ false
    others x x≢j x≢ℓ x≢c = at₁ (FinP.<-cmp x j)
      where
      at₃ : Tri (x < c) (x ≡ c) (c < x) → j < x → ℓ < x → oddᶻ (W ! x) ≡ false
      at₃ (tri< x<c _ _) _ ℓ<x = btw x ℓ<x x<c
      at₃ (tri≈ _ x≡c _) _ _ = ⊥-elim (x≢c x≡c)
      at₃ (tri> _ _ c<x) _ _ = ≡.trans (≡.sym (≡.cong (_∧ oddᶻ (W ! x)) (dec-true (c FinP.<? x) c<x)))
                                 (first-nothing (λ y → does (c FinP.<? y) ∧ oddᶻ (W ! y)) nx′ x)
      at₂ : Tri (x < ℓ) (x ≡ ℓ) (ℓ < x) → j < x → oddᶻ (W ! x) ≡ false
      at₂ (tri< x<ℓ _ _) j<x = proj₂ (proj₂ (nextOdd-spec W nx)) x j<x x<ℓ
      at₂ (tri≈ _ x≡ℓ _) _ = ⊥-elim (x≢ℓ x≡ℓ)
      at₂ (tri> _ _ ℓ<x) j<x = at₃ (FinP.<-cmp x c) j<x ℓ<x
      at₁ : Tri (x < j) (x ≡ j) (j < x) → oddᶻ (W ! x) ≡ false
      at₁ (tri< x<j _ _) = proj₂ (firstOdd-spec W fo) x x<j
      at₁ (tri≈ _ x≡j _) = ⊥-elim (x≢j x≡j)
      at₁ (tri> _ _ j<x) = at₂ (FinP.<-cmp x ℓ) j<x
    cnt : count (λ x → oddᶻ (W ! x)) ≡ 3
    cnt = count-three (λ x → oddᶻ (W ! x)) j ℓ c (FinP.<⇒≢ jℓ) (FinP.<⇒≢ (ℕP.<-trans jℓ ℓc)) (FinP.<⇒≢ ℓc)
            (proj₁ (firstOdd-spec W fo)) (proj₁ (proj₂ (nextOdd-spec W nx))) oc others
