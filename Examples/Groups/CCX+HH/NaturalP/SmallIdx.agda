------------------------------------------------------------------------
-- Presentations of groups
--
-- Small indices are states on the bottom four wires.
--
-- The index of a state reads wire 0 as its least significant bit
-- (GeneralN/BinaryBasis): the even and odd indices are the two halves
-- of the interleaved partition, `ι (left …) i = 2 i` and
-- `ι (right …) i = 2 i + 1` (`toℕ-left`, `toℕ-right`).  So an index
-- below 2ᵗ has no bit on wire t or above (`bits-high`), and an index
-- below 16 is a state in the span of the unit vectors of the bottom
-- four wires (`small-span`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.SmallIdx where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_ ; _∧_)
open import Data.Bool.Properties using (xor-identityʳ ; ∧-identityʳ ; ∧-zeroʳ)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; punchIn)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _*_ ; _^_ ; _<_ ; _≤_ ; z≤n ; s≤s)
import Data.Nat.Properties as NP
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; map)
open import Relation.Binary.PropositionalEquality
open import Notations using (₄₊)

open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (ι)
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating ; columns)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (bits ; cons)
open import Examples.Groups.CCX+HH.NaturalP.Span using (InSpan ; E4 ; comb)

------------------------------------------------------------------------
-- The interleaved partition

private
  left′ : ∀ {m n} (eq : m * 2 ≡ n) (i : Fin m) →
    toℕ (ι (left (subst (Partition m) eq (columns m))) i) ≡ 2 * toℕ i + 0
  left′ refl i = FP.toℕ-combine i zero

  right′ : ∀ {m n} (eq : m * 2 ≡ n) (i : Fin m) →
    toℕ (ι (right (subst (Partition m) eq (columns m))) i) ≡ 2 * toℕ i + 1
  right′ refl i = FP.toℕ-combine i (suc zero)

toℕ-left : ∀ m (i : Fin m) → toℕ (ι (left (alternating m)) i) ≡ 2 * toℕ i + 0
toℕ-left m = left′ (NP.*-comm m 2)

toℕ-right : ∀ m (i : Fin m) → toℕ (ι (right (alternating m)) i) ≡ 2 * toℕ i + 1
toℕ-right m = right′ (NP.*-comm m 2)

------------------------------------------------------------------------
-- High bits of small indices

private
  half : ∀ a b → 2 * a + 0 < 2 * b → a < b
  half a b lt = NP.*-cancelˡ-< 2 a b (subst (_< 2 * b) (NP.+-identityʳ (2 * a)) lt)

  half′ : ∀ a b → 2 * a + 1 < 2 * b → a < b
  half′ a b lt = NP.*-cancelˡ-< 2 a b
    (NP.<-trans (subst (_< 2 * a + 1) (NP.+-identityʳ (2 * a)) (NP.+-monoʳ-< (2 * a) (s≤s z≤n))) lt)

  -- An odd number is not below 1.
  odd≮1 : ∀ a → 2 * a + 1 < 1 → ⊥
  odd≮1 a lt = NP.<-irrefl refl (NP.≤-<-trans (subst (1 ≤_) (NP.+-comm 1 (2 * a)) (s≤s z≤n)) lt)

  -- From an even number below 1, half is below 1.
  even<1 : ∀ a → 2 * a + 0 < 1 → a < 1
  even<1 zero    lt = s≤s z≤n
  even<1 (suc a) (s≤s ())

bits-high : ∀ n t (x : Fin (2 ^ n)) → toℕ x < 2 ^ t → (j : Fin n) → t ≤ toℕ j → bits n x j ≡ false
bits-high (suc n) zero x lt j le
  with locate (alternating (2 ^ n)) x | cover (alternating (2 ^ n)) x
... | inj₁ y | eq = at j
  where
  y<1 : toℕ y < 1
  y<1 = even<1 (toℕ y) (subst (_< 1) (trans (cong toℕ (sym eq)) (toℕ-left (2 ^ n) y)) lt)
  at : (j : Fin (suc n)) → cons false (bits n y) j ≡ false
  at zero    = refl
  at (suc j) = bits-high n zero y y<1 j z≤n
... | inj₂ y | eq =
  ⊥-elim (odd≮1 (toℕ y) (subst (_< 1) (trans (cong toℕ (sym eq)) (toℕ-right (2 ^ n) y)) lt))
bits-high (suc n) (suc t) x lt j le
  with locate (alternating (2 ^ n)) x | cover (alternating (2 ^ n)) x
... | inj₁ y | eq = at j le
  where
  y< : toℕ y < 2 ^ t
  y< = half (toℕ y) (2 ^ t) (subst (_< 2 * 2 ^ t) (trans (cong toℕ (sym eq)) (toℕ-left (2 ^ n) y)) lt)
  at : (j : Fin (suc n)) → suc t ≤ toℕ j → cons false (bits n y) j ≡ false
  at (suc j) (s≤s le) = bits-high n t y y< j le
... | inj₂ y | eq = at j le
  where
  y< : toℕ y < 2 ^ t
  y< = half′ (toℕ y) (2 ^ t) (subst (_< 2 * 2 ^ t) (trans (cong toℕ (sym eq)) (toℕ-right (2 ^ n) y)) lt)
  at : (j : Fin (suc n)) → suc t ≤ toℕ j → cons true (bits n y) j ≡ false
  at (suc j) (s≤s le) = bits-high n t y y< j le

------------------------------------------------------------------------
-- Indices below 16

private
  q0 : ∀ a b c d → (a ∧ true) xor ((b ∧ false) xor ((c ∧ false) xor ((d ∧ false) xor false))) ≡ a
  q0 a b c d rewrite ∧-identityʳ a | ∧-zeroʳ b | ∧-zeroʳ c | ∧-zeroʳ d = xor-identityʳ a
  q1 : ∀ a b c d → (a ∧ false) xor ((b ∧ true) xor ((c ∧ false) xor ((d ∧ false) xor false))) ≡ b
  q1 a b c d rewrite ∧-zeroʳ a | ∧-identityʳ b | ∧-zeroʳ c | ∧-zeroʳ d = xor-identityʳ b
  q2 : ∀ a b c d → (a ∧ false) xor ((b ∧ false) xor ((c ∧ true) xor ((d ∧ false) xor false))) ≡ c
  q2 a b c d rewrite ∧-zeroʳ a | ∧-zeroʳ b | ∧-identityʳ c | ∧-zeroʳ d = xor-identityʳ c
  q3 : ∀ a b c d → (a ∧ false) xor ((b ∧ false) xor ((c ∧ false) xor ((d ∧ true) xor false))) ≡ d
  q3 a b c d rewrite ∧-zeroʳ a | ∧-zeroʳ b | ∧-zeroʳ c | ∧-identityʳ d = xor-identityʳ d
  qz : ∀ a b c d → (a ∧ false) xor ((b ∧ false) xor ((c ∧ false) xor ((d ∧ false) xor false))) ≡ false
  qz a b c d rewrite ∧-zeroʳ a | ∧-zeroʳ b | ∧-zeroʳ c | ∧-zeroʳ d = refl

small-span : ∀ M (x : Fin (2 ^ ₄₊ M)) → toℕ x < 16 → InSpan E4 (bits (₄₊ M) x)
small-span M x lt = cs , pt
  where
  s = bits (₄₊ M) x
  s0 = s zero
  s1 = s (suc zero)
  s2 = s (suc (suc zero))
  s3 = s (suc (suc (suc zero)))
  cs = s0 ∷ s1 ∷ s2 ∷ s3 ∷ []
  pt : comb E4 cs ≈s s
  pt zero                      = q0 s0 s1 s2 s3
  pt (suc zero)                = q1 s0 s1 s2 s3
  pt (suc (suc zero))          = q2 s0 s1 s2 s3
  pt (suc (suc (suc zero)))    = q3 s0 s1 s2 s3
  pt (suc (suc (suc (suc j)))) =
    trans (qz s0 s1 s2 s3) (sym (bits-high (₄₊ M) 4 x lt (suc (suc (suc (suc j)))) (s≤s (s≤s (s≤s (s≤s z≤n))))))
