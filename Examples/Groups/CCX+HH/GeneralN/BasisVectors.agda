------------------------------------------------------------------------
-- Presentations of groups
--
-- Basis vectors and their behavior under the two-block operators used
-- by the independent physical semantics.  This bridges bit routing to
-- vector semantics without restricting spectator or borrowed bits.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.BasisVectors where

open import Data.Bool.Base using (Bool ; false ; true)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec ; tabulate)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (Dec ; yes ; no)
open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (D ; isCommutativeRing-D ; adj-D ; ½ᴰ)
open import Instances using (0#)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
  using (δ ; δ-refl ; δ-≢ ; _!_ ; !-tabulate ; vec-ext ; col ; 𝕀 ; restrict ; restrict-!)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι ; injective)
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (parallel ; parallel-left ; parallel-right ; restrict-ext)

private variable m n : ℕ

basis : Fin n → Vec D n
basis i = tabulate λ j → δ j i

zeroV : ∀ n → Vec D n
zeroV n = tabulate λ _ → 0#

basis-! : ∀ (i j : Fin n) → basis i ! j ≡ δ j i
basis-! i j = !-tabulate (λ k → δ k i) j

zero-! : ∀ (i : Fin n) → zeroV n ! i ≡ 0#
zero-! i = !-tabulate (λ _ → 0#) i

basis-col : ∀ (i : Fin n) → basis i ≡ col 𝕀 i
basis-col i = sym (!-tabulate (λ j → tabulate (λ k → δ k j)) i)

private
  δ-embedding : ∀ (e : Emb m n) (i j : Fin m) → δ (ι e i) (ι e j) ≡ δ i j
  δ-embedding e i j = choose (i ≟ j)
    where
    choose : Dec (i ≡ j) → δ (ι e i) (ι e j) ≡ δ i j
    choose (yes refl) = trans (δ-refl (ι e i)) (sym (δ-refl i))
    choose (no ne) = trans (δ-≢ (injective e ne)) (sym (δ-≢ ne))

restrict-basis : ∀ (e : Emb m n) i → restrict e (basis (ι e i)) ≡ basis i
restrict-basis e i = vec-ext λ j → trans (restrict-! e (basis (ι e i)) j)
  (trans (basis-! (ι e i) (ι e j))
    (trans (δ-embedding e j i) (sym (basis-! i j))))

restrict-zero : ∀ (e : Emb m n) → restrict e (zeroV n) ≡ zeroV m
restrict-zero e = vec-ext λ i → trans (restrict-! e (zeroV _) i)
  (trans (zero-! (ι e i)) (sym (zero-! i)))

module _ (p : Partition m n) where

  left-other : ∀ i → restrict (left p) (basis (ι (right p) i)) ≡ zeroV m
  left-other i = vec-ext λ j → trans (restrict-! (left p) (basis (ι (right p) i)) j)
    (trans (basis-! (ι (right p) i) (ι (left p) j))
      (trans (δ-≢ (disjoint p j i)) (sym (zero-! j))))

  right-other : ∀ i → restrict (right p) (basis (ι (left p) i)) ≡ zeroV m
  right-other i = vec-ext λ j → trans (restrict-! (right p) (basis (ι (left p) i)) j)
    (trans (basis-! (ι (left p) i) (ι (right p) j))
      (trans (δ-≢ (λ eq → disjoint p i j (sym eq))) (sym (zero-! j))))

  parallel-zero : ∀ f g → f (zeroV m) ≡ zeroV m → g (zeroV m) ≡ zeroV m →
    parallel p f g (zeroV n) ≡ zeroV n
  parallel-zero f g f0 g0 = restrict-ext p
    (trans (parallel-left p f g (zeroV n))
      (trans (cong f (restrict-zero (left p)))
        (trans f0 (sym (restrict-zero (left p))))))
    (trans (parallel-right p f g (zeroV n))
      (trans (cong g (restrict-zero (right p)))
        (trans g0 (sym (restrict-zero (right p))))))

  parallel-basis-left : ∀ f g i j → g (zeroV m) ≡ zeroV m →
    f (basis i) ≡ basis j →
    parallel p f g (basis (ι (left p) i)) ≡ basis (ι (left p) j)
  parallel-basis-left f g i j g0 fi = restrict-ext p
    (trans (parallel-left p f g (basis (ι (left p) i)))
      (trans (cong f (restrict-basis (left p) i))
        (trans fi (sym (restrict-basis (left p) j)))))
    (trans (parallel-right p f g (basis (ι (left p) i)))
      (trans (cong g (right-other i)) (trans g0 (sym (right-other j)))))

  parallel-basis-right : ∀ f g i j → f (zeroV m) ≡ zeroV m →
    g (basis i) ≡ basis j →
    parallel p f g (basis (ι (right p) i)) ≡ basis (ι (right p) j)
  parallel-basis-right f g i j f0 gi = restrict-ext p
    (trans (parallel-left p f g (basis (ι (right p) i)))
      (trans (cong f (left-other i)) (trans f0 (sym (left-other j)))))
    (trans (parallel-right p f g (basis (ι (right p) i)))
      (trans (cong g (restrict-basis (right p) i))
        (trans gi (sym (restrict-basis (right p) j)))))

  parallel-basis : ∀ f b i j → f (zeroV m) ≡ zeroV m →
    f (basis i) ≡ basis j →
    parallel p f f (basis (ι (select p b) i)) ≡ basis (ι (select p b) j)
  parallel-basis f false i j f0 fi = parallel-basis-left f f i j f0 fi
  parallel-basis f true i j f0 fi = parallel-basis-right f f i j f0 fi
