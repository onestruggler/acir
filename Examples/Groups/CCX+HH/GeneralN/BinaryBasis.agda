------------------------------------------------------------------------
-- Presentations of groups
--
-- Computational basis numbering with wire zero least significant.
-- Assignments are functions on Fin n, compared pointwise.  Inserting
-- a bottom bit uses alternating coordinates; inserting a top bit uses
-- contiguous coordinates.  No function-extensionality axiom is used.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.BinaryBasis where

open import Data.Bool.Base using (Bool ; false ; true)
open import Data.Fin.Base as F using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _^_)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (ι)
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary
open import Examples.Groups.CCX+HH.EncodingSemantics.Coordinates using (commute)
open import Examples.Groups.CCX+HH.GeneralN.Classical using (State ; _≈s_ ; lower)

private variable n : ℕ

cons : Bool → State n → State (suc n)
cons b s zero = b
cons b s (suc i) = s i

idx : ∀ n → State n → Fin (2 ^ n)
idx zero s = zero
idx (suc n) s = ι (select (alternating (2 ^ n)) (s zero)) (idx n (lower s))

idx-cong : ∀ n {s t} → s ≈s t → idx n s ≡ idx n t
idx-cong zero eq = refl
idx-cong (suc n) eq = cong₂
  (λ b i → ι (select (alternating (2 ^ n)) b) i)
  (eq zero) (idx-cong n (λ i → eq (suc i)))

bits : ∀ n → Fin (2 ^ n) → State n
bits zero i ()
bits (suc n) i = [ cons false ∘bits , cons true ∘bits ]′ (locate (alternating (2 ^ n)) i)
  where
  _∘bits : (State n → State (suc n)) → Fin (2 ^ n) → State (suc n)
  (f ∘bits) j = f (bits n j)

bits-select : ∀ n b j →
  bits (suc n) (ι (select (alternating (2 ^ n)) b) j) ≈s cons b (bits n j)
bits-select n false j i = cong
  (λ q → [ (λ k → cons false (bits n k)) , (λ k → cons true (bits n k)) ]′ q i)
  (locate-left (alternating (2 ^ n)) j)
bits-select n true j i = cong
  (λ q → [ (λ k → cons false (bits n k)) , (λ k → cons true (bits n k)) ]′ q i)
  (locate-right (alternating (2 ^ n)) j)

bits-idx : ∀ n s → bits n (idx n s) ≈s s
bits-idx zero s ()
bits-idx (suc n) s zero = bits-select n (s zero) (idx n (lower s)) zero
bits-idx (suc n) s (suc i) = trans
  (bits-select n (s zero) (idx n (lower s)) (suc i)) (bits-idx n (lower s) i)

idx-bits : ∀ n i → idx n (bits n i) ≡ i
idx-bits zero zero = refl
idx-bits (suc n) i = trans (step (locate (alternating (2 ^ n)) i))
  (cover (alternating (2 ^ n)) i)
  where
  step : ∀ q → idx (suc n)
    ([ (λ j → cons false (bits n j)) , (λ j → cons true (bits n j)) ]′ q)
    ≡ [ ι (left (alternating (2 ^ n))) , ι (right (alternating (2 ^ n))) ]′ q
  step (inj₁ j) = cong (ι (left (alternating (2 ^ n)))) (idx-bits n j)
  step (inj₂ j) = cong (ι (right (alternating (2 ^ n)))) (idx-bits n j)

idx-injective : ∀ n {s t} → idx n s ≡ idx n t → s ≈s t
idx-injective n {s} {t} eq i = trans (sym (bits-idx n s i))
  (trans (cong (λ j → bits n j i) eq) (bits-idx n t i))

append : ∀ n → State n → Bool → State (suc n)
append zero s b zero = b
append zero s b (suc ())
append (suc n) s b zero = s zero
append (suc n) s b (suc i) = append n (lower s) b i

prefix : ∀ n → State (suc n) → State n
prefix zero s ()
prefix (suc n) s zero = s zero
prefix (suc n) s (suc i) = prefix n (lower s) i

last : ∀ n → State (suc n) → Bool
last zero s = s zero
last (suc n) s = last n (lower s)

append-view : ∀ n s → append n (prefix n s) (last n s) ≈s s
append-view zero s zero = refl
append-view zero s (suc ())
append-view (suc n) s zero = refl
append-view (suc n) s (suc i) = append-view n (lower s) i

idx-append : ∀ n s b → idx (suc n) (append n s b) ≡
  ι (select (contiguous (2 ^ n)) b) (idx n s)
idx-append zero s false = refl
idx-append zero s true = refl
idx-append (suc n) s b = trans
  (cong (ι (select (alternating (2 ^ suc n)) (s zero))) (idx-append n (lower s) b))
  (sym (commute (2 ^ n) b (s zero) (idx n (lower s))))
