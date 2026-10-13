------------------------------------------------------------------------
-- Presentations of groups
--
-- Every three-cycle on computational basis levels is a fixed-width
-- X,CX,CCX,HH circuit, for every width at least four.  The affine
-- router only chooses the three levels; the localized commutator fixes
-- all others.  Correctness includes every ordinary matrix column.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH.GeneralN.ThreeCycle (n : ℕ) where

open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (suc ; _^_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl ; sym ; trans)
open import Relation.Nullary.Negation using (¬_)
open import Word.Base using (_•_)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (inverse ; inverse-correct ; inverse-correctʳ ; act-injective)
import Examples.Groups.CCX+HH.GeneralN.ThreeCycleBase as Base
import Examples.Groups.CCX+HH.GeneralN.AffineRouting as Affine
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (idx ; bits ; idx-cong ; idx-bits)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (physical-column ; ket ; ket-cong)
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A

module B = Base n
width = B.P.width

private
  point12 : ¬ (B.point₁ C.≈s B.point₂)
  point12 eq with eq (suc zero)
  ... | ()
  point13 : ¬ (B.point₁ C.≈s B.point₃)
  point13 eq with eq zero
  ... | ()
  point23 : ¬ (B.point₂ C.≈s B.point₃)
  point23 eq with eq zero
  ... | ()

  base-route = Affine.triple-route B.point₁ B.point₂ B.point₃ point12 point13 point23

  recover : ∀ (w : C.Circuit width) s t → C.act w s C.≈s t → C.act (inverse w) t C.≈s s
  recover w s t eq i = trans (C.act-cong (inverse w) (λ j → sym (eq j)) i) (inverse-correct w s i)

record Cycle (a b c : C.State width) : Set where
  field
    word : C.Circuit width
    first : C.act word a C.≈s b
    second : C.act word b C.≈s c
    third : C.act word c C.≈s a
    outside : ∀ s → ¬ (s C.≈s a) → ¬ (s C.≈s b) → ¬ (s C.≈s c) → C.act word s C.≈s s
open Cycle public

cycle : ∀ a b c → ¬ (a C.≈s b) → ¬ (a C.≈s c) → ¬ (b C.≈s c) → Cycle a b c
cycle a b c ab ac bc = record
  { word = route • B.word • inverse route
  ; first = λ i → trans (C.act-cong route
      (λ j → trans (C.act-cong B.word (recover route B.point₁ a ra) j) (B.first j)) i) (rb i)
  ; second = λ i → trans (C.act-cong route
      (λ j → trans (C.act-cong B.word (recover route B.point₂ b rb) j) (B.second j)) i) (rc i)
  ; third = λ i → trans (C.act-cong route
      (λ j → trans (C.act-cong B.word (recover route B.point₃ c rc) j) (B.third j)) i) (ra i)
  ; outside = fixed
  }
  where
  target = Affine.triple-route a b c ab ac bc
  route = inverse (Affine.TripleRoute.word target) • Affine.TripleRoute.word base-route

  ra : C.act route B.point₁ C.≈s a
  ra i = trans
    (C.act-cong (inverse (Affine.TripleRoute.word target)) (Affine.TripleRoute.first base-route) i)
    (recover (Affine.TripleRoute.word target) a _ (Affine.TripleRoute.first target) i)
  rb : C.act route B.point₂ C.≈s b
  rb i = trans
    (C.act-cong (inverse (Affine.TripleRoute.word target)) (Affine.TripleRoute.second base-route) i)
    (recover (Affine.TripleRoute.word target) b _ (Affine.TripleRoute.second target) i)
  rc : C.act route B.point₃ C.≈s c
  rc i = trans
    (C.act-cong (inverse (Affine.TripleRoute.word target)) (Affine.TripleRoute.third base-route) i)
    (recover (Affine.TripleRoute.word target) c _ (Affine.TripleRoute.third target) i)

  avoiding : ∀ s p q → ¬ (s C.≈s q) → C.act route p C.≈s q →
    ¬ (C.act (inverse route) s C.≈s p)
  avoiding s p q ne image eq = ne λ i → trans (sym (inverse-correctʳ route s i))
    (trans (C.act-cong route eq i) (image i))

  fixed : ∀ s → ¬ (s C.≈s a) → ¬ (s C.≈s b) → ¬ (s C.≈s c) →
    C.act (route • B.word • inverse route) s C.≈s s
  fixed s sa sb sc i = trans
    (C.act-cong route (B.outside (C.act (inverse route) s)
      (avoiding s B.point₁ a sa ra) (avoiding s B.point₂ b sb rb) (avoiding s B.point₃ c sc rc)) i)
    (inverse-correctʳ route s i)

bits-distinct : ∀ {a b : Fin (2 ^ width)} → a ≢ b → ¬ (bits width a C.≈s bits width b)
bits-distinct {a} {b} ne eq = ne (trans (sym (idx-bits width a))
  (trans (idx-cong width eq) (idx-bits width b)))

indexed : ∀ (a b c : Fin (2 ^ width)) → a ≢ b → a ≢ c → b ≢ c →
  Cycle (bits width a) (bits width b) (bits width c)
indexed a b c ab ac bc = cycle (bits width a) (bits width b) (bits width c)
  (bits-distinct ab) (bits-distinct ac) (bits-distinct bc)

module Indexed (a b c : Fin (2 ^ width)) (ab : a ≢ b) (ac : a ≢ c) (bc : b ≢ c) where
  witness = indexed a b c ab ac bc
  circuit = C.physical (Cycle.word witness)

  first-column : A.col (Q.interpret circuit) a ≡ ket width (bits width b)
  first-column = trans (physical-column (Cycle.word witness) a) (ket-cong width (Cycle.first witness))

  second-column : A.col (Q.interpret circuit) b ≡ ket width (bits width c)
  second-column = trans (physical-column (Cycle.word witness) b) (ket-cong width (Cycle.second witness))

  third-column : A.col (Q.interpret circuit) c ≡ ket width (bits width a)
  third-column = trans (physical-column (Cycle.word witness) c) (ket-cong width (Cycle.third witness))

  outside-column : ∀ i → i ≢ a → i ≢ b → i ≢ c →
    A.col (Q.interpret circuit) i ≡ ket width (bits width i)
  outside-column i ia ib ic = trans (physical-column (Cycle.word witness) i)
    (ket-cong width (Cycle.outside witness (bits width i)
      (bits-distinct ia) (bits-distinct ib) (bits-distinct ic)))
