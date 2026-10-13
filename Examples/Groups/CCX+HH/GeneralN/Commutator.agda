------------------------------------------------------------------------
-- Presentations of groups
--
-- At every width at least four, the circuit image is precisely the
-- commutator subgroup of the dyadic orthogonal group.  Derived means
-- identity in the universal commutative quotient of Table 1.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; _^_)

module Examples.Groups.CCX+HH.GeneralN.Commutator (n : ℕ) where

open import Data.Nat.Base using (_≤_ ; s≤s ; z≤n)
import Data.Nat.Properties as NP
open import Data.Product.Base using (Σ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Word.Base using (Word)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH.GeneralN.Generation as Gen
import Examples.Groups.CCX+HH.Subgroup.AbelianizationCore as Abel
import Examples.Groups.CCX+HH.Subgroup.AbelianizationAt as Characterization
open import Examples.Groups.CCX+HH.Subgroup.Action using (c00)
open import Examples.Groups.CCX+HH.Subgroup.CircuitCharge using (image-closed)

width = 4 + n
N = 2 ^ width
open Abel N public using (Derived ; commutator ; commutator-member)

private
  enough : 2 ≤ N
  enough = NP.≤-trans (s≤s (s≤s z≤n))
    (NP.^-monoʳ-≤ 2 {4} {4 + n} (NP.m≤m+n 4 n))

circuit-derived : ∀ (c : H.Circuit width) → Derived (E.encode c)
circuit-derived c = Characterization.kernel N enough (image-closed c00 c)

synthesize : Word (T.Gen N) → H.Circuit width
synthesize = Gen.synthesize n

correct : ∀ w → Derived w → Q.interpret (synthesize w) ≡ S.⟦ w ⟧ᵐ
correct w member = Gen.correct n w (Characterization.kernel-only N member)

generated : ∀ w → Derived w →
  Σ (H.Circuit width) (λ c → Q.interpret c ≡ S.⟦ w ⟧ᵐ)
generated w member = Gen.generated n w (Characterization.kernel-only N member)

necessary : ∀ w (c : H.Circuit width) → Q.interpret c ≡ S.⟦ w ⟧ᵐ → Derived w
necessary w c eq = Characterization.kernel N enough (Gen.necessary n w c eq)
