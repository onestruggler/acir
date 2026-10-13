------------------------------------------------------------------------
-- Presentations of groups
--
-- Canonical actual circuit words at every width.  The finite small
-- cases and the Algorithm-1/Clément normalizer share one interface:
-- normalization is derivable, matrix equality is exactly equality of
-- normal words, and normalization is idempotent.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Normalization where

open import Data.Nat.Base using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε)
open import Examples.Groups.CCX+HH.Syntactics using (Circuit)
import Examples.Groups.CCX+HH.Semantics as C
import Examples.Groups.CCX+HH.Presentation as P
import Examples.Groups.CCX+HH.LowWidth as Low
import Examples.Groups.CCX+HH.OneQubit as One
import Examples.Groups.CCX+HH.TwoQubit.Normalization as Two
import Examples.Groups.CCX+HH.ThreeQubit.NormalForm as Three
import Examples.Groups.CCX+HH.GeneralN.Normalization as General

nf : ∀ {n} → Circuit n → Circuit n
nf {0} w = ε
nf {1} w = One.normal (One.denote w)
nf {2} = Two.nf
nf {3} w = Three.section (Three.nf w)
nf {suc (suc (suc (suc n)))} = General.nf n

correct : ∀ {n} (w : Circuit n) → C.interpret (nf w) ≡ C.interpret w
correct {0} w = Eq.sym (Low.Zero.semantics w)
correct {1} w = Eq.sym (Low.One.soundness (One.normalize w))
correct {2} = Two.correct
correct {3} w = Eq.sym (P.soundness (Three.normalize w))
correct {suc (suc (suc (suc n)))} = General.correct n

semantic-cong : ∀ {n} {u v : Circuit n} → C.interpret u ≡ C.interpret v → nf u ≡ nf v
semantic-cong {0} eq = Eq.refl
semantic-cong {1} eq = Eq.cong One.normal (One.soundness (Low.One.completeness eq))
semantic-cong {2} = Two.semantic-cong
semantic-cong {3} eq = Eq.cong Three.section (Three.nf-cong (P.completeness eq))
semantic-cong {suc (suc (suc (suc n)))} = General.semantic-cong n

normalize : ∀ {n} (w : Circuit n) → w P.≈ nf w
normalize w = P.completeness (Eq.sym (correct w))

cong : ∀ {n} {u v : Circuit n} → u P.≈ v → nf u ≡ nf v
cong eq = semantic-cong (P.soundness eq)

complete : ∀ {n} {u v : Circuit n} → nf u ≡ nf v → u P.≈ v
complete {u = u} {v} eq = P.completeness
  (Eq.trans (Eq.sym (correct u)) (Eq.trans (Eq.cong C.interpret eq) (correct v)))

idempotent : ∀ {n} (w : Circuit n) → nf (nf w) ≡ nf w
idempotent w = semantic-cong (correct w)
