------------------------------------------------------------------------
-- Presentations of groups
--
-- A compact auxiliary rule set on the fourteen stabilizer letters:
-- seven phase squares, twenty-one phase commutations, the twenty-eight
-- S8 rules, and forty-nine permutation/phase conjugation rules.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.Compact.Syntactics where

open import Data.Fin.Base as F using (Fin ; zero ; suc ; inject₁ ; _<_)
import Data.Fin.Properties as FP
open import Relation.Nullary.Decidable using (yes ; no)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)
import Examples.Groups.Symmetric.Syntactics as Sym
open import Examples.Groups.CCX+HH.ThreeQubit.StabilizerGenerators using (Letter ; phase ; exchange)
open import Examples.Groups.CCX+HH.ThreeQubit.StabilizerNormalForm using (position)
import Presentation.Base as PB

P : Fin 7 → Word Letter
P i = [ phase i ]ʷ

X : Fin 7 → Word Letter
X i = [ exchange i ]ʷ

permutation : Sym.Circuit 8 → Word Letter
permutation = wmap (λ g → exchange (position g))

-- The action on the basis M0 Mj of the even diagonal sign subgroup.
conjugate : Fin 7 → Fin 7 → Word (Fin 7)
conjugate zero zero = [ zero ]ʷ
conjugate zero (suc j) = [ zero ]ʷ • [ suc j ]ʷ
conjugate (suc i) j with j FP.≟ inject₁ i | j FP.≟ suc i
... | yes _ | _ = [ suc i ]ʷ
... | no _ | yes _ = [ inject₁ i ]ʷ
... | no _ | no _ = [ j ]ʷ

infix 4 _===_
data _===_ : WRel Letter where
  phase-square : ∀ i → P i • P i === ε
  phase-commute : ∀ i j .(i<j : i < j) → P i • P j === P j • P i
  symmetric : ∀ {u v} → Sym._VRel,_===_ 8 u v → permutation u === permutation v
  cross : ∀ i j → X i • P j === (P ʷ) (conjugate i j) • X i

open PB _===_ public using (_≈_)
private module R = PB _===_

phase-commutation : ∀ i j → P i • P j ≈ P j • P i
phase-commutation i j with FP.<-cmp i j
... | tri< p _ _ = R.axiom (phase-commute i j p)
... | tri≈ _ refl _ = R.refl
... | tri> _ _ p = R.sym (R.axiom (phase-commute j i p))
