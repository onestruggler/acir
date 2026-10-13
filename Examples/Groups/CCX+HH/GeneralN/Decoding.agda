------------------------------------------------------------------------
-- Presentations of groups
--
-- An actual circuit decoder for every dyadic auxiliary edge at every
-- width at least four.  Its signs, exchanges and mixed atoms are built
-- from X, CX, CCX and HH without initialized ancillas.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; _^_)

module Examples.Groups.CCX+HH.GeneralN.Decoding (n : ℕ) where

open import Data.Nat.Base using (_≤_ ; s≤s ; z≤n)
import Data.Nat.Properties as NP
open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FP
open import Relation.Nullary.Decidable using (recompute)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Examples.Groups.CCX+HH.Syntactics using (Circuit)
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.Semantics as C
import Examples.Groups.CCX+HH.CircuitTranslation as Translation
import Examples.Groups.CCX+HH.GeneralN.DecodingPlans as Plan
import Examples.Groups.CCX+H.GeneralN.SignPair as Sign
import Examples.Groups.CCX+HH.GeneralN.DoubleExchange as Exchange
import Examples.Groups.CCX+HH.GeneralN.MixedPhysical as Mixed
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as Main
import Examples.Groups.CCX+HH-TwoLevel.Reduction as Reduction
import Presentation.Base as PB

width = 4 + n
N = 2 ^ width
module Transfer = Translation n
private module A = PB (T._===_ {N})

private
  enough : 6 ≤ N
  enough = NP.≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
    (NP.^-monoʳ-≤ 2 {4} {4 + n} (NP.m≤m+n 4 n))

  relevant : ∀ {a b : Fin N} → .(a < b) → a < b
  relevant {a} {b} p = recompute (a FP.<? b) p

atom : Plan.Atom N → Circuit width
atom (Plan.MM a b) = Sign.circuit n a b
atom (Plan.XX a b c d ab cd) = Exchange.Pair.circuit n a b c d (relevant ab) (relevant cd)
atom (Plan.J a b c d ab bc cd) = Mixed.Block.circuit n a b c d
  (relevant ab) (relevant bc) (relevant cd)

atom-correct : ∀ p → C.interpret (atom p) ≡ S.⟦ Plan.e p ⟧ᵐ
atom-correct (Plan.MM a b) = Sign.correct n a b
atom-correct (Plan.XX a b c d ab cd) =
  Exchange.Pair.correct n a b c d (relevant ab) (relevant cd)
atom-correct (Plan.J a b c d ab bc cd) =
  Mixed.Block.correct n a b c d (relevant ab) (relevant bc) (relevant cd)

atoms-correct : ∀ w → E.encode ((atom ʷ) w) A.≈ Plan.read w
atoms-correct [ p ]ʷ = Main.completeness
  (Eq.trans (C.encoding-correct (atom p)) (atom-correct p))
atoms-correct ε = A.refl
atoms-correct (u • v) = A.cong (atoms-correct u) (atoms-correct v)

d : Transfer.Auxiliary.Edge → Circuit width
d y = (atom ʷ) (Plan.plan N enough y)

source-correct : ∀ y → E.encode (d y) A.≈ Transfer.Auxiliary.e y
source-correct y = A.trans (atoms-correct (Plan.plan N enough y))
  (A.sym (Plan.correct N enough y))

correct : ∀ y → C.interpret (d y) ≡ S.⟦ Transfer.Auxiliary.e y ⟧ᵐ
correct y = Eq.trans (Eq.sym (C.encoding-correct (d y)))
  (Reduction.sound-act (source-correct y) S.𝕀)

decoder : Transfer.Decoder
decoder = record { d = d ; correct = correct }
