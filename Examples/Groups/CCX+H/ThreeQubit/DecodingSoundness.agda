------------------------------------------------------------------------
-- Presentations of groups
--
-- The three-wire decoder is a semantic section of the encoding.
--
-- Small exact computations verify the decoder's atoms.  Each K is
-- then checked by its short auxiliary conjugation word, so no proof
-- expands its entire circuit and repeats the atom computations.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.ThreeQubit.DecodingSoundness where

open import Data.Fin.Base using (zero ; suc)
import Data.Fin.Properties as FP
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)
open import Relation.Nullary.Decidable using (recompute)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Examples.Groups.CCX+H.Encoding using (encode)
open import Examples.Groups.CCX+H.ThreeQubit.Decoding
open import Examples.Groups.CCX+H.ThreeQubit.AuxiliaryPlan
import Examples.Groups.CCX+H.ThreeQubit.Checks.X0 as X0Check
import Examples.Groups.CCX+H.ThreeQubit.Checks.X1 as X1Check
import Examples.Groups.CCX+H.ThreeQubit.Checks.X2 as X2Check
import Examples.Groups.CCX+H.ThreeQubit.Checks.X3 as X3Check
import Examples.Groups.CCX+H.ThreeQubit.Checks.X4 as X4Check
import Examples.Groups.CCX+H.ThreeQubit.Checks.X5 as X5Check
import Examples.Groups.CCX+H.ThreeQubit.Checks.X6 as X6Check
import Examples.Groups.CCX+H.ThreeQubit.Checks.X7 as X7Check
import Examples.Groups.CCX+H.ThreeQubit.Checks.Signs as SignCheck
import Examples.Groups.CCX+H.ThreeQubit.Checks.K0 as K0Check
import Examples.Groups.CCX+H.ThreeQubit.Checks.PlanK as PlanCheck
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD)

private module M = S.Dim 4

atom-correct : ∀ a → M.⟦ encode (realise a) ⟧ᴸ ≡ M.⟦ aux a ⟧ᴸ
atom-correct (sign a) = SignCheck.check a
atom-correct (exchange zero b) = X0Check.check b
atom-correct (exchange (suc zero) b) = X1Check.check b
atom-correct (exchange (suc (suc zero)) b) = X2Check.check b
atom-correct (exchange (suc (suc (suc zero))) b) = X3Check.check b
atom-correct (exchange (suc (suc (suc (suc zero)))) b) = X4Check.check b
atom-correct (exchange (suc (suc (suc (suc (suc zero))))) b) = X5Check.check b
atom-correct (exchange (suc (suc (suc (suc (suc (suc zero)))))) b) = X6Check.check b
atom-correct (exchange (suc (suc (suc (suc (suc (suc (suc zero))))))) b) = X7Check.check b
atom-correct k0 = K0Check.check
atom-correct ih = refl

word-correct : ∀ (w : Word Atom) →
  M.⟦ encode ((realise ʷ) w) ⟧ᴸ ≡ M.⟦ (aux ʷ) w ⟧ᴸ
word-correct [ a ]ʷ = atom-correct a
word-correct ε = refl
word-correct (w • v) =
  trans (M.⟦•⟧ᴸ (encode ((realise ʷ) w)) (encode ((realise ʷ) v)))
    (trans (cong₂ _·*·_ (word-correct w) (word-correct v))
      (sym (M.⟦•⟧ᴸ ((aux ʷ) w) ((aux ʷ) v))))

plan-correct : ∀ g → M.⟦ (aux ʷ) (plan g) ⟧ᴸ ≡ M.⟦ [ g ]ʷ ⟧ᴸ
plan-correct T.IH = refl
plan-correct T.⌊ U.M-gen a ⌋ = refl
plan-correct T.⌊ U.X-gen a b p ⌋ =
  cong M.⟦_⟧ᴸ (xword-ordered a b p)
plan-correct T.⌊ U.K-gen a b c d p q r ⌋ =
  PlanCheck.check a b c d (recompute (a FP.<? b) p)
    (recompute (b FP.<? c) q) (recompute (c FP.<? d) r)

-- Every auxiliary generator is realised by a circuit on the same
-- three wires.  No ancilla and no semantic equality axiom is used.
d-correct : ∀ g → M.⟦ encode (d g) ⟧ᴸ ≡ M.⟦ [ g ]ʷ ⟧ᴸ
d-correct g = trans (word-correct (plan g)) (plan-correct g)
