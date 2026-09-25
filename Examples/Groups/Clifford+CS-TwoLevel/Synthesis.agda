------------------------------------------------------------------------
-- Presentations of groups
--
-- The exact synthesis algorithm (Algorithm 2.10) and its correctness
-- (Theorem 2.9): for a column-orthonormal matrix M, the word synth M
-- is the concatenation N_m ⋯ N_1 of the syllables along the path of
-- normal edges from M to I, and ⟦ synth M ⟧ M = I.
--
-- The recursion is well-founded on the level.  Neither the proof of
-- column-orthonormality nor the accessibility proof affects the word,
-- so the word is a function of the matrix alone (synth-irr), and one
-- normal edge unfolds it (synth-step).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Synthesis where

open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Induction.WellFounded using (Acc ; acc)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (recompute)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base using (Word ; ε ; _•_)
open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (D)
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics
open import Examples.Groups.Clifford+CS-TwoLevel.Pivot
open import Examples.Groups.Clifford+CS-TwoLevel.Syllable using (syl ; step)
open import Examples.Groups.Clifford+CS-TwoLevel.Step using (step-lt)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The algorithm

-- One step preserves column-orthonormality.
ColOrth-step : (M : Matrix n n D) → ColOrth M → ColOrth (step M)
ColOrth-step M o = ColOrth-actMʷ (syl M) o

-- The level drops, as a proof recomputed from the decision, so that
-- the proof of column-orthonormality may be irrelevant.
private
  lt : (M : Matrix n n D) → .(ColOrth M) → ∀ {p} → pivot M ≡ just p → level (step M) <ₗ level M
  lt M o pv = recompute (level (step M) <ₗ? level M) (step-lt o pv)

-- Given the pivot r of M.
synthAt : (M : Matrix n n D) → .(ColOrth M) → Acc _<ₗ_ (level M) →
          (r : Maybe (Fin n)) → pivot M ≡ r → Word (Gen n)
synthAt M o a nothing pv = ε
synthAt M o (acc rs) (just p) pv =
  synthAt (step M) (ColOrth-step M o) (rs (lt M o pv)) (pivot (step M)) refl • syl M

synth : (M : Matrix n n D) → .(ColOrth M) → Word (Gen n)
synth M o = synthAt M o (<ₗ-wellFounded (level M)) (pivot M) refl

------------------------------------------------------------------------
-- Correctness: ⟦ synth M ⟧ M = I

synthAt-correct : (M : Matrix n n D) .(o : ColOrth M) (a : Acc _<ₗ_ (level M))
                  (r : Maybe (Fin n)) (pv : pivot M ≡ r) → actMʷ (synthAt M o a r pv) M ≡ 𝕀
synthAt-correct M o a nothing pv = pivot-nothing M pv
synthAt-correct M o (acc rs) (just p) pv =
  synthAt-correct (step M) (ColOrth-step M o) (rs (lt M o pv)) (pivot (step M)) refl

synth-correct : (M : Matrix n n D) .(o : ColOrth M) → actMʷ (synth M o) M ≡ 𝕀
synth-correct M o = synthAt-correct M o (<ₗ-wellFounded (level M)) (pivot M) refl

------------------------------------------------------------------------
-- The word depends on the matrix alone

synthAt-irr : (M : Matrix n n D) .(o : ColOrth M) (a a′ : Acc _<ₗ_ (level M))
              (r : Maybe (Fin n)) (pv : pivot M ≡ r) → synthAt M o a r pv ≡ synthAt M o a′ r pv
synthAt-irr M o a a′ nothing pv = refl
synthAt-irr M o (acc rs) (acc rs′) (just p) pv =
  cong (_• syl M) (synthAt-irr (step M) (ColOrth-step M o) (rs (lt M o pv)) (rs′ (lt M o pv)) (pivot (step M)) refl)

-- A normal edge M ⇒ step M, with syllable syl M.
synth-step : (M : Matrix n n D) .(o : ColOrth M) {p : Fin n} → pivot M ≡ just p →
             synth M o ≡ synth (step M) (ColOrth-step M o) • syl M
synth-step M o {p} pv = aux (pivot M) refl pv (<ₗ-wellFounded (level M))
  where
  aux : (r : Maybe (Fin _)) (e : pivot M ≡ r) → r ≡ just p → (a : Acc _<ₗ_ (level M)) →
        synthAt M o a r e ≡ synth (step M) (ColOrth-step M o) • syl M
  aux (just .p) e refl (acc rs) =
    cong (_• syl M) (synthAt-irr (step M) (ColOrth-step M o) (rs (lt M o e)) (<ₗ-wellFounded (level (step M)))
                                 (pivot (step M)) refl)
