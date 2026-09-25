------------------------------------------------------------------------
-- Presentations of groups
--
-- The Main Lemma (Lemma 3.10), by the basic generator: Case 1 (H_[0,1],
-- CaseH), Case 2 (ω_[0], CaseW) and Cases 3–5 (X_[α,α+1], CaseX, with
-- its hard subcase in CaseXM, in dimension at most 4); and with it the
-- completeness of the relations.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; suc)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.MainLemma {n : ℕ} where

open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Maybe.Base using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base using (Word)
import Presentation.Base as PB
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring using (D)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (ColOrth ; ⟦_⟧ᵐ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Pivot using (pivot)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Basic {n} using (bX ; bH ; bω)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Reduction {n} using (MainLemma ; completeness)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.BaseCase {n} using (base)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.ExpLevel {n} using (exp-level)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.CaseH {n} using (caseH)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.CaseW {n} using (caseW)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.CaseX {n} using (caseX ; Hard)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.CaseXM {n} using (hard)

open PB (_===_ {n}) using (_≈_)

-- The hard subcase of Cases 3–5, at every instance.
HardAll : Set
HardAll = ∀ (α β : Fin n) (αβ1 : toℕ β ≡ suc (toℕ α)) (s : Matrix n n D) .(o : ColOrth s) {p : Fin n}
          (ps : pivot s ≡ just p) → Hard α β αβ1 s o ps

main-lemma : HardAll → MainLemma
main-lemma hard (X-gen a b _) (bX e) s o ps = caseX a b e s o ps (hard a b e s o ps)
main-lemma hard (H-gen a b _) (bH a0 b1) s o ps = caseH a b a0 b1 s o ps
main-lemma hard (ω-gen a) (bω a0) s o ps = caseW a a0 s o ps

-- The relations are complete, given the hard subcase.
completeness-given : HardAll → {u v : Word (Gen n)} → ⟦ u ⟧ᵐ ≡ ⟦ v ⟧ᵐ → u ≈ v
completeness-given hard = completeness (main-lemma hard) base exp-level

------------------------------------------------------------------------
-- In dimension at most 4

module _ (n≤4 : n ℕ.≤ 4) where

  -- The hard subcase (CaseXM), and so the Main Lemma.
  hard-all : HardAll
  hard-all α β αβ1 s o ps = hard n≤4 α β αβ1 s o ps

  main : MainLemma
  main = main-lemma hard-all

  -- The relations are complete: words with the same matrix are equal
  -- in the presentation.
  relations-complete : {u v : Word (Gen n)} → ⟦ u ⟧ᵐ ≡ ⟦ v ⟧ᵐ → u ≈ v
  relations-complete = completeness main base exp-level
