------------------------------------------------------------------------
-- Presentations of groups
--
-- The Main Lemma (Lemma 3.6), by the basic generator: Case 1 (i_[0],
-- CaseI), Case 2 (K_[0,1], CaseK) and Case 3 (X_[α,α+1], CaseX, with
-- its hard subcase in CaseXM); and with it the completeness of
-- the relations (Theorem 3.2).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; suc)

module Examples.Groups.Clifford+CS-TwoLevel.MainLemma {n : ℕ} where

open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Maybe.Base using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base using (Word)
import Presentation.Base as PB
open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (D)
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics using (ColOrth ; ⟦_⟧ᵐ)
open import Examples.Groups.Clifford+CS-TwoLevel.Pivot using (pivot)
open import Examples.Groups.Clifford+CS-TwoLevel.Basic {n} using (bX ; bK ; bi)
open import Examples.Groups.Clifford+CS-TwoLevel.Reduction {n} using (MainLemma ; completeness)
open import Examples.Groups.Clifford+CS-TwoLevel.BaseCase {n} using (base)
open import Examples.Groups.Clifford+CS-TwoLevel.ExpLevel {n} using (exp-level)
open import Examples.Groups.Clifford+CS-TwoLevel.CaseI {n} using (caseI)
open import Examples.Groups.Clifford+CS-TwoLevel.CaseK {n} using (caseK)
open import Examples.Groups.Clifford+CS-TwoLevel.CaseX {n} using (caseX ; Hard)
open import Examples.Groups.Clifford+CS-TwoLevel.CaseXM {n} using (hard)

open PB (_===_ {n}) using (_≈_)

-- The hard subcase of Case 3, at every instance.
HardAll : Set
HardAll = ∀ (α β : Fin n) (αβ1 : toℕ β ≡ suc (toℕ α)) (s : Matrix n n D) .(o : ColOrth s) {p : Fin n}
          (ps : pivot s ≡ just p) → Hard α β αβ1 s o ps

main-lemma : HardAll → MainLemma
main-lemma hard (X-gen a b _) (bX e) s o ps = caseX a b e s o ps (hard a b e s o ps)
main-lemma hard (K-gen a b _) (bK a0 b1) s o ps = caseK a b a0 b1 s o ps
main-lemma hard (i-gen a) (bi a0) s o ps = caseI a a0 s o ps

-- Theorem 3.2, given the hard subcase.
completeness-given : HardAll → {u v : Word (Gen n)} → ⟦ u ⟧ᵐ ≡ ⟦ v ⟧ᵐ → u ≈ v
completeness-given hard = completeness (main-lemma hard) base exp-level

-- The hard subcase (CaseXM), and so the Main Lemma.
hard-all : HardAll
hard-all α β αβ1 s o ps = hard α β αβ1 s o ps

main : MainLemma
main = main-lemma hard-all

-- Theorem 3.2: the relations are complete, words with the same matrix
-- are equal in the presentation.
relations-complete : {u v : Word (Gen n)} → ⟦ u ⟧ᵐ ≡ ⟦ v ⟧ᵐ → u ≈ v
relations-complete = completeness main base exp-level
