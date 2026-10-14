------------------------------------------------------------------------
-- Presentations of groups
--
-- Finite checks by one boolean, for the generated coset tables of the
-- natural calculus: a property of every state, and distinctness of
-- representatives from a table of their matrices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.Checks where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; T)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Quantum.Synthesis.Ring using (Dyadic)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Examples.Groups.CCX+HH.Decide using (eqMat ; eqD ; eqMat-sound ; eqMat-refl ; eqD-sound ; eqD-refl)

allF : ∀ {K} → (Fin K → Bool) → Bool
allF {zero} p = true
allF {suc K} p = p zero ∧ allF {K} (λ c → p (suc c))

allF-sound : ∀ {K} (p : Fin K → Bool) → T (allF p) → ∀ c → T (p c)
allF-sound {suc K} p h zero with p zero
allF-sound {suc K} p h zero | true = tt
allF-sound {suc K} p () zero | false
allF-sound {suc K} p h (suc c) with p zero
allF-sound {suc K} p h (suc c) | true = allF-sound (λ c → p (suc c)) h c
allF-sound {suc K} p () (suc c) | false

-- A table of matrices, checked against the representatives and checked
-- pairwise distinct, makes the representatives' matrices distinct.
module Distinct {K m : ℕ} (sem : Fin K → Matrix m m Dyadic) (table : Fin K → Matrix m m Dyadic)
  (agree : T (allF (λ c → eqMat eqD (sem c) (table c))))
  (apart : T (allF (λ c → allF (λ d → (toℕ c ≡ᵇ toℕ d) ∨ not (eqMat eqD (table c) (table d))))))
  where

  private
    agree′ : ∀ c → sem c ≡ table c
    agree′ c = eqMat-sound eqD eqD-sound _ _ (allF-sound _ agree c)

    same-table : ∀ c d → table c ≡ table d → c ≡ d
    same-table c d e = FP.toℕ-injective (≡ᵇ⇒≡ _ _ (lemma (allF-sound _ (allF-sound _ apart c) d)))
      where
      eqT : T (eqMat eqD (table c) (table d))
      eqT = Eq.subst (λ M → T (eqMat eqD (table c) M)) e (eqMat-refl eqD eqD-refl (table c))
      lemma : T ((toℕ c ≡ᵇ toℕ d) ∨ not (eqMat eqD (table c) (table d))) → T (toℕ c ≡ᵇ toℕ d)
      lemma h with toℕ c ≡ᵇ toℕ d | eqMat eqD (table c) (table d) | eqT
      ... | true | _ | _ = tt
      ... | false | true | _ = h
      ... | false | false | ()

  distinct : ∀ c d → sem c ≡ sem d → c ≡ d
  distinct c d e = same-table c d (Eq.trans (Eq.sym (agree′ c)) (Eq.trans e (agree′ d)))
