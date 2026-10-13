------------------------------------------------------------------------
-- Presentations of groups
--
-- Canonical sign words and their normalization in the compact theory.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.Compact.Diagonal where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; tail)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Examples.Groups.CCX+HH.ThreeQubit.Compact.Syntactics
import Examples.Groups.CCX+HH.ThreeQubit.StabilizerNormalForm as NF
import Examples.Groups.CCX+HH.ThreeQubit.PhaseNormalization as PN
import Presentation.Base as PB

private module R = PB _===_
module Diagonal = PN _===_ P (λ i → R.axiom (phase-square i)) phase-commutation

plan : ∀ {n} → (Fin n → Fin 7) → Vec Bool n → Word (Fin 7)
plan f [] = ε
plan f (false ∷ s) = plan (λ i → f (suc i)) s
plan f (true ∷ s) = [ f zero ]ʷ • plan (λ i → f (suc i)) s

plan-correct : ∀ {n} (f : Fin n → Fin 7) s →
  (P ʷ) (plan f s) ≡ NF.phase-word f s
plan-correct f [] = refl
plan-correct f (false ∷ s) = plan-correct (λ i → f (suc i)) s
plan-correct f (true ∷ s) = Eq.cong (P (f zero) •_) (plan-correct (λ i → f (suc i)) s)

section-correct : ∀ {n} (f : Fin n → Fin 7) s →
  Diagonal.section f s ≡ NF.phase-word f s
section-correct f [] = refl
section-correct f (false ∷ s) = section-correct (λ i → f (suc i)) s
section-correct f (true ∷ s) = Eq.cong (P (f zero) •_) (section-correct (λ i → f (suc i)) s)

transformed : Fin 7 → Vec Bool 7 → Vec Bool 7
transformed i s = Diagonal.nf ((conjugate i ʷ) (plan (λ j → j) s))

permuted : Fin 7 → Vec Bool 7 → Vec Bool 7
permuted i s = tail (NF.swap i (NF.parity s ∷ s))
