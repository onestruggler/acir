------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantic content of Proposition 2.55's `sound-ax` for the qubit
-- Clifford extension: how Pauli words behave in CMS n.
--
-- sound-ax has to check two families against the P4-action:
--
--   ConjRelʷ conj   x · y = conj x y · x   for a gate x and a Pauli
--                   generator y — conj records conjugation in CMS n;
--   RelTwist  corr  [ ū ]ᵣ = [ corr r̄ ]ₗ · [ v̄ ]ᵣ  for each symplectic
--                   relator r̄ — corr records the Pauli that lifting r̄
--                   accumulates.
--
-- This module proves the two lemmas the first family rests on, both
-- about `pauliWord` (which IS the extension's inclusion, so ⟦_⟧₀ of a
-- Pauli generator):
--
--   pauliWord-∙    pauliWord P · pauliWord Q = pauliWord (P +ₚ Q)
--   pauli-conj     x · pauliWord P = pauliWord (actg x P) · x
--
-- The second is the conjugation law itself, and its proof is the one
-- line of mathematics in the whole family: conjugating by a Clifford
-- moves the phase by ι (sform P R), and the symplectic action preserves
-- sform (Interpretation.actg-sform), so both sides collect the same
-- phase.  Nothing is computed gate by gate — no case analysis on x at
-- all — which is what keeps this clear of the cact blow-up that
-- Selinger.Soundness has to work around.
--
-- What still separates these from `sound-ax` itself:
--
--   * the ConjRelʷ case needs, in addition, that ⟦_⟧ of a left-embedded
--     `vecToWord P` is pauliWord P — the delogging lemma.  conj x y is
--     by definition vecToWord (actg x (genToVec y)), so with that lemma
--     the case is exactly pauli-conj at P = genToVec y;
--   * the RelTwist case is per-relator: for each axiom of the simplified
--     symplectic rule set, its two sides must act alike up to the
--     correction (Z₀ for order-S, ε elsewhere, shifted by cong↑).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.ExtensionSoundness where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Zp.ModularArithmetic
open import Word.Base using (Word ; [_]ʷ ; _•_)

open import Examples.Groups.Clifford.Qubit.CliffordGroup
  using (p-2 ; p-prime ; _≈ᶜ_ ; pauliWord ; cact-pauliWord ; sform-+ˡ)

open PrimeModulus p-2 p-prime

open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using (Pauli ; sform ; _+ₚ_)
import Examples.Groups.Symplectic.Semantics p-2 p-prime as SympSem
open SympSem.Interpretation using (actg ; actg-sform)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen)

open import Examples.Groups.Clifford.Qubit.SignedPauli using (Φ ; P4Carrier ; ι ; ι-+)
open import Examples.Groups.Clifford.Qubit.CliffordAction using (cact ; δ)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- ℤ/4 rearrangements

private
  -- (s + a) + b ≡ s + (b + a): the two orders in which two phases can be
  -- collected onto s.
  swap-onto : (s a b : Φ) → (s + a) + b ≡ s + (b + a)
  swap-onto s a b = Eq.trans (+-assoc s a b) (Eq.cong (s +_) (+-comm a b))

------------------------------------------------------------------------
-- Pauli words multiply by adding their vectors
--
-- Conjugation by P shifts the phase by ι (sform P R) and fixes the
-- phaseless Pauli (CliffordGroup.cact-pauliWord), so composing two of
-- them adds the two shifts — and sform is additive in its first
-- argument.

pauliWord-∙ : (P Q : Pauli n) →
              (pauliWord P • pauliWord Q) ≈ᶜ pauliWord (P +ₚ Q)
pauliWord-∙ P Q (s , R) = begin
  cact (pauliWord P) (cact (pauliWord Q) (s , R))
    ≡⟨ Eq.cong (cact (pauliWord P)) (cact-pauliWord Q s R) ⟩
  cact (pauliWord P) (s + ι (sform Q R) , R)
    ≡⟨ cact-pauliWord P (s + ι (sform Q R)) R ⟩
  ((s + ι (sform Q R)) + ι (sform P R)) , R
    ≡⟨ Eq.cong (_, R) (swap-onto s (ι (sform Q R)) (ι (sform P R))) ⟩
  (s + (ι (sform P R) + ι (sform Q R))) , R
    ≡⟨ Eq.cong (λ □ → (s + □) , R) (Eq.sym (ι-+ (sform P R) (sform Q R))) ⟩
  (s + ι (sform P R + sform Q R)) , R
    ≡⟨ Eq.cong (λ □ → (s + ι □) , R) (Eq.sym (sform-+ˡ P Q R)) ⟩
  (s + ι (sform (P +ₚ Q) R)) , R
    ≡⟨ Eq.sym (cact-pauliWord (P +ₚ Q) s R) ⟩
  cact (pauliWord (P +ₚ Q)) (s , R)   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Conjugation: a gate moves a Pauli word past itself, symplectically
--
-- This is the ConjRelʷ family's mathematical content.  Reading both
-- sides at (s , R):
--
--   x · P  :  R ↦ actg x R,  phase  s + ι (sform P R)      + δ x R
--   (x·P·x⁻¹) · x :  R ↦ actg x R,  phase  s + δ x R + ι (sform (actg x P) (actg x R))
--
-- and the two phases agree because actg x preserves sform.  No gate is
-- ever unfolded: `x` stays a variable throughout.

pauli-conj : (x : Gen n) (P : Pauli n) →
             ([ x ]ʷ • pauliWord P) ≈ᶜ (pauliWord (actg x P) • [ x ]ʷ)
pauli-conj x P (s , R) = begin
  cact [ x ]ʷ (cact (pauliWord P) (s , R))
    ≡⟨ Eq.cong (cact [ x ]ʷ) (cact-pauliWord P s R) ⟩
  cact [ x ]ʷ (s + ι (sform P R) , R)
    ≡⟨ Eq.refl ⟩
  ((s + ι (sform P R)) + δ x R) , actg x R
    ≡⟨ Eq.cong (_, actg x R) (swap-onto s (ι (sform P R)) (δ x R)) ⟩
  (s + (δ x R + ι (sform P R))) , actg x R
    ≡⟨ Eq.cong (λ □ → (s + (δ x R + ι □)) , actg x R)
               (Eq.sym (actg-sform x P R)) ⟩
  (s + (δ x R + ι (sform (actg x P) (actg x R)))) , actg x R
    ≡⟨ Eq.cong (_, actg x R)
               (Eq.sym (+-assoc s (δ x R) (ι (sform (actg x P) (actg x R))))) ⟩
  ((s + δ x R) + ι (sform (actg x P) (actg x R))) , actg x R
    ≡⟨ Eq.sym (cact-pauliWord (actg x P) (s + δ x R) (actg x R)) ⟩
  cact (pauliWord (actg x P)) (s + δ x R , actg x R)
    ≡⟨ Eq.refl ⟩
  cact (pauliWord (actg x P)) (cact [ x ]ʷ (s , R))   ∎
  where open Eq.≡-Reasoning
