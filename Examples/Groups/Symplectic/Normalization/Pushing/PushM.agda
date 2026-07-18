------------------------------------------------------------------------
-- Presentations of groups
--
-- Pushing a "dirty" S-gate through an M box (the X-normal column
-- M = E · [Vec D]).  This is step ② of the LM-box coset update: the
-- dirty output of pushing a generator through the L box is fed through
-- the M box.
--
--   [ m ]ᵐ • S  ≈  dir • [ m' ]ᵐ
--
-- The S only ever touches the *bottom* box of M: it commutes freely past
-- the ↑-lifted upper D boxes (lemma-comm-S-w↑), and interacts with the
-- bottom D box via aux-DS (Pushing.DS).  Depending on that box's a:
--
--   * a = 0 : the S escapes upward as a direction gate S↑ (box b ↦ b);
--   * a ≠ 0 : the S is absorbed into the box (b ↦ b − a), no direction;
--   * base M 1 = E : the E box E←S absorbs it (e ↦ e − 1), no direction.
--
-- Because aux-DS is stated at arbitrary width (₂₊ n), this holds for the
-- full M (₁₊ n), not just the base widths.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.PushM (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_,_ ; ∃)
open import Data.Vec using (_∷_)
open import Data.Fin using (toℕ)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-Sᵏ-w↑)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.BoxRelations p-2 p-prime
open One using (E←S)
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime using (aux-DS)

open import Notations
open import Word.Base using (Word ; _•_ ; ε)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

------------------------------------------------------------------------
-- Pushing an S-gate through an M box.

push-M-S : ∀ {n} (m : M (₁₊ n)) →
  let open PB ((₁₊ n) QRel,_===_) in
  ∃ λ (dir : Word (Gen (₁₊ n))) → ∃ λ (m' : M (₁₊ n)) → [ m ]ᵐ • S ≈ dir • [ m' ]ᵐ

-- Base case M 1 = E : E←S absorbs the S, no direction gate.
push-M-S {0} e = ε , (e + - ₁) , trans (E←S e) (sym left-unit)
  where open PB (1 QRel,_===_) ; open PP (1 QRel,_===_)

-- a = 0 : the S escapes upward as S↑, box unchanged.
push-M-S {₁₊ n} (e , (₀ , b) ∷ v) = S ↑ , (e , (₀ , b) ∷ v) , claim
  where
  open PB ((₂₊ n) QRel,_===_) ; open PP ((₂₊ n) QRel,_===_) ; open SR word-setoid
  x = ₀ , b
  claim : ([ e ]ᵉ • ([ x ]ᵈ • [ v ]ᵛᵈ ↑)) • S
        ≈ S ↑ • ([ e ]ᵉ • ([ x ]ᵈ • [ v ]ᵛᵈ ↑))
  claim = begin
    ([ e ]ᵉ • ([ x ]ᵈ • [ v ]ᵛᵈ ↑)) • S       ≈⟨ assoc ⟩
    [ e ]ᵉ • (([ x ]ᵈ • [ v ]ᵛᵈ ↑) • S)       ≈⟨ cright assoc ⟩
    [ e ]ᵉ • ([ x ]ᵈ • ([ v ]ᵛᵈ ↑ • S))       ≈⟨ cright (cright (sym (lemma-comm-S-w↑ [ v ]ᵛᵈ))) ⟩
    [ e ]ᵉ • ([ x ]ᵈ • (S • [ v ]ᵛᵈ ↑))       ≈⟨ cright (sym assoc) ⟩
    [ e ]ᵉ • (([ x ]ᵈ • S) • [ v ]ᵛᵈ ↑)       ≈⟨ cright (cleft (aux-DS x)) ⟩
    [ e ]ᵉ • ((S ↑ • [ x ]ᵈ) • [ v ]ᵛᵈ ↑)     ≈⟨ cright assoc ⟩
    [ e ]ᵉ • (S ↑ • ([ x ]ᵈ • [ v ]ᵛᵈ ↑))     ≈⟨ sym assoc ⟩
    ([ e ]ᵉ • S ↑) • ([ x ]ᵈ • [ v ]ᵛᵈ ↑)     ≈⟨ cleft (lemma-comm-Sᵏ-w↑ (toℕ (- e)) S) ⟩
    (S ↑ • [ e ]ᵉ) • ([ x ]ᵈ • [ v ]ᵛᵈ ↑)     ≈⟨ assoc ⟩
    S ↑ • ([ e ]ᵉ • ([ x ]ᵈ • [ v ]ᵛᵈ ↑))     ∎

-- a ≠ 0 : the S is absorbed by the bottom D box (b ↦ b − a).
push-M-S {₁₊ n} (e , (a@(₁₊ i) , b) ∷ v) = ε , (e , (a , b + - a) ∷ v) , claim
  where
  open PB ((₂₊ n) QRel,_===_) ; open PP ((₂₊ n) QRel,_===_) ; open SR word-setoid
  x  = a , b
  x' = a , b + - a
  claim : ([ e ]ᵉ • ([ x ]ᵈ • [ v ]ᵛᵈ ↑)) • S
        ≈ ε • ([ e ]ᵉ • ([ x' ]ᵈ • [ v ]ᵛᵈ ↑))
  claim = begin
    ([ e ]ᵉ • ([ x ]ᵈ • [ v ]ᵛᵈ ↑)) • S       ≈⟨ assoc ⟩
    [ e ]ᵉ • (([ x ]ᵈ • [ v ]ᵛᵈ ↑) • S)       ≈⟨ cright assoc ⟩
    [ e ]ᵉ • ([ x ]ᵈ • ([ v ]ᵛᵈ ↑ • S))       ≈⟨ cright (cright (sym (lemma-comm-S-w↑ [ v ]ᵛᵈ))) ⟩
    [ e ]ᵉ • ([ x ]ᵈ • (S • [ v ]ᵛᵈ ↑))       ≈⟨ cright (sym assoc) ⟩
    [ e ]ᵉ • (([ x ]ᵈ • S) • [ v ]ᵛᵈ ↑)       ≈⟨ cright (cleft (aux-DS x)) ⟩
    [ e ]ᵉ • ((ε ↑ • [ x' ]ᵈ) • [ v ]ᵛᵈ ↑)    ≈⟨ cright (cleft left-unit) ⟩
    [ e ]ᵉ • ([ x' ]ᵈ • [ v ]ᵛᵈ ↑)            ≈⟨ sym left-unit ⟩
    ε • ([ e ]ᵉ • ([ x' ]ᵈ • [ v ]ᵛᵈ ↑))      ∎
