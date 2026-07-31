------------------------------------------------------------------------
-- Presentations of groups
--
-- General-width version of BR.Three.B-CZ.lemma-dir-and-b'-cz: pushing CZ
-- through a single lifted B box leaves the box unchanged and emits the
-- residual dir = CZ02 • CZ^k.  The width-3 core is widened to width
-- (₃₊ n) by CongDownK.cong↓ᵏ, exactly as BR.Three.DD-CZ-n.gen-dd-cz
-- widens DD-CZ.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.PushBcz (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

import Relation.Binary.PropositionalEquality as Eq

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime using (cong↓ᵏ)
open import Examples.Groups.Symplectic.BR.Three.BB-CZ-n p-2 p-prime using (b↑-↓ᵏ)
import Examples.Groups.Symplectic.BR.Three.B-CZ p-2 p-prime as BCZ

open import Notations
open import Word.Base using (_•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

module _ {n : ℕ} where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid

  -- CZ ↓ᵏ n ≡ CZ is definitional (gate₂ ↧ᵏ k = gate₂), hence Eq.refl.
  gen-B↑←CZ : ∀ (x : B) →
    ([ x ]ᵇ ↑) • CZ ≈ (BCZ.dir-of x ↓ᵏ n) • ([ x ]ᵇ ↑)
  gen-B↑←CZ x = begin
    ([ x ]ᵇ ↑) • CZ                                ≈⟨ refl' eqL ⟩
    (([_]ᵇ {0} x ↑) • CZ) ↓ᵏ n                     ≈⟨ cong↓ᵏ n _ _ (BCZ.lemma-dir-and-b'-cz x) ⟩
    (BCZ.dir-of x • ([_]ᵇ {0} x ↑)) ↓ᵏ n           ≈⟨ refl' eqR ⟩
    (BCZ.dir-of x ↓ᵏ n) • ([ x ]ᵇ ↑)               ∎
    where
    eqL : ([ x ]ᵇ ↑) • CZ Eq.≡ (([_]ᵇ {0} x ↑) • CZ) ↓ᵏ n
    eqL = Eq.cong₂ _•_ (Eq.sym (b↑-↓ᵏ x n)) Eq.refl
    eqR : (BCZ.dir-of x • ([_]ᵇ {0} x ↑)) ↓ᵏ n Eq.≡ (BCZ.dir-of x ↓ᵏ n) • ([ x ]ᵇ ↑)
    eqR = Eq.cong₂ _•_ Eq.refl (b↑-↓ᵏ x n)
