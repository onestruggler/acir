------------------------------------------------------------------------
-- Presentations of groups
--
-- At p = 3, semi-M↑CZ is independent of the other Paper-V1 rules
--
-- The witness is the affine symplectic model of Affine with CZ twisted
-- by the Pauli (Z ⊗ Z)^t, t = 1: every rule but semi-M↑CZ holds in it,
-- and semi-M↑CZ fails at width 2.  The survey found the same at every
-- p, g and t ≠ 0 it tried; here the model is checked at p = 3, g = 2,
-- and in SemiMCZ5 at p = 5, g = 2.
--
-- Every rule is checked by evaluating both sides at all points: the 9
-- of width 1 for the one-wire rules there, the 81 of width 2 for
-- every one- and two-wire rule there, M-power once per exponent.  The
-- three-wire rules start at width 3, where the model has one point.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qupit.Independence.SemiMCZ3 where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Notations
open import Word.Base using (Word)
open import ForStdlib.Data.Fin.Mod using (-_)

open import Examples.Groups.ProjectiveClifford.Qupit.Independence.Parameters
  using (prime-3 ; root-3 ; root-3-gen)
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  0 prime-3 root-3 root-3-gen as Pap
open Pap using (Gen)
open Pap.Clifford-Relations using (module Base ; srel)
open Base using (_SRel,_===_)
open import Examples.Groups.ProjectiveClifford.Qupit.Independence.Selection
  0 prime-3 root-3 root-3-gen
  using (semi-M↑CZ ; Without ; _IndependentOf_ ; module Soundness)

-- S translates by −½, which is 1 mod 3; the twist is 1.
S-translation : - Pap.1/2 ≡ ₁
S-translation = refl

import Examples.Groups.ProjectiveClifford.Qupit.Independence.Affine
  0 prime-3 root-3 root-3-gen ₁ ₁ as A

private
  variable
    n : ℕ
    w v : Word (Gen n)

open Soundness semi-M↑CZ A.mon A.⟦_⟧₀

sound-srel : (s : n SRel, w === v) → Without semi-M↑CZ (srel s) →
             ∀ x → ⟦ w ⟧ x ≡ ⟦ v ⟧ x
sound-srel {0} () _
-- width 1
sound-srel {1} Base.order-S        _  = A.decide 1 tt
sound-srel {1} Base.order-H        _  = A.decide 1 tt
sound-srel {1} (Base.M-power ₀)    _  = A.decide 1 tt
sound-srel {1} (Base.M-power ₁)    _  = A.decide 1 tt
sound-srel {1} (Base.M-power ₂)    _  = A.decide 1 tt
sound-srel {1} Base.semi-MR        _  = A.decide 1 tt
sound-srel {1} Base.comm-HHSHHS    _  = A.decide 1 tt
-- width 2
sound-srel {2} Base.order-S        _  = A.decide 2 tt
sound-srel {2} Base.order-H        _  = A.decide 2 tt
sound-srel {2} (Base.M-power ₀)    _  = A.decide 2 tt
sound-srel {2} (Base.M-power ₁)    _  = A.decide 2 tt
sound-srel {2} (Base.M-power ₂)    _  = A.decide 2 tt
sound-srel {2} Base.semi-MR        _  = A.decide 2 tt
sound-srel {2} Base.comm-HHSHHS    _  = A.decide 2 tt
sound-srel {2} Base.order-CZ       _  = A.decide 2 tt
sound-srel {2} Base.order-Ex       _  = A.decide 2 tt
sound-srel {2} Base.comm-CZ-S↑     _  = A.decide 2 tt
sound-srel {2} Base.semi-M↑CZ      ¬u = ⊥-elim (¬u refl)
sound-srel {2} Base.semi-Ex-S↑     _  = A.decide 2 tt
sound-srel {2} Base.semi-Ex-H↑     _  = A.decide 2 tt
sound-srel {2} Base.blake-c12      _  = A.decide 2 tt
-- widths ≥ 3
sound-srel {₃₊ _} _                _  = λ _ → refl

open Shift (λ {n} → A.σ {n}) (λ {n} → A.σ-hom {n}) (λ _ _ → refl)
open Rules sound-srel sound-cong↑
  (λ {n} h g _ → A.comm₁ n h g)
  (λ {n} h g _ → A.comm₂ n h g)
  (λ ())
  public

-- At width 2 the two sides of semi-M↑CZ have the same linear part —
-- the untwisted model satisfies the rule — but not the same
-- translation: the left side twists g times, the right side once.
semi-M↑CZ-independent : srel (Base.semi-M↑CZ {0}) IndependentOf semi-M↑CZ
semi-M↑CZ-independent = independent (srel Base.semi-M↑CZ) (A.refute 2 tt)
