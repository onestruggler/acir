------------------------------------------------------------------------
-- Presentations of groups
--
-- At p = 5, semi-M↑CZ is independent of the other Paper-V1 rules
--
-- SemiMCZ3's witness at p = 5, g = 2: the affine symplectic model of
-- Affine with CZ twisted by the Pauli (Z ⊗ Z)^t, t = 1.  Every rule but
-- semi-M↑CZ holds in it, and semi-M↑CZ fails at width 2.
--
-- Every rule is checked by evaluating both sides at all points: the 25
-- of width 1 for the one-wire rules there, the 625 of width 2 for
-- every one- and two-wire rule there, M-power once per exponent.  The
-- three-wire rules start at width 3, where the model has one point.
-- This is the slowest module of the directory, at about five minutes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qupit.Independence.SemiMCZ5 where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Notations
open import Word.Base using (Word)
open import ForStdlib.Data.Fin.Mod using (-_)

open import Examples.Groups.ProjectiveClifford.Qupit.Independence.Parameters
  using (prime-5 ; root-5 ; root-5-gen)
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  2 prime-5 root-5 root-5-gen as Pap
open Pap using (Gen)
open Pap.Clifford-Relations using (module Base ; srel)
open Base using (_SRel,_===_)
open import Examples.Groups.ProjectiveClifford.Qupit.Independence.Selection
  2 prime-5 root-5 root-5-gen
  using (semi-M↑CZ ; Without ; _IndependentOf_ ; module Soundness)

-- S translates by −½, which is 2 mod 5; the twist is 1.
S-translation : - Pap.1/2 ≡ ₂
S-translation = refl

import Examples.Groups.ProjectiveClifford.Qupit.Independence.Affine
  2 prime-5 root-5 root-5-gen ₂ ₁ as A

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
sound-srel {1} (Base.M-power ₃)    _  = A.decide 1 tt
sound-srel {1} (Base.M-power ₄)    _  = A.decide 1 tt
sound-srel {1} Base.semi-MR        _  = A.decide 1 tt
sound-srel {1} Base.comm-HHSHHS    _  = A.decide 1 tt
-- width 2
sound-srel {2} Base.order-S        _  = A.decide 2 tt
sound-srel {2} Base.order-H        _  = A.decide 2 tt
sound-srel {2} (Base.M-power ₀)    _  = A.decide 2 tt
sound-srel {2} (Base.M-power ₁)    _  = A.decide 2 tt
sound-srel {2} (Base.M-power ₂)    _  = A.decide 2 tt
sound-srel {2} (Base.M-power ₃)    _  = A.decide 2 tt
sound-srel {2} (Base.M-power ₄)    _  = A.decide 2 tt
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

semi-M↑CZ-independent : srel (Base.semi-M↑CZ {0}) IndependentOf semi-M↑CZ
semi-M↑CZ-independent = independent (srel Base.semi-M↑CZ) (A.refute 2 tt)
