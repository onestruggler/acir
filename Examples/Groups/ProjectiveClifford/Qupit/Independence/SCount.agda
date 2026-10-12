------------------------------------------------------------------------
-- Presentations of groups
--
-- At p = 3, blake-c12 and semi-Ex-S↑ are independent of the other
-- Paper-V1 rules
--
-- Both witnesses count S letters mod 3, in the additive group ℤ/3ℤ,
-- which is commutative, so every structural comm rule holds in it.
--
--   * Counting every S, on every wire, at every width: each rule but
--     blake-c12 has as many S letters on each side, mod 3.  blake-c12
--     has 2 + 2 + 1 = 5 on the left and none on the right.  Shifting
--     does not change the count, so the shift is the identity.
--
--   * Counting only the S letters on wire 0: shifting a word up a wire
--     takes all its letters off wire 0, so the shift is the zero map.
--     semi-Ex-S↑ has its S on wire 1 on the left and on wire 0 on the
--     right; every other rule has as many S letters on wire 0 on each
--     side, mod 3.
--
-- Both depend on p = 3: at p = 5 the survey found blake-c12 redundant,
-- and semi-Ex-S↑ open.  Every rule is checked by computation, so the
-- exponents of the multiplier words — through toℕ, ½ and the inverse
-- of the root — are evaluated, and M-power is checked at each of its
-- three exponents.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qupit.Independence.SCount where

open import Algebra.Bundles using (Monoid ; Ring)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Notations
open import Word.Base using (Word)
open import ForStdlib.Data.Fin.Mod using (ℤ ; +-*-ring)

open import Examples.Groups.ProjectiveClifford.Qupit.Independence.Parameters
  using (prime-3 ; root-3 ; root-3-gen)
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  0 prime-3 root-3 root-3-gen as Pap
open Pap using (H-gate ; S-gate ; Gen ; gate₀ ; gate₁ ; gate₂ ; _↥)
open Pap.Clifford-Relations using (module Base ; srel)
open Base using (_SRel,_===_)
open import Examples.Groups.ProjectiveClifford.Qupit.Independence.Selection
  0 prime-3 root-3 root-3-gen
  using (blake-c12 ; semi-Ex-S↑ ; Without ; _IndependentOf_ ; module Soundness)

private
  variable
    n : ℕ
    w v : Word (Gen n)

------------------------------------------------------------------------
-- ℤ/3ℤ, at every width

ℤ₃ : Monoid _ _
ℤ₃ = Ring.+-monoid (+-*-ring 1)

open Ring (+-*-ring 1) using (+-comm)

------------------------------------------------------------------------
-- blake-c12: every S letter

module All-S where

  ⟦_⟧₀ : Gen n → ℤ 3
  ⟦ gate₀ () ⟧₀
  ⟦ gate₁ H-gate ⟧₀ = ₀
  ⟦ gate₁ S-gate ⟧₀ = ₁
  ⟦ gate₂ _ ⟧₀      = ₀
  ⟦ g ↥ ⟧₀          = ⟦ g ⟧₀

  open Soundness blake-c12 (λ _ → ℤ₃) ⟦_⟧₀
  open Shift (λ x → x)
    (record { isMagmaHomomorphism = record
                { isRelHomomorphism = record { cong = λ e → e }
                ; homo = λ _ _ → refl }
            ; ε-homo = refl })
    (λ _ → refl)

  sound-srel : (s : n SRel, w === v) → Without blake-c12 (srel s) →
               ⟦ w ⟧ ≡ ⟦ v ⟧
  sound-srel Base.order-S        _  = refl
  sound-srel Base.order-H        _  = refl
  sound-srel (Base.M-power ₀)    _  = refl
  sound-srel (Base.M-power ₁)    _  = refl
  sound-srel (Base.M-power ₂)    _  = refl
  sound-srel Base.semi-MR        _  = refl
  sound-srel Base.comm-HHSHHS    _  = refl
  sound-srel Base.order-CZ       _  = refl
  sound-srel Base.order-Ex       _  = refl
  sound-srel Base.comm-CZ-S↑     _  = refl
  sound-srel Base.semi-M↑CZ      _  = refl
  sound-srel Base.semi-Ex-S↑     _  = refl
  sound-srel Base.semi-Ex-H↑     _  = refl
  sound-srel Base.blake-c12      ¬u = ⊥-elim (¬u refl)
  sound-srel Base.yang-baxter    _  = refl
  sound-srel Base.cz-slide       _  = refl
  sound-srel Base.semi-CX↑-CZ↓   _  = refl

  open Rules sound-srel sound-cong↑
    (λ {n} h g _ → +-comm ⟦ g ↥ ⟧₀ ⟦ gate₁ {n = n} h ⟧₀)
    (λ {n} h g _ → +-comm ⟦ g ↥ ↥ ⟧₀ ⟦ gate₂ {n = n} h ⟧₀)
    (λ ())
    public

  -- At width 2 the left side of blake-c12 has five S letters, the
  -- right side none.
  blake-c12-independent : srel (Base.blake-c12 {0}) IndependentOf blake-c12
  blake-c12-independent = independent (srel Base.blake-c12) λ ()

------------------------------------------------------------------------
-- semi-Ex-S↑: the S letters on wire 0

module Wire₀-S where

  ⟦_⟧₀ : Gen n → ℤ 3
  ⟦ gate₀ () ⟧₀
  ⟦ gate₁ H-gate ⟧₀ = ₀
  ⟦ gate₁ S-gate ⟧₀ = ₁
  ⟦ gate₂ _ ⟧₀      = ₀
  ⟦ _ ↥ ⟧₀          = ₀

  open Soundness semi-Ex-S↑ (λ _ → ℤ₃) ⟦_⟧₀
  open Shift (λ _ → ₀)
    (record { isMagmaHomomorphism = record
                { isRelHomomorphism = record { cong = λ _ → refl }
                ; homo = λ _ _ → refl }
            ; ε-homo = refl })
    (λ _ → refl)

  sound-srel : (s : n SRel, w === v) → Without semi-Ex-S↑ (srel s) →
               ⟦ w ⟧ ≡ ⟦ v ⟧
  sound-srel Base.order-S        _  = refl
  sound-srel Base.order-H        _  = refl
  sound-srel (Base.M-power ₀)    _  = refl
  sound-srel (Base.M-power ₁)    _  = refl
  sound-srel (Base.M-power ₂)    _  = refl
  sound-srel Base.semi-MR        _  = refl
  sound-srel Base.comm-HHSHHS    _  = refl
  sound-srel Base.order-CZ       _  = refl
  sound-srel Base.order-Ex       _  = refl
  sound-srel Base.comm-CZ-S↑     _  = refl
  sound-srel Base.semi-M↑CZ      _  = refl
  sound-srel Base.semi-Ex-S↑     ¬u = ⊥-elim (¬u refl)
  sound-srel Base.semi-Ex-H↑     _  = refl
  sound-srel Base.blake-c12      _  = refl
  sound-srel Base.yang-baxter    _  = refl
  sound-srel Base.cz-slide       _  = refl
  sound-srel Base.semi-CX↑-CZ↓   _  = refl

  open Rules sound-srel sound-cong↑
    (λ {n} h g _ → +-comm ⟦ g ↥ ⟧₀ ⟦ gate₁ {n = n} h ⟧₀)
    (λ {n} h g _ → +-comm ⟦ g ↥ ↥ ⟧₀ ⟦ gate₂ {n = n} h ⟧₀)
    (λ ())
    public

  -- At width 2 the S of semi-Ex-S↑ is on wire 1 on the left and on
  -- wire 0 on the right.
  semi-Ex-S↑-independent :
    srel (Base.semi-Ex-S↑ {0}) IndependentOf semi-Ex-S↑
  semi-Ex-S↑-independent = independent (srel Base.semi-Ex-S↑) λ ()
