{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The Paper-V0 calculus at Paper-V0's own rules.
--
-- The calculus itself is relation-agnostic and lives in Lemmas/, stated
-- over any family of relations with the rules each part uses, in
-- dependency order:
--
--   OneWire    multiplier arithmetic, the Paulis, group-likeness, and
--              Pauli conjugation by H
--   TwoWire    the Ex-conjugation algebra; from it the two
--              Pauli-versus-CZ rules, Simplified-V1's lower-wire rules,
--              and Selinger's c10 and c11
--   ThreeWire  the remote CZ, yang-baxter and cz-slide as theorems, and
--              Selinger's c12–c15
--
-- This module instantiates them at Paper-V0's relation, each rule passed
-- as the axiom it is, under the names Iso.agda uses.  Of Paper-V0's
-- sixteen axioms the calculus uses twelve: order-SH, yang-baxter and
-- cz-slide not at all, and semi-MR only for One-Wire.lemma-semi-MR,
-- which Iso needs.
------------------------------------------------------------------------

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Notations
import Presentation.Base as PB
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
open import ForStdlib.Data.Fin.Mod

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen
open Clifford-Relations

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas.OneWire
  p-3 p-prime g* g-gen as OW
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas.TwoWire
  p-3 p-prime g* g-gen as TW
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas.ThreeWire
  p-3 p-prime g* g-gen as TH

open OW public using (lemma-pow-mod)

------------------------------------------------------------------------
-- Paper-V0's rules, as the calculus takes them

private
  two-wire-rules : TW.Two-Wire-Rules _QRel,_===_
  two-wire-rules = record
    { order-S     = PB.axiom order-S
    ; order-H     = PB.axiom order-H
    ; M-power     = λ k → PB.axiom (M-power k)
    ; comm-HHSHHS = PB.axiom comm-HHSHHS
    ; order-CZ    = PB.axiom order-CZ
    ; order-Ex    = PB.axiom order-Ex
    ; comm-CZ-S↑  = PB.axiom comm-CZ-S↑
    ; semi-M↑CZ   = PB.axiom semi-M↑CZ
    ; semi-Ex-S↑  = PB.axiom semi-Ex-S↑
    ; semi-Ex-H↑  = PB.axiom semi-Ex-H↑
    ; blake-c12   = PB.axiom blake-c12
    ; comm₁       = λ h x → PB.axiom (comm₁ h x)
    ; lemma-cong↑ = lemma-cong↑
    }

  three-wire-rules : TH.Three-Wire-Rules _QRel,_===_
  three-wire-rules = record
    { two-wire     = two-wire-rules
    ; semi-CX↑-CZ↓ = PB.axiom semi-CX↑-CZ↓
    ; comm₂        = λ h x → PB.axiom (comm₂ h x)
    }

------------------------------------------------------------------------
-- The one-wire layer, with semi-MR

module One-Wire (n : ℕ) where

  open OW.One-Wire n ((₁₊ n) QRel,_===_)
    (TW.Two-Wire-Rules-At.one-wire two-wire-rules) public
  open OW.One-Wire-MR n ((₁₊ n) QRel,_===_)
    (TW.Two-Wire-Rules-At.one-wire two-wire-rules) (PB.axiom semi-MR) public

------------------------------------------------------------------------
-- Everything else, at every width

open TH.Three-Wire-Calculus _QRel,_===_ three-wire-rules
  public using ( module Paper-GroupLike ; module One-Wire-Group
               ; module Ex-Conjugation ; module Down-Rules
               ; module Three-Wire )
