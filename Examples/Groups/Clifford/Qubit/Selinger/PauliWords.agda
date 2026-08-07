------------------------------------------------------------------------
-- Presentations of groups
--
-- The word calculus of the derived Pauli operators X = HS²H and Z = S²
-- inside Selinger's Figure 8 modulo the global scalar.
--
-- Everything here lives purely on the Figure-8 side: no Pauli generators,
-- no extension presentation.  These are the facts Qubit.Selinger.Iso
-- needs in order to check that the Pauli relations survive translation:
--
--   * X and Z square to the identity;
--   * X and Z commute on one wire — the one place C4 is needed, since
--     they anticommute in the exact group;
--   * X and Z commute with anything on higher wires.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger.PauliWords where

open import Data.Nat using (ℕ)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot using (p-2 ; p-prime)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; SympGate ; gate₁ ; H-gate ; S-gate ; _↑ ; H ; S)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime as MS
open MS using (X ; Z ; SH ; _CRel,_===_ ; srel ; comm₁)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Pauli words square to the identity

Z²≈ε : PB._≈_ ((₁₊ n) CRel,_===_) (Z • Z) ε
Z²≈ε = PB.trans PB.assoc (PB.axiom (srel MS.c3))

-- X² = HS²H·HS²H: the middle H² cancels by C2, leaving S⁴ = ε by C3 and
-- then a final H² = ε.
X²≈ε : PB._≈_ ((₁₊ n) CRel,_===_) (X • X) ε
X²≈ε = PB.trans PB.assoc
         (PB.trans (PB.cong PB.refl inner) (PB.axiom (srel MS.c2)))
  where
  inner : PB._≈_ ((₁₊ _) CRel,_===_) ((S ^ 2 • H) • X) H
  inner =
    PB.trans PB.assoc
      (PB.trans (PB.cong PB.refl
                  (PB.trans (PB.sym PB.assoc)
                    (PB.trans (PB.cong (PB.axiom (srel MS.c2)) PB.refl)
                              PB.left-unit)))
        (PB.trans (PB.sym PB.assoc)
          (PB.trans (PB.cong Z²≈ε PB.refl) PB.left-unit)))

------------------------------------------------------------------------
-- X and Z commute on one wire
--
-- They anticommute in the exact group, and commute only modulo the
-- scalar: this is the one place C4 is needed, and the reason exact
-- Figure 8 would not do here.  The route is
--
--   C4 ⟹ SHSHS = H ⟹ HSHS = S³H ⟹ HSH = S³HS³ ⟹ X = S³XS³
--      ⟹ X = ZXZ ⟹ ZX = XZ,
--
-- each step being "multiply through and cancel with C2 or C3", with the
-- rebracketing left to by-assoc.

module XZ (m : ℕ) where

  private Γ = (₁₊ m) CRel,_===_
  open PB Γ
  open PP Γ using (by-assoc ; word-setoid)
  open SR word-setoid

  -- SHSHSH = ε with the last H cancelled by C2.
  step1 : (S • H • S • H • S) ≈ H
  step1 = begin
    S • H • S • H • S              ≈⟨ sym right-unit ⟩
    (S • H • S • H • S) • ε        ≈⟨ cong refl (sym (axiom (srel MS.c2))) ⟩
    (S • H • S • H • S) • (H • H)  ≈⟨ by-assoc auto ⟩
    (SH ^ 3) • H                   ≈⟨ cong (axiom (srel MS.c4)) refl ⟩
    ε • H                          ≈⟨ left-unit ⟩
    H                              ∎

  -- Multiply step1 on the left by S³ and cancel S⁴ by C3.
  step2 : (H • S • H • S) ≈ (S • S • S • H)
  step2 = begin
    H • S • H • S                          ≈⟨ sym left-unit ⟩
    ε • (H • S • H • S)                    ≈⟨ cong (sym (axiom (srel MS.c3))) refl ⟩
    (S ^ 4) • (H • S • H • S)              ≈⟨ by-assoc auto ⟩
    (S • S • S) • (S • H • S • H • S)      ≈⟨ cong refl step1 ⟩
    (S • S • S) • H                        ≈⟨ by-assoc auto ⟩
    S • S • S • H                          ∎

  -- Multiply step2 on the right by S³ and cancel S⁴ by C3.
  step3 : (H • S • H) ≈ (S • S • S • H • S • S • S)
  step3 = begin
    H • S • H                              ≈⟨ sym right-unit ⟩
    (H • S • H) • ε                        ≈⟨ cong refl (sym (axiom (srel MS.c3))) ⟩
    (H • S • H) • (S ^ 4)                  ≈⟨ by-assoc auto ⟩
    (H • S • H • S) • (S • S • S)          ≈⟨ cong step2 refl ⟩
    (S • S • S • H) • (S • S • S)          ≈⟨ by-assoc auto ⟩
    S • S • S • H • S • S • S              ∎

  -- X = HSSH = (HSH)(HSH), the middle H² cancelling by C2.
  step4 : ((H • S • H) • (H • S • H)) ≈ X
  step4 = begin
    (H • S • H) • (H • S • H)              ≈⟨ by-assoc auto ⟩
    (H • S) • ((H • H) • (S • H))          ≈⟨ cong refl (cong (axiom (srel MS.c2)) refl) ⟩
    (H • S) • (ε • (S • H))                ≈⟨ cong refl left-unit ⟩
    (H • S) • (S • H)                      ≈⟨ by-assoc auto ⟩
    X                                      ∎

  -- Substituting step3 twice, the inner S⁶ drops to S² by C3.
  step5 : X ≈ ((S • S • S) • X • (S • S • S))
  step5 = begin
    X
      ≈⟨ sym step4 ⟩
    (H • S • H) • (H • S • H)
      ≈⟨ cong step3 step3 ⟩
    (S • S • S • H • S • S • S) • (S • S • S • H • S • S • S)
      ≈⟨ by-assoc auto ⟩
    ((S • S • S) • H) • ((S ^ 4) • ((S • S) • (H • (S • S • S))))
      ≈⟨ cong refl (cong (axiom (srel MS.c3)) refl) ⟩
    ((S • S • S) • H) • (ε • ((S • S) • (H • (S • S • S))))
      ≈⟨ cong refl left-unit ⟩
    ((S • S • S) • H) • ((S • S) • (H • (S • S • S)))
      ≈⟨ by-assoc auto ⟩
    (S • S • S) • X • (S • S • S)
      ∎

  -- Applying step5 twice gives S⁶ on each side, i.e. Z on each side.
  step6 : X ≈ (Z • X • Z)
  step6 = begin
    X
      ≈⟨ step5 ⟩
    (S • S • S) • X • (S • S • S)
      ≈⟨ cong refl (cong step5 refl) ⟩
    (S • S • S) • ((S • S • S) • X • (S • S • S)) • (S • S • S)
      ≈⟨ by-assoc auto ⟩
    (S • S) • ((S ^ 4) • (X • ((S ^ 4) • (S • S))))
      ≈⟨ cong refl (cong (axiom (srel MS.c3)) refl) ⟩
    (S • S) • (ε • (X • ((S ^ 4) • (S • S))))
      ≈⟨ cong refl left-unit ⟩
    (S • S) • (X • ((S ^ 4) • (S • S)))
      ≈⟨ cong refl (cong refl (cong (axiom (srel MS.c3)) refl)) ⟩
    (S • S) • (X • (ε • (S • S)))
      ≈⟨ cong refl (cong refl left-unit) ⟩
    (S • S) • (X • (S • S))
      ≈⟨ by-assoc auto ⟩
    Z • X • Z
      ∎

  -- Hence ZX = XZ, using Z² = ε.
  XZ≈ZX : (X • Z) ≈ (Z • X)
  XZ≈ZX = begin
    X • Z              ≈⟨ cong step6 refl ⟩
    (Z • X • Z) • Z    ≈⟨ by-assoc auto ⟩
    Z • X • (Z • Z)    ≈⟨ cong refl (cong refl Z²≈ε) ⟩
    Z • X • ε          ≈⟨ cong refl right-unit ⟩
    Z • X              ∎

------------------------------------------------------------------------
-- Pauli words on disjoint wires commute
--
-- X and Z are words over bottom 1-ary gates, so they commute with any
-- shifted word by comm₁ lifted from generators to words.

module ↑Comm (m : ℕ) where

  private Γ = (₁₊ m) CRel,_===_
  open PB Γ

  ↑-comm-gen : (v : Word (Gen m)) (h : SympGate 1) →
               ((v ↑) • [ gate₁ h ]ʷ) ≈ ([ gate₁ h ]ʷ • (v ↑))
  ↑-comm-gen [ gg ]ʷ h = axiom (comm₁ h gg)
  ↑-comm-gen ε       h = trans left-unit (sym right-unit)
  ↑-comm-gen (u • w) h =
    trans assoc
      (trans (cong refl (↑-comm-gen w h))
        (trans (sym assoc)
          (trans (cong (↑-comm-gen u h) refl) assoc)))

  -- Commuting past a product, given both factors.
  ↑-comm-• : ∀ {a b} (v : Word (Gen m)) →
             ((v ↑) • a) ≈ (a • (v ↑)) → ((v ↑) • b) ≈ (b • (v ↑)) →
             ((v ↑) • (a • b)) ≈ ((a • b) • (v ↑))
  ↑-comm-• v pa pb =
    trans (sym assoc)
      (trans (cong pa refl)
        (trans assoc (trans (cong refl pb) (sym assoc))))

  ↑-comm-Z : (v : Word (Gen m)) → ((v ↑) • Z) ≈ (Z • (v ↑))
  ↑-comm-Z v = ↑-comm-• v (↑-comm-gen v S-gate) (↑-comm-gen v S-gate)

  -- X = H • (Z • H).
  ↑-comm-X : (v : Word (Gen m)) → ((v ↑) • X) ≈ (X • (v ↑))
  ↑-comm-X v =
    ↑-comm-• v (↑-comm-gen v H-gate)
      (↑-comm-• v (↑-comm-Z v) (↑-comm-gen v H-gate))
