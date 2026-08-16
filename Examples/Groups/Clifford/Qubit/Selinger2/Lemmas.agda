------------------------------------------------------------------------
-- Presentations of groups
--
-- The derived rules of Selinger's supplement, Lemmas 1.1-1.3
-- (arXiv:1310.6813, ancillary file clifford-supplement.pdf), proved
-- from Figure 8.
--
-- These are the rules the supplement's Section 3 proofs are written in:
-- every one of the ninety-nine rewrite equations of Figures 3-7 is
-- derived from Figure 8 through them, so they are the layer that has to
-- exist before those rules can be replayed.  The numbering is the
-- supplement's, and the name each rule carries in the machine-readable
-- proof file is given alongside, since that is what a replay looks up.
--
--   Lemma 1.1, one qubit, from Figure 8(a)-(b)          (1)-(10)
--   Lemma 1.2, two qubits, from Figure 8(a)-(c)         (11)-(18)
--   Lemma 1.3, three qubits, from Figure 8(a)-(d)       (19)-(21)
--
-- Lemma 1.2 and 1.3 are each stated "as well as its upside-down
-- version"; where Figure 8 supplies both halves as separate axioms
-- (C6/C7, C10/C11) both are recorded here.
--
-- Word order is the circuit order of the paper, and the scalar is
-- written on the right as Selinger writes it.  ω is central (Figure8's
-- ω-central, itself Circuit.Base's comm₀ walked across a word), so
-- moving it there is never more than one step.  ω⁻¹ is spelled ω ^ 7,
-- which by (1) is the same element.
--
-- The rebracketing between steps is by-assoc, which compares flattened
-- generator lists and so is Eq.refl throughout; only the steps that name
-- a rule do any work.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger2.Lemmas where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Groups.Clifford.Qubit.Selinger2.Figure8
open import Examples.Groups.Clifford.Qubit.Selinger2.Wires using (comm-bot)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Lemma 1.1 — one qubit
--
-- Ten identities in H, S and the scalar, from ω⁸ = 1, H² = 1, S⁴ = 1 and
-- SHSHSH = ω alone.  Each proof is the supplement's, step for step.

module OneQubit {n : ℕ} where

  private
    Γ = (₁₊ n) CRel,_===_

  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  -- An axiom of Figure 8 at this width, flattened.
  ax : ∀ {w v a b} → (₁₊ n) Sel, a === b →
       Assoc.to-list Γ w ≡ Assoc.to-list Γ a →
       Assoc.to-list Γ b ≡ Assoc.to-list Γ v → w ≈ v
  ax r = by-assoc-and (axiom (srel r))

  ------------------------------------------------------------------
  -- (1)-(3): the axioms C1-C3.

  -- (1)  ω⁸ = 1                                       [supplement: omega]
  ω⁸ : ω ^ 8 ≈ ε
  ω⁸ = axiom (srel c1)

  -- (2)  HH = 1                                       [supplement: HH]
  HH : H • H ≈ ε
  HH = ax c2 Eq.refl Eq.refl

  -- (3)  SSSS = 1                                     [supplement: SSSS]
  SSSS : S • S • S • S ≈ ε
  SSSS = ax c3 Eq.refl Eq.refl

  -- C4 flattened.  Not one of the numbered properties, but the form the
  -- chains below use.
  SHSHSH : S • H • S • H • S • H ≈ ω
  SHSHSH = ax c4 Eq.refl Eq.refl

  ------------------------------------------------------------------
  -- (4)  SHSH = HSSS · ω                              [supplement: HSHS]
  --
  --   SHSH = SHSH·SSSS = SHSH·SH·HSSS = ω·HSSS = HSSS·ω.

  SHSH : S • H • S • H ≈ H • S • S • S • ω
  SHSH = begin
    S • H • S • H
      ≈⟨ right-unit reversed ⟩
    (S • H • S • H) • ε
      ≈⟨ cright SSSS reversed ⟩
    (S • H • S • H) • (S • S • S • S)
      ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S • H • S) • ε • (S • S • S)
      ≈⟨ cright cleft HH reversed ⟩
    (S • H • S • H • S) • (H • H) • (S • S • S)
      ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S • H • S • H) • (H • S • S • S)
      ≈⟨ cleft SHSHSH ⟩
    ω • (H • S • S • S)
      ≈⟨ ω-central (H • S • S • S) ⟩
    (H • S • S • S) • ω
      ≈⟨ by-assoc Eq.refl ⟩
    H • S • S • S • ω ∎

  ------------------------------------------------------------------
  -- (5)  HSHS = SSSH · ω                              [supplement: SHSH]
  --
  --   HSHS = HSHS·HH = H·(SHSH)·H = H·HSSS·ω·H = SSSH·ω.

  HSHS : H • S • H • S ≈ S • S • S • H • ω
  HSHS = begin
    H • S • H • S
      ≈⟨ right-unit reversed ⟩
    (H • S • H • S) • ε
      ≈⟨ cright HH reversed ⟩
    (H • S • H • S) • (H • H)
      ≈⟨ by-assoc Eq.refl ⟩
    H • (S • H • S • H) • H
      ≈⟨ cright cleft SHSH ⟩
    H • (H • S • S • S • ω) • H
      ≈⟨ by-assoc Eq.refl ⟩
    (H • H) • (S • S • S) • ω • H
      ≈⟨ cleft HH ⟩
    ε • (S • S • S) • ω • H
      ≈⟨ left-unit ⟩
    (S • S • S) • ω • H
      ≈⟨ cright ω-central H ⟩
    (S • S • S) • H • ω
      ≈⟨ by-assoc Eq.refl ⟩
    S • S • S • H • ω ∎

  ------------------------------------------------------------------
  -- (4) read backwards.  Multiplying SHSH = HSSS·ω by ω⁷ on the right
  -- and cancelling ω⁸ gives HSSS = SHSH·ω⁷, which is what (6) and (10)
  -- actually use.

  HSSS : H • S • S • S ≈ S • H • S • H • ω ^ 7
  HSSS = begin
    H • S • S • S
      ≈⟨ right-unit reversed ⟩
    (H • S • S • S) • ε
      ≈⟨ cright ω⁸ reversed ⟩
    (H • S • S • S) • ω ^ 8
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S • S • S • ω) • ω ^ 7
      ≈⟨ cleft SHSH reversed ⟩
    (S • H • S • H) • ω ^ 7
      ≈⟨ by-assoc Eq.refl ⟩
    S • H • S • H • ω ^ 7 ∎

  ------------------------------------------------------------------
  -- (6)  HSSSH = SHS · ω⁻¹                           [supplement: HSSSH]

  HSSSH : H • S • S • S • H ≈ S • H • S • ω ^ 7
  HSSSH = begin
    H • S • S • S • H
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S • S • S) • H
      ≈⟨ cleft HSSS ⟩
    (S • H • S • H • ω ^ 7) • H
      ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S • H) • (ω ^ 7 • H)
      ≈⟨ cright ω^-central 7 H ⟩
    (S • H • S • H) • (H • ω ^ 7)
      ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S) • (H • H) • ω ^ 7
      ≈⟨ cright cleft HH ⟩
    (S • H • S) • ε • ω ^ 7
      ≈⟨ by-assoc Eq.refl ⟩
    S • H • S • ω ^ 7 ∎

  -- (6) read backwards, in the form (7) and (8) use.
  SHS : S • H • S ≈ H • S • S • S • H • ω
  SHS = begin
    S • H • S
      ≈⟨ right-unit reversed ⟩
    (S • H • S) • ε
      ≈⟨ cright ω⁸ reversed ⟩
    (S • H • S) • ω ^ 8
      ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S • ω ^ 7) • ω
      ≈⟨ cleft HSSSH reversed ⟩
    (H • S • S • S • H) • ω
      ≈⟨ by-assoc Eq.refl ⟩
    H • S • S • S • H • ω ∎

  ------------------------------------------------------------------
  -- (7)  SHSSHS = HSSH · ω²                         [supplement: SHSSHS]
  --
  --   SHSSHS = (SHS)(SHS) = HSSSH·HSSSH·ω² = HSSSSSSH·ω² = HSSH·ω².

  SHSSHS : S • H • S • S • H • S ≈ H • S • S • H • ω ^ 2
  SHSSHS = begin
    S • H • S • S • H • S
      ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S) • (S • H • S)
      ≈⟨ cong SHS SHS ⟩
    (H • S • S • S • H • ω) • (H • S • S • S • H • ω)
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S • S • S • H) • (ω • (H • S • S • S • H • ω))
      ≈⟨ cright ω-central (H • S • S • S • H • ω) ⟩
    (H • S • S • S • H) • ((H • S • S • S • H • ω) • ω)
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S • S • S) • (H • H) • (S • S • S • H • ω • ω)
      ≈⟨ cright cleft HH ⟩
    (H • S • S • S) • ε • (S • S • S • H • ω • ω)
      ≈⟨ by-assoc Eq.refl ⟩
    H • (S • S • S • S) • (S • S • H • ω • ω)
      ≈⟨ cright cleft SSSS ⟩
    H • ε • (S • S • H • ω • ω)
      ≈⟨ by-assoc Eq.refl ⟩
    H • S • S • H • ω ^ 2 ∎

  ------------------------------------------------------------------
  -- (8)  HSSHSS = SSHSSH · ω⁴                       [supplement: HSSHSS]
  --
  --   HSSHSS =(6) HSHSSSHS·ω =(5) SSSHSSHS·ω² =(7) SSHSSH·ω⁴.

  HSSHSS : H • S • S • H • S • S ≈ S • S • H • S • S • H • ω ^ 4
  HSSHSS = begin
    H • S • S • H • S • S
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S) • (S • H • S) • S
      ≈⟨ cright cleft SHS ⟩
    (H • S) • (H • S • S • S • H • ω) • S
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S • H • S • S • S • H) • (ω • S)
      ≈⟨ cright ω-central S ⟩
    (H • S • H • S • S • S • H) • (S • ω)
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S • H • S) • (S • S • H • S • ω)
      ≈⟨ cleft HSHS ⟩
    (S • S • S • H • ω) • (S • S • H • S • ω)
      ≈⟨ by-assoc Eq.refl ⟩
    (S • S • S • H) • (ω • (S • S • H • S • ω))
      ≈⟨ cright ω-central (S • S • H • S • ω) ⟩
    (S • S • S • H) • ((S • S • H • S • ω) • ω)
      ≈⟨ by-assoc Eq.refl ⟩
    (S • S) • (S • H • S • S • H • S) • ω ^ 2
      ≈⟨ cright cleft SHSSHS ⟩
    (S • S) • (H • S • S • H • ω ^ 2) • ω ^ 2
      ≈⟨ by-assoc Eq.refl ⟩
    S • S • H • S • S • H • ω ^ 4 ∎

  ------------------------------------------------------------------
  -- (5) read backwards, as (9) uses it.

  SSSH : S • S • S • H ≈ H • S • H • S • ω ^ 7
  SSSH = begin
    S • S • S • H
      ≈⟨ right-unit reversed ⟩
    (S • S • S • H) • ε
      ≈⟨ cright ω⁸ reversed ⟩
    (S • S • S • H) • ω ^ 8
      ≈⟨ by-assoc Eq.refl ⟩
    (S • S • S • H • ω) • ω ^ 7
      ≈⟨ cleft HSHS reversed ⟩
    (H • S • H • S) • ω ^ 7
      ≈⟨ by-assoc Eq.refl ⟩
    H • S • H • S • ω ^ 7 ∎

  ------------------------------------------------------------------
  -- (9)  SSSHSSH = HSSHS · ω⁻²                     [supplement: SSSHSSH]
  --
  --   SSSHSSH =(5) HSHSSSH·ω⁻¹ =(5) HSHHSHS·ω⁻² =(2) HSSHS·ω⁻².

  SSSHSSH : S • S • S • H • S • S • H ≈ H • S • S • H • S • ω ^ 6
  SSSHSSH = begin
    S • S • S • H • S • S • H
      ≈⟨ by-assoc Eq.refl ⟩
    (S • S • S • H) • (S • S • H)
      ≈⟨ cleft SSSH ⟩
    (H • S • H • S • ω ^ 7) • (S • S • H)
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S • H • S) • (ω ^ 7 • (S • S • H))
      ≈⟨ cright ω^-central 7 (S • S • H) ⟩
    (H • S • H • S) • ((S • S • H) • ω ^ 7)
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S • H) • (S • S • S • H) • ω ^ 7
      ≈⟨ cright cleft SSSH ⟩
    (H • S • H) • (H • S • H • S • ω ^ 7) • ω ^ 7
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S) • (H • H) • (S • H • S • ω ^ 14)
      ≈⟨ cright cleft HH ⟩
    (H • S) • ε • (S • H • S • ω ^ 14)
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S • S • H • S) • ω ^ 8 • ω ^ 6
      ≈⟨ cright cleft ω⁸ ⟩
    (H • S • S • H • S) • ε • ω ^ 6
      ≈⟨ by-assoc Eq.refl ⟩
    H • S • S • H • S • ω ^ 6 ∎

  ------------------------------------------------------------------
  -- (10)  SSSHSSS = HSH · ω⁻¹                      [supplement: SSSHSSS]
  --
  --   SSSHSSS =(4) SSSSHSH·ω⁻¹ =(3) HSH·ω⁻¹.

  SSSHSSS : S • S • S • H • S • S • S ≈ H • S • H • ω ^ 7
  SSSHSSS = begin
    S • S • S • H • S • S • S
      ≈⟨ by-assoc Eq.refl ⟩
    (S • S • S) • (H • S • S • S)
      ≈⟨ cright HSSS ⟩
    (S • S • S) • (S • H • S • H • ω ^ 7)
      ≈⟨ by-assoc Eq.refl ⟩
    (S • S • S • S) • (H • S • H • ω ^ 7)
      ≈⟨ cleft SSSS ⟩
    ε • (H • S • H • ω ^ 7)
      ≈⟨ left-unit ⟩
    H • S • H • ω ^ 7 ∎

  -- (10) read backwards, as the two-qubit rule (15) uses it.
  HSH : H • S • H ≈ S • S • S • H • S • S • S • ω
  HSH = begin
    H • S • H
      ≈⟨ right-unit reversed ⟩
    (H • S • H) • ε
      ≈⟨ cright ω⁸ reversed ⟩
    (H • S • H) • ω ^ 8
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S • H • ω ^ 7) • ω
      ≈⟨ cleft SSSHSSS reversed ⟩
    (S • S • S • H • S • S • S) • ω
      ≈⟨ by-assoc Eq.refl ⟩
    S • S • S • H • S • S • S • ω ∎

  ------------------------------------------------------------------
  -- The wire-0 identity that closes (15): two uses of HSSS and one HH.
  --
  --   HSSHSSS = HSS·(HSSS) = (HSSS)HSH·ω⁷ = SHSHHSH·ω¹⁴ = SHSSH·ω⁶.

  -- The wire-1 identity that closes (16): one use of (5) and one of (3).
  HSSHSHS : H • S • S • H • S • H • S ≈ H • S • H • ω
  HSSHSHS = begin
    H • S • S • H • S • H • S
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S • S) • (H • S • H • S)
      ≈⟨ cright HSHS ⟩
    (H • S • S) • (S • S • S • H • ω)
      ≈⟨ by-assoc Eq.refl ⟩
    H • (S • S • S • S) • (S • H • ω)
      ≈⟨ cright cleft SSSS ⟩
    H • ε • (S • H • ω)
      ≈⟨ by-assoc Eq.refl ⟩
    H • S • H • ω ∎

  HSSHSSS : H • S • S • H • S • S • S ≈ S • H • S • S • H • ω ^ 6
  HSSHSSS = begin
    H • S • S • H • S • S • S
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S • S) • (H • S • S • S)
      ≈⟨ cright HSSS ⟩
    (H • S • S) • (S • H • S • H • ω ^ 7)
      ≈⟨ by-assoc Eq.refl ⟩
    (H • S • S • S) • (H • S • H • ω ^ 7)
      ≈⟨ cleft HSSS ⟩
    (S • H • S • H • ω ^ 7) • (H • S • H • ω ^ 7)
      ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S • H) • (ω ^ 7 • (H • S • H • ω ^ 7))
      ≈⟨ cright ω^-central 7 (H • S • H • ω ^ 7) ⟩
    (S • H • S • H) • ((H • S • H • ω ^ 7) • ω ^ 7)
      ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S) • (H • H) • (S • H • ω ^ 14)
      ≈⟨ cright cleft HH ⟩
    (S • H • S) • ε • (S • H • ω ^ 14)
      ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S • S • H) • ω ^ 8 • ω ^ 6
      ≈⟨ cright cleft ω⁸ ⟩
    (S • H • S • S • H) • ε • ω ^ 6
      ≈⟨ by-assoc Eq.refl ⟩
    S • H • S • S • H • ω ^ 6 ∎

------------------------------------------------------------------------
-- Lemma 1.2 — two qubits
--
-- Four of the eight are Figure 8 axioms outright, flattened: (11) is C5,
-- (12) is C6 and its upside-down version C7, and (13) is C11 with C10
-- upside down.  The remaining four, (14)-(18), are derived in the
-- supplement's Section 2 and are not yet here.

module TwoQubit {n : ℕ} where

  private
    Γ = (₂₊ n) CRel,_===_

  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  -- (11)  CZ·CZ = 1                                   [supplement: ZZZZ]
  ZZZZ : CZ • CZ ≈ ε
  ZZZZ = axiom (srel c5)

  -- (12)  S·CZ = CZ·S, on the lower wire and on the upper
  --                                                    [supplement: SZZ]
  SZZ : S ↓ • CZ ≈ CZ • S ↓
  SZZ = axiom (srel c6)

  SZZ↑ : S ↑ • CZ ≈ CZ • S ↑
  SZZ↑ = axiom (srel c7)

  -- (13)  CZ·H·CZ = SH·CZ·SHS·S↑·ω⁻¹, and upside down
  --                                                  [supplement: ZZHZZ]
  ZZHZZ : CZ • H ↓ • CZ ≈ S ↓ • H ↓ • CZ • S ↓ • H ↓ • S ↓ • S ↑ • ω ^ 7
  ZZHZZ = by-assoc-and (axiom (srel c11)) Eq.refl Eq.refl

  ZZHZZ↑ : CZ • H ↑ • CZ ≈ S ↑ • H ↑ • CZ • S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7
  ZZHZZ↑ = by-assoc-and (axiom (srel c10)) Eq.refl Eq.refl

  -- C8 and C9 flattened: the Pauli X of §4 through a controlled-Z.
  private
    XZZ : H ↓ • S ↓ • S ↓ • H ↓ • CZ ≈
          CZ • H ↓ • S ↓ • S ↓ • H ↓ • S ↑ • S ↑
    XZZ = by-assoc-and (axiom (srel c8)) Eq.refl Eq.refl

    XZZ↑ : H ↑ • S ↑ • S ↑ • H ↑ • CZ ≈
           CZ • H ↑ • S ↑ • S ↑ • H ↑ • S ↓ • S ↓
    XZZ↑ = by-assoc-and (axiom (srel c9)) Eq.refl Eq.refl

  ------------------------------------------------------------------
  -- (14)  SSH·CZ = H·CZ·HSSH·S↑S↑, and upside down  [supplement: SSHZZ]
  --
  --   SSH·CZ = HH·SSH·CZ = H·(X·CZ) = H·CZ·X·Z↑, by (2) and C8.

  SSHZZ : S ↓ • S ↓ • H ↓ • CZ ≈
          H ↓ • CZ • H ↓ • S ↓ • S ↓ • H ↓ • S ↑ • S ↑
  SSHZZ = begin
    S ↓ • S ↓ • H ↓ • CZ
      ≈⟨ left-unit reversed ⟩
    ε • (S ↓ • S ↓ • H ↓ • CZ)
      ≈⟨ cleft OneQubit.HH reversed ⟩
    (H ↓ • H ↓) • (S ↓ • S ↓ • H ↓ • CZ)
      ≈⟨ by-assoc Eq.refl ⟩
    H ↓ • (H ↓ • S ↓ • S ↓ • H ↓ • CZ)
      ≈⟨ cright XZZ ⟩
    H ↓ • (CZ • H ↓ • S ↓ • S ↓ • H ↓ • S ↑ • S ↑)
      ≈⟨ by-assoc Eq.refl ⟩
    H ↓ • CZ • H ↓ • S ↓ • S ↓ • H ↓ • S ↑ • S ↑ ∎

  ------------------------------------------------------------------
  -- Two auxiliaries for (15).
  --
  -- Gates on the two wires commute: that is Circuit.Base's comm₁,
  -- already walked across a word by Lift-Relation's comm-gate₁-w↑, so
  -- moving S↑S↑ past a word of unshifted gates costs one step per
  -- letter and no axiom of Selinger's.

  private
    -- Z↑ = S↑S↑ past SSS on the lower wire.  One call: comm-bot walks
    -- Circuit.Base's comm₁ across the whole bottom-wire word, and both
    -- sides reduce to the products written here.
    ZZ↑SSS : (S ↑ • S ↑) • (S ↓ • S ↓ • S ↓) ≈ (S ↓ • S ↓ • S ↓) • (S ↑ • S ↑)
    ZZ↑SSS = comm-bot (S • S) ([ S-gate ]ʷ • [ S-gate ]ʷ • [ S-gate ]ʷ)

    -- (12), three times over: a controlled-Z crosses SSS on the lower
    -- wire.
    SSSZZ : S ↓ • S ↓ • S ↓ • CZ ≈ CZ • S ↓ • S ↓ • S ↓
    SSSZZ = begin
      S ↓ • S ↓ • S ↓ • CZ         ≈⟨ cright cright SZZ ⟩
      S ↓ • S ↓ • CZ • S ↓         ≈⟨ cright (assoc reversed) ⟩
      S ↓ • ((S ↓ • CZ) • S ↓)     ≈⟨ cright cleft SZZ ⟩
      S ↓ • ((CZ • S ↓) • S ↓)     ≈⟨ cright assoc ⟩
      S ↓ • (CZ • S ↓ • S ↓)       ≈⟨ assoc reversed ⟩
      (S ↓ • CZ) • (S ↓ • S ↓)     ≈⟨ cleft SZZ ⟩
      (CZ • S ↓) • (S ↓ • S ↓)     ≈⟨ assoc ⟩
      CZ • S ↓ • S ↓ • S ↓ ∎

  ------------------------------------------------------------------
  -- (15)  HSH·CZ = SH·CZ·SHSSH·S↑S↑·ω⁻¹              [supplement: HSHZZ]
  --
  --   HSH·CZ =(10) SSSHSSS·CZ·ω =(12) SSSH·CZ·SSS·ω
  --          =(14) SH·CZ·HSSHSSS·S↑S↑·ω =(4),(4),(2) SH·CZ·SHSSH·S↑S↑·ω⁻¹.

  HSHZZ : H ↓ • S ↓ • H ↓ • CZ ≈
          S ↓ • H ↓ • CZ • S ↓ • H ↓ • S ↓ • S ↓ • H ↓ • S ↑ • S ↑ • ω ^ 7
  HSHZZ = begin
    H ↓ • S ↓ • H ↓ • CZ
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • S ↓ • H ↓) • CZ
      ≈⟨ cleft OneQubit.HSH ⟩
    (S ↓ • S ↓ • S ↓ • H ↓ • S ↓ • S ↓ • S ↓ • ω) • CZ
      ≈⟨ by-assoc Eq.refl ⟩
    (S ↓ • S ↓ • S ↓ • H ↓) • ((S ↓ • S ↓ • S ↓) • (ω • CZ))
      ≈⟨ cright cright ω-central CZ ⟩
    (S ↓ • S ↓ • S ↓ • H ↓) • ((S ↓ • S ↓ • S ↓) • (CZ • ω))
      ≈⟨ by-assoc Eq.refl ⟩
    (S ↓ • S ↓ • S ↓ • H ↓) • ((S ↓ • S ↓ • S ↓ • CZ) • ω)
      ≈⟨ cright cleft SSSZZ ⟩
    (S ↓ • S ↓ • S ↓ • H ↓) • ((CZ • S ↓ • S ↓ • S ↓) • ω)
      ≈⟨ by-assoc Eq.refl ⟩
    S ↓ • ((S ↓ • S ↓ • H ↓ • CZ) • ((S ↓ • S ↓ • S ↓) • ω))
      ≈⟨ cright cleft SSHZZ ⟩
    S ↓ • ((H ↓ • CZ • H ↓ • S ↓ • S ↓ • H ↓ • S ↑ • S ↑)
             • ((S ↓ • S ↓ • S ↓) • ω))
      ≈⟨ by-assoc Eq.refl ⟩
    (S ↓ • H ↓ • CZ • H ↓ • S ↓ • S ↓ • H ↓)
      • ((S ↑ • S ↑) • (S ↓ • S ↓ • S ↓)) • ω
      ≈⟨ cright cleft ZZ↑SSS ⟩
    (S ↓ • H ↓ • CZ • H ↓ • S ↓ • S ↓ • H ↓)
      • ((S ↓ • S ↓ • S ↓) • (S ↑ • S ↑)) • ω
      ≈⟨ by-assoc Eq.refl ⟩
    (S ↓ • H ↓ • CZ) • (H ↓ • S ↓ • S ↓ • H ↓ • S ↓ • S ↓ • S ↓)
      • (S ↑ • S ↑ • ω)
      ≈⟨ cright cleft OneQubit.HSSHSSS ⟩
    (S ↓ • H ↓ • CZ) • (S ↓ • H ↓ • S ↓ • S ↓ • H ↓ • ω ^ 6)
      • (S ↑ • S ↑ • ω)
      ≈⟨ by-assoc Eq.refl ⟩
    (S ↓ • H ↓ • CZ • S ↓ • H ↓ • S ↓ • S ↓ • H ↓)
      • (ω ^ 6 • (S ↑ • S ↑)) • ω
      ≈⟨ cright cleft ω^-central 6 (S ↑ • S ↑) ⟩
    (S ↓ • H ↓ • CZ • S ↓ • H ↓ • S ↓ • S ↓ • H ↓)
      • ((S ↑ • S ↑) • ω ^ 6) • ω
      ≈⟨ by-assoc Eq.refl ⟩
    S ↓ • H ↓ • CZ • S ↓ • H ↓ • S ↓ • S ↓ • H ↓ • S ↑ • S ↑ • ω ^ 7 ∎

  SSHZZ↑ : S ↑ • S ↑ • H ↑ • CZ ≈
           H ↑ • CZ • H ↑ • S ↑ • S ↑ • H ↑ • S ↓ • S ↓
  SSHZZ↑ = begin
    S ↑ • S ↑ • H ↑ • CZ
      ≈⟨ left-unit reversed ⟩
    ε • (S ↑ • S ↑ • H ↑ • CZ)
      ≈⟨ cleft (lemma-cong↑ (H • H) ε OneQubit.HH) reversed ⟩
    (H ↑ • H ↑) • (S ↑ • S ↑ • H ↑ • CZ)
      ≈⟨ by-assoc Eq.refl ⟩
    H ↑ • (H ↑ • S ↑ • S ↑ • H ↑ • CZ)
      ≈⟨ cright XZZ↑ ⟩
    H ↑ • (CZ • H ↑ • S ↑ • S ↑ • H ↑ • S ↓ • S ↓)
      ≈⟨ by-assoc Eq.refl ⟩
    H ↑ • CZ • H ↑ • S ↑ • S ↑ • H ↑ • S ↓ • S ↓ ∎

  ------------------------------------------------------------------
  -- (16)  SH·CZ·HH·CZ = H·CZ·HH·CZ·HSH             [supplement: SHZZHHZZ]
  --
  -- The move that starts it is (11) read backwards: inserting CZ·CZ = 1
  -- exposes a CZ·H·CZ block, which (13) then spends.  That happens twice
  -- here, once on each wire, so the derivation splits cleanly into the
  -- two halves below and (16) is their composite plus three
  -- commutations.

  private
    ω⁸ : ω ^ 8 ≈ ε
    ω⁸ = axiom (srel c1)

    -- (13), then (4) on the wire-0 prefix, then (12) and (3).
    halfA : S ↓ • H ↓ • CZ • H ↓ • CZ ≈ H ↓ • CZ • H ↓ • S ↓ • S ↑
    halfA = begin
      S ↓ • H ↓ • CZ • H ↓ • CZ
        ≈⟨ by-assoc Eq.refl ⟩
      (S ↓ • H ↓) • (CZ • H ↓ • CZ)
        ≈⟨ cright ZZHZZ ⟩
      (S ↓ • H ↓) • (S ↓ • H ↓ • CZ • S ↓ • H ↓ • S ↓ • S ↑ • ω ^ 7)
        ≈⟨ by-assoc Eq.refl ⟩
      (S ↓ • H ↓ • S ↓ • H ↓) • (CZ • S ↓ • H ↓ • S ↓ • S ↑ • ω ^ 7)
        ≈⟨ cleft OneQubit.SHSH ⟩
      (H ↓ • S ↓ • S ↓ • S ↓ • ω) • (CZ • S ↓ • H ↓ • S ↓ • S ↑ • ω ^ 7)
        ≈⟨ by-assoc Eq.refl ⟩
      H ↓ • (S ↓ • S ↓ • S ↓) • (ω • (CZ • S ↓ • H ↓ • S ↓ • S ↑ • ω ^ 7))
        ≈⟨ cright cright ω-central (CZ • S ↓ • H ↓ • S ↓ • S ↑ • ω ^ 7) ⟩
      H ↓ • (S ↓ • S ↓ • S ↓) • ((CZ • S ↓ • H ↓ • S ↓ • S ↑ • ω ^ 7) • ω)
        ≈⟨ by-assoc Eq.refl ⟩
      H ↓ • ((S ↓ • S ↓ • S ↓ • CZ) • (S ↓ • H ↓ • S ↓ • S ↑ • ω ^ 8))
        ≈⟨ cright cleft SSSZZ ⟩
      H ↓ • ((CZ • S ↓ • S ↓ • S ↓) • (S ↓ • H ↓ • S ↓ • S ↑ • ω ^ 8))
        ≈⟨ by-assoc Eq.refl ⟩
      H ↓ • CZ • (S ↓ • S ↓ • S ↓ • S ↓) • (H ↓ • S ↓ • S ↑ • ω ^ 8)
        ≈⟨ cright cright cleft OneQubit.SSSS ⟩
      H ↓ • CZ • ε • (H ↓ • S ↓ • S ↑ • ω ^ 8)
        ≈⟨ by-assoc Eq.refl ⟩
      (H ↓ • CZ • H ↓ • S ↓ • S ↑) • ω ^ 8
        ≈⟨ cright ω⁸ ⟩
      (H ↓ • CZ • H ↓ • S ↓ • S ↑) • ε
        ≈⟨ right-unit ⟩
      H ↓ • CZ • H ↓ • S ↓ • S ↑ ∎

    -- (16)'s wire-1 identity, lifted from the one-qubit (5)+(3).
    HSSHSHS↑ : H ↑ • S ↑ • S ↑ • H ↑ • S ↑ • H ↑ • S ↑ ≈ H ↑ • S ↑ • H ↑ • ω
    HSSHSHS↑ = begin
      H ↑ • S ↑ • S ↑ • H ↑ • S ↑ • H ↑ • S ↑
        ≈⟨ lemma-cong↑ (H • S • S • H • S • H • S) (H • S • H • ω)
                       OneQubit.HSSHSHS ⟩
      H ↑ • S ↑ • H ↑ • ω ↑
        ≈⟨ cright cright cright ω↑≈ω ⟩
      H ↑ • S ↑ • H ↑ • ω ∎

    -- The same shape upside down: (13)↑, then (14)↑, then HSSHSHS↑.
    halfB : S ↑ • CZ • H ↑ • CZ ≈
            H ↑ • CZ • H ↑ • S ↑ • H ↑ • S ↓ • S ↓ • S ↓
    halfB = begin
      S ↑ • CZ • H ↑ • CZ
        ≈⟨ by-assoc Eq.refl ⟩
      S ↑ • (CZ • H ↑ • CZ)
        ≈⟨ cright ZZHZZ↑ ⟩
      S ↑ • (S ↑ • H ↑ • CZ • S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7)
        ≈⟨ by-assoc Eq.refl ⟩
      (S ↑ • S ↑ • H ↑ • CZ) • (S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7)
        ≈⟨ cleft SSHZZ↑ ⟩
      (H ↑ • CZ • H ↑ • S ↑ • S ↑ • H ↑ • S ↓ • S ↓)
        • (S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7)
        ≈⟨ by-assoc Eq.refl ⟩
      (H ↑ • CZ • H ↑ • S ↑ • S ↑ • H ↑)
        • ((S ↓ • S ↓) • (S ↑ • H ↑ • S ↑)) • (S ↓ • ω ^ 7)
        ≈⟨ cright cleft comm-bot (S • H • S) ([ S-gate ]ʷ • [ S-gate ]ʷ) reversed ⟩
      (H ↑ • CZ • H ↑ • S ↑ • S ↑ • H ↑)
        • ((S ↑ • H ↑ • S ↑) • (S ↓ • S ↓)) • (S ↓ • ω ^ 7)
        ≈⟨ by-assoc Eq.refl ⟩
      (H ↑ • CZ) • (H ↑ • S ↑ • S ↑ • H ↑ • S ↑ • H ↑ • S ↑)
        • (S ↓ • S ↓ • S ↓ • ω ^ 7)
        ≈⟨ cright cleft HSSHSHS↑ ⟩
      (H ↑ • CZ) • (H ↑ • S ↑ • H ↑ • ω) • (S ↓ • S ↓ • S ↓ • ω ^ 7)
        ≈⟨ by-assoc Eq.refl ⟩
      (H ↑ • CZ • H ↑ • S ↑ • H ↑) • (ω • (S ↓ • S ↓ • S ↓ • ω ^ 7))
        ≈⟨ cright ω-central (S ↓ • S ↓ • S ↓ • ω ^ 7) ⟩
      (H ↑ • CZ • H ↑ • S ↑ • H ↑) • ((S ↓ • S ↓ • S ↓ • ω ^ 7) • ω)
        ≈⟨ by-assoc Eq.refl ⟩
      (H ↑ • CZ • H ↑ • S ↑ • H ↑ • S ↓ • S ↓ • S ↓) • ω ^ 8
        ≈⟨ cright ω⁸ ⟩
      (H ↑ • CZ • H ↑ • S ↑ • H ↑ • S ↓ • S ↓ • S ↓) • ε
        ≈⟨ right-unit ⟩
      H ↑ • CZ • H ↑ • S ↑ • H ↑ • S ↓ • S ↓ • S ↓ ∎

  SHZZHHZZ : S ↓ • H ↓ • CZ • H ↓ • H ↑ • CZ ≈
             H ↓ • CZ • H ↓ • H ↑ • CZ • H ↑ • S ↑ • H ↑
  SHZZHHZZ = begin
    S ↓ • H ↓ • CZ • H ↓ • H ↑ • CZ
      ≈⟨ by-assoc Eq.refl ⟩
    (S ↓ • H ↓ • CZ • H ↓) • ε • (H ↑ • CZ)
      ≈⟨ cright cleft ZZZZ reversed ⟩
    (S ↓ • H ↓ • CZ • H ↓) • (CZ • CZ) • (H ↑ • CZ)
      ≈⟨ by-assoc Eq.refl ⟩
    (S ↓ • H ↓ • CZ • H ↓ • CZ) • (CZ • H ↑ • CZ)
      ≈⟨ cleft halfA ⟩
    (H ↓ • CZ • H ↓ • S ↓ • S ↑) • (CZ • H ↑ • CZ)
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • CZ • H ↓ • S ↓) • (S ↑ • CZ • H ↑ • CZ)
      ≈⟨ cright halfB ⟩
    (H ↓ • CZ • H ↓ • S ↓) • (H ↑ • CZ • H ↑ • S ↑ • H ↑ • S ↓ • S ↓ • S ↓)
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • CZ • H ↓) • (S ↓ • H ↑)
      • (CZ • H ↑ • S ↑ • H ↑ • S ↓ • S ↓ • S ↓)
      ≈⟨ cright cleft comm-bot H ([ S-gate ]ʷ) reversed ⟩
    (H ↓ • CZ • H ↓) • (H ↑ • S ↓)
      • (CZ • H ↑ • S ↑ • H ↑ • S ↓ • S ↓ • S ↓)
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • CZ • H ↓ • H ↑) • (S ↓ • CZ)
      • (H ↑ • S ↑ • H ↑ • S ↓ • S ↓ • S ↓)
      ≈⟨ cright cleft SZZ ⟩
    (H ↓ • CZ • H ↓ • H ↑) • (CZ • S ↓)
      • (H ↑ • S ↑ • H ↑ • S ↓ • S ↓ • S ↓)
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • CZ • H ↓ • H ↑ • CZ) • (S ↓ • (H ↑ • S ↑ • H ↑))
      • (S ↓ • S ↓ • S ↓)
      ≈⟨ cright cleft comm-bot (H • S • H) ([ S-gate ]ʷ) reversed ⟩
    (H ↓ • CZ • H ↓ • H ↑ • CZ) • ((H ↑ • S ↑ • H ↑) • S ↓)
      • (S ↓ • S ↓ • S ↓)
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↑ • S ↑ • H ↑) • (S ↓ • S ↓ • S ↓ • S ↓)
      ≈⟨ cright OneQubit.SSSS ⟩
    (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↑ • S ↑ • H ↑) • ε
      ≈⟨ right-unit ⟩
    H ↓ • CZ • H ↓ • H ↑ • CZ • H ↑ • S ↑ • H ↑ ∎

  ------------------------------------------------------------------
  -- (17)  H·CZ·HSH·CZ = CZ·HSH·CZ·SSSHS↑·X          [supplement: HZZSHHZZ]
  --
  -- Same opening as (16) -- (12) to pull the S left of the first CZ,
  -- then (11) to expose a CZ·H·CZ block -- but the two halves are
  -- different: the wire-0 one ends in C8, because by then its prefix has
  -- become the Pauli X, and the wire-1 one is just S⁴ = 1.  What closes
  -- it is (15) and then (7).
  --
  -- Stated in the spelling the supplement's own proof file uses (its
  -- equations 3.22 and 3.30), since that is what a replay of Section 3
  -- has to match.

  private
    SSSS↑ : S ↑ • S ↑ • S ↑ • S ↑ ≈ ε
    SSSS↑ = lemma-cong↑ (S • S • S • S) ε OneQubit.SSSS

    -- (13), then C8, then the wire-0 word collapses by HSSHSHS.
    halfA' : H ↓ • S ↓ • CZ • H ↓ • CZ ≈ CZ • H ↓ • S ↓ • H ↓ • S ↑ • S ↑ • S ↑
    halfA' = begin
      H ↓ • S ↓ • CZ • H ↓ • CZ
        ≈⟨ by-assoc Eq.refl ⟩
      (H ↓ • S ↓) • (CZ • H ↓ • CZ)
        ≈⟨ cright ZZHZZ ⟩
      (H ↓ • S ↓) • (S ↓ • H ↓ • CZ • S ↓ • H ↓ • S ↓ • S ↑ • ω ^ 7)
        ≈⟨ by-assoc Eq.refl ⟩
      (H ↓ • S ↓ • S ↓ • H ↓ • CZ) • (S ↓ • H ↓ • S ↓ • S ↑ • ω ^ 7)
        ≈⟨ cleft XZZ ⟩
      (CZ • H ↓ • S ↓ • S ↓ • H ↓ • S ↑ • S ↑)
        • (S ↓ • H ↓ • S ↓ • S ↑ • ω ^ 7)
        ≈⟨ by-assoc Eq.refl ⟩
      CZ • (H ↓ • S ↓ • S ↓ • H ↓) • ((S ↑ • S ↑) • (S ↓ • H ↓ • S ↓))
        • (S ↑ • ω ^ 7)
        ≈⟨ cright cright cleft
             comm-bot (S • S) ([ S-gate ]ʷ • [ H-gate ]ʷ • [ S-gate ]ʷ) ⟩
      CZ • (H ↓ • S ↓ • S ↓ • H ↓) • ((S ↓ • H ↓ • S ↓) • (S ↑ • S ↑))
        • (S ↑ • ω ^ 7)
        ≈⟨ by-assoc Eq.refl ⟩
      CZ • (H ↓ • S ↓ • S ↓ • H ↓ • S ↓ • H ↓ • S ↓)
        • (S ↑ • S ↑ • S ↑ • ω ^ 7)
        ≈⟨ cright cleft OneQubit.HSSHSHS ⟩
      CZ • (H ↓ • S ↓ • H ↓ • ω) • (S ↑ • S ↑ • S ↑ • ω ^ 7)
        ≈⟨ by-assoc Eq.refl ⟩
      CZ • (H ↓ • S ↓ • H ↓) • (ω • (S ↑ • S ↑ • S ↑ • ω ^ 7))
        ≈⟨ cright cright ω-central (S ↑ • S ↑ • S ↑ • ω ^ 7) ⟩
      CZ • (H ↓ • S ↓ • H ↓) • ((S ↑ • S ↑ • S ↑ • ω ^ 7) • ω)
        ≈⟨ by-assoc Eq.refl ⟩
      (CZ • H ↓ • S ↓ • H ↓ • S ↑ • S ↑ • S ↑) • ω ^ 8
        ≈⟨ cright ω⁸ ⟩
      (CZ • H ↓ • S ↓ • H ↓ • S ↑ • S ↑ • S ↑) • ε
        ≈⟨ right-unit ⟩
      CZ • H ↓ • S ↓ • H ↓ • S ↑ • S ↑ • S ↑ ∎

    -- (13)↑, and then the four S↑ cancel outright.
    halfB' : S ↑ • S ↑ • S ↑ • CZ • H ↑ • CZ ≈
             H ↑ • CZ • S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7
    halfB' = begin
      S ↑ • S ↑ • S ↑ • CZ • H ↑ • CZ
        ≈⟨ by-assoc Eq.refl ⟩
      (S ↑ • S ↑ • S ↑) • (CZ • H ↑ • CZ)
        ≈⟨ cright ZZHZZ↑ ⟩
      (S ↑ • S ↑ • S ↑) • (S ↑ • H ↑ • CZ • S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7)
        ≈⟨ by-assoc Eq.refl ⟩
      (S ↑ • S ↑ • S ↑ • S ↑) • (H ↑ • CZ • S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7)
        ≈⟨ cleft SSSS↑ ⟩
      ε • (H ↑ • CZ • S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7)
        ≈⟨ left-unit ⟩
      H ↑ • CZ • S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7 ∎

  HZZSHHZZ : H ↓ • CZ • H ↑ • S ↓ • H ↓ • CZ ≈
             CZ • H ↑ • S ↓ • H ↓ • CZ • S ↑ • S ↑ • S ↑ • H ↑ • S ↑
               • H ↓ • S ↓ • S ↓ • H ↓
  HZZSHHZZ = begin
    H ↓ • CZ • H ↑ • S ↓ • H ↓ • CZ
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • CZ) • (H ↑ • (S ↓ • H ↓)) • CZ
      ≈⟨ cright cleft comm-bot H ([ S-gate ]ʷ • [ H-gate ]ʷ) ⟩
    (H ↓ • CZ) • ((S ↓ • H ↓) • H ↑) • CZ
      ≈⟨ by-assoc Eq.refl ⟩
    H ↓ • (CZ • S ↓) • (H ↓ • H ↑ • CZ)
      ≈⟨ cright cleft SZZ reversed ⟩
    H ↓ • (S ↓ • CZ) • (H ↓ • H ↑ • CZ)
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • S ↓ • CZ • H ↓) • ε • (H ↑ • CZ)
      ≈⟨ cright cleft ZZZZ reversed ⟩
    (H ↓ • S ↓ • CZ • H ↓) • (CZ • CZ) • (H ↑ • CZ)
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • S ↓ • CZ • H ↓ • CZ) • (CZ • H ↑ • CZ)
      ≈⟨ cleft halfA' ⟩
    (CZ • H ↓ • S ↓ • H ↓ • S ↑ • S ↑ • S ↑) • (CZ • H ↑ • CZ)
      ≈⟨ by-assoc Eq.refl ⟩
    (CZ • H ↓ • S ↓ • H ↓) • (S ↑ • S ↑ • S ↑ • CZ • H ↑ • CZ)
      ≈⟨ cright halfB' ⟩
    (CZ • H ↓ • S ↓ • H ↓) • (H ↑ • CZ • S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7)
      ≈⟨ by-assoc Eq.refl ⟩
    CZ • ((H ↓ • S ↓ • H ↓) • H ↑) • (CZ • S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7)
      ≈⟨ cright cleft
           comm-bot H ([ H-gate ]ʷ • [ S-gate ]ʷ • [ H-gate ]ʷ) reversed ⟩
    CZ • (H ↑ • (H ↓ • S ↓ • H ↓)) • (CZ • S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7)
      ≈⟨ by-assoc Eq.refl ⟩
    CZ • H ↑ • (H ↓ • S ↓ • H ↓ • CZ) • (S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7)
      ≈⟨ cright cright cleft HSHZZ ⟩
    CZ • H ↑ • (S ↓ • H ↓ • CZ • S ↓ • H ↓ • S ↓ • S ↓ • H ↓ • S ↑ • S ↑ • ω ^ 7)
      • (S ↑ • H ↑ • S ↑ • S ↓ • ω ^ 7)
      ≈⟨ by-assoc Eq.refl ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ • S ↓ • H ↓ • S ↓ • S ↓ • H ↓ • S ↑ • S ↑)
      • (ω ^ 7 • (S ↑ • H ↑ • S ↑ • S ↓)) • ω ^ 7
      ≈⟨ cright cleft ω^-central 7 (S ↑ • H ↑ • S ↑ • S ↓) ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ • S ↓ • H ↓ • S ↓ • S ↓ • H ↓ • S ↑ • S ↑)
      • ((S ↑ • H ↑ • S ↑ • S ↓) • ω ^ 7) • ω ^ 7
      ≈⟨ by-assoc Eq.refl ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ • S ↓ • H ↓ • S ↓ • S ↓ • H ↓)
      • ((S ↑ • S ↑ • S ↑ • H ↑ • S ↑) • S ↓) • ω ^ 14
      ≈⟨ cright cleft comm-bot (S • S • S • H • S) ([ S-gate ]ʷ) ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ • S ↓ • H ↓ • S ↓ • S ↓ • H ↓)
      • (S ↓ • (S ↑ • S ↑ • S ↑ • H ↑ • S ↑)) • ω ^ 14
      ≈⟨ by-assoc Eq.refl ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ) • (S ↓ • H ↓ • S ↓ • S ↓ • H ↓ • S ↓)
      • (S ↑ • S ↑ • S ↑ • H ↑ • S ↑ • ω ^ 14)
      ≈⟨ cright cleft OneQubit.SHSSHS ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ) • (H ↓ • S ↓ • S ↓ • H ↓ • ω ^ 2)
      • (S ↑ • S ↑ • S ↑ • H ↑ • S ↑ • ω ^ 14)
      ≈⟨ by-assoc Eq.refl ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ • H ↓ • S ↓ • S ↓ • H ↓)
      • (ω ^ 2 • (S ↑ • S ↑ • S ↑ • H ↑ • S ↑)) • ω ^ 14
      ≈⟨ cright cleft ω^-central 2 (S ↑ • S ↑ • S ↑ • H ↑ • S ↑) ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ • H ↓ • S ↓ • S ↓ • H ↓)
      • ((S ↑ • S ↑ • S ↑ • H ↑ • S ↑) • ω ^ 2) • ω ^ 14
      ≈⟨ by-assoc Eq.refl ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ)
      • ((H ↓ • S ↓ • S ↓ • H ↓) • (S ↑ • S ↑ • S ↑ • H ↑ • S ↑)) • ω ^ 16
      ≈⟨ cright cleft
           comm-bot (S • S • S • H • S)
                    ([ H-gate ]ʷ • [ S-gate ]ʷ • [ S-gate ]ʷ • [ H-gate ]ʷ)
             reversed ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ)
      • ((S ↑ • S ↑ • S ↑ • H ↑ • S ↑) • (H ↓ • S ↓ • S ↓ • H ↓)) • ω ^ 16
      ≈⟨ by-assoc Eq.refl ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ • S ↑ • S ↑ • S ↑ • H ↑ • S ↑
       • H ↓ • S ↓ • S ↓ • H ↓) • ω ^ 8 • ω ^ 8
      ≈⟨ cright cleft ω⁸ ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ • S ↑ • S ↑ • S ↑ • H ↑ • S ↑
       • H ↓ • S ↓ • S ↓ • H ↓) • ε • ω ^ 8
      ≈⟨ by-assoc Eq.refl ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ • S ↑ • S ↑ • S ↑ • H ↑ • S ↑
       • H ↓ • S ↓ • S ↓ • H ↓) • ω ^ 8
      ≈⟨ cright ω⁸ ⟩
    (CZ • H ↑ • S ↓ • H ↓ • CZ • S ↑ • S ↑ • S ↑ • H ↑ • S ↑
       • H ↓ • S ↓ • S ↓ • H ↓) • ε
      ≈⟨ right-unit ⟩
    CZ • H ↑ • S ↓ • H ↓ • CZ • S ↑ • S ↑ • S ↑ • H ↑ • S ↑
      • H ↓ • S ↓ • S ↓ • H ↓ ∎

------------------------------------------------------------------------
-- Lemma 1.2, the one rule still to be proved
--
-- Taken from the supplement's own proof file, in the spelling it uses
-- there (minctx.py finds the minimal-context instance of a rule, which
-- states it); confirmed by check_words.py.  Its proof is on
-- the supplement's page 3, and is four steps: (11), (13), (15), (17).
--
--   (18)  H₀·CZ·H₁H₀·CZ·H₁H₀·CZ  =  CZ·H₁H₀·CZ·H₁H₀·CZ·H₁
--                                             [supplement: HZZHHZZHHZZ,
--                                                     equation 3.100]
--
-- Read it as: the block Q = CZ·H₁H₀·CZ·H₁H₀·CZ is a SWAP, so an H on
-- wire 0 before it is an H on wire 1 after it -- i.e. H₀·Q = Q·H₁.
-- Everything it needs is now available, (17) included.
--
-- THE PLACEMENT, worked out and verified (check_words.py).  Write
-- LHS = H₀ · CZ₁ · H₁H₀ · CZ₂ · H₁H₀ · CZ₃.  The (11) goes in the
-- SECOND block, not the first: split CZ₂·H₁H₀·CZ₃ into
-- (CZ₂·H₀·CZ')·(CZ'·H₁·CZ₃).  Then
--
--   (13) on CZ₂·H₀·CZ'  brings an S₀H₀ to the left of the new CZ,
--                       so the front reads H₀·CZ₁·H₁·(H₀S₀H₀)·CZ;
--   (15) on H₀S₀H₀·CZ   turns that into H₀·CZ₁·H₁S₀H₀·CZ,
--
-- which is EXACTLY (17)'s left-hand side, and (17) is the fourth and
-- last step.  The checked intermediate, after (11), (13) and (15), is
--
--   H₀·CZ·H₁S₀H₀·CZ · (S₀H₀S₀S₀H₀·S₀H₀S₀) · (S₁S₁S₁) · CZ·H₁·CZ · ω⁻²
--
-- with the first six letters being (17)'s redex.  What is left after
-- applying (17) is tail bookkeeping on the two wire words -- the wire-1
-- one has an S⁴ in it, and the trailing CZ·H₁·CZ is a (13)↑ redex.
--
-- Also proved-in-advance and verified is the bare-H analogue of
-- halfA/halfA', which is NOT the opening move but is correct and may be
-- useful in the tail:
--
--   halfA''  H₀·CZ·H₀·CZ  =  S₀H₀·CZ·H₀S₀S₀S₀·S₁S₁S₁
--
-- (route: (13), then (15), then SHSSHSHS collapses by (7) and (2)).
-- DEAD END, do not repeat: opening with (11) on the FIRST block and
-- pushing through halfA'' then halfB' leaves a wire-0 prefix S₀H₀ to the
-- left of the leading CZ, which no commutation can remove.
--
-- Worth knowing before writing it: the proof file spells (14), (15) and
-- (16) with their wire-0 and wire-1 blocks in the OPPOSITE order to the
-- statements proved above -- e.g. it writes (14) as
-- S₀S₀H₀·CZ = H₀·CZ·S₁S₁·H₀S₀S₀H₀.  The words are the same up to
-- commuting gates on disjoint wires, so nothing above needs restating;
-- it is the replay that has to bridge the two, and Wires.comm-bot is
-- what it bridges them with.
--
-- On (17), note that the halfA / halfB decomposition applied to it
-- yields a DIFFERENT right-hand side,
--
--   H₀·CZ·S₀H₀H₁·CZ  =  CZ · H₀S₀H₀ · H₁ · CZ · S₁H₁S₁ · S₀ · ω⁻¹
--
-- (route: (12) to pull S₀ left of the first CZ, (11), (13), then C8 --
-- the wire-0 prefix has become the Pauli X -- then HSSHSHS; the second
-- block is halfB followed by (14)↑, (2) and (6)).  Both words are
-- correct -- check_words.py evaluates them and they agree --
-- so this is not a misreading; they are two spellings of the same
-- operator.  Prove the FORM ABOVE, not the easier derived one: the
-- supplement's Section 3 proofs use (17) in Selinger's spelling, and a
-- replay of those steps has to produce his words letter for letter.
--
-- Both go the way (16) went, and the way to write them is the way (16)
-- is written above: insert CZ·CZ = 1 by (11) to expose a CZ·H·CZ block,
-- spend it with (13), clean the exposed wire with the one-qubit rules,
-- then repeat upside down -- so each splits into two halves that meet at
-- a single commutation.  Selinger's chains are twelve steps for (17)
-- (which additionally uses C8 directly and (15)) and four for (18)
-- (which uses (15) and then (17)).
--
-- Every wire-0/wire-1 interleaving is Wires.comm-bot, one call per
-- crossing, and no step of Selinger's is spent on it.

------------------------------------------------------------------------
-- Lemma 1.3 — three qubits
--
-- (19) is C12.  (20) and (21) are the two three-qubit derived rules,
-- still to be proved; their proofs are on the supplement's pages 3
-- onwards.
--
-- Their statements are NOT taken from the pictures, which at three
-- wires are past what a rendered page can be read off reliably.  They
-- are read off the supplement's own proof file instead: the instance of
-- a rule with the least surrounding context states it, and
-- minctx.py finds it.  For `Ri` that is equation 3.65 and
-- for `Rii` equations 3.40 / 3.54 (3.57 uses it backwards).  Both are
-- confirmed by check_words.py.  Writing CZ for the
-- controlled-Z on wires 0-1 and CZ' for the one on wires 1-2:
--
--   (20)  CZ · V · CZ' = V,   where                        [supplement: Ri]
--           V = H₁·CZ'·H₂H₁·CZ'·H₂H₀·CZ·H₁H₀·CZ·H₁
--         equivalently CZ · V = V · CZ'.  This is the sense in which a
--         controlled-Z crosses a three-qubit block; the page-1 picture
--         draws the upside-down version, CZ'·U = U·CZ with
--           U = H₁H₂·CZ·H₀H₁·CZ·H₀·CZ'·H₁H₂·CZ'·H₁.
--
--   (21)  CZ·H₁·CZ'·H₁H₀·CZ·H₁H₀·CZ·H₁·CZ'·S₁H₁H₀·CZ·H₁S₁S₁H₁
--           =  H₁H₀·CZ·CZ'·S₁H₁H₁S₁S₁H₁H₀·S₀S₀S₀     [supplement: Rii]
--
-- Note (21)'s words are not reduced -- H₁H₁ occurs on the right -- which
-- is expected: they are whatever the machine-generated proof produced,
-- and a replay has to reproduce them letter for letter.

module ThreeQubit {n : ℕ} where

  private
    Γ = (₃₊ n) CRel,_===_

  open PB Γ

  -- (19)  the two controlled-Zs of a triple commute       [supplement: ZZxZZ]
  ZZxZZ : CZ ↑ • CZ ≈ CZ • CZ ↑
  ZZxZZ = axiom (srel c12)
