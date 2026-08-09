------------------------------------------------------------------------
-- Presentations of groups
--
-- The dictionary between Figure 8's alphabet and the symplectic one.
--
-- Since Qubit.Selinger.Figure8 acquired its own gate set, its circuits
-- are words over ExactGate — ω plus H, S, CZ — while everything in the
-- P4-action layer (CliffordAction, CliffordGroup, Selinger.Action) works
-- over SympGate.  The two alphabets differ by exactly the scalar, so
-- there is a translation each way:
--
--   E : Word (Gen n)      → Word (F8.Gen n)   gates, relabelled;
--   D : Word (F8.Gen n)   → Word (Gen n)      gates back, and ω ↦ (SH)³.
--
-- D is the interesting one.  It is where the two readings of the scalar
-- meet: Figure 8 names it, the action layer computes with the word
-- (SH)³ that it names.  Both are monoid maps, so both are determined by
-- their action on generators, and both commute with the wire shift.
--
-- E is a plain relabelling — SympGate has no 0-ary gate, so nothing has
-- to be invented — and D undoes it on the nose (D∘E below).  The other
-- round trip is NOT an identity: E (D ω) is (SH)³ relabelled, not the
-- generator ω, and the two are equal only up to Figure 8's C4.  That
-- asymmetry is the whole content of the exact layer, and it is why this
-- module states D∘E and stops.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.Relabel
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; _ʷ ; wmap)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; SympGate ; Circuit ; S ; H ; _↑)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime as F8
open F8 using (ExactGate ; ω-gate)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Symplectic to Figure 8
--
-- A pure relabelling: SympGate's three gates are ExactGate's three
-- wire-consuming ones, and SympGate has no 0-ary gate for the gate₀
-- clause to be about.

gate→ : SympGate m → ExactGate m
gate→ Symplectic.H-gate  = F8.H-gate
gate→ Symplectic.S-gate  = F8.S-gate
gate→ Symplectic.CZ-gate = F8.CZ-gate

sym→ex : Gen n → F8.Gen n
sym→ex (Symplectic.gate₀ ())
sym→ex (Symplectic.gate₁ h) = F8.gate₁ (gate→ h)
sym→ex (Symplectic.gate₂ h) = F8.gate₂ (gate→ h)
sym→ex (x Symplectic.↥)     = sym→ex x F8.↥

E : Circuit n → F8.Circuit n
E = wmap sym→ex

------------------------------------------------------------------------
-- Figure 8 to symplectic
--
-- The scalar goes to the word it names.  A shifted generator goes to
-- the shift of its translation, which is what makes D commute with _↑;
-- note that this sends ω ↑ to ((SH)³) ↑ rather than to (SH)³, so the two
-- readings of Figure8.ω↑=ω differ by a wire shift and are reconciled
-- only by the action (ω acts trivially at every width), not on the nose.

-- The scalar is 0-ary, so it exists at width 0 as well, where there is
-- no S for (SH)³ to be built from — Gen ₀ is empty and ε is the only
-- symplectic circuit there.  This is the same split ScalarKernel's Ω₁
-- used to make, and the same degeneracy: at width 0 the symplectic side
-- has no room for a scalar.
ex→sym : F8.Gen n → Circuit n
ex→sym {₀}    (F8.gate₀ ω-gate) = ε
ex→sym {₁₊ _} (F8.gate₀ ω-gate) = (S • H) ^ 3
ex→sym (F8.gate₁ F8.H-gate)  = H
ex→sym (F8.gate₁ F8.S-gate)  = S
ex→sym (F8.gate₂ F8.CZ-gate) = Symplectic.CZ
ex→sym (x F8.↥)              = (ex→sym x) ↑

D : F8.Circuit n → Circuit n
D = ex→sym ʷ

------------------------------------------------------------------------
-- How the two fit together

-- D undoes E on the nose: E never produces a scalar, and on the gates
-- the two relabellings are inverse.
D∘E : (w : Circuit n) → D (E w) ≡ w
D∘E [ Symplectic.gate₀ () ]ʷ
D∘E [ Symplectic.gate₁ Symplectic.H-gate ]ʷ  = Eq.refl
D∘E [ Symplectic.gate₁ Symplectic.S-gate ]ʷ  = Eq.refl
D∘E [ Symplectic.gate₂ Symplectic.CZ-gate ]ʷ = Eq.refl
D∘E [ x Symplectic.↥ ]ʷ                      =
  Eq.cong _↑ (D∘E [ x ]ʷ)
D∘E ε       = Eq.refl
D∘E (u • v) = Eq.cong₂ _•_ (D∘E u) (D∘E v)

-- Both maps commute with the wire shift, on the nose.
E-↑ : (w : Circuit n) → E (w ↑) ≡ (E w) F8.↑
E-↑ [ x ]ʷ  = Eq.refl
E-↑ ε       = Eq.refl
E-↑ (u • v) = Eq.cong₂ _•_ (E-↑ u) (E-↑ v)

D-↑ : (w : F8.Circuit n) → D (w F8.↑) ≡ (D w) ↑
D-↑ [ x ]ʷ  = Eq.refl
D-↑ ε       = Eq.refl
D-↑ (u • v) = Eq.cong₂ _•_ (D-↑ u) (D-↑ v)
