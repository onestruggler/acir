------------------------------------------------------------------------
-- Presentations of groups
--
-- A colouring of the controls, the box on wire 1, and (335), (336)
--
-- `col s w` is w conjugated by X on the wires where s is false; `B₁ m`
-- is the box on wire 1 controlled by wire 0 and the wires 2 ….  In a
-- module of their own so that the four-wire decisions (Base335,
-- Base336) and their uses (BoxComm) state them with the same names: a
-- stored evaluation is only ever compared with its use syntactically.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Col where

open import Data.Nat using (ℕ)
open import Word.Base using (_•_)

open import Notations using (₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)

col : ∀ {n} → Bits n → Circuit n → Circuit n
col s w = negsB s • w • negsB s

B₁ : ∀ m → Circuit (₃₊ m)
B₁ m = Ex ↓ • Λ□ (₂₊ m) • Ex ↓

-- (335) and (336) at the canonical position: the box on wire 0 commutes
-- with every colouring of itself and of the box on wire 1 (BoxComm).
C335 C336 : ℕ → Set
C335 m = ∀ (s : Bits (₃₊ m)) → (₃₊ m) ⊢ Λ□ (₂₊ m) • col s (Λ□ (₂₊ m)) ≈ col s (Λ□ (₂₊ m)) • Λ□ (₂₊ m)
C336 m = ∀ (s : Bits (₃₊ m)) → (₃₊ m) ⊢ Λ□ (₂₊ m) • col s (B₁ m) ≈ col s (B₁ m) • Λ□ (₂₊ m)
