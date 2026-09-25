------------------------------------------------------------------------
-- Presentations of groups
--
-- A colouring of the controls, the box on wire 1, and (335), (336)
--
-- `col s w` is w conjugated by X on the wires where s is false; `B₁ m`
-- is the box on wire 1 controlled by wire 0 and the wires 2 …, and
-- `Hg m` the H gate with its H on wire 0 and its box wire 1, controlled
-- by the wires 2 … (P ⊗ P on the wires 0 1 around B₁).  In a module of
-- their own so that the four-wire decisions (Base335, Base336,
-- Base338) and their uses (BoxComm, Box338) state them with the same
-- names: a stored evaluation is only ever compared with its use
-- syntactically.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Col where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ)
open import Data.Vec using (_∷_)
open import Word.Base using (_•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (cyc ; cyc⁻¹)

col : ∀ {n} → Bits n → Circuit n → Circuit n
col s w = negsB s • w • negsB s

B₁ : ∀ m → Circuit (₃₊ m)
B₁ m = Ex ↓ • Λ□ (₂₊ m) • Ex ↓

-- (335) and (336) at the canonical position: the box on wire 0 commutes
-- with every colouring of itself and of the box on wire 1 (BoxComm).
C335 C336 : ℕ → Set
C335 m = ∀ (s : Bits (₃₊ m)) → (₃₊ m) ⊢ Λ□ (₂₊ m) • col s (Λ□ (₂₊ m)) ≈ col s (Λ□ (₂₊ m)) • Λ□ (₂₊ m)
C336 m = ∀ (s : Bits (₃₊ m)) → (₃₊ m) ⊢ Λ□ (₂₊ m) • col s (B₁ m) ≈ col s (B₁ m) • Λ□ (₂₊ m)

Hg : ∀ m → Circuit (₃₊ m)
Hg m = PP ↓ • B₁ m • PP ↓

-- (338) at the canonical position: the box on wire 0 commutes with the
-- H gate on wire 0 whose box wire is its control wire 1, in every
-- colouring y of the H gate's controls (y all true is the paper's case
-- x = y, the others x ≠ y).
C338 : ℕ → Set
C338 m = ∀ (y : Bits (₁₊ m)) →
         (₃₊ m) ⊢ Λ□ (₂₊ m) • col (true ∷ true ∷ y) (Hg m) ≈ col (true ∷ true ∷ y) (Hg m) • Λ□ (₂₊ m)

-- The box on wire 0 (v true) or on wire 1 (v false), controlled by the
-- other of the wires 0 1 and by the wires 2 ….
Vb : Bool → ∀ m → Circuit (₃₊ m)
Vb true  m = Λ□ (₂₊ m)
Vb false m = B₁ m

-- The colours of the wires 0 1 2 of a box white on wire 2 and coloured γ
-- on the other of the wires 0 1: on wire 1 for the box on wire 0 (v
-- true), on wire 0 for the box on wire 1 (v false).
c₀ c₁ : Bool → Bool → Bool
c₀ true  γ = true
c₀ false γ = γ
c₁ true  γ = γ
c₁ false γ = true

bot : Bool → Bool → ∀ {j} → Bits j → Bits (₃₊ j)
bot v γ x = c₀ v γ ∷ c₁ v γ ∷ false ∷ x

-- P ⊗ P on the wires 0 3, and on the wires 1 3: P ⊗ P on the wires 0 1
-- under the cycle that carries wire 0 up to wire 3 (a placement around
-- wire 3 is that cycle, GeneralN.Place), and that under the swap of the
-- wires 0 1.
P₀₃ P₁₃ : ∀ {r} → Circuit (₄₊ r)
P₀₃ = cyc⁻¹ 3 • PP ↓ • cyc 3
P₁₃ = Ex ↓ • P₀₃ • Ex ↓

-- The H gate on wire 3 with its box wire on wire 1, controlled by the
-- wires 0 2 ….
Hg₃ : ∀ m → Circuit (₄₊ m)
Hg₃ m = P₁₃ • B₁ (₁₊ m) • P₁₃

-- (339) at the canonical position, with the wires 2 3 exchanged: the box
-- on wire 0, black on the wires 1 2, coloured a on wire 3 and x above,
-- commutes with the H gate on wire 3 whose box wire is wire 1, black on
-- wire 0, white on wire 2 and coloured y above.  The paper's (339) has
-- the two series differ on some wire, which its reduction moves next to
-- the lower wires and colours black in the box, white in the H gate; here
-- that wire is wire 2, the paper's H wire being wire 3.
C339 : ℕ → Set
C339 m = ∀ (a : Bool) (x y : Bits m) →
         (₄₊ m) ⊢ col (true ∷ true ∷ true ∷ a ∷ x) (Λ□ (₃₊ m)) • col (true ∷ true ∷ false ∷ true ∷ y) (Hg₃ m)
                ≈ col (true ∷ true ∷ false ∷ true ∷ y) (Hg₃ m) • col (true ∷ true ∷ true ∷ a ∷ x) (Λ□ (₃₊ m))
