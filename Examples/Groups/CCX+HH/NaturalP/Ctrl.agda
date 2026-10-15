------------------------------------------------------------------------
-- Presentations of groups
--
-- Controlled circuits: the control on wire 0, the circuit on the wires
-- above it.
--
-- `ctrl` replaces every gate of a circuit by its controlled version,
-- gate by gate.  At the bottom of the circuit the controlled gate is a
-- fixed gadget: X becomes the CNOT from wire 0 (XC), CX a Toffoli (its
-- control on wire 2 joined by wire 0), SW the Fredkin gate, and the two
-- gates whose controlled versions need a borrowed wire, HH and CCX,
-- become CHHa (two conjugated Toffolis) and C3Xa (Barenco's four
-- Toffolis), borrowing the wire just above the gate.  A gate one wire
-- up is the gadget with the control moved up past a spare wire
-- (`CTRL₁`): the spare wire is where HH and CCX then borrow (CHHb,
-- C3Xb), and each further wire up is a conjugation by the two swaps
-- that carry the control and the spare wire one wire down.  So no
-- definition depends on the width of the circuit, except that HH and
-- CCX at the bottom need a wire above them (the circuits here have at
-- least four wires, where that always holds).
--
-- The gadgets were found and checked exactly by Rules/gadgets.py, and
-- the whole construction against the controlled operator, for every
-- gate at every position up to six wires, by Rules/ctrlcheck.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Ctrl where

open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.CCX+HH.NaturalP.Syntactics

private
  variable
    n m : ℕ

------------------------------------------------------------------------
-- The gadgets (control on wire 0)

-- The Toffoli with controls on wires 0 and 2 and its target on wire 1:
-- the CNOT from wire 2 to wire 1, controlled by wire 0.
CCXc : Circuit (₃₊ n)
CCXc = HH • CCX • HH

-- The Fredkin gate: the swap of wires 1 and 2, controlled by wire 0.
Fredkin : Circuit (₃₊ n)
Fredkin = HH • CCX • HH ↑ • CCX • HH ↑ • CCX • HH

-- HH on wires 1 2 controlled by wire 0, wire 3 borrowed.  HH ⊗ I on the
-- wires 1 2 3 is a product of four reflections in orthogonal roots, and
-- each half of it is CX ⊗ I conjugated by V₁ = CX HH, resp.
-- V₂ = HH ↑ CX HH (one wire up here).
CHHa : Circuit (₄₊ n)
CHHa = CX ↑ • HH ↑ • CCXc • HH ↑ • CX ↑ •
       HH ↑ ↑ • CX ↑ • HH ↑ • CCXc • HH ↑ • CX ↑ • HH ↑ ↑

-- HH on wires 2 3 controlled by wire 0, wire 1 borrowed.
CHHb : Circuit (₄₊ n)
CHHb = σ ↑ • σ ↑ ↑ • CHHa • σ ↑ ↑ • σ ↑

-- The Toffoli with controls 0 and 4 and target 1, and the one with
-- controls 2 and 3 and target 4.
private
  T₁ T₂ : Circuit (suc (₄₊ n))
  T₁ = σ • σ ↑ • σ • σ ↑ ↑ ↑ • CCX ↑ • σ ↑ ↑ ↑ • σ • σ ↑ • σ
  T₂ = σ ↑ ↑ • σ ↑ ↑ ↑ • σ ↑ ↑ • CCX ↑ ↑ • σ ↑ ↑ • σ ↑ ↑ ↑ • σ ↑ ↑

-- CCX on wires 1 2 3 (target 1) controlled by wire 0, wire 4 borrowed:
-- Barenco's construction.
C3Xa : Circuit (suc (₄₊ n))
C3Xa = T₁ • T₂ • T₁ • T₂

-- CCX on wires 2 3 4 (target 2) controlled by wire 0, wire 1 borrowed.
C3Xb : Circuit (suc (₄₊ n))
C3Xb = σ ↑ • σ ↑ ↑ • σ ↑ ↑ ↑ • C3Xa • σ ↑ ↑ ↑ • σ ↑ ↑ • σ ↑

------------------------------------------------------------------------
-- Controlled gates and circuits

-- The controlled version of a gate of a circuit on the wires 1 … m.
CTRL  : Gen m → Circuit (₁₊ m)
-- The same with the gate one wire higher, wire 1 spare: the circuit on
-- the wires 2 … m + 1.
CTRL₁ : Gen m → Circuit (₂₊ m)

CTRL (gate₀ ())
CTRL (gate₁ X-gate)                  = XC
CTRL (gate₂ CX-gate)                 = CCXc
CTRL (gate₂ SW-gate)                 = Fredkin
CTRL {₂₊ zero}    (gate₂ HH-gate)    = ε
CTRL {₂₊ (suc _)} (gate₂ HH-gate)    = CHHa
CTRL {₃₊ zero}    (gate₃ CCX-gate)   = ε
CTRL {₃₊ (suc _)} (gate₃ CCX-gate)   = C3Xa
CTRL (g ↥)                           = CTRL₁ g

CTRL₁ (gate₀ ())
CTRL₁ (gate₁ X-gate)    = σ • XC ↑ • σ
CTRL₁ (gate₂ CX-gate)   = σ • CCXc ↑ • σ
CTRL₁ (gate₂ SW-gate)   = σ • Fredkin ↑ • σ
CTRL₁ (gate₂ HH-gate)   = CHHb
CTRL₁ (gate₃ CCX-gate)  = C3Xb
CTRL₁ (g ↥)             = (σ ↑ • σ) • CTRL₁ g ↑ • (σ • σ ↑)

-- A circuit on the wires 1 … m, controlled by wire 0.
ctrl : Circuit m → Circuit (₁₊ m)
ctrl [ g ]ʷ  = CTRL g
ctrl ε       = ε
ctrl (u • v) = ctrl u • ctrl v

-- … and controlled by wire 0 being 0.
ctrl⁻ : Circuit m → Circuit (₁₊ m)
ctrl⁻ w = X • ctrl w • X
