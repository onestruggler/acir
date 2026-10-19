------------------------------------------------------------------------
-- Presentations of groups
--
-- Natural rules for X, CX, CCX and H, with the swap as a gate.
--
-- The rules are CCX+H.Natural's — the involutions, (X H)⁸ = 1, and the
-- two-wire rules — together with the rules of CCX+HH.NaturalP read
-- through HH ↦ H • H ↑ (`HHw`): the swap gate's definition and the
-- rules on two, three and four wires with HH written out.  So the
-- translation θ of NaturalP.Transfer sends every rule of NaturalP to a
-- rule here, letter for letter.  The swap is a symmetry by
-- Circuit.Prop.
--
-- One rule has no CCX+HH counterpart: CCXH⁴, (X H)⁴ = −1 controlled by
-- two wires, where the −1 becomes the CZ of the controls.  Without it
-- the rules are incomplete on three wires: there every other rule holds
-- in W(E8) (the CCX+HH group, no single H) or in the real Clifford group
-- (no CCX), so they present at most the amalgam of the two over their
-- intersection, in which CCXH⁴ is a reduced word of length eight and so
-- not the identity (CCX+H/Rules3/README.md).  Wire 0 is the bottom wire and CX's control is wire 1.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.Syntactics where

open import Data.Nat.Base using (ℕ ; suc)
open import Word.Base using (WRel ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

data Gate : ℕ → Set where
  X-gate   : Gate 1
  H-gate   : Gate 1
  CX-gate  : Gate 2
  SW-gate  : Gate 2
  CCX-gate : Gate 3

open import Circuit.Prop Gate SW-gate public

private
  variable
    n : ℕ

X H : Circuit (suc n)
X = [ gate₁ X-gate ]ʷ
H = [ gate₁ H-gate ]ʷ

CX : Circuit (suc (suc n))
CX = [ gate₂ CX-gate ]ʷ

CCX : Circuit (suc (suc (suc n)))
CCX = [ gate₃ CCX-gate ]ʷ

-- HH, the CNOT from wire 0 to wire 1, CZ and Z.
HHw XC CZ : Circuit (suc (suc n))
HHw = H • H ↑
XC  = HHw • CX • HHw
CZ  = H • CX • H

Z : Circuit (suc n)
Z = H • X • H

infix 4 _NH,_===_
data _NH,_===_ : (n : ℕ) → CRel n where
  -- every gate but the swap is an involution (the swap is, by σ-inv)
  X²   : (₁₊ n) NH, X • X === ε
  H²   : (₁₊ n) NH, H • H === ε
  CX²  : (₂₊ n) NH, CX • CX === ε
  CCX² : (₃₊ n) NH, CCX • CCX === ε
  -- one wire
  XH⁸  : (₁₊ n) NH, X • H • X • H • X • H • X • H • X • H • X • H • X • H • X • H === ε
  -- the swap gate is the swap word
  sw-def : (₂₊ n) NH, σ === CX • XC • CX
  -- two wires
  X-control  : (₂₊ n) NH, X ↑ • CX • X ↑ === CX • X
  X-controlᵣ : (₂₊ n) NH, XC • X • XC === X • X ↑
  CNOT-S3    : (₂₊ n) NH, CX • XC • CX • XC • CX • XC === ε
  X-Z        : (₂₊ n) NH, X • HHw • X ↑ • HHw === HHw • X ↑ • HHw • X
  CZ-XC      : (₂₊ n) NH, CZ • XC • CZ • XC === Z
  -- three wires
  CCX-sym    : (₃₊ n) NH, σ ↑ • CCX • σ ↑ === CCX
  CCX-neg    : (₃₊ n) NH, X ↑ • CCX • X ↑ === CCX • σ ↑ • CX • σ ↑
  CCX-XC     : (₃₊ n) NH, CCX • XC • CCX • XC === σ • CCX • σ • CCX
  HH-swap₀   : (₃₊ n) NH, σ • HHw ↑ • σ === HHw • HHw ↑
  HH-swap₁   : (₃₊ n) NH, σ ↑ • HHw • σ ↑ === HHw • HHw ↑
  CCX-HH     : (₃₊ n) NH, CCX • XC • HHw • XC === XC • HHw • XC • CCX
  -- three wires, with a single H: (X H)⁴ = −1 controlled by two wires
  CCXH⁴      : (₃₊ n) NH, CCX • H • CCX • H • CCX • H • CCX • H === CZ ↑
  -- four wires
  CCX-comm   : (₄₊ n) NH, CCX ↑ • CX • CCX ↑ • CX === σ • CCX ↑ • σ

open Lift-To-Prop _NH,_===_ public
