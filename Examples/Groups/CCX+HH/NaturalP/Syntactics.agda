------------------------------------------------------------------------
-- Presentations of groups
--
-- The natural CCX+HH rules with the swap as a gate.
--
-- Natural.Syntactics has no swap gate: its Ex is the word CX XC CX,
-- and three of its rules (braid, CX-up, CCX-up) are the naturality of
-- that word.  Here the swap is a fifth gate, SW, and Circuit.Prop makes
-- it a symmetry: σ-inv and σ-nat₁ … σ-nat₃ are axioms, braid, CX-up and
-- CCX-up are their instances at SW, CX and CCX, and the rule `sw-def`
-- identifies SW with CX XC CX.  The other rules are Natural's, with Ex
-- written σ.  NaturalP.Bridge translates both ways (SW ↦ Ex), so the
-- two theories are complete at the same widths; the width induction is
-- carried out here, where the placement calculus of Circuit.Prop is
-- available.  Words are read in matrix-product order, as in Natural.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Syntactics where

open import Data.Nat.Base using (ℕ ; suc)
open import Word.Base using (WRel ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

data Gate : ℕ → Set where
  X-gate   : Gate 1
  CX-gate  : Gate 2
  HH-gate  : Gate 2
  SW-gate  : Gate 2
  CCX-gate : Gate 3

open import Circuit.Prop Gate SW-gate public

private
  variable
    n : ℕ

X : Circuit (suc n)
X = [ gate₁ X-gate ]ʷ

CX HH : Circuit (suc (suc n))
CX = [ gate₂ CX-gate ]ʷ
HH = [ gate₂ HH-gate ]ʷ

CCX : Circuit (suc (suc (suc n)))
CCX = [ gate₃ CCX-gate ]ʷ

-- The CNOT from wire 0 to wire 1.
XC : Circuit (suc (suc n))
XC = HH • CX • HH

infix 4 _NP,_===_
data _NP,_===_ : (n : ℕ) → CRel n where
  -- every gate but the swap is an involution (the swap is, by σ-inv)
  X²   : (₁₊ n) NP, X • X === ε
  CX²  : (₂₊ n) NP, CX • CX === ε
  CCX² : (₃₊ n) NP, CCX • CCX === ε
  HH²  : (₂₊ n) NP, HH • HH === ε
  -- the swap gate is the swap word of Natural
  sw-def : (₂₊ n) NP, σ === CX • XC • CX
  -- two wires
  X-control  : (₂₊ n) NP, X ↑ • CX • X ↑ === CX • X
  X-controlᵣ : (₂₊ n) NP, XC • X • XC === X • X ↑
  CNOT-S3    : (₂₊ n) NP, CX • XC • CX • XC • CX • XC === ε
  X-Z        : (₂₊ n) NP, X • HH • X ↑ • HH === HH • X ↑ • HH • X
  -- three wires (braid and CX-up are σ-nat₂ at SW and CX)
  CCX-sym    : (₃₊ n) NP, σ ↑ • CCX • σ ↑ === CCX
  CCX-neg    : (₃₊ n) NP, X ↑ • CCX • X ↑ === CCX • σ ↑ • CX • σ ↑
  CCX-XC     : (₃₊ n) NP, CCX • XC • CCX • XC === σ • CCX • σ • CCX
  HH-swap₀   : (₃₊ n) NP, σ • HH ↑ • σ === HH • HH ↑
  HH-swap₁   : (₃₊ n) NP, σ ↑ • HH • σ ↑ === HH • HH ↑
  CCX-HH     : (₃₊ n) NP, CCX • XC • HH • XC === XC • HH • XC • CCX
  -- four wires (CCX-up is σ-nat₃ at CCX)
  CCX-comm   : (₄₊ n) NP, CCX ↑ • CX • CCX ↑ • CX === σ • CCX ↑ • σ

open Lift-To-Prop _NP,_===_ public
