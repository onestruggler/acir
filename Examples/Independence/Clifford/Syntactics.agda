------------------------------------------------------------------------
-- Presentations of groups
--
-- Qubit Clifford circuits: the gates and the rule set Cliff₂ of
-- Blake, "Simpler presentations for many fragments of quantum
-- circuits" (arXiv:2602.09874), Figure 2
--
-- The gates are ω = e^{iπ/4} (0-ary), H, S and CNOT, with the swap σ
-- structural (Examples.Independence.Prop).  Wire 0 is the bottom wire:
-- CX has its control on wire 1 and its target on wire 0, as the paper
-- draws it, and a one-wire gate on the upper wire of two is g ↑.
-- Words are in diagram order, so each side reads as its figure.  The
-- shortcuts are those of Figure 9; a CNOT whose wires are not the
-- adjacent pair (control, target) from the top is the CNOT conjugated
-- by swaps, as Figure 9's (1) and (2) draw it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Clifford.Syntactics where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Gates

data Gate : ℕ → Set where
  ω-gate        : Gate 0
  H-gate S-gate : Gate 1
  CX-gate       : Gate 2

open import Examples.Independence.Prop Gate public

ω : Circuit n
ω = [ gate₀ ⌈ ω-gate ⌉ ]ʷ

H S : Circuit (₁₊ n)
H = [ gate₁ ⌈ H-gate ⌉ ]ʷ
S = [ gate₁ ⌈ S-gate ⌉ ]ʷ

CX : Circuit (₂₊ n)
CX = [ gate₂ ⌈ CX-gate ⌉ ]ʷ

------------------------------------------------------------------------
-- Shortcuts (Figure 9)

Z X S† : Circuit (₁₊ n)
Z  = S ^ 2
X  = H • Z • H
S† = S ^ 3

ω† : Circuit n
ω† = ω ^ 7

-- CNOT with its control on wire 0 and its target on wire 1.
CX↓ : Circuit (₂₊ n)
CX↓ = σ • CX • σ

-- CNOT from wire 2 to wire 0, past wire 1 (Figure 9 (1)).
CX₂₀ : Circuit (₃₊ n)
CX₂₀ = σ • CX ↑ • σ

------------------------------------------------------------------------
-- The rule set Cliff₂ (Figure 2)

data Rule : Set where
  ω⁸ H² S⁴ E CPh B CZ I : Rule

arity : Rule → ℕ
arity ω⁸  = 0
arity H²  = 1
arity S⁴  = 1
arity E   = 1
arity CPh = 2
arity B   = 2
arity CZ  = 2
arity I   = 3

-- Each axiom as its left and right side.
axiom : (r : Rule) → Circuit (arity r) × Circuit (arity r)
axiom ω⁸  = ω ^ 8           , ε
axiom H²  = H • H           , ε
axiom S⁴  = S ^ 4           , ε
axiom E   = H • S • H       , ω • S ^ 3 • H • S ^ 3
axiom CPh = CX • S ↑ • CX   , S ↑
axiom B   = CX • CX↓        , σ • CX
axiom CZ  = H • CX • H      , S ↑ • S • CX • S ^ 3 • CX
axiom I   = CX • CX ↑ • CX₂₀ , CX ↑ • CX

lhs rhs : (r : Rule) → Circuit (arity r)
lhs r = proj₁ (axiom r)
rhs r = proj₂ (axiom r)

open Fragment arity lhs rhs public
