------------------------------------------------------------------------
-- Presentations of groups
--
-- Real Clifford circuits: the gates and the rule set RCliff₂ of
-- Blake, "Simpler presentations for many fragments of quantum
-- circuits" (arXiv:2602.09874), Figure 3
--
-- The gates are the scalar −1 (0-ary), H, Z and CNOT; conventions as
-- in Examples.Independence.Clifford.Syntactics.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Real-Clifford.Syntactics where

open import Data.Nat using (ℕ)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Gates

data Gate : ℕ → Set where
  m-gate        : Gate 0
  H-gate Z-gate : Gate 1
  CX-gate       : Gate 2

open import Examples.Independence.Prop Gate public

-- The scalar −1.
neg : Circuit n
neg = [ gate₀ ⌈ m-gate ⌉ ]ʷ

H Z : Circuit (₁₊ n)
H = [ gate₁ ⌈ H-gate ⌉ ]ʷ
Z = [ gate₁ ⌈ Z-gate ⌉ ]ʷ

CX : Circuit (₂₊ n)
CX = [ gate₂ ⌈ CX-gate ⌉ ]ʷ

------------------------------------------------------------------------
-- Shortcuts (Figure 9)

X : Circuit (₁₊ n)
X = H • Z • H

CX↓ : Circuit (₂₊ n)
CX↓ = σ • CX • σ

CX₂₀ : Circuit (₃₊ n)
CX₂₀ = σ • CX ↑ • σ

------------------------------------------------------------------------
-- The rule set RCliff₂ (Figure 3)

infix 4 _SRel,_===_
data _SRel,_===_ : (n : ℕ) → CRel n where
  −²  : 0 SRel, neg ^ 2                === ε
  H²  : 1 SRel, H • H                  === ε
  Z²  : 1 SRel, Z • Z                  === ε
  F   : 1 SRel, Z • H • Z • H          === neg • H • Z • H • Z
  CX² : 2 SRel, CX • CX                === ε
  B   : 2 SRel, CX • CX↓               === σ • CX
  ZC  : 2 SRel, Z • CX • Z             === CX • Z ↑
  CZr : 2 SRel, H ↑ • H • CX • H ↑ • H === CX↓
  CF  : 2 SRel, CX • H • CX • Z • H    === H • Z • CX • H • CX
  I   : 3 SRel, CX • CX ↑ • CX₂₀       === CX ↑ • CX

open Lift-To-Prop _SRel,_===_ public
