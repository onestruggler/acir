------------------------------------------------------------------------
-- Presentations of groups
--
-- Clifford+CS circuits: the gates and the rule set CliffCS₂ of Blake,
-- "Simpler presentations for many fragments of quantum circuits"
-- (arXiv:2602.09874), Figure 6
--
-- The gates are ω = e^{iπ/4} (0-ary), H, S and the controlled S,
-- CS = diag(1, 1, 1, i), which is symmetric in its two wires;
-- conventions as in Examples.Independence.Clifford.Syntactics.  CNOT
-- is a shortcut here, H CS CS H on its target, wire 0.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Clifford+CS.Syntactics where

open import Data.Nat using (ℕ)
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
  CS-gate       : Gate 2

open import Examples.Independence.Prop Gate public

ω : Circuit n
ω = [ gate₀ ⌈ ω-gate ⌉ ]ʷ

H S : Circuit (₁₊ n)
H = [ gate₁ ⌈ H-gate ⌉ ]ʷ
S = [ gate₁ ⌈ S-gate ⌉ ]ʷ

CS : Circuit (₂₊ n)
CS = [ gate₂ ⌈ CS-gate ⌉ ]ʷ

------------------------------------------------------------------------
-- Shortcuts (Figure 9)

Z X S† : Circuit (₁₊ n)
Z  = S ^ 2
X  = H • Z • H
S† = S ^ 3

ω† : Circuit n
ω† = ω ^ 7

CX CX↓ : Circuit (₂₊ n)
CX  = H • CS • CS • H
CX↓ = σ • CX • σ

CX₂₀ : Circuit (₃₊ n)
CX₂₀ = σ • CX ↑ • σ

-- The two sides of (SH_k): CS on wires 0–1 and 1–2, with H on wire 1.
SHˡ SHʳ : ℕ → Circuit (₃₊ n)
SHˡ k = CS • H ↑ • CS ^ k • H ↑ • CS ↑ • H ↑ • (CS ↑) ^ k
SHʳ k = CS ↑ • H ↑ • (CS ↑) ^ k • H ↑ • CS • H ↑ • CS ^ k

------------------------------------------------------------------------
-- The rule set CliffCS₂ (Figure 6)

infix 4 _SRel,_===_
data _SRel,_===_ : (n : ℕ) → CRel n where
  ω⁸  : 0 SRel, ω ^ 8                     === ε
  H²  : 1 SRel, H • H                     === ε
  S⁴  : 1 SRel, S ^ 4                     === ε
  E   : 1 SRel, H • S • H                 === ω • S ^ 3 • H • S ^ 3
  CPh : 2 SRel, CS • S ↑ • CS • CS • CS   === S ↑
  CSr : 2 SRel, CS                        === σ • CS • σ
  B   : 2 SRel, CX • CX↓                  === σ • CX
  XCS : 2 SRel, X ↑ • CS                  === CS • CS • CS • X ↑ • S
  CE  : 2 SRel, S ↑ • H ↑ • CS • H ↑ • CS === CS • H ↑ • CS • H ↑ • S ↑
  I   : 3 SRel, CX • CX ↑ • CX₂₀          === CX ↑ • CX
  SH₀ : 3 SRel, SHˡ 0                     === SHʳ 0
  SH₁ : 3 SRel, SHˡ 1                     === SHʳ 1
  SH₂ : 3 SRel, SHˡ 2                     === SHʳ 2
  SH₃ : 3 SRel, SHˡ 3                     === SHʳ 3

open Lift-To-Prop _SRel,_===_ public
