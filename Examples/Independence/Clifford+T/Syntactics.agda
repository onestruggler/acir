------------------------------------------------------------------------
-- Presentations of groups
--
-- Clifford+T circuits: the gates and the rule set CliffT₂ of Blake,
-- "Simpler presentations for many fragments of quantum circuits"
-- (arXiv:2602.09874), Figure 5
--
-- The gates are ω = e^{iπ/4} (0-ary), H, T and CNOT; conventions as in
-- Examples.Independence.Clifford.Syntactics.  The controlled gates of
-- the shortcuts have their control on wire 1 and act on wire 0; a
-- hollow control (CH₀, CX₀) fires on 0, and CH↓, CH₀↓ are drawn upside
-- down.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Clifford+T.Syntactics where

open import Data.Nat using (ℕ)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Gates

data Gate : ℕ → Set where
  ω-gate        : Gate 0
  H-gate T-gate : Gate 1
  CX-gate       : Gate 2

open import Examples.Independence.Prop Gate public

ω : Circuit n
ω = [ gate₀ ⌈ ω-gate ⌉ ]ʷ

H T : Circuit (₁₊ n)
H = [ gate₁ ⌈ H-gate ⌉ ]ʷ
T = [ gate₁ ⌈ T-gate ⌉ ]ʷ

CX : Circuit (₂₊ n)
CX = [ gate₂ ⌈ CX-gate ⌉ ]ʷ

------------------------------------------------------------------------
-- Shortcuts (Figure 9)

S S† Z X T† : Circuit (₁₊ n)
S  = T ^ 2
S† = S ^ 3
Z  = S ^ 2
X  = H • Z • H
T† = T ^ 7

CX↓ : Circuit (₂₊ n)
CX↓ = σ • CX • σ

-- CNOT with a hollow control, controlled H, controlled H with a
-- hollow control, and controlled S.
CX₀ CH CH₀ CS CS† CH↓ CH₀↓ : Circuit (₂₊ n)
CX₀  = CX • X
CH   = S • H • T • CX • T† • H • S†
CH₀  = CH • H
CS   = T ↑ • T • CX • T† • CX
CS†  = CS ^ 3
CH↓  = σ • CH • σ
CH₀↓ = σ • CH₀ • σ

------------------------------------------------------------------------
-- The rule set CliffT₂ (Figure 5)

infix 4 _SRel,_===_
data _SRel,_===_ : (n : ℕ) → CRel n where
  ω⁸  : 0 SRel, ω ^ 8             === ε
  T⁸  : 1 SRel, T ^ 8             === ε
  H²  : 1 SRel, H • H             === ε
  E   : 1 SRel, H • S • H         === ω • S ^ 3 • H • S ^ 3
  TX  : 1 SRel, ω • T† • X        === X • T
  CPh : 2 SRel, CX • T ↑ • CX     === T ↑
  B   : 2 SRel, CX • CX↓          === σ • CX
  CZ  : 2 SRel, H • CX • H        === S ↑ • S • CX • S ^ 3 • CX
  CSH : 2 SRel, CS • CH₀          === CH₀ • CS
  HT² : 2 SRel, CH • T • CH₀ • T† === T • CH₀ • T† • CH
  HTH : 2 SRel, CH₀ • T • CH • CH₀↓ • T ↑ • CH↓ ===
                CH₀↓ • T ↑ • CH↓ • CH₀ • T • CH

open Lift-To-Prop _SRel,_===_ public
