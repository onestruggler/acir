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

data Rule : Set where
  ω⁸ H² S⁴ E CPh CSr B XCS CE I SH₀ SH₁ SH₂ SH₃ : Rule

arity : Rule → ℕ
arity ω⁸  = 0
arity H²  = 1
arity S⁴  = 1
arity E   = 1
arity CPh = 2
arity CSr = 2
arity B   = 2
arity XCS = 2
arity CE  = 2
arity I   = 3
arity SH₀ = 3
arity SH₁ = 3
arity SH₂ = 3
arity SH₃ = 3

axiom : (r : Rule) → Circuit (arity r) × Circuit (arity r)
axiom ω⁸  = ω ^ 8                     , ε
axiom H²  = H • H                     , ε
axiom S⁴  = S ^ 4                     , ε
axiom E   = H • S • H                 , ω • S ^ 3 • H • S ^ 3
axiom CPh = CS • S ↑ • CS • CS • CS   , S ↑
axiom CSr = CS                        , σ • CS • σ
axiom B   = CX • CX↓                  , σ • CX
axiom XCS = X ↑ • CS                  , CS • CS • CS • X ↑ • S
axiom CE  = S ↑ • H ↑ • CS • H ↑ • CS , CS • H ↑ • CS • H ↑ • S ↑
axiom I   = CX • CX ↑ • CX₂₀          , CX ↑ • CX
axiom SH₀ = SHˡ 0                     , SHʳ 0
axiom SH₁ = SHˡ 1                     , SHʳ 1
axiom SH₂ = SHˡ 2                     , SHʳ 2
axiom SH₃ = SHˡ 3                     , SHʳ 3

lhs rhs : (r : Rule) → Circuit (arity r)
lhs r = proj₁ (axiom r)
rhs r = proj₂ (axiom r)

open Fragment arity lhs rhs public
