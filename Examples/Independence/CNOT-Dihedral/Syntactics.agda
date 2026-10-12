------------------------------------------------------------------------
-- Presentations of groups
--
-- CNOT-dihedral circuits: the gates and the rule set CNOTdihe₂ of
-- Blake, "Simpler presentations for many fragments of quantum
-- circuits" (arXiv:2602.09874), Figure 7
--
-- The gates are ω = e^{iπ/4} (0-ary), X, T and CNOT; conventions as in
-- Examples.Independence.Clifford.Syntactics.  The shortcuts CT and CCT
-- of Figure 9 are the phase gates |x, y⟩ ↦ ω^{x ⊕ y} |x, y⟩ and
-- |x, y, z⟩ ↦ ω^{x ⊕ y ⊕ z} |x, y, z⟩ (blue and green in Figure 7);
-- placed on wires that are not adjacent, they are conjugated by swaps
-- that bring the wires together, spelled as Amy, Chen and Ross spell
-- them (Examples.Groups.CNOT+Dihedral.Syntactics: U₀₂, U₁₃, U₀₃, V₀₂₃,
-- V₀₁₃), so that (C²T) and (C³T) are their R₉ and R₁₃ letter for
-- letter.  CTᵢⱼ and CCTᵢⱼₖ name the wires.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.CNOT-Dihedral.Syntactics where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Gates

data Gate : ℕ → Set where
  ω-gate        : Gate 0
  X-gate T-gate : Gate 1
  CX-gate       : Gate 2

open import Examples.Independence.Prop Gate public

ω : Circuit n
ω = [ gate₀ ⌈ ω-gate ⌉ ]ʷ

X T : Circuit (₁₊ n)
X = [ gate₁ ⌈ X-gate ⌉ ]ʷ
T = [ gate₁ ⌈ T-gate ⌉ ]ʷ

CX : Circuit (₂₊ n)
CX = [ gate₂ ⌈ CX-gate ⌉ ]ʷ

------------------------------------------------------------------------
-- Shortcuts (Figure 9)

S Z T† : Circuit (₁₊ n)
S  = T ^ 2
Z  = S ^ 2
T† = T ^ 7

CX↓ CT : Circuit (₂₊ n)
CX↓ = σ • CX • σ
CT  = CX • T • CX

CX₂₀ CCT : Circuit (₃₊ n)
CX₂₀ = σ • CX ↑ • σ
CCT  = CX ↑ • CX • T • CX • CX ↑

-- CT on three wires.
CT₂₁ CT₂₀ CT₁₀ : Circuit (₃₊ n)
CT₂₁ = CT ↑
CT₂₀ = σ • CT ↑ • σ
CT₁₀ = CT

-- CT and CCT on four wires.
CT₃₂ CT₃₁ CT₃₀ : Circuit (₄₊ n)
CT₃₂ = CT ↑ ↑
CT₃₁ = σ ↑ • CT ↑ ↑ • σ ↑
CT₃₀ = σ • σ ↑ • CT ↑ ↑ • σ ↑ • σ

CCT₃₂₁ CCT₃₂₀ CCT₃₁₀ CCT₂₁₀ : Circuit (₄₊ n)
CCT₃₂₁ = CCT ↑
CCT₃₂₀ = σ • CCT ↑ • σ
CCT₃₁₀ = σ ↑ • σ • CCT ↑ • σ • σ ↑
CCT₂₁₀ = CCT

-- T^k on each of the bottom three, and four, wires.
T³ʷ : ℕ → Circuit (₃₊ n)
T³ʷ k = T ^ k • (T ^ k) ↑ • (T ^ k) ↑ ↑

T⁴ʷ : ℕ → Circuit (₄₊ n)
T⁴ʷ k = T ^ k • (T ^ k) ↑ • (T ^ k) ↑ ↑ • (T ^ k) ↑ ↑ ↑

------------------------------------------------------------------------
-- The rule set CNOTdihe₂ (Figure 7)

data Rule : Set where
  ω⁸ X² T⁸ TX XC B ZC CPh I C²T C³T : Rule

arity : Rule → ℕ
arity ω⁸  = 0
arity X²  = 1
arity T⁸  = 1
arity TX  = 1
arity XC  = 2
arity B   = 2
arity ZC  = 2
arity CPh = 2
arity I   = 3
arity C²T = 3
arity C³T = 4

axiom : (r : Rule) → Circuit (arity r) × Circuit (arity r)
axiom ω⁸  = ω ^ 8               , ε
axiom X²  = X • X               , ε
axiom T⁸  = T ^ 8               , ε
axiom TX  = ω • T† • X          , X • T
axiom XC  = CX • X              , X ↑ • CX • X ↑
axiom B   = CX • CX↓            , σ • CX
axiom ZC  = CX • Z ↑            , Z • CX • Z
axiom CPh = CX • T ↑ • CX       , T ↑
axiom I   = CX₂₀                , CX • CX ↑ • CX • CX ↑
axiom C²T = CCT • CCT           ,
            T³ʷ 6 • CT₂₁ ^ 2 • CT₂₀ ^ 2 • CT₁₀ ^ 2
axiom C³T = CX ↑ ↑ • CCT • CX ↑ ↑ ,
            T⁴ʷ 5 • CT₃₂ ^ 3 • CT₃₁ ^ 3 • CT₃₀ ^ 3 •
            CT₂₁ ^ 3 • CT₂₀ ^ 3 • CT₁₀ ^ 3 •
            CCT₃₂₁ • CCT₃₂₀ • CCT₃₁₀ • CCT₂₁₀

lhs rhs : (r : Rule) → Circuit (arity r)
lhs r = proj₁ (axiom r)
rhs r = proj₂ (axiom r)

open Fragment arity lhs rhs public
