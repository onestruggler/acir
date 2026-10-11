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
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
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

data Rule : Set where
  −² H² Z² F CX² B ZC CZr CF I : Rule

arity : Rule → ℕ
arity −²  = 0
arity H²  = 1
arity Z²  = 1
arity F   = 1
arity CX² = 2
arity B   = 2
arity ZC  = 2
arity CZr = 2
arity CF  = 2
arity I   = 3

axiom : (r : Rule) → Circuit (arity r) × Circuit (arity r)
axiom −²  = neg ^ 2                , ε
axiom H²  = H • H                  , ε
axiom Z²  = Z • Z                  , ε
axiom F   = Z • H • Z • H          , neg • H • Z • H • Z
axiom CX² = CX • CX                , ε
axiom B   = CX • CX↓               , σ • CX
axiom ZC  = Z • CX • Z             , CX • Z ↑
axiom CZr = H ↑ • H • CX • H ↑ • H , CX↓
axiom CF  = CX • H • CX • Z • H    , H • Z • CX • H • CX
axiom I   = CX • CX ↑ • CX₂₀       , CX ↑ • CX

lhs rhs : (r : Rule) → Circuit (arity r)
lhs r = proj₁ (axiom r)
rhs r = proj₂ (axiom r)

open Fragment arity lhs rhs public
