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

data Rule : Set where
  ω⁸ T⁸ H² E TX CPh B CZ CSH HT² HTH : Rule

arity : Rule → ℕ
arity ω⁸  = 0
arity T⁸  = 1
arity H²  = 1
arity E   = 1
arity TX  = 1
arity CPh = 2
arity B   = 2
arity CZ  = 2
arity CSH = 2
arity HT² = 2
arity HTH = 2

axiom : (r : Rule) → Circuit (arity r) × Circuit (arity r)
axiom ω⁸  = ω ^ 8                , ε
axiom T⁸  = T ^ 8                , ε
axiom H²  = H • H                , ε
axiom E   = H • S • H            , ω • S ^ 3 • H • S ^ 3
axiom TX  = ω • T† • X           , X • T
axiom CPh = CX • T ↑ • CX        , T ↑
axiom B   = CX • CX↓             , σ • CX
axiom CZ  = H • CX • H           , S ↑ • S • CX • S ^ 3 • CX
axiom CSH = CS • CH₀             , CH₀ • CS
axiom HT² = CH • T • CH₀ • T†    , T • CH₀ • T† • CH
axiom HTH = CH₀ • T • CH • CH₀↓ • T ↑ • CH↓ ,
            CH₀↓ • T ↑ • CH↓ • CH₀ • T • CH

lhs rhs : (r : Rule) → Circuit (arity r)
lhs r = proj₁ (axiom r)
rhs r = proj₂ (axiom r)

open Fragment arity lhs rhs public
