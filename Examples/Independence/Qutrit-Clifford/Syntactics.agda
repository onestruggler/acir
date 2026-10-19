------------------------------------------------------------------------
-- Presentations of groups
--
-- Qutrit Clifford circuits: the gates and the rule set Cliff₃ of
-- Blake, "Simpler presentations for many fragments of quantum
-- circuits" (arXiv:2602.09874), Figure 4
--
-- The gates are ω₁₂ = e^{iπ/6} (0-ary), H, S and the qutrit CNOT
-- |x, y⟩ ↦ |x, x + y⟩, its control on wire 1; conventions otherwise as
-- in Examples.Independence.Clifford.Syntactics.
--
-- One correction: Figure 4 prints the scalar of (E) as ω₁₂⁷.  With the
-- semantics of Section 3.2 (H|x⟩ = Σₖ e^{2πi xk/3}|k⟩/√3,
-- S = diag(1, 1, e^{2πi/3})), S H S is ω₁₂ H³ S² H³, and ω₁₂⁷ = −ω₁₂
-- makes (E) unsound; it is stated here with ω₁₂.  No separator of
-- Figure 8(c) sees the exponent: ?ω₁₂ separates (ω¹²) at arity 0,
-- where (E) does not apply.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Qutrit-Clifford.Syntactics where

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

K H† S† S′ Z X : Circuit (₁₊ n)
K  = H ^ 2
H† = H ^ 3
S† = S ^ 2
S′ = K • S • K
Z  = S† • S′
X  = H • Z • H†

CX↓ : Circuit (₂₊ n)
CX↓ = σ • CX • σ

CX₂₀ : Circuit (₃₊ n)
CX₂₀ = σ • CX ↑ • σ

------------------------------------------------------------------------
-- The rule set Cliff₃ (Figure 4)

infix 4 _SRel,_===_
data _SRel,_===_ : (n : ℕ) → CRel n where
  ω¹² : 0 SRel, ω ^ 12            === ε
  H⁴  : 1 SRel, H ^ 4             === ε
  S³  : 1 SRel, S ^ 3             === ε
  E   : 1 SRel, S • H • S         === H ^ 3 • S ^ 2 • H ^ 3 • ω
  SS′ : 1 SRel, S • K • S • K     === K • S • K • S
  CPh : 2 SRel, CX • S ↑ • K • CX === S ↑ • K
  KC  : 2 SRel, K ↑ • CX          === CX • CX • K ↑
  CZ  : 2 SRel, H • CX • H ^ 3    === S ↑ • S • CX • S ^ 2 • CX • CX
  B   : 2 SRel, σ • CX            === CX • CX↓ • CX↓ • K ↑
  I   : 3 SRel, CX • CX ↑ • CX₂₀  === CX ↑ • CX

open Lift-To-Prop _SRel,_===_ public
