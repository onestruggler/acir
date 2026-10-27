/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Qudit Clifford circuits in odd prime dimension: the rules of Figure 1

Bian, Li, Ross, van de Wetering and Zhao, *A Complete and Natural Rule Set
for Multi-Qudit Clifford Circuits in All Odd Prime Dimensions*
(arXiv:2609.40106).

For an odd prime `p`, the generators are the scalar `-ω` (`ω = e^{2πi/p}`),
the one-qudit gates `H` and `S` and the two-qudit gate `CZ` (Definition
2.11); the derived generators of Figure 2 are abbreviations ((T1)–(T4),
(T6), (T7)). The relations are the sixteen rules `C0`–`C15` of Figure 1,
`C3` a family indexed by `k ∈ ℤ_p`, each on the wires it is drawn on; the
theory is their closure `Lift (Padded (Rule p g))` under the structural
rules ("we assume the standard spatial relations", as in the qutrit
paper). `g` is the chosen generator of `ℤ_p^*`.

**Exponents** are read as in Remarks 1.1 and 2.2: an exponent of a gate of
order `p`, or of `ω`, is an element of `ℤ_p`, applied as the power by its
representative in `{0, …, p - 1}` (`ZMod.val`); `S^{-1}` is `S^{p-1}`,
`CX^{-1}` is `CX^{p-1}`, and `a⁻¹`, `u / v` are computed in `ℤ_p`. The
scalars `-1` and `ω` are the circuits `(-ω)^p` and `(-ω)^{p+1}`
(Figure 1's caption), and `(a/p)_L ∈ {±1}` is `(-1)^0` or `(-1)^1`.

**Wires and order** are as in `QCert.QutritClifford`: the paper's top wire
on `k` wires is wire `k - 1`, its bottom wire is wire `0`; `a ⨾ b` is `a`
followed by `b` (the word `b * a`), so each rule reads as its figure.
-/
import QCert.Circuit.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace QCert.QuditClifford

/-- The gates of qudit Clifford circuits (Definition 2.11): the scalar
`-ω`, the Hadamard gate `H`, the phase gate `S` and the controlled-Z gate
`CZ`. -/
inductive Gate : ℕ → Type
  /-- The scalar `-ω`, of order `2p`. -/
  | negω : Gate 0
  /-- The Hadamard gate. -/
  | H : Gate 1
  /-- The phase gate `S |j⟩ = ω^{j(j-1)/2} |j⟩`. -/
  | S : Gate 1
  /-- The controlled-Z gate. -/
  | CZ : Gate 2

/-- Qudit Clifford circuits on `n` wires. -/
abbrev Circ (n : ℕ) := Circuit Gate n

/-- Composition in time order: `a ⨾ b` is `a` followed by `b`. -/
def seq {n : ℕ} (a b : Circ n) : Circ n := b * a

@[inherit_doc] scoped infixl:70 " ⨾ " => seq

theorem seq_def {n : ℕ} (a b : Circ n) : a ⨾ b = b * a := rfl

/-- A circuit on the top `n` of `n + 1` wires. -/
abbrev top {n : ℕ} (c : Circ n) : Circ (n + 1) := Circuit.shift c

/-- A one-wire circuit on the bottom wire of `n + 1` wires. -/
abbrev bot {n : ℕ} (c : Circ 1) : Circ (n + 1) := Circuit.pad n c

/-- A two-wire circuit on the bottom two wires of `n + 2` wires. -/
abbrev bot2 {n : ℕ} (c : Circ 2) : Circ (n + 2) := Circuit.pad n c

/-! ### Generators -/

/-- The scalar `-ω`, at any width. -/
def negω {n : ℕ} : Circ n := Circuit.g0 Gate.negω

/-- The Hadamard gate. -/
def H : Circ 1 := Circuit.g1 Gate.H

/-- The phase gate. -/
def S : Circ 1 := Circuit.g1 Gate.S

/-- The controlled-Z gate. -/
def CZ : Circ 2 := Circuit.g2 Gate.CZ

/-! ### Derived generators (Figure 2) -/

section Derived

variable (p : ℕ)

/-- The scalar `-1 = (-ω)^p`. -/
def neg1 {n : ℕ} : Circ n := negω ^ p

/-- The scalar `ω = (-ω)^{p+1}`. -/
def ω {n : ℕ} : Circ n := negω ^ (p + 1)

/-- (T2) `X = H ⨾ S^{-1} ⨾ H² ⨾ S ⨾ H`. -/
def X : Circ 1 := H ⨾ S ^ (p - 1) ⨾ H ^ 2 ⨾ S ⨾ H

/-- (T3) `Z = S^{-1} ⨾ H² ⨾ S ⨾ H²`. -/
def Z : Circ 1 := S ^ (p - 1) ⨾ H ^ 2 ⨾ S ⨾ H ^ 2

/-- The exponent of `-1` in the Legendre symbol: `(a/p)_L = (-1)^{legendreExp p a}`. -/
def legendreExp [Fact p.Prime] (a : ZMod p) : ℕ := if legendreSym p a.val = 1 then 0 else 1

/-- (T1) The multiplier `M_a`, `a ∈ ℤ_p^*`:
`H ⨾ S^{a⁻¹} ⨾ H ⨾ S^a ⨾ H ⨾ S^{a⁻¹} ⨾ X^{(1-a)/2} ⨾ Z^{(1-a)/(2a)} · (a/p)_L ω^{(-a²+4a-2)/(8a)}`. -/
def M [Fact p.Prime] (a : ZMod p) : Circ 1 :=
  H ⨾ S ^ (a⁻¹).val ⨾ H ⨾ S ^ a.val ⨾ H ⨾ S ^ (a⁻¹).val ⨾ X p ^ ((1 - a) / 2).val ⨾
    Z p ^ ((1 - a) / (2 * a)).val ⨾ neg1 p ^ legendreExp p a ⨾
    ω p ^ ((-a ^ 2 + 4 * a - 2) / (8 * a)).val

/-- Two one-wire circuits side by side: `a` on the top wire, `b` on the
bottom wire. -/
def par (a b : Circ 1) : Circ 2 := top a * bot b

/-- (T4) The swap: `H ⊗ H`, `CZ`, three times over, times `λ_p² = (-1)^{(p-1)/2}`. -/
def SWAP : Circ 2 :=
  par H H ⨾ CZ ⨾ par H H ⨾ CZ ⨾ par H H ⨾ CZ ⨾ neg1 p ^ ((p - 1) / 2)

/-- (T6) `CX`, control on the top wire, target on the bottom wire: `H` on
the target, `CZ`, `H³` on the target. -/
def CX : Circ 2 := bot H ⨾ CZ ⨾ bot (H ^ 3)

/-- `CZ` on the bottom two of three wires. -/
def CZ₀₁ : Circ 3 := bot2 CZ

/-- `CZ` on the top two of three wires. -/
def CZ₁₂ : Circ 3 := top CZ

/-- The swap of the bottom two of three wires. -/
def SWAP₀₁ : Circ 3 := bot2 (SWAP p)

/-- The swap of the top two of three wires. -/
def SWAP₁₂ : Circ 3 := top (SWAP p)

/-- `CX` from the top wire to the middle wire. -/
def CX₂₁ : Circ 3 := top (CX)

/-- (T7) The remote `CZ` on the top and bottom wires: the bottom swap, `CZ`
on the top two wires, the bottom swap. -/
def CZ₀₂ : Circ 3 := SWAP₀₁ p ⨾ CZ₁₂ ⨾ SWAP₀₁ p

end Derived

/-! ### The rules of Figure 1 -/

/-- The sixteen rules of Figure 1, for the odd prime `p` and the chosen
generator `g` of `ℤ_p^*`: `Rule p g k w v` is the rule `w = v` between
`k`-wire circuits. -/
inductive Rule (p : ℕ) [Fact p.Prime] (g : ZMod p) : (k : ℕ) → Circ k → Circ k → Prop
  /-- (C0) `(-ω)^{2p} = 1`. -/
  | C0 : Rule p g 0 (negω ^ (2 * p)) 1
  /-- (C1) `S^p = 1`. -/
  | C1 : Rule p g 1 (S ^ p) 1
  /-- (C2) `H² = M_{-1} · (-1)^{(p-1)/2}`. -/
  | C2 : Rule p g 1 (H ^ 2) (M p (-1) ⨾ neg1 p ^ ((p - 1) / 2))
  /-- (C3) `(M_g)^k = M_{g^k}`, `k ∈ ℤ_p`. -/
  | C3 (k : ZMod p) : Rule p g 1 (M p g ^ k.val) (M p (g ^ k.val))
  /-- (C4) `S ⨾ M_g = M_g ⨾ S^{g^{-2}} ⨾ Z^{(1-g)/(2g²)}`. -/
  | C4 : Rule p g 1 (S ⨾ M p g)
      (M p g ⨾ S ^ ((g ^ 2)⁻¹).val ⨾ Z p ^ ((1 - g) / (2 * g ^ 2)).val)
  /-- (C5) `H² ⨾ S ⨾ H² ⨾ S = S ⨾ H² ⨾ S ⨾ H²`. -/
  | C5 : Rule p g 1 (H ^ 2 ⨾ S ⨾ H ^ 2 ⨾ S) (S ⨾ H ^ 2 ⨾ S ⨾ H ^ 2)
  /-- (C6) `CZ^p = 1`. -/
  | C6 : Rule p g 2 (CZ ^ p) 1
  /-- (C7) `SWAP² = 1`. -/
  | C7 : Rule p g 2 (SWAP p ^ 2) 1
  /-- (C8) `S` on the top wire, then `CZ`, is `CZ`, then `S` on the top wire. -/
  | C8 : Rule p g 2 (top S ⨾ CZ) (CZ ⨾ top S)
  /-- (C9) `M_g` on the top wire, then `CZ`, is `CZ^g`, then `M_g` on the top wire. -/
  | C9 : Rule p g 2 (top (M p g) ⨾ CZ) (CZ ^ g.val ⨾ top (M p g))
  /-- (C10) `S` on the top wire, then the swap, is the swap, then `S` on the
  bottom wire. -/
  | C10 : Rule p g 2 (top S ⨾ SWAP p) (SWAP p ⨾ bot S)
  /-- (C11) `H` on the top wire, then the swap, is the swap, then `H` on the
  bottom wire. -/
  | C11 : Rule p g 2 (top H ⨾ SWAP p) (SWAP p ⨾ bot H)
  /-- (C12) `CX`, `S` on the bottom wire, `CX^{-1}`, then `S^{-1}` on both
  wires, is `CZ`. -/
  | C12 : Rule p g 2 (CX ⨾ bot S ⨾ CX ^ (p - 1) ⨾ top (S ^ (p - 1)) ⨾ bot (S ^ (p - 1))) CZ
  /-- (C13) The braid relation of the swaps. -/
  | C13 : Rule p g 3 (SWAP₁₂ p ⨾ SWAP₀₁ p ⨾ SWAP₁₂ p) (SWAP₀₁ p ⨾ SWAP₁₂ p ⨾ SWAP₀₁ p)
  /-- (C14) `CZ` on the bottom two wires, then the top swap and the bottom
  swap, is the two swaps, then `CZ` on the top two wires. -/
  | C14 : Rule p g 3 (CZ₀₁ ⨾ SWAP₁₂ p ⨾ SWAP₀₁ p) (SWAP₁₂ p ⨾ SWAP₀₁ p ⨾ CZ₁₂)
  /-- (C15) `CX` from the top wire to the middle wire, then `CZ` on the
  bottom two wires, is `CZ` on the bottom two wires, the same `CX`, then
  the remote `CZ` (T7). -/
  | C15 : Rule p g 3 (CX₂₁ ⨾ CZ₀₁) (CZ₀₁ ⨾ CX₂₁ ⨾ CZ₀₂ p)

/-- The theory of `n`-qudit circuits: the rules of Figure 1 on the bottom
wires of every wider circuit, closed under the structural rules. -/
abbrev Theory (p : ℕ) [Fact p.Prime] (g : ZMod p) : CRel Gate := Lift (Padded (Rule p g))

end QCert.QuditClifford
