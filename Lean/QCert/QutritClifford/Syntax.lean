/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Qutrit Clifford circuits: gates and the rules of Figure 1

Li, Mosca, Ross, van de Wetering and Zhao, *A Complete and Natural Rule Set
for Multi-Qutrit Clifford Circuits* (QPL 2025, arXiv:2508.14670).

The generators are the scalar `-ω`, the one-qutrit gates `H` and `S` and the
two-qutrit gate `CZ` (§2.1); the derived generators of Figure 5 are
abbreviations (`D1`–`D11`).  The relations are the eighteen rules
`C1`–`C18` of Figure 1, each stated on the wires it is drawn on
(`Rule k w v` for `k`-wire circuits), and the theory is their closure
`Lift (Padded Rule)` under the structural rules, which the paper assumes
("the standard spatial relations which allow us to commute gates acting on
disjoint subsets of qutrits", Figure 1; Remark 2.5).

**Wires.** The paper draws a circuit with its first qutrit on top.  The
framework numbers wires from the bottom: on `k` wires the paper's top wire
is wire `k - 1` and its bottom wire is wire `0`.  So on two wires `CX` has
its control on wire 1 and its target on wire 0 (`CX |x, y⟩ = |x, x + y⟩`,
`x` the top qutrit), and `XC` the reverse.

**Order.** The paper writes circuits left to right in time order.  Words
of the framework are in operator order (`w * v` applies `v` first), so a
circuit drawn left to right as `a, b` is written `a ⨾ b`, which is
`b * a`.  Every rule below reads left to right as its figure.  A global
phase drawn as `· λ` at the end of a circuit (Figure 6(a)) is a scalar
gate composed with it.
-/
import QCert.Circuit.Basic

namespace QCert.QutritClifford

/-- The gates of qutrit Clifford circuits (§2.1): the scalar `-ω`
(`ω = e^{2πi/3}`), the Hadamard gate `H`, the phase gate `S` and the
controlled-Z gate `CZ` (Definition 2.4). -/
inductive Gate : ℕ → Type
  /-- The scalar `-ω`, a primitive sixth root of unity. -/
  | negω : Gate 0
  /-- The Hadamard gate. -/
  | H : Gate 1
  /-- The phase gate `S = diag(ω, ω, 1)`. -/
  | S : Gate 1
  /-- The controlled-Z gate. -/
  | CZ : Gate 2

/-- Qutrit Clifford circuits on `n` wires. -/
abbrev Circ (n : ℕ) := Circuit Gate n

/-- Composition in time order: `a ⨾ b` is `a` followed by `b`, the circuit
`b * a`. -/
def seq {n : ℕ} (a b : Circ n) : Circ n := b * a

@[inherit_doc] scoped infixl:70 " ⨾ " => seq

theorem seq_def {n : ℕ} (a b : Circ n) : a ⨾ b = b * a := rfl

/-- A circuit on the top `n` of `n + 1` wires. -/
abbrev top {n : ℕ} (c : Circ n) : Circ (n + 1) := Circuit.shift c

/-- A one-wire circuit on the bottom wire (wire `0`) of `n + 1` wires. -/
abbrev bot {n : ℕ} (c : Circ 1) : Circ (n + 1) := Circuit.pad n c

/-- A two-wire circuit on the bottom two wires of `n + 2` wires. -/
abbrev bot2 {n : ℕ} (c : Circ 2) : Circ (n + 2) := Circuit.pad n c

/-! ### Generators -/

/-- The scalar `-ω`, at any width. -/
def negω {n : ℕ} : Circ n := Circuit.g0 Gate.negω

/-- The Hadamard gate on one wire. -/
def H : Circ 1 := Circuit.g1 Gate.H

/-- The phase gate on one wire. -/
def S : Circ 1 := Circuit.g1 Gate.S

/-- The controlled-Z gate on two wires. -/
def CZ : Circ 2 := Circuit.g2 Gate.CZ

/-! ### Derived generators (Figure 5) -/

/-- (D1) `-1 = (-ω)³`. -/
def neg1 {n : ℕ} : Circ n := negω ^ 3

/-- (D2) `ω = (-ω)⁴`. -/
def ω {n : ℕ} : Circ n := negω ^ 4

/-- (D3) `S' = H² ⨾ S ⨾ H²`. -/
def S' : Circ 1 := H ^ 2 ⨾ S ⨾ H ^ 2

/-- (D4) `X = H ⨾ S ⨾ H² ⨾ S² ⨾ H`. -/
def X : Circ 1 := H ⨾ S ⨾ H ^ 2 ⨾ S ^ 2 ⨾ H

/-- (D5) `Z = H² ⨾ S² ⨾ H² ⨾ S`. -/
def Z : Circ 1 := H ^ 2 ⨾ S ^ 2 ⨾ H ^ 2 ⨾ S

/-- Two one-wire circuits side by side: `a` on the top wire, `b` on the
bottom wire. -/
def par (a b : Circ 1) : Circ 2 := top a * bot b

/-- (D6) The swap: `H ⊗ H`, `CZ`, three times over. -/
def SWAP : Circ 2 :=
  par H H ⨾ CZ ⨾ par H H ⨾ CZ ⨾ par H H ⨾ CZ

/-- (D7) `CX`, control on the top wire (wire 1), target on the bottom wire
(wire 0): `H` on the target, `CZ`, `H³` on the target. -/
def CX : Circ 2 := bot H ⨾ CZ ⨾ bot (H ^ 3)

/-- (D8) `XC`, target on the top wire (wire 1), control on the bottom wire
(wire 0): `H` on the target, `CZ`, `H³` on the target. -/
def XC : Circ 2 := top H ⨾ CZ ⨾ top (H ^ 3)

/-! ### Gates on three wires

The paper's top, middle and bottom wires are wires 2, 1 and 0. -/

/-- `CZ` on the bottom two wires (the middle and bottom qutrits). -/
def CZ₀₁ : Circ 3 := bot2 CZ

/-- `CZ` on the top two wires (the top and middle qutrits). -/
def CZ₁₂ : Circ 3 := top CZ

/-- The swap of the bottom two wires. -/
def SWAP₀₁ : Circ 3 := bot2 SWAP

/-- The swap of the top two wires. -/
def SWAP₁₂ : Circ 3 := top SWAP

/-- `CX` with control on the top wire and target on the middle wire. -/
def CX₂₁ : Circ 3 := top CX

/-- (D9) The remote `CZ` on the top and bottom wires: the bottom swap, `CZ`
on the top two wires, the bottom swap. -/
def CZ₀₂ : Circ 3 := SWAP₀₁ ⨾ CZ₁₂ ⨾ SWAP₀₁

/-- (D10) The remote `CX`, control on the top wire and target on the
bottom wire: the bottom swap, `CX` on the top two wires, the bottom swap. -/
def CX₂₀ : Circ 3 := SWAP₀₁ ⨾ CX₂₁ ⨾ SWAP₀₁

/-- (D11) The remote `XC`, target on the top wire and control on the bottom
wire: the top swap, `XC` on the bottom two wires, the top swap. -/
def XC₂₀ : Circ 3 := SWAP₁₂ ⨾ bot2 XC ⨾ SWAP₁₂

/-! ### The rules of Figure 1 -/

/-- The eighteen rules of Figure 1, each on the wires it is drawn on:
`Rule k w v` is the rule `w = v` between `k`-wire circuits.  `g^m` is `m`
copies of `g` (Figure 6(b)). -/
inductive Rule : (k : ℕ) → Circ k → Circ k → Prop
  /-- (C1) `(-ω)⁶ = 1`. -/
  | C1 : Rule 0 (negω ^ 6) 1
  /-- (C2) `H⁴ = 1`. -/
  | C2 : Rule 1 (H ^ 4) 1
  /-- (C3) `S³ = 1`. -/
  | C3 : Rule 1 (S ^ 3) 1
  /-- (C4) `S² ⨾ H ⨾ S² ⨾ H ⨾ S² ⨾ H = -ω`. -/
  | C4 : Rule 1 (S ^ 2 ⨾ H ⨾ S ^ 2 ⨾ H ⨾ S ^ 2 ⨾ H) negω
  /-- (C5) `S ⨾ S' = S' ⨾ S`. -/
  | C5 : Rule 1 (S ⨾ S') (S' ⨾ S)
  /-- (C6) `CZ³ = 1`. -/
  | C6 : Rule 2 (CZ ^ 3) 1
  /-- (C7) `SWAP² = 1`. -/
  | C7 : Rule 2 (SWAP ^ 2) 1
  /-- (C8) `S` on the top wire, then `CZ`, is `CZ`, then `S` on the top
  wire. -/
  | C8 : Rule 2 (top S ⨾ CZ) (CZ ⨾ top S)
  /-- (C9) `H²` on the top wire, then `CZ²`, is `CZ`, then `H²` on the top
  wire. -/
  | C9 : Rule 2 (top (H ^ 2) ⨾ CZ ⨾ CZ) (CZ ⨾ top (H ^ 2))
  /-- (C10) `S` on the top wire, then the swap, is the swap, then `S` on the
  bottom wire. -/
  | C10 : Rule 2 (top S ⨾ SWAP) (SWAP ⨾ bot S)
  /-- (C11) `H` on the top wire, then the swap, is the swap, then `H` on the
  bottom wire. -/
  | C11 : Rule 2 (top H ⨾ SWAP) (SWAP ⨾ bot H)
  /-- (C12) `CZ ⨾ SWAP = SWAP ⨾ CZ`. -/
  | C12 : Rule 2 (CZ ⨾ SWAP) (SWAP ⨾ CZ)
  /-- (C13) `S` on the top wire, then `XC`, is `XC`, `CZ`, then `S` on the
  top wire and `S'` on the bottom wire, times `ω²`. -/
  | C13 : Rule 2 (top S ⨾ XC) (XC ⨾ CZ ⨾ top S ⨾ bot S' ⨾ ω ^ 2)
  /-- (C14) `CZ ⨾ XC` is `XC`, `CZ`, then `S'` and `S` on the bottom wire,
  times `ω`. -/
  | C14 : Rule 2 (CZ ⨾ XC) (XC ⨾ CZ ⨾ bot S' ⨾ bot S ⨾ ω)
  /-- (C15) `CZ` on the bottom two wires and `CZ` on the top two wires
  commute. -/
  | C15 : Rule 3 (CZ₀₁ ⨾ CZ₁₂) (CZ₁₂ ⨾ CZ₀₁)
  /-- (C16) The braid relation of the swaps. -/
  | C16 : Rule 3 (SWAP₁₂ ⨾ SWAP₀₁ ⨾ SWAP₁₂) (SWAP₀₁ ⨾ SWAP₁₂ ⨾ SWAP₀₁)
  /-- (C17) `CZ` on the bottom two wires, then the top swap and the bottom
  swap, is the two swaps, then `CZ` on the top two wires. -/
  | C17 : Rule 3 (CZ₀₁ ⨾ SWAP₁₂ ⨾ SWAP₀₁) (SWAP₁₂ ⨾ SWAP₀₁ ⨾ CZ₁₂)
  /-- (C18) `CX` from the top wire to the middle wire, then `CZ` on the
  bottom two wires, is `CZ` on the bottom two wires, the same `CX`, then
  the remote `CZ` on the top and bottom wires (D9). -/
  | C18 : Rule 3 (CX₂₁ ⨾ CZ₀₁) (CZ₀₁ ⨾ CX₂₁ ⨾ CZ₀₂)

/-- The theory of `n`-qutrit circuits: the rules of Figure 1 on the bottom
wires of every wider circuit, closed under the structural rules. -/
abbrev Theory : CRel Gate := Lift (Padded Rule)

end QCert.QutritClifford
