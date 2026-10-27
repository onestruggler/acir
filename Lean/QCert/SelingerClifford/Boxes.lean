/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): the gates A–E

The gates `A_i`, `B_j`, `C_k`, `D_ℓ`, `E_h` of Figure 1 (Definition 4.2), as
words of letters in time order, in our wire numbering (wire `0` at the
bottom).  `bA i a`, `bC k a`, `bE h a` act on wire `a`; `bB j a` and
`bD ℓ a` on wires `a, a + 1`; the paper numbers qubits from the top, so
its upper qubit of a two-qubit gate is our wire `a + 1`.  `bX a` is
`X = HSSH`.
-/
import QCert.SelingerClifford.Letters

namespace QCert.SelingerClifford

/-- `X = HSSH` on wire `a`. -/
def bX (a : ℕ) : List Lt := [.H a, .S a, .S a, .H a]

/-- `A_i` on wire `a`: `A₁ = I`, `A₂ = H`, `A₃ = HSH`. -/
def bA : ℕ → ℕ → List Lt
  | 2, a => [.H a]
  | 3, a => [.H a, .S a, .H a]
  | _, _ => []

/-- `B_j` on wires `a, a + 1`. -/
def bB : ℕ → ℕ → List Lt
  | 1, a => [.H a, .CZ a, .H a, .H (a + 1), .CZ a, .H (a + 1), .H a, .CZ a]
  | 2, a => [.CZ a, .H (a + 1), .H a, .CZ a]
  | 3, a => [.H (a + 1), .S (a + 1), .CZ a, .H (a + 1), .H a, .CZ a]
  | 4, a => [.H (a + 1), .CZ a, .H (a + 1), .H a, .CZ a]
  | _, _ => []

/-- `C_k` on wire `a`: `C₁ = I`, `C₂ = HSSH`. -/
def bC : ℕ → ℕ → List Lt
  | 2, a => [.H a, .S a, .S a, .H a]
  | _, _ => []

/-- `D_ℓ` on wires `a, a + 1`. -/
def bD : ℕ → ℕ → List Lt
  | 1, a => [.CZ a, .H (a + 1), .H a, .CZ a, .H (a + 1), .H a, .CZ a, .H a]
  | 2, a => [.H (a + 1), .CZ a, .H (a + 1), .H a, .CZ a, .H a]
  | 3, a => [.H (a + 1), .H a, .S a, .CZ a, .H (a + 1), .H a, .CZ a, .H a]
  | 4, a => [.H (a + 1), .H a, .CZ a, .H (a + 1), .H a, .CZ a, .H a]
  | _, _ => []

/-- `E_h` on wire `a`: `S^{h-1}`. -/
def bE : ℕ → ℕ → List Lt
  | 2, a => [.S a]
  | 3, a => [.S a, .S a]
  | 4, a => [.S a, .S a, .S a]
  | _, _ => []

end QCert.SelingerClifford
