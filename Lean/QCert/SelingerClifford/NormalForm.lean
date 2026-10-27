/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): normal forms

Definition 4.3 of Selinger's paper, in our wire numbering (wire `0` at the
bottom; the paper numbers qubits from the top, so its first qubit is our
wire `n - 1`).  On `n` wires:

* a *Z-normal* circuit `L⁽ⁿ⁾` acts on the top `m` wires (`1 ≤ m ≤ n`):
  `A_i` on wire `n - m`, then `B_{j₁}, …, B_{j_{m-1}}` on the pairs of wires
  `(n - m, n - m + 1), …, (n - 2, n - 1)`, then `C_k` on wire `n - 1`;
* an *X-normal* circuit `M⁽ⁿ⁾` is `D_{ℓ₁}, …, D_{ℓ_{n-1}}` on the pairs
  `(n - 2, n - 1), …, (0, 1)`, then `E_h` on wire `0`;
* a *normal* circuit is `L⁽ⁿ⁾ M⁽ⁿ⁾` followed by a normal circuit on the top
  `n - 1` wires, ending with a scalar `ω^p` (equation (4.3)).

All three are read in time order, as in the paper's diagrams.
-/
import QCert.SelingerClifford.Boxes
import QCert.SelingerClifford.Derivation

namespace QCert.SelingerClifford

/-- A Z-normal circuit on `n` wires (Definition 4.3). -/
structure ZNormal (n : ℕ) where
  /-- The number of wires the circuit acts on (the top `m`). -/
  m : ℕ
  hm : 1 ≤ m ∧ m ≤ n
  /-- `A_{i + 1}`. -/
  i : Fin 3
  /-- `B_{js p + 1}` on the wires `n - m + p, n - m + p + 1`. -/
  js : Fin (m - 1) → Fin 4
  /-- `C_{k + 1}`. -/
  k : Fin 2

/-- An X-normal circuit on `n` wires (Definition 4.3). -/
structure XNormal (n : ℕ) where
  /-- `D_{ls p + 1}` on the wires `n - 2 - p, n - 1 - p`. -/
  ls : Fin (n - 1) → Fin 4
  /-- `E_{h + 1}`. -/
  h : Fin 4

/-- The word of a Z-normal circuit, in time order. -/
def ZNormal.word {n : ℕ} (L : ZNormal n) : List Lt :=
  bA (L.i + 1) (n - L.m) ++ (List.ofFn fun p : Fin (L.m - 1) =>
    bB (L.js p + 1) (n - L.m + p)).flatten ++ bC (L.k + 1) (n - 1)

/-- The word of an X-normal circuit, in time order. -/
def XNormal.word {n : ℕ} (M : XNormal n) : List Lt :=
  (List.ofFn fun p : Fin (n - 1) => bD (M.ls p + 1) (n - 2 - p)).flatten ++ bE (M.h + 1) 0

/-- Normal circuits (equation (4.3)): `L⁽ⁿ⁾ M⁽ⁿ⁾` followed by a normal
circuit on the top `n - 1` wires; on no wires, a scalar `ω^p`. -/
inductive NF : ℕ → Type
  | scalar (p : Fin 8) : NF 0
  | cons {n : ℕ} (L : ZNormal (n + 1)) (M : XNormal (n + 1)) (N : NF n) : NF (n + 1)

/-- The circuit of a normal form (in operator order: `L` is applied first). -/
def NF.circ : {n : ℕ} → NF n → Circ n
  | _, .scalar p => om ^ (p : ℕ)
  | n + 1, .cons L M N => Circuit.shift N.circ * wc (n + 1) M.word * wc (n + 1) L.word

end QCert.SelingerClifford
