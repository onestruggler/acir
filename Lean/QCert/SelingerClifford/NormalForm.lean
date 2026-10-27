/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): normal forms

Definition 4.3 of Selinger's paper, in our wire numbering (wire `0` at the
bottom; the paper numbers qubits from the top, so its first qubit is our
wire `n - 1`).  On `n` wires:

* a *Z-normal* circuit `L⁽ⁿ⁾` acts on the top `m` wires (`1 ≤ m ≤ n`), from
  the wire `a = n - m` up: `A_i` on the wire `a`, then `B_{j₁}, …,
  B_{j_{m-1}}` on the pairs of wires `(a, a + 1), …, (n - 2, n - 1)`, then
  `C_k` on the wire `n - 1` (`bA i a ++ BC a js k`);
* an *X-normal* circuit `M⁽ⁿ⁾` is `D_{ℓ₁}, …, D_{ℓ_{n-1}}` on the pairs
  `(n - 2, n - 1), …, (0, 1)`, then `E_h` on the wire `0` (`DC ls h`);
* a *normal* circuit is `L⁽ⁿ⁾ M⁽ⁿ⁾` followed by a normal circuit on the top
  `n - 1` wires, ending with a scalar `ω^p` (equation (4.3)).

All three are read in time order, as in the paper's diagrams.  Box indices
are stored from `0` (`A_{i+1}` for `i : Fin 3`).
-/
import QCert.SelingerClifford.Dirty

namespace QCert.SelingerClifford

/-- A Z-normal circuit on `n` wires (Definition 4.3): `A_{i+1}` on the wire
`a`, the ladder `B_{js₁+1}, …` from the wire `a` up, and `C_{k+1}` on the top
wire. -/
structure ZNormal (n : ℕ) where
  /-- The lowest wire the circuit acts on (`n - m`). -/
  a : ℕ
  i : Fin 3
  js : List (Fin 4)
  k : Fin 2
  h : a + js.length + 1 = n

/-- An X-normal circuit on `n` wires (Definition 4.3): the ladder
`D_{ls₁+1}, …` from the top pair of wires down, and `E_{h+1}` on the wire
`0`. -/
structure XNormal (n : ℕ) where
  ls : List (Fin 4)
  h : Fin 4
  hl : ls.length + 1 = n

/-- The word of a Z-normal circuit, in time order. -/
def ZNormal.word {n : ℕ} (L : ZNormal n) : List Lt := bA (L.i.val + 1) L.a ++ BC L.a L.js L.k

/-- The word of an X-normal circuit, in time order. -/
def XNormal.word {n : ℕ} (M : XNormal n) : List Lt := DC M.ls M.h

/-- Normal circuits (equation (4.3)): `L⁽ⁿ⁾ M⁽ⁿ⁾` followed by a normal
circuit on the top `n - 1` wires; on no wires, a scalar `ω^p`. -/
inductive NF : ℕ → Type
  | scalar (p : Fin 8) : NF 0
  | cons {n : ℕ} (L : ZNormal (n + 1)) (M : XNormal (n + 1)) (N : NF n) : NF (n + 1)

/-- The word of a normal circuit, in time order. -/
def NF.word : {n : ℕ} → NF n → List Lt
  | _, .scalar p => List.replicate p.val .om
  | _, .cons L M N => L.word ++ M.word ++ N.word.map Lt.up

/-- The circuit of a normal form. -/
def NF.circ {n : ℕ} (N : NF n) : Circ n := wc n N.word

end QCert.SelingerClifford
