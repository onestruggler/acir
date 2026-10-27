/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hadamard-Π, §4.2: generators and the relations of Figure 6

Fang, Heunen and Kaarsgaard, *Hadamard-Π: Equational quantum programming*
(POPL 2026, arXiv:2506.06835), §4.2.

The alphabet is the set `𝒢ₙ` of Definition 4.5:

  `𝒢ₙ = { (-1)_[a], X_[b,c], H_[b,c] | 1 ≤ a ≤ n, 1 ≤ b < c ≤ n }`,

the one-level matrix `(-1)` and the two-level matrices `X = [[0,1],[1,0]]`
and `H = (1/√2)[[1,1],[1,-1]]` (Definition 4.4).  **Indices start at 0
here** (the paper's start at 1), so `a b c : Fin n`.  A two-level generator
carries the proof that its indices are increasing, as in `𝒢ₙ`.

The relations are those of Figure 6, whose caption says "The indices are
distinct".  A relation of the figure is a scheme in the letters
`a, b, c, …`; its instances are the assignments of distinct indices to the
letters for which every generator it mentions is in `𝒢ₙ`, i.e. has
increasing indices.  Each constructor of `Fig6` below is one scheme, named
by its printed label, with exactly those side conditions: the order
conditions that make the generators valid, and the remaining
distinctness conditions.  (For instance in (d3) the figure writes
`H_[c,d] H_[a,c] H_[b,d]` and `H_[a,b]`, so `a < b`, `c < d`, `a < c`,
`b < d`, and `b ≠ c` is what is left of distinctness.)

Words are written in the paper's order: the word `G₁ G₂ ⋯ Gℓ` is
`G₁ * G₂ * ⋯ * Gℓ` and denotes the matrix product `G₁ ⋯ Gℓ`
(Definition 4.12).
-/
import QCert.Presentation

namespace QCert.HadamardPi

/-- The generators `𝒢ₙ` of Definition 4.5, indices from 0. -/
inductive Gen (n : ℕ) : Type
  /-- `(-1)_[a]`, the one-level matrix `-1` at index `a`. -/
  | Z (a : Fin n)
  /-- `X_[a,b]` for `a < b`, the two-level matrix `[[0,1],[1,0]]`. -/
  | X (a b : Fin n) (h : a < b)
  /-- `H_[a,b]` for `a < b`, the two-level matrix `(1/√2)[[1,1],[1,-1]]`. -/
  | H (a b : Fin n) (h : a < b)

/-- The one-letter word `(-1)_[a]`. -/
scoped macro "Z_[" a:term "]" : term => `(FreeMonoid.of (Gen.Z $a))
/-- The one-letter word `X_[a,b]`; the order `a < b` is found by `omega`
from the hypotheses in context. -/
scoped macro "X_[" a:term "," b:term "]" : term => `(FreeMonoid.of (Gen.X $a $b (by omega)))
/-- The one-letter word `H_[a,b]`; the order `a < b` is found by `omega`
from the hypotheses in context. -/
scoped macro "H_[" a:term "," b:term "]" : term => `(FreeMonoid.of (Gen.H $a $b (by omega)))

/-- The relations of Figure 6.  All indices are distinct, and every
generator mentioned has increasing indices (see the module docstring). -/
inductive Fig6 {n : ℕ} : WRel (Gen n)
  /-- (a1) `(-1)_[a]² ≈ ε`. -/
  | a1 (a : Fin n) : Fig6 (Z_[a] * Z_[a]) 1
  /-- (a2) `X_[a,b]² ≈ ε`. -/
  | a2 {a b : Fin n} (hab : a < b) : Fig6 (X_[a,b] * X_[a,b]) 1
  /-- (a3) `H_[a,b]² ≈ ε`. -/
  | a3 {a b : Fin n} (hab : a < b) : Fig6 (H_[a,b] * H_[a,b]) 1
  /-- (b1) `(-1)_[a] (-1)_[b] ≈ (-1)_[b] (-1)_[a]`. -/
  | b1 {a b : Fin n} (hab : a ≠ b) : Fig6 (Z_[a] * Z_[b]) (Z_[b] * Z_[a])
  /-- (b2) `(-1)_[a] X_[b,c] ≈ X_[b,c] (-1)_[a]`. -/
  | b2 {a b c : Fin n} (hbc : b < c) (hab : a ≠ b) (hac : a ≠ c) :
      Fig6 (Z_[a] * X_[b,c]) (X_[b,c] * Z_[a])
  /-- (b3) `X_[a,b] X_[c,d] ≈ X_[c,d] X_[a,b]`. -/
  | b3 {a b c d : Fin n} (hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d)
      (hbc : b ≠ c) (hbd : b ≠ d) : Fig6 (X_[a,b] * X_[c,d]) (X_[c,d] * X_[a,b])
  /-- (b4) `(-1)_[a] H_[b,c] ≈ H_[b,c] (-1)_[a]`. -/
  | b4 {a b c : Fin n} (hbc : b < c) (hab : a ≠ b) (hac : a ≠ c) :
      Fig6 (Z_[a] * H_[b,c]) (H_[b,c] * Z_[a])
  /-- (b5) `X_[a,b] H_[c,d] ≈ H_[c,d] X_[a,b]`. -/
  | b5 {a b c d : Fin n} (hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d)
      (hbc : b ≠ c) (hbd : b ≠ d) : Fig6 (X_[a,b] * H_[c,d]) (H_[c,d] * X_[a,b])
  /-- (b6) `H_[a,b] H_[c,d] ≈ H_[c,d] H_[a,b]`. -/
  | b6 {a b c d : Fin n} (hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d)
      (hbc : b ≠ c) (hbd : b ≠ d) : Fig6 (H_[a,b] * H_[c,d]) (H_[c,d] * H_[a,b])
  /-- (c1) `(-1)_[a] X_[a,b] ≈ X_[a,b] (-1)_[b]`. -/
  | c1 {a b : Fin n} (hab : a < b) : Fig6 (Z_[a] * X_[a,b]) (X_[a,b] * Z_[b])
  /-- (c2) `X_[b,c] X_[a,b] ≈ X_[a,b] X_[a,c]`. -/
  | c2 {a b c : Fin n} (hab : a < b) (hbc : b < c) :
      Fig6 (X_[b,c] * X_[a,b]) (X_[a,b] * X_[a,c])
  /-- (c3) `X_[a,c] X_[b,c] ≈ X_[b,c] X_[a,b]`. -/
  | c3 {a b c : Fin n} (hab : a < b) (hbc : b < c) :
      Fig6 (X_[a,c] * X_[b,c]) (X_[b,c] * X_[a,b])
  /-- (c4) `H_[b,c] X_[a,b] ≈ X_[a,b] H_[a,c]`. -/
  | c4 {a b c : Fin n} (hab : a < b) (hbc : b < c) :
      Fig6 (H_[b,c] * X_[a,b]) (X_[a,b] * H_[a,c])
  /-- (c5) `H_[a,c] X_[b,c] ≈ X_[b,c] H_[a,b]`. -/
  | c5 {a b c : Fin n} (hab : a < b) (hbc : b < c) :
      Fig6 (H_[a,c] * X_[b,c]) (X_[b,c] * H_[a,b])
  /-- (d1) `(-1)_[a] (-1)_[b] H_[a,b] ≈ H_[a,b] (-1)_[a] (-1)_[b]`. -/
  | d1 {a b : Fin n} (hab : a < b) :
      Fig6 (Z_[a] * Z_[b] * H_[a,b]) (H_[a,b] * Z_[a] * Z_[b])
  /-- (d2) `(-1)_[b] H_[a,b] ≈ H_[a,b] X_[a,b]`. -/
  | d2 {a b : Fin n} (hab : a < b) : Fig6 (Z_[b] * H_[a,b]) (H_[a,b] * X_[a,b])
  /-- (d3) `(H_[c,d] H_[a,c] H_[b,d])⁴ ≈ H_[a,b] H_[c,d]`. -/
  | d3 {a b c d : Fin n} (hab : a < b) (hcd : c < d) (hac : a < c) (hbd : b < d)
      (hbc : b ≠ c) :
      Fig6 ((H_[c,d] * H_[a,c] * H_[b,d]) ^ 4) (H_[a,b] * H_[c,d])
  /-- (d4) `(H_[a,c] H_[b,d] H_[a,b] H_[a,c] H_[b,d] X_[c,e] X_[d,f])³
  ≈ H_[c,e] H_[d,f] H_[e,f] H_[c,e] H_[d,f] X_[c,e] X_[d,f]`. -/
  | d4 {a b c d e f : Fin n} (hac : a < c) (hbd : b < d) (hab : a < b) (hce : c < e)
      (hdf : d < f) (hef : e < f) (hbc : b ≠ c) (hbe : b ≠ e) (hcd : c ≠ d) (hde : d ≠ e) :
      Fig6 ((H_[a,c] * H_[b,d] * H_[a,b] * H_[a,c] * H_[b,d] * X_[c,e] * X_[d,f]) ^ 3)
        (H_[c,e] * H_[d,f] * H_[e,f] * H_[c,e] * H_[d,f] * X_[c,e] * X_[d,f])

end QCert.HadamardPi
