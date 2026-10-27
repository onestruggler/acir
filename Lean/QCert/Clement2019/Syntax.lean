/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clément (2019): generators and the relations (1)–(22)

A. Clément, *A complete set of relations for the real Clifford+T group*,
unpublished notes supervised by N. J. Ross and P. Selinger (March 2019).

Convention 1 of the notes: indices start at 0, as here.  The generators
(Definition 1.5) are the one-level matrices `(-1)[j]` and the two-level
matrices `H[j,k]`, `X[j,k]` (Definitions 1.2 and 1.3) for any `j ≠ k`,
in either order (Remark 1.6).  The relations are those of Definition 3.3,
equations (1)–(21), together with equation (22), which the Note after
Remark 3.4 adds when `n = 2` (Lemma 3.5 derives it from (1)–(15) when
`n ≥ 3`).  "When writing `X[j,k]` or `H[j,k]`, we implicitly assume that
`j ≠ k`": each constructor below carries those conditions and the side
conditions printed next to the equation.  (20) and (21) are stated at the
indices `0, …, 3` and `0, …, 5`, so they exist when `n ≥ 4`, resp.
`n ≥ 6`.

A word `G_q ⋯ G_1` denotes the product `G_q ⋯ G_1` in the written order
(Definition 3.1), as `FreeMonoid.lift` does.
-/
import QCert.Presentation

namespace QCert.Clement2019

/-- The generators of Definition 1.5, indices from 0. -/
inductive Gen (n : ℕ) : Type
  /-- `(-1)[j]`, the one-level matrix `-1` at index `j`. -/
  | Z (j : Fin n)
  /-- `H[j,k]` for `j ≠ k`, the two-level matrix `(1/√2)[[1,1],[1,-1]]`. -/
  | H (j k : Fin n) (h : j ≠ k)
  /-- `X[j,k]` for `j ≠ k`, the two-level matrix `[[0,1],[1,0]]`. -/
  | X (j k : Fin n) (h : j ≠ k)

/-- The one-letter word `(-1)[j]`. -/
scoped macro "Z_[" a:term "]" : term => `(FreeMonoid.of (Gen.Z $a))
/-- The one-letter word `H[j,k]`; `j ≠ k` is found from the context. -/
scoped macro "H_[" a:term "," b:term "]" : term =>
  `(FreeMonoid.of (Gen.H $a $b (by first | omega | simp)))
/-- The one-letter word `X[j,k]`; `j ≠ k` is found from the context. -/
scoped macro "X_[" a:term "," b:term "]" : term =>
  `(FreeMonoid.of (Gen.X $a $b (by first | omega | simp)))

/-- The index `i` of `Fin n`. -/
abbrev idx {n : ℕ} (i : ℕ) (h : i < n := by omega) : Fin n := ⟨i, h⟩

/-- The relations (1)–(22) of Definition 3.3 and the Note after Remark 3.4. -/
inductive Rel {n : ℕ} : WRel (Gen n)
  /-- (1) `(-1)[j]² ≈ ε`. -/
  | r1 (j : Fin n) : Rel (Z_[j] * Z_[j]) 1
  /-- (2) `H[j,k]² ≈ ε`. -/
  | r2 {j k : Fin n} (hjk : j ≠ k) : Rel (H_[j,k] * H_[j,k]) 1
  /-- (3) `X[j,k]² ≈ ε`. -/
  | r3 {j k : Fin n} (hjk : j ≠ k) : Rel (X_[j,k] * X_[j,k]) 1
  /-- (4) `(-1)[j] (-1)[k] ≈ (-1)[k] (-1)[j]` (`j ≠ k`). -/
  | r4 {j k : Fin n} (hjk : j ≠ k) : Rel (Z_[j] * Z_[k]) (Z_[k] * Z_[j])
  /-- (5) `(-1)[l] H[j,k] ≈ H[j,k] (-1)[l]` (`l ≠ j, k`). -/
  | r5 {j k l : Fin n} (hjk : j ≠ k) (hlj : l ≠ j) (hlk : l ≠ k) :
      Rel (Z_[l] * H_[j,k]) (H_[j,k] * Z_[l])
  /-- (6) `(-1)[l] X[j,k] ≈ X[j,k] (-1)[l]` (`l ≠ j, k`). -/
  | r6 {j k l : Fin n} (hjk : j ≠ k) (hlj : l ≠ j) (hlk : l ≠ k) :
      Rel (Z_[l] * X_[j,k]) (X_[j,k] * Z_[l])
  /-- (7) `H[j,k] H[l,t] ≈ H[l,t] H[j,k]` (`{j,k} ∩ {l,t} = ∅`). -/
  | r7 {j k l t : Fin n} (hjk : j ≠ k) (hlt : l ≠ t) (hjl : j ≠ l) (hjt : j ≠ t) (hkl : k ≠ l)
      (hkt : k ≠ t) : Rel (H_[j,k] * H_[l,t]) (H_[l,t] * H_[j,k])
  /-- (8) `H[j,k] X[l,t] ≈ X[l,t] H[j,k]` (`{j,k} ∩ {l,t} = ∅`). -/
  | r8 {j k l t : Fin n} (hjk : j ≠ k) (hlt : l ≠ t) (hjl : j ≠ l) (hjt : j ≠ t) (hkl : k ≠ l)
      (hkt : k ≠ t) : Rel (H_[j,k] * X_[l,t]) (X_[l,t] * H_[j,k])
  /-- (9) `X[j,k] X[l,t] ≈ X[l,t] X[j,k]` (`{j,k} ∩ {l,t} = ∅`). -/
  | r9 {j k l t : Fin n} (hjk : j ≠ k) (hlt : l ≠ t) (hjl : j ≠ l) (hjt : j ≠ t) (hkl : k ≠ l)
      (hkt : k ≠ t) : Rel (X_[j,k] * X_[l,t]) (X_[l,t] * X_[j,k])
  /-- (10) `X[j,k] (-1)[k] ≈ (-1)[j] X[j,k]`. -/
  | r10 {j k : Fin n} (hjk : j ≠ k) : Rel (X_[j,k] * Z_[k]) (Z_[j] * X_[j,k])
  /-- (11) `X[j,k] (-1)[j] ≈ (-1)[k] X[j,k]`. -/
  | r11 {j k : Fin n} (hjk : j ≠ k) : Rel (X_[j,k] * Z_[j]) (Z_[k] * X_[j,k])
  /-- (12) `X[j,k] X[j,l] ≈ X[k,l] X[j,k]` (`k ≠ l`). -/
  | r12 {j k l : Fin n} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
      Rel (X_[j,k] * X_[j,l]) (X_[k,l] * X_[j,k])
  /-- (13) `X[j,k] X[l,j] ≈ X[l,k] X[j,k]` (`k ≠ l`). -/
  | r13 {j k l : Fin n} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
      Rel (X_[j,k] * X_[l,j]) (X_[l,k] * X_[j,k])
  /-- (14) `X[j,k] H[j,l] ≈ H[k,l] X[j,k]` (`k ≠ l`). -/
  | r14 {j k l : Fin n} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
      Rel (X_[j,k] * H_[j,l]) (H_[k,l] * X_[j,k])
  /-- (15) `X[j,k] H[l,j] ≈ H[l,k] X[j,k]` (`k ≠ l`). -/
  | r15 {j k l : Fin n} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
      Rel (X_[j,k] * H_[l,j]) (H_[l,k] * X_[j,k])
  /-- (16) `(-1)[j] (-1)[k] X[j,k] ≈ X[j,k] (-1)[j] (-1)[k]`. -/
  | r16 {j k : Fin n} (hjk : j ≠ k) : Rel (Z_[j] * Z_[k] * X_[j,k]) (X_[j,k] * Z_[j] * Z_[k])
  /-- (17) `(-1)[j] (-1)[k] H[j,k] ≈ H[j,k] (-1)[j] (-1)[k]`. -/
  | r17 {j k : Fin n} (hjk : j ≠ k) : Rel (Z_[j] * Z_[k] * H_[j,k]) (H_[j,k] * Z_[j] * Z_[k])
  /-- (18) `H[j,k] X[j,k] ≈ (-1)[k] H[j,k]`. -/
  | r18 {j k : Fin n} (hjk : j ≠ k) : Rel (H_[j,k] * X_[j,k]) (Z_[k] * H_[j,k])
  /-- (19) `H[j,k] H[l,t] H[j,l] H[k,t] ≈ H[j,l] H[k,t] H[j,k] H[l,t]` (`j ≠ t`; by
  Remark 3.4 the notation allows `k = l`, where the equation is trivial). -/
  | r19 {j k l t : Fin n} (hjk : j ≠ k) (hlt : l ≠ t) (hjl : j ≠ l) (hkt : k ≠ t) (hjt : j ≠ t) :
      Rel (H_[j,k] * H_[l,t] * H_[j,l] * H_[k,t]) (H_[j,l] * H_[k,t] * H_[j,k] * H_[l,t])
  /-- (20) `H[0,1] H[0,2] H[1,3] H[0,1] (-1)[0] (-1)[1] H[0,2] H[1,3]
  ≈ H[0,2] H[1,3] H[0,1] (-1)[0] (-1)[1] H[0,2] H[1,3] H[0,1]`. -/
  | r20 (hn : 4 ≤ n) :
      Rel (H_[idx 0, idx 1] * H_[idx 0, idx 2] * H_[idx 1, idx 3] * H_[idx 0, idx 1] *
          Z_[idx 0] * Z_[idx 1] * H_[idx 0, idx 2] * H_[idx 1, idx 3])
        (H_[idx 0, idx 2] * H_[idx 1, idx 3] * H_[idx 0, idx 1] * Z_[idx 0] * Z_[idx 1] *
          H_[idx 0, idx 2] * H_[idx 1, idx 3] * H_[idx 0, idx 1])
  /-- (21) `H[0,1] H[0,2] H[1,3] H[0,4] H[1,5] H[0,1] (-1)[0] (-1)[1] H[0,4] H[1,5] H[0,2] H[1,3]
  ≈ H[0,2] H[1,3] H[0,4] H[1,5] H[0,1] (-1)[0] (-1)[1] H[0,4] H[1,5] H[0,2] H[1,3] H[0,1]`. -/
  | r21 (hn : 6 ≤ n) :
      Rel (H_[idx 0, idx 1] * H_[idx 0, idx 2] * H_[idx 1, idx 3] * H_[idx 0, idx 4] *
          H_[idx 1, idx 5] * H_[idx 0, idx 1] * Z_[idx 0] * Z_[idx 1] * H_[idx 0, idx 4] *
          H_[idx 1, idx 5] * H_[idx 0, idx 2] * H_[idx 1, idx 3])
        (H_[idx 0, idx 2] * H_[idx 1, idx 3] * H_[idx 0, idx 4] * H_[idx 1, idx 5] *
          H_[idx 0, idx 1] * Z_[idx 0] * Z_[idx 1] * H_[idx 0, idx 4] * H_[idx 1, idx 5] *
          H_[idx 0, idx 2] * H_[idx 1, idx 3] * H_[idx 0, idx 1])
  /-- (22), added when `n = 2`: `X[j,k] H[j,k] ≈ H[k,j] X[j,k]`. -/
  | r22 (hn : n = 2) {j k : Fin n} (hjk : j ≠ k) : Rel (X_[j,k] * H_[j,k]) (H_[k,j] * X_[j,k])

end QCert.Clement2019
