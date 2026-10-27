/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Deciding equations between two-qubit Clifford+T words

The value of a word is decided column by column: a column is a vector
`(1/√2)^k (x₀, x₁, x₂, x₃)` with coordinates in ℤ[ω] (`V4`), each
generator acts on it by a few integer operations (`V4.act`), and two such
vectors are compared by cross-multiplying with powers of `√2`
(`V4.eqv`).  `check w v = true`, decided by `decide +kernel`, implies that
`w` and `v` have the same value in `U(4)` (`sem_eq_of_check`).
-/
import QCert.CliffordT2.Semantics
import QCert.CliffordT2.ZOmega

namespace QCert.CliffordT2

open Matrix

/-- The generator matrices written out entry by entry. -/
def matLit : Gen → Matrix (Fin 4) (Fin 4) QOmega
  | .ω => !![ωQ, 0, 0, 0; 0, ωQ, 0, 0; 0, 0, ωQ, 0; 0, 0, 0, ωQ]
  | .H₀ => !![s, 0, s, 0; 0, s, 0, s; s, 0, -s, 0; 0, s, 0, -s]
  | .H₁ => !![s, s, 0, 0; s, -s, 0, 0; 0, 0, s, s; 0, 0, s, -s]
  | .S₀ => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, iQ, 0; 0, 0, 0, iQ]
  | .S₁ => !![1, 0, 0, 0; 0, iQ, 0, 0; 0, 0, 1, 0; 0, 0, 0, iQ]
  | .T₀ => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, ωQ, 0; 0, 0, 0, ωQ]
  | .T₁ => !![1, 0, 0, 0; 0, ωQ, 0, 0; 0, 0, 1, 0; 0, 0, 0, ωQ]
  | .CZ => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

theorem matQ_eq_matLit : ∀ x : Gen, matQ x = matLit x := by decide +kernel

/-- A vector `(1/√2)^k (x₀, x₁, x₂, x₃)` over ℤ[ω]. -/
structure V4 where
  k : ℕ
  x0 : ZOmega
  x1 : ZOmega
  x2 : ZOmega
  x3 : ZOmega
  deriving DecidableEq

namespace V4

open ZOmega

/-- The vector over ℚ(ω). -/
def toVec (v : V4) : Fin 4 → QOmega :=
  ![QOmega.invSqrt2 ^ v.k * toQ v.x0, QOmega.invSqrt2 ^ v.k * toQ v.x1,
    QOmega.invSqrt2 ^ v.k * toQ v.x2, QOmega.invSqrt2 ^ v.k * toQ v.x3]

/-- The action of a generator. -/
def act : Gen → V4 → V4
  | .ω, ⟨k, a, b, c, d⟩ => ⟨k, w * a, w * b, w * c, w * d⟩
  | .H₀, ⟨k, a, b, c, d⟩ => ⟨k + 1, a + c, b + d, a - c, b - d⟩
  | .H₁, ⟨k, a, b, c, d⟩ => ⟨k + 1, a + b, a - b, c + d, c - d⟩
  | .S₀, ⟨k, a, b, c, d⟩ => ⟨k, a, b, i * c, i * d⟩
  | .S₁, ⟨k, a, b, c, d⟩ => ⟨k, a, i * b, c, i * d⟩
  | .T₀, ⟨k, a, b, c, d⟩ => ⟨k, a, b, w * c, w * d⟩
  | .T₁, ⟨k, a, b, c, d⟩ => ⟨k, a, w * b, c, w * d⟩
  | .CZ, ⟨k, a, b, c, d⟩ => ⟨k, a, b, c, -d⟩

/-- The action of a word, the last letter first. -/
def run : List Gen → V4 → V4
  | [], v => v
  | x :: l, v => act x (run l v)

/-- Equality of the values of two vectors. -/
def eqv (u v : V4) : Bool :=
  mulRt2 v.k u.x0 == mulRt2 u.k v.x0 && mulRt2 v.k u.x1 == mulRt2 u.k v.x1 &&
    mulRt2 v.k u.x2 == mulRt2 u.k v.x2 && mulRt2 v.k u.x3 == mulRt2 u.k v.x3

/-- The basis vectors. -/
def basis : Fin 4 → V4
  | 0 => ⟨0, 1, 0, 0, 0⟩
  | 1 => ⟨0, 0, 1, 0, 0⟩
  | 2 => ⟨0, 0, 0, 1, 0⟩
  | 3 => ⟨0, 0, 0, 0, 1⟩

theorem toVec_basis : ∀ j : Fin 4, toVec (basis j) = Pi.single j 1 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem toVec_act (x : Gen) (v : V4) : toVec (act x v) = matQ x *ᵥ toVec v := by
  obtain ⟨k, a, b, c, d⟩ := v
  rw [matQ_eq_matLit]
  have hs : QOmega.invSqrt2 = s := rfl
  cases x <;> funext j <;> fin_cases j <;>
    simp [act, toVec, matLit, mulVec, dotProduct, Fin.sum_univ_four, hs, -Quartic.mul_def,
      -Quartic.add_def, -Quartic.neg_def, -Quartic.sub_def, -Quartic.zero_def,
      -Quartic.one_def] <;> ring

theorem toVec_run (l : List Gen) (v : V4) :
    toVec (run l v) = (l.map matQ).prod *ᵥ toVec v := by
  induction l with
  | nil => simp [run]
  | cons x l ih => rw [run, toVec_act, ih, List.map_cons, List.prod_cons, mulVec_mulVec]

theorem toVec_eq_of_eqv {u v : V4} (h : eqv u v = true) : toVec u = toVec v := by
  simp only [eqv, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  funext j
  fin_cases j
  · exact scaled_eq h0
  · exact scaled_eq h1
  · exact scaled_eq h2
  · exact scaled_eq h3

end V4

/-- The decision procedure: the two words act alike on every basis vector. -/
def check (w v : Word Gen) : Bool :=
  V4.eqv (V4.run w.toList (V4.basis 0)) (V4.run v.toList (V4.basis 0)) &&
  V4.eqv (V4.run w.toList (V4.basis 1)) (V4.run v.toList (V4.basis 1)) &&
  V4.eqv (V4.run w.toList (V4.basis 2)) (V4.run v.toList (V4.basis 2)) &&
  V4.eqv (V4.run w.toList (V4.basis 3)) (V4.run v.toList (V4.basis 3))

theorem lift_matQ_mulVec (w : Word Gen) (j : Fin 4) :
    FreeMonoid.lift matQ w *ᵥ Pi.single j 1 = V4.toVec (V4.run w.toList (V4.basis j)) := by
  rw [V4.toVec_run, V4.toVec_basis, FreeMonoid.lift_apply]

theorem lift_matQ_eq_of_check {w v : Word Gen} (h : check w v = true) :
    FreeMonoid.lift matQ w = FreeMonoid.lift matQ v := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have hc : ∀ j : Fin 4, FreeMonoid.lift matQ w *ᵥ Pi.single j 1 =
      FreeMonoid.lift matQ v *ᵥ Pi.single j 1 := by
    intro j
    rw [lift_matQ_mulVec, lift_matQ_mulVec]
    fin_cases j
    · exact V4.toVec_eq_of_eqv h0
    · exact V4.toVec_eq_of_eqv h1
    · exact V4.toVec_eq_of_eqv h2
    · exact V4.toVec_eq_of_eqv h3
  refine Matrix.ext fun i j => ?_
  have := congrFun (hc j) i
  rw [mulVec_single_one, mulVec_single_one] at this
  exact this

/-- Two words that `check` decides equal have the same value in `U(4)`. -/
theorem sem_eq_of_check {w v : Word Gen} (h : check w v = true) :
    FreeMonoid.lift sem w = FreeMonoid.lift sem v :=
  lift_unitaryQ_eq matQ matQ_unitary (lift_matQ_eq_of_check h)

end QCert.CliffordT2
