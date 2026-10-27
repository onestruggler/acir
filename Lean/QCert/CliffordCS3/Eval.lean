/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Deciding equations between three-qubit Clifford+CS words

As for two-qubit Clifford+T (`QCert.CliffordT2.Eval`): a column is a
vector `(1/√2)^k (x₀, …, x₇)` with coordinates in ℤ[ω] (`V8`), each
generator acts by a few integer operations (`V8.act`; `K = ω⁷ H` with
`ω⁷ = (1 - i)/√2`), and `check w v = true`, decided by `decide +kernel`,
implies that `w` and `v` have the same value in `U(8)` (`sem_eq_of_check`).
-/
import QCert.CliffordCS3.Semantics
import QCert.CliffordT2.ZOmega

namespace QCert.CliffordCS3

open Matrix

theorem matQ_K₀ : matQ .K₀ = matLit .K₀ := matQ_eq_matLit _
theorem matQ_K₁ : matQ .K₁ = matLit .K₁ := matQ_eq_matLit _
theorem matQ_K₂ : matQ .K₂ = matLit .K₂ := matQ_eq_matLit _
theorem matQ_S₀ : matQ .S₀ = diagonal ![1, 1, 1, 1, iQ, iQ, iQ, iQ] := by
  rw [matQ_eq_matLit]; decide +kernel
theorem matQ_S₁ : matQ .S₁ = diagonal ![1, 1, iQ, iQ, 1, 1, iQ, iQ] := by
  rw [matQ_eq_matLit]; decide +kernel
theorem matQ_S₂ : matQ .S₂ = diagonal ![1, iQ, 1, iQ, 1, iQ, 1, iQ] := by
  rw [matQ_eq_matLit]; decide +kernel
theorem matQ_CS₀₁ : matQ .CS₀₁ = diagonal ![1, 1, 1, 1, 1, 1, iQ, iQ] := by
  rw [matQ_eq_matLit]; decide +kernel
theorem matQ_CS₁₂ : matQ .CS₁₂ = diagonal ![1, 1, 1, iQ, 1, 1, 1, iQ] := by
  rw [matQ_eq_matLit]; decide +kernel

/-- A vector `(1/√2)^k (x₀, …, x₇)` over ℤ[ω]. -/
structure V8 where
  k : ℕ
  x0 : ZOmega
  x1 : ZOmega
  x2 : ZOmega
  x3 : ZOmega
  x4 : ZOmega
  x5 : ZOmega
  x6 : ZOmega
  x7 : ZOmega
  deriving DecidableEq

namespace V8

open ZOmega

/-- `ω⁷ = -ω³`. -/
def m : ZOmega := ⟨0, 0, 0, -1⟩

theorem toQ_m_mul_invSqrt2 : toQ m * QOmega.invSqrt2 = κ := by decide +kernel

/-- The vector over ℚ(ω). -/
def toVec (v : V8) : Fin 8 → QOmega :=
  ![QOmega.invSqrt2 ^ v.k * toQ v.x0, QOmega.invSqrt2 ^ v.k * toQ v.x1,
    QOmega.invSqrt2 ^ v.k * toQ v.x2, QOmega.invSqrt2 ^ v.k * toQ v.x3,
    QOmega.invSqrt2 ^ v.k * toQ v.x4, QOmega.invSqrt2 ^ v.k * toQ v.x5,
    QOmega.invSqrt2 ^ v.k * toQ v.x6, QOmega.invSqrt2 ^ v.k * toQ v.x7]

/-- The action of a generator. -/
def act : Gen → V8 → V8
  | .i, ⟨k, a, b, c, d, e, f, g, h⟩ => ⟨k, i * a, i * b, i * c, i * d, i * e, i * f, i * g, i * h⟩
  | .K₀, ⟨k, a, b, c, d, e, f, g, h⟩ =>
    ⟨k + 1, m * (a + e), m * (b + f), m * (c + g), m * (d + h),
      m * (a - e), m * (b - f), m * (c - g), m * (d - h)⟩
  | .K₁, ⟨k, a, b, c, d, e, f, g, h⟩ =>
    ⟨k + 1, m * (a + c), m * (b + d), m * (a - c), m * (b - d),
      m * (e + g), m * (f + h), m * (e - g), m * (f - h)⟩
  | .K₂, ⟨k, a, b, c, d, e, f, g, h⟩ =>
    ⟨k + 1, m * (a + b), m * (a - b), m * (c + d), m * (c - d),
      m * (e + f), m * (e - f), m * (g + h), m * (g - h)⟩
  | .S₀, ⟨k, a, b, c, d, e, f, g, h⟩ => ⟨k, a, b, c, d, i * e, i * f, i * g, i * h⟩
  | .S₁, ⟨k, a, b, c, d, e, f, g, h⟩ => ⟨k, a, b, i * c, i * d, e, f, i * g, i * h⟩
  | .S₂, ⟨k, a, b, c, d, e, f, g, h⟩ => ⟨k, a, i * b, c, i * d, e, i * f, g, i * h⟩
  | .CS₀₁, ⟨k, a, b, c, d, e, f, g, h⟩ => ⟨k, a, b, c, d, e, f, i * g, i * h⟩
  | .CS₁₂, ⟨k, a, b, c, d, e, f, g, h⟩ => ⟨k, a, b, c, i * d, e, f, g, i * h⟩

/-- The action of a word, the last letter first. -/
def run : List Gen → V8 → V8
  | [], v => v
  | x :: l, v => act x (run l v)

/-- Equality of the values of two vectors. -/
def eqv (u v : V8) : Bool :=
  mulRt2 v.k u.x0 == mulRt2 u.k v.x0 && mulRt2 v.k u.x1 == mulRt2 u.k v.x1 &&
    mulRt2 v.k u.x2 == mulRt2 u.k v.x2 && mulRt2 v.k u.x3 == mulRt2 u.k v.x3 &&
    mulRt2 v.k u.x4 == mulRt2 u.k v.x4 && mulRt2 v.k u.x5 == mulRt2 u.k v.x5 &&
    mulRt2 v.k u.x6 == mulRt2 u.k v.x6 && mulRt2 v.k u.x7 == mulRt2 u.k v.x7

/-- The basis vectors. -/
def basis (j : Fin 8) : V8 :=
  ⟨0, if j = 0 then 1 else 0, if j = 1 then 1 else 0, if j = 2 then 1 else 0,
    if j = 3 then 1 else 0, if j = 4 then 1 else 0, if j = 5 then 1 else 0,
    if j = 6 then 1 else 0, if j = 7 then 1 else 0⟩

theorem toVec_basis : ∀ j : Fin 8, toVec (basis j) = Pi.single j 1 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem toVec_act (x : Gen) (v : V8) : toVec (act x v) = matQ x *ᵥ toVec v := by
  obtain ⟨k, a, b, c, d, e, f, g, h⟩ := v
  have hκ : κ = toQ m * QOmega.invSqrt2 := toQ_m_mul_invSqrt2.symm
  cases x
  case i =>
    rw [show matQ .i = iQ • (1 : Matrix (Fin 8) (Fin 8) QOmega) from rfl, smul_mulVec,
      one_mulVec]
    funext j; fin_cases j <;> simp [act, toVec,
        -Quartic.mul_def, -Quartic.add_def, -Quartic.neg_def,
        -Quartic.sub_def, -Quartic.zero_def, -Quartic.one_def] <;> ring
  case K₀ =>
    rw [matQ_K₀]
    funext j; fin_cases j <;>
      simp [act, toVec, matLit, mulVec, dotProduct, Fin.sum_univ_eight, hκ,
        -Quartic.mul_def, -Quartic.add_def, -Quartic.neg_def,
        -Quartic.sub_def, -Quartic.zero_def, -Quartic.one_def] <;> ring
  case K₁ =>
    rw [matQ_K₁]
    funext j; fin_cases j <;>
      simp [act, toVec, matLit, mulVec, dotProduct, Fin.sum_univ_eight, hκ,
        -Quartic.mul_def, -Quartic.add_def, -Quartic.neg_def,
        -Quartic.sub_def, -Quartic.zero_def, -Quartic.one_def] <;> ring
  case K₂ =>
    rw [matQ_K₂]
    funext j; fin_cases j <;>
      simp [act, toVec, matLit, mulVec, dotProduct, Fin.sum_univ_eight, hκ,
        -Quartic.mul_def, -Quartic.add_def, -Quartic.neg_def,
        -Quartic.sub_def, -Quartic.zero_def, -Quartic.one_def] <;> ring
  all_goals
    first
    | rw [matQ_S₀] | rw [matQ_S₁] | rw [matQ_S₂] | rw [matQ_CS₀₁] | rw [matQ_CS₁₂]
    funext j; rw [mulVec_diagonal]; fin_cases j <;> simp [act, toVec,
        -Quartic.mul_def, -Quartic.add_def, -Quartic.neg_def,
        -Quartic.sub_def, -Quartic.zero_def, -Quartic.one_def] <;> ring

theorem toVec_run (l : List Gen) (v : V8) :
    toVec (run l v) = (l.map matQ).prod *ᵥ toVec v := by
  induction l with
  | nil => simp [run]
  | cons x l ih => rw [run, toVec_act, ih, List.map_cons, List.prod_cons, mulVec_mulVec]

theorem toVec_eq_of_eqv {u v : V8} (h : eqv u v = true) : toVec u = toVec v := by
  simp only [eqv, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  funext j
  fin_cases j
  · exact scaled_eq h0
  · exact scaled_eq h1
  · exact scaled_eq h2
  · exact scaled_eq h3
  · exact scaled_eq h4
  · exact scaled_eq h5
  · exact scaled_eq h6
  · exact scaled_eq h7

end V8

/-- The decision procedure: the two words act alike on every basis vector. -/
def check (w v : Word Gen) : Bool :=
  (List.finRange 8).all fun j =>
    V8.eqv (V8.run w.toList (V8.basis j)) (V8.run v.toList (V8.basis j))

theorem lift_matQ_mulVec (w : Word Gen) (j : Fin 8) :
    FreeMonoid.lift matQ w *ᵥ Pi.single j 1 = V8.toVec (V8.run w.toList (V8.basis j)) := by
  rw [V8.toVec_run, V8.toVec_basis, FreeMonoid.lift_apply]

theorem lift_matQ_eq_of_check {w v : Word Gen} (h : check w v = true) :
    FreeMonoid.lift matQ w = FreeMonoid.lift matQ v := by
  simp only [check, List.all_eq_true, List.mem_finRange, true_implies] at h
  refine Matrix.ext fun i j => ?_
  have hc : FreeMonoid.lift matQ w *ᵥ Pi.single j 1 = FreeMonoid.lift matQ v *ᵥ Pi.single j 1 := by
    rw [lift_matQ_mulVec, lift_matQ_mulVec]
    exact V8.toVec_eq_of_eqv (h j)
  have := congrFun hc i
  rw [mulVec_single_one, mulVec_single_one] at this
  exact this

/-- Two words that `check` decides equal have the same value in `U(8)`. -/
theorem sem_eq_of_check {w v : Word Gen} (h : check w v = true) :
    FreeMonoid.lift sem w = FreeMonoid.lift sem v :=
  lift_unitaryQ_eq matQ matQ_unitary (lift_matQ_eq_of_check h)

end QCert.CliffordCS3
