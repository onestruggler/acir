/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Direct exact evaluation on a pair of qubits

Evaluate the six pair generators without expanding them into two-level
words. A column is a Gaussian-integer vector times `κ ^ k`, where
`κ = 1 / (1 + i)`. A K gate needs only four sums/differences and one
increment; phase gates permute and negate integer coordinates.
The soundness proof connects this evaluator to the existing matrix
semantics and two-qubit completeness theorem.
-/
import QCert.CliffordCS3.Two.Completeness

namespace QCert.CliffordCS3.Two.Fast

open Matrix

@[ext] structure G where
  re : ℤ
  im : ℤ

namespace G

def add (a b : G) : G := ⟨a.re + b.re, a.im + b.im⟩
def sub (a b : G) : G := ⟨a.re - b.re, a.im - b.im⟩
def phase (a : G) : G := ⟨-a.im, a.re⟩
def gamma (a : G) : G := ⟨a.re - a.im, a.re + a.im⟩
def scale : ℕ → G → G
  | 0, a => a
  | n + 1, a => gamma (scale n a)
def eqb (a b : G) : Bool := a.re == b.re && a.im == b.im
def toQ (a : G) : QOmega := ⟨a.re, 0, a.im, 0⟩

theorem eq_of_eqb {a b : G} (h : eqb a b = true) : a = b := by
  simp only [eqb, Bool.and_eq_true, beq_iff_eq] at h
  exact G.ext h.1 h.2

theorem toQ_add (a b : G) : toQ (add a b) = toQ a + toQ b := by
  ext <;> simp [toQ, add]
theorem toQ_sub (a b : G) : toQ (sub a b) = toQ a - toQ b := by
  ext <;> simp [toQ, sub]
theorem toQ_phase (a : G) : toQ (phase a) = iQ * toQ a := by
  ext <;> simp [toQ, phase, iQ, QOmega.I]
theorem toQ_gamma (a : G) : toQ (gamma a) = (1 + iQ) * toQ a := by
  ext <;> simp [toQ, gamma, iQ, QOmega.I] <;> ring
theorem toQ_scale (n : ℕ) (a : G) : toQ (scale n a) = (1 + iQ) ^ n * toQ a := by
  induction n with
  | zero => simp [scale]
  | succ n ih => rw [scale, toQ_gamma, ih, pow_succ]; ring

theorem scaled_eq_le {k l : ℕ} {a b : G} (hkl : k ≤ l)
    (h : eqb (scale (l - k) a) b = true) :
    κ ^ k * toQ a = κ ^ l * toQ b := by
  have h' := congrArg toQ (eq_of_eqb h)
  rw [toQ_scale] at h'
  calc κ ^ k * toQ a
      = κ ^ k * (κ ^ (l - k) * (1 + iQ) ^ (l - k)) * toQ a := by
        rw [← mul_pow, κ_mul, one_pow, mul_one]
    _ = κ ^ (k + (l - k)) * ((1 + iQ) ^ (l - k) * toQ a) := by rw [pow_add]; ring
    _ = κ ^ l * ((1 + iQ) ^ (l - k) * toQ a) := by rw [Nat.add_sub_of_le hkl]
    _ = κ ^ l * toQ b := by rw [h']

/-- Align only the difference of denominator exponents. -/
def eqScaled (k : ℕ) (a : G) (l : ℕ) (b : G) : Bool :=
  bif Nat.ble k l then eqb (scale (l - k) a) b else eqb (scale (k - l) b) a

theorem scaled_eq {k l : ℕ} {a b : G} (h : eqScaled k a l b = true) :
    κ ^ k * toQ a = κ ^ l * toQ b := by
  cases hkl : Nat.ble k l
  · have hle : ¬ k ≤ l := by
      intro hle
      have ht : Nat.ble k l = true := by simpa only [Nat.ble_eq] using hle
      rw [hkl] at ht
      contradiction
    exact (scaled_eq_le (by omega) (show eqb (scale (k - l) b) a = true from
      by simpa [eqScaled, hkl] using h)).symm
  · exact scaled_eq_le (by simpa using hkl) (by simpa [eqScaled, hkl] using h)

end G

structure V where
  k : ℕ
  a : G
  b : G
  c : G
  d : G

namespace V

def toVec (v : V) : Fin 4 → QOmega :=
  ![κ ^ v.k * v.a.toQ, κ ^ v.k * v.b.toQ, κ ^ v.k * v.c.toQ, κ ^ v.k * v.d.toQ]

def act : Gen2 → V → V
  | .i, ⟨k, a, b, c, d⟩ => ⟨k, a.phase, b.phase, c.phase, d.phase⟩
  | .Ku, ⟨k, a, b, c, d⟩ => ⟨k + 1, a.add c, b.add d, a.sub c, b.sub d⟩
  | .Kl, ⟨k, a, b, c, d⟩ => ⟨k + 1, a.add b, a.sub b, c.add d, c.sub d⟩
  | .Su, ⟨k, a, b, c, d⟩ => ⟨k, a, b, c.phase, d.phase⟩
  | .Sl, ⟨k, a, b, c, d⟩ => ⟨k, a, b.phase, c, d.phase⟩
  | .CS, ⟨k, a, b, c, d⟩ => ⟨k, a, b, c, d.phase⟩

def run : List Gen2 → V → V
  | [], v => v
  | x :: xs, v => act x (run xs v)

def eqv (u v : V) : Bool :=
  G.eqScaled u.k u.a v.k v.a && G.eqScaled u.k u.b v.k v.b &&
  G.eqScaled u.k u.c v.k v.c && G.eqScaled u.k u.d v.k v.d

def basis (j : Fin 4) : V :=
  ⟨0, ⟨if j = 0 then 1 else 0, 0⟩, ⟨if j = 1 then 1 else 0, 0⟩,
    ⟨if j = 2 then 1 else 0, 0⟩, ⟨if j = 3 then 1 else 0, 0⟩⟩

theorem toVec_basis : ∀ j : Fin 4, toVec (basis j) = Pi.single j 1 := by decide +kernel

theorem toVec_eq_of_eqv {u v : V} (h : eqv u v = true) : toVec u = toVec v := by
  simp only [eqv, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  funext j
  fin_cases j
  · exact G.scaled_eq h0
  · exact G.scaled_eq h1
  · exact G.scaled_eq h2
  · exact G.scaled_eq h3

end V

def mat : Gen2 → Matrix (Fin 4) (Fin 4) QOmega
  | .i => diagonal ![iQ, iQ, iQ, iQ]
  | .Ku => !![κ, 0, κ, 0; 0, κ, 0, κ; κ, 0, -κ, 0; 0, κ, 0, -κ]
  | .Kl => !![κ, κ, 0, 0; κ, -κ, 0, 0; 0, 0, κ, κ; 0, 0, κ, -κ]
  | .Su => diagonal ![1, 1, iQ, iQ]
  | .Sl => diagonal ![1, iQ, 1, iQ]
  | .CS => diagonal ![1, 1, 1, iQ]

theorem mat_eq : ∀ x, mat x = FreeMonoid.lift gmat (f2 x) := by decide +kernel

theorem V.toVec_act (x : Gen2) (v : V) : V.toVec (V.act x v) = mat x *ᵥ V.toVec v := by
  obtain ⟨k, a, b, c, d⟩ := v
  cases x <;> funext j <;> fin_cases j <;>
    simp [V.act, V.toVec, mat, mulVec, dotProduct, Fin.sum_univ_four,
      G.toQ_add, G.toQ_sub, G.toQ_phase, pow_succ,
      -Quartic.mul_def, -Quartic.add_def, -Quartic.neg_def,
      -Quartic.sub_def, -Quartic.zero_def, -Quartic.one_def] <;> ring

theorem V.toVec_run (xs : List Gen2) (v : V) :
    V.toVec (V.run xs v) = (xs.map mat).prod *ᵥ V.toVec v := by
  induction xs with
  | nil => simp [V.run]
  | cons x xs ih => rw [V.run, V.toVec_act, ih, List.map_cons, List.prod_cons, mulVec_mulVec]

def check (w v : Word Gen2) : Bool :=
  (List.finRange 4).all fun j => V.eqv (V.run w.toList (V.basis j)) (V.run v.toList (V.basis j))

theorem mat_eq_of_check {w v : Word Gen2} (h : check w v = true) :
    FreeMonoid.lift mat w = FreeMonoid.lift mat v := by
  simp only [check, List.all_eq_true, List.mem_finRange, true_implies] at h
  refine Matrix.ext fun a j => ?_
  have hc : FreeMonoid.lift mat w *ᵥ Pi.single j 1 = FreeMonoid.lift mat v *ᵥ Pi.single j 1 := by
    have e1 := V.toVec_run w.toList (V.basis j)
    have e2 := V.toVec_run v.toList (V.basis j)
    rw [V.toVec_basis] at e1 e2
    rw [FreeMonoid.lift_apply, FreeMonoid.lift_apply, ← e1, ← e2, V.toVec_eq_of_eqv (h j)]
  have := congrFun hc a
  rw [mulVec_single_one, mulVec_single_one] at this
  exact this

theorem lift_mat (w : Word Gen2) : FreeMonoid.lift mat w = FreeMonoid.lift gmat (FreeMonoid.lift f2 w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih => simp only [map_mul, FreeMonoid.lift_eval_of, ih, mat_eq]

theorem derivable_of_check {w v : Word Gen2} (h : check w v = true) : Derivable Rel2 w v := by
  apply complete2
  apply lift_sem_eq_of_gmat
  rw [← lift_mat, ← lift_mat]
  exact mat_eq_of_check h

end QCert.CliffordCS3.Two.Fast
