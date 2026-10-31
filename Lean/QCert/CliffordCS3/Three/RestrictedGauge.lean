/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Reading the local macro alphabet with a changed coset representative
-/
import QCert.CliffordCS3.Three.Gauge
import QCert.CliffordCS3.Three.PhaseDressed

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace QCert.CliffordCS3.Three.RestrictedGauge

open QuotientGroup LocalKZ
noncomputable section

inductive Letter
  | t4 | t5 | t6 | k | z
  deriving DecidableEq

def encode : Letter → Macro.ML
  | .t4 => .T 4 | .t5 => .T 5 | .t6 => .T 6 | .k => .K | .z => .Z

def odd : Letter → Bool
  | .k | .z => true
  | _ => false

def lift : Letter → G
  | .t4 => u (Cert.token 4)
  | .t5 => u (Cert.token 5)
  | .t6 => T
  | .k => A * C
  | .z => C

def H (c : Bool) (x : Letter) : G := u (h c (encode x)).1
def word (xs : List Letter) : Word Macro.ML := FreeMonoid.ofList (xs.map encode)
def correction : G := C ^ 2 * Q

theorem C_Q : Commute C Q := AtomTokens.C_Q

theorem C_fourth : C ^ 4 = 1 := by
  have ht := congrArg sw P_fourth
  simpa only [map_pow, AtomTokens.sw_P, map_one] using ht

theorem correction_square : correction * correction = 1 := by
  change (C ^ 2 * Q) * (C ^ 2 * Q) = 1
  calc
    _ = C ^ 2 * C ^ 2 * (Q * Q) := by rw [mul_assoc, ← mul_assoc Q, (C_Q.pow_left 2).symm.eq]; group
    _ = 1 := by rw [Q_square, mul_one, ← pow_add]; exact C_fourth

theorem correction_C : Commute correction C :=
  (Commute.pow_self C 2).mul_left C_Q.symm

theorem H_state (c : Bool) (x : Letter) : (h c (encode x)).2 = Gauge.next c (odd x) := by
  cases c <;> cases x <;> rfl

theorem run_bridge (c : Bool) (xs : List Letter) :
    u (hstar h c (word xs)).1 = Gauge.run odd H c xs := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih =>
    change u (hstar h c (FreeMonoid.ofList (encode x :: xs.map encode))).1 = _
    rw [FreeMonoid.ofList_cons, hstar_mul, hstar_of]
    change u ((h c (encode x)).1 * (hstar h (h c (encode x)).2 (word xs)).1) = _
    rw [map_mul, H_state, ih]
    rfl

/-- Local identities needed for changing the coset representative. -/
structure Facts : Prop where
  conjugate_A : C * A * C⁻¹ = A ^ 2 * P * Q
  commute_t4 : Commute C (u (Cert.token 4))
  commute_t5 : Commute C (u (Cert.token 5))
  correction_A : Commute correction A
  correction_t4 : Commute correction (u (Cert.token 4))
  correction_t5 : Commute correction (u (Cert.token 5))
  correction_t6 : Commute correction T

theorem letter_equation (F : Facts) (c : Bool) (x : Letter) :
    H c x = C ^ Gauge.bit c * lift x *
      (C ^ Gauge.bit (Gauge.next c (odd x)))⁻¹ * correction ^ Gauge.carry c (odd x) := by
  cases c <;> cases x
  all_goals simp only [Gauge.bit, Gauge.next, Gauge.carry, odd, Bool.false_eq_true,
    Bool.true_eq, Bool.false_and, Bool.true_and, Bool.xor_false, Bool.xor_true,
    Bool.not_false, Bool.not_true, ite_false, ite_true, pow_zero, pow_one,
    inv_one, mul_one, one_mul, lift]
  · rfl
  · rfl
  · rfl
  · change A = A * C * C⁻¹; group
  · change 1 = C * C⁻¹; group
  · change u (Cert.token 4) = C * u (Cert.token 4) * C⁻¹
    rw [F.commute_t4.eq]; group
  · change u (Cert.token 5) = C * u (Cert.token 5) * C⁻¹
    rw [F.commute_t5.eq]; group
  · exact PhaseDressed.C_dresses.symm
  · change A ^ 2 * P = C * (A * C) * correction
    calc
      A ^ 2 * P = A ^ 2 * P * (correction * correction) := by rw [correction_square, mul_one]
      _ = (A ^ 2 * P * Q) * C ^ 2 * correction := by
        have hc : correction = Q * C ^ 2 := (C_Q.pow_left 2).eq
        calc
          _ = (A ^ 2 * P * correction) * correction := by group
          _ = (A ^ 2 * P * (Q * C ^ 2)) * correction :=
            congrArg (fun g : G => (A ^ 2 * P * g) * correction) hc
          _ = _ := by group
      _ = C * (A * C) * correction := by rw [← F.conjugate_A, sq]; group
  · change Q = C * C * correction
    change Q = C * C * (C ^ 2 * Q)
    have hc : C * C * C ^ 2 = 1 := by rw [← sq, ← pow_add]; exact C_fourth
    rw [← mul_assoc, hc, one_mul]

theorem correction_lift (F : Facts) (x : Letter) : Commute correction (lift x) := by
  cases x
  · exact F.correction_t4
  · exact F.correction_t5
  · exact F.correction_t6
  · exact F.correction_A.mul_right correction_C
  · exact correction_C

/-- Equal lifted even macro words of equal odd-letter count have derivable residuals. -/
theorem residuals_equal (F : Facts) (c : Bool) (xs ys : List Letter) (k : Nat)
    (hx : Gauge.count odd xs = 2 * k) (hy : Gauge.count odd ys = 2 * k)
    (he : Gauge.eval lift xs = Gauge.eval lift ys) :
    Derivable Rel (hstar h c (word xs)).1 (hstar h c (word ys)).1 := by
  apply to_derivable
  rw [run_bridge, run_bridge]
  exact Gauge.run_eq_of_even C correction lift odd H correction_C (correction_lift F)
    (letter_equation F) c xs ys k hx hy he

end
end QCert.CliffordCS3.Three.RestrictedGauge
