/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma 7.5, the equations (a1)–(a3)

The decoding `D` of Definition 7.3 is computed in the quotient monoid of
two-wire circuits by the theory, as products of the classes of `H`, `Z` on
each wire, `CZ`, `CH` and the swap (`decL`).  A rewriting normalization
there — cancelling involutions, commuting single-qubit gates on different
wires, and moving swaps to the right past single-qubit gates and `CZ`
(Equations (1), (2), (4), (5), (9), (f1), (f2), (g)) — decides the decoded
equations (a1), (a2) and (a3) of Figure 6 at every index: every generator
decodes to an involution (Appendix C.2, "Decoding Equation (a3)").  The
other equations of Figure 6 need the auxiliary equations of Appendix B.2
and are not formalized.
-/
import QCert.RealCliffordCH.TwoQubit

namespace QCert.RealCliffordCH.Two

open Circuit

theorem invc {a : Q2} (ha : a * a = 1) (t : Q2) : a * (a * t) = t := by
  rw [← mul_assoc, ha, one_mul]

theorem h0h0 : h0 * h0 = 1 := by
  rw [← map_mul, ← map_one cl, cl_eq]; exact derivable_rule Rule.e1 1
theorem z0z0 : z0 * z0 = 1 := by
  rw [← map_mul, ← map_one cl, cl_eq]; exact derivable_rule Rule.e2 1
theorem h1h1 : h1 * h1 = 1 := by
  rw [← map_mul, ← map_one cl, cl_eq]; exact derivable_shift (derivable_rule Rule.e1 0)
theorem z1z1 : z1 * z1 = 1 := by
  rw [← map_mul, ← map_one cl, cl_eq]; exact derivable_shift (derivable_rule Rule.e2 0)
theorem cqcq : cq * cq = 1 := by
  rw [← map_mul, ← map_one cl, cl_eq]; exact derivable_rule Rule.e4 0
theorem kqkq : kq * kq = 1 := by
  rw [← map_mul, ← map_one cl, cl_eq]; exact derivable_rule Rule.e5 0

theorem comm01 (a b : Gate 1) : cl (g1 a) * cl (shift (g1 b)) = cl (shift (g1 b)) * cl (g1 a) := by
  rw [← map_mul, ← map_mul, cl_eq]
  exact (Derivable.of (Lift.comm1 a (Gen.gate1 b))).symm

theorem c_h0h1 (t : Q2) : h0 * (h1 * t) = h1 * (h0 * t) := by
  rw [← mul_assoc, comm01 .H .H, mul_assoc]
theorem c_h0z1 (t : Q2) : h0 * (z1 * t) = z1 * (h0 * t) := by
  rw [← mul_assoc, comm01 .H .Z, mul_assoc]
theorem c_z0h1 (t : Q2) : z0 * (h1 * t) = h1 * (z0 * t) := by
  rw [← mul_assoc, comm01 .Z .H, mul_assoc]
theorem c_z0z1 (t : Q2) : z0 * (z1 * t) = z1 * (z0 * t) := by
  rw [← mul_assoc, comm01 .Z .Z, mul_assoc]


/-- The decoding in the quotient, as products of the letters. -/
def decL : G4 → Q2
  | .Z a => match a.val with
    | 0 => x0 * (x1 * (cq * (x0 * x1)))
    | 1 => x1 * (cq * x1)
    | 2 => x0 * (cq * x0)
    | _ => cq
  | .X a b _ => match a.val, b.val with
    | 0, 1 => x1 * (h0 * (cq * (h0 * x1)))
    | 0, 2 => x0 * (sw * (h0 * (cq * (h0 * (sw * x0)))))
    | 0, 3 => x1 * (x0 * sw)
    | 1, 2 => sw
    | 1, 3 => sw * (h0 * (cq * (h0 * sw)))
    | _, _ => h0 * (cq * h0)
  | .H a b _ => match a.val, b.val with
    | 0, 1 => x1 * (kq * x1)
    | 0, 2 => x0 * (sw * (kq * (sw * x0)))
    | 0, 3 => sw * (h0 * (cq * (h0 * (sw * (x1 * (kq * (x1 * (sw * (h0 * (cq * (h0 * sw)))))))))))
    | 1, 2 => h0 * (cq * (h0 * (sw * (kq * (sw * (h0 * (cq * h0)))))))
    | 1, 3 => sw * (kq * sw)
    | _, _ => kq

theorem cl_dec (g : G4) : cl (dec g) = decL g := by
  rcases g with ⟨a⟩ | ⟨a, b, hab⟩ | ⟨a, b, hab⟩ <;> fin_cases a <;> (try fin_cases b) <;>
    simp only [dec, decL, Fin.isValue, czww, czw, czw0, cnot, cnotw, cnot10, cnot10w, ch10, ch10w, chw,
      x, drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.prod_cons,
      List.prod_nil, mul_one, map_mul, mul_assoc, x0, x1]

theorem cl_decW (u : Word G4) : cl (decW u) = FreeMonoid.lift decL u := by
  induction u using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g u ih => rw [map_mul, map_mul, ih, map_mul, FreeMonoid.lift_eval_of, decW, FreeMonoid.lift_eval_of, cl_dec]

macro "rcch_qnorm" : tactic => `(tactic| (
  rw [cl_decW, cl_decW];
  simp only [map_mul, map_one, FreeMonoid.lift_eval_of, decL, Fin.isValue, x0, x1, mul_one, one_mul, mul_assoc];
  simp only [invc h0h0, invc z0z0, invc h1h1, invc z1z1, invc cqcq, invc kqkq, swc_sw, h0h0, z0z0, h1h1, z1z1,
    cqcq, kqkq, sw_sw, c_h0h1, c_h0z1, c_z0h1, c_z0z1, swc_h0, swc_z0, swc_h1, swc_z1, swc_cq, mul_one, one_mul]))

open HadamardPi in
set_option maxHeartbeats 4000000 in
/-- Decoding Equation (a1): `D((-1)_[a])² = ε`. -/
theorem dec_a1 : ∀ a : Fin 4, cl (decW (Z_[a] * Z_[a])) = cl (decW 1) := by
  intro a; fin_cases a <;> rcch_qnorm

open HadamardPi in
set_option maxHeartbeats 4000000 in
/-- Decoding Equation (a2): `D(X_[a,b])² = ε`. -/
theorem dec_a2 : ∀ a b : Fin 4, ∀ hab : a < b, cl (decW (X_[a,b] * X_[a,b])) = cl (decW 1) := by
  intro a b hab; fin_cases a <;> fin_cases b <;> first | (exact absurd hab (by decide)) | rcch_qnorm

open HadamardPi in
set_option maxHeartbeats 4000000 in
/-- Decoding Equation (a3): `D(H_[a,b])² = ε`. -/
theorem dec_a3 : ∀ a b : Fin 4, ∀ hab : a < b, cl (decW (H_[a,b] * H_[a,b])) = cl (decW 1) := by
  intro a b hab; fin_cases a <;> fin_cases b <;> first | (exact absurd hab (by decide)) | rcch_qnorm

end QCert.RealCliffordCH.Two
