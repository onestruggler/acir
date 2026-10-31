/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Group algebra for the three-qubit phase commutator

These lemmas are purely group theoretic. Their hypotheses are instantiated
by Figure 2 and by checked two-qubit identities in Monomial.lean.
-/
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.Group

namespace QCert.CliffordCS3.Three.Monomial

variable {G : Type*} [Group G]

theorem inv_of_square {a : G} (h : a * a = 1) : a⁻¹ = a :=
  (eq_inv_of_mul_eq_one_left h).symm

/-- Commuting with a conjugate can be tested after conjugating the first entry. -/
theorem commute_conjugate {b y d : G} (h : Commute (y⁻¹ * b * y) d) :
    Commute b (y * d * y⁻¹) := by
  have := h.conj y
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right, mul_inv_cancel, mul_one] using this

theorem commute_cross_phase {b d y s : G}
    (hy : y * y = 1) (hbd : Commute b d) (hsd : Commute s d)
    (hyby : y * b * y = b⁻¹ * s) :
    Commute b (d * y * d⁻¹ * y) := by
  have hi := inv_of_square hy
  have hcon : Commute (y⁻¹ * b * y) d⁻¹ := by
    rw [hi, hyby]
    exact (hbd.inv_left.mul_left hsd).inv_right
  have h := commute_conjugate hcon
  rw [hi] at h
  simpa only [mul_assoc] using hbd.mul_right h

/-- C14 makes a phase commute with its CNOT conjugate. -/
theorem commute_phase_conjugate {a b d y s : G}
    (ha : a * a = 1) (hy : y * y = 1)
    (hbd : Commute b d) (hsd : Commute s d)
    (hyby : y * b * y = b⁻¹ * s)
    (h14 : b * a * b⁻¹ * a = d * y * d⁻¹ * y) :
    Commute b (a * b * a) := by
  have h := commute_cross_phase hy hbd hsd hyby
  rw [← h14] at h
  have hh : Commute b (a * b⁻¹ * a) := by
    have e := h.eq
    have e' := mul_left_cancel (show b * (b * (a * b⁻¹ * a)) = b * ((a * b⁻¹ * a) * b) by
      simpa only [mul_assoc] using e)
    exact e'
  have hi := hh.inv_right
  simpa only [mul_inv_rev, inv_inv, inv_of_square ha, mul_assoc] using hi

/-- The third pair phase is fixed by the CNOT that does not change its controls. -/
theorem commute_third_phase_cnot {a x b : G}
    (ha : a * a = 1) (hx : x * x = 1)
    (hax : a * x * a = x * a * x) (hbx : Commute b x) :
    Commute (x * a * b * a * x) a := by
  change x * a * b * a * x * a = a * (x * a * b * a * x)
  calc
    x * a * b * a * x * a = x * a * b * (a * x * a) := by group
    _ = x * a * b * (x * a * x) := by rw [hax]
    _ = x * a * (b * x) * a * x := by group
    _ = x * a * (x * b) * a * x := by rw [hbx.eq]
    _ = x * a * x * b * a * x := by group
    _ = a * x * a * b * a * x := by rw [← hax]
    _ = a * (x * a * b * a * x) := by group

/-- C15 is the square identity that forces the triple-controlled phase to square to one. -/
theorem triple_phase_square {a x b c : G}
    (ha : a * a = 1) (hx : x * x = 1)
    (hax : a * x * a = x * a * x) (hbx : Commute b x)
    (hba : Commute b (a * b * a))
    (hc : c = x * a * b * a * x)
    (h15 : x * a * b ^ 2 * a * x = a * b ^ 2 * a * b ^ 2)
    (hb4 : b ^ 4 = 1) :
    (c⁻¹ * (a * b * a) * b⁻¹) ^ 2 = 1 := by
  have hca : Commute c a := hc ▸ commute_third_phase_cnot ha hx hax hbx
  have hcb : Commute c b := by
    have h := hba.symm.conj x
    simp only [inv_of_square hx] at h
    have hxb : x * b * x = b := by
      calc
        x * b * x = b * (x * x) := by rw [hbx.symm.eq]; group
        _ = b := by rw [hx, mul_one]
    rw [hxb] at h
    simpa only [hc, mul_assoc] using h
  have hcu : Commute c (a * b * a) := (hca.mul_right hcb).mul_right hca
  have haa (z : G) : a * (a * z) = z := by rw [← mul_assoc, ha, one_mul]
  have hxx (z : G) : x * (x * z) = z := by rw [← mul_assoc, hx, one_mul]
  have hs : c ^ 2 = (a * b * a) ^ 2 * b ^ 2 := by
    rw [hc]
    calc
      (x * a * b * a * x) ^ 2 = x * a * b ^ 2 * a * x := by
        simp only [sq, mul_assoc, hxx, haa]
      _ = a * b ^ 2 * a * b ^ 2 := h15
      _ = (a * b * a) ^ 2 * b ^ 2 := by
        simp only [sq, mul_assoc, haa]
  rw [mul_assoc c⁻¹ (a * b * a) b⁻¹,
    (hcu.inv_left.mul_right hcb.inv_inv).mul_pow,
    (hba.symm.inv_right).mul_pow, inv_pow, inv_pow, hs]
  rw [mul_inv_rev]
  calc
    (b ^ 2)⁻¹ * ((a * b * a) ^ 2)⁻¹ * ((a * b * a) ^ 2 * (b ^ 2)⁻¹) =
        (b ^ 2)⁻¹ * (b ^ 2)⁻¹ := by group
    _ = (b ^ 4)⁻¹ := by group
    _ = 1 := by rw [hb4, inv_one]

/-- Conjugating the triple sign by the other CNOT leaves a pair sign. -/
theorem conjugate_triple_phase {x b D c q : G}
    (hx : x * x = 1) (hxb : Commute x b)
    (hc : c = x * D * x) (hq : q = c⁻¹ * D * b⁻¹)
    (hqq : q * q = 1) (hqb : Commute q b) (hb4 : b ^ 4 = 1) :
    x * q * x = q * b ^ 2 := by
  have hi := inv_of_square hx
  have hqqi := inv_of_square hqq
  have hxx (z : G) : x * (x * z) = z := by rw [← mul_assoc, hx, one_mul]
  have hconjc : x * c * x = D := by
    rw [hc]
    simp only [mul_assoc, hxx, hx, mul_one]
  have hconjD : x * D * x = c := hc.symm
  have hconjb : x * b * x = b := by
    rw [hxb.eq, mul_assoc, hx, mul_one]
  have hconj : x * q * x = b⁻¹ * q⁻¹ * b⁻¹ := by
    rw [hq]
    calc
      x * (c⁻¹ * D * b⁻¹) * x =
          (x * c * x)⁻¹ * (x * D * x) * (x * b * x)⁻¹ := by
        have h : x * (c⁻¹ * D * b⁻¹) * x⁻¹ =
            (x * c * x⁻¹)⁻¹ * (x * D * x⁻¹) * (x * b * x⁻¹)⁻¹ := by group
        simpa only [hi] using h
      _ = D⁻¹ * c * b⁻¹ := by rw [hconjc, hconjD, hconjb]
      _ = b⁻¹ * (c⁻¹ * D * b⁻¹)⁻¹ * b⁻¹ := by group
  rw [hconj, hqqi, hqb.symm.inv_left.eq, mul_assoc, ← mul_inv_rev, ← sq]
  have hb : (b ^ 2)⁻¹ = b ^ 2 := by
    apply inv_of_square
    simpa only [← pow_add] using hb4
  rw [hb]

end QCert.CliffordCS3.Three.Monomial

