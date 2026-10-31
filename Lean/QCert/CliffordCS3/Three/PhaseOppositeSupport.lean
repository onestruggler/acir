/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The atom fixes the phase on a complementary control
-/
import QCert.CliffordCS3.Three.PhaseGaugeSupport

namespace QCert.CliffordCS3.Three.PhaseOppositeSupport

open QuotientGroup LocalKZ AtomTokens PhaseCases PhaseDressed
noncomputable section

theorem A_complementary_phase : Commute A (C⁻¹ * S0) := by
  have h : Commute A AtomCross.E := by
    rw [AtomCross.A_factor]
    exact ((((AtomCross.D_E.inv_left.mul_left AtomCross.V_E).mul_left
      AtomCross.D_E.inv_left).mul_left AtomCross.V_E.inv_left).mul_left
      (AtomCross.D_E.pow_left 2))
  change Commute A (S0 * C⁻¹) at h
  rwa [S0_C.inv_right.eq] at h

theorem C_opposite_atom : Commute C (F2 * A * F2) := by
  have hi := Monomial.inv_of_square Monomial.f2_square
  have h : Commute (F2⁻¹ * C * F2) A := by
    rw [hi, Monomial.f2_conjugates_c]
    exact A_complementary_phase.symm
  have ht := Monomial.commute_conjugate h
  rwa [hi] at ht

end
end QCert.CliffordCS3.Three.PhaseOppositeSupport
