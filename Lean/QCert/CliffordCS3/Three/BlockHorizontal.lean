/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The horizontal pair of residual Hadamards
-/
import QCert.CliffordCS3.Three.RecoveryGeneration
import QCert.CliffordCS3.Three.BlockVertical
import QCert.CliffordCS3.Three.Cert.KCases
import QCert.CliffordCS3.Three.PermutationFrames
import QCert.CliffordCS3.Three.PermutationBlockFrames
import QCert.CliffordCS3.Three.PhasePoint

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.BlockHorizontal

open QuotientGroup LocalKZ AtomTokens PhaseCases RecoveryWords
noncomputable section

abbrev D : G := Monomial.dQ
abbrev B0 : G := BlockVertical.B0
def r : G := C ^ 2 * Q
def L : G := A * C
def F : G := u (PermutationRoutes.tokens PermutationFrames.frame)
def barA : G := F2 * A * F2
def H : G := (F * L * F⁻¹) * L

theorem sw12_S0 : sw12 S0 = S0 := by
  have ht := BlockVertical.conj12_s0
  rw [PermutationBase.conj_def, PermutationBase.ss12_eq,
    Monomial.inv_of_square Monomial.swap12_square] at ht
  rw [sw12_eq]
  exact ht

theorem sw12_F1 : sw12 F1 = F2 := by
  have h := congrArg sw12 sw12_F2
  have hs (x : G) : sw12 (sw12 x) = x := by
    simp only [sw12_eq]
    have hh (g : G) : Monomial.swap12Q * (Monomial.swap12Q * g) = g := by
      rw [← mul_assoc, Monomial.swap12_square, one_mul]
    simp only [mul_assoc, hh, Monomial.swap12_square, mul_one]
  rw [hs] at h
  exact h.symm

theorem remove_control : A * barA * D = B0 := by
  have ht := congrArg (sw12.comp sw) (of_derivable RecoveryGeneration.remove_control)
  change sw12 (sw (AM * (F0 * AM * F0))) =
    sw12 (sw (u RecoveryGeneration.single)) at ht
  have hf : sw F0 = F1 := by
    exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Swap01.pair * Two.W2.Xu * Swap01.pair) (v := Two.W2.Xl)
      (by decide +kernel)))
  have hs : sw (u (W.S 1)) = S0 := Monomial.swap_conjugates_s1
  simp only [map_mul, sw_A, hf, AtomControlSymmetry.f12_A, sw12_F1] at ht
  have hsingle : sw12 (sw (u RecoveryGeneration.single)) * D = B0 := by
    have hp : sw (u W.CS12) = C := sw_P
    simp only [RecoveryGeneration.single, u_commW, u_invW, map_mul, map_inv,
      sw_K, hs, hp, PhaseDressed.sw12_K0, sw12_S0, PhaseDressed.sw12_C, inv_inv]
    exact (BlockVertical.u_blockWord 0 W.CS01).symm
  rw [← hsingle, ← ht]
  rfl

theorem F2_B0 : Commute F2 B0 := by
  have hs : Commute F2 S0 := by
    have hh : Commute F2 (u (W.S 1)) := of_derivable (Two.derivable_embed 1
      (Two.derivable_of_check2 (w := Two.W2.Xl * Two.W2.Su)
        (v := Two.W2.Su * Two.W2.Xl) (by decide +kernel)))
    have h := hh.map sw
    have he : sw (u (W.S 1)) = S0 := Monomial.swap_conjugates_s1
    simpa only [sw_F2, he] using h
  change Commute F2 (u (BlockVertical.blockWord 0 W.CS01))
  rw [BlockVertical.u_blockWord]
  exact BlockVertical.commute_controlled Monomial.f2_K0_commute hs Monomial.f2_d_commute

theorem remove_control_rev : barA * A * D = B0 := by
  have ht := congrArg (fun g : G => F2 * g * F2) remove_control
  change F2 * (A * barA * D) * F2 = F2 * B0 * F2 at ht
  have hf (g : G) : F2 * (F2 * g) = g := by
    rw [← mul_assoc, Monomial.f2_square, one_mul]
  have hb : F2 * B0 * F2 = B0 := by
    rw [F2_B0.eq, mul_assoc, Monomial.f2_square, mul_one]
  rw [hb] at ht
  have he : F2 * (A * barA * D) * F2 = barA * A * D := by
    rw [barA]
    calc
      F2 * (A * (F2 * A * F2) * D) * F2 =
          (F2 * A * F2) * A * (F2 * D * F2) := by group
      _ = (F2 * A * F2) * A * D := by
        have hc : Commute F2 D := Monomial.f2_d_commute
        have hd : F2 * D * F2 = D := by
          rw [hc.eq, mul_assoc, Monomial.f2_square, mul_one]
        rw [hd]
  rwa [he] at ht

theorem opposite_atoms : Commute A barA := by
  apply mul_right_cancel (b := D)
  exact remove_control.trans remove_control_rev.symm

theorem frame_A : F * A * F⁻¹ = barA := by
  let J := u (PermutationRoutes.tokens PermutationFrames.stabilizer)
  have hj : Commute A J := by
    change Commute A
      (u (Cert.token 2) * (u (Cert.token 1) * (u (Cert.token 0) *
      (u (Cert.token 2) * (u (Cert.token 1) * (u (Cert.token 2) * (u (Cert.token 4) * 1)))))))
    exact atom_token2.mul_right (AtomDoubleWhite.atom_token1.mul_right
      (atom_token0.mul_right (atom_token2.mul_right (AtomDoubleWhite.atom_token1.mul_right
      (atom_token2.mul_right (atom_token4.mul_right (Commute.one_right A)))))))
  have hfj : F * J = F2 := by
    have h := of_derivable PermutationFrames.frame_stabilizer
    simpa only [PermutationRoutes.tokens, List.map_append, List.prod_append, map_mul] using h
  calc
    F * A * F⁻¹ = (F * J) * A * (F * J)⁻¹ := by
      rw [mul_inv_rev]
      calc
        F * A * F⁻¹ = F * (A * J * J⁻¹) * F⁻¹ := by group
        _ = F * (J * A * J⁻¹) * F⁻¹ := by rw [hj.eq]
        _ = _ := by group
    _ = barA := by rw [hfj, Monomial.inv_of_square Monomial.f2_square]; rfl

theorem C_token4 : Commute C (u (Cert.token 4)) := by
  have ht := PhaseStabilizers.phase_token3.map sw
  have he : u (Cert.token 3) = F2 * (u (W.K 1) * Q * (u (W.K 1))⁻¹) * F2 := by
    rw [← LocalKZ.K_inv 1]; rfl
  rw [he] at ht
  simp only [map_mul, map_inv, sw_P, sw_F2, sw_K, sw_Q] at ht
  have he' : F2 * (K * Q * K⁻¹) * F2 = u (Cert.token 4) := by rw [← T_eq]; rfl
  rwa [he'] at ht

theorem frame_C : F * C * F⁻¹ = C * D * Q := by
  have hft : F * u (Cert.token 4) = Monomial.zQ := by
    have h := of_derivable PermutationBlockFrames.horizontal
    exact h
  have hcon : F * C * F⁻¹ = Monomial.zQ * C * Monomial.zQ := by
    have hz : Monomial.zQ⁻¹ = Monomial.zQ := Monomial.inv_of_square Monomial.z_square
    calc
      F * C * F⁻¹ = F * (C * u (Cert.token 4) * (u (Cert.token 4))⁻¹) * F⁻¹ := by group
      _ = F * (u (Cert.token 4) * C * (u (Cert.token 4))⁻¹) * F⁻¹ := by rw [C_token4.eq]
      _ = (F * u (Cert.token 4)) * C * (F * u (Cert.token 4))⁻¹ := by group
      _ = Monomial.zQ * C * Monomial.zQ := by rw [hft, hz]
  rw [hcon]
  have hc : Monomial.zQ * C * Monomial.zQ = Monomial.yQ * D * Monomial.yQ := by
    rw [show C = Monomial.zQ * (Monomial.yQ * D * Monomial.yQ) * Monomial.zQ
      from Monomial.c_as_alternate_conjugate]
    have hh (g : G) : Monomial.zQ * (Monomial.zQ * g) = g := by
      rw [← mul_assoc, Monomial.z_square, one_mul]
    simp only [mul_assoc, hh, Monomial.z_square, mul_one]
  rw [hc]
  have hq : Q = C⁻¹ * (Monomial.yQ * D * Monomial.yQ) * D⁻¹ := Monomial.u_ccZ_alternate
  calc
    Monomial.yQ * D * Monomial.yQ = C * Q * D := by rw [hq]; group
    _ = C * D * Q := by rw [mul_assoc, D_Q.symm.eq, ← mul_assoc]

theorem frame_L : F * L * F⁻¹ = barA * (C * D * Q) := by
  rw [L]
  calc
    F * (A * C) * F⁻¹ = (F * A * F⁻¹) * (F * C * F⁻¹) := by group
    _ = _ := by rw [frame_A, frame_C]

theorem phase_frame_commutes (hr : Commute r A) : Commute (C * D * Q) A := by
  have he : D * A * D⁻¹ = C * A * C⁻¹ :=
    PhasePoint.D_atom_dresses.trans PhasePoint.C_atom_dresses.symm
  have hcd : Commute (C⁻¹ * D) A := by
    have hh := congrArg (fun g : G => C⁻¹ * g * D) he
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  have hfactor : C * D * Q = (C⁻¹ * D) * r := by
    rw [r]
    have hc : Commute D C := Monomial.c_d_commute.symm
    calc
      C * D * Q = (C⁻¹ * (C ^ 2 * D)) * Q := by group
      _ = (C⁻¹ * (D * C ^ 2)) * Q := by rw [(hc.pow_right 2).symm.eq]
      _ = _ := by group
  rw [hfactor]
  exact hcd.mul_left hr

theorem horizontal (hr : Commute r A) : H = B0 * r := by
  rw [H, frame_L, L]
  have hp := phase_frame_commutes hr
  calc
    (barA * (C * D * Q)) * (A * C) = (barA * A) * ((C * D * Q) * C) := by
      rw [mul_assoc barA, ← mul_assoc (C * D * Q), hp.eq]
      group
    _ = (barA * A) * (D * r) := by
      congr 1
      rw [r]
      have hc : Commute C (D * Q) := Monomial.c_d_commute.mul_right C_Q
      calc
        (C * D * Q) * C = C * ((D * Q) * C) := by group
        _ = C * (C * (D * Q)) := by rw [hc.symm.eq]
        _ = (C ^ 2 * D) * Q := by simp only [sq]; group
        _ = _ := by rw [(Monomial.c_d_commute.pow_left 2).eq]; group
    _ = B0 * r := by rw [← mul_assoc, remove_control_rev]

end
end QCert.CliffordCS3.Three.BlockHorizontal
