/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Interchange of the two four-point Hadamard blocks
-/
import QCert.CliffordCS3.Three.BlockHorizontal
import QCert.CliffordCS3.Three.GaugeFacts

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace QCert.CliffordCS3.Three.BlockInterchange

open QuotientGroup LocalKZ PermutationBase
noncomputable section

abbrev L : G := BlockHorizontal.L
abbrev r : G := RestrictedGauge.correction
abbrev H : G := BlockHorizontal.H
def J : G := u (PermutationRoutes.tokens [2, 1, 2, 4])
def V1 : G := u (PermutationRoutes.tokens [6, 5])
def V2 : G := u (PermutationRoutes.tokens [4, 5])
def V : G := conj V1 L * conj V2 L

theorem token4_L : Commute (u (Cert.token 4)) L :=
  (AtomTokens.atom_token4.mul_left PhaseGaugeSupport.C_token4).symm

theorem J_L : Commute J L := by
  have ht1 : Commute L (u (Cert.token 1)) :=
    AtomDoubleWhite.atom_token1.mul_left PhaseGaugeSupport.C_token1
  have ht2 : Commute L (u (Cert.token 2)) :=
    AtomTokens.atom_token2.mul_left PhaseGaugeSupport.C_token2
  exact (ht2.mul_right (ht1.mul_right (ht2.mul_right
    (token4_L.symm.mul_right (Commute.one_right L))))).symm

theorem right_factor : V2 * J = ss02 := by
  have h := of_derivable PermutationBlockFrames.vertical_right
  simpa only [PermutationRoutes.tokens, List.map_append, List.prod_append, map_mul] using h

theorem left_factor : V1 * J = u W.CX10 * ss02 := by
  have h := of_derivable PermutationBlockFrames.vertical_left
  simpa only [PermutationRoutes.tokens, List.map_append, List.prod_append, map_mul] using h

theorem frame_right : conj V2 L = conj ss02 L := by
  rw [← right_factor, conj_mul, conj_of_commute J_L]

theorem frame_left : conj V1 L = conj (u W.CX10) (conj ss02 L) := by
  rw [← conj_mul, ← left_factor, conj_mul, conj_of_commute J_L]

theorem horizontal_frame : H = conj (u W.CX12) L * L := by
  have he : BlockHorizontal.F * u (Cert.token 4) = u W.CX12 :=
    of_derivable PermutationBlockFrames.horizontal
  change conj BlockHorizontal.F L * L = _
  rw [← he, conj_mul, conj_of_commute token4_L]

theorem map_conj (f : G →* G) (a b : G) : f (conj a b) = conj (f a) (f b) := by
  simp only [conj_def, map_mul, map_inv]

theorem vertical_conjugate : V = conj ss02 H := by
  rw [V, frame_left, frame_right, horizontal_frame, map_mul,
    map_conj (conj ss02) (u W.CX12) L,
    BlockVertical.conj02_cx12]

theorem horizontal : H = BlockVertical.B0 * r :=
  BlockHorizontal.horizontal PhaseGaugeSupport.r_A

theorem vertical : V = BlockVertical.B2 * r := by
  rw [vertical_conjugate, horizontal, map_mul, BlockVertical.conjugate_block]
  exact congrArg (fun g : G => BlockVertical.B2 * g) BlockVertical.conj02_correction

theorem r_L : Commute r L :=
  PhaseGaugeSupport.r_A.mul_right RestrictedGauge.correction_C

theorem r_F : Commute r BlockHorizontal.F := by
  exact PhaseGaugeSupport.r_token4.mul_right (PhaseGaugeSupport.r_token5.mul_right
    (PhaseGaugeSupport.r_T.mul_right (PhaseGaugeSupport.r_token4.mul_right
    (PhaseGaugeSupport.r_token5.mul_right (Commute.one_right r)))))

theorem r_H : Commute r H :=
  ((r_F.mul_right r_L).mul_right r_F.inv_right).mul_right r_L

theorem r_B0 : Commute r BlockVertical.B0 := by
  have he : H * r⁻¹ = BlockVertical.B0 := by rw [horizontal]; group
  rw [← he]
  exact r_H.mul_right (Commute.refl r).inv_right

theorem r_B2 : Commute r BlockVertical.B2 := by
  have h := r_B0.map (conj ss02)
  rw [BlockVertical.conjugate_block] at h
  change Commute (conj ss02 (C ^ 2 * Q)) BlockVertical.B2 at h
  rw [BlockVertical.conj02_correction] at h
  exact h

theorem blocks_commute : Commute V H := by
  rw [vertical, horizontal]
  exact (BlockVertical.blocks_commute.symm.mul_right r_B2.symm).mul_left
    (r_B0.mul_right (Commute.refl r))

end
end QCert.CliffordCS3.Three.BlockInterchange
