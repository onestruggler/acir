/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The one-point sign fixes all six complementary transpositions

The even tokens share the target of the residual atom. Their diagonal
forms commute with its exchanged sign, and the atom transports this
commutation back to the sign. Wire swaps give the other target wires.
-/
import QCert.CliffordCS3.Three.AtomWhiteTransport
import QCert.CliffordCS3.Three.PhaseSymmetry12
import QCert.CliffordCS3.Three.WhiteSign

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.PhaseCases

open QuotientGroup LocalKZ AtomTokens
noncomputable section

private theorem sign_commute_of_atom {B : G} (ha : Commute A B)
    (ht : Commute T B) : Commute Q B := by
  have he : Q = A⁻¹ * T * A := by
    calc
      Q = A⁻¹ * (A * Q) := by group
      _ = A⁻¹ * (T * A) := by rw [A_Q]
      _ = _ := by group
  rw [he]
  exact (ha.inv_left.mul_left ht).mul_left ha

theorem sign_token0 : Commute Q (u (Cert.token 0)) := by
  apply sign_commute_of_atom atom_token0
  rw [T_eq, token0_form]
  exact ((Commute.refl Q).mul_right (C_Q.symm.pow_right 2)).conj K

theorem sign_token4 : Commute Q (u (Cert.token 4)) := by
  apply sign_commute_of_atom atom_token4
  rw [T_eq, token4_form]
  exact ((Commute.refl Q).mul_right (D_Q.symm.pow_right 2)).conj K

theorem sign_token2 : Commute Q (u (Cert.token 2)) := by
  apply sign_commute_of_atom atom_token2
  rw [T_eq, token2_form]
  exact ((((Commute.refl Q).mul_right (C_Q.symm.pow_right 2)).mul_right
    (D_Q.symm.pow_right 2)).mul_right (S0_Q.symm.pow_right 2)).conj K

abbrev F0 : G := u (W.X 0)
abbrev K2 : G := u (W.K 2)

theorem sw_F1 : sw F1 = F0 := by
  exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Swap01.pair * Two.W2.Xl * Swap01.pair) (v := Two.W2.Xu)
    (by decide +kernel)))

theorem sw_F2 : sw F2 = F2 := by
  change Monomial.swapQ * F2 * Monomial.swapQ = F2
  rw [Monomial.f2_swap_commute.symm.eq, mul_assoc, S_square, mul_one]

theorem sw_K0 : sw K = u (W.K 1) := by
  exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Swap01.pair * Two.W2.Ku * Swap01.pair) (v := Two.W2.Kl)
    (by decide +kernel)))

def sw12 : G →* G where
  toFun x := Monomial.swap12Q * x * Monomial.swap12Q⁻¹
  map_one' := by group
  map_mul' x y := by group

theorem sw12_eq (x : G) : sw12 x = Monomial.swap12Q * x * Monomial.swap12Q := by
  change Monomial.swap12Q * x * Monomial.swap12Q⁻¹ = _
  rw [Monomial.inv_of_square Monomial.swap12_square]

theorem sw12_Q : sw12 Q = Q := by
  rw [sw12_eq]
  exact of_derivable Monomial.swap12_ccZ

private def pair12 : Word Two.Gen2 :=
  (Two.W2.Ku * Two.W2.CS * Two.W2.CS * Two.W2.Ku * Two.W2.I) *
  (Two.W2.Kl * Two.W2.CS * Two.W2.CS * Two.W2.Kl * Two.W2.I) *
  (Two.W2.Ku * Two.W2.CS * Two.W2.CS * Two.W2.Ku * Two.W2.I)

theorem sw12_K1 : sw12 (u (W.K 1)) = K2 := by
  rw [sw12_eq]
  exact of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := pair12 * Two.W2.Ku * pair12) (v := Two.W2.Kl)
    (by decide +kernel)))

theorem sw12_F2 : sw12 F2 = F1 := by
  rw [sw12_eq]
  exact of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := pair12 * Two.W2.Xl * pair12) (v := Two.W2.Xu)
    (by decide +kernel)))

theorem sw12_F0 : sw12 F0 = F0 := by
  have hk1 : Commute F0 (u (W.K 1)) :=
    of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Xu * Two.W2.Kl) (v := Two.W2.Kl * Two.W2.Xu)
      (by decide +kernel)))
  have hk2 : Commute F0 (u (W.K 2)) := by
    have hk : Commute (u (W.K 2)) K :=
      of_derivable (Derivable.of (Rel.comm_loc Local.K Local.K 0 2 (by decide))).symm
    have hs : Commute (u (W.K 2)) S0 :=
      of_derivable (Derivable.of (Rel.comm_loc Local.S Local.K 0 2 (by decide))).symm
    have hi : Commute (u (W.K 2)) (u W.I) :=
      of_derivable (Derivable.of (Rel.comm_i .K₂ (by decide))).symm
    simpa only [F0, W.X, map_mul] using
      ((((hk.mul_right hs).mul_right hs).mul_right hk).mul_right hi).symm
  have hb : Commute F0 P := by
    have hk : Commute P K := P_K
    have hs : Commute P S0 :=
      of_derivable (Derivable.of (Rel.comm_0_12 Local.S)).symm
    have hi : Commute P (u W.I) :=
      of_derivable (Derivable.of (Rel.comm_i .CS₁₂ (by decide))).symm
    simpa only [F0, W.X, map_mul] using
      ((((hk.mul_right hs).mul_right hs).mul_right hk).mul_right hi).symm
  have hi : Commute F0 (u W.I) :=
    of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Xu * Two.W2.I) (v := Two.W2.I * Two.W2.Xu)
      (by decide +kernel)))
  have hy : Commute F0 Monomial.yQ := by
    simpa only [Monomial.yQ, W.CX21, W.CX, map_mul] using
      (((hk1.mul_right hb).mul_right hb).mul_right hk1).mul_right hi
  have hz : Commute F0 Monomial.zQ := by
    simpa only [Monomial.zQ, W.CX12, W.CX, map_mul] using
      (((hk2.mul_right hb).mul_right hb).mul_right hk2).mul_right hi
  have hs : Commute F0 Monomial.swap12Q :=
    (hy.mul_right hz).mul_right hy
  change Monomial.swap12Q * F0 * Monomial.swap12Q⁻¹ = F0
  rw [hs.symm.eq]
  group

theorem token5_transport : sw12 (sw (u (Cert.token 0))) = u (Cert.token 5) := by
  have he : u (Cert.token 0) = F1 * (K * Q * K⁻¹) * F1 := by
    rw [← T_eq]
    rfl
  rw [he]
  simp only [map_mul, map_inv, sw_F1, sw_K0, sw_Q, sw12_F0, sw12_K1, sw12_Q]
  rw [← K_inv 2]
  rfl

theorem token1_transport : sw12 (sw (u (Cert.token 2))) = u (Cert.token 1) := by
  have he : u (Cert.token 2) = F1 * F2 * (K * Q * K⁻¹) * F2 * F1 := by
    rw [← T_eq]
    rfl
  rw [he]
  simp only [map_mul, map_inv, sw_F1, sw_F2, sw_K0, sw_Q,
    sw12_F0, sw12_F2, sw12_K1, sw12_Q]
  rw [← K_inv 2]
  rfl

theorem sign_token5 : Commute Q (u (Cert.token 5)) := by
  have ht := sign_token0.map (sw12.comp sw)
  simpa only [MonoidHom.comp_apply, sw_Q, sw12_Q, token5_transport] using ht

theorem sign_token1 : Commute Q (u (Cert.token 1)) := by
  have ht := sign_token2.map (sw12.comp sw)
  simpa only [MonoidHom.comp_apply, sw_Q, sw12_Q, token1_transport] using ht

theorem sign_token3 : Commute Q (u (Cert.token 3)) := by
  have ht := of_derivable WhiteSign.sign_white_toffoli
  simpa only [map_mul] using ht

theorem sign_token (d : Fin 6) : Commute Q (u (Cert.token d.castSucc)) := by
  fin_cases d
  · exact sign_token0
  · exact sign_token1
  · exact sign_token2
  · exact sign_token3
  · exact sign_token4
  · exact sign_token5

end
end QCert.CliffordCS3.Three.PhaseCases
