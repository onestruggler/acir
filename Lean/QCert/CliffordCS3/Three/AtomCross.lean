/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The residual atom commutes with an opposite-control exchange
-/
import QCert.CliffordCS3.Three.AtomWhiteTransport
import QCert.CliffordCS3.Three.CrossCommutation
import QCert.CliffordCS3.Three.WhiteSign
import QCert.CliffordCS3.Three.Cert.AtomFactor
import QCert.CliffordCS3.Three.Cert.AtomRotation

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.AtomCross

open QuotientGroup LocalKZ
noncomputable section

abbrev D : G := Monomial.dQ
abbrev S0 : G := u (W.S 0)
abbrev Z : G := Q * D ^ 2
abbrev O : G := CrossCommutation.O
abbrev V : G := CrossCommutation.F CrossCommutation.V
def E : G := S0 * C⁻¹

theorem sw_eq_F (x : G) : sw x = CrossCommutation.F x := by
  simp only [sw, CrossCommutation.F, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Monomial.inv_of_square S_square]

theorem A_factor : A = D⁻¹ * V * D⁻¹ * V⁻¹ * D ^ 2 := by
  have ht := congrArg sw (of_derivable Cert.AtomFactor.factor)
  change sw AM = sw (D ^ 3 * CrossCommutation.V * D ^ 3 *
    u MonomialControlled.controlInv * D ^ 2) at ht
  simp only [map_mul, map_pow, sw_A, AtomTokens.sw_D,
    CrossCommutation.Vinv, map_inv] at ht
  rw [sw_eq_F] at ht
  rwa [Monomial.cube_eq_inv Monomial.d_fourth] at ht

theorem V_E : Commute V E := by
  have ht := of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := (Two.W2.CS * Two.W2.Ku * Two.W2.CS * Two.W2.Ku * Two.W2.CS) *
      (Two.W2.Su * Two.W2.CS ^ 3))
    (v := (Two.W2.Su * Two.W2.CS ^ 3) *
      (Two.W2.CS * Two.W2.Ku * Two.W2.CS * Two.W2.Ku * Two.W2.CS))
    (by decide +kernel)))
  change CrossCommutation.V * (u (W.S 1) * P ^ 3) =
    (u (W.S 1) * P ^ 3) * CrossCommutation.V at ht
  have hh := congrArg sw ht
  have hs : sw (u (W.S 1)) = S0 := Monomial.swap_conjugates_s1
  simp only [map_mul, map_pow, hs, AtomTokens.sw_P] at hh
  rw [sw_eq_F] at hh
  have hc4 : C ^ 4 = 1 := by
    have h := congrArg sw P_fourth
    simpa only [map_pow, map_one, AtomTokens.sw_P] using h
  change V * (S0 * C ^ 3) = (S0 * C ^ 3) * V at hh
  rwa [Monomial.cube_eq_inv hc4] at hh

theorem phaseWord : u Cert.AtomRotation.phaseWord = S0 := by
  have ht := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := (Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I) * Two.W2.CS *
      (Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I) * Two.W2.CS)
    (v := Two.W2.Su) (by decide +kernel)))
  simpa [Cert.AtomRotation.phaseWord, W.CX01, W.CX, Two.embW, Two.emb, pow_two] using ht

theorem core_eq : u Cert.AtomRotation.core = C * Z := by
  change R * D ^ 2 = C * (Q * D ^ 2)
  rw [R_eq, mul_assoc]

theorem exchange_eq : u Cert.AtomRotation.exchange = C * O := by
  change u (W.K 1) * u Cert.AtomRotation.core * u (W.I * W.K 1) = C * O
  rw [core_eq, K_inv]
  have hc := WhiteSign.c_K1_commute
  change u (W.K 1) * (C * Z) * (u (W.K 1))⁻¹ =
    C * (u (W.K 1) * Z * (u (W.K 1))⁻¹)
  rw [← mul_assoc _ C, hc.symm.eq]
  group

theorem D_O : D * O * D⁻¹ = E⁻¹ * Z * O := by
  have ht := of_derivable Cert.AtomRotation.rotation
  simp only [map_mul, map_pow, core_eq, exchange_eq, phaseWord,
    Monomial.cube_eq_inv Monomial.d_fourth] at ht
  have hs4 : S0 ^ 4 = 1 := by
    simpa only [map_pow, map_one] using of_derivable (Derivable.of (Rel.c3 0))
  rw [Monomial.cube_eq_inv hs4] at ht
  apply mul_left_cancel (a := C)
  calc
    C * (D * O * D⁻¹) = D * (C * O) * D⁻¹ := by
      calc
        C * (D * O * D⁻¹) = (C * D) * O * D⁻¹ := by group
        _ = (D * C) * O * D⁻¹ := by rw [Monomial.c_d_commute.eq]
        _ = D * (C * O) * D⁻¹ := by group
    _ = S0⁻¹ * (C * Z) * (C * O) := ht
    _ = C * (E⁻¹ * Z * O) := by
      rw [E, mul_inv_rev, inv_inv]
      have hsc := AtomTokens.S0_C.inv_left
      have hcz := AtomTokens.C_Q.mul_right (Monomial.c_d_commute.pow_right 2)
      calc
        S0⁻¹ * (C * Z) * (C * O) = (S0⁻¹ * C) * (Z * C) * O := by group
        _ = (C * S0⁻¹) * (C * Z) * O := by rw [hsc.eq, hcz.symm.eq]
        _ = C * ((C * S0⁻¹) * Z * O) := by
          calc
            (C * S0⁻¹) * (C * Z) * O = C * (S0⁻¹ * C) * Z * O := by group
            _ = C * (C * S0⁻¹) * Z * O := by rw [hsc.eq]
            _ = _ := by group

theorem D_E : Commute D E :=
  AtomTokens.S0_D.symm.mul_right Monomial.c_d_commute.symm.inv_right

theorem D_Z : Commute D Z := AtomTokens.D_Q.mul_right (Commute.self_pow D 2)

theorem V_D_O : Commute V (D * O * D⁻¹) := by
  rw [D_O]
  exact (V_E.inv_right.mul_right CrossCommutation.FV_opposite).mul_right
    CrossCommutation.FV_O

theorem V_D2_O : Commute V (D ^ 2 * O * (D ^ 2)⁻¹) := by
  have he : D ^ 2 * O * (D ^ 2)⁻¹ = E⁻¹ * Z * (E⁻¹ * Z * O) := by
    calc
      D ^ 2 * O * (D ^ 2)⁻¹ = D * (D * O * D⁻¹) * D⁻¹ := by simp only [sq]; group
      _ = D * (E⁻¹ * Z * O) * D⁻¹ := by rw [D_O]
      _ = E⁻¹ * Z * (D * O * D⁻¹) := by
        calc
          D * (E⁻¹ * Z * O) * D⁻¹ = (D * (E⁻¹ * Z)) * O * D⁻¹ := by group
          _ = ((E⁻¹ * Z) * D) * O * D⁻¹ := by rw [(D_E.inv_right.mul_right D_Z).eq]
          _ = _ := by group
      _ = _ := by rw [D_O]
  rw [he]
  exact (V_E.inv_right.mul_right CrossCommutation.FV_opposite).mul_right
    ((V_E.inv_right.mul_right CrossCommutation.FV_opposite).mul_right CrossCommutation.FV_O)

theorem A_O : Commute A O := by
  have h1 := V_D_O.conj D⁻¹
  have h2 := V_D2_O.inv_left.conj ((D ^ 2)⁻¹)
  simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at h1 h2
  rw [A_factor]
  have hf : D⁻¹ * V * D⁻¹ * V⁻¹ * D ^ 2 =
      (D⁻¹ * V * D) * ((D ^ 2)⁻¹ * V⁻¹ * D ^ 2) := by group
  rw [hf]
  simpa only [mul_assoc] using h1.mul_left h2

theorem token3_eq : u (Cert.token 3) = O := by
  have hf : u (W.X 2) * Q * u (W.X 2) = Q * D ^ 2 :=
    of_derivable Monomial.X2_ccZ
  have hk : Commute (u (W.X 2)) (u (W.K 1)) :=
    of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
      (w := Two.W2.Xl * Two.W2.Ku) (v := Two.W2.Ku * Two.W2.Xl)
      (by decide +kernel)))
  change u (W.X 2) * (u (W.K 1) * Q * (u W.I * u (W.K 1))) * u (W.X 2) = O
  rw [show u W.I * u (W.K 1) = (u (W.K 1))⁻¹ by simpa only [map_mul] using K_inv 1]
  calc
    u (W.X 2) * (u (W.K 1) * Q * (u (W.K 1))⁻¹) * u (W.X 2) =
        u (W.K 1) * (u (W.X 2) * Q * u (W.X 2)) * (u (W.K 1))⁻¹ := by
      calc
        u (W.X 2) * (u (W.K 1) * Q * (u (W.K 1))⁻¹) * u (W.X 2) =
            (u (W.X 2) * u (W.K 1)) * Q * ((u (W.K 1))⁻¹ * u (W.X 2)) := by group
        _ = (u (W.K 1) * u (W.X 2)) * Q * (u (W.X 2) * (u (W.K 1))⁻¹) := by
          rw [hk.eq, hk.inv_right.symm.eq]
        _ = _ := by group
    _ = O := by rw [hf]; rfl

theorem atom_token3 : Commute A (u (Cert.token 3)) := by rw [token3_eq]; exact A_O

end
end QCert.CliffordCS3.Three.AtomCross
