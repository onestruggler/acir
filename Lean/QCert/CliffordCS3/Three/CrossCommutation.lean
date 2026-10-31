/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Opposite-control Toffoli commutation

The controlled-gate certificates imply that two Toffoli transpositions
with opposite values of their shared control commute.
-/
import QCert.CliffordCS3.Three.MonomialAffine
import QCert.CliffordCS3.Three.PhaseSymmetry
import QCert.CliffordCS3.Three.MonomialControlled

set_option maxRecDepth 10000

namespace QCert.CliffordCS3.Three.CrossCommutation

open QuotientGroup Monomial

private theorem conj_factor {H : Type*} [Group H] (c v z : H) (hc : Commute c v) :
    v * (c * z) * v⁻¹ = c * (v * z * v⁻¹) := by
  calc
    v * (c * z) * v⁻¹ = (v * c) * (z * v⁻¹) := by group
    _ = (c * v) * (z * v⁻¹) := by rw [hc.symm.eq]
    _ = c * (v * z * v⁻¹) := by group

private theorem cancel_central_commute {H : Type*} [Group H] {c a b : H}
    (hca : Commute c a) (hcb : Commute c b) (h : Commute (c * a) (c * b)) :
    Commute a b := by
  apply mul_left_cancel (a := c * c)
  calc
    (c * c) * (a * b) = c * (c * a) * b := by group
    _ = c * (a * c) * b := by rw [hca.eq]
    _ = (c * a) * (c * b) := by group
    _ = (c * b) * (c * a) := h.eq
    _ = c * (b * c) * a := by group
    _ = c * (c * b) * a := by rw [hcb.symm.eq]
    _ = (c * c) * (b * a) := by group

private theorem cancel_commute_factor {H : Type*} [Group H] {c a b : H}
    (hca : Commute c a) (h : Commute a (c * b)) : Commute a b := by
  apply mul_left_cancel (a := c)
  calc
    c * (a * b) = (c * a) * b := by group
    _ = (a * c) * b := by rw [hca.eq]
    _ = a * (c * b) := by group
    _ = (c * b) * a := h.eq
    _ = c * (b * a) := by group

abbrev Q : G := u Cert.ccZ
abbrev k₀ : G := u (W.K 0)
abbrev k₁ : G := u (W.K 1)
abbrev R : G := u MonomialControlled.core
abbrev V : G := u MonomialControlled.control
def O : G := k₁ * (Q * dQ ^ 2) * k₁⁻¹

private theorem kinv (q : Fin 3) : u (W.I * W.K q) = (u (W.K q))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [map_mul, map_one] using of_derivable (K_inverse' q)

private theorem kinv' (q : Fin 3) : u W.I * u (W.K q) = (u (W.K q))⁻¹ := by
  rw [← map_mul]
  exact kinv q

private theorem swap_k₀ : swapQ * k₀ * swapQ = k₁ := by
  have h := Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Swap01.pair * Two.W2.Ku * Swap01.pair)
    (v := Two.W2.Kl) (by decide +kernel))
  exact of_derivable h

private theorem c_k₁ : Commute cQ k₁ := by
  have hb : Commute bQ k₀ := of_derivable (Derivable.of (Rel.comm_0_12 Local.K)).symm
  have h := hb.conj swapQ
  rw [inv_of_square swap_square, swap_k₀] at h
  exact h

private theorem c_Q : Commute cQ Q := by
  rw [show Q = cQ⁻¹ * (aQ * bQ * aQ) * bQ⁻¹ from u_ccZ]
  exact ((Commute.refl cQ).inv_right.mul_right c_conjugate_commute).mul_right c_b_commute.inv_right

private theorem R_eq : R = cQ * Q := by
  have hr : R = aQ * bQ * aQ * bQ ^ 3 := rfl
  rw [hr, cube_eq_inv b_fourth]
  change aQ * bQ * aQ * bQ⁻¹ = cQ * u Cert.ccZ
  rw [u_ccZ]
  group

theorem V_eq : V = bQ * k₁ * bQ * k₁ * bQ := rfl

theorem Vinv : u MonomialControlled.controlInv = V⁻¹ := by
  have h : u MonomialControlled.controlInv =
      bQ ^ 3 * u (W.I * W.K 1) * bQ ^ 3 * u (W.I * W.K 1) * bQ ^ 3 := rfl
  rw [h, cube_eq_inv b_fourth, kinv, V_eq]
  group

theorem c_V : Commute cQ V := by
  rw [V_eq]
  exact (((c_b_commute.mul_right c_k₁).mul_right c_b_commute).mul_right c_k₁).mul_right c_b_commute

private theorem c_O : Commute cQ O :=
  ((c_k₁.mul_right (c_Q.mul_right (c_d_commute.pow_right 2))).mul_right c_k₁.inv_right)

private theorem conjugate_Q : V * Q * V⁻¹ = k₁ * Q * k₁⁻¹ := by
  have h := of_derivable MonomialControlled.conjugate_core
  simp only [map_mul, Vinv, kinv'] at h
  change V * R * V⁻¹ = k₁ * R * k₁⁻¹ at h
  rw [R_eq, conj_factor cQ V Q c_V, conj_factor cQ k₁ Q c_k₁] at h
  exact mul_left_cancel h

private theorem Q_O : Commute Q O := by
  have h := of_derivable MonomialControlled.core_opposite_commute
  simp only [map_mul, map_pow, kinv'] at h
  have hh : Commute R (k₁ * (R * dQ ^ 2) * k₁⁻¹) := by
    simpa only [Commute, SemiconjBy, mul_assoc] using h
  rw [R_eq, mul_assoc cQ Q (dQ ^ 2), conj_factor cQ k₁ (Q * dQ ^ 2) c_k₁] at hh
  exact cancel_central_commute c_Q c_O hh

private theorem V_opposite : Commute V (Q * dQ ^ 2) := by
  have h := of_derivable MonomialControlled.commute_opposite_core
  simp only [map_mul, map_pow] at h
  change Commute V (R * dQ ^ 2) at h
  rw [R_eq, mul_assoc] at h
  exact cancel_commute_factor c_V h

def F : G →* G := (MulAut.conj swapQ).toMonoidHom

@[simp] theorem F_Q : F Q = Q := by
  have h := of_derivable swap_ccZ
  simpa only [F, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_of_square swap_square, map_mul] using h

@[simp] theorem F_d : F dQ = dQ := by
  simpa only [F, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_of_square swap_square] using swap_conjugates_d

@[simp] private theorem F_k₁ : F k₁ = k₀ := by
  have h := of_derivable Swap01.conjugate_K
  simpa only [F, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_of_square swap_square, map_mul] using h

@[simp] theorem F_b : F bQ = cQ := by
  simp only [F, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_of_square swap_square]
  rfl

theorem F_V : F V = cQ * k₀ * cQ * k₀ * cQ := by
  rw [V_eq]
  simp only [map_mul, F_b, F_k₁]

private theorem FV_k₁ : Commute (F V) k₁ := by
  have hk : Commute k₀ k₁ :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.K 0 1 (by decide)))
  rw [F_V]
  exact (((c_k₁.mul_left hk).mul_left c_k₁).mul_left hk).mul_left c_k₁

theorem FV_opposite : Commute (F V) (Q * dQ ^ 2) := by
  have h := congrArg F V_opposite.eq
  simpa only [map_mul, map_pow, F_Q, F_d] using h

theorem FV_O : Commute (F V) O :=
  (FV_k₁.mul_right FV_opposite).mul_right FV_k₁.inv_right

theorem token_opposite_commute : Commute (u (Cert.token 6)) O := by
  have hq := congrArg F conjugate_Q
  simp only [map_mul, map_inv, F_Q, F_k₁] at hq
  have ht : u (Cert.token 6) = k₀ * Q * k₀⁻¹ := by
    rw [← kinv 0]
    rfl
  have h := Q_O.conj (F V)
  have he : F V * O * (F V)⁻¹ = O := by
    rw [FV_O.eq]
    group
  rw [he, hq, ← ht] at h
  exact h

end QCert.CliffordCS3.Three.CrossCommutation

