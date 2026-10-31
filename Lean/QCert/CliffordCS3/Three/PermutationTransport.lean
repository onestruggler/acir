/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Wire permutations in the syntactic Clifford+CS group
-/
import QCert.CliffordCS3.Three.PermutationBase
import QCert.CliffordCS3.Three.PhaseSymmetry12

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace QCert.CliffordCS3.Three.PermutationBase
open QuotientGroup Monomial
noncomputable section

abbrev k (j : Fin 3) : G := u (W.K j)
abbrev s (j : Fin 3) : G := u (W.S j)
abbrev ii : G := u W.I
abbrev ss01 : G := u swapWord
abbrev ss12 : G := u swap12
abbrev ss02 : G := u swap02

def conj (v : G) : G →* G := (MulAut.conj v).toMonoidHom

theorem conj_def (v g : G) : conj v g = v * g * v⁻¹ := rfl

theorem scalar_commute (w : Word Gen) : Commute ii (u w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [map_one]; exact Commute.one_right _
  | mul_of a w ih =>
    rw [map_mul]
    refine (show Commute ii (u (FreeMonoid.of a)) from ?_).mul_right ih
    cases a <;> first | exact Commute.refl _ | exact of_derivable (Derivable.of (Rel.comm_i _ (by decide)))

theorem k_commute (a b : Fin 3) : Commute (k a) (k b) := by
  rcases lt_trichotomy a b with h | h | h
  · exact of_derivable (Derivable.of (Rel.comm_loc Local.K Local.K a b h))
  · subst b; exact Commute.refl _
  · exact (of_derivable (Derivable.of (Rel.comm_loc Local.K Local.K b a h))).symm

theorem conj_of_commute {v g : G} (h : Commute v g) : conj v g = g := by
  rw [conj_def, h.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem ss01_inv : ss01⁻¹ = ss01 := inv_of_square swap_square
theorem ss12_inv : ss12⁻¹ = ss12 := by
  apply inv_of_square
  simpa only [map_mul, map_one] using of_derivable PermutationBase.swap12_square

theorem conj01_def (g : G) : conj ss01 g = ss01 * g * ss01 := by rw [conj_def, ss01_inv]
theorem conj12_def (g : G) : conj ss12 g = ss12 * g * ss12 := by rw [conj_def, ss12_inv]

theorem conj01_k0 : conj ss01 (k 0) = k 1 := by
  rw [conj_def, ss01_inv]
  exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := ((Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I) *
      (Two.W2.Ku * Two.W2.CS ^ 2 * Two.W2.Ku * Two.W2.I) *
      (Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I)) * Two.W2.Ku *
      ((Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I) *
      (Two.W2.Ku * Two.W2.CS ^ 2 * Two.W2.Ku * Two.W2.I) *
      (Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I)))
    (v := Two.W2.Kl) (by decide +kernel)))

theorem conj01_k1 : conj ss01 (k 1) = k 0 := by
  rw [conj_def, ss01_inv]
  exact of_derivable Swap01.conjugate_K

theorem conj01_k2 : conj ss01 (k 2) = k 2 := by
  apply conj_of_commute
  have hd : Commute dQ (k 2) := of_derivable (Derivable.of (Rel.comm_2_01 Local.K)).symm
  have hi := scalar_commute (W.K 2)
  have ha : Commute aQ (k 2) := by
    simpa only [aQ, W.CX01, W.CX, map_mul] using
      (((((k_commute 1 2).mul_left hd).mul_left hd).mul_left (k_commute 1 2)).mul_left hi)
  have hx : Commute xQ (k 2) := by
    simpa only [xQ, W.CX10, W.CX, map_mul] using
      (((((k_commute 0 2).mul_left hd).mul_left hd).mul_left (k_commute 0 2)).mul_left hi)
  exact (ha.mul_left hx).mul_left ha

private def cu : Word Two.Gen2 := Two.W2.Ku * Two.W2.CS ^ 2 * Two.W2.Ku * Two.W2.I
private def cl : Word Two.Gen2 := Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I
private def sw : Word Two.Gen2 := cl * cu * cl

theorem conj12_k0 : conj ss12 (k 0) = k 0 := by
  apply conj_of_commute
  have hb : Commute bQ (k 0) := of_derivable (Derivable.of (Rel.comm_0_12 Local.K)).symm
  have hi := scalar_commute (W.K 0)
  have hy : Commute yQ (k 0) := by
    simpa only [yQ, W.CX21, W.CX, map_mul] using
      (((((k_commute 1 0).mul_left hb).mul_left hb).mul_left (k_commute 1 0)).mul_left hi)
  have hz : Commute zQ (k 0) := K0_z_commute.symm
  exact (hz.mul_left hy).mul_left hz

theorem conj12_k1 : conj ss12 (k 1) = k 2 := by
  rw [conj_def, ss12_inv]
  exact of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := sw * Two.W2.Ku * sw) (v := Two.W2.Kl) (by decide +kernel)))

theorem conj12_k2 : conj ss12 (k 2) = k 1 := by
  rw [conj_def, ss12_inv]
  exact of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := sw * Two.W2.Kl * sw) (v := Two.W2.Ku) (by decide +kernel)))

theorem conj01_ii : conj ss01 ii = ii := conj_of_commute (scalar_commute swapWord).symm
theorem conj12_ii : conj ss12 ii = ii := conj_of_commute (scalar_commute swap12).symm

theorem conj01_Q : conj ss01 (u Cert.ccZ) = u Cert.ccZ := by
  rw [conj_def, ss01_inv]; exact of_derivable swap_ccZ

theorem ss12_eq : ss12 = swap12Q := cnot_braid12.symm

theorem conj12_Q : conj ss12 (u Cert.ccZ) = u Cert.ccZ := by
  rw [conj_def, ss12_inv, ss12_eq]
  exact of_derivable swap12_ccZ

theorem conj01_d : conj ss01 dQ = dQ := by
  rw [conj_def, ss01_inv]; exact swap_conjugates_d

theorem conj01_b : conj ss01 bQ = cQ := by rw [conj_def, ss01_inv]; rfl
theorem conj12_d : conj ss12 dQ = cQ := by
  rw [conj_def, ss12_inv, ss12_eq]; exact swap12_d

theorem conj12_b : conj ss12 bQ = bQ := by
  rw [conj_def, ss12_inv]
  exact of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := sw * Two.W2.CS * sw) (v := Two.W2.CS) (by decide +kernel)))

theorem conj01_c : conj ss01 cQ = bQ := by
  rw [conj_def, ss01_inv]
  change ss01 * (ss01 * bQ * ss01) * ss01 = bQ
  have h (g : G) : ss01 * (ss01 * g) = g := by rw [← mul_assoc, swap_square, one_mul]
  simp only [mul_assoc, h, swap_square, mul_one]

theorem conj_mul (a b g : G) : conj (a * b) g = conj a (conj b g) := by
  simp only [conj_def, mul_inv_rev, mul_assoc]

theorem conj02 (g : G) : conj ss02 g = conj ss12 (conj ss01 (conj ss12 g)) := by
  change conj (ss12 * ss01 * ss12) g = _
  rw [conj_mul, conj_mul]

theorem r18 : Eqn [.CZ02] [.S12, .CZ01, .S12] := by
  apply to_derivable
  change u cz02 = ss12 * dQ ^ 2 * ss12
  have h := congrArg (fun g : G => g ^ 2) conj12_d
  dsimp only at h
  rw [← map_pow, conj_def, ss12_inv] at h
  rw [h]
  have h := congrArg (fun g : G => g ^ 2) conj01_b
  dsimp only at h
  rw [← map_pow, conj_def, ss01_inv] at h
  exact h

theorem r19 : Eqn [.CZ12] [.S01, .CZ02, .S01] := by
  apply to_derivable
  have hh : u cz02 = cQ ^ 2 := by
    have h := congrArg (fun g : G => g ^ 2) conj01_b
    dsimp only at h
    rw [← map_pow, conj_def, ss01_inv] at h
    exact h
  change bQ ^ 2 = ss01 * u cz02 * ss01
  rw [hh]
  have h := congrArg (fun g : G => g ^ 2) conj01_c
  dsimp only at h
  rw [← map_pow, conj_def, ss01_inv] at h
  exact h.symm

theorem r33 : Eqn [.CCX01] [.S12, .CCX02, .S12] := by
  apply to_derivable
  change u (ccx 2) = ss12 * u (ccx 1) * ss12
  rw [← conj12_def]
  simp only [ccx, map_mul, conj12_k1, conj12_Q, conj12_ii]

theorem r32 : Eqn [.CCX01] [.S02, .CCX12, .S02] := by
  apply to_derivable
  have hs : ss02⁻¹ = ss02 := by
    change (ss12 * ss01 * ss12)⁻¹ = _
    simp only [mul_inv_rev, ss01_inv, ss12_inv, mul_assoc]; rfl
  change u (ccx 2) = ss02 * u (ccx 0) * ss02
  have he (g : G) : ss02 * g * ss02 = conj ss02 g := by rw [conj_def, hs]
  rw [he, conj02]
  simp only [ccx, map_mul, conj12_k0, conj12_k1, conj12_k2, conj01_k0,
    conj01_k1, conj01_k2, conj12_Q, conj01_Q, conj12_ii, conj01_ii]

theorem r11 : Eqn [.K01] [.S02, .K12, .S02] := by
  apply to_derivable
  have hs : ss02⁻¹ = ss02 := by
    change (ss12 * ss01 * ss12)⁻¹ = _
    simp only [mul_inv_rev, ss01_inv, ss12_inv, mul_assoc]; rfl
  change u hh01 = ss02 * u hh12 * ss02
  have he (g : G) : ss02 * g * ss02 = conj ss02 g := by rw [conj_def, hs]
  rw [he, conj02]
  simp only [hh01, hh12, map_mul, conj12_k0, conj12_k1, conj12_k2, conj01_k0,
    conj01_k1, conj01_k2, conj12_ii, conj01_ii]
  exact congrArg (fun g : G => ii * g) (k_commute 0 1).eq

theorem cx02_eval : u cx02 = k 2 * cQ ^ 2 * k 2 * ii := by
  change ss12 * (k 1 * dQ ^ 2 * k 1 * ii) * ss12 = _
  rw [← conj12_def]
  simp only [map_mul, map_pow, conj12_k1, conj12_d, conj12_ii]

theorem cx20_eval : u cx20 = k 0 * cQ ^ 2 * k 0 * ii := by
  change ss12 * (k 0 * dQ ^ 2 * k 0 * ii) * ss12 = _
  rw [← conj12_def]
  simp only [map_mul, map_pow, conj12_k0, conj12_d, conj12_ii]

theorem r30 : Eqn [.CX12] [.S01, .CX02, .S01] := by
  apply to_derivable
  change zQ = ss01 * u cx02 * ss01
  rw [← conj01_def, cx02_eval]
  simp only [map_mul, map_pow, conj01_k2, conj01_c, conj01_ii]
  rfl

theorem r31 : Eqn [.CX21] [.S01, .CX20, .S01] := by
  apply to_derivable
  change yQ = ss01 * u cx20 * ss01
  rw [← conj01_def, cx20_eval]
  simp only [map_mul, map_pow, conj01_k0, conj01_c, conj01_ii]
  rfl

theorem k_inv (j : Fin 3) : (k j)⁻¹ = k j * ii := by
  apply (eq_inv_of_mul_eq_one_right ?_).symm
  have h := of_derivable (K_inverse j)
  simpa only [map_mul, map_one, (scalar_commute (W.K j)).eq] using h

theorem ccx_eval (j : Fin 3) : u (ccx j) = conj (k j) (u Cert.ccZ) := by
  simp only [ccx, map_mul]
  rw [conj_def, k_inv]
  rw [(scalar_commute (W.K j)).eq]

theorem hh12_k1 : u hh12 * k 1 = k 2 := by
  have hki : ii * (k 1 * k 1) = 1 := by
    have h := of_derivable (K_inverse' 1)
    simpa only [map_mul, map_one, mul_assoc] using h
  change (ii * k 1 * k 2) * k 1 = k 2
  calc
    (ii * k 1 * k 2) * k 1 = ii * k 1 * (k 2 * k 1) := by group
    _ = ii * (k 1 * k 1) * k 2 := by rw [(k_commute 2 1).eq]; group
    _ = k 2 := by rw [hki, one_mul]

theorem hh12_inv : (u hh12)⁻¹ = u hh12 := by
  apply inv_of_square
  simpa only [map_mul, map_one] using of_derivable (generator_involution .K12)

theorem r17 : Eqn [.CCX01] [.K12, .CCX02, .K12] := by
  apply to_derivable
  change u (ccx 2) = u hh12 * u (ccx 1) * u hh12
  have he (g : G) : u hh12 * g * u hh12 = conj (u hh12) g := by rw [conj_def, hh12_inv]
  rw [he, ccx_eval, ccx_eval, ← conj_mul, hh12_k1]

theorem r1 : Eqn [.CZ01] [.K12, .CX01, .K12] := by
  apply to_derivable
  have ha : aQ = conj (k 1) (dQ ^ 2) := by rw [conj_def, k_inv]; rfl
  have he (g : G) : u hh12 * g * u hh12 = conj (u hh12) g := by rw [conj_def, hh12_inv]
  change dQ ^ 2 = u hh12 * aQ * u hh12
  rw [he, ha, ← conj_mul, hh12_k1]
  have hd : Commute (k 2) dQ := of_derivable (Derivable.of (Rel.comm_2_01 Local.K))
  exact (conj_of_commute (hd.pow_right 2)).symm

theorem r39 : Eqn [.K01, .K12] [.K12, .K01] := by
  apply to_derivable
  have hi01 := scalar_commute hh01
  have hk1 : Commute (u hh01) (k 1) :=
    (((scalar_commute (W.K 1)).mul_left (k_commute 0 1)).mul_left (Commute.refl _))
  have hk2 : Commute (u hh01) (k 2) :=
    (((scalar_commute (W.K 2)).mul_left (k_commute 0 2)).mul_left (k_commute 1 2))
  exact ((hi01.symm.mul_right hk1).mul_right hk2).eq

theorem r46 : Eqn [.CCX01, .CCX02] [.CCX02, .CCX01, .CCX02, .CCX01] := by
  apply to_derivable
  have h := congrArg (conj ss02) (of_derivable MonomialBraidConcrete.toffoli_braid)
  simp only [map_mul, ccx, conj02, conj12_k0, conj12_k1, conj12_k2, conj01_k0,
    conj01_k1, conj01_k2, conj12_Q, conj01_Q, conj12_ii, conj01_ii] at h
  have hb : u (ccx 2) * u (ccx 1) * u (ccx 2) =
      u (ccx 1) * u (ccx 2) * u (ccx 1) := h
  have hs : u (ccx 2) * u (ccx 2) = 1 := by
    simpa only [map_mul, map_one] using of_derivable (ccx_square 2 ccZ_square)
  have ht := congrArg (fun g : G => g * u (ccx 2)) hb
  simpa only [mul_assoc, hs, mul_one] using ht

theorem r43 : Eqn [.CX01, .CZ12] [.CZ12, .CZ02, .CX01] := by
  apply to_derivable
  have h15 : cQ ^ 2 = (aQ * bQ ^ 2 * aQ) * bQ ^ 2 := by
    have h := of_derivable (Derivable.of Rel.c15)
    simp only [map_mul, map_pow] at h
    have he : cQ ^ 2 = xQ * aQ * bQ ^ 2 * aQ * xQ := by
      rw [c_as_conjugate]
      have ha : aQ * (aQ * (bQ * aQ * xQ)) = bQ * aQ * xQ := by rw [← mul_assoc, a_square, one_mul]
      have hx (g : G) : xQ * (xQ * g) = g := by rw [← mul_assoc, x_square, one_mul]
      simp only [sq, mul_assoc, hx, ← mul_assoc aQ aQ, a_square, one_mul]
    rw [he]; exact h
  have hb4 : bQ ^ 2 * bQ ^ 2 = 1 := by rw [← pow_add]; exact b_fourth
  have hc : u cz02 = cQ ^ 2 := by
    change ss01 * bQ ^ 2 * ss01 = _
    rw [← conj01_def, map_pow, conj01_b]
  change aQ * bQ ^ 2 = bQ ^ 2 * u cz02 * aQ
  rw [hc, ((c_b_commute.pow_left 2).pow_right 2).symm.eq, h15]
  simp only [mul_assoc, hb4, one_mul, a_square, mul_one]

theorem r5 : Eqn [.CX20] [.X1, .CCX12, .X1, .CCX12] := by
  apply to_derivable
  have hc : u cx20 = conj (k 0) (cQ ^ 2) := by
    rw [cx20_eval, conj_def, k_inv]; rfl
  have hf : Commute (u (W.X 1)) (k 0) := by
    exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Xl * Two.W2.Ku) (v := Two.W2.Ku * Two.W2.Xl) (by decide +kernel)))
  have ht : u (ccx 0) = conj (k 0) (u Cert.ccZ) := ccx_eval 0
  have hq : u Cert.ccZ * u Cert.ccZ = 1 := by
    simpa only [map_mul, map_one] using of_derivable ccZ_square
  have hflip : u (W.X 1) * u Cert.ccZ * u (W.X 1) = u Cert.ccZ * cQ ^ 2 :=
    of_derivable X1_ccZ_flip
  have hdiag : Commute (u Cert.ccZ) cQ := by
    rw [u_ccZ]
    exact (((Commute.refl cQ).inv_left).mul_left c_conjugate_commute.symm).mul_left c_b_commute.symm.inv_left
  change u cx20 = u (W.X 1) * u (ccx 0) * u (W.X 1) * u (ccx 0)
  rw [hc, ht]
  symm
  calc
    u (W.X 1) * conj (k 0) (u Cert.ccZ) * u (W.X 1) * conj (k 0) (u Cert.ccZ) =
      conj (k 0) (u (W.X 1) * u Cert.ccZ * u (W.X 1)) * conj (k 0) (u Cert.ccZ) := by
        simp only [conj_def]
        calc
          _ = (u (W.X 1) * k 0) * u Cert.ccZ * ((k 0)⁻¹ * u (W.X 1)) *
            (k 0 * u Cert.ccZ * (k 0)⁻¹) := by group
          _ = _ := by rw [hf.eq, hf.inv_right.symm.eq]; group
    _ = conj (k 0) (u Cert.ccZ * cQ ^ 2 * u Cert.ccZ) := by rw [hflip, ← map_mul]
    _ = conj (k 0) (cQ ^ 2) := by
      rw [(hdiag.pow_right 2).eq, mul_assoc, hq, mul_one]

theorem conj_hh01_b2 : conj (u hh01) (bQ ^ 2) = yQ := by
  have h0 : Commute (k 0) bQ := of_derivable (Derivable.of (Rel.comm_0_12 Local.K))
  have he : u hh01 = k 1 * (k 0 * ii) := by
    change ii * k 0 * k 1 = _
    rw [(scalar_commute (W.K 0)).eq, mul_assoc, (scalar_commute (W.K 1)).eq,
      ← mul_assoc, (k_commute 0 1).eq, mul_assoc]
  rw [he, conj_mul, conj_mul, conj_of_commute ((scalar_commute W.CS12).pow_right 2),
    conj_of_commute (h0.pow_right 2), conj_def, k_inv]
  rfl

theorem conj_hh01_c2 : conj (u hh01) (cQ ^ 2) = u cx20 := by
  have hhc : Commute ss01 (u hh01) := by
    change ss01 * u hh01 = u hh01 * ss01
    have hb : u hh01 = ss01 * u hh01 * ss01 := of_derivable r35
    have h := congrArg (fun g : G => ss01 * g) hb
    have hss (g : G) : ss01 * (ss01 * g) = g := by rw [← mul_assoc, swap_square, one_mul]
    simpa only [map_mul, mul_assoc, hss] using h
  have hc : cQ ^ 2 = conj ss01 (bQ ^ 2) := by rw [map_pow, conj01_b]
  rw [hc, ← conj_mul, hhc.symm.eq, conj_mul, conj_hh01_b2]
  change conj ss01 (k 1 * bQ ^ 2 * k 1 * ii) = _
  simp only [map_mul, map_pow, conj01_k1, conj01_b, conj01_ii]
  exact cx20_eval.symm

theorem r6 : Eqn [.CX21] [.CX20, .CX01, .CX20, .CX01] := by
  apply to_derivable
  let J := (conj ss01).comp (conj (u hh01))
  have hja : J aQ = aQ := by
    have hh : conj (u hh01) aQ = xQ := by
      rw [conj_def]
      have hi : (u hh01)⁻¹ = u hh01 := by
        apply inv_of_square
        simpa only [map_mul, map_one] using of_derivable (generator_involution .K01)
      rw [hi]; exact (of_derivable r12).symm
    change conj ss01 (conj (u hh01) aQ) = _
    rw [hh, conj_def, ss01_inv]
    have hs := congrArg (conj ss01) swap_conjugates_a
    simp only [map_mul, conj01_def] at hs
    exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
      (w := sw * cu * sw) (v := cl) (by decide +kernel)))
  have hjb : J (bQ ^ 2) = u cx20 := by
    change conj ss01 (conj (u hh01) (bQ ^ 2)) = _
    rw [conj_hh01_b2]
    change conj ss01 (k 1 * bQ ^ 2 * k 1 * ii) = _
    simp only [map_mul, map_pow, conj01_k1, conj01_b, conj01_ii]
    exact cx20_eval.symm
  have hjc : J (u cz02) = yQ := by
    have hc : u cz02 = cQ ^ 2 := by
      change ss01 * bQ ^ 2 * ss01 = _
      rw [← conj01_def, map_pow, conj01_b]
    change conj ss01 (conj (u hh01) (u cz02)) = _
    rw [hc, conj_hh01_c2]
    rw [conj01_def]
    exact (of_derivable r31).symm
  have hb : aQ * bQ ^ 2 = bQ ^ 2 * u cz02 * aQ := of_derivable r43
  have h := congrArg J hb
  rw [map_mul, map_mul, map_mul, hja, hjb, hjc] at h
  have hs : u cx20 * u cx20 = 1 := by
    simpa only [map_mul, map_one] using of_derivable (generator_involution .CX20)
  have he := congrArg (fun g : G => u cx20 * g * aQ) h
  simpa only [mul_assoc, hs, a_square, mul_one, ← mul_assoc (u cx20) (u cx20), one_mul] using he.symm

theorem r16 : Eqn [.Z2] [.S02, .Z0, .S02] := by
  apply to_derivable
  have hz0 : u (W.S 0 ^ 2) = (k 0)⁻¹ * u (W.X 0) * k 0 := by
    rw [k_inv]
    exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Su ^ 2) (v := (Two.W2.Ku * Two.W2.I) * Two.W2.Xu * Two.W2.Ku)
      (by decide +kernel)))
  have hz2 : u (W.S 2 ^ 2) = (k 2)⁻¹ * u (W.X 2) * k 2 := by
    rw [k_inv]
    exact of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
      (w := Two.W2.Sl ^ 2) (v := (Two.W2.Kl * Two.W2.I) * Two.W2.Xl * Two.W2.Kl)
      (by decide +kernel)))
  have hs : ss02⁻¹ = ss02 := by
    change (ss12 * ss01 * ss12)⁻¹ = _
    simp only [mul_inv_rev, ss01_inv, ss12_inv, mul_assoc]; rfl
  have hx : conj ss02 (u (W.X 0)) = u (W.X 2) := by
    rw [conj_def, hs]; exact (of_derivable r15).symm
  have hk : conj ss02 (k 0) = k 2 := by
    rw [conj02, conj12_k0, conj01_k0, conj12_k1]
  change u (W.S 2 ^ 2) = ss02 * u (W.S 0 ^ 2) * ss02
  have he (g : G) : ss02 * g * ss02 = conj ss02 g := by rw [conj_def, hs]
  rw [he, hz0, map_mul, map_mul, map_inv, hk, hx, ← hz2]

end
end QCert.CliffordCS3.Three.PermutationBase
