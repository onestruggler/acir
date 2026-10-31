/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The two controlled Hadamards commute

Both controls are on wire 1. Their target-wire factors commute by the
structural equations and C12; no three-qubit semantic completeness is used.
-/
import QCert.CliffordCS3.Three.RecoveryWords
import QCert.CliffordCS3.Three.PermutationTransport

set_option maxRecDepth 10000

namespace QCert.CliffordCS3.Three.BlockVertical

open QuotientGroup RecoveryWords PermutationBase Monomial

def blockWord (j : Fin 3) (d : Word Gen) : Word Gen :=
  commW (W.K j * W.S j * invW (W.K j)) (invW d) * d

def B0 : G := u (blockWord 0 W.CS01)
def B2 : G := u (blockWord 2 W.CS12)

def controlled {H : Type*} [Group H] (k s d : H) : H :=
  (k * s * k⁻¹) * d⁻¹ * (k * s * k⁻¹)⁻¹ * d * d

theorem u_blockWord (j : Fin 3) (d : Word Gen) :
    u (blockWord j d) = controlled (u (W.K j)) (u (W.S j)) (u d) := by
  simp only [blockWord, map_mul, u_commW, u_invW, controlled, inv_inv]

theorem map_controlled {H H' : Type*} [Group H] [Group H']
    (f : H →* H') (k s d : H) :
    f (controlled k s d) = controlled (f k) (f s) (f d) := by
  simp only [controlled, map_mul, map_inv]

theorem commute_controlled {H : Type*} [Group H] {x k s d : H}
    (hk : Commute x k) (hs : Commute x s) (hd : Commute x d) :
    Commute x (controlled k s d) :=
  (((((hk.mul_right hs).mul_right hk.inv_right).mul_right hd.inv_right).mul_right
    ((hk.mul_right hs).mul_right hk.inv_right).inv_right).mul_right hd).mul_right hd

theorem blocks_commute : Commute B0 B2 := by
  have hkk : Commute (k 0) (k 2) := k_commute 0 2
  have hsk : Commute (s 0) (k 2) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.S Local.K 0 2 (by decide)))
  have hdk : Commute dQ (k 2) :=
    (of_derivable (Derivable.of (Rel.comm_2_01 Local.K))).symm
  have hks : Commute (k 0) (s 2) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.S 0 2 (by decide)))
  have hss : Commute (s 0) (s 2) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.S Local.S 0 2 (by decide)))
  have hds : Commute dQ (s 2) :=
    (of_derivable (Derivable.of (Rel.comm_2_01 Local.S))).symm
  have hkp : Commute (k 0) bQ := of_derivable (Derivable.of (Rel.comm_0_12 Local.K))
  have hsp : Commute (s 0) bQ := of_derivable (Derivable.of (Rel.comm_0_12 Local.S))
  have hdp : Commute dQ bQ := b_d_commute.symm
  rw [B0, B2, u_blockWord, u_blockWord]
  exact commute_controlled
    (commute_controlled hkk.symm hsk.symm hdk.symm).symm
    (commute_controlled hks.symm hss.symm hds.symm).symm
    (commute_controlled hkp.symm hsp.symm hdp.symm).symm

private def cu : Word Two.Gen2 := Two.W2.Ku * Two.W2.CS ^ 2 * Two.W2.Ku * Two.W2.I
private def cl : Word Two.Gen2 := Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I
private def sw2 : Word Two.Gen2 := cl * cu * cl

theorem conj12_s0 : conj ss12 (s 0) = s 0 := by
  apply conj_of_commute
  have hk1 : Commute (s 0) (k 1) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.S Local.K 0 1 (by decide)))
  have hk2 : Commute (s 0) (k 2) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.S Local.K 0 2 (by decide)))
  have hb : Commute (s 0) bQ := of_derivable (Derivable.of (Rel.comm_0_12 Local.S))
  have hi := (scalar_commute (W.S 0)).symm
  have hy : Commute (s 0) yQ := by
    simpa only [yQ, W.CX21, W.CX, map_mul] using
      (((hk1.mul_right hb).mul_right hb).mul_right hk1).mul_right hi
  have hz : Commute (s 0) zQ := by
    simpa only [zQ, W.CX12, W.CX, map_mul] using
      (((hk2.mul_right hb).mul_right hb).mul_right hk2).mul_right hi
  exact ((hz.mul_right hy).mul_right hz).symm

theorem conj01_s0 : conj ss01 (s 0) = s 1 := by
  rw [conj01_def]
  exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := sw2 * Two.W2.Su * sw2) (v := Two.W2.Sl) (by decide +kernel)))

theorem conj12_s1 : conj ss12 (s 1) = s 2 := by
  rw [conj12_def]
  exact of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := sw2 * Two.W2.Su * sw2) (v := Two.W2.Sl) (by decide +kernel)))

theorem conjugate_block : conj ss02 B0 = B2 := by
  rw [B0, u_blockWord, map_controlled]
  change controlled (conj ss02 (k 0)) (conj ss02 (s 0)) (conj ss02 dQ) = B2
  rw [conj02, conj02, conj02, conj12_k0, conj01_k0, conj12_k1,
    conj12_s0, conj01_s0, conj12_s1, conj12_d, conj01_c, conj12_b]
  exact (u_blockWord 2 W.CS12).symm

theorem conj12_c : conj ss12 cQ = dQ := by
  rw [← conj12_d, conj12_def, conj12_def]
  have hs : ss12 * ss12 = 1 := by
    simpa only [map_mul, map_one] using of_derivable swap12_square
  have hh (z : G) : ss12 * (ss12 * z) = z := by rw [← mul_assoc, hs, one_mul]
  simp only [mul_assoc, hh, hs, mul_one]

theorem conj02_c : conj ss02 cQ = cQ := by
  rw [conj02, conj12_c, conj01_d, conj12_d]

theorem conj02_Q : conj ss02 LocalKZ.Q = LocalKZ.Q := by
  rw [conj02, conj12_Q, conj01_Q, conj12_Q]

theorem conj02_correction :
    conj ss02 (LocalKZ.C ^ 2 * LocalKZ.Q) = LocalKZ.C ^ 2 * LocalKZ.Q := by
  rw [map_mul, map_pow, conj02_c, conj02_Q]

theorem conj02_cx12 : conj ss02 (u W.CX12) = u W.CX10 := by
  have hk : conj ss02 (k 2) = k 0 := by
    rw [conj02, conj12_k2, conj01_k1, conj12_k0]
  have hb : conj ss02 bQ = dQ := by
    rw [conj02, conj12_b, conj01_b, conj12_c]
  have hi : conj ss02 ii = ii := by
    rw [conj02, conj12_ii, conj01_ii, conj12_ii]
  change conj ss02 (k 2 * bQ * bQ * k 2 * ii) = k 0 * dQ * dQ * k 0 * ii
  simp only [map_mul, hk, hb, hi]

end QCert.CliffordCS3.Three.BlockVertical
