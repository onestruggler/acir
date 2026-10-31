/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The permutation proof alphabet inside Clifford+CS

The images are explicit circuits. Only selected Figure 4 equations are
transported; the unused four-level generator Kc is sent to the identity.
-/
import QCert.ToffoliHadamard.Syntax
import QCert.CliffordCS3.Three.MonomialBraidConcrete
import QCert.CliffordCS3.Three.PhaseFlip

set_option maxRecDepth 10000

namespace QCert.CliffordCS3.Three.PermutationBase
open QuotientGroup Monomial
open ToffoliHadamard (Sym1)
noncomputable section

def swap12 : Word Gen := W.CX12 * W.CX21 * W.CX12
def swap02 : Word Gen := swap12 * swapWord * swap12
def cx02 : Word Gen := swap12 * W.CX01 * swap12
def cx20 : Word Gen := swap12 * W.CX10 * swap12
def cz02 : Word Gen := swapWord * W.CS12 ^ 2 * swapWord
def hh01 : Word Gen := W.I * W.K 0 * W.K 1
def hh12 : Word Gen := W.I * W.K 1 * W.K 2

def decode : Sym1 → Word Gen
  | .X0 => W.X 0 | .X1 => W.X 1 | .X2 => W.X 2
  | .CX01 => W.CX01 | .CX02 => cx02 | .CX10 => W.CX10
  | .CX12 => W.CX12 | .CX20 => cx20 | .CX21 => W.CX21
  | .CCX01 => ccx 2 | .CCX02 => ccx 1 | .CCX12 => ccx 0
  | .Z0 => W.S 0 ^ 2 | .Z1 => W.S 1 ^ 2 | .Z2 => W.S 2 ^ 2
  | .CZ01 => W.CS01 ^ 2 | .CZ02 => cz02 | .CZ12 => W.CS12 ^ 2
  | .K01 => hh01 | .K12 => hh12
  | .S01 => swapWord | .S02 => swap02 | .S12 => swap12
  | .CCZ => Cert.ccZ | .Kc => 1

def D : Word Sym1 →* Word Gen := FreeMonoid.lift decode
abbrev word (l : List Sym1) : Word Gen := D (FreeMonoid.ofList l)
abbrev Eqn (l r : List Sym1) : Prop := Derivable Rel (word l) (word r)

private def cu : Word Two.Gen2 := Two.W2.Ku * Two.W2.CS ^ 2 * Two.W2.Ku * Two.W2.I
private def cl : Word Two.Gen2 := Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I
private def sw : Word Two.Gen2 := cl * cu * cl
private def hh : Word Two.Gen2 := Two.W2.I * Two.W2.Ku * Two.W2.Kl

theorem swap12_square : Derivable Rel (swap12 * swap12) 1 :=
  Two.derivable_embed 1 (Two.derivable_of_check2 (w := sw * sw) (v := 1) (by decide +kernel))

theorem r2 : Eqn [.X1] [.CX01, .X0, .CX01, .X0] :=
  Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Xl) (v := cl * Two.W2.Xu * cl * Two.W2.Xu) (by decide +kernel))

theorem r4 : Eqn [.Z1] [.K12, .X1, .K12] :=
  Two.derivable_embed 1 (Two.derivable_of_check2
    (w := Two.W2.Su ^ 2) (v := hh * Two.W2.Xu * hh) (by decide +kernel))

theorem r7 : Eqn [.CX12] [.K12, .CX21, .K12] :=
  Two.derivable_embed 1 (Two.derivable_of_check2 (w := cl) (v := hh * cu * hh) (by decide +kernel))

theorem r8 : Eqn [.S12] [.CX12, .CX21, .CX12] := Derivable.refl _
theorem r9 : Eqn [.CX02] [.S12, .CX01, .S12] := Derivable.refl _
theorem r13 : Eqn [.S01] [.CX01, .CX10, .CX01] := Derivable.refl _

theorem r10 : Eqn [.S02] [.CX02, .CX20, .CX02] := by
  apply to_derivable
  change u swap02 = u (cx02 * cx20 * cx02)
  have hs : u swap12 * u swap12 = 1 := by
    simpa only [map_mul, map_one] using of_derivable swap12_square
  have hss (g : G) : u swap12 * (u swap12 * g) = g := by rw [← mul_assoc, hs, one_mul]
  simp only [swap02, cx02, cx20, swapWord, map_mul, mul_assoc, hss]

theorem r12 : Eqn [.CX10] [.K01, .CX01, .K01] :=
  Two.derivable_embed 0 (Two.derivable_of_check2 (w := cu) (v := hh * cl * hh) (by decide +kernel))

theorem r14 : Eqn [.CCX02] [.S01, .CCX12, .S01] :=
  MonomialBraidConcrete.swap_token.symm

theorem r20 : Eqn [.S12] [.CZ12, .K12, .CZ12, .K12, .CZ12, .K12] := by
  have h := Two.derivable_embed 1 (Two.derivable_of_check2
    (w := sw) (v := (Two.W2.CS ^ 2 * hh) ^ 3) (by decide +kernel))
  change Derivable Rel swap12 ((W.CS12 ^ 2 * hh12) * (W.CS12 ^ 2 * hh12) * (W.CS12 ^ 2 * hh12))
  simpa only [map_pow, pow_succ, pow_zero, one_mul, mul_assoc] using h

theorem r28 : Eqn [.X1] [.S01, .X0, .S01] :=
  Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Xl) (v := sw * Two.W2.Xu * sw) (by decide +kernel))

theorem r29 : Eqn [.CX20] [.S02, .CX02, .S02] := by
  apply to_derivable
  change u cx20 = u (swap02 * cx02 * swap02)
  have hs : u swap12 * u swap12 = 1 := by
    simpa only [map_mul, map_one] using of_derivable swap12_square
  have hss (g : G) : u swap12 * (u swap12 * g) = g := by rw [← mul_assoc, hs, one_mul]
  simp only [cx20, cx02, swap02, map_mul, mul_assoc, hss]
  have h := congrArg (fun v : G => u swap12 * v * u swap12) swap_conjugates_a.symm
  simpa only [mul_assoc] using h

theorem r34 : Eqn [.Z1] [.S01, .Z0, .S01] :=
  Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Sl ^ 2) (v := sw * Two.W2.Su ^ 2 * sw) (by decide +kernel))

theorem r35 : Eqn [.K01] [.S01, .K01, .S01] :=
  Two.derivable_embed 0 (Two.derivable_of_check2 (w := hh) (v := sw * hh * sw) (by decide +kernel))

theorem r36 : Eqn [.CCX12, .CX10] [.CX10, .CCX12] := token6_CX10_commute

theorem r38 : Eqn [.X0, .CX10] [.CX10, .X0] :=
  Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Xu * cu) (v := cu * Two.W2.Xu) (by decide +kernel))

theorem r41 : Eqn [.K01, .Z0] [.X0, .K01] :=
  Two.derivable_embed 0 (Two.derivable_of_check2
    (w := hh * Two.W2.Su ^ 2) (v := Two.W2.Xu * hh) (by decide +kernel))

theorem r44 : Eqn [.CX12, .CCX12] [.CCX12, .CX10, .CX12] := CX12_token6

theorem r45 : Eqn [.CCX12, .CX01] [.CX01, .CCX02, .CCX12, .CCX02] := by
  apply to_derivable
  have h := of_derivable MonomialBraidConcrete.CX01_toffoli_conjugate
  have he := congrArg (fun g : G => aQ * g) h
  have haa (g : G) : aQ * (aQ * g) = g := by rw [← mul_assoc, a_square, one_mul]
  simpa only [map_mul, mul_assoc, haa] using he

theorem generator_involution (g : Sym1) : Derivable Rel (decode g * decode g) 1 := by
  cases g with
  | X0 => exact X_square 0
  | X1 => exact X_square 1
  | X2 => exact X_square 2
  | CX01 =>
    exact Two.derivable_embed 0 (Two.derivable_of_check2 (w := cl * cl) (v := 1) (by decide +kernel))
  | CX10 =>
    exact Two.derivable_embed 0 (Two.derivable_of_check2 (w := cu * cu) (v := 1) (by decide +kernel))
  | CX12 =>
    exact Two.derivable_embed 1 (Two.derivable_of_check2 (w := cl * cl) (v := 1) (by decide +kernel))
  | CX21 =>
    exact Two.derivable_embed 1 (Two.derivable_of_check2 (w := cu * cu) (v := 1) (by decide +kernel))
  | CX02 =>
    exact conjugate_square swap12_square swap12_square
      (Two.derivable_embed 0 (Two.derivable_of_check2 (w := cl * cl) (v := 1) (by decide +kernel)))
  | CX20 =>
    exact conjugate_square swap12_square swap12_square
      (Two.derivable_embed 0 (Two.derivable_of_check2 (w := cu * cu) (v := 1) (by decide +kernel)))
  | CCX01 => exact ccx_square 2 ccZ_square
  | CCX02 => exact ccx_square 1 ccZ_square
  | CCX12 => exact ccx_square 0 ccZ_square
  | Z0 => exact Derivable.of (Rel.c3 0)
  | Z1 => exact Derivable.of (Rel.c3 1)
  | Z2 => exact Derivable.of (Rel.c3 2)
  | CZ01 => exact Derivable.of (Rel.c5 0)
  | CZ12 => exact Derivable.of (Rel.c5 1)
  | CZ02 => exact conjugate_square Swap01.sq Swap01.sq (Derivable.of (Rel.c5 1))
  | K01 =>
    exact Two.derivable_embed 0 (Two.derivable_of_check2 (w := hh * hh) (v := 1) (by decide +kernel))
  | K12 =>
    exact Two.derivable_embed 1 (Two.derivable_of_check2 (w := hh * hh) (v := 1) (by decide +kernel))
  | S01 => exact Swap01.sq
  | S12 => exact swap12_square
  | S02 => exact conjugate_square swap12_square swap12_square Swap01.sq
  | Kc => exact Derivable.refl _
  | CCZ => exact ccZ_square

theorem X0_commutes_K (j : Fin 2) : Commute (u (W.X 0)) (u (W.K j.succ)) := by
  have hk : Commute (u (W.K 0)) (u (W.K j.succ)) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.K 0 j.succ (by fin_cases j <;> decide)))
  have hs : Commute (u (W.S 0)) (u (W.K j.succ)) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.S Local.K 0 j.succ (by fin_cases j <;> decide)))
  have hi : Commute (u W.I) (u (W.K j.succ)) :=
    of_derivable (Derivable.of (Rel.comm_i (Local.K.on j.succ) (by fin_cases j <;> decide)))
  simpa only [W.X, map_mul] using (((hk.mul_left hs).mul_left hs).mul_left hk).mul_left hi

theorem X0_commutes_b : Commute (u (W.X 0)) bQ := by
  have hk : Commute (u (W.K 0)) bQ := of_derivable (Derivable.of (Rel.comm_0_12 Local.K))
  have hs : Commute (u (W.S 0)) bQ := of_derivable (Derivable.of (Rel.comm_0_12 Local.S))
  have hi : Commute (u W.I) bQ := of_derivable (Derivable.of (Rel.comm_i .CS₁₂ (by decide)))
  simpa only [W.X, map_mul] using (((hk.mul_left hs).mul_left hs).mul_left hk).mul_left hi

theorem X0_commutes_i : Commute (u (W.X 0)) (u W.I) := by
  exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Xu * Two.W2.I) (v := Two.W2.I * Two.W2.Xu) (by decide +kernel)))

theorem r26 : Eqn [.CX12, .X0] [.X0, .CX12] := by
  apply to_derivable
  have hk : Commute (u (W.X 0)) (u (W.K 2)) := X0_commutes_K 1
  have h := ((((hk.mul_right X0_commutes_b).mul_right X0_commutes_b).mul_right hk).mul_right
    X0_commutes_i).symm
  simpa only [← map_mul] using h.eq

theorem r27 : Eqn [.X0, .K12] [.K12, .X0] := by
  apply to_derivable
  have hk1 : Commute (u (W.X 0)) (u (W.K 1)) := X0_commutes_K 0
  have hk2 : Commute (u (W.X 0)) (u (W.K 2)) := X0_commutes_K 1
  simpa only [← map_mul] using ((X0_commutes_i.mul_right hk1).mul_right hk2).eq

theorem r37 : Eqn [.X0, .CCX12] [.CCX12, .X0] := by
  apply to_derivable
  have hS : Commute s0Q (u Cert.ccZ) := by
    rw [u_ccZ]
    exact ((s0_c_commute.inv_right).mul_right s0_D_commute).mul_right s0_b_commute.inv_right
  have hi : (u (W.K 0))⁻¹ = u (W.I * W.K 0) := by
    apply (eq_inv_of_mul_eq_one_left ?_).symm
    simpa only [map_mul, map_one] using of_derivable (K_inverse' 0)
  have hkx : (u (W.K 0))⁻¹ * u (W.X 0) * u (W.K 0) = s0Q ^ 2 := by
    rw [hi]
    have h := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
      (w := (Two.W2.I * Two.W2.Ku) * Two.W2.Xu * Two.W2.Ku)
      (v := Two.W2.Su ^ 2) (by decide +kernel)))
    simpa only [map_mul, map_pow] using h
  have hcon : Commute ((u (W.K 0))⁻¹ * u (W.X 0) * u (W.K 0)) (u Cert.ccZ) := by
    rw [hkx]; exact hS.pow_left 2
  have h := commute_conjugate hcon
  rw [hi] at h
  simpa only [← map_mul] using h.eq

theorem X0_commutes_swap12 : Commute (u (W.X 0)) (u swap12) := by
  have hk1 : Commute (u (W.X 0)) (u (W.K 1)) := X0_commutes_K 0
  have hk2 : Commute (u (W.X 0)) (u (W.K 2)) := X0_commutes_K 1
  have hz : Commute (u (W.X 0)) zQ := by
    simpa only [zQ, W.CX12, W.CX, map_mul] using
      ((((hk2.mul_right X0_commutes_b).mul_right X0_commutes_b).mul_right hk2).mul_right X0_commutes_i)
  have hy : Commute (u (W.X 0)) yQ := by
    simpa only [yQ, W.CX21, W.CX, map_mul] using
      ((((hk1.mul_right X0_commutes_b).mul_right X0_commutes_b).mul_right hk1).mul_right X0_commutes_i)
  simpa only [swap12, map_mul] using (hz.mul_right hy).mul_right hz

theorem r15 : Eqn [.X2] [.S02, .X0, .S02] := by
  apply to_derivable
  change u (W.X 2) = u (swap02 * W.X 0 * swap02)
  have hs : u swap12 * u swap12 = 1 := by
    simpa only [map_mul, map_one] using of_derivable swap12_square
  have hP : u swap12 * u (W.X 0) * u swap12 = u (W.X 0) := by
    rw [X0_commutes_swap12.symm.eq, mul_assoc, hs, mul_one]
  have hW : u swapWord * u (W.X 0) * u swapWord = u (W.X 1) := by
    exact (of_derivable r28).symm
  have hX : u swap12 * u (W.X 1) * u swap12 = u (W.X 2) :=
    of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
      (w := sw * Two.W2.Xu * sw) (v := Two.W2.Xl) (by decide +kernel)))
  symm
  simp only [swap02, map_mul]
  calc
    (u swap12 * u swapWord * u swap12) * u (W.X 0) * (u swap12 * u swapWord * u swap12) =
        u swap12 * u swapWord * (u swap12 * u (W.X 0) * u swap12) * u swapWord * u swap12 := by group
    _ = u swap12 * u swapWord * u (W.X 0) * u swapWord * u swap12 := by rw [hP]
    _ = u swap12 * (u swapWord * u (W.X 0) * u swapWord) * u swap12 := by group
    _ = u (W.X 2) := by rw [hW, hX]

theorem r42 : Eqn [.X0, .CCX01] [.CCX01, .CX12, .X0] := by
  apply to_derivable
  have hk : Commute (u (W.X 0)) (u (W.K 2)) := X0_commutes_K 1
  have hi : (u (W.K 2))⁻¹ = u (W.I * W.K 2) := by
    apply (eq_inv_of_mul_eq_one_left ?_).symm
    simpa only [map_mul, map_one] using of_derivable (K_inverse' 2)
  have ht : u (ccx 2) = u (W.K 2) * u Cert.ccZ * (u (W.K 2))⁻¹ := by rw [hi]; rfl
  have hf := of_derivable X0_ccZ_flip
  simp only [map_mul, map_pow] at hf
  have hcx : u (W.K 2) * bQ ^ 2 * (u (W.K 2))⁻¹ = zQ := by
    rw [hi]
    exact of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
      (w := Two.W2.Kl * Two.W2.CS ^ 2 * (Two.W2.I * Two.W2.Kl))
      (v := cl) (by decide +kernel)))
  have hconj : u (W.X 0) * u (ccx 2) * u (W.X 0) = u (ccx 2) * zQ := by
    rw [ht]
    calc
      u (W.X 0) * (u (W.K 2) * u Cert.ccZ * (u (W.K 2))⁻¹) * u (W.X 0) =
          (u (W.X 0) * u (W.K 2)) * u Cert.ccZ * ((u (W.K 2))⁻¹ * u (W.X 0)) := by group
      _ = (u (W.K 2) * u (W.X 0)) * u Cert.ccZ * (u (W.X 0) * (u (W.K 2))⁻¹) := by
        rw [hk.eq, hk.symm.inv_left.eq]
      _ = u (W.K 2) * (u (W.X 0) * u Cert.ccZ * u (W.X 0)) * (u (W.K 2))⁻¹ := by group
      _ = u (W.K 2) * (u Cert.ccZ * bQ ^ 2) * (u (W.K 2))⁻¹ := by rw [hf]
      _ = (u (W.K 2) * u Cert.ccZ * (u (W.K 2))⁻¹) * zQ := by rw [← hcx]; group
  have hx : u (W.X 0) * u (W.X 0) = 1 := by
    simpa only [map_mul, map_one] using of_derivable (X_square 0)
  have h := congrArg (fun v : G => v * u (W.X 0)) hconj
  simpa only [map_mul, mul_assoc, hx, mul_one] using h

end
end QCert.CliffordCS3.Three.PermutationBase

