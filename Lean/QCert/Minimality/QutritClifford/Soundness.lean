/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Soundness of Cliff₃

Every rule of Figure 4, with (E) corrected, and every law of the symmetry
holds in the semantics of Definition 17, each decided over ℤ[ζ₁₂] on row
tries.  (E) as printed, with `ω₁₂⁷`, is unsound: its two sides differ by
the factor `-1` (`E_printed_unsound`).
-/
import QCert.Minimality.QutritClifford.Semantics

namespace QCert.Minimality.QutritClifford

open Circuit

private theorem go {n : ℕ} {w v : Circuit Gate n}
    (h : (rowsRep 3 n).ops.smul (ZZeta.sqrt3 ^ (scaled.ex v - scaled.ex w)) (evalRows ops n w) =
      (rowsRep 3 n).ops.smul (ZZeta.sqrt3 ^ (scaled.ex w - scaled.ex v)) (evalRows ops n v)) :
    sem.sem n w = sem.sem n v :=
  Qutrit.sem_eq_of_rows sem scaled sem_toOps h

/-- Every rule of Figure 4 (with (E) corrected) is sound. -/
theorem sound_ax : ∀ a : Ax, sem.sem a.arity a.sides.1 = sem.sem a.arity a.sides.2
  | .ω12 => go (by decide +kernel)
  | .H4 => go (by decide +kernel)
  | .S3 => go (by decide +kernel)
  | .E => go (by decide +kernel)
  | .SS' => go (by decide +kernel)
  | .CPh => go (by decide +kernel)
  | .KC => go (by decide +kernel)
  | .CZ => go (by decide +kernel)
  | .B => go (by decide +kernel)
  | .I => go (by decide +kernel)

/-- The laws of the symmetry hold for the swap matrix. -/
theorem sound_sym {k : ℕ} {w v : Circuit Gate k} : Sym Gate.swap k w v → sem.sem k w = sem.sem k v
  | .invol => go (by decide +kernel)
  | .nat1 .H => go (by decide +kernel)
  | .nat1 .S => go (by decide +kernel)
  | .nat2 .CX => go (by decide +kernel)
  | .nat2 .swap => go (by decide +kernel)
  | .nat3 g => nomatch g

/-- Soundness: every equation derivable in Cliff₃ holds in the semantics. -/
theorem sound {n : ℕ} {w v : Circuit Gate n} (h : pres.Proves n w v) : sem.sem n w = sem.sem n v := by
  refine derivable_sound (fun w v r => ?_) h
  refine sem.lift_sound (sem.padded_sound ?_) _ w v r
  intro k w v b
  cases b with
  | sym s => exact sound_sym s
  | ax a _ => exact sound_ax a

/-- (E) as printed in Figure 4, with `ω₁₂⁷`, does not hold: its left-hand
side is `ω₁₂⁶ = -1` times its right-hand side. -/
theorem E_printed_unsound : sem.sem 1 (seq [S, H, S]) ≠ sem.sem 1 E_printed_rhs := by
  intro h
  have h6 : sem.sem 1 (seq [S, H, S]) =
      sem.sem 1 (seq [E_printed_rhs, seq (List.replicate 6 ω)]) := go (by decide +kernel)
  have hs : ∀ k : ℕ, (sem.sem 1 (seq (List.replicate k ω)) : Op ℂ 3 1) = ZZeta.ζ12 ^ k • 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ, seq_cons, map_mul, Submonoid.coe_mul, ih]
      show _ * ((ZZeta.ζ12 : ℂ) • (1 : Op ℂ 3 1)) = _
      rw [smul_mul_smul_comm, one_mul, pow_succ]
  have hpair : (sem.sem 1 (seq [E_printed_rhs, seq (List.replicate 6 ω)]) : Op ℂ 3 1) =
      ZZeta.ζ12 ^ 6 • (sem.sem 1 E_printed_rhs : Op ℂ 3 1) := by
    rw [seq_cons, seq_cons, seq_nil, one_mul, map_mul, Submonoid.coe_mul, hs, smul_mul_assoc,
      one_mul]
  have hz : ZZeta.ζ12 ^ 6 = -1 := by
    have h4 := ZZeta.ζ12_pow_four
    simp only [Int.cast_one, Int.cast_neg, one_mul] at h4
    linear_combination (ZZeta.ζ12 ^ 2 + 1) * h4
  have h6' := congrArg Subtype.val h6
  rw [hpair, h, hz, neg_one_smul] at h6'
  set U : Op ℂ 3 1 := (sem.sem 1 E_printed_rhs : Op ℂ 3 1) with hU_def
  have h2 : (2 : ℂ) • U = 0 := by
    rw [two_smul]; nth_rw 2 [h6']; exact add_neg_cancel U
  have h0 : U = 0 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hU := (sem.sem 1 E_printed_rhs).2
  rw [Matrix.mem_unitaryGroup_iff, ← hU_def, h0, zero_mul] at hU
  exact zero_ne_one hU

end QCert.Minimality.QutritClifford
