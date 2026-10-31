/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The order-eight macro axiom

The coset action alternates A and A²P. The controlled-commutator cube
A³ = P² and P⁴ = 1 therefore establish the K⁸ relation.
-/
import QCert.CliffordCS3.Three.Conjugation
import QCert.CliffordCS3.Three.Checks

set_option maxRecDepth 10000

namespace QCert.CliffordCS3.Three

open Macro Swap01

theorem atom_phase_commute_of
    (hc : Derivable Rel (W.CS12 * (Swap01.word * W.CS12 * Swap01.word))
      ((Swap01.word * W.CS12 * Swap01.word) * W.CS12)) :
    Commute (q phase) (q Cert.atom) := by
  have hk : Commute (q phase) (q (W.K 0)) := by
    exact q_of (Derivable.of (Rel.comm_0_12 Local.K)).symm
  have hd : Commute (q phase) (q W.CS01) := by
    exact q_of (Derivable.of Rel.c12)
  have hi : Commute (q phase) (q W.I) := by
    exact q_of (Derivable.of (Rel.comm_i .CS₁₂ (by decide))).symm
  have hc' : Commute (q phase) (swap (q W.CS12)) := by
    simpa only [swap, MonoidHom.coe_mk, OneHom.coe_mk, ← map_mul] using q_of hc
  rw [← swap_atom]
  simp only [middleAtom, map_mul, map_pow, swap_K, swap_I, swap_CS]
  exact ((((((hk.mul_right hd).mul_right (hi.mul_right hk)).mul_right
    (hc'.pow_right 3)).mul_right hk).mul_right (hd.pow_right 3)).mul_right
    (hi.mul_right hk)).mul_right hc'

theorem phase_fourth : q phase ^ 4 = 1 := by
  simpa only [map_pow, map_one] using q_of (Derivable.of (Rel.c5 1))

theorem phase_twelfth : (q phase ^ 3) ^ 4 = 1 := by
  rw [← pow_mul, show 3 * 4 = 4 * 3 by decide, pow_mul, phase_fourth, one_pow]

theorem atom_phase_block : q (Cert.atom * (Cert.atom ^ 2 * phase)) = q phase ^ 3 := by
  have hc : q Cert.atom ^ 3 = q phase ^ 2 := by
    simpa only [map_pow] using q_of atom_cube
  simp only [map_mul, map_pow]
  rw [← mul_assoc, ← pow_succ', hc, ← pow_succ]

theorem K_eight_false :
    Derivable Rel (hstar h false (FreeMonoid.of Macro.ML.K ^ 8)).1 1 := by
  have hword : (hstar h false (FreeMonoid.of Macro.ML.K ^ 8)).1 =
      (Cert.atom * (Cert.atom ^ 2 * phase)) ^ 4 := rfl
  rw [hword]
  apply of_q
  rw [map_pow, atom_phase_block, phase_twelfth, map_one]

theorem K_eight_true_of (hp : Commute (q phase) (q Cert.atom)) :
    Derivable Rel (hstar h true (FreeMonoid.of Macro.ML.K ^ 8)).1 1 := by
  have hword : (hstar h true (FreeMonoid.of Macro.ML.K ^ 8)).1 =
      (Cert.atom ^ 2 * phase * Cert.atom) ^ 4 := rfl
  rw [hword]
  apply of_q
  have hb : q (Cert.atom ^ 2 * phase * Cert.atom) = q phase ^ 3 := by
    simp only [map_mul, map_pow, mul_assoc]
    rw [hp.eq, ← mul_assoc, ← pow_succ]
    have hc : q Cert.atom ^ 3 = q phase ^ 2 := by
      simpa only [map_pow] using q_of atom_cube
    rw [hc, ← pow_succ]
  rw [map_pow, hb, phase_twelfth, map_one]

end QCert.CliffordCS3.Three
