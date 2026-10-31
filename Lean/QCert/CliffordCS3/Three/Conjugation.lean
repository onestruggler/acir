/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Transport between the outer and middle target wires

Conjugation by the swap of wires 0 and 1 is a monoid homomorphism on the
presented quotient. The required local swap equations follow from the
completed two-qubit theory.
-/
import QCert.CliffordCS3.Rewrite
import QCert.CliffordCS3.Three.Cert.Words
import QCert.CliffordCS3.Three.Cert.AtomCube

namespace QCert.CliffordCS3.Three.Swap01

open Two

def pair : Word Gen2 := FreeMonoid.ofList
  [.Kl, .CS, .CS, .Kl, .i, .Ku, .CS, .CS, .Ku, .i, .Kl, .CS, .CS, .Kl, .i]

def word : Word Gen := embW 0 pair

theorem sq : Derivable Rel (word * word) 1 := by
  have ht := derivable_embed 0 (derivable_of_check2
    (w := pair * pair) (v := 1) (by decide +kernel))
  simpa only [map_mul, map_one, word] using ht

theorem conjugate_K : Derivable Rel (word * W.K 1 * word) (W.K 0) := by
  exact derivable_embed 0 (derivable_of_check2
    (w := pair * FreeMonoid.of .Kl * pair) (v := FreeMonoid.of .Ku)
    (by decide +kernel))

theorem conjugate_I : Derivable Rel (word * W.I * word) W.I := by
  exact derivable_embed 0 (derivable_of_check2
    (w := pair * FreeMonoid.of .i * pair) (v := FreeMonoid.of .i)
    (by decide +kernel))

theorem conjugate_CS : Derivable Rel (word * W.CS01 * word) W.CS01 := by
  exact derivable_embed 0 (derivable_of_check2
    (w := pair * FreeMonoid.of .CS * pair) (v := FreeMonoid.of .CS)
    (by decide +kernel))

abbrev Quot := (conGen Rel).Quotient

def q : Word Gen →* Quot := (conGen Rel).mk'

theorem q_of {u v : Word Gen} (h : Derivable Rel u v) : q u = q v :=
  (Con.eq _).2 h

theorem of_q {u v : Word Gen} (h : q u = q v) : Derivable Rel u v :=
  (Con.eq _).1 h

theorem qsq : q word * q word = 1 := by
  simpa only [map_mul, map_one] using q_of sq

/-- Conjugation by the involutive swap. -/
def swap : Quot →* Quot where
  toFun x := q word * x * q word
  map_one' := by simp only [mul_one, qsq]
  map_mul' x y := by
    simp only [mul_assoc]
    rw [show q word * (q word * (y * q word)) = y * q word by
      rw [← mul_assoc, qsq, one_mul]]

theorem swap_K : swap (q (W.K 1)) = q (W.K 0) := by
  simpa only [swap, MonoidHom.coe_mk, OneHom.coe_mk, ← map_mul] using q_of conjugate_K

theorem swap_I : swap (q W.I) = q W.I := by
  simpa only [swap, MonoidHom.coe_mk, OneHom.coe_mk, ← map_mul] using q_of conjugate_I

theorem swap_CS : swap (q W.CS01) = q W.CS01 := by
  simpa only [swap, MonoidHom.coe_mk, OneHom.coe_mk, ← map_mul] using q_of conjugate_CS

def middleAtom : Word Gen :=
  W.K 1 * W.CS01 * (W.I * W.K 1) * W.CS12 ^ 3 *
    W.K 1 * W.CS01 ^ 3 * (W.I * W.K 1) * W.CS12

theorem swap_atom : swap (q middleAtom) = q Cert.atom := by
  simp only [middleAtom, map_mul, map_pow, swap_K, swap_I, swap_CS]
  change q (W.K 0) * q W.CS01 * (q W.I * q (W.K 0)) *
    (q word * q W.CS12 * q word) ^ 3 * q (W.K 0) * q W.CS01 ^ 3 *
      (q W.I * q (W.K 0)) * (q word * q W.CS12 * q word) = q Cert.atom
  rw [← show swap (q W.CS12) = q word * q W.CS12 * q word from rfl,
    ← map_pow]
  change q (W.K 0) * q W.CS01 * (q W.I * q (W.K 0)) *
    (q word * (q W.CS12) ^ 3 * q word) * q (W.K 0) * q W.CS01 ^ 3 *
      (q W.I * q (W.K 0)) * (q word * q W.CS12 * q word) = q Cert.atom
  simp only [← map_mul, ← map_pow]
  rfl

theorem CX10_square : q (W.CX10 * W.CX10) = 1 := by
  have ht := derivable_embed 0 (derivable_of_check2
    (w := (W2.Ku * W2.CS ^ 2 * W2.Ku * W2.I) ^ 2) (v := 1)
    (by decide +kernel))
  exact q_of ht

theorem CX01_square : q (W.CX01 * W.CX01) = 1 := by
  have ht := derivable_embed 0 (derivable_of_check2
    (w := (W2.Kl * W2.CS ^ 2 * W2.Kl * W2.I) ^ 2) (v := 1)
    (by decide +kernel))
  exact q_of ht

theorem swap_braid : q word = q (W.CX10 * W.CX01 * W.CX10) := by
  have ht := derivable_embed 0 (derivable_of_check2
    (w := pair)
    (v := (W2.Ku * W2.CS ^ 2 * W2.Ku * W2.I) *
      (W2.Kl * W2.CS ^ 2 * W2.Kl * W2.I) * (W2.Ku * W2.CS ^ 2 * W2.Ku * W2.I))
    (by decide +kernel))
  apply q_of
  simpa [word, W.CX10, W.CX01, W.CX, pow_two, embW, emb, pair] using ht

theorem commute_phase_CX10 : Commute (q W.CS12) (q W.CX10) := by
  have hk : Commute (q W.CS12) (q (W.K 0)) := by
    simpa only [Commute, SemiconjBy, ← map_mul] using
      q_of (Derivable.of (Rel.comm_0_12 Local.K)).symm
  have hs : Commute (q W.CS12) (q W.CS01) := by
    simpa only [Commute, SemiconjBy, ← map_mul] using q_of (Derivable.of Rel.c12)
  have hi : Commute (q W.CS12) (q W.I) := by
    simpa only [Commute, SemiconjBy, ← map_mul] using
      q_of (Derivable.of (Rel.comm_i .CS₁₂ (by decide))).symm
  simpa only [W.CX10, W.CX, map_mul] using
    (((hk.mul_right hs).mul_right hs).mul_right hk).mul_right hi

theorem swap_phaseSquare : swap (q Cert.AtomCube.phaseSquare) = q (W.CS12 ^ 2) := by
  -- Keep the relation in its original orientation before conjugating.
  have h15' : q (W.CX10 * W.CX01 * W.CS12 ^ 2 * W.CX01 * W.CX10) =
      q Cert.AtomCube.phaseSquare := q_of (Derivable.of Rel.c15)
  rw [← h15']
  change q word * q (W.CX10 * W.CX01 * W.CS12 ^ 2 * W.CX01 * W.CX10) * q word = _
  rw [swap_braid]
  have hx : q W.CX10 * q W.CX10 = 1 := by simpa only [map_mul] using CX10_square
  have ha : q W.CX01 * q W.CX01 = 1 := by simpa only [map_mul] using CX01_square
  have hc := commute_phase_CX10.pow_left 2
  simp only [map_mul, map_pow, mul_assoc]
  simp only [← mul_assoc, hx, ha, one_mul]
  rw [hc.symm.eq, mul_assoc, hx, mul_one]

theorem atom_cube : Derivable Rel (Cert.atom ^ 3) (W.CS12 ^ 2) := by
  apply of_q
  have hc := congrArg swap (q_of Cert.AtomCube.cube)
  have hword : Cert.AtomCube.word = middleAtom := rfl
  rw [hword, map_pow, map_pow, swap_atom, swap_phaseSquare] at hc
  simpa only [map_pow] using hc

end QCert.CliffordCS3.Three.Swap01
