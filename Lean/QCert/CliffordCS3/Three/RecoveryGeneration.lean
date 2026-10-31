/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Generating the circuit gates from the recovered atoms
-/
import QCert.CliffordCS3.Three.RecoveryClosure
import QCert.CliffordCS3.Three.RecoveryWords
import QCert.CliffordCS3.Three.Cert.AtomRecovery
import QCert.CliffordCS3.Three.PermutationTransport

set_option maxRecDepth 10000

namespace QCert.CliffordCS3.Three.RecoveryGeneration

open QuotientGroup RecoveryWords RecoveryClosure

def core : Word Gen :=
  commW (W.K 1 * W.CS01 * invW (W.K 1)) (invW W.CS12)

def whiteCore : Word Gen :=
  commW (W.K 1 * (invW W.CS01 * W.S 1) * invW (W.K 1)) (invW W.CS12)

def single : Word Gen :=
  commW (W.K 1 * W.S 1 * invW (W.K 1)) (invW W.CS12)

theorem u_core : u core = u Swap01.middleAtom := by
  have hi : u W.I = (u (W.K 1))⁻¹ * (u (W.K 1))⁻¹ := by
    have he := LocalKZ.K_inv 1
    rw [map_mul] at he
    calc
      u W.I = (u W.I * u (W.K 1)) * (u (W.K 1))⁻¹ := by group
      _ = _ := by rw [he]
  simp only [core, u_commW, map_mul, u_invW, Swap01.middleAtom, map_pow,
    Monomial.cube_eq_inv Monomial.b_fourth,
    Monomial.cube_eq_inv Monomial.d_fourth, hi, Monomial.bQ, Monomial.dQ]
  group

theorem flip_K : PermutationBase.conj (u (W.X 0)) (u (W.K 1)) = u (W.K 1) := by
  rw [PermutationBase.conj_def, Monomial.inv_of_square Monomial.flip0_square]
  exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Xu * Two.W2.Kl * Two.W2.Xu) (v := Two.W2.Kl) (by decide +kernel)))

theorem flip_CS : PermutationBase.conj (u (W.X 0)) (u W.CS01) =
    (u W.CS01)⁻¹ * u (W.S 1) := by
  rw [PermutationBase.conj_def, Monomial.inv_of_square Monomial.flip0_square]
  have ht := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Xu * Two.W2.CS * Two.W2.Xu)
    (v := Two.W2.CS ^ 3 * Two.W2.Sl) (by decide +kernel)))
  have he : u (W.X 0) * u W.CS01 * u (W.X 0) = u W.CS01 ^ 3 * u (W.S 1) := ht
  simpa only [Monomial.cube_eq_inv Monomial.d_fourth] using he

theorem flip_phase : PermutationBase.conj (u (W.X 0)) (u W.CS12) = u W.CS12 :=
  Monomial.conj0_b

theorem flip_core : PermutationBase.conj (u (W.X 0)) (u core) = u whiteCore := by
  simp only [core, whiteCore, u_commW, map_mul, u_invW, map_inv,
    flip_K, flip_CS, flip_phase]

theorem remove_control : Derivable Rel
    (Swap01.middleAtom * (W.X 0 * Swap01.middleAtom * W.X 0)) single := by
  apply to_derivable
  have ht : u (core * whiteCore) = u single :=
    of_derivable Cert.AtomRecovery.remove_controlRule.sound
  rw [map_mul, ← flip_core, u_core] at ht
  rw [PermutationBase.conj_def, Monomial.inv_of_square Monomial.flip0_square] at ht
  simpa only [map_mul] using ht

private def single2 : Word Two.Gen2 := FreeMonoid.ofList
  [.Ku, .Su, .i, .Ku, .CS, .CS, .CS, .i, .Ku, .i, .i, .i,
   .Su, .Su, .Su, .i, .Ku, .CS, .CS, .CS, .CS, .CS, .CS, .CS, .CS, .CS]

theorem remove_second_control : Derivable Rel
    (single * (W.X 2 * single * W.X 2)) (W.K 1 * W.S 1 ^ 3) := by
  have ht := Two.derivable_embed 1 (Two.derivable_of_check2
    (w := single2 * (Two.W2.Xl * single2 * Two.W2.Xl))
    (v := Two.W2.Ku * Two.W2.Su ^ 3) (by decide +kernel))
  convert ht using 1 <;> decide +kernel

theorem recover_middleAtom (hb : HypB) (hs : Recovered Swap01.word) :
    Recovered Swap01.middleAtom := by
  apply recovered_congr hb
    (recovered_mul (recovered_mul hs (recovered_atom hb)) hs)
  apply to_derivable
  have he := LocalKZ.sw_A
  change u Swap01.word * u Swap01.middleAtom * u Swap01.word = u Cert.atom at he
  have hi : u Swap01.word * u Swap01.word = 1 := by
    simpa only [map_mul, map_one] using of_derivable Swap01.sq
  have hh (z : G) : u Swap01.word * (u Swap01.word * z) = z := by
    rw [← mul_assoc, hi, one_mul]
  simp only [map_mul]
  rw [← he]
  simp only [mul_assoc, hh, hi, mul_one]

theorem recover_K1 (hb : HypB) (ha : Recovered Swap01.middleAtom)
    (hx0 : Recovered (W.X 0)) (hx2 : Recovered (W.X 2))
    (hs : Recovered (W.S 1)) : Recovered (W.K 1) := by
  have hsingle := recovered_congr hb
    (recovered_mul ha (recovered_mul (recovered_mul hx0 ha) hx0)) remove_control
  have hks := recovered_congr hb
    (recovered_mul hsingle (recovered_mul (recovered_mul hx2 hsingle) hx2))
    remove_second_control
  apply recovered_congr hb (recovered_mul hks hs)
  exact Two.derivable_embed 1 (Two.derivable_of_check2
    (w := Two.W2.Ku * Two.W2.Su ^ 3 * Two.W2.Su) (v := Two.W2.Ku)
    (by decide +kernel))

private def sw2 : Word Two.Gen2 :=
  (Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I) *
  (Two.W2.Ku * Two.W2.CS ^ 2 * Two.W2.Ku * Two.W2.I) *
  (Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I)

theorem recover_S1 (hb : HypB) (hx : Recovered (W.X 2)) : Recovered (W.S 1) := by
  have hp := recovered_phase hb
  apply recovered_congr hb (recovered_mul hp (recovered_mul (recovered_mul hx hp) hx))
  exact Two.derivable_embed 1 (Two.derivable_of_check2
    (w := Two.W2.CS * (Two.W2.Xl * Two.W2.CS * Two.W2.Xl))
    (v := Two.W2.Su) (by decide +kernel))

theorem recover_S2 (hb : HypB) (hx : Recovered (W.X 1)) : Recovered (W.S 2) := by
  have hp := recovered_phase hb
  apply recovered_congr hb (recovered_mul hp (recovered_mul (recovered_mul hx hp) hx))
  exact Two.derivable_embed 1 (Two.derivable_of_check2
    (w := Two.W2.CS * (Two.W2.Xu * Two.W2.CS * Two.W2.Xu))
    (v := Two.W2.Sl) (by decide +kernel))

theorem recover_S0 (hb : HypB) (hs : Recovered Swap01.word)
    (h1 : Recovered (W.S 1)) : Recovered (W.S 0) := by
  apply recovered_congr hb (recovered_mul (recovered_mul hs h1) hs)
  exact Two.derivable_embed 0 (Two.derivable_of_check2
    (w := sw2 * Two.W2.Sl * sw2) (v := Two.W2.Su) (by decide +kernel))

theorem recover_I (hb : HypB) (hs : Recovered (W.S 1))
    (hx : Recovered (W.X 1)) : Recovered W.I := by
  apply recovered_congr hb (recovered_mul hs (recovered_mul (recovered_mul hx hs) hx))
  exact Two.derivable_embed 1 (Two.derivable_of_check2
    (w := Two.W2.Su * (Two.W2.Xu * Two.W2.Su * Two.W2.Xu))
    (v := Two.W2.I) (by decide +kernel))

theorem recover_CS01 (hb : HypB) (hs01 : Recovered Swap01.word)
    (hs12 : Recovered PermutationBase.swap12) : Recovered W.CS01 := by
  have hc := recovered_mul (recovered_mul hs01 (recovered_phase hb)) hs01
  apply recovered_congr hb (recovered_mul (recovered_mul hs12 hc) hs12)
  apply to_derivable
  have ht := PermutationBase.conj12_d
  rw [PermutationBase.conj12_def] at ht
  have hs : PermutationBase.ss12 * PermutationBase.ss12 = 1 := by
    simpa only [map_mul, map_one] using of_derivable PermutationBase.swap12_square
  have hh (z : G) : PermutationBase.ss12 * (PermutationBase.ss12 * z) = z := by
    rw [← mul_assoc, hs, one_mul]
  change PermutationBase.ss12 * Monomial.cQ * PermutationBase.ss12 = Monomial.dQ
  rw [← ht]
  simp only [mul_assoc, hh, hs, mul_one]

theorem recover_K0 (hb : HypB) (hs : Recovered Swap01.word)
    (h1 : Recovered (W.K 1)) : Recovered (W.K 0) :=
  recovered_congr hb (recovered_mul (recovered_mul hs h1) hs) Swap01.conjugate_K

theorem recover_K2 (hb : HypB) (hs : Recovered PermutationBase.swap12)
    (h1 : Recovered (W.K 1)) : Recovered (W.K 2) := by
  apply recovered_congr hb (recovered_mul (recovered_mul hs h1) hs)
  exact Two.derivable_embed 1 (Two.derivable_of_check2
    (w := sw2 * Two.W2.Ku * sw2) (v := Two.W2.Kl) (by decide +kernel))

theorem recover_generators (hb : HypB)
    (hx : ∀ j : Fin 3, Recovered (W.X j))
    (hs01 : Recovered Swap01.word) (hs12 : Recovered PermutationBase.swap12) :
    ∀ x : Gen, Recovered (FreeMonoid.of x) := by
  have hS1 := recover_S1 hb (hx 2)
  have hK1 := recover_K1 hb (recover_middleAtom hb hs01) (hx 0) (hx 2) hS1
  intro x
  cases x
  · exact recover_I hb hS1 (hx 1)
  · exact recover_K0 hb hs01 hK1
  · exact hK1
  · exact recover_K2 hb hs12 hK1
  · exact recover_S0 hb hs01 hS1
  · exact hS1
  · exact recover_S2 hb (hx 1)
  · exact recover_CS01 hb hs01 hs12
  · exact recovered_phase hb

end QCert.CliffordCS3.Three.RecoveryGeneration
