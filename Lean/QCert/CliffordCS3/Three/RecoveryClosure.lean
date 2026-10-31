/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Recovery through short preimages

Once the coset relations hold, recovery is closed under multiplication and
the defining circuit equations. Small preimages in the ambient presentation
therefore suffice; the large canonical translations need not be replayed.
-/
import QCert.CliffordCS3.Three.BasicCases
import QCert.BianSelingerUn.Theorem
import QCert.CliffordCS3.Soundness

namespace QCert.CliffordCS3.Three.RecoveryClosure

open Matrix Macro

abbrev act := encodedAction h
abbrev fw : Word Gen →* Word (BianSelingerUn.Gen 8) := FreeMonoid.lift fG

def HypB : Prop := ∀ (c : Bool) (w v : Word (BianSelingerUn.Gen 8)),
  BianSelingerUn.Rel 8 w v →
    (hstar act c w).2 = (hstar act c v).2 ∧
      Derivable Rel (hstar act c w).1 (hstar act c v).1

def Recovered (w : Word Gen) : Prop :=
  (hstar act false (fw w)).2 = false ∧
    Derivable Rel (hstar act false (fw w)).1 w

theorem recovered_one : Recovered 1 := ⟨rfl, Derivable.refl _⟩

theorem recovered_mul {w v : Word Gen} (hw : Recovered w) (hv : Recovered v) :
    Recovered (w * v) := by
  unfold Recovered at *
  rw [map_mul, hstar_mul, hw.1]
  exact ⟨hv.1, hw.2.mul hv.2⟩

theorem recovered_pow {w : Word Gen} (hw : Recovered w) (n : ℕ) : Recovered (w ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using recovered_one
  | succ n ih => simpa only [pow_succ] using recovered_mul ih hw

def checkPreimage (w : Word Gen) (b : Word (BianSelingerUn.Gen 8)) : Bool :=
  (List.finRange 8).all fun j =>
    V8.eqv (V8.brun b.toList (V8.basis j)) (V8.run w.toList (V8.basis j))

theorem preimage_sem {w : Word Gen} {b : Word (BianSelingerUn.Gen 8)}
    (hc : checkPreimage w b = true) :
    FreeMonoid.lift (BianSelingerUn.sem 8) b = FreeMonoid.lift semU w := by
  have hm : FreeMonoid.lift gmatQ b = FreeMonoid.lift matQ w := by
    simp only [checkPreimage, List.all_eq_true, List.mem_finRange, true_implies] at hc
    refine Matrix.ext fun a j => ?_
    have e1 := V8.toVec_brun b.toList (V8.basis j)
    have e2 := V8.toVec_run w.toList (V8.basis j)
    rw [V8.toVec_basis] at e1 e2
    have he : FreeMonoid.lift gmatQ b *ᵥ Pi.single j 1 =
        FreeMonoid.lift matQ w *ᵥ Pi.single j 1 := by
      rw [FreeMonoid.lift_apply, FreeMonoid.lift_apply, ← e1,
        V8.toVec_eq_of_eqv (hc j), e2]
    have := congrFun he a
    simpa only [mulVec_single_one] using this
  rw [← lift_lift_f]
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_lift_sem, coe_lift_sem, hm]
  congr 1
  clear hc hm b
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih =>
    rw [map_mul, map_mul, map_mul, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of, gmatQ_fG, ih]

theorem recovered_of_preimage (hb : HypB) (w : Word Gen)
    (b : Word (BianSelingerUn.Gen 8)) (hc : checkPreimage w b = true)
    (hs : (hstar act false b).2 = false)
    (hr : Derivable Rel (hstar act false b).1 w) : Recovered w := by
  have he : FreeMonoid.lift (BianSelingerUn.sem 8) (fw w) =
      FreeMonoid.lift (BianSelingerUn.sem 8) b := by
    rw [lift_lift_f, preimage_sem hc]
  have hp := rs_claimB act hb ((BianSelingerUn.presentation 8).complete he) false
  exact ⟨hp.1.trans hs, hp.2.trans hr⟩

theorem recovered_congr (hb : HypB) {w v : Word Gen}
    (hw : Recovered w) (hwv : Derivable Rel w v) : Recovered v := by
  have he : FreeMonoid.lift (BianSelingerUn.sem 8) (fw v) =
      FreeMonoid.lift (BianSelingerUn.sem 8) (fw w) := by
    rw [lift_lift_f, lift_lift_f]
    have hh := derivable_sound sound hwv
    apply Subtype.ext
    -- The subgroup semantics has the same underlying unitary matrices.
    have coe (z : Word Gen) :
        ((FreeMonoid.lift semU z : U_ZHalfI 8) : unitaryGroup (Fin 8) ℂ) =
          FreeMonoid.lift sem z := by
      induction z using FreeMonoid.inductionOn' with
      | one => rfl
      | mul_of x z ih =>
        rw [map_mul, map_mul, Subgroup.coe_mul, FreeMonoid.lift_eval_of,
          FreeMonoid.lift_eval_of, ih]
        rfl
    rw [coe, coe, hh]
  have hp := rs_claimB act hb ((BianSelingerUn.presentation 8).complete he) false
  exact ⟨hp.1.trans hw.1, (hp.2.trans hw.2).trans hwv⟩

def tokenPreimage : Fin 7 → Word (BianSelingerUn.Gen 8)
  | 0 => BianSelingerUn.X 1 5 (by decide)
  | 1 => BianSelingerUn.X 0 1 (by decide)
  | 2 => BianSelingerUn.X 0 4 (by decide)
  | 3 => BianSelingerUn.X 4 6 (by decide)
  | 4 => BianSelingerUn.X 2 6 (by decide)
  | 5 => BianSelingerUn.X 2 3 (by decide)
  | 6 => BianSelingerUn.X 3 7 (by decide)

theorem recovered_token (hb : HypB) (d : Fin 7) : Recovered (Cert.token d) := by
  apply recovered_of_preimage hb _ (tokenPreimage d)
  · revert d; decide +kernel
  · fin_cases d <;> rfl
  · fin_cases d <;> exact Derivable.refl _

theorem recovered_sign (hb : HypB) : Recovered Cert.ccZ := by
  apply recovered_of_preimage hb _ (bi 7 * bi 7)
  · decide +kernel
  · rfl
  · exact Derivable.refl _

theorem recovered_atom (hb : HypB) : Recovered Cert.atom := by
  apply recovered_of_preimage hb _ (bK 3 7 * bi 7 ^ 3)
  · decide +kernel
  · rfl
  · change Derivable Rel (Cert.atom * Cert.ccZ * Cert.ccZ) Cert.atom
    simpa only [mul_assoc, mul_one] using Monomial.ccZ_square.mul_left Cert.atom

theorem recovered_phase (hb : HypB) : Recovered phase := by
  apply recovered_of_preimage hb _ (bi 3 * bi 7)
  · decide +kernel
  · rfl
  · exact phase_recovered

end QCert.CliffordCS3.Three.RecoveryClosure
