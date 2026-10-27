/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness of `LinPhase_d`

Theorem 2 of Blake (arXiv:2603.06466) for the linear phases (level `1`),
following its proof (Lemmas 10–15, Proposition 1): every circuit is an
affine circuit after a diagonal normal form `ω^k Z^{a_0} ⋯ Z^{a_{n-1}}`
(Definition 24; `zcol`), a diagonal normal form moving through an affine
gate by the transport rules (21), (22), (23) (Lemma 12); the affine part is
fixed by the relabelling (Theorem 1) and the coefficients by the phase
function (Lemma 7).

The one transport case that is not a rule, `Z` on the control of `CX`, is
derived by conjugating (21) with `M_{-1}` on the control.
-/
import QCert.PhaseAffine.AffineComplete

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

/-! ### Relations of the linear phase -/

section Rel

variable [Fact d.Prime] (h : 1 ≤ lv) (m : ℕ)

omit [Fact d.Prime] in
/-- (19) on the bottom wires: `ω^d = 1`. -/
theorem relωd {n : ℕ} : mk (g0 (n := n) (Gate.omega (d := d) h)) ^ d = 1 := by
  have e := mk_rule (d := d) (lv := lv) n (Rules.r19 h)
  simp only [map_pow, pad_g0, map_one] at e
  exact e

omit [Fact d.Prime] in
/-- (20): `Z^d = 1`. -/
theorem relZd : mk (g1 (n := m) (Gate.Z (d := d) h)) ^ d = 1 := by
  simpa [pad_g1] using mk_rule (d := d) (lv := lv) m (Rules.r20 h)

omit [Fact d.Prime] in
/-- (23): `X`, `Z` is `Z`, `X`, `ω`. -/
theorem relZX : mk (g1 (n := m) (Gate.Z (d := d) h)) * mk (g1 Gate.X) =
    mk (g0 (Gate.omega h)) * mk (g1 Gate.X) * mk (g1 (Gate.Z h)) := by
  simpa [pad_g1, pad_g0, mul_assoc] using mk_rule (d := d) (lv := lv) m (Rules.r23 h)

/-- (22): `M_x`, `Z` is `Z^x`, `M_x`. -/
theorem relZM (x : (ZMod d)ˣ) : mk (g1 (n := m) (Gate.Z (d := d) h)) * mk (g1 (Gate.M x)) =
    mk (g1 (Gate.M x)) * mk (g1 (Gate.Z h)) ^ (x : ZMod d).val := by
  simpa [pad_g1, fpow] using mk_rule (d := d) (lv := lv) m (Rules.r22 h x)

omit [Fact d.Prime] in
/-- (21): `Z` on both wires, then `CX`, is `CX`, then `Z` on the target. -/
theorem rel21Z : mk (g2 (n := m) (Gate.CX (d := d) (lv := lv))) * mk (g1 (Gate.Z h)) *
    mk (shift (g1 (Gate.Z h))) = mk (g1 (Gate.Z h)) * mk (g2 Gate.CX) := by
  simpa [pad_g1, pad_g2, pad_shift, mul_assoc] using mk_rule (d := d) (lv := lv) m (Rules.r21 h)

theorem relZ_neg_one : mk (g1 (n := m) (Gate.Z (d := d) h)) ^ (-1 : ZMod d).val =
    (mk (g1 (Gate.Z h)))⁻¹ := pow_val_neg_one (relZd h m) one_lt_d

/-- `Z` on the control commutes with `CX`: conjugate (21) by `M_{-1}` on the
control. -/
theorem relZ1CX : mk (shift (g1 (n := m) (Gate.Z (d := d) h))) * mk (g2 Gate.CX) =
    mk (g2 Gate.CX) * mk (shift (g1 (Gate.Z h))) := by
  set c := mk (g2 (n := m) (Gate.CX (d := d) (lv := lv)))
  set z0 := mk (g1 (n := m + 1) (Gate.Z (d := d) h))
  set z1 := mk (shift (g1 (n := m) (Gate.Z (d := d) h)))
  set mt := mk (shift (g1 (n := m) (Gate.M (d := d) (lv := lv) (-1))))
  have hstar : c * z0 * z1 = z0 * c := rel21Z h m
  have hmm : mt * mt = 1 := relM1_top_sq m
  have hmi : mt⁻¹ = mt := inv_eq_of_mul_eq_one_left hmm
  have hc : mt * c * mt = c⁻¹ := relM1CX m
  have h01 : z0 * z1 = z1 * z0 := (mk_comm1' (Gate.Z h) (g1 (Gate.Z h))).eq
  have hb : mt * z0 = z0 * mt := (mk_comm1' (Gate.Z h) (g1 (Gate.M (-1)))).eq.symm
  have hz : mt * z1 * mt = z1⁻¹ := by
    have h1 : mk (g1 (n := m) (Gate.M (d := d) (lv := lv) (-1))) * mk (g1 (Gate.Z h)) *
        mk (g1 (Gate.M (-1))) * mk (g1 (Gate.Z h)) = 1 := by
      have e := relZM (d := d) h m (-1)
      rw [Units.val_neg, Units.val_one, relZ_neg_one h m] at e
      calc _ = mk (g1 (n := m) (Gate.M (d := d) (lv := lv) (-1))) *
            (mk (g1 (Gate.Z h)) * mk (g1 (Gate.M (-1)))) * mk (g1 (Gate.Z h)) := by group
        _ = mk (g1 (n := m) (Gate.M (d := d) (lv := lv) (-1))) *
            (mk (g1 (Gate.M (-1))) * (mk (g1 (Gate.Z h)))⁻¹) * mk (g1 (Gate.Z h)) := by rw [e]
        _ = (mk (g1 (n := m) (Gate.M (d := d) (lv := lv) (-1))) * mk (g1 (Gate.M (-1)))) *
            ((mk (g1 (Gate.Z h)))⁻¹ * mk (g1 (Gate.Z h))) := by group
        _ = 1 := by rw [relM1_sq, inv_mul_cancel, one_mul]
    have := mk_shift_one (w := g1 (n := m) (Gate.M (d := d) (lv := lv) (-1)) * g1 (Gate.Z h) *
      g1 (Gate.M (-1)) * g1 (Gate.Z h)) (by simp only [map_mul]; exact h1)
    simp only [map_mul] at this
    exact eq_inv_of_mul_eq_one_left this
  have hz0 : mt * z0 * mt = z0 := by rw [hb, mul_assoc, hmm, mul_one]
  -- conjugate `hstar` by `mt`
  have hs : c⁻¹ * z0 * z1⁻¹ = z0 * c⁻¹ := by
    have := congrArg (MulAut.conj mt) hstar
    simp only [map_mul, MulAut.conj_apply, hmi] at this
    rw [hc, hz, hz0] at this
    exact this
  -- combine
  have e1 : c * z0⁻¹ = z0⁻¹ * c * z1 := by
    calc c * z0⁻¹ = z0⁻¹ * (z0 * c) * z0⁻¹ := by group
      _ = z0⁻¹ * (c * z0 * z1) * z0⁻¹ := by rw [hstar]
      _ = z0⁻¹ * c * (z0 * z1) * z0⁻¹ := by group
      _ = z0⁻¹ * c * (z1 * z0) * z0⁻¹ := by rw [h01]
      _ = _ := by group
  have e2 : c * z0⁻¹ = z1 * z0⁻¹ * c := by
    have := congrArg (·⁻¹) hs
    simp only [mul_inv_rev, inv_inv] at this
    rw [← this]; group
  have e3 : z0⁻¹ * (z1 * c) = z0⁻¹ * (c * z1) := by
    calc z0⁻¹ * (z1 * c) = z1 * z0⁻¹ * c := by
          rw [← mul_assoc, (Commute.inv_left (show Commute z0 z1 from h01)).eq]
      _ = z0⁻¹ * c * z1 := by rw [← e2, e1]
      _ = _ := by group
  exact mul_left_cancel e3

end Rel

/-! ### The diagonal normal form of `LinPhase_d` -/

/-- The `Z`-column: `Z^{a_i}` on every wire `i` (Definitions 21 and 24). -/
def zcol (h : 1 ≤ lv) : (n : ℕ) → Lab d n → C d lv n
  | 0, _ => 1
  | n + 1, a => shift (zcol h n (Fin.tail a)) * g1 (Gate.Z h) ^ᶠ (a 0)

/-- The scalar left by an affine gate moving out of a `Z`-column. -/
def zsc : {n : ℕ} → Gen (Gate d lv) n → Lab d n → ZMod d
  | _, .gate1 .X, e => e 0
  | _, .up g, e => zsc g (Fin.tail e)
  | _, _, _ => 0

/-- The `Z`-column after an affine gate moves out of it (Lemma 12: the
substitution `q ↦ q ∘ g`). -/
def zmap : {n : ℕ} → Gen (Gate d lv) n → Lab d n → Lab d n
  | _, .gate1 (.M a), e => Fin.cons ((a : ZMod d) * e 0) (Fin.tail e)
  | _, .gate2 .CX, e => Fin.cons (e 0) (Fin.cons (e 0 + e 1) (Fin.tail (Fin.tail e)))
  | _, .gate2 .SWAP, e => Fin.cons (e 1) (Fin.cons (e 0) (Fin.tail (Fin.tail e)))
  | _, .up g, e => Fin.cons (e 0) (zmap g (Fin.tail e))
  | _, _, e => e

theorem zcol_zero (h : 1 ≤ lv) (n : ℕ) : zcol (d := d) h n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [zcol, fpow, Pi.zero_apply, ZMod.val_zero, pow_zero, mul_one]
    rw [show (Fin.tail (0 : Lab d (n + 1))) = 0 from rfl, ih, map_one]

theorem mk_zcol_succ (h : 1 ≤ lv) {n : ℕ} (a : Lab d (n + 1)) :
    mk (zcol h (n + 1) a) =
      mk (shift (zcol h n (Fin.tail a))) * mk (g1 (Gate.Z h)) ^ (a 0).val := by
  rw [zcol, map_mul, fpow, map_pow]

theorem mk_zcol_succ_succ (h : 1 ≤ lv) {m : ℕ} (c : Lab d (m + 2)) :
    mk (zcol h (m + 2) c) =
      mk (shift (shift (zcol h m (Fin.tail (Fin.tail c))))) *
        mk (shift (g1 (Gate.Z h))) ^ (c 1).val * mk (g1 (Gate.Z h)) ^ (c 0).val := by
  simp only [zcol, map_mul, fpow, map_pow]
  rfl

section Transport

variable [Fact d.Prime] (h : 1 ≤ lv)

omit [Fact d.Prime] in
theorem mk_omega_central {n : ℕ} (q : Q d lv n) : Commute (mk (g0 (Gate.omega h))) q := by
  obtain ⟨w, rfl⟩ := mk_surjective q
  show mk (g0 (Gate.omega h)) * mk w = mk w * mk (g0 (Gate.omega h))
  rw [← map_mul, ← map_mul]; exact mk_scalar_comm_word _ w

omit [Fact d.Prime] in
theorem relZd_top (m : ℕ) : mk (shift (g1 (n := m) (Gate.Z (d := d) h))) ^ d = 1 := by
  have := mk_shift_one (w := g1 (n := m) (Gate.Z (d := d) h) ^ d) (by rw [map_pow]; exact relZd h m)
  simpa only [map_pow] using this

theorem relZXpow (m : ℕ) (k : ℕ) :
    mk (g1 (n := m) (Gate.Z (d := d) h)) ^ k * mk (g1 Gate.X) =
      mk (g0 (Gate.omega h)) ^ k * mk (g1 Gate.X) * mk (g1 (Gate.Z h)) ^ k := by
  set z := mk (g1 (n := m) (Gate.Z (d := d) h))
  set x := mk (g1 (n := m) (Gate.X (d := d) (lv := lv)))
  set o := mk (g0 (n := m + 1) (Gate.omega (d := d) h))
  have hzx : z * x = o * x * z := relZX h m
  have ho : ∀ q, Commute o q := mk_omega_central h
  induction k with
  | zero => simp
  | succ k ih =>
    calc z ^ (k + 1) * x = z ^ k * (z * x) := by rw [pow_succ, mul_assoc]
      _ = (z ^ k * o) * x * z := by rw [hzx]; group
      _ = o * (z ^ k * x) * z := by rw [← (ho (z ^ k)).eq]; group
      _ = o * (o ^ k * x * z ^ k) * z := by rw [ih]
      _ = o ^ (k + 1) * x * z ^ (k + 1) := by group

theorem relZMpow (m : ℕ) (a : (ZMod d)ˣ) (k : ℕ) :
    mk (g1 (n := m) (Gate.Z (d := d) h)) ^ k * mk (g1 (Gate.M a)) =
      mk (g1 (Gate.M a)) * (mk (g1 (Gate.Z h)) ^ (a : ZMod d).val) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_assoc, relZM h m a, ← mul_assoc, ih, mul_assoc, ← pow_succ]

omit [Fact d.Prime] in
theorem relZ0CXpow (m : ℕ) (k : ℕ) :
    mk (g1 (n := m + 1) (Gate.Z (d := d) h)) ^ k * mk (g2 (n := m) Gate.CX) =
      mk (g2 Gate.CX) * (mk (g1 (Gate.Z h)) * mk (shift (g1 (Gate.Z h)))) ^ k := by
  have e : mk (g1 (n := m + 1) (Gate.Z (d := d) h)) * mk (g2 (n := m) Gate.CX) =
      mk (g2 Gate.CX) * (mk (g1 (Gate.Z h)) * mk (shift (g1 (Gate.Z h)))) := by
    rw [← mul_assoc]; exact (rel21Z h m).symm
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_assoc, e, ← mul_assoc, ih, mul_assoc, ← pow_succ]

theorem relZ1CXpow (m : ℕ) (k : ℕ) :
    mk (shift (g1 (n := m) (Gate.Z (d := d) h))) ^ k * mk (g2 Gate.CX) =
      mk (g2 Gate.CX) * mk (shift (g1 (Gate.Z h))) ^ k :=
  ((Commute.pow_left (relZ1CX h m) k).eq)

/-- The `Z`-column and an affine generator (Lemma 12 at level 1). -/
theorem zcol_push {n : ℕ} (y : Gen (Gate d lv) n) (hy : y.IsAff) (e : Lab d n) :
    mk (zcol h n e * FreeMonoid.of y) =
      mk (FreeMonoid.of y) * mk (g0 (Gate.omega h)) ^ (zsc y e).val *
        mk (zcol h n (zmap y e)) := by
  induction y with
  | gate0 c => exact absurd hy (by simp [Gen.IsAff])
  | gate3 g => exact absurd hy (by simp [Gen.IsAff])
  | @gate1 m g =>
    have ho : ∀ q, Commute (mk (g0 (n := m + 1) (Gate.omega (d := d) h))) q :=
      mk_omega_central h
    cases g with
    | X =>
      show mk (zcol h (m + 1) e) * mk (g1 Gate.X) =
        mk (g1 Gate.X) * mk (g0 (Gate.omega h)) ^ (e 0).val * mk (zcol h (m + 1) e)
      rw [mk_zcol_succ, mul_assoc, relZXpow h m]
      set A := mk (shift (zcol h m (Fin.tail e)))
      set x := mk (g1 (n := m) (Gate.X (d := d) (lv := lv)))
      set o := mk (g0 (n := m + 1) (Gate.omega (d := d) h))
      set z := mk (g1 (n := m) (Gate.Z (d := d) h))
      have hxA : Commute x A := mk_comm1' Gate.X _
      have h1 : A * o ^ (e 0).val = o ^ (e 0).val * A := ((ho A).pow_left _).eq.symm
      have h2 : o ^ (e 0).val * x = x * o ^ (e 0).val := ((ho x).pow_left _).eq
      calc A * (o ^ (e 0).val * x * z ^ (e 0).val)
          = (A * o ^ (e 0).val) * x * z ^ (e 0).val := by group
        _ = o ^ (e 0).val * (A * x) * z ^ (e 0).val := by rw [h1]; group
        _ = o ^ (e 0).val * (x * A) * z ^ (e 0).val := by rw [← hxA.eq]
        _ = (o ^ (e 0).val * x) * A * z ^ (e 0).val := by group
        _ = x * o ^ (e 0).val * (A * z ^ (e 0).val) := by rw [h2]; group
    | M a =>
      show mk (zcol h (m + 1) e) * mk (g1 (Gate.M a)) =
        mk (g1 (Gate.M a)) * mk (g0 (Gate.omega h)) ^ (0 : ZMod d).val *
          mk (zcol h (m + 1) (Fin.cons ((a : ZMod d) * e 0) (Fin.tail e)))
      rw [mk_zcol_succ, mk_zcol_succ, Fin.tail_cons, Fin.cons_zero, ZMod.val_zero, pow_zero,
        mul_one, pow_val_mul (relZd h m)]
      set A := mk (shift (zcol h m (Fin.tail e)))
      set x := mk (g1 (n := m) (Gate.M (d := d) (lv := lv) a))
      set z := mk (g1 (n := m) (Gate.Z (d := d) h))
      have hxA : Commute x A := mk_comm1' (Gate.M a) _
      have e1 : z ^ (e 0).val * x = x * (z ^ (a : ZMod d).val) ^ (e 0).val := relZMpow h m a _
      calc A * z ^ (e 0).val * x = A * (z ^ (e 0).val * x) := by group
        _ = A * x * (z ^ (a : ZMod d).val) ^ (e 0).val := by rw [e1]; group
        _ = x * (A * (z ^ (a : ZMod d).val) ^ (e 0).val) := by rw [← hxA.eq]; group
    | Z h' => exact absurd hy (by simp [Gen.IsAff])
    | S h' => exact absurd hy (by simp [Gen.IsAff])
    | T h' => exact absurd hy (by simp [Gen.IsAff])
  | @gate2 m g =>
    cases g with
    | CX =>
      show mk (zcol h (m + 2) e) * mk (g2 Gate.CX) =
        mk (g2 Gate.CX) * mk (g0 (Gate.omega h)) ^ (0 : ZMod d).val *
          mk (zcol h (m + 2) (Fin.cons (e 0) (Fin.cons (e 0 + e 1) (Fin.tail (Fin.tail e)))))
      rw [mk_zcol_succ_succ, mk_zcol_succ_succ, ZMod.val_zero, pow_zero, mul_one]
      rw [show (Fin.cons (e 0) (Fin.cons (e 0 + e 1) (Fin.tail (Fin.tail e))) :
          Lab d (m + 2)) 1 = e 0 + e 1 from rfl,
        show (Fin.tail (Fin.tail (Fin.cons (e 0) (Fin.cons (e 0 + e 1) (Fin.tail (Fin.tail e)))
          : Lab d (m + 2))) : Lab d m) = Fin.tail (Fin.tail e) from rfl, Fin.cons_zero,
        pow_val_add (relZd_top h m)]
      set A := mk (shift (shift (zcol h m (Fin.tail (Fin.tail e)))))
      set z0 := mk (g1 (n := m + 1) (Gate.Z (d := d) h))
      set z1 := mk (shift (g1 (n := m) (Gate.Z (d := d) h)))
      set c := mk (g2 (n := m) (Gate.CX (d := d) (lv := lv)))
      have h01 : Commute z0 z1 := mk_comm1' (Gate.Z h) _
      have hcA : Commute c A := mk_comm2' Gate.CX _
      have e0 : z0 ^ (e 0).val * c = c * (z0 * z1) ^ (e 0).val := relZ0CXpow h m _
      have e1 : z1 ^ (e 1).val * c = c * z1 ^ (e 1).val := relZ1CXpow h m _
      calc A * z1 ^ (e 1).val * z0 ^ (e 0).val * c
          = A * z1 ^ (e 1).val * (c * (z0 * z1) ^ (e 0).val) := by rw [mul_assoc _ _ c, e0]
        _ = A * (z1 ^ (e 1).val * c) * (z0 * z1) ^ (e 0).val := by group
        _ = A * (c * z1 ^ (e 1).val) * (z0 ^ (e 0).val * z1 ^ (e 0).val) := by
            rw [e1, h01.mul_pow]
        _ = (A * c) * z1 ^ (e 1).val * (z0 ^ (e 0).val * z1 ^ (e 0).val) := by group
        _ = (c * A) * z1 ^ (e 1).val * (z1 ^ (e 0).val * z0 ^ (e 0).val) := by
            rw [← hcA.eq, ((h01.pow_left _).pow_right _).eq]
        _ = c * (A * (z1 ^ (e 0).val * z1 ^ (e 1).val) * z0 ^ (e 0).val) := by group
    | SWAP =>
      show mk (zcol h (m + 2) e) * mk (g2 Gate.SWAP) =
        mk (g2 Gate.SWAP) * mk (g0 (Gate.omega h)) ^ (0 : ZMod d).val *
          mk (zcol h (m + 2) (Fin.cons (e 1) (Fin.cons (e 0) (Fin.tail (Fin.tail e)))))
      rw [mk_zcol_succ_succ, mk_zcol_succ_succ, ZMod.val_zero, pow_zero, mul_one]
      rw [show (Fin.cons (e 1) (Fin.cons (e 0) (Fin.tail (Fin.tail e))) : Lab d (m + 2)) 1 =
          e 0 from rfl,
        show (Fin.tail (Fin.tail (Fin.cons (e 1) (Fin.cons (e 0) (Fin.tail (Fin.tail e))) :
          Lab d (m + 2))) : Lab d m) = Fin.tail (Fin.tail e) from rfl, Fin.cons_zero]
      set A := mk (shift (shift (zcol h m (Fin.tail (Fin.tail e)))))
      set z0 := mk (g1 (n := m + 1) (Gate.Z (d := d) h))
      set z1 := mk (shift (g1 (n := m) (Gate.Z (d := d) h)))
      set c := mk (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))
      have h01 : Commute z0 z1 := mk_comm1' (Gate.Z h) _
      have hcA : Commute c A := mk_comm2' Gate.SWAP _
      have e0' : z0 ^ (e 0).val * c = c * z1 ^ (e 0).val := (relSW_pow' m (Gate.Z h) _).symm
      have e1' : z1 ^ (e 1).val * c = c * z0 ^ (e 1).val := (relSW_pow m (Gate.Z h) _).symm
      calc A * z1 ^ (e 1).val * z0 ^ (e 0).val * c
          = A * z1 ^ (e 1).val * (c * z1 ^ (e 0).val) := by rw [mul_assoc _ _ c, e0']
        _ = A * (z1 ^ (e 1).val * c) * z1 ^ (e 0).val := by group
        _ = (A * c) * (z0 ^ (e 1).val * z1 ^ (e 0).val) := by rw [e1']; group
        _ = (c * A) * (z1 ^ (e 0).val * z0 ^ (e 1).val) := by
            rw [← hcA.eq, ((h01.pow_left _).pow_right _).eq]
        _ = c * (A * z1 ^ (e 0).val * z0 ^ (e 1).val) := by group
  | @up m g ih =>
    have e' := mk_shift (ih hy (Fin.tail e))
    simp only [map_mul, map_pow] at e'
    rw [mk_scalar_up] at e'
    show mk (zcol h (m + 1) e) * mk (shift (FreeMonoid.of g)) =
      mk (shift (FreeMonoid.of g)) * mk (g0 (Gate.omega h)) ^ (zsc g (Fin.tail e)).val *
        mk (zcol h (m + 1) (Fin.cons (e 0) (zmap g (Fin.tail e))))
    rw [mk_zcol_succ, mk_zcol_succ, Fin.tail_cons, Fin.cons_zero]
    have hz : Commute (mk (g1 (n := m) (Gate.Z (d := d) h))) (mk (shift (FreeMonoid.of g))) :=
      mk_comm1' (Gate.Z h) _
    calc mk (shift (zcol h m (Fin.tail e))) * mk (g1 (Gate.Z h)) ^ (e 0).val *
          mk (shift (FreeMonoid.of g))
        = mk (shift (zcol h m (Fin.tail e))) * mk (shift (FreeMonoid.of g)) *
          mk (g1 (Gate.Z h)) ^ (e 0).val := by rw [mul_assoc, (hz.pow_left _).eq, ← mul_assoc]
      _ = _ := by rw [e']; group

end Transport

section Layered

variable [Fact d.Prime] (h : 1 ≤ lv)

/-- A diagonal normal form moves through an affine circuit (Lemma 14 at
level 1). -/
theorem zcol_push_word {n : ℕ} (A : C d lv n) (hA : IsAffW A) (e : Lab d n) :
    ∃ (c : ℕ) (e' : Lab d n),
      mk (zcol h n e * A) = mk A * mk (g0 (Gate.omega h)) ^ c * mk (zcol h n e') := by
  induction A using FreeMonoid.inductionOn' generalizing e with
  | one => exact ⟨0, e, by simp⟩
  | mul_of y A ih =>
    obtain ⟨hy, hA⟩ := IsAffW.of_mul_left hA
    obtain ⟨c, e', he⟩ := ih hA (zmap y e)
    refine ⟨(zsc y e).val + c, e', ?_⟩
    have ho : ∀ q, Commute (mk (g0 (n := n) (Gate.omega (d := d) h))) q := mk_omega_central h
    calc mk (zcol h n e * (FreeMonoid.of y * A))
        = mk (zcol h n e * FreeMonoid.of y) * mk A := by simp only [map_mul, mul_assoc]
      _ = mk (FreeMonoid.of y) * mk (g0 (Gate.omega h)) ^ (zsc y e).val *
          (mk (zcol h n (zmap y e)) * mk A) := by rw [zcol_push h y hy e]; group
      _ = mk (FreeMonoid.of y) * mk (g0 (Gate.omega h)) ^ (zsc y e).val *
          (mk A * mk (g0 (Gate.omega h)) ^ c * mk (zcol h n e')) := by rw [← map_mul, he]
      _ = mk (FreeMonoid.of y) * (mk (g0 (Gate.omega h)) ^ (zsc y e).val * mk A) *
          mk (g0 (Gate.omega h)) ^ c * mk (zcol h n e') := by group
      _ = mk (FreeMonoid.of y) * (mk A * mk (g0 (Gate.omega h)) ^ (zsc y e).val) *
          mk (g0 (Gate.omega h)) ^ c * mk (zcol h n e') := by rw [((ho _).pow_left _).eq]
      _ = _ := by rw [map_mul, pow_add]; group

/-- `Z`-columns multiply coefficientwise. -/
theorem zcol_mul {n : ℕ} (e a : Lab d n) :
    mk (zcol h n e) * mk (zcol h n a) = mk (zcol h n (e + a)) := by
  induction n with
  | zero => simp [zcol]
  | succ n ih =>
    rw [mk_zcol_succ, mk_zcol_succ, mk_zcol_succ, Pi.add_apply, pow_val_add (relZd h n)]
    have hc : Commute (mk (g1 (n := n) (Gate.Z (d := d) h))) (mk (shift (zcol h n (Fin.tail a)))) :=
      mk_comm1' (Gate.Z h) _
    have e2 := mk_shift (show mk (zcol h n (Fin.tail e) * zcol h n (Fin.tail a)) =
      mk (zcol h n (Fin.tail e + Fin.tail a)) by rw [map_mul, ih])
    simp only [map_mul] at e2
    rw [show Fin.tail (e + a) = Fin.tail e + Fin.tail a from rfl, ← e2]
    calc mk (shift (zcol h n (Fin.tail e))) * mk (g1 (Gate.Z h)) ^ (e 0).val *
          (mk (shift (zcol h n (Fin.tail a))) * mk (g1 (Gate.Z h)) ^ (a 0).val)
        = mk (shift (zcol h n (Fin.tail e))) * (mk (g1 (Gate.Z h)) ^ (e 0).val *
          mk (shift (zcol h n (Fin.tail a)))) * mk (g1 (Gate.Z h)) ^ (a 0).val := by group
      _ = _ := by rw [(hc.pow_left _).eq]; group

/-- A `Z` gate is a `Z`-column. -/
def zunit : {n : ℕ} → Gen (Gate d lv) n → Lab d n
  | _ + 1, .gate1 (.Z _) => Fin.cons 1 0
  | _ + 1, .up g => Fin.cons 0 (zunit g)
  | _, _ => 0

/-- At level `1` a generator is affine, the scalar, or a `Z`-column. -/
theorem gen_cases1 {n : ℕ} (x : Gen (Gate d 1) n) :
    x.IsAff ∨ mk (FreeMonoid.of x) = mk (g0 (n := n) (Gate.omega le_rfl)) ∨
      mk (FreeMonoid.of x) = mk (zcol le_rfl n (zunit x)) := by
  induction x with
  | gate0 c => right; left; rw [gate0_eq c]
  | @gate1 m g =>
    cases g with
    | X => left; trivial
    | M a => left; trivial
    | Z h' =>
      right; right
      show mk (g1 (Gate.Z h')) = mk (zcol le_rfl (m + 1) (Fin.cons 1 0))
      rw [mk_zcol_succ, Fin.tail_cons, zcol_zero, map_one, map_one, one_mul, Fin.cons_zero,
        pow_val_one one_lt_d]
    | S h' => omega
    | T h' => omega
  | gate2 g => left; trivial
  | gate3 g => nomatch g
  | @up m g ih =>
    rcases ih with h1 | h1 | h1
    · left; exact h1
    · right; left
      rw [← shift_of, ← mk_scalar_up]
      exact mk_shift h1
    · right; right
      show mk (shift (FreeMonoid.of g)) = mk (zcol le_rfl (m + 1) (Fin.cons 0 (zunit g)))
      rw [mk_zcol_succ, Fin.tail_cons, Fin.cons_zero, ZMod.val_zero, pow_zero, mul_one]
      exact mk_shift h1

/-- Lemma 15 at level 1: every circuit is an affine circuit after a diagonal
normal form `ω^k Z^{a_0} ⋯ Z^{a_{n-1}}`. -/
theorem layered1 {n : ℕ} (w : C d 1 n) :
    ∃ (A : C d 1 n) (k : ℕ) (a : Lab d n), IsAffW A ∧
      mk w = mk A * mk (g0 (Gate.omega le_rfl)) ^ k * mk (zcol le_rfl n a) := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨1, 0, 0, fun x hx => by simp at hx, by simp [zcol_zero]⟩
  | mul_of x w ih =>
    obtain ⟨A, k, a, hA, hw⟩ := ih
    have ho : ∀ q, Commute (mk (g0 (n := n) (Gate.omega (d := d) (lv := 1) le_rfl))) q :=
      mk_omega_central le_rfl
    rcases gen_cases1 x with hx | hx | hx
    · refine ⟨FreeMonoid.of x * A, k, a, fun y hy => ?_, ?_⟩
      · rw [FreeMonoid.toList_of_mul] at hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hx
        · exact hA y hy
      · rw [map_mul, hw, map_mul]; group
    · refine ⟨A, k + 1, a, hA, ?_⟩
      rw [map_mul, hw, hx, pow_succ]
      calc mk (g0 (Gate.omega le_rfl)) * (mk A * mk (g0 (Gate.omega le_rfl)) ^ k *
            mk (zcol le_rfl n a))
          = (mk (g0 (Gate.omega le_rfl)) * mk A) * mk (g0 (Gate.omega le_rfl)) ^ k *
            mk (zcol le_rfl n a) := by group
        _ = (mk A * mk (g0 (Gate.omega le_rfl))) * mk (g0 (Gate.omega le_rfl)) ^ k *
            mk (zcol le_rfl n a) := by rw [(ho _).eq]
        _ = _ := by group
    · obtain ⟨c, e', he⟩ := zcol_push_word le_rfl A hA (zunit x)
      refine ⟨A, c + k, e' + a, hA, ?_⟩
      rw [map_mul, hw, hx, ← mul_assoc, ← mul_assoc, ← map_mul, he, ← zcol_mul le_rfl, pow_add]
      calc mk A * mk (g0 (Gate.omega le_rfl)) ^ c * mk (zcol le_rfl n e') *
            mk (g0 (Gate.omega le_rfl)) ^ k * mk (zcol le_rfl n a)
          = mk A * mk (g0 (Gate.omega le_rfl)) ^ c * (mk (zcol le_rfl n e') *
            mk (g0 (Gate.omega le_rfl)) ^ k) * mk (zcol le_rfl n a) := by group
        _ = _ := by rw [← ((ho (mk (zcol le_rfl n e'))).pow_left k).eq]; group

end Layered

/-! ### Uniqueness (Lemma 7 and Proposition 1 at level 1) -/

section Unique

local notation "𝒢" => gateData d lv

theorem sem_zcol [NeZero d] (h : 1 ≤ lv) (n : ℕ) (a : Lab d n) :
    (𝒢).sem n (zcol h n a) = PA.diag (fun v => ∑ i, a i * v i) := by
  induction n with
  | zero =>
    refine PA.ext (funext fun v => funext fun i => i.elim0) (funext fun v => ?_)
    simp [zcol, PA.diag]
  | succ n ih =>
    rw [zcol, map_mul, GateData.sem_shift, ih, fpow, map_pow, GateData.sem_of]
    have hp : ((𝒢).gen (Gen.gate1 (n := n) (Gate.Z h))) ^ (a 0).val =
        PA.onBottom n (PA.diag fun v => a 0 * v 0) := by
      show (PA.onBottomHom n (PA.diag fun v : Lab d 1 => v 0)) ^ (a 0).val = _
      rw [← map_pow, PA.diag_pow, PA.onBottomHom_apply]
      congr 2; funext v; simp
    rw [hp]
    refine PA.ext (funext fun v => funext fun i => ?_) (funext fun v => ?_)
    · simp only [PA.mul_f, Function.comp_apply, PA.diag_f, id]
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [PA.onTop_f_zero', PA.onBottom1_f_zero]; rfl
      · rw [PA.onTop_f_succ]
        show Fin.tail ((PA.onBottom n (PA.diag fun v : Lab d 1 => a 0 * v 0)).f v) j = v j.succ
        exact PA.onBottom1_f_succ (PA.diag fun v : Lab d 1 => a 0 * v 0) v j
    · simp only [PA.mul_q, PA.onTop_q', PA.onBottom1_q, PA.diag_q]
      have hf : (PA.onBottom n (PA.diag fun v : Lab d 1 => a 0 * v 0)).f v = v := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [PA.onBottom1_f_zero]; rfl
        · exact PA.onBottom1_f_succ (PA.diag fun v : Lab d 1 => a 0 * v 0) v j
      rw [hf, Fin.sum_univ_succ]; simp [Fin.tail]

theorem sem_omega_pow [NeZero d] (h : 1 ≤ lv) {n : ℕ} (k : ℕ) :
    (𝒢).sem n (g0 (Gate.omega h) ^ k) = PA.diag (fun _ => (k : ZMod d)) := by
  rw [map_pow, GateData.sem_of]
  show PA.diag (fun _ => (1 : ZMod d)) ^ k = _
  rw [PA.diag_pow]; congr 1; funext v; simp

theorem gen_aff_q {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsAff) (v : Lab d n) :
    ((𝒢).gen x).q v = 0 := by
  induction x with
  | gate0 c => exact absurd hx (by simp [Gen.IsAff])
  | gate3 g => exact absurd hx (by simp [Gen.IsAff])
  | gate1 g => cases g <;> first | rfl | exact absurd hx (by simp [Gen.IsAff])
  | gate2 g => cases g <;> rfl
  | up g ih => exact ih hx _

theorem sem_aff_q {n : ℕ} (w : C d lv n) (hw : IsAffW w) (v : Lab d n) :
    ((𝒢).sem n w).q v = 0 := by
  induction w using FreeMonoid.inductionOn' generalizing v with
  | one => rfl
  | mul_of x w ih =>
    obtain ⟨hx, hw⟩ := IsAffW.of_mul_left hw
    rw [map_mul, GateData.sem_of, PA.mul_q, ih hw, gen_aff_q x hx, add_zero]

end Unique

/-- Theorem 2 for `LinPhase_d`, for the pairs. -/
theorem complete1 [Fact d.Prime] {n : ℕ} {w v : C d 1 n}
    (h : (gateData d 1).sem n w = (gateData d 1).sem n v) : Derivable (theory d 1 n) w v := by
  obtain ⟨A, k, a, hA, hw⟩ := layered1 w
  obtain ⟨B, l, b, hB, hv⟩ := layered1 v
  have sw := pa_sound admissible_one (mk_eq_iff.1 (by rw [hw, map_mul, map_mul, map_pow] :
    mk w = mk (A * g0 (Gate.omega le_rfl) ^ k * zcol le_rfl n a)))
  have sv := pa_sound admissible_one (mk_eq_iff.1 (by rw [hv, map_mul, map_mul, map_pow] :
    mk v = mk (B * g0 (Gate.omega le_rfl) ^ l * zcol le_rfl n b)))
  rw [map_mul, map_mul, sem_omega_pow, sem_zcol] at sw sv
  have e := sw.symm.trans (h.trans sv)
  -- the phases
  have hq : ∀ u : Lab d n, (∑ i, a i * u i) + (k : ZMod d) = (∑ i, b i * u i) + (l : ZMod d) := by
    intro u
    have := congrArg (fun p : PA d n => p.q u) e
    simpa [PA.diag, sem_aff_q A hA, sem_aff_q B hB] using this
  have hkl : (k : ZMod d) = l := by simpa using hq 0
  have hab : a = b := by
    funext j
    have := hq (Pi.single j 1)
    simpa [Pi.single_apply, hkl] using this
  -- the affine parts
  have hAB : (gateData d 1).sem n A = (gateData d 1).sem n B := by
    refine PA.ext ?_ (funext fun u => by rw [sem_aff_q A hA, sem_aff_q B hB])
    have := congrArg PA.f e
    simpa [PA.diag] using this
  have hAB' := mk_eq_iff.2 (affine_complete admissible_one hA hB hAB)
  have hω : mk (g0 (n := n) (Gate.omega (d := d) (lv := 1) le_rfl)) ^ k =
      mk (g0 (Gate.omega le_rfl)) ^ l := by
    rw [← pow_mod_eq (relωd le_rfl), ← pow_mod_eq (relωd le_rfl) l, ← ZMod.val_natCast,
      ← ZMod.val_natCast, hkl]
  exact mk_eq_iff.1 (by rw [hw, hv, hAB', hω, hab])

end QCert.PhaseAffine
