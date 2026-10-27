/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Phase atoms

For the phase fragments of Blake (arXiv:2603.06466), a one-wire phase gate
`G` (`Z`, `S`, or `T`) on wire `0`, conjugated by a linear circuit `W`, is
the *atom* `W⁻¹ G W`: its phase is that of `G` at the first coordinate of
`W x`, a linear form in `x`.  This module shows that the atom depends only
on that linear form (`atom_wd`), so that a phase gate may be placed on any
linear form by any linear circuit that computes it.  This replaces the
placements by symmetries of the paper's Lemmas 11 and 12 (Section 5.3):
transport through a linear gate is conjugation, `V⁻¹ (W⁻¹ G W) V =
(W V)⁻¹ G (W V)`.

The proof: if `W` and `W'` compute the same first coordinate, `U = W' W⁻¹`
fixes the first coordinate, and such a linear circuit commutes with `G` on
wire `0` (`commute_of_row0`).  By the normal form of `LinearNF`, `U` is a
stair, a fan and a circuit one wire up; fixing the first coordinate forces
the stair and the fan to be trivial, or to be `CX s CX⁻¹`, which is the
`CX` from wire `0` to wire `1` (the Bruhat relation from (7)) and `M_{-1}`
on wire `1`.  Each of these commutes with `G` on wire `0`, `G` being on the
control of the `CX` ((29) for `S`, (39) for `T`, and Lemma 29's companion
for `Z`).
-/
import QCert.PhaseAffine.LinPhase

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

section Inverse

variable [Fact d.Prime]

/-- Every linear generator has a linear inverse word. -/
theorem linInv_gen : ∀ {n : ℕ} (x : Gen (Gate d lv) n), x.IsLin →
    ∃ w : C d lv n, IsLinW w ∧ mk (w * FreeMonoid.of x) = 1
  | _, .gate0 _, hx => absurd hx (by simp [Gen.IsLin])
  | _, .gate1 .X, hx => absurd hx (by simp [Gen.IsLin])
  | _, .gate1 (.M a), _ => ⟨g1 (Gate.M a⁻¹), isLinW_M _, by
      rw [map_mul]
      exact (qm_mul _ a a⁻¹).trans (by rw [mul_inv_cancel, qm_one])⟩
  | _, .gate1 (.Z _), hx => absurd hx (by simp [Gen.IsLin])
  | _, .gate1 (.S _), hx => absurd hx (by simp [Gen.IsLin])
  | _, .gate1 (.T _), hx => absurd hx (by simp [Gen.IsLin])
  | _, .gate2 .CX, _ => ⟨g2 Gate.CX ^ (d - 1), (isLinW_g2 _).pow _, by
      rw [map_mul, map_pow, ← pow_succ, Nat.sub_add_cancel (one_lt_d (d := d)).le]
      exact qa_pow _⟩
  | _, .gate2 .SWAP, _ => ⟨g2 Gate.SWAP, isLinW_g2 _, by rw [map_mul]; exact qs_mul_self _⟩
  | _, .gate3 g, _ => nomatch g
  | _, .up g, hx => by
    obtain ⟨w, hw, e⟩ := linInv_gen g hx
    refine ⟨shift w, isLinW_shift hw, ?_⟩
    rw [← shift_of, ← map_mul, ← shiftQ_mk, e, map_one]

/-- Every linear circuit has a linear inverse word. -/
theorem linInv {n : ℕ} (w : C d lv n) (hw : IsLinW w) :
    ∃ w' : C d lv n, IsLinW w' ∧ mk (w' * w) = 1 := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨1, IsLinW.one, by simp⟩
  | mul_of x w ih =>
    obtain ⟨hx, hw'⟩ := IsLinW.of_mul hw
    obtain ⟨a, ha, ea⟩ := linInv_gen x hx
    obtain ⟨b, hb, eb⟩ := ih hw'
    refine ⟨b * a, hb.mul ha, ?_⟩
    simp only [map_mul] at ea eb ⊢
    calc mk b * mk a * (mk (FreeMonoid.of x) * mk w)
        = mk b * (mk a * mk (FreeMonoid.of x)) * mk w := by group
      _ = 1 := by rw [ea, mul_one, eb]

end Inverse

section Row

variable [Fact d.Prime]

local notation "𝒢" => gateData d lv

theorem stairW_of_tail : ∀ (n : ℕ) (v : Lab d (n + 1)), Fin.tail v = 0 →
    stairW (lv := lv) n v = g1 (Gate.M (unitOf (v 0)))
  | 0, _, _ => rfl
  | n + 1, v, h => by rw [stairW, if_pos h]

theorem stairW_succ (n : ℕ) (v : Lab d (n + 2)) (h : Fin.tail v ≠ 0) :
    stairW (lv := lv) (n + 1) v =
      shift (stairW n (Fin.tail v)) * g2 Gate.CX ^ (v 0).val * g2 Gate.SWAP := by
  rw [stairW, if_neg h]

/-- The relabelling of a linear circuit is onto. -/
theorem sem_surj (hA : Admissible d lv) {n : ℕ} (u : C d lv n) :
    Function.Surjective ((𝒢).sem n u).f := by
  obtain ⟨r', hr'⟩ := mk_surjective ((mk u : Q d lv n)⁻¹)
  have : mk (u * r') = mk (1 : C d lv n) := by
    rw [map_mul, hr', map_one]; exact mul_inv_cancel _
  have e := pa_sound hA (mk_eq_iff.1 this)
  rw [map_mul, map_one] at e
  intro z
  refine ⟨((𝒢).sem n r').f z, ?_⟩
  have := congrArg (fun p => p.f z) e
  simpa only [PA.mul_f, Function.comp_apply, PA.one_f, id] using this

/-- `G` on wire `0` commutes with `CX` from wire `0` to wire `1` when `G` on
the control commutes with `CX`. -/
theorem commute_abar {m : ℕ} (g : Gate d lv 1)
    (hg : Commute (shiftQ (mk (g1 (n := m) g))) (qa (d := d) (lv := lv) m)) :
    Commute (mk (g1 (n := m + 1) g)) (qs m * qa m * qs m) := by
  have h1 : qs (d := d) (lv := lv) m * mk (g1 (n := m + 1) g) =
      shiftQ (mk (g1 (n := m) g)) * qs m := relSWnat m g
  have h2 : mk (g1 (n := m + 1) g) * qs (d := d) (lv := lv) m =
      qs m * shiftQ (mk (g1 (n := m) g)) := (relSWnat' m g).symm
  show mk (g1 g) * (qs m * qa m * qs m) = qs m * qa m * qs m * mk (g1 g)
  calc mk (g1 g) * (qs m * qa m * qs m) = (mk (g1 g) * qs m) * qa m * qs m := by group
    _ = qs m * (shiftQ (mk (g1 g)) * qa m) * qs m := by rw [h2]; group
    _ = qs m * qa m * (shiftQ (mk (g1 g)) * qs m) := by rw [hg.eq]; group
    _ = _ := by rw [← h1]; group

/-- A linear circuit that fixes the first coordinate commutes with a phase
gate on wire `0` that commutes with `CX` when placed on its control. -/
theorem commute_of_row0 (hA : Admissible d lv) (g : Gate d lv 1)
    (hg : ∀ m : ℕ, Commute (shiftQ (mk (g1 (n := m) g))) (qa (d := d) (lv := lv) m))
    {n : ℕ} (U : C d lv (n + 1)) (hU : IsLinW U)
    (h0 : ∀ y, ((𝒢).sem (n + 1) U).f y 0 = y 0) :
    Commute (mk U) (mk (g1 (n := n) g)) := by
  obtain ⟨v, h, hv, ⟨c, B, hB, rfl⟩, e⟩ := decompose n U hU
  have hsem : (𝒢).sem (n + 1) U = (𝒢).sem (n + 1) (stairW n v * (fanW n c * shift B)) :=
    pa_sound hA (mk_eq_iff.1 (by rw [e, map_mul, map_mul]; rfl))
  have hsurj := sem_surj hA B
  have hB0 : ((𝒢).sem n B).f 0 = 0 := (sem_lin B hB).1
  have hF : ∀ y0 y', ((𝒢).sem (n + 1) (fanW n c * shift B)).f (Fin.cons y0 y') =
      Fin.cons (y0 + ∑ j, c j * ((𝒢).sem n B).f y' j) (((𝒢).sem n B).f y') := by
    intro y0 y'; rw [sem_f_mul, sem_f_shift, sem_fanW]
  have hrow : ∀ y0 y', ((𝒢).sem (n + 1) (stairW n v)).f
      (Fin.cons (y0 + ∑ j, c j * ((𝒢).sem n B).f y' j) (((𝒢).sem n B).f y')) 0 = y0 := by
    intro y0 y'
    have := h0 (Fin.cons y0 y')
    rwa [hsem, sem_f_mul, hF, Fin.cons_zero] at this
  rw [e]
  by_cases ht : Fin.tail v = 0
  · have hv0 := tail_ne_zero_of hv ht
    have hrow' : ∀ y0 y', v 0 * (y0 + ∑ j, c j * ((𝒢).sem n B).f y' j) = y0 := by
      intro y0 y'
      have := hrow y0 y'
      rwa [stairW_of_tail n v ht, sem_f_M, Fin.cons_zero, unitOf_val hv0] at this
    have h1 : v 0 = 1 := by simpa [hB0] using hrow' 1 0
    have hc : c = 0 := by
      funext j
      obtain ⟨y', hy'⟩ := hsurj (Pi.single j 1)
      have := hrow' 0 y'
      simpa [h1, hy', Pi.single_apply] using this
    rw [stair_of_tail n v ht, h1, unitOf_one, qm_one, hc, fan_zero, one_mul, one_mul]
    exact (comm1Q g _).symm
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
      cases n with
      | zero => exact absurd (Subsingleton.elim _ _) ht
      | succ n' => exact ⟨n', rfl⟩
    have hrow' : ∀ y0 y', ((𝒢).sem (n' + 1) B).f y' 0 +
        v 0 * (y0 + ∑ j, c j * ((𝒢).sem (n' + 1) B).f y' j) = y0 := by
      intro y0 y'
      have := hrow y0 y'
      rw [stairW_succ n' v ht, ← Fin.cons_self_tail (((𝒢).sem (n' + 1) B).f y'),
        sem_f_mul, sem_f_mul, sem_f_SW, sem_f_CX_pow, sem_f_shift, Fin.cons_zero,
        ZMod.natCast_zmod_val] at this
      rw [← Fin.cons_self_tail (((𝒢).sem (n' + 1) B).f y')] at this ⊢
      simpa [Fin.cons_zero, mul_comm] using this
    have h1 : v 0 = 1 := by simpa [hB0] using hrow' 1 0
    have hc : c = Fin.cons (-1) 0 := by
      funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · obtain ⟨y', hy'⟩ := hsurj (Pi.single 0 1)
        have := hrow' 0 y'
        rw [h1, hy', zero_add, one_mul] at this
        simp [Pi.single_apply] at this
        rw [Fin.cons_zero]; linear_combination this
      · obtain ⟨y', hy'⟩ := hsurj (Pi.single k.succ 1)
        have := hrow' 0 y'
        rw [h1, hy', zero_add, one_mul] at this
        have hk : (0 : Fin (n' + 1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
        simp [Pi.single_apply, hk] at this
        rw [Fin.cons_succ]; simpa using this
    rw [stair_succ n' v ht, h1, hc, fan_cons_zero, val_one_zmod, pow_one, qa_neg_one]
    -- `a s a⁻¹` is `ā` and `M_{-1}` on wire `1`
    have hB := swap_conj_cx (d := d) (lv := lv) n'
    have hn : shiftQ (qm (d := d) (lv := lv) n' (-1)) * shiftQ (qm n' (-1)) = 1 :=
      relM1_top_sq n'
    have has : qa (d := d) (lv := lv) n' * qs n' * (qa n')⁻¹ =
        qs n' * qa n' * qs n' * shiftQ (qm n' (-1)) := by
      rw [hB, mul_assoc _ (shiftQ _), hn, mul_one]
    have hg0 : Commute (mk (g1 (n := n' + 1) g)) (qs n' * qa n' * qs n') := commute_abar g (hg n')
    have hm : Commute (mk (g1 (n := n' + 1) g)) (shiftQ (qm (d := d) (lv := lv) n' (-1))) :=
      comm1Q _ _
    have hS : Commute (mk (g1 (n := n' + 1) g)) (shiftQ (stair n' (Fin.tail v))) := comm1Q _ _
    have hBc : Commute (mk (g1 (n := n' + 1) g)) (shiftQ (mk B)) := comm1Q _ _
    rw [show shiftQ (stair n' (Fin.tail v)) * qa n' * qs n' * ((qa n')⁻¹ * shiftQ (mk B)) =
      shiftQ (stair n' (Fin.tail v)) * (qa n' * qs n' * (qa n')⁻¹) * shiftQ (mk B) by group,
      has]
    exact ((hS.mul_right (hg0.mul_right hm)).mul_right hBc).symm

end Row

/-! ### Atoms -/

section Atom

variable [Fact d.Prime]

/-- The atom of a one-wire gate `G` and a circuit `W`: `W⁻¹ G W`, with `G`
on wire `0`. -/
noncomputable def atom {n : ℕ} (g : Gate d lv 1) (W : C d lv (n + 1)) : Q d lv (n + 1) :=
  (mk W)⁻¹ * mk (g1 g) * mk W

local notation "𝒢" => gateData d lv

/-- An atom depends only on the first coordinate of its circuit. -/
theorem atom_wd (hA : Admissible d lv) (g : Gate d lv 1)
    (hg : ∀ m : ℕ, Commute (shiftQ (mk (g1 (n := m) g))) (qa (d := d) (lv := lv) m))
    {n : ℕ} {W W' : C d lv (n + 1)} (hW : IsLinW W) (hW' : IsLinW W')
    (hrow : ∀ y, ((𝒢).sem (n + 1) W).f y 0 = ((𝒢).sem (n + 1) W').f y 0) :
    atom g W = atom g W' := by
  obtain ⟨W'', hW'', e⟩ := linInv W hW
  have hWi : mk W'' = (mk W)⁻¹ := by rw [map_mul] at e; exact eq_inv_of_mul_eq_one_left e
  have e' : mk W * mk W'' = 1 := by rw [hWi, mul_inv_cancel]
  have hs : (𝒢).sem (n + 1) (W * W'') = 1 := by
    rw [← map_one ((𝒢).sem (n + 1))]
    exact pa_sound hA (mk_eq_iff.1 (by rw [map_mul, e', map_one]))
  have h0 : ∀ y, ((𝒢).sem (n + 1) (W' * W'')).f y 0 = y 0 := by
    intro y
    rw [sem_f_mul, ← hrow, ← sem_f_mul, hs]; rfl
  have hc := commute_of_row0 hA g hg (W' * W'') (hW'.mul hW'') h0
  rw [map_mul, hWi] at hc
  simp only [atom]
  calc (mk W)⁻¹ * mk (g1 g) * mk W
      = (mk W)⁻¹ * ((mk W' * (mk W)⁻¹)⁻¹ * (mk W' * (mk W)⁻¹ * mk (g1 g))) * mk W := by group
    _ = (mk W)⁻¹ * ((mk W' * (mk W)⁻¹)⁻¹ * (mk (g1 g) * (mk W' * (mk W)⁻¹))) * mk W := by
        rw [hc.eq]
    _ = _ := by group

end Atom

end QCert.PhaseAffine
