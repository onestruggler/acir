/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equations (342) and (344) from six wires on, by semantic separation

In both, the first gate is the multi-controlled `H` on the wires `0, 1`
(control `c₁` on wire `2`, the wires `3, …` coloured by `x`).  The second is
the multi-controlled `H` with its box on wire `1`, its `H` on wire `2`
(control `c₂` on wire `0`) for (344), and with its box on wire `0`, its `H`
on wire `2` (control `c₂` on wire `1`) for (342); the wires `3, …` coloured
by `y`, and `x ≠ y`.

As for (339) (`E339b`): `sep_reduce` puts the difference on wire `3`, black
for `x`, and the swap of the wires `2, 3` gives the frame.  There the first
gate is (269) `P ⊗ P` around the box of (339) with its control on wire `1`
black (`hg0_box4`), whose pieces are `E339b`'s (`piecesA … true`).  The
second gate is `E339a.BE` for (344), and `BE` conjugated by the swap of the
wires `0, 1` for (342).  So, conjugating the pair by `P ⊗ P`, the second
gate's pieces are `E339b`'s conjugated by `Q`: `P ⊗ P` for (344), `P ⊗ P`
and the swap of the wires `0, 1` for (342) (`qL`, `qL'`, letters on the
wires `0, 1`).  The four kinds of pairs:

* two rotations: as `E339s.commRR_s`, the conjugation by `Q` keeping wire
  `2` (`commRR_q`, completeness on five wires);
* the remainder of the box against a rotation: as `E339s.commAr_s`
  (`commAr_q`, a semantic step without wire `4`);
* a rotation against the remainder: `Q` takes the remainder to the box on
  wire `1` (resp. `0`) idle on wire `3` between `P ⊗ P`; conjugated by the
  swap of the wires `3, 4` both avoid wire `4` (`commRpp`);
* the two remainders: merged on their idle wires (309), the four products
  are (338) under the swap of the wires `0, 1` for (344), (337) for (342),
  between `P ⊗ P`.

No window is decided here; the only decisions are two-wire checks of the
conjugating words.  Memory (2026-10-29): 12 s, peak 0.30 GB anonymous.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E339b

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8 Sep

/-- Pointwise equality of control functions on the wires `0, …, 4` and above. -/
macro "ctl_case44" : tactic => `(tactic| (intro i hi; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨
  i = 3 ∨ i = 4 ∨ 5 ≤ i) with h | h | h | h | h | h5 <;> (try subst h) <;>
  simp only [colOn, ctlOr, ctlAt, yH, yS, xE, xF, zS, xA, xA4, yB, yB3, ctlX, setCtl,
    Net.tau, Function.comp] <;> (try split_ifs) <;>
  first | rfl | (exfalso; omega) | (simp [List.lookup]; done) | omega))

/-! ## Local small words -/

/-- Two local words with the same semantics on `K` wires are equal from
`K + 1` wires on (completeness on `K` wires). -/
theorem locK {K : ℕ} {L R : List Lt} (hL : L.all (isLoc K) = true) (hR : R.all (isLoc K) = true)
    (h : SE.lcheck K true L R = true) {N : ℕ} (hN : K < N) (ih : IH N) :
    Derivable (theory N) (wc K N L) (wc K N R) := by
  have hL' : ∀ x ∈ L, x.ok K = true := fun x hx => isLoc_ok (List.all_eq_true.1 hL x hx)
  have hR' : ∀ x ∈ R, x.ok K = true := fun x hx => isLoc_ok (List.all_eq_true.1 hR x hx)
  have he := SE.lcheck_sound true hL' hR' h
  rw [circWL_loc, circWL_loc] at he
  have dK : Derivable (theory K) (wc K K L) (wc K K R) := ih K hN _ _ (sem_of_eval he)
  exact der_loc hL hR dK N (by omega)

theorem wc_conjL (K N : ℕ) (u X u' : List Lt) :
    wc K N (u ++ X ++ u') = wc K N u' * wc K N X * wc K N u := by
  rw [wc_append, wc_append, mul_assoc]

/-! ## The conjugating words -/

/-- What is asked of the words `qL` (applied first) and `qL'` conjugating
the pieces of the second gate: small letters on the wires `0, 1`, inverse. -/
structure QOK (qL qL' : List Lt) : Prop where
  loc : ∀ x ∈ qL ++ qL', x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x ∧
    isLoc 5 x = true ∧ isSmall x = true ∧ x.ok 2 = true ∧ isLoc 2 x = true
  rt : rtW qL 2 = some 2
  rt' : rtW qL' 2 = some 2
  on : SE.lcheck 2 true (qL ++ qL') [] = true
  off : SE.lcheck 2 false (qL ++ qL') [] = true

/-- The word of a rotation of the second gate. -/
abbrev bw (qL qL' : List Lt) (h : Lt) : List Lt := qL ++ (uL ++ [h] ++ uL') ++ qL'

section Q

variable {qL qL' : List Lt} (hq : QOK qL qL')
include hq

theorem QOK.small : qL.all isSmall = true ∧ qL'.all isSmall = true := by
  constructor <;> refine List.all_eq_true.2 fun x hx => (hq.loc x (by simp [hx])).2.2.2.2.1

theorem QOK.inv (K M : ℕ) (hM : 2 ≤ M) :
    opsQ.eval M (wc K M qL') * opsQ.eval M (wc K M qL) = 1 := by
  have h := inv_of_lcheck (K := 2) (l := qL ++ qL') (fun x hx => (hq.loc x hx).2.2.2.2.2.1)
    hq.on hq.off M hM
  rw [wc_append, map_mul] at h
  rwa [wc_small 2 K M qL hq.small.1, wc_small 2 K M qL' hq.small.2] at h

theorem QOK.ok (K : ℕ) (hK : 5 ≤ K) : (∀ x ∈ qL, x.ok K = true) ∧ (∀ x ∈ qL', x.ok K = true) := by
  have h : ∀ x ∈ qL ++ qL', x.ok K = true := by
    intro x hx
    obtain ⟨y, rfl⟩ : ∃ y, x = .s y := by
      have := (hq.loc x hx).2.2.2.2.1
      cases x with
      | s y => exact ⟨y, rfl⟩
      | g _ _ _ _ => simp [isSmall] at this
    have := (hq.loc _ hx).1
    simp only [Lt.ok, decide_eq_true_eq] at this ⊢
    omega
  exact ⟨fun x hx => h x (by simp [hx]), fun x hx => h x (by simp [hx])⟩

theorem QOK.ok4 : (∀ x ∈ qL, x.ok 4 = true) ∧ (∀ x ∈ qL', x.ok 4 = true) := by
  have h : ∀ x ∈ qL ++ qL', x.ok 4 = true := by
    intro x hx
    obtain ⟨y, rfl⟩ : ∃ y, x = .s y := by
      have := (hq.loc x hx).2.2.2.2.1
      cases x with
      | s y => exact ⟨y, rfl⟩
      | g _ _ _ _ => simp [isSmall] at this
    have := (hq.loc _ hx).2.2.2.2.2.1
    simp only [Lt.ok, decide_eq_true_eq] at this ⊢
    omega
  exact ⟨fun x hx => h x (by simp [hx]), fun x hx => h x (by simp [hx])⟩

theorem triv_bw5 (n : ℕ) {c1 c3 : Bool} {h : Lt} (hh : h ∈ rots c1 false c3) :
    Triv 2 1 (opsQ.eval (n + 5) (wc 5 (n + 5) (bw qL qL' h))) := by
  show Triv 2 1 (opsQ.eval (n + 5) (wc 5 (n + 5) (qL ++ (uL ++ [h] ++ uL') ++ qL')))
  rw [wc_conjL]
  exact triv_conj (K := 5) (by omega) (hq.ok 5 le_rfl).1 (hq.ok 5 le_rfl).2 (by omega) (by omega)
    hq.rt hq.rt' (hq.inv 5 (n + 5) (by omega)) (triv_uh n hh)

theorem triv_bw4 (M : ℕ) (hM : 5 ≤ M) {c1 c3 : Bool} {h : Lt} (hh : h ∈ rots c1 false c3) :
    Triv 2 1 (opsQ.eval M (wc 4 M (bw qL qL' h))) := by
  show Triv 2 1 (opsQ.eval M (wc 4 M (qL ++ (uL ++ [h] ++ uL') ++ qL')))
  rw [wc_conjL]
  have hx : Triv 2 1 (opsQ.eval M (h.circ 4 M)) := by
    rw [← rots_rebase hh]
    simpa using triv_rots M (by omega) c1 false c3 h hh
  have tB : Triv 2 1 (opsQ.eval M (wc 4 M (uL ++ [h] ++ uL'))) := by
    rw [wc_conj]
    exact triv_conj (K := 4) (by omega) uL_ok.1 uL_ok.2 (by omega) (by omega) rt_uL rt_uL'
      (uL_inv4 M (by omega)) hx
  exact triv_conj (K := 4) (by omega) hq.ok4.1 hq.ok4.2 (by omega) (by omega) hq.rt hq.rt'
    (hq.inv 4 M (by omega)) tB

theorem bw_loc5 {c1 c3 : Bool} {h : Lt} (hh : h ∈ rots c1 false c3) :
    (bw qL qL' h).all (isLoc 5) = true := by
  have lh := rots_loc5 _ _ _ h hh
  have lq : ∀ x ∈ qL ++ qL', isLoc 5 x = true := fun x hx => (hq.loc x hx).2.2.2.1
  refine List.all_eq_true.2 fun x hx => ?_
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (hx | (hx | rfl) | hx) | hx
  · exact lq x (by simp [hx])
  · exact List.all_eq_true.1 uL_loc5.1 x hx
  · exact lh
  · exact List.all_eq_true.1 uL_loc5.2 x hx
  · exact lq x (by simp [hx])

theorem bw_drop4 {c1 c3 : Bool} {h : Lt} (hh : h ∈ rots c1 false c3) :
    ∀ x ∈ bw qL qL' h, x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := by
  have hr := rots_drop4 _ _ _ h hh
  have hu := List.all_eq_true.1 uL_drop4
  have lq : ∀ x ∈ qL ++ qL', x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x :=
    fun x hx => ⟨(hq.loc x hx).1, (hq.loc x hx).2.1, (hq.loc x hx).2.2.1⟩
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (hx | (hx | rfl) | hx) | hx
  · exact lq x (by simp [hx])
  · have := hu x (List.mem_append_left _ hx)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · exact hr
  · have := hu x (List.mem_append_right _ hx)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · exact lq x (by simp [hx])

/-- A rotation of the first gate passes a conjugated rotation of the second
(completeness on five wires). -/
theorem commRR_q (m : ℕ) (ih : IH (m + 6)) {b1 b3 c1 c3 : Bool} {r h : Lt}
    (hr : r ∈ rots b1 true b3) (hh : h ∈ rots c1 false c3) :
    Derivable (theory (m + 6)) (wc 5 (m + 6) ([.s (.S 3), r, .s (.S 3)] ++ bw qL qL' h))
      (wc 5 (m + 6) (bw qL qL' h ++ [.s (.S 3), r, .s (.S 3)])) := by
  have hs := sep_sem (K := 5) (M := 0 + 5) (p := 2) (by decide : (0 : Fin 2) ≠ 1)
    (triv_s3r 0 hr) (triv_bw5 hq 0 hh)
  have d5 := ih 5 (by omega) _ _ hs
  have lr := rots_loc5 _ _ _ r hr
  have lb := bw_loc5 hq hh
  have l1 : ([.s (.S 3), r, .s (.S 3)] ++ bw qL qL' h).all (isLoc 5) = true := by
    rw [List.all_append, lb]; simp only [List.all_cons, List.all_nil, lr] <;> decide
  have l2 : (bw qL qL' h ++ [.s (.S 3), r, .s (.S 3)]).all (isLoc 5) = true := by
    rw [List.all_append, lb]; simp only [List.all_cons, List.all_nil, lr] <;> decide
  exact der_loc l1 l2 d5 (m + 6) (by omega)

/-- The remainder `Ar` of the first gate passes a conjugated rotation of the
second: both avoid wire `4`. -/
theorem commAr_q (m : ℕ) (ih : IH (m + 6)) (c₁ c₂ : Bool) {c1 c3 : Bool} {h : Lt}
    (hh : h ∈ rots c1 false c3) :
    Derivable (theory (m + 6)) (wc 5 (m + 6) ([Ar c₁ c₂] ++ bw qL qL' h))
      (wc 5 (m + 6) (bw qL qL' h ++ [Ar c₁ c₂])) := by
  have hb := bw_drop4 hq hh
  have hA := Ar_drop4 c₁ c₂
  have mem : ∀ x ∈ [Ar c₁ c₂] ++ bw qL qL' h,
      x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rw [List.mem_singleton.1 hx]; exact hA
    · exact hb x hx
  have mem' : ∀ x ∈ bw qL qL' h ++ [Ar c₁ c₂],
      x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := fun x hx =>
    mem x (by simp only [List.mem_append] at hx ⊢; tauto)
  have e1 : ([Ar c₁ c₂] ++ bw qL qL' h).map (Lt.drop 4) = [Ar c₁ c₂] ++ bw qL qL' h := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem x hx).2.2), List.map_id]
  have e2 : (bw qL qL' h ++ [Ar c₁ c₂]).map (Lt.drop 4) = bw qL qL' h ++ [Ar c₁ c₂] := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem' x hx).2.2), List.map_id]
  have tA : Triv 2 0 (opsQ.eval (m + 1 + 4) (wc 4 (m + 1 + 4) [Ar c₁ c₂])) := by
    have := triv_g (K := 4) (N := m + 1 + 4) (by omega) .box [0] [(1, c₂), (2, true), (3, c₁)] true
      rfl (p := 2) (by omega) (by decide) (b := true) rfl
    simpa [wc, drawn, Ar] using this
  have tB := triv_bw4 hq (m + 1 + 4) (by omega) hh
  have hsem := sep_sem (K := 4) (M := m + 1 + 4) (by decide : (0 : Fin 2) ≠ 1) tA tB
  rw [← e1, ← e2] at hsem
  exact SE.Frame.window (frame 4) (m + 1) ih (q := 4) le_rfl
    (fun x hx => ⟨(mem x hx).1, (mem x hx).2.1⟩) (fun x hx => ⟨(mem' x hx).1, (mem' x hx).2.1⟩)
    hsem

/-- `bw` as a conjugation. -/
theorem wc_bw (N : ℕ) (h : Lt) :
    wc 5 N (bw qL qL' h) = wc 4 N qL' * (wc 4 N uL' * h.circ 5 N * wc 4 N uL) * wc 4 N qL := by
  show wc 5 N (qL ++ (uL ++ [h] ++ uL') ++ qL') = _
  rw [wc_conjL, wc_conj, wc_small 5 4 _ qL hq.small.1, wc_small 5 4 _ qL' hq.small.2,
    wc_small 5 4 _ uL uL_small.1, wc_small 5 4 _ uL' uL_small.2]

theorem commRR_qc (m : ℕ) (ih : IH (m + 6)) {b1 b3 c1 c3 : Bool} {r h : Lt}
    (hr : r ∈ rots b1 true b3) (hh : h ∈ rots c1 false c3) :
    Comm (m + 6) (swAt (m + 6) 3 * r.circ 4 (m + 6) * swAt (m + 6) 3)
      (wc 4 (m + 6) qL' * (wc 4 (m + 6) uL' * h.circ 4 (m + 6) * wc 4 (m + 6) uL) *
        wc 4 (m + 6) qL) := by
  have d := commRR_q hq m ih hr hh
  rw [wc_app2 5 (m + 6) [.s (.S 3), r, .s (.S 3)] (bw qL qL' h),
    wc_app2 5 (m + 6) (bw qL qL' h) [.s (.S 3), r, .s (.S 3)], wc_three, wc_bw hq, circ_S,
    rots_rebase hr, rots_rebase hh] at d
  exact d

theorem commArR_qc (m : ℕ) (ih : IH (m + 6)) (x : ℕ → Bool) (c₁ c₂ : Bool) {c1 c3 : Bool}
    {h : Lt} (hh : h ∈ rots c1 false c3) :
    Comm (m + 6) (cX 5 (m + 6) x (Ar c₁ c₂))
      (wc 4 (m + 6) qL' * (wc 4 (m + 6) uL' * h.circ 4 (m + 6) * wc 4 (m + 6) uL) *
        wc 4 (m + 6) qL) := by
  have d := commAr_q hq m ih c₁ c₂ hh
  have hb := bw_drop4 hq hh
  have hl : ∀ g ∈ [Ar c₁ c₂] ++ bw qL qL' h, g.ok 5 = true := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · rw [List.mem_singleton.1 hg]; exact (Ar_drop4 c₁ c₂).1
    · exact (hb g hg).1
  have hr' : ∀ g ∈ bw qL qL' h ++ [Ar c₁ c₂], g.ok 5 = true := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact (hb g hg).1
    · rw [List.mem_singleton.1 hg]; exact (Ar_drop4 c₁ c₂).1
  have hc := colour_wc (K := 5) (N := m + 6) (by omega) x hl hr' d
  have loc := bw_loc5 hq hh
  have eW : wcX 5 (m + 6) x (bw qL qL' h) = wc 5 (m + 6) (bw qL qL' h) := by
    unfold wcX wc
    congr 1
    exact List.map_congr_left (fun g hg => cX_loc x (List.all_eq_true.1 loc g hg))
  have eS : wcX 5 (m + 6) x [Ar c₁ c₂] = cX 5 (m + 6) x (Ar c₁ c₂) := by
    simp [wcX, drawn]
  have e2 : ∀ a b : List Lt, wcX 5 (m + 6) x (a ++ b) =
      drawn [wcX 5 (m + 6) x a, wcX 5 (m + 6) x b] := by
    intro a b
    simp only [wcX, List.map_append, drawn_append, drawn_two]
  rw [e2 [Ar c₁ c₂] (bw qL qL' h), e2 (bw qL qL' h) [Ar c₁ c₂], eW, eS, wc_bw hq,
    rots_rebase hh] at hc
  exact hc

end Q

/-! ## The remainder of the second gate against a rotation of the first -/

/-- The box idle on wire `3` with its box wire on wire `t ∈ {0, 1}`, its
control on the other of the wires `0, 1` of colour `c`, white on wire `2`. -/
abbrev Yt (N t : ℕ) (c : Bool) (y : ℕ → Bool) : Circ N :=
  mc N .box [t] (ctlOr (ctlAt (1 - t) c) (ctlOr (ctlAt 2 false) (colOn 4 N y)))

/-- `Yt` conjugated by the swap of the wires `3, 4`, as a letter. -/
def Ylt (t : ℕ) (c b : Bool) : Lt := .g .box [t] [(1 - t, c), (2, false), (3, b)] true

theorem Ylt_facts : ∀ t, t ≤ 1 → ∀ c b : Bool,
    (Ylt t c b).ok 5 = true ∧ (Ylt t c b).avoids 4 = true ∧ (Ylt t c b).drop 4 = Ylt t c b ∧
      (Ylt t c b).ok 4 = true := by
  intro t ht c b
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl <;> revert c b <;> decide

theorem ppL_small : N13.ppL.all (fun x => x.ok 5 && x.avoids 4 && x.drop 4 == x && isLoc 5 x &&
    isSmall x && x.ok 2) = true := by decide

theorem rt_ppL : rtW N13.ppL 2 = some 2 := by decide
theorem chkPP_on : SE.lcheck 2 true (N13.ppL ++ N13.ppL) [] = true := by decide +kernel
theorem chkPP_off : SE.lcheck 2 false (N13.ppL ++ N13.ppL) [] = true := by decide +kernel

theorem ppL_ok2 : ∀ x ∈ N13.ppL ++ N13.ppL, x.ok 2 = true := by decide

theorem ppL_inv (M : ℕ) (hM : 2 ≤ M) :
    opsQ.eval M (wc 4 M N13.ppL) * opsQ.eval M (wc 4 M N13.ppL) = 1 := by
  have h := inv_of_lcheck (K := 2) (l := N13.ppL ++ N13.ppL) ppL_ok2 chkPP_on chkPP_off M hM
  rw [wc_append, map_mul] at h
  have e : wc 2 M N13.ppL = wc 4 M N13.ppL := wc_small 2 4 M _ (by decide)
  rwa [e] at h

theorem wc_ppL6 (m : ℕ) : wc 4 (m + 6) N13.ppL = (pp : Circ (m + 6)) := wc_ppL (m + 1)

theorem wc5_ppL (N : ℕ) : wc 5 N N13.ppL = wc 4 N N13.ppL := wc_small 5 4 N _ (by decide)

/-- A rotation of the first gate passes `P ⊗ P · Yl · P ⊗ P`: both avoid wire `4`. -/
theorem commRY_pp (m : ℕ) (ih : IH (m + 6)) {b1 b3 : Bool} {r : Lt} (hr : r ∈ rots b1 true b3)
    (t : ℕ) (ht : t ≤ 1) (c b : Bool) :
    Derivable (theory (m + 6)) (wc 5 (m + 6) ([r] ++ (N13.ppL ++ [Ylt t c b] ++ N13.ppL)))
      (wc 5 (m + 6) ((N13.ppL ++ [Ylt t c b] ++ N13.ppL) ++ [r])) := by
  have hr4 := rots_drop4 _ _ _ r hr
  have hY := Ylt_facts t ht c b
  have hp : ∀ x ∈ N13.ppL, x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := by
    intro x hx
    have := List.all_eq_true.1 ppL_small x hx
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨this.1.1.1.1.1, this.1.1.1.1.2, this.1.1.1.2⟩
  have hw : ∀ x ∈ N13.ppL ++ [Ylt t c b] ++ N13.ppL,
      x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := by
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with (hx | rfl) | hx
    · exact hp x hx
    · exact ⟨hY.1, hY.2.1, hY.2.2.1⟩
    · exact hp x hx
  have mem : ∀ x ∈ [r] ++ (N13.ppL ++ [Ylt t c b] ++ N13.ppL),
      x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rw [List.mem_singleton.1 hx]; exact hr4
    · exact hw x hx
  have mem' : ∀ x ∈ (N13.ppL ++ [Ylt t c b] ++ N13.ppL) ++ [r],
      x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hw x hx
    · rw [List.mem_singleton.1 hx]; exact hr4
  have e1 : ([r] ++ (N13.ppL ++ [Ylt t c b] ++ N13.ppL)).map (Lt.drop 4) =
      [r] ++ (N13.ppL ++ [Ylt t c b] ++ N13.ppL) := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem x hx).2.2), List.map_id]
  have e2 : ((N13.ppL ++ [Ylt t c b] ++ N13.ppL) ++ [r]).map (Lt.drop 4) =
      (N13.ppL ++ [Ylt t c b] ++ N13.ppL) ++ [r] := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem' x hx).2.2), List.map_id]
  have tR : Triv 2 0 (opsQ.eval (m + 1 + 4) (wc 4 (m + 1 + 4) [r])) := by
    rw [wc_one', ← rots_rebase hr]
    simpa using triv_rots (m + 1 + 4) (by omega) b1 true b3 r hr
  have tY0 : Triv 2 1 (opsQ.eval (m + 1 + 4) ((Ylt t c b).circ 4 (m + 1 + 4))) := by
    have := triv_g (K := 4) (N := m + 1 + 4) (by omega) .box [t] [(1 - t, c), (2, false), (3, b)]
      true hY.2.2.2 (p := 2) (by omega) (by simp; omega) (b := false)
      (by rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl <;> rfl)
    simpa [Ylt] using this
  have hpo : ∀ x ∈ N13.ppL, x.ok 4 = true := by
    intro x hx
    have := List.all_eq_true.1 ppL_small x hx
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨y, rfl⟩ : ∃ y, x = .s y := by
      cases x with
      | s y => exact ⟨y, rfl⟩
      | g _ _ _ _ => simp [isSmall] at this
    have h2 := this.2
    simp only [Lt.ok, decide_eq_true_eq] at h2 ⊢
    omega
  have tY : Triv 2 1 (opsQ.eval (m + 1 + 4) (wc 4 (m + 1 + 4) (N13.ppL ++ [Ylt t c b] ++ N13.ppL))) := by
    rw [wc_conj]
    exact triv_conj (K := 4) (by omega) hpo hpo (by omega) (by omega) rt_ppL rt_ppL
      (ppL_inv (m + 1 + 4) (by omega)) tY0
  have hsem := sep_sem (K := 4) (M := m + 1 + 4) (by decide : (0 : Fin 2) ≠ 1) tR tY
  rw [← e1, ← e2] at hsem
  exact SE.Frame.window (frame 4) (m + 1) ih (q := 4) le_rfl
    (fun x hx => ⟨(mem x hx).1, (mem x hx).2.1⟩) (fun x hx => ⟨(mem' x hx).1, (mem' x hx).2.1⟩)
    hsem

/-- The swap of the wires `3, 4` passes `P ⊗ P`. -/
theorem s3_pp (m : ℕ) :
    Derivable (theory (m + 6)) (swAt (m + 6) 3 * (pp : Circ (m + 6))) (pp * swAt (m + 6) 3) :=
  comm_low_high _ _ (lowW_mono (lowW_pp (m + 4)) (by omega)) (gLo_swAt (m + 6) 3)

/-- A rotation of the first gate, conjugated by the swap of the wires `3, 4`,
passes `P ⊗ P · Yt · P ⊗ P`. -/
theorem commRpp (m : ℕ) (ih : IH (m + 6)) (y : ℕ → Bool) (c : Bool) (t : ℕ) (ht : t ≤ 1)
    {b1 b3 : Bool} {r : Lt} (hr : r ∈ rots b1 true b3) :
    Comm (m + 6) (swAt (m + 6) 3 * r.circ 4 (m + 6) * swAt (m + 6) 3)
      ((pp : Circ (m + 6)) * Yt (m + 6) t c y * pp) := by
  -- the remainder conjugated by the swap of the wires `3, 4`
  have h3 := swBH ih 3 (by omega) .box (Or.inl rfl) [t] [t]
    (ctlOr (ctlAt (1 - t) c) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y)))
    (ctlX 5 [(1 - t, c), (2, false), (3, y 4)] y) rfl (List.nodup_singleton t)
    (by intro u hu; simp at hu; omega)
    (by rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl <;> rfl)
    (by rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl <;> ctl_case44)
  have eY : cX 5 (m + 6) y (Ylt t c (y 4)) =
      mc (m + 6) .box [t] (ctlX 5 [(1 - t, c), (2, false), (3, y 4)] y) := rfl
  -- the commutation without wire `4`, coloured by `y`
  have d := commRY_pp m ih hr t ht c (y 4)
  have hr4 := rots_drop4 _ _ _ r hr
  have hY := Ylt_facts t ht c (y 4)
  have hp : ∀ x ∈ N13.ppL, x.ok 5 = true := by
    intro x hx
    have := List.all_eq_true.1 ppL_small x hx
    simp only [Bool.and_eq_true] at this
    exact this.1.1.1.1.1
  have hw : ∀ x ∈ N13.ppL ++ [Ylt t c (y 4)] ++ N13.ppL, x.ok 5 = true := by
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with (hx | rfl) | hx
    · exact hp x hx
    · exact hY.1
    · exact hp x hx
  have hl : ∀ g ∈ [r] ++ (N13.ppL ++ [Ylt t c (y 4)] ++ N13.ppL), g.ok 5 = true := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · rw [List.mem_singleton.1 hg]; exact hr4.1
    · exact hw g hg
  have hr' : ∀ g ∈ (N13.ppL ++ [Ylt t c (y 4)] ++ N13.ppL) ++ [r], g.ok 5 = true := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hw g hg
    · rw [List.mem_singleton.1 hg]; exact hr4.1
  have hc := colour_wc (K := 5) (N := m + 6) (by omega) y hl hr' d
  have eP : wcX 5 (m + 6) y N13.ppL = (pp : Circ (m + 6)) := by
    have : wcX 5 (m + 6) y N13.ppL = wc 5 (m + 6) N13.ppL := by
      unfold wcX wc
      congr 1
    rw [this, wc5_ppL, wc_ppL6]
  have e2 : ∀ a b : List Lt, wcX 5 (m + 6) y (a ++ b) =
      drawn [wcX 5 (m + 6) y a, wcX 5 (m + 6) y b] := by
    intro a b
    simp only [wcX, List.map_append, drawn_append, drawn_two]
  have e3 : wcX 5 (m + 6) y (N13.ppL ++ [Ylt t c (y 4)] ++ N13.ppL) =
      (pp : Circ (m + 6)) * cX 5 (m + 6) y (Ylt t c (y 4)) * pp := by
    simp only [wcX, List.map_append, drawn_append, List.map_singleton, drawn_one]
    rw [← wcX, eP, mul_assoc]
  have eR : wcX 5 (m + 6) y [r] = r.circ 4 (m + 6) := by
    simp only [wcX, List.map_singleton, drawn_one]
    rw [rots_cX hr, rots_rebase hr]
  rw [e2 [r] (N13.ppL ++ [Ylt t c (y 4)] ++ N13.ppL),
    e2 (N13.ppL ++ [Ylt t c (y 4)] ++ N13.ppL) [r], e3, eR, eY] at hc
  -- conjugate back by the swap of the wires `3, 4`
  have hs := swsw (m + 6) 3 (by omega)
  have k := Comm.conj hc hs
  refine Comm.congr (Derivable.refl _) ?_ k
  have hc3 := s3_pp m
  have e4 : swAt (m + 6) 3 * ((pp : Circ (m + 6)) *
      mc (m + 6) .box [t] (ctlX 5 [(1 - t, c), (2, false), (3, y 4)] y) * pp) * swAt (m + 6) 3 =
      (swAt (m + 6) 3 * pp) * mc (m + 6) .box [t] (ctlX 5 [(1 - t, c), (2, false), (3, y 4)] y) *
        (pp * swAt (m + 6) 3) := by simp only [mul_assoc]
  rw [e4]
  refine (dmul (dmul hc3 (Derivable.refl _)) hc3.symm).trans ?_
  have e5 : pp * swAt (m + 6) 3 *
      mc (m + 6) .box [t] (ctlX 5 [(1 - t, c), (2, false), (3, y 4)] y) *
      (swAt (m + 6) 3 * (pp : Circ (m + 6))) =
      pp * (swAt (m + 6) 3 * mc (m + 6) .box [t] (ctlX 5 [(1 - t, c), (2, false), (3, y 4)] y) *
        swAt (m + 6) 3) * pp := by simp only [mul_assoc]
  rw [e5]
  exact dctx _ _ (conj_back hs h3)

end QCert.RealCliffordCH.Sec8.D.N13
