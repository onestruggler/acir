/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (339) from six wires on, by semantic separation

Work in progress (nothing imports it).  The frame is `E339a`'s; see the
third-session section of `HANDOVER.md` for the plan.  Here: the
conjugating word `uL … uL'` of the inner box of `B` (`M` followed by the
swap of the wires `1, 2`), its inverse at every width (`inv_of_lcheck`: a
four-wire decision lifted through the block form), and two of the four
kinds of pairs, by `Sep` with no simulation in the kernel:
* `commRR_s`: a rotation of `A` (conjugated by the swap of the wires
  `3, 4`) against a conjugated rotation of `B`, on the five wires `0–4`
  (completeness there; six wires at least);
* `commAr_s`: the remainder `Ar` of `A` (idle on wire `4`) against a
  conjugated rotation of `B`, a semantic step without wire `4`.

Memory (2026-10-29): 24 s, peak 1.5 GB anonymous (4.3 GB resident with the
mapped imports).
-/
import QCert.RealCliffordCH.Sec8.D.N13.E339a
import QCert.RealCliffordCH.Sec8.D.N13.SepSem

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8 Sep

/-- The word conjugating the inner box of `B`: `uL` is applied first. -/
def uL : List Lt := mL' ++ [.s (.S 1)]
def uL' : List Lt := [.s (.S 1)] ++ mL

theorem rt_uL : rtW uL 2 = some 2 := by decide
theorem rt_uL' : rtW uL' 2 = some 2 := by decide
theorem rt_s3 : rtW [.s (.S 3)] 2 = some 2 := by decide

theorem uL_ok : (∀ x ∈ uL, x.ok 4 = true) ∧ (∀ x ∈ uL', x.ok 4 = true) := by decide

theorem chkU_on : SE.lcheck 4 true (uL ++ uL') [] = true := by decide +kernel
theorem chkU_off : SE.lcheck 4 false (uL ++ uL') [] = true := by decide +kernel
theorem chkS3_on : SE.lcheck 5 true [.s (.S 3), .s (.S 3)] [] = true := by decide +kernel
theorem chkS3_off : SE.lcheck 5 false [.s (.S 3), .s (.S 3)] [] = true := by decide +kernel

/-- A word whose two block readings are the identity (decided on `K` wires)
is the identity at every width. -/
theorem inv_of_lcheck {K : ℕ} {l : List Lt} (hok : ∀ x ∈ l, x.ok K = true)
    (hon : SE.lcheck K true l [] = true) (hoff : SE.lcheck K false l [] = true) :
    ∀ N, K ≤ N → opsQ.eval N (wc K N l) = 1 := by
  intro N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + K := ⟨N - K, by omega⟩
  have e1 := SE.lcheck_sound true hok (by simp) hon
  have e2 := SE.lcheck_sound false hok (by simp) hoff
  rw [SE.circWL_true] at e1
  rw [SE.circWL_false] at e2
  have e0 := eval_wc_blk (m := n) (K := K) [] (by simp)
  rw [eval_wc_blk (m := n) (K := K) l hok, e1, e2]
  simpa [wc, drawn] using e0.symm

/-- A small letter. -/
def isSmall : Lt → Bool
  | .s _ => true
  | .g _ _ _ _ => false

theorem wc_small (K K' N : ℕ) (l : List Lt) (h : l.all isSmall = true) :
    wc K N l = wc K' N l := by
  unfold wc
  congr 1
  refine List.map_congr_left fun x hx => ?_
  have := List.all_eq_true.1 h x hx
  cases x with
  | s y => rfl
  | g _ _ _ _ => simp [isSmall] at this

theorem uL_small : uL.all isSmall = true ∧ uL'.all isSmall = true := by decide

/-- `uL'` undoes `uL`, in the semantics, at every width from five, with the
letters read on five local wires. -/
theorem uL_inv (N : ℕ) (hN : 5 ≤ N) :
    opsQ.eval N (wc 5 N uL') * opsQ.eval N (wc 5 N uL) = 1 := by
  have h := inv_of_lcheck (K := 4) (l := uL ++ uL') (fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact uL_ok.1 x hx
      · exact uL_ok.2 x hx) chkU_on chkU_off N (by omega)
  rw [wc_append, map_mul] at h
  rwa [wc_small 4 5 N uL uL_small.1, wc_small 4 5 N uL' uL_small.2] at h

theorem s3_inv (N : ℕ) (hN : 5 ≤ N) :
    opsQ.eval N (wc 5 N [.s (.S 3)]) * opsQ.eval N (wc 5 N [.s (.S 3)]) = 1 := by
  have h := inv_of_lcheck (K := 5) (l := [.s (.S 3), .s (.S 3)]) (by decide) chkS3_on chkS3_off
    N hN
  rw [show ([.s (.S 3), .s (.S 3)] : List Lt) = [.s (.S 3)] ++ [.s (.S 3)] from rfl, wc_append,
    map_mul] at h
  exact h

/-- The rotations of the expansion, read on five local wires: trivial where
their control on wire `2` does not match. -/
theorem triv_rots (N : ℕ) (hN : 5 ≤ N) : ∀ b1 b2 b3 : Bool, ∀ r ∈ rots b1 b2 b3,
    Triv 2 (if b2 then 0 else 1) (opsQ.eval N (r.circ 5 N)) := by
  intro b1 b2 b3 r hr
  have hok : r.ok 5 = true := by
    simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> cases b1 <;> rfl
  obtain ⟨Kd, tg, cs, bb, rfl, hl, ht⟩ : ∃ Kd tg cs bb, r = Lt.g Kd tg cs bb ∧
      cs.lookup 2 = some b2 ∧ 2 ∉ tg := by
    simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, _, rfl, rfl, by decide⟩
  exact triv_g (K := 5) hN Kd tg cs bb hok (by omega) ht hl

/-! ## Rotation against conjugated rotation -/

theorem wc_three' (K N : ℕ) (a b c : Lt) :
    wc K N [a, b, c] = wc K N [c] * b.circ K N * wc K N [a] := by
  simp [wc, drawn, mul_assoc]

theorem wc_conj (K N : ℕ) (u u' : List Lt) (h : Lt) :
    wc K N (u ++ [h] ++ u') = wc K N u' * h.circ K N * wc K N u := by
  rw [wc_append, wc_append]
  simp [wc, drawn, mul_assoc]

/-- A rotation black on wire `2` (`rots _ true _`), conjugated by the swap of
the wires `3, 4`: trivial where wire `2` is `0`. -/
theorem triv_s3r (n : ℕ) {b1 b3 : Bool} {r : Lt} (hr : r ∈ rots b1 true b3) :
    Triv 2 0 (opsQ.eval (n + 5) (wc 5 (n + 5) [.s (.S 3), r, .s (.S 3)])) := by
  rw [wc_three']
  have hx : Triv 2 0 (opsQ.eval (n + 5) (r.circ 5 (n + 5))) := by
    simpa using triv_rots (n + 5) (by omega) b1 true b3 r hr
  exact triv_conj (K := 5) (by omega) (by decide) (by decide) (by omega) (by omega) rt_s3 rt_s3
    (s3_inv (n + 5) (by omega)) hx

/-- A rotation white on wire `2`, conjugated by `uL … uL'`: trivial where
wire `2` is `1`. -/
theorem uL_ok5 : (∀ x ∈ uL, x.ok 5 = true) ∧ (∀ x ∈ uL', x.ok 5 = true) := by decide

/-- A rotation white on wire `2`, conjugated by `uL … uL'`: trivial where
wire `2` is `1`. -/
theorem triv_uh (n : ℕ) {c1 c3 : Bool} {h : Lt} (hh : h ∈ rots c1 false c3) :
    Triv 2 1 (opsQ.eval (n + 5) (wc 5 (n + 5) (uL ++ [h] ++ uL'))) := by
  rw [wc_conj]
  have hx : Triv 2 1 (opsQ.eval (n + 5) (h.circ 5 (n + 5))) := by
    simpa using triv_rots (n + 5) (by omega) c1 false c3 h hh
  have hinv := uL_inv (n + 5) (by omega)
  exact triv_conj (K := 5) (by omega) uL_ok5.1 uL_ok5.2 (by omega) (by omega) rt_uL rt_uL'
    hinv hx

theorem rots_loc5 : ∀ b1 b2 b3 : Bool, ∀ r ∈ rots b1 b2 b3, isLoc 5 r = true := by decide
theorem uL_loc5 : uL.all (isLoc 5) = true ∧ uL'.all (isLoc 5) = true := by decide

/-- A rotation of `A` (black on wire `2`, conjugated by the swap of the wires
`3, 4`) passes a conjugated rotation of `B` (white on wire `2`): the two words
live on the wires `0–4`, so completeness on five wires applies. -/
theorem commRR_s (m : ℕ) (ih : IH (m + 6)) {b1 b3 c1 c3 : Bool} {r h : Lt}
    (hr : r ∈ rots b1 true b3) (hh : h ∈ rots c1 false c3) :
    Derivable (theory (m + 6)) (wc 5 (m + 6) ([.s (.S 3), r, .s (.S 3)] ++ (uL ++ [h] ++ uL')))
      (wc 5 (m + 6) ((uL ++ [h] ++ uL') ++ [.s (.S 3), r, .s (.S 3)])) := by
  have hs := sep_sem (K := 5) (M := 0 + 5) (p := 2) (by decide : (0 : Fin 2) ≠ 1)
    (triv_s3r 0 hr) (triv_uh 0 hh)
  have d5 := ih 5 (by omega) _ _ hs
  have lr := rots_loc5 _ _ _ r hr
  have lh := rots_loc5 _ _ _ h hh
  have lu := uL_loc5
  have l1 : ([.s (.S 3), r, .s (.S 3)] ++ (uL ++ [h] ++ uL')).all (isLoc 5) = true := by
    simp only [List.all_append, List.all_cons, List.all_nil, lr, lh, lu.1, lu.2]; decide
  have l2 : ((uL ++ [h] ++ uL') ++ [.s (.S 3), r, .s (.S 3)]).all (isLoc 5) = true := by
    simp only [List.all_append, List.all_cons, List.all_nil, lr, lh, lu.1, lu.2]; decide
  exact der_loc l1 l2 d5 (m + 6) (by omega)

/-! ## The remainder of `A` against a conjugated rotation of `B` -/

/-- The remainder of `A`'s expansion with the triple `1, 2, 4`: the box on
wire `0`, controls `1` (`c₂`), `2` (black), `3` (`c₁`), the bulk above `4`;
idle on wire `4`. -/
def Ar (c₁ c₂ : Bool) : Lt := .g .box [0] [(1, c₂), (2, true), (3, c₁)] true

theorem uL_inv4 (N : ℕ) (hN : 4 ≤ N) :
    opsQ.eval N (wc 4 N uL') * opsQ.eval N (wc 4 N uL) = 1 := by
  have h := inv_of_lcheck (K := 4) (l := uL ++ uL') (fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact uL_ok.1 x hx
      · exact uL_ok.2 x hx) chkU_on chkU_off N hN
  rwa [wc_append, map_mul] at h

theorem rots_drop4 : ∀ b1 b2 b3 : Bool, ∀ r ∈ rots b1 b2 b3,
    r.ok 5 = true ∧ r.avoids 4 = true ∧ r.drop 4 = r := by decide
theorem uL_drop4 : (uL ++ uL').all (fun x => x.ok 5 && x.avoids 4 && x.drop 4 == x) = true := by
  decide
theorem Ar_drop4 : ∀ c₁ c₂ : Bool,
    (Ar c₁ c₂).ok 5 = true ∧ (Ar c₁ c₂).avoids 4 = true ∧ (Ar c₁ c₂).drop 4 = Ar c₁ c₂ := by
  decide

/-- `Ar` passes a rotation of `B` conjugated by `uL … uL'`: both avoid wire
`4`, and they are separated on wire `2`. -/
theorem commAr_s (m : ℕ) (ih : IH (m + 6)) (c₁ c₂ : Bool) {c1 c3 : Bool} {h : Lt}
    (hh : h ∈ rots c1 false c3) :
    Derivable (theory (m + 6)) (wc 5 (m + 6) ([Ar c₁ c₂] ++ (uL ++ [h] ++ uL')))
      (wc 5 (m + 6) ((uL ++ [h] ++ uL') ++ [Ar c₁ c₂])) := by
  have hr := rots_drop4 _ _ _ h hh
  have hu := List.all_eq_true.1 uL_drop4
  have hA := Ar_drop4 c₁ c₂
  have mem : ∀ x ∈ [Ar c₁ c₂] ++ (uL ++ [h] ++ uL'),
      x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := by
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with rfl | (hx | rfl) | hx
    · exact hA
    · have := hu x (List.mem_append_left _ hx)
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    · exact hr
    · have := hu x (List.mem_append_right _ hx)
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
  have mem' : ∀ x ∈ (uL ++ [h] ++ uL') ++ [Ar c₁ c₂],
      x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := fun x hx =>
    mem x (by simp only [List.mem_append] at hx ⊢; tauto)
  have e1 : ([Ar c₁ c₂] ++ (uL ++ [h] ++ uL')).map (Lt.drop 4) =
      [Ar c₁ c₂] ++ (uL ++ [h] ++ uL') := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem x hx).2.2), List.map_id]
  have e2 : ((uL ++ [h] ++ uL') ++ [Ar c₁ c₂]).map (Lt.drop 4) =
      (uL ++ [h] ++ uL') ++ [Ar c₁ c₂] := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem' x hx).2.2), List.map_id]
  have tA : Triv 2 0 (opsQ.eval (m + 1 + 4) (wc 4 (m + 1 + 4) [Ar c₁ c₂])) := by
    have := triv_g (K := 4) (N := m + 1 + 4) (by omega) .box [0] [(1, c₂), (2, true), (3, c₁)] true
      rfl (p := 2) (by omega) (by decide) (b := true) rfl
    simpa [wc, drawn, Ar] using this
  have tB : Triv 2 1 (opsQ.eval (m + 1 + 4) (wc 4 (m + 1 + 4) (uL ++ [h] ++ uL'))) := by
    rw [wc_conj]
    have hx : Triv 2 1 (opsQ.eval (m + 1 + 4) (h.circ 4 (m + 1 + 4))) := by
      rw [← rots_rebase hh]
      simpa using triv_rots (m + 1 + 4) (by omega) c1 false c3 h hh
    exact triv_conj (K := 4) (by omega) uL_ok.1 uL_ok.2 (by omega) (by omega) rt_uL rt_uL'
      (uL_inv4 (m + 1 + 4) (by omega)) hx
  have hsem := sep_sem (K := 4) (M := m + 1 + 4) (by decide : (0 : Fin 2) ≠ 1) tA tB
  rw [← e1, ← e2] at hsem
  exact SE.Frame.window (frame 4) (m + 1) ih (q := 4) le_rfl
    (fun x hx => ⟨(mem x hx).1, (mem x hx).2.1⟩) (fun x hx => ⟨(mem' x hx).1, (mem' x hx).2.1⟩)
    hsem

end QCert.RealCliffordCH.Sec8.D.N13
