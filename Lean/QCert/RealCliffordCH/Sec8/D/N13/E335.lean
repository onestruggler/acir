/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (335) from five wires on

Two boxes on wire `0`, every other wire a control (colourings `x`, `y`),
commute.  If `x = y` there is nothing to prove.  Otherwise, by (307) (the
box commutes with the swaps of its controls, `box_swap`), the colourings
may be assumed to differ on wire `2`, black for `x` and white for `y`
(`comm335_ge5`).  Then both boxes are written by (320)/(321) (`expX`, every
colour), and every gate of one expansion commutes with every gate of the
other (`pairs335`): two rotations on the wires `0, …, 3` by a semantic step
without wire `4` (`commRR`), a rotation and a box idle on wire `3` by (318)
and (319) (`commRB`, `commBR`, the latter conjugated by `X` on wire `2`),
two boxes idle on wire `3` by a semantic step without wire `3`
(`Sem.comm_box_idle`).
-/
import QCert.RealCliffordCH.Sec8.D.N13.E320
import QCert.RealCliffordCH.Sec8.D.N13.Sem

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-! ## The expansion at every width, every colour -/

/-- The box on wire `0`, controls `1, 2, 3` and the bulk, on four local wires. -/
def bxC4 (b1 b2 b3 : Bool) : Lt := .g .box [0] [(1, b1), (2, b2), (3, b3)] true
/-- The box of the expansion, on four local wires. -/
def P3' (b1 b2 : Bool) : Lt := .g .box [0] [(1, b1), (2, b2)] true

def pcs4 (b1 b2 b3 : Bool) : List Lt :=
  [P1 b1 b2 b3, P2 b1 b2 b3, P3' b1 b2, P4 b1 b2 b3, P5 b1 b2 b3, P2 b1 b2 b3, P3' b1 b2,
    P4 b1 b2 b3]

theorem pcs4_ok : ∀ b1 b2 b3 : Bool, ∀ g ∈ pcs4 b1 b2 b3, g.ok 4 = true := by decide
theorem bxC4_ok : ∀ b1 b2 b3 : Bool, ∀ g ∈ [bxC4 b1 b2 b3], g.ok 4 = true := by decide

theorem exp4 (m : ℕ) (ih : IH (m + 5)) (b1 b2 b3 : Bool) :
    Derivable (theory (m + 5)) (wc 4 (m + 5) [bxC4 b1 b2 b3]) (wc 4 (m + 5) (pcs4 b1 b2 b3)) := by
  have h := exp320 m ih b1 b2 b3
  have eB : (bxC b1 b2 b3).circ 5 (m + 5) = (bxC4 b1 b2 b3).circ 4 (m + 5) := mc_congr _ _ _ (by ctl_tac)
  have e1 : (P1 b1 b2 b3).circ 5 (m + 5) = (P1 b1 b2 b3).circ 4 (m + 5) := mc_congr _ _ _ (by ctl_tac)
  have e2 : (P2 b1 b2 b3).circ 5 (m + 5) = (P2 b1 b2 b3).circ 4 (m + 5) := mc_congr _ _ _ (by ctl_tac)
  have e3 : (P3 b1 b2).circ 5 (m + 5) = (P3' b1 b2).circ 4 (m + 5) := mc_congr _ _ _ (by ctl_tac)
  have e4 : (P4 b1 b2 b3).circ 5 (m + 5) = (P4 b1 b2 b3).circ 4 (m + 5) := mc_congr _ _ _ (by ctl_tac)
  have e5 : (P5 b1 b2 b3).circ 5 (m + 5) = (P5 b1 b2 b3).circ 4 (m + 5) := mc_congr _ _ _ (by ctl_tac)
  simp only [wc, pcs, List.map_cons, List.map_nil, eB, e1, e2, e3, e4, e5] at h
  simp only [wc, pcs4, List.map_cons, List.map_nil]
  exact h

/-- The coloured box as the product of the eight gates of (320)/(321). -/
theorem expX (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x : ℕ → Bool) :
    Derivable (theory N) (mc N .box [0] (colOn 1 N x)) (wcX 4 N x (pcs4 (x 1) (x 2) (x 3))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
  have h := colour_wc (K := 4) (N := m + 5) (by omega) x (bxC4_ok (x 1) (x 2) (x 3))
    (pcs4_ok (x 1) (x 2) (x 3)) (exp4 m ih (x 1) (x 2) (x 3))
  have e : wcX 4 (m + 5) x [bxC4 (x 1) (x 2) (x 3)] = mc (m + 5) .box [0] (colOn 1 (m + 5) x) := by
    show drawn [mc _ _ _ _] = _
    rw [drawn_one]
    exact mc_congr _ _ _ (by ctl_tac)
  rw [e] at h
  exact h

/-! ## Pairs of gates -/

/-- The rotations of the expansion. -/
def rots (b1 b2 b3 : Bool) : List Lt := [P1 b1 b2 b3, P2 b1 b2 b3, P4 b1 b2 b3, P5 b1 b2 b3]

theorem chkRR : ∀ b1 b3 c1 c3 : Bool, ∀ r ∈ rots b1 true b3, ∀ r' ∈ rots c1 false c3,
    check 4 [] [r, r'] [r', r] [.sem 0 2 [r', r] 4] = true := by
  decide +kernel

theorem rots_rebase {N : ℕ} {b1 b2 b3 : Bool} {r : Lt} (hr : r ∈ rots b1 b2 b3) :
    r.circ 5 N = r.circ 4 N := by
  simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact mc_congr _ _ _ (by ctl_tac)

theorem rots_cX {K N : ℕ} {x : ℕ → Bool} {b1 b2 b3 : Bool} {r : Lt} (hr : r ∈ rots b1 b2 b3) :
    cX K N x r = r.circ K N := by
  simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> rfl

theorem pcs4_cls {b1 b2 b3 : Bool} {g : Lt} (h : g ∈ pcs4 b1 b2 b3) :
    g ∈ rots b1 b2 b3 ∨ g = P3' b1 b2 := by
  simp only [pcs4, rots, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
  rcases h with h | h | h | h | h | h | h | h <;> simp [h]

/-- The box idle on wire `3`, in the conventions of the interface. -/
abbrev boxN (N : ℕ) (z : ℕ → Bool) (c1 c2 : Bool) : Circ N :=
  mc N .box [0] (ctlOr (ctlAt 1 c1) (ctlOr (ctlAt 2 c2) (colOn 4 N z)))

theorem P3'_cX (N : ℕ) (z : ℕ → Bool) (c1 c2 : Bool) : cX 4 N z (P3' c1 c2) = boxN N z c1 c2 :=
  mc_congr _ _ _ (by ctl_tac)

section Pairs

variable (m : ℕ) (ih : IH (m + 5))
include ih

theorem commRR (x y : ℕ → Bool) {r r' : Lt} (hr : r ∈ rots (x 1) true (x 3))
    (hr' : r' ∈ rots (y 1) false (y 3)) : Comm (m + 5) (cX 4 (m + 5) x r) (cX 4 (m + 5) y r') := by
  have h := check_sound (frame 4) ih (allD_nil 5 m) (chkRR (x 1) (x 3) (y 1) (y 3) r hr r' hr')
  rw [rots_cX hr, rots_cX hr']
  unfold Comm
  rw [← rots_rebase (N := m + 5) hr, ← rots_rebase (N := m + 5) hr']
  exact h

/-- A rotation black on wire `2` and a box white on wire `2`: (318), (319). -/
theorem commRB' (b1 b3 c1 : Bool) (z : ℕ → Bool) {r : Lt} (hr : r ∈ rots b1 true b3) :
    Comm (m + 5) (r.circ 4 (m + 5)) (boxN (m + 5) z c1 false) := by
  simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have e : (P1 b1 true b3).circ 4 (m + 5) =
        mc (m + 5) (Kind.sgnZX false) [0] (ctlOr (ctlAt 1 b1) (ctlOr (ctlAt 2 true) (ctlAt 3 b3))) :=
      mc_congr _ _ _ (by ctl_tac)
    rw [e]; exact eq319_ge5 (m + 5) (by omega) ih z false b3 b1 c1
  · have e : (P2 b1 true b3).circ 4 (m + 5) =
        mc (m + 5) (Kind.sgnZX (!b1)) [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 true) (ctlAt 3 b3))) :=
      mc_congr _ _ _ (by ctl_tac)
    rw [e]; exact eq318_ge5 (m + 5) (by omega) ih z (!b1) b3 c1
  · have e : (P4 b1 true b3).circ 4 (m + 5) =
        mc (m + 5) (Kind.sgnZX b1) [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 true) (ctlAt 3 b3))) :=
      mc_congr _ _ _ (by ctl_tac)
    rw [e]; exact eq318_ge5 (m + 5) (by omega) ih z b1 b3 c1
  · have e : (P5 b1 true b3).circ 4 (m + 5) =
        mc (m + 5) (Kind.sgnZX true) [0] (ctlOr (ctlAt 1 b1) (ctlOr (ctlAt 2 true) (ctlAt 3 b3))) :=
      mc_congr _ _ _ (by ctl_tac)
    rw [e]; exact eq319_ge5 (m + 5) (by omega) ih z true b3 b1 c1

theorem commRB (x y : ℕ → Bool) {r : Lt} (hr : r ∈ rots (x 1) true (x 3)) :
    Comm (m + 5) (cX 4 (m + 5) x r) (cX 4 (m + 5) y (P3' (y 1) false)) := by
  rw [rots_cX hr, P3'_cX]
  exact commRB' m ih (x 1) (x 3) (y 1) y hr

/-- `X` on wire `2` exchanges the colours of the box there. -/
theorem flipBox (z : ℕ → Bool) (c1 : Bool) :
    Derivable (theory (m + 5)) (xAt (m + 5) 2 * boxN (m + 5) z c1 false * xAt (m + 5) 2)
      (boxN (m + 5) z c1 true) := by
  have h := eq81 (m + 5) .box [0] (ctlOr (ctlAt 1 c1) (ctlOr (ctlAt 2 false) (colOn 4 (m + 5) z)))
    2 false (by omega) (by decide) (by simp [ctlOr, ctlAt, colOn])
  have e : drawn [xAt (m + 5) 2, boxN (m + 5) z c1 false, xAt (m + 5) 2] =
      xAt (m + 5) 2 * boxN (m + 5) z c1 false * xAt (m + 5) 2 := by simp [drawn, mul_assoc]
  rw [e] at h
  exact h.trans (der_of_eq (mc_congr _ _ _ (by ctl_tac)))

theorem commBR (x y : ℕ → Bool) {r' : Lt} (hr' : r' ∈ rots (y 1) false (y 3)) :
    Comm (m + 5) (cX 4 (m + 5) x (P3' (x 1) true)) (cX 4 (m + 5) y r') := by
  rw [rots_cX hr', P3'_cX]
  refine Derivable.symm ?_
  have hx := xAt_inv (m + 5) 2 (by omega)
  simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl
  · exact comm_flip (commRB' m ih (y 1) (y 3) (x 1) x (r := P1 (y 1) true (y 3)) (by simp [rots])) hx
      (flip81 .zx [0] _ _ false 2 true (by omega) (by decide) rfl (by ctl_tac)) (flipBox m ih x _)
  · exact comm_flip (commRB' m ih (y 1) (y 3) (x 1) x (r := P2 (y 1) true (y 3)) (by simp [rots])) hx
      (flip81 _ [1] _ _ false 2 true (by omega) (by decide) rfl (by ctl_tac)) (flipBox m ih x _)
  · exact comm_flip (commRB' m ih (y 1) (y 3) (x 1) x (r := P4 (y 1) true (y 3)) (by simp [rots])) hx
      (flip81 _ [1] _ _ false 2 true (by omega) (by decide) rfl (by ctl_tac)) (flipBox m ih x _)
  · exact comm_flip (commRB' m ih (y 1) (y 3) (x 1) x (r := P5 (y 1) true (y 3)) (by simp [rots])) hx
      (flip81 .xz [0] _ _ false 2 true (by omega) (by decide) rfl (by ctl_tac)) (flipBox m ih x _)

theorem commBB (x y : ℕ → Bool) :
    Comm (m + 5) (cX 4 (m + 5) x (P3' (x 1) true)) (cX 4 (m + 5) y (P3' (y 1) false)) := by
  show Comm (m + 4 + 1) (mc _ .box [0] _) (mc _ .box [0] _)
  exact comm_box_idle (q := 3) ih _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp [ctlX]) (by simp [ctlX])

/-- Every gate of one expansion commutes with every gate of the other. -/
theorem pairs335 (x y : ℕ → Bool) :
    ∀ a ∈ (pcs4 (x 1) true (x 3)).map (cX 4 (m + 5) x),
      ∀ b ∈ (pcs4 (y 1) false (y 3)).map (cX 4 (m + 5) y), Comm (m + 5) a b := by
  intro a ha b hb
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hb
  rcases pcs4_cls hg with hr | rfl <;> rcases pcs4_cls hg' with hr' | rfl
  · exact commRR m ih x y hr hr'
  · exact commRB m ih x y hr
  · exact commBR m ih x y hr'
  · exact commBB m ih x y

end Pairs

/-- (335) when the colourings are black, resp. white, on wire `2`. -/
theorem comm335_core (m : ℕ) (ih : IH (m + 5)) (x y : ℕ → Bool) (hx : x 2 = true)
    (hy : y 2 = false) :
    Comm (m + 5) (mc (m + 5) .box [0] (colOn 1 (m + 5) x)) (mc (m + 5) .box [0] (colOn 1 (m + 5) y)) := by
  have ex := expX (m + 5) (by omega) ih x
  have ey := expX (m + 5) (by omega) ih y
  rw [hx] at ex
  rw [hy] at ey
  exact Comm.congr ex.symm ey.symm (comm_drawn _ _ (pairs335 m ih x y))

/-! ## The relabeling -/

/-- (307): the swap of two controls relabels the box. -/
theorem box_swap (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x : ℕ → Bool) (j : ℕ) (hj : 1 ≤ j)
    (hjN : j + 2 ≤ N) :
    Derivable (theory N) (swAt N j * mc N .box [0] (colOn 1 N x) * swAt N j)
      (mc N .box [0] (colOn 1 N (x ∘ Net.tau j))) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have hsym : CanonSym .box (ctrlWires (k + 1) [0] (colOn 1 (k + 1) x)).length := by
    have e := ctrlWires_full k 1 (colOn 1 (k + 1) x) (fun i => by
      simp only [colOn]; split_ifs with h <;> simp [h] <;> omega)
    rw [show ([0] : List ℕ) = List.range 1 from rfl, e, List.length_range']
    exact canonSym_box k (fun j hj hj2 => eq307 (k + 1) (by omega) ih j hj hj2)
  have h := mc_swap_sym (k + 1) j hjN .box [0] (colOn 1 (k + 1) x) rfl (by simp) (by simp)
    hsym
  have e1 : ([0] : List ℕ).map (Net.tau j) = [0] := by
    rw [List.map_singleton, Net.tau_of_lt (by omega : 0 < j)]
  rw [e1] at h
  have e2 : drawn [swAt (k + 1) j, mc (k + 1) .box [0] (colOn 1 (k + 1) x), swAt (k + 1) j] =
      swAt (k + 1) j * mc (k + 1) .box [0] (colOn 1 (k + 1) x) * swAt (k + 1) j := by
    simp [drawn, mul_assoc]
  rw [e2] at h
  refine h.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
  simp only [Function.comp, colOn, Net.tau]
  split_ifs <;> first | rfl | omega | (simp_all; done) | (exfalso; omega) | simp_all

/-- (335) from five wires on. -/
theorem comm335_ge5 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x y : ℕ → Bool) :
    Comm N (mc N .box [0] (colOn 1 N x)) (mc N .box [0] (colOn 1 N y)) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
  have sw : ∀ (x y : ℕ → Bool) (j : ℕ), 1 ≤ j → j + 2 ≤ m + 5 →
      Comm (m + 5) (mc (m + 5) .box [0] (colOn 1 (m + 5) (x ∘ Net.tau j)))
        (mc (m + 5) .box [0] (colOn 1 (m + 5) (y ∘ Net.tau j))) →
      Comm (m + 5) (mc (m + 5) .box [0] (colOn 1 (m + 5) x))
        (mc (m + 5) .box [0] (colOn 1 (m + 5) y)) := by
    intro x y j hj hjN h
    have hs := swsw (m + 5) j hjN
    have bx := box_swap (m + 5) (by omega) ih (x ∘ Net.tau j) j hj hjN
    have by' := box_swap (m + 5) (by omega) ih (y ∘ Net.tau j) j hj hjN
    have tt : ∀ z : ℕ → Bool, (z ∘ Net.tau j) ∘ Net.tau j = z := fun z => by
      funext i; simp [Function.comp, Net.tau_tau]
    rw [tt] at bx by'
    exact Comm.congr bx by' (Comm.conj h hs)
  have at2 : ∀ x y : ℕ → Bool, x 2 ≠ y 2 →
      Comm (m + 5) (mc (m + 5) .box [0] (colOn 1 (m + 5) x))
        (mc (m + 5) .box [0] (colOn 1 (m + 5) y)) := by
    intro x y hxy
    cases hx : x 2 <;> cases hy : y 2 <;> rw [hx, hy] at hxy
    · exact absurd rfl hxy
    · exact Derivable.symm (comm335_core m ih y x hy hx)
    · exact comm335_core m ih x y hx hy
    · exact absurd rfl hxy
  have up : ∀ q, 2 ≤ q → q < m + 5 → ∀ x y : ℕ → Bool, x q ≠ y q →
      Comm (m + 5) (mc (m + 5) .box [0] (colOn 1 (m + 5) x))
        (mc (m + 5) .box [0] (colOn 1 (m + 5) y)) := by
    intro q hq2 hqN
    induction q, hq2 using Nat.le_induction with
    | base => exact at2
    | succ q hq ihq =>
      intro x y hxy
      refine sw x y q (by omega) (by omega) (ihq (by omega) _ _ ?_)
      show x (Net.tau q q) ≠ y (Net.tau q q)
      rw [show Net.tau q q = q + 1 by simp [Net.tau]]
      exact hxy
  by_cases hall : ∀ i, 1 ≤ i → i < m + 5 → x i = y i
  · have e : mc (m + 5) .box [0] (colOn 1 (m + 5) x) = mc (m + 5) .box [0] (colOn 1 (m + 5) y) :=
      mc_congr _ _ _ (fun i hi => by
        simp only [colOn]; split_ifs with h
        · rw [hall i h.1 h.2]
        · rfl)
    rw [e]
    exact Derivable.refl _
  · push_neg at hall
    obtain ⟨q, hq1, hqN, hxy⟩ := hall
    rcases (by omega : q = 1 ∨ 2 ≤ q) with rfl | hq2
    · refine sw x y 1 le_rfl (by omega) (at2 _ _ ?_)
      show x (Net.tau 1 2) ≠ y (Net.tau 1 2)
      rw [show Net.tau 1 2 = 1 from rfl]
      exact hxy
    · exact up q hq2 hqN x y hxy

end QCert.RealCliffordCH.Sec8.D.N13
