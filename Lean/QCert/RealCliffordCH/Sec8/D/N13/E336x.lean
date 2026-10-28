/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (336) from five wires on

The box on wire `0` (control `c₁` on wire `1`, the wires `2, …` coloured by
`x`) and the box on wire `1` (control `c₂` on wire `0`, coloured by `y`)
commute.  Equal colourings are `E336`.  Otherwise, by (307) (`box_swap`
generalized, `relabel`), the colourings may be assumed to differ on wire
`2`, and by (81) to be black there for `x`, white for `y`.  Then both boxes
are written by (320)/(321) (`expX`; the second conjugated by the swap of the
wires `0, 1`), and every gate of one expansion commutes with every gate of
the other: two rotations by a semantic step without wire `4`, a rotation and
a box idle on wire `3` by (318) and (319) on either box wire (`E318g`), two
boxes idle on wire `3` by a semantic step without wire `3`.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E336
import QCert.RealCliffordCH.Sec8.D.N13.E340
import QCert.RealCliffordCH.Sec8.D.N13.E318g

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-! ## Products and conjugation -/

/-- Conjugating every factor of a product by an invertible `u`. -/
theorem conj_drawn {N : ℕ} {u v : Circ N} (h1 : Derivable (theory N) (v * u) 1)
    (h2 : Derivable (theory N) (u * v) 1) : ∀ l : List (Circ N),
    Derivable (theory N) (u * drawn l * v) (drawn (l.map fun a => u * a * v))
  | [] => by simpa [drawn] using h2
  | a :: l => by
    rw [Net.drawn_cons, List.map_cons, Net.drawn_cons]
    have ih := conj_drawn h1 h2 l
    have e : u * (drawn l * a) * v = u * drawn l * 1 * (a * v) := by simp only [mul_one, mul_assoc]
    rw [e]
    refine (dctx _ _ h1.symm).trans ?_
    have e2 : u * drawn l * (v * u) * (a * v) = (u * drawn l * v) * (u * a * v) := by
      simp only [mul_assoc]
    rw [e2]
    exact dmul ih (Derivable.refl _)

theorem drawn_map_comp {N : ℕ} {α : Type*} (f : α → Circ N) (g : Circ N → Circ N) (l : List α) :
    drawn ((l.map f).map g) = drawn (l.map (g ∘ f)) := by rw [List.map_map]

/-! ## Relabeling by a swap of two controls -/

/-- (307): a box with a control on every wire but its box wire, conjugated by
the swap of two of its controls. -/
theorem box_relabel (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (t : ℕ) (ht : t < N) (c : ℕ → Option Bool)
    (hc : ∀ i < N, i ≠ t → (c i).isSome = true) (j : ℕ) (hjN : j + 2 ≤ N) (htj : t ≠ j)
    (htj' : t ≠ j + 1) :
    Derivable (theory N) (swAt N j * mc N .box [t] c * swAt N j) (mc N .box [t] (c ∘ Net.tau j)) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have hlen : (ctrlWires (k + 1) [t] c).length = k := by
    have : ctrlWires (k + 1) [t] c = (List.range (k + 1)).erase t := by
      rw [List.Nodup.erase_eq_filter List.nodup_range]
      unfold ctrlWires
      refine List.filter_congr (fun i hi => ?_)
      rw [List.mem_range] at hi
      by_cases hit : i = t
      · subst hit; simp
      · simp [hc i hi hit, hit]
    rw [this, List.length_erase_of_mem (List.mem_range.2 ht), List.length_range]; rfl
  have hsym : CanonSym .box (ctrlWires (k + 1) [t] c).length := by
    rw [hlen]
    exact canonSym_box k (fun j hj hj2 => eq307 (k + 1) (by omega) ih j hj hj2)
  have h := mc_swap_sym (k + 1) j hjN .box [t] c rfl (by simp) (by simpa using ht) hsym
  have e1 : ([t] : List ℕ).map (Net.tau j) = [t] := by
    rw [List.map_singleton]; congr 1; unfold Net.tau; split_ifs <;> omega
  rw [e1] at h
  have e2 : drawn [swAt (k + 1) j, mc (k + 1) .box [t] c, swAt (k + 1) j] =
      swAt (k + 1) j * mc (k + 1) .box [t] c * swAt (k + 1) j := by simp [drawn, mul_assoc]
  rwa [e2] at h

/-! ## Moving the first difference to a given wire -/

/-- `x` with the colour of wire `lo` exchanged. -/
def flipAt (lo : ℕ) (x : ℕ → Bool) : ℕ → Bool := fun i => if i = lo then !x i else x i

/-- A property of pairs of colourings that is invariant under the swaps of
adjacent wires `≥ lo` and under exchanging both colours of wire `lo` holds
for every pair that differs on the wires `lo, …, N - 1`, once it holds when
they differ on wire `lo`, black for the first. -/
theorem sep_reduce {N lo : ℕ} (P : (ℕ → Bool) → (ℕ → Bool) → Prop)
    (hswap : ∀ x y j, lo ≤ j → j + 2 ≤ N → P (x ∘ Net.tau j) (y ∘ Net.tau j) → P x y)
    (hflip : ∀ x y, P (flipAt lo x) (flipAt lo y) → P x y)
    (hcore : ∀ x y, x lo = true → y lo = false → P x y) :
    ∀ x y, DiffOn lo N x y → P x y := by
  have base : ∀ x y, x lo ≠ y lo → P x y := by
    intro x y hxy
    cases hx : x lo <;> cases hy : y lo <;> rw [hx, hy] at hxy
    · exact absurd rfl hxy
    · refine hflip x y (hcore _ _ ?_ ?_) <;> simp [flipAt, hx, hy]
    · exact hcore x y hx hy
    · exact absurd rfl hxy
  have up : ∀ q, lo ≤ q → q < N → ∀ x y, x q ≠ y q → P x y := by
    intro q hq hqN
    induction q, hq using Nat.le_induction with
    | base => exact base
    | succ q hq ihq =>
      intro x y hxy
      refine hswap x y q hq (by omega) (ihq (by omega) _ _ ?_)
      show x (Net.tau q q) ≠ y (Net.tau q q)
      rw [show Net.tau q q = q + 1 by simp [Net.tau]]
      exact hxy
  rintro x y ⟨q, hq, hqN, hxy⟩
  exact up q hq hqN x y hxy

/-! ## The rotations of the expansion as gates -/

theorem P1_circ (N : ℕ) (b1 b2 b3 : Bool) : (P1 b1 b2 b3).circ 4 N =
    mc N (Kind.sgnZX false) [0] (ctlOr (ctlAt 1 b1) (ctlOr (ctlAt 2 b2) (ctlAt 3 b3))) :=
  mc_congr _ _ _ (by ctl_tac)
theorem P2_circ (N : ℕ) (b1 b2 b3 : Bool) : (P2 b1 b2 b3).circ 4 N =
    mc N (Kind.sgnZX (!b1)) [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 b2) (ctlAt 3 b3))) :=
  mc_congr _ _ _ (by ctl_tac)
theorem P4_circ (N : ℕ) (b1 b2 b3 : Bool) : (P4 b1 b2 b3).circ 4 N =
    mc N (Kind.sgnZX b1) [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 b2) (ctlAt 3 b3))) :=
  mc_congr _ _ _ (by ctl_tac)
theorem P5_circ (N : ℕ) (b1 b2 b3 : Bool) : (P5 b1 b2 b3).circ 4 N =
    mc N (Kind.sgnZX true) [0] (ctlOr (ctlAt 1 b1) (ctlOr (ctlAt 2 b2) (ctlAt 3 b3))) :=
  mc_congr _ _ _ (by ctl_tac)

/-- The swap of the wires `0, 1` on a rotation of the expansion. -/
theorem s0_rot (N : ℕ) (hN : 3 ≤ N) (a : Bool) (t : ℕ) (ht : t ≤ 1) (c c' : ℕ → Option Bool)
    (hc : ∀ i < N, c (Net.tau 0 i) = c' i) :
    Derivable (theory N) (swAt N 0 * mc N (Kind.sgnZX a) [t] c * swAt N 0)
      (mc N (Kind.sgnZX a) [Net.tau 0 t] c') :=
  mc_s0 N hN _ t ht c c' (by cases a <;> decide) hc

/-! ## Pairs of gates of the two expansions -/

/-- Pointwise equality of control functions built with `ctlAt`, `ctlOr`, `colOn`, `setCtl`. -/
macro "ctl_eq" : tactic => `(tactic| (intro i hi; rcases i with _ | _ | _ | _ | _ | _ | i <;>
  (simp only [ctl, ctlX, ctlOr, ctlAt, blackOn, colOn, setCtl, Net.tau]) <;> (try split_ifs) <;>
  first | rfl | (exfalso; omega) | simp | omega | simp_all))

/-- `X` on wire `2` exchanges the colour of a black control there. -/
theorem flip2 (N : ℕ) (hN : 3 ≤ N) (K : Kind) (tg : List ℕ) (c c' : ℕ → Option Bool)
    (hjt : 2 ∉ tg) (hc : c 2 = some true) (h' : ∀ i < N, setCtl c 2 (some false) i = c' i) :
    Derivable (theory N) (xAt N 2 * mc N K tg c * xAt N 2) (mc N K tg c') := by
  have h := eq81 N K tg c 2 true (by omega) hjt hc
  rw [show drawn [xAt N 2, mc N K tg c, xAt N 2] = xAt N 2 * mc N K tg c * xAt N 2 by
    simp [drawn, mul_assoc]] at h
  exact h.trans (der_of_eq (mc_congr _ _ _ h'))

/-- The rotations of the expansion with the wires `0, 1` exchanged. -/
def srots (b1 b2 b3 : Bool) : List Lt :=
  [.g .zx [1] [(0, b1), (2, b2), (3, b3)] false,
   .g (Kind.sgnZX (!b1)) [0] [(1, true), (2, b2), (3, b3)] false,
   .g (Kind.sgnZX b1) [0] [(1, true), (2, b2), (3, b3)] false,
   .g .xz [1] [(0, b1), (2, b2), (3, b3)] false]

theorem srots_rebase {N : ℕ} {b1 b2 b3 : Bool} {r : Lt} (hr : r ∈ srots b1 b2 b3) :
    r.circ 5 N = r.circ 4 N := by
  simp only [srots, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact mc_congr _ _ _ (by ctl_tac)

theorem s0_rots (N : ℕ) (hN : 3 ≤ N) {b1 b2 b3 : Bool} {r : Lt} (hr : r ∈ rots b1 b2 b3) :
    ∃ r'' ∈ srots b1 b2 b3,
      Derivable (theory N) (swAt N 0 * r.circ 4 N * swAt N 0) (r''.circ 4 N) := by
  simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨.g .zx [1] [(0, b1), (2, b2), (3, b3)] false, by simp [srots], ?_⟩
    rw [P1_circ]; exact s0_rot N hN false 0 (by omega) _ _ (by ctl_eq)
  · refine ⟨.g (Kind.sgnZX (!b1)) [0] [(1, true), (2, b2), (3, b3)] false, by simp [srots], ?_⟩
    rw [P2_circ]; exact s0_rot N hN (!b1) 1 le_rfl _ _ (by ctl_eq)
  · refine ⟨.g (Kind.sgnZX b1) [0] [(1, true), (2, b2), (3, b3)] false, by simp [srots], ?_⟩
    rw [P4_circ]; exact s0_rot N hN b1 1 le_rfl _ _ (by ctl_eq)
  · refine ⟨.g .xz [1] [(0, b1), (2, b2), (3, b3)] false, by simp [srots], ?_⟩
    rw [P5_circ]; exact s0_rot N hN true 0 (by omega) _ _ (by ctl_eq)

theorem chkRR2 : ∀ b1 b3 c1 c3 : Bool, ∀ r ∈ rots b1 true b3, ∀ r' ∈ srots c1 false c3,
    check 4 [] [r, r'] [r', r] [.sem 0 2 [r', r] 4] = true := by
  decide +kernel

section Pairs

variable (m : ℕ) (ih : IH (m + 5))
include ih

theorem commRRs (b1 b3 c1 c3 : Bool) {r r' : Lt} (hr : r ∈ rots b1 true b3)
    (hr' : r' ∈ rots c1 false c3) :
    Comm (m + 5) (r.circ 4 (m + 5)) (swAt (m + 5) 0 * r'.circ 4 (m + 5) * swAt (m + 5) 0) := by
  obtain ⟨r'', hr'', hs⟩ := s0_rots (m + 5) (by omega) hr'
  have h := check_sound (frame 4) ih (allD_nil 5 m) (chkRR2 b1 b3 c1 c3 r hr r'' hr'')
  rw [wc_two, wc_two, rots_rebase hr, srots_rebase hr''] at h
  exact Comm.congr (Derivable.refl _) hs.symm h

/-- A rotation black on wire `2` and the box on wire `1` white on wire `2`:
(318), (319) on the box wire `1`. -/
theorem commRBs (b1 b3 c2 : Bool) (z : ℕ → Bool) {r : Lt} (hr : r ∈ rots b1 true b3) :
    Comm (m + 5) (r.circ 4 (m + 5)) (swAt (m + 5) 0 * boxN (m + 5) z c2 false * swAt (m + 5) 0) := by
  have hb : Derivable (theory (m + 5)) (swAt (m + 5) 0 * boxN (m + 5) z c2 false * swAt (m + 5) 0)
      (mc (m + 5) .box [1] (ctlOr (ctlAt 0 c2) (ctlOr (ctlAt 2 false) (colOn 4 (m + 5) z)))) :=
    mc_s0 (m + 5) (by omega) _ 0 (by omega) _ _ (by decide) (fun i hi => by
      simp only [ctlOr, ctlAt, colOn, Net.tau]; split_ifs <;> first | rfl | omega | simp_all)
  refine Comm.congr (Derivable.refl _) hb.symm ?_
  simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [P1_circ]; exact eq318s_ge5 (m + 5) (by omega) ih z false b3 c2 b1
  · rw [P2_circ]; exact eq319s_ge5 (m + 5) (by omega) ih z (!b1) b3 true c2
  · rw [P4_circ]; exact eq319s_ge5 (m + 5) (by omega) ih z b1 b3 true c2
  · rw [P5_circ]; exact eq318s_ge5 (m + 5) (by omega) ih z true b3 c2 b1

set_option maxHeartbeats 1000000 in
/-- A rotation white on wire `2`, conjugated by the swap of the wires `0, 1`,
and the box on wire `0` black on wire `2`: (318), (319) under `X` on wire `2`. -/
theorem commBRs (c1 c2 c3 : Bool) (z : ℕ → Bool) {r' : Lt} (hr' : r' ∈ rots c2 false c3) :
    Comm (m + 5) (boxN (m + 5) z c1 true) (swAt (m + 5) 0 * r'.circ 4 (m + 5) * swAt (m + 5) 0) := by
  have hx := xAt_inv (m + 5) 2 (by omega)
  have fb := flipBox m ih z c1
  simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl
  · rw [P1_circ]
    have hs := s0_rot (m + 5) (by omega) false 0 (by omega) (ctlOr (ctlAt 1 c2) (ctlOr (ctlAt 2 false) (ctlAt 3 c3)))
      (ctlOr (ctlAt 0 c2) (ctlOr (ctlAt 2 false) (ctlAt 3 c3))) (by ctl_eq)
    have f := comm_flip (eq318g_ge5 (m + 5) (by omega) ih z false c3 c1 c2) hx
      (flip2 (m + 5) (by omega) _ [1] _ (ctlOr (ctlAt 0 c2) (ctlOr (ctlAt 2 false) (ctlAt 3 c3))) (by decide) (by simp [ctlOr, ctlAt]) (by ctl_eq)) fb
    exact Comm.congr (Derivable.refl _) hs.symm (Derivable.symm f)
  · rw [P2_circ]
    have hs := s0_rot (m + 5) (by omega) (!c2) 1 le_rfl (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (ctlAt 3 c3)))
      (ctlOr (ctlAt 1 true) (ctlOr (ctlAt 2 false) (ctlAt 3 c3))) (by ctl_eq)
    have f := comm_flip (eq319_ge5 (m + 5) (by omega) ih z (!c2) c3 true c1) hx
      (flip2 (m + 5) (by omega) _ [0] _ (ctlOr (ctlAt 1 true) (ctlOr (ctlAt 2 false) (ctlAt 3 c3))) (by decide) (by simp [ctlOr, ctlAt]) (by ctl_eq)) fb
    exact Comm.congr (Derivable.refl _) hs.symm (Derivable.symm f)
  · rw [P4_circ]
    have hs := s0_rot (m + 5) (by omega) c2 1 le_rfl (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (ctlAt 3 c3)))
      (ctlOr (ctlAt 1 true) (ctlOr (ctlAt 2 false) (ctlAt 3 c3))) (by ctl_eq)
    have f := comm_flip (eq319_ge5 (m + 5) (by omega) ih z c2 c3 true c1) hx
      (flip2 (m + 5) (by omega) _ [0] _ (ctlOr (ctlAt 1 true) (ctlOr (ctlAt 2 false) (ctlAt 3 c3))) (by decide) (by simp [ctlOr, ctlAt]) (by ctl_eq)) fb
    exact Comm.congr (Derivable.refl _) hs.symm (Derivable.symm f)
  · rw [P5_circ]
    have hs : Derivable (theory (m + 5)) (swAt (m + 5) 0 * mc (m + 5) (Kind.sgnZX true) [0]
        (ctlOr (ctlAt 1 c2) (ctlOr (ctlAt 2 false) (ctlAt 3 c3))) * swAt (m + 5) 0)
        (mc (m + 5) (Kind.sgnZX true) [1] (ctlOr (ctlAt 0 c2) (ctlOr (ctlAt 2 false) (ctlAt 3 c3)))) :=
      s0_rot (m + 5) (by omega) true 0 (Nat.zero_le 1) _ _ (by ctl_eq)
    have f := comm_flip (eq318g_ge5 (m + 5) (by omega) ih z true c3 c1 c2) hx
      (flip2 (m + 5) (by omega) _ [1] _ (ctlOr (ctlAt 0 c2) (ctlOr (ctlAt 2 false) (ctlAt 3 c3))) (by decide) (by simp [ctlOr, ctlAt]) (by ctl_eq)) fb
    exact Comm.congr (Derivable.refl _) hs.symm (Derivable.symm f)

/-- Two boxes idle on wire `3`. -/
theorem commBBs (c1 c2 : Bool) (z w : ℕ → Bool) :
    Comm (m + 5) (boxN (m + 5) z c1 true) (swAt (m + 5) 0 * boxN (m + 5) w c2 false * swAt (m + 5) 0) := by
  have hb : Derivable (theory (m + 5)) (swAt (m + 5) 0 * boxN (m + 5) w c2 false * swAt (m + 5) 0)
      (mc (m + 5) .box [1] (ctlOr (ctlAt 0 c2) (ctlOr (ctlAt 2 false) (colOn 4 (m + 5) w)))) :=
    mc_s0 (m + 5) (by omega) _ 0 (by omega) _ _ (by decide) (by ctl_eq)
  refine Comm.congr (Derivable.refl _) hb.symm ?_
  show Comm (m + 4 + 1) (mc _ .box [0] _) (mc _ .box [1] _)
  exact comm_box_idle (q := 3) ih _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp [ctlOr, ctlAt, colOn]) (by simp [ctlOr, ctlAt, colOn])

/-- Every gate of one expansion commutes with every gate of the other. -/
theorem pairs336 (x y : ℕ → Bool) (c1 c2 : Bool) :
    ∀ a ∈ (pcs4 c1 true (x 3)).map (cX 4 (m + 5) x),
      ∀ b ∈ ((pcs4 c2 false (y 3)).map (cX 4 (m + 5) y)).map
        (fun a => swAt (m + 5) 0 * a * swAt (m + 5) 0), Comm (m + 5) a b := by
  intro a ha b hb
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hb'
  rcases pcs4_cls hg with hr | rfl <;> rcases pcs4_cls hg' with hr' | rfl
  · rw [rots_cX hr, rots_cX hr']; exact commRRs m ih _ _ _ _ hr hr'
  · rw [rots_cX hr, P3'_cX]; exact commRBs m ih _ _ _ y hr
  · rw [P3'_cX, rots_cX hr']; exact commBRs m ih _ _ _ x hr'
  · rw [P3'_cX, P3'_cX]; exact commBBs m ih _ _ x y

end Pairs

/-! ## (336) -/

/-- The colouring of `bA N x c` as one colouring of the wires `1, …`. -/
def setOne (c : Bool) (x : ℕ → Bool) : ℕ → Bool := fun i => if i = 1 then c else x i

theorem bA_eq (N : ℕ) (x : ℕ → Bool) (c : Bool) :
    bA N x c = mc N .box [0] (colOn 1 N (setOne c x)) :=
  mc_congr _ _ _ (fun i hi => by
    simp only [ctlOr, ctlAt, colOn, setOne]; split_ifs <;> first | rfl | (exfalso; omega) | simp_all)

/-- (336) when the colourings are black, resp. white, on wire `2`. -/
theorem comm336_core (m : ℕ) (ih : IH (m + 5)) (x y : ℕ → Bool) (c1 c2 : Bool) (hx : x 2 = true)
    (hy : y 2 = false) : Comm (m + 5) (bA (m + 5) x c1) (bB (m + 5) y c2) := by
  have ex : Derivable (theory (m + 5)) (bA (m + 5) x c1)
      (wcX 4 (m + 5) (setOne c1 x) (pcs4 c1 true (x 3))) := by
    have h := expX (m + 5) (by omega) ih (setOne c1 x)
    have e2 : setOne c1 x 2 = true := by simp [setOne, hx]
    rw [e2] at h
    rw [bA_eq]; exact h
  have ey : Derivable (theory (m + 5)) (bA (m + 5) y c2)
      (wcX 4 (m + 5) (setOne c2 y) (pcs4 c2 false (y 3))) := by
    have h := expX (m + 5) (by omega) ih (setOne c2 y)
    have e2 : setOne c2 y 2 = false := by simp [setOne, hy]
    rw [e2] at h
    rw [bA_eq]; exact h
  have hs := swsw (m + 5) 0 (by omega)
  have sB : Derivable (theory (m + 5)) (bB (m + 5) y c2)
      (swAt (m + 5) 0 * bA (m + 5) y c2 * swAt (m + 5) 0) :=
    (swapAB (m + 5) (by omega) y c2).1.symm
  have eB := sB.trans ((dright _ (dleft _ ey)).trans (conj_drawn hs hs _))
  exact Comm.congr ex.symm eB.symm
    (comm_drawn _ _ (pairs336 m ih (setOne c1 x) (setOne c2 y) c1 c2))

/-! ## Relabeling the colourings -/

theorem colOn_tau {lo N j : ℕ} (hj : lo ≤ j) (hjN : j + 2 ≤ N) (x : ℕ → Bool) {i : ℕ} (hi : i < N) :
    colOn lo N (x ∘ Net.tau j) (Net.tau j i) = colOn lo N x i := by
  simp only [colOn, Function.comp, Net.tau_tau]
  unfold Net.tau; split_ifs <;> first | rfl | omega

theorem ctlAt_tau {u j : ℕ} (hu : u < j) (b : Bool) (i : ℕ) :
    ctlAt u b (Net.tau j i) = ctlAt u b i := by
  simp only [ctlAt]; unfold Net.tau; split_ifs <;> first | rfl | omega

theorem colOn_flip {lo N : ℕ} (hlo : lo < N) (x : ℕ → Bool) (i : ℕ) :
    setCtl (colOn lo N (flipAt lo x)) lo (some !(flipAt lo x lo)) i = colOn lo N x i := by
  simp only [setCtl, colOn, flipAt]; split_ifs <;> simp_all

/-- (336) from five wires on. -/
theorem comm336_ge5 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x y : ℕ → Bool) (c₁ c₂ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
      (mc N .box [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
  show Comm (m + 5) (bA (m + 5) x c₁) (bB (m + 5) y c₂)
  by_cases hd : DiffOn 2 (m + 5) x y
  · refine sep_reduce (P := fun x y => Comm (m + 5) (bA (m + 5) x c₁) (bB (m + 5) y c₂)) ?_ ?_
      (fun x y hx hy => comm336_core m ih x y c₁ c₂ hx hy) x y hd
    · intro x y j hj hjN h
      have full : ∀ (u : ℕ) (b : Bool) (z : ℕ → Bool), u ≤ 1 → ∀ i < m + 5, i ≠ 1 - u →
          (ctlOr (ctlAt u b) (colOn 2 (m + 5) z) i).isSome = true := by
        intro u b z hu i hi hiu
        simp only [ctlOr, ctlAt, colOn]; split_ifs <;> simp <;> omega
      have rA := box_relabel (m + 5) (by omega) ih 0 (by omega) _ (full 1 c₁ (x ∘ Net.tau j) le_rfl)
        j hjN (by omega) (by omega)
      have rB := box_relabel (m + 5) (by omega) ih 1 (by omega) _ (full 0 c₂ (y ∘ Net.tau j) (by omega))
        j hjN (by omega) (by omega)
      refine Comm.congr (rA.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_))))
        (rB.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))) (Comm.conj h (swsw _ j hjN))
      · simp only [Function.comp, ctlOr, ctlAt_tau (show 1 < j by omega), colOn_tau (by omega) hjN x hi]
      · simp only [Function.comp, ctlOr, ctlAt_tau (show 0 < j by omega), colOn_tau (by omega) hjN y hi]
    · intro x y h
      have hx := xAt_inv (m + 5) 2 (by omega)
      refine comm_flip h hx ?_ ?_
      · have e := eq81 (m + 5) .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 (m + 5) (flipAt 2 x))) 2
          (flipAt 2 x 2) (by omega) (by decide) (by simp [ctlOr, ctlAt, colOn])
        rw [show drawn [xAt (m + 5) 2, bA (m + 5) (flipAt 2 x) c₁, xAt (m + 5) 2] =
          xAt (m + 5) 2 * bA (m + 5) (flipAt 2 x) c₁ * xAt (m + 5) 2 by simp [drawn, mul_assoc]] at e
        refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
        have := colOn_flip (lo := 2) (N := m + 5) (by omega) x i
        simp only [setCtl, ctlOr, ctlAt] at this ⊢
        split_ifs at this ⊢ <;> simp_all
      · have e := eq81 (m + 5) .box [1] (ctlOr (ctlAt 0 c₂) (colOn 2 (m + 5) (flipAt 2 y))) 2
          (flipAt 2 y 2) (by omega) (by decide) (by simp [ctlOr, ctlAt, colOn])
        rw [show drawn [xAt (m + 5) 2, bB (m + 5) (flipAt 2 y) c₂, xAt (m + 5) 2] =
          xAt (m + 5) 2 * bB (m + 5) (flipAt 2 y) c₂ * xAt (m + 5) 2 by simp [drawn, mul_assoc]] at e
        refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
        have := colOn_flip (lo := 2) (N := m + 5) (by omega) y i
        simp only [setCtl, ctlOr, ctlAt] at this ⊢
        split_ifs at this ⊢ <;> simp_all
  · have e : bB (m + 5) y c₂ = bB (m + 5) x c₂ := mc_congr _ _ _ (fun i hi => by
      simp only [ctlOr, ctlAt, colOn]
      by_cases h1 : 2 ≤ i ∧ i < m + 5
      · have : y i = x i := by
          by_contra hne; exact hd ⟨i, h1.1, h1.2, fun h => hne h.symm⟩
        simp [h1, this]
      · simp [h1])
    rw [e]
    exact same336 (m + 5) hN ih x c₁ c₂

end QCert.RealCliffordCH.Sec8.D.N13
