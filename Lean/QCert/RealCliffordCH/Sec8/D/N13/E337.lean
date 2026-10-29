/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equations (337) and (338) from five wires on

The box on wire `0` (control `c₁` on wire `1`, the wires `2, …` coloured by
`x`) commutes with the multi-controlled `H` whose box is on wire `0`, resp.
`1`, and whose `H` is on wire `1`, resp. `0` (controls on the wires `2, …`
coloured by `y`), when `x ≠ y`.

As for (336) (`E336x`): by (307), (313) the colourings may be assumed to
differ on wire `2`, and by (81) to be black there for `x`, white for `y`.
The multi-controlled `H` is the box with a black control on wire `1`
(resp. `0`) between two `P ⊗ P` (`hg0_box4`, `hg1_box4`).  Both boxes are
written by (320)/(321) (`expX`), and every gate of one expansion commutes
with every gate of the other, conjugated by `P ⊗ P`:

* two rotations: a semantic step without wire `4`;
* a rotation black on wire `2` and the box idle on wire `3`, white on wire
  `2`, between `P ⊗ P`: (322)/(323) (`eq322_word`) conjugated by `P ⊗ P`
  (and by the swap of the wires `0, 1` for (338));
* the box black on wire `2` and a rotation white there between `P ⊗ P`:
  (322)/(323) conjugated by `X` on wire `2`;
* two boxes idle on wire `3`: a semantic step without wire `3`
  (`commBBpp`).

Status: not built.  Its decided steps need too much memory as written (one
declaration of four runs in `E337r1` passed 4.7 GB; `E322`, imported through
`E322x`, needs about 11 GB): see `HANDOVER.md` before building.  Nothing
imports it.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E336x
import QCert.RealCliffordCH.Sec8.D.N13.E322x
import QCert.RealCliffordCH.Sec8.D.N13.BoxPPBridge
import QCert.RealCliffordCH.Sec8.D.N13.E345
import QCert.RealCliffordCH.Sec8.D.N13.E337r1
import QCert.RealCliffordCH.Sec8.D.N13.E337r2

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-! ## `P ⊗ P` -/

theorem wc_ppL (m : ℕ) : wc 4 (m + 5) N13.ppL = (pp : Circ (m + 5)) := rfl

theorem pp5_inv (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) ((pp : Circ (m + 5)) * pp) 1 :=
  pp_inv (m + 2) ih

/-- `P ⊗ P` twice around a gate cancels. -/
theorem pp_pp_conj {m : ℕ} (ih : IH (m + 5)) (a : Circ (m + 5)) :
    Derivable (theory (m + 5)) ((pp : Circ (m + 5)) * (pp * a * pp) * pp) a := by
  have h := pp5_inv m ih
  have e : (pp : Circ (m + 5)) * (pp * a * pp) * pp = (pp * pp) * a * (pp * pp) := by
    simp only [mul_assoc]
  rw [e]
  have := dmul (dmul h (Derivable.refl a)) h
  simpa only [one_mul, mul_one] using this

/-- Conjugation by an involution undone. -/
theorem conj_back {N : ℕ} {u a b : Circ N} (hu : Derivable (theory N) (u * u) 1)
    (h : Derivable (theory N) (u * a * u) b) : Derivable (theory N) (u * b * u) a := by
  refine (dright u (dleft u h.symm)).trans ?_
  have e : u * (u * a * u) * u = (u * u) * a * (u * u) := by simp only [mul_assoc]
  rw [e]
  have := dmul (dmul hu (Derivable.refl a)) hu
  simpa only [one_mul, mul_one] using this

/-- `X` on wire `2` passes `P ⊗ P` on the wires `0, 1`. -/
theorem x2_pp (m : ℕ) :
    Derivable (theory (m + 5)) (xAt (m + 5) 2 * (pp : Circ (m + 5))) (pp * xAt (m + 5) 2) := by
  exact comm_low_high _ _ (lowW_pp (m + 3)) (xAt_wires (m + 5) 2).2

/-! ## The rotations of (322) -/

/-- The rotation of (322)/(323): on wire `0` (`R0`) or `1` (`R1`). -/
def Rr (one a α β : Bool) : Lt := if one then R1 a α β else R0 a α β

/-- The same, white on wire `2`. -/
def Rw (one a α β : Bool) : Lt :=
  if one then .g (Kind.sgnZX a) [1] [(0, β), (2, false), (3, α)] false
  else .g (Kind.sgnZX a) [0] [(1, β), (2, false), (3, α)] false

theorem wc_W322 (m : ℕ) (one a α β : Bool) :
    wc 4 (m + 5) (W322 one a α β) =
      (pp : Circ (m + 5)) * (Rr one a α β).circ 4 (m + 5) * pp := by
  cases one <;> simp [W322, W0, W1, Rr, wc_append, wc_one', wc_ppL, mul_assoc]

theorem rots_Rr {b1 b3 : Bool} {r : Lt} (hr : r ∈ rots b1 true b3) :
    ∃ one a β, r = Rr one a b3 β := by
  simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨false, false, b1, rfl⟩
  · exact ⟨true, !b1, true, rfl⟩
  · exact ⟨true, b1, true, rfl⟩
  · exact ⟨false, true, b1, rfl⟩

theorem rots_Rw {b1 b3 : Bool} {r : Lt} (hr : r ∈ rots b1 false b3) :
    ∃ one a β, r = Rw one a b3 β := by
  simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨false, false, b1, rfl⟩
  · exact ⟨true, !b1, true, rfl⟩
  · exact ⟨true, b1, true, rfl⟩
  · exact ⟨false, true, b1, rfl⟩

theorem srots_Rw {b1 b3 : Bool} {r : Lt} (hr : r ∈ srots b1 false b3) :
    ∃ one a β, r = Rw one a b3 β := by
  simp only [srots, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨true, false, b1, rfl⟩
  · exact ⟨false, !b1, true, rfl⟩
  · exact ⟨false, b1, true, rfl⟩
  · exact ⟨true, true, b1, rfl⟩

theorem rots_Rr_s {b1 b3 : Bool} {r : Lt} (hr : r ∈ rots b1 true b3) :
    ∃ one a β, r = Rr (!one) a b3 β := by
  obtain ⟨one, a, β, rfl⟩ := rots_Rr hr
  exact ⟨!one, a, β, by simp⟩

/-- `X` on wire `2` turns the white rotation black. -/
theorem flipRw (m : ℕ) (one a α β : Bool) :
    Derivable (theory (m + 5)) (xAt (m + 5) 2 * (Rw one a α β).circ 4 (m + 5) * xAt (m + 5) 2)
      ((Rr one a α β).circ 4 (m + 5)) := by
  cases one
  · exact flip81 _ [0] _ _ false 2 false (by omega) (by decide) rfl (by ctl_tac)
  · exact flip81 _ [1] _ _ false 2 false (by omega) (by decide) rfl (by ctl_tac)

/-- The swap of the wires `0, 1` exchanges the two rotations of (322). -/
theorem swapRr (m : ℕ) (one a α β : Bool) :
    Derivable (theory (m + 5)) (swAt (m + 5) 0 * (Rr one a α β).circ 4 (m + 5) * swAt (m + 5) 0)
      ((Rr (!one) a α β).circ 4 (m + 5)) := by
  cases one
  · exact s0_rot (m + 5) (by omega) a 0 (by omega) _ _ (by ctl_eq)
  · exact s0_rot (m + 5) (by omega) a 1 le_rfl _ _ (by ctl_eq)

/-! ## The pairs -/

section Pairs

variable (m : ℕ) (ih : IH (m + 5))
include ih

/-- (322)/(323) between `P ⊗ P`: a rotation black on wire `2` passes the box
idle on wire `3`, white on wire `2`, conjugated by `P ⊗ P`. -/
theorem commR_ppB (z : ℕ → Bool) (one a α β γ : Bool) :
    Comm (m + 5) ((Rr one a α β).circ 4 (m + 5))
      ((pp : Circ (m + 5)) * boxN (m + 5) z γ false * pp) := by
  have h := eq322_word m ih z one a α β γ
  rw [wc_W322] at h
  have hc := Comm.conj h (pp5_inv m ih) (u := pp) (v := pp)
  exact Comm.congr (pp_pp_conj ih _) (Derivable.refl _) hc

/-- (322)/(323) under `X` on wire `2`: the box idle on wire `3`, black on wire
`2`, passes a rotation white there between `P ⊗ P`. -/
theorem commB_ppRw (z : ℕ → Bool) (c1 one a α β : Bool) :
    Comm (m + 5) (boxN (m + 5) z c1 true)
      ((pp : Circ (m + 5)) * (Rw one a α β).circ 4 (m + 5) * pp) := by
  have h := eq322_word m ih z one a α β c1
  rw [wc_W322] at h
  have hx := xAt_inv (m + 5) 2 (by omega)
  have hb : Derivable (theory (m + 5))
      (xAt (m + 5) 2 * ((pp : Circ (m + 5)) * (Rr one a α β).circ 4 (m + 5) * pp) * xAt (m + 5) 2)
      ((pp : Circ (m + 5)) * (Rw one a α β).circ 4 (m + 5) * pp) := by
    exact pp_move_swap (x2_pp m) (conj_back hx (flipRw m one a α β))
  exact comm_flip (Derivable.symm h) hx (flipBox m ih z c1) hb

/-- The swap of the wires `0, 1` carries the box idle on wire `3` to wire `1`. -/
theorem sw_boxN (z : ℕ → Bool) (c2 : Bool) :
    Derivable (theory (m + 5)) (swAt (m + 5) 0 * boxN (m + 5) z c2 false * swAt (m + 5) 0)
      (mc (m + 5) .box [1] (ctlOr (ctlAt 0 c2) (ctlOr (ctlAt 2 false) (colOn 4 (m + 5) z)))) :=
  mc_s0 (m + 5) (by omega) _ 0 (by omega) _ _ (by decide) (by ctl_eq)

/-- (322)/(323) between `P ⊗ P`, the box on wire `1`. -/
theorem commR_ppB1 (z : ℕ → Bool) (one a α β : Bool) :
    Comm (m + 5) ((Rr one a α β).circ 4 (m + 5))
      ((pp : Circ (m + 5)) *
        mc (m + 5) .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (colOn 4 (m + 5) z))) *
        pp) := by
  have h := commR_ppB m ih z (!one) a α β true
  have hs := swsw (m + 5) 0 (by omega)
  have ha := swapRr m (!one) a α β
  rw [Bool.not_not] at ha
  have hb := pp_move_swap (pp_swap4 (m + 1) ih) (sw_boxN m ih z true)
  exact comm_flip h hs ha hb

/-- Two boxes idle on wire `3`, the second between `P ⊗ P`. -/
theorem commBB337 (z w : ℕ → Bool) (c1 : Bool) :
    Comm (m + 5) (boxN (m + 5) z c1 true)
      ((pp : Circ (m + 5)) * boxN (m + 5) w true false * pp) := by
  have h := commBBpp m ih false false c1 true z w
  have e1 : mc (m + 5) .box [boxTarget false] (boxCtl4 (m + 5) false c1 true z) =
      boxN (m + 5) z c1 true := mc_congr _ _ _ (by unfold boxCtl4 boxCtl; ctl_eq)
  have e2 : mc (m + 5) .box [boxTarget false] (boxCtl4 (m + 5) false true false w) =
      boxN (m + 5) w true false := mc_congr _ _ _ (by unfold boxCtl4 boxCtl; ctl_eq)
  rwa [e1, e2] at h

theorem commBB338 (z w : ℕ → Bool) (c1 : Bool) :
    Comm (m + 5) (boxN (m + 5) z c1 true)
      ((pp : Circ (m + 5)) *
        mc (m + 5) .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (colOn 4 (m + 5) w))) *
        pp) := by
  have h := commBBpp m ih false true c1 true z w
  have e1 : mc (m + 5) .box [boxTarget false] (boxCtl4 (m + 5) false c1 true z) =
      boxN (m + 5) z c1 true := mc_congr _ _ _ (by unfold boxCtl4 boxCtl; ctl_eq)
  have e2 : mc (m + 5) .box [boxTarget true] (boxCtl4 (m + 5) true true false w) =
      mc (m + 5) .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (colOn 4 (m + 5) w))) :=
    mc_congr _ _ _ (by unfold boxCtl4 boxCtl; ctl_eq)
  rwa [e1, e2] at h

end Pairs

/-! ## Two rotations, a semantic step without wire `4` -/

theorem comm_of_ppchk {m : ℕ} (ih : IH (m + 5)) {r r' : Lt}
    (hr : r.circ 5 (m + 5) = r.circ 4 (m + 5)) (hr' : r'.circ 5 (m + 5) = r'.circ 4 (m + 5))
    (c : check 4 [] ([r] ++ N13.ppL ++ [r'] ++ N13.ppL) (N13.ppL ++ [r'] ++ N13.ppL ++ [r])
      [.sem 0 22 (N13.ppL ++ [r'] ++ N13.ppL ++ [r]) 4] = true) :
    Comm (m + 5) (r.circ 4 (m + 5)) ((pp : Circ (m + 5)) * r'.circ 4 (m + 5) * pp) := by
  have h := check_sound (frame 4) ih (allD_nil 5 m) c
  have ep : wc 5 (m + 5) N13.ppL = (pp : Circ (m + 5)) := rfl
  simp only [wc_append, wc_one', ep, hr, hr'] at h
  unfold Comm
  rw [drawn_two, drawn_two]
  simpa only [mul_assoc] using h

/-- A two-letter run to the empty word: the letters are inverse. -/
theorem inv_of_chk {m : ℕ} (ih : IH (m + 5)) {x y : Lt}
    (hx : x.circ 5 (m + 5) = x.circ 4 (m + 5)) (hy : y.circ 5 (m + 5) = y.circ 4 (m + 5))
    (c : check 4 [] [x, y] [] [.sem 0 2 [] 4] = true) :
    Derivable (theory (m + 5)) (y.circ 4 (m + 5) * x.circ 4 (m + 5)) 1 := by
  have h := check_sound (frame 4) ih (allD_nil 5 m) c
  have e : wc 5 (m + 5) ([] : List Lt) = 1 := rfl
  rw [wc_two, drawn_two, e, hx, hy] at h
  exact h

/-- Conjugates of inverse circuits are inverse. -/
theorem conj_inv {N : ℕ} {P a b : Circ N} (hP : Derivable (theory N) (P * P) 1)
    (h : Derivable (theory N) (a * b) 1) :
    Derivable (theory N) ((P * a * P) * (P * b * P)) 1 := by
  have e : P * a * P * (P * b * P) = P * a * (P * P) * (b * P) := by simp only [mul_assoc]
  rw [e]
  refine (dright _ (dleft _ hP)).trans ?_
  rw [mul_one]
  have e2 : P * a * (b * P) = P * (a * b) * P := by simp only [mul_assoc]
  rw [e2]
  refine (dctx P P h).trans ?_
  rw [mul_one]
  exact hP

/-- Commutation passes to an inverse of the second gate (Lemma B.5). -/
theorem comm_inv_r {N : ℕ} {a b b' : Circ N} (h : Comm N a b)
    (h1 : Derivable (theory N) (b * b') 1) (h2 : Derivable (theory N) (b' * b) 1) :
    Comm N a b' :=
  Derivable.symm (Comm.inv (Derivable.symm h) h1 h2)

theorem rots2_sub {b1 b2 b3 : Bool} {r : Lt} (h : r ∈ rots2 b1 b2 b3) : r ∈ rots b1 b2 b3 := by
  simp only [rots2, rots, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
  rcases h with rfl | rfl <;> simp

theorem srots2_sub {b1 b2 b3 : Bool} {r : Lt} (h : r ∈ srots2 b1 b2 b3) :
    r ∈ srots b1 b2 b3 := by
  rw [srots_eq]
  simp only [srots2, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
  rcases h with rfl | rfl <;> simp

/-- A rotation of the expansion is one of `rots2` or the inverse of one. -/
theorem rots_base (m : ℕ) (ih : IH (m + 5)) {b1 b2 b3 : Bool} {r : Lt}
    (hr : r ∈ rots b1 b2 b3) :
    ∃ r0 ∈ rots2 b1 b2 b3, r = r0 ∨
      (Derivable (theory (m + 5)) (r0.circ 4 (m + 5) * r.circ 4 (m + 5)) 1 ∧
        Derivable (theory (m + 5)) (r.circ 4 (m + 5) * r0.circ 4 (m + 5)) 1) := by
  have hc := chkInvR b1 b2 b3
  have rb : ∀ {x : Lt}, x ∈ rots b1 b2 b3 → x.circ 5 (m + 5) = x.circ 4 (m + 5) :=
    fun hx => rots_rebase hx
  have m1 : P1 b1 b2 b3 ∈ rots b1 b2 b3 := by simp [rots]
  have m2 : P2 b1 b2 b3 ∈ rots b1 b2 b3 := by simp [rots]
  have m4 : P4 b1 b2 b3 ∈ rots b1 b2 b3 := by simp [rots]
  have m5 : P5 b1 b2 b3 ∈ rots b1 b2 b3 := by simp [rots]
  simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [rots2], Or.inl rfl⟩
  · exact ⟨_, by simp [rots2], Or.inl rfl⟩
  · exact ⟨P2 b1 b2 b3, by simp [rots2], Or.inr
      ⟨inv_of_chk ih (rb m4) (rb m2) hc.2.2.1, inv_of_chk ih (rb m2) (rb m4) hc.2.2.2⟩⟩
  · exact ⟨P1 b1 b2 b3, by simp [rots2], Or.inr
      ⟨inv_of_chk ih (rb m5) (rb m1) hc.1, inv_of_chk ih (rb m1) (rb m5) hc.2.1⟩⟩

/-- The same for the rotations with the wires `0, 1` exchanged. -/
theorem srots_base (m : ℕ) (ih : IH (m + 5)) {b1 b2 b3 : Bool} {r : Lt}
    (hr : r ∈ srots b1 b2 b3) :
    ∃ r0 ∈ srots2 b1 b2 b3, r = r0 ∨
      (Derivable (theory (m + 5)) (r0.circ 4 (m + 5) * r.circ 4 (m + 5)) 1 ∧
        Derivable (theory (m + 5)) (r.circ 4 (m + 5) * r0.circ 4 (m + 5)) 1) := by
  have hc := chkInvS b1 b2 b3
  have rb : ∀ {x : Lt}, x ∈ srots b1 b2 b3 → x.circ 5 (m + 5) = x.circ 4 (m + 5) :=
    fun hx => srots_rebase hx
  have m1 : SR1 b1 b2 b3 ∈ srots b1 b2 b3 := by simp [srots_eq]
  have m2 : SR2 b1 b2 b3 ∈ srots b1 b2 b3 := by simp [srots_eq]
  have m3 : SR3 b1 b2 b3 ∈ srots b1 b2 b3 := by simp [srots_eq]
  have m4 : SR4 b1 b2 b3 ∈ srots b1 b2 b3 := by simp [srots_eq]
  rw [srots_eq] at hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [srots2], Or.inl rfl⟩
  · exact ⟨_, by simp [srots2], Or.inl rfl⟩
  · exact ⟨SR2 b1 b2 b3, by simp [srots2], Or.inr
      ⟨inv_of_chk ih (rb m3) (rb m2) hc.2.2.1, inv_of_chk ih (rb m2) (rb m3) hc.2.2.2⟩⟩
  · exact ⟨SR1 b1 b2 b3, by simp [srots2], Or.inr
      ⟨inv_of_chk ih (rb m4) (rb m1) hc.1, inv_of_chk ih (rb m1) (rb m4) hc.2.1⟩⟩

/-- From the base cases to all rotations, on both sides. -/
theorem comm_bases {m : ℕ} (ih : IH (m + 5)) {r0 r r1 r' : Lt}
    (h : Comm (m + 5) (r0.circ 4 (m + 5)) ((pp : Circ (m + 5)) * r1.circ 4 (m + 5) * pp))
    (e0 : r = r0 ∨ (Derivable (theory (m + 5)) (r0.circ 4 (m + 5) * r.circ 4 (m + 5)) 1 ∧
        Derivable (theory (m + 5)) (r.circ 4 (m + 5) * r0.circ 4 (m + 5)) 1))
    (e1 : r' = r1 ∨ (Derivable (theory (m + 5)) (r1.circ 4 (m + 5) * r'.circ 4 (m + 5)) 1 ∧
        Derivable (theory (m + 5)) (r'.circ 4 (m + 5) * r1.circ 4 (m + 5)) 1)) :
    Comm (m + 5) (r.circ 4 (m + 5)) ((pp : Circ (m + 5)) * r'.circ 4 (m + 5) * pp) := by
  have h' : Comm (m + 5) (r0.circ 4 (m + 5)) ((pp : Circ (m + 5)) * r'.circ 4 (m + 5) * pp) := by
    rcases e1 with rfl | ⟨i1, i2⟩
    · exact h
    · exact comm_inv_r h (conj_inv (pp5_inv m ih) i1) (conj_inv (pp5_inv m ih) i2)
  rcases e0 with rfl | ⟨i1, i2⟩
  · exact h'
  · exact Comm.inv h' i1 i2

theorem commRR337 {m : ℕ} (ih : IH (m + 5)) {b1 b3 c3 : Bool} {r r' : Lt}
    (hr : r ∈ rots b1 true b3) (hr' : r' ∈ rots true false c3) :
    Comm (m + 5) (r.circ 4 (m + 5)) ((pp : Circ (m + 5)) * r'.circ 4 (m + 5) * pp) := by
  obtain ⟨r0, hr0, e0⟩ := rots_base m ih hr
  obtain ⟨r1, hr1, e1⟩ := rots_base m ih hr'
  exact comm_bases ih (comm_of_ppchk ih (rots_rebase (rots2_sub hr0)) (rots_rebase (rots2_sub hr1))
    (chkRR337r b1 b3 c3 r0 hr0 r1 hr1)) e0 e1

theorem commRR338 {m : ℕ} (ih : IH (m + 5)) {b1 b3 c3 : Bool} {r r' : Lt}
    (hr : r ∈ rots b1 true b3) (hr' : r' ∈ srots true false c3) :
    Comm (m + 5) (r.circ 4 (m + 5)) ((pp : Circ (m + 5)) * r'.circ 4 (m + 5) * pp) := by
  obtain ⟨r0, hr0, e0⟩ := rots_base m ih hr
  obtain ⟨r1, hr1, e1⟩ := srots_base m ih hr'
  exact comm_bases ih (comm_of_ppchk ih (rots_rebase (rots2_sub hr0))
    (srots_rebase (srots2_sub hr1)) (chkRR338r b1 b3 c3 r0 hr0 r1 hr1)) e0 e1

/-! ## The pairs -/

section Pairs2

variable (m : ℕ) (ih : IH (m + 5))
include ih

theorem pairs337 (x y : ℕ → Bool) (c1 x3 y3 : Bool) :
    ∀ a ∈ (pcs4 c1 true x3).map (cX 4 (m + 5) x),
      ∀ b ∈ ((pcs4 true false y3).map (cX 4 (m + 5) y)).map
        (fun a => (pp : Circ (m + 5)) * a * pp), Comm (m + 5) a b := by
  intro a ha b hb
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hb'
  rcases pcs4_cls hg with hr | rfl <;> rcases pcs4_cls hg' with hr' | rfl
  · rw [rots_cX hr, rots_cX hr']
    exact commRR337 ih hr hr'
  · rw [rots_cX hr, P3'_cX]
    obtain ⟨one, a, β, rfl⟩ := rots_Rr hr
    exact commR_ppB m ih y one a x3 β true
  · rw [P3'_cX, rots_cX hr']
    obtain ⟨one, a, β, rfl⟩ := rots_Rw hr'
    exact commB_ppRw m ih x c1 one a y3 β
  · rw [P3'_cX, P3'_cX]
    exact commBB337 m ih x y c1

theorem pairs338 (x y : ℕ → Bool) (c1 x3 y3 : Bool) :
    ∀ a ∈ (pcs4 c1 true x3).map (cX 4 (m + 5) x),
      ∀ b ∈ (((pcs4 true false y3).map (cX 4 (m + 5) y)).map
        (fun a => swAt (m + 5) 0 * a * swAt (m + 5) 0)).map
        (fun a => (pp : Circ (m + 5)) * a * pp), Comm (m + 5) a b := by
  intro a ha b hb
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
  obtain ⟨b1, hb1, rfl⟩ := List.mem_map.1 hb
  obtain ⟨b2, hb2, rfl⟩ := List.mem_map.1 hb1
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hb2
  rcases pcs4_cls hg with hr | rfl <;> rcases pcs4_cls hg' with hr' | rfl
  · rw [rots_cX hr, rots_cX hr']
    obtain ⟨r'', hr'', hs⟩ := s0_rots (m + 5) (by omega) hr'
    exact Comm.congr (Derivable.refl _) (dright _ (dleft _ hs.symm))
      (commRR338 ih hr hr'')
  · rw [rots_cX hr, P3'_cX]
    obtain ⟨one, a, β, rfl⟩ := rots_Rr hr
    exact Comm.congr (Derivable.refl _) (dright _ (dleft _ (sw_boxN m ih y true).symm))
      (commR_ppB1 m ih y one a x3 β)
  · rw [P3'_cX, rots_cX hr']
    obtain ⟨r'', hr'', hs⟩ := s0_rots (m + 5) (by omega) hr'
    obtain ⟨one, a, β, rfl⟩ := srots_Rw hr''
    exact Comm.congr (Derivable.refl _) (dright _ (dleft _ hs.symm))
      (commB_ppRw m ih x c1 one a y3 β)
  · rw [P3'_cX, P3'_cX]
    exact Comm.congr (Derivable.refl _) (dright _ (dleft _ (sw_boxN m ih y true).symm))
      (commBB338 m ih x y c1)

end Pairs2

/-! ## The cores: the colourings black, resp. white, on wire `2` -/

theorem expA (m : ℕ) (ih : IH (m + 5)) (x : ℕ → Bool) (c : Bool) (b : Bool) (hx : x 2 = b) :
    Derivable (theory (m + 5)) (bA (m + 5) x c)
      (wcX 4 (m + 5) (setOne c x) (pcs4 c b (x 3))) := by
  have h := expX (m + 5) (by omega) ih (setOne c x)
  have e2 : setOne c x 2 = b := by simp [setOne, hx]
  rw [e2] at h
  rw [bA_eq]; exact h

theorem comm337_core (m : ℕ) (ih : IH (m + 5)) (x y : ℕ → Bool) (c1 : Bool) (hx : x 2 = true)
    (hy : y 2 = false) :
    Comm (m + 5) (bA (m + 5) x c1) (mc (m + 5) .hg [0, 1] (colOn 2 (m + 5) y)) := by
  have ex := expA m ih x c1 true hx
  have ey := expA m ih y true false hy
  have hpp := pp5_inv m ih
  have eB : Derivable (theory (m + 5)) (mc (m + 5) .hg [0, 1] (colOn 2 (m + 5) y))
      (drawn (((pcs4 true false (y 3)).map (cX 4 (m + 5) (setOne true y))).map
        (fun a => (pp : Circ (m + 5)) * a * pp))) :=
    (hg0_box4 (m + 1) y).trans ((dright _ (dleft _ ey)).trans (conj_drawn hpp hpp _))
  exact Comm.congr ex.symm eB.symm
    (comm_drawn _ _ (pairs337 m ih (setOne c1 x) (setOne true y) c1 (x 3) (y 3)))

theorem comm338_core (m : ℕ) (ih : IH (m + 5)) (x y : ℕ → Bool) (c1 : Bool) (hx : x 2 = true)
    (hy : y 2 = false) :
    Comm (m + 5) (bA (m + 5) x c1) (mc (m + 5) .hg [1, 0] (colOn 2 (m + 5) y)) := by
  have ex := expA m ih x c1 true hx
  have ey := expA m ih y true false hy
  have hpp := pp5_inv m ih
  have hs := swsw (m + 5) 0 (by omega)
  have sB : Derivable (theory (m + 5)) (bB (m + 5) y true)
      (swAt (m + 5) 0 * bA (m + 5) y true * swAt (m + 5) 0) :=
    (swapAB (m + 5) (by omega) y true).1.symm
  have eB1 := sB.trans ((dright _ (dleft _ ey)).trans (conj_drawn hs hs _))
  have eB : Derivable (theory (m + 5)) (mc (m + 5) .hg [1, 0] (colOn 2 (m + 5) y))
      (drawn ((((pcs4 true false (y 3)).map (cX 4 (m + 5) (setOne true y))).map
        (fun a => swAt (m + 5) 0 * a * swAt (m + 5) 0)).map
        (fun a => (pp : Circ (m + 5)) * a * pp))) :=
    (hg1_box4 (m + 1) ih y).trans ((dright _ (dleft _ eB1)).trans (conj_drawn hpp hpp _))
  exact Comm.congr ex.symm eB.symm
    (comm_drawn _ _ (pairs338 m ih (setOne c1 x) (setOne true y) c1 (x 3) (y 3)))

/-! ## Relabeling the multi-controlled `H` -/

theorem ctrl_len_hg (k : ℕ) (tg : List ℕ) (htg : tg = [0, 1] ∨ tg = [1, 0]) (y : ℕ → Bool) :
    (ctrlWires (k + 2) tg (colOn 2 (k + 2) y)).length = k := by
  have e : ctrlWires (k + 2) tg (colOn 2 (k + 2) y) =
      ctrlWires (k + 2) (List.range 2) (colOn 2 (k + 2) y) := by
    unfold ctrlWires
    refine List.filter_congr (fun i _ => ?_)
    rcases htg with rfl | rfl
    · rfl
    · rcases i with _ | _ | i <;> rfl
  rw [e, ctrlWires_full k 2 _ (fun i => by simp only [colOn]; split_ifs with h <;> simp [h] <;> omega),
    List.length_range']

/-- (313): the swap of two controls relabels the multi-controlled `H`. -/
theorem hg_relabel (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (tg : List ℕ) (htg : tg = [0, 1] ∨ tg = [1, 0])
    (y : ℕ → Bool) (j : ℕ) (hj : 2 ≤ j) (hjN : j + 2 ≤ N) :
    Derivable (theory N) (swAt N j * mc N .hg tg (colOn 2 N (y ∘ Net.tau j)) * swAt N j)
      (mc N .hg tg (colOn 2 N y)) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  have hsym : CanonSym .hg (ctrlWires (k + 2) tg (colOn 2 (k + 2) (y ∘ Net.tau j))).length := by
    rw [ctrl_len_hg k tg htg]
    exact canonSym_hg k (fun u hu1 hu2 => eq313 (k + 2) hN ih u hu1 hu2)
  have h := mc_swap_sym (k + 2) j hjN .hg tg (colOn 2 (k + 2) (y ∘ Net.tau j))
    (by rcases htg with rfl | rfl <;> rfl) (by rcases htg with rfl | rfl <;> decide)
    (by rcases htg with rfl | rfl <;> simp <;> omega) hsym
  have e1 : tg.map (Net.tau j) = tg := by
    rcases htg with rfl | rfl <;> simp only [List.map_cons, List.map_nil, Net.tau] <;>
      split_ifs <;> first | rfl | omega
  rw [e1] at h
  have e2 : drawn [swAt (k + 2) j, mc (k + 2) .hg tg (colOn 2 (k + 2) (y ∘ Net.tau j)),
      swAt (k + 2) j] =
      swAt (k + 2) j * mc (k + 2) .hg tg (colOn 2 (k + 2) (y ∘ Net.tau j)) * swAt (k + 2) j := by
    simp [drawn, mul_assoc]
  rw [e2] at h
  exact h.trans (der_of_eq (mc_congr _ _ _ (fun i hi => colOn_tau (by omega) hjN y hi)))

/-- (81) on the control `2` of a multi-controlled `H`. -/
theorem hg_flip2 (N : ℕ) (hN : 3 ≤ N) (tg : List ℕ) (htg : 2 ∉ tg) (y : ℕ → Bool) :
    Derivable (theory N) (xAt N 2 * mc N .hg tg (colOn 2 N (flipAt 2 y)) * xAt N 2)
      (mc N .hg tg (colOn 2 N y)) := by
  have e := eq81 N .hg tg (colOn 2 N (flipAt 2 y)) 2 (flipAt 2 y 2) (by omega) htg
    (by simp only [colOn]; exact if_pos ⟨le_rfl, by omega⟩)
  rw [show drawn [xAt N 2, mc N .hg tg (colOn 2 N (flipAt 2 y)), xAt N 2] =
    xAt N 2 * mc N .hg tg (colOn 2 N (flipAt 2 y)) * xAt N 2 by simp [drawn, mul_assoc]] at e
  exact e.trans (der_of_eq (mc_congr _ _ _ (fun i _ => colOn_flip (by omega) y i)))

/-- (81) on the control `2` of the box of (337). -/
theorem bA_flip2 (N : ℕ) (hN : 3 ≤ N) (x : ℕ → Bool) (c : Bool) :
    Derivable (theory N) (xAt N 2 * bA N (flipAt 2 x) c * xAt N 2) (bA N x c) := by
  have e := eq81 N .box [0] (ctlOr (ctlAt 1 c) (colOn 2 N (flipAt 2 x))) 2
    (flipAt 2 x 2) (by omega) (by decide) (by simp [ctlOr, ctlAt, colOn, show 2 < N by omega])
  rw [show drawn [xAt N 2, bA N (flipAt 2 x) c, xAt N 2] =
    xAt N 2 * bA N (flipAt 2 x) c * xAt N 2 by simp [drawn, mul_assoc]] at e
  refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
  have := colOn_flip (lo := 2) (N := N) (by omega) x i
  simp only [setCtl, ctlOr, ctlAt] at this ⊢
  split_ifs at this ⊢ <;> simp_all

/-- (307): the swap of two controls relabels the box of (337). -/
theorem bA_relabel (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) (c : Bool) (j : ℕ)
    (hj : 2 ≤ j) (hjN : j + 2 ≤ N) :
    Derivable (theory N) (swAt N j * bA N (x ∘ Net.tau j) c * swAt N j) (bA N x c) := by
  have full : ∀ i < N, i ≠ 0 → (ctlOr (ctlAt 1 c) (colOn 2 N (x ∘ Net.tau j)) i).isSome = true := by
    intro i hi hi0
    simp only [ctlOr, ctlAt, colOn]; split_ifs <;> simp <;> omega
  have rA := box_relabel N hN ih 0 (by omega) _ full j hjN (by omega) (by omega)
  refine rA.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
  simp only [Function.comp, ctlOr, ctlAt_tau (show 1 < j by omega), colOn_tau (by omega) hjN x hi]

/-! ## (337) and (338) from five wires on -/

theorem comm337_ge5 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (c₁ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x))) (mc N .hg [0, 1] (colOn 2 N y)) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
  refine sep_reduce (P := fun x y => Comm (m + 5) (bA (m + 5) x c₁)
    (mc (m + 5) .hg [0, 1] (colOn 2 (m + 5) y))) ?_ ?_
    (fun x y hx hy => comm337_core m ih x y c₁ hx hy) x y hxy
  · intro x y j hj hjN h
    exact Comm.congr (bA_relabel (m + 5) (by omega) ih x c₁ j hj hjN)
      (hg_relabel (m + 5) (by omega) ih [0, 1] (Or.inl rfl) y j hj hjN)
      (Comm.conj h (swsw _ j hjN))
  · intro x y h
    exact comm_flip h (xAt_inv (m + 5) 2 (by omega)) (bA_flip2 (m + 5) (by omega) x c₁)
      (hg_flip2 (m + 5) (by omega) [0, 1] (by decide) y)

theorem comm338d_ge5 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (c₁ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x))) (mc N .hg [1, 0] (colOn 2 N y)) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
  refine sep_reduce (P := fun x y => Comm (m + 5) (bA (m + 5) x c₁)
    (mc (m + 5) .hg [1, 0] (colOn 2 (m + 5) y))) ?_ ?_
    (fun x y hx hy => comm338_core m ih x y c₁ hx hy) x y hxy
  · intro x y j hj hjN h
    exact Comm.congr (bA_relabel (m + 5) (by omega) ih x c₁ j hj hjN)
      (hg_relabel (m + 5) (by omega) ih [1, 0] (Or.inr rfl) y j hj hjN)
      (Comm.conj h (swsw _ j hjN))
  · intro x y h
    exact comm_flip h (xAt_inv (m + 5) 2 (by omega)) (bA_flip2 (m + 5) (by omega) x c₁)
      (hg_flip2 (m + 5) (by omega) [1, 0] (by decide) y)

end QCert.RealCliffordCH.Sec8.D.N13
