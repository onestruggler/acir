/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (339) from six wires on

The box `A₀` on wire `0` (controls `1` of colour `c₂`, `2` of colour `c₁`,
the wires `3, …` coloured by `x`) commutes with the multi-controlled `H`
`B₀` with its box on wire `1` and its `H` on wire `2` (control `0` of colour
`c₃`, the wires `3, …` coloured by `y`), when `x ≠ y`.

By (307), (313) the colourings may be assumed to differ on wire `3`, black
for `x`, white for `y` (`sep_reduce`); the swap of the wires `2, 3` then
carries the pair to the frame of `E336x`: `A` the box on wire `0` with the
separating control on wire `2` and `c₁` on wire `3`, `B` the
multi-controlled `H` on the wires `1, 3` (`AE`, `BE`).  `A` is expanded by
(320)/(321) (`expX`).  `B` is a box between the swaps and `P ⊗ P` of the
word `M` (`expBE`: three swaps carry it to the wires `0, 1`, (269) writes
it as `P ⊗ P` around the box, and the transposition of the wires `1, 3`
puts the black control of its `H` wire on wire `3`), and that box is
expanded by (320)/(321) too.  The pieces commute pairwise:

* two rotations: one semantic step on the wires `0–3` (`chkRR339`);
* a rotation of `A` against the remainder of `B`: the remainder conjugated
  by `M` is the box on wire `1` idle on wire `3` (`remB`, through (276) in
  the middle), and this is (318)/(319) as in `E336x` (`commRBs`);
* the remainders: two boxes idle on wire `3` (`commBBs`);
* the remainder of `A` against a rotation of `B` conjugated by `M`: the
  remainder is idle on wire `3`; it is expanded once more with the triple
  `1, 2, 4` (a semantic step without wire `3`), its rotations pass the
  conjugated rotation by completeness on the five wires `0–4` (`Loc5.loc5`,
  hence six wires at least) and its remainder by a semantic step without
  wire `4` (`chkBR339`).

Status: not yet built at the time of writing (the build queue was full); nothing imports it.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E337
import QCert.RealCliffordCH.Sec8.D.N13.Loc5

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-! ## Relabeling by one swap -/

/-- Naturality of boxes and multi-controlled `H` under one swap, any wires
(`E.mcSwapBH`, from (307), (313)). -/
theorem swBH {N : ℕ} (ih : IH N) (j : ℕ) (hj : j + 2 ≤ N) (K : Kind) (hK : K = .box ∨ K = .hg)
    (tg tg' : List ℕ) (c c' : ℕ → Option Bool) (htg : tg.length = kindSp K) (hnd : tg.Nodup)
    (htN : ∀ t ∈ tg, t < N) (ht' : tg.map (Net.tau j) = tg')
    (hc : ∀ i < N, c (Net.tau j i) = c' i) :
    Derivable (theory N) (swAt N j * mc N K tg c * swAt N j) (mc N K tg' c') := by
  have h := E.mcSwapBH ih j hj K hK tg c htg hnd htN
  rw [ht', show drawn [swAt N j, mc N K tg c, swAt N j] = swAt N j * mc N K tg c * swAt N j by
    simp [drawn, mul_assoc]] at h
  exact h.trans (der_of_eq (mc_congr _ _ _ hc))

/-! ## The gates in the frame -/

/-- The colours of the box in the frame. -/
def xE (c₁ c₂ : Bool) (x : ℕ → Bool) : ℕ → Bool :=
  fun i => if i = 1 then c₂ else if i = 2 then true else if i = 3 then c₁ else x i

/-- The colours of the box inside the multi-controlled `H`, after the
transposition of the wires `1, 3`. -/
def yS (c₃ : Bool) (y : ℕ → Bool) : ℕ → Bool :=
  fun i => if i = 1 then false else if i = 2 then c₃ else if i = 3 then true else y i

/-- The colours of the box inside the multi-controlled `H` on the wires `0, 1`. -/
def yH (c₃ : Bool) (y : ℕ → Bool) : ℕ → Bool :=
  fun i => if i = 2 then c₃ else if i = 3 then false else y i

/-- Pointwise equality of control functions on the wires `0, …, 4` and above. -/
macro "ctl_case" : tactic => `(tactic| (intro i hi; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨
  i = 3 ∨ i = 4 ∨ 5 ≤ i) with rfl | rfl | rfl | rfl | rfl | h5 <;>
  simp only [colOn, ctlOr, ctlAt, yH, yS, xE, ctlX, Net.tau] <;> (try split_ifs) <;>
  first | rfl | (exfalso; omega) | simp_all | omega))

/-- The multi-controlled `H` of (339) in the frame. -/
abbrev BE (N : ℕ) (c₃ : Bool) (y : ℕ → Bool) : Circ N :=
  mc N .hg [1, 3] (ctlOr (ctlAt 0 c₃) (ctlOr (ctlAt 2 false) (colOn 4 N y)))

/-- The swaps and `P ⊗ P` carrying the box inside `BE` to the frame:
`M = S₀ S₂ S₁ (P ⊗ P) S₁ S₂ S₁` and its reverse `M'`. -/
def mL : List Lt :=
  [.s (.S 1), .s (.S 2), .s (.S 1)] ++ N13.ppL ++ [.s (.S 1), .s (.S 2), .s (.S 0)]
def mL' : List Lt :=
  [.s (.S 0), .s (.S 2), .s (.S 1)] ++ N13.ppL ++ [.s (.S 1), .s (.S 2), .s (.S 1)]

theorem wc_three (K N : ℕ) (a b c : Lt) :
    wc K N [a, b, c] = c.circ K N * b.circ K N * a.circ K N := by
  simp [wc, drawn, mul_assoc]

theorem circ_S (K N j : ℕ) : (Lt.s (L.S j)).circ K N = swAt N j := rfl

/-- `M X M'` written out. -/
theorem mL_conj (m : ℕ) (X : Circ (m + 6)) :
    wc 4 (m + 6) mL * X * wc 4 (m + 6) mL' =
      swAt (m + 6) 0 * (swAt (m + 6) 2 * (swAt (m + 6) 1 * ((pp : Circ (m + 6)) *
        (swAt (m + 6) 1 * (swAt (m + 6) 2 * (swAt (m + 6) 1 * X * swAt (m + 6) 1) *
          swAt (m + 6) 2) * swAt (m + 6) 1) * pp) * swAt (m + 6) 1) * swAt (m + 6) 2) *
        swAt (m + 6) 0 := by
  have ep : wc 4 (m + 6) N13.ppL = (pp : Circ (m + 6)) := wc_ppL (m + 1)
  simp only [mL, mL', wc_append, ep, wc_three, circ_S, mul_assoc]

theorem wc5_mL (N : ℕ) : wc 5 N mL = wc 4 N mL := rfl
theorem wc5_mL' (N : ℕ) : wc 5 N mL' = wc 4 N mL' := rfl

theorem chkMM : check 4 [] (mL ++ mL') [] [.sem 0 32 [] 4] = true ∧
    check 4 [] (mL' ++ mL) [] [.sem 0 32 [] 4] = true := by
  decide +kernel

theorem MM_inv (m : ℕ) (ih : IH (m + 6)) :
    Derivable (theory (m + 6)) (wc 4 (m + 6) mL' * wc 4 (m + 6) mL) 1 ∧
    Derivable (theory (m + 6)) (wc 4 (m + 6) mL * wc 4 (m + 6) mL') 1 := by
  have h1 := check_sound (m := m + 1) (frame 4) ih (allD_nil 5 (m + 1)) chkMM.1
  have h2 := check_sound (m := m + 1) (frame 4) ih (allD_nil 5 (m + 1)) chkMM.2
  rw [wc_append, wc5_mL, wc5_mL'] at h1 h2
  exact ⟨h1, h2⟩


/-! ## `P ⊗ P` on the box wire and an idle wire: (276) -/

/-- (276) for the box on wire `0`, wire `1` idle, the wires `2, …` coloured by
`yH c₃ y`: from `N8.s276` (box wire `1`, wire `0` idle) read on two local
wires, coloured, and conjugated by the swap of the wires `0, 1`. -/
theorem pp_box276 (m : ℕ) (ih : IH (m + 6)) (c₃ : Bool) (y : ℕ → Bool) :
    Derivable (theory (m + 6))
      ((pp : Circ (m + 6)) * mc (m + 6) .box [0] (colOn 2 (m + 6) (yH c₃ y)) * pp)
      (mc (m + 6) .box [0] (colOn 2 (m + 6) (yH c₃ y))) := by
  have h0 : Derivable (theory (m + 6)) (wc 5 (m + 6) (N8.ppL 0 ++ [B1] ++ N8.ppL 0))
      (wc 5 (m + 6) [B1]) := s276 (m + 1) ih
  rw [B1_eq] at h0
  have eB : (Lt.g .box [1] [(2, true), (3, true), (4, true)] true).circ 5 (m + 6) =
      (Lt.g .box [1] [] true).circ 2 (m + 6) :=
    mc_congr _ _ _ (by ctl_tac)
  have ep : ∀ K, wc K (m + 6) (N8.ppL 0) = (pp : Circ (m + 6)) := fun _ => rfl
  have h2 : Derivable (theory (m + 6))
      (wc 2 (m + 6) (N8.ppL 0 ++ [Lt.g .box [1] [] true] ++ N8.ppL 0))
      (wc 2 (m + 6) [Lt.g .box [1] [] true]) := by
    simp only [wc_append, wc_one', ep] at h0 ⊢
    rwa [eB] at h0
  have hc := colour_wc (K := 2) (N := m + 6) (by omega) (yH c₃ y)
    (l := N8.ppL 0 ++ [Lt.g .box [1] [] true] ++ N8.ppL 0)
    (r := [Lt.g .box [1] [] true]) (by decide) (by decide) h2
  have eY : cX 2 (m + 6) (yH c₃ y) (Lt.g .box [1] [] true) =
      mc (m + 6) .box [1] (colOn 2 (m + 6) (yH c₃ y)) := by
    show mc _ _ _ _ = _
    refine mc_congr _ _ _ (fun i hi => ?_)
    simp only [ctlX, colOn]
    split_ifs <;> first | rfl | omega
  have eL : wcX 2 (m + 6) (yH c₃ y) (N8.ppL 0 ++ [Lt.g .box [1] [] true] ++ N8.ppL 0) =
      (pp : Circ (m + 6)) * mc (m + 6) .box [1] (colOn 2 (m + 6) (yH c₃ y)) * pp := by
    unfold wcX
    simp only [List.map_append, drawn_append, List.map_singleton, drawn_one, eY]
    rfl
  have eR : wcX 2 (m + 6) (yH c₃ y) [Lt.g .box [1] [] true] =
      mc (m + 6) .box [1] (colOn 2 (m + 6) (yH c₃ y)) := by
    unfold wcX
    rw [List.map_singleton, drawn_one, eY]
  rw [eL, eR] at hc
  have eS := swBH ih 0 (by omega) .box (Or.inl rfl) [1] [0] (colOn 2 (m + 6) (yH c₃ y))
    (colOn 2 (m + 6) (yH c₃ y)) rfl (by decide) (by intro t ht; simp at ht; omega) rfl (fun i hi => by
      rcases i with _ | _ | i <;> simp [colOn, Net.tau])
  have hp := pp_swap4 (m + 2) ih
  exact (pp_move_swap hp eS).symm.trans ((dctx _ _ hc).trans eS)

/-! ## The expansions -/

/-- The multi-controlled `H` of the frame between the swaps and `P ⊗ P` of
`M`: the box with its controls `1` (white), `2` (`c₃`), `3` (black, its `H`
wire). -/
theorem expBE (m : ℕ) (ih : IH (m + 6)) (c₃ : Bool) (y : ℕ → Bool) :
    Derivable (theory (m + 6)) (BE (m + 6) c₃ y)
      (wc 4 (m + 6) mL * mc (m + 6) .box [0] (colOn 1 (m + 6) (yS c₃ y)) *
        wc 4 (m + 6) mL') := by
  rw [mL_conj]
  have s0 := swBH ih 0 (by omega) .hg (Or.inr rfl) [0, 3] [1, 3]
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y)))
    (ctlOr (ctlAt 0 c₃) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y))) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case)
  have s2 := swBH ih 2 (by omega) .hg (Or.inr rfl) [0, 2] [0, 3]
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 3 false) (colOn 4 (m + 6) y)))
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y))) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case)
  have s1 := swBH ih 1 (by omega) .hg (Or.inr rfl) [0, 1] [0, 2]
    (colOn 2 (m + 6) (yH c₃ y))
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 3 false) (colOn 4 (m + 6) y))) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case)
  have hp : Derivable (theory (m + 6)) (mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) (yH c₃ y)))
      ((pp : Circ (m + 6)) * bA (m + 6) (yH c₃ y) true * pp) := hg0_box4 (m + 2) (yH c₃ y)
  have t1 := swBH ih 1 (by omega) .box (Or.inl rfl) [0] [0]
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 2 true) (ctlOr (ctlAt 3 false) (colOn 4 (m + 6) y))))
    (ctlOr (ctlAt 1 true) (colOn 2 (m + 6) (yH c₃ y))) rfl (by decide) (by intro t ht; simp at ht; omega) rfl
    (by ctl_case)
  have t2 := swBH ih 2 (by omega) .box (Or.inl rfl) [0] [0]
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 2 false) (ctlOr (ctlAt 3 true) (colOn 4 (m + 6) y))))
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 2 true) (ctlOr (ctlAt 3 false) (colOn 4 (m + 6) y))))
    rfl (by decide) (by intro t ht; simp at ht; omega) rfl (by ctl_case)
  have t3 := swBH ih 1 (by omega) .box (Or.inl rfl) [0] [0] (colOn 1 (m + 6) (yS c₃ y))
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 2 false) (ctlOr (ctlAt 3 true) (colOn 4 (m + 6) y))))
    rfl (by decide) (by intro t ht; simp at ht; omega) rfl
    (by ctl_case)
  have k1 := hp.trans (dctx _ _ (t1.symm.trans (dctx _ _ (t2.symm.trans (dctx _ _ t3.symm)))))
  exact s0.symm.trans (dctx _ _ (s2.symm.trans (dctx _ _ (s1.symm.trans (dctx _ _ k1)))))

/-- The remainder of the expansion inside the multi-controlled `H`,
conjugated back by `M`: the box on wire `1`, idle on wire `3`. -/
theorem remB (m : ℕ) (ih : IH (m + 6)) (c₃ : Bool) (y : ℕ → Bool) :
    Derivable (theory (m + 6))
      (wc 4 (m + 6) mL * boxN (m + 6) (yS c₃ y) false c₃ * wc 4 (m + 6) mL')
      (swAt (m + 6) 0 * boxN (m + 6) y c₃ false * swAt (m + 6) 0) := by
  rw [mL_conj]
  have hs1 := swsw (m + 6) 1 (by omega)
  have hs2 := swsw (m + 6) 2 (by omega)
  have r1 := swBH ih 1 (by omega) .box (Or.inl rfl) [0] [0]
    (ctlOr (ctlAt 1 false) (ctlOr (ctlAt 2 c₃) (colOn 4 (m + 6) (yS c₃ y))))
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y))) rfl (by decide) (by intro t ht; simp at ht; omega)
    rfl (by ctl_case)
  have r2 := swBH ih 2 (by omega) .box (Or.inl rfl) [0] [0]
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y)))
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 3 false) (colOn 4 (m + 6) y))) rfl (by decide) (by intro t ht; simp at ht; omega)
    rfl (by ctl_case)
  have r3 := swBH ih 1 (by omega) .box (Or.inl rfl) [0] [0]
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 3 false) (colOn 4 (m + 6) y)))
    (colOn 2 (m + 6) (yH c₃ y)) rfl (by decide) (by intro t ht; simp at ht; omega) rfl
    (by ctl_case)
  have a2 := (dctx _ _ r1).trans r2
  have a3 := (dctx _ _ a2).trans r3
  have a4 := (dctx _ _ a3).trans (pp_box276 m ih c₃ y)
  have a5 := (dctx _ _ a4).trans (conj_back hs1 r3)
  have a6 := (dctx _ _ a5).trans (conj_back hs2 r2)
  exact dctx _ _ a6

/-! ## Two rotations: one semantic step on the wires `0–3` -/

theorem chkRR339 : ∀ b1 b3 c3 : Bool, ∀ r ∈ rots b1 true b3, ∀ r' ∈ rots false c3 true,
    check 4 [] ([r] ++ mL' ++ [r'] ++ mL) (mL' ++ [r'] ++ mL ++ [r])
      [.sem 0 34 (mL' ++ [r'] ++ mL ++ [r]) 4] = true := by
  decide +kernel

theorem commRR339 (m : ℕ) (ih : IH (m + 6)) {b1 b3 c3 : Bool} {r r' : Lt}
    (hr : r ∈ rots b1 true b3) (hr' : r' ∈ rots false c3 true) :
    Comm (m + 6) (r.circ 4 (m + 6))
      (wc 4 (m + 6) mL * r'.circ 4 (m + 6) * wc 4 (m + 6) mL') := by
  have h := check_sound (m := m + 1) (frame 4) ih (allD_nil 5 (m + 1))
    (chkRR339 b1 b3 c3 r hr r' hr')
  simp only [wc_append, wc_one', wc5_mL, wc5_mL', rots_rebase hr, rots_rebase hr'] at h
  unfold Comm
  rw [drawn_two, drawn_two]
  simpa only [mul_assoc] using h

/-! ## The remainder of the box against a rotation of the multi-controlled `H` -/

/-- The remainder of the box, with its control on wire `4` explicit. -/
def G4 (c b : Bool) : Lt := .g .box [0] [(1, c), (2, true), (4, b)] true
/-- Its expansion by (320)/(321) with the triple `1, 2, 4` (idle on wire `3`). -/
def Q1 (c b : Bool) : Lt := .g .zx [0] [(1, c), (2, true), (4, b)] false
def Q2 (c b : Bool) : Lt := .g (Kind.sgnZX (!c)) [1] [(0, true), (2, true), (4, b)] false
def Q3 (c : Bool) : Lt := .g .box [0] [(1, c), (2, true)] true
def Q4 (c b : Bool) : Lt := .g (Kind.sgnZX c) [1] [(0, true), (2, true), (4, b)] false
def Q5 (c b : Bool) : Lt := .g .xz [0] [(1, c), (2, true), (4, b)] false
def qs (c b : Bool) : List Lt := [Q1 c b, Q2 c b, Q3 c, Q4 c b, Q5 c b, Q2 c b, Q3 c, Q4 c b]

/-- A rotation of the multi-controlled `H` between `M` and its reverse. -/
def RW (r : Lt) : List Lt := mL' ++ [r] ++ mL

/-- The five-wire steps of the run: a piece of the expansion against `R`. -/
def TG (c b : Bool) (R : List Lt) : SE.Tbl :=
  [([Q1 c b] ++ R, R ++ [Q1 c b]), ([Q2 c b] ++ R, R ++ [Q2 c b]),
   ([Q4 c b] ++ R, R ++ [Q4 c b]), ([Q5 c b] ++ R, R ++ [Q5 c b])]

/-- The run carrying `R` across `G4`: expand `G4` (a semantic step without
wire `3`), carry `R` across the eight pieces (the table, or a semantic step
without wire `4` for the remainder `Q3`), fold the expansion back. -/
def runG (c b : Bool) (R : List Lt) : List St :=
  [.sem 0 1 (qs c b) 3, .rw 7 2 false, .sem 6 (R.length + 1) (R ++ [Q3 c]) 4, .rw 5 1 false,
   .rw 4 3 false, .rw 3 2 false, .sem 2 (R.length + 1) (R ++ [Q3 c]) 4, .rw 1 1 false,
   .rw 0 0 false, .sem R.length 8 [G4 c b] 3]

theorem G4_ok (c b : Bool) : (G4 c b).ok 5 = true := by cases c <;> cases b <;> rfl

theorem cX_loc {K N : ℕ} (z : ℕ → Bool) {g : Lt} (hg : isLoc K g = true) :
    cX K N z g = g.circ K N := by
  cases g with
  | s l => rfl
  | g Kd tg cs bb =>
    simp only [isLoc, Bool.and_eq_true, Bool.not_eq_true'] at hg
    obtain ⟨_, rfl⟩ := hg
    rfl

/-- A word `R` of local letters avoiding wire `4` passes the box `G4 c b`
(idle on wire `3`, the wires `5, …` coloured by `z`) once the run `runG` and
its four five-wire steps are decided: from six wires on. -/
theorem gcl (m : ℕ) (ih : IH (m + 6)) (z : ℕ → Bool) (c b : Bool) (R : List Lt)
    (hrun : check 4 (TG c b R) ([G4 c b] ++ R) (R ++ [G4 c b]) (runG c b R) = true)
    (htab : ∀ e ∈ TG c b R, e.1.all (isLoc 5) = true ∧ e.2.all (isLoc 5) = true ∧
      SE.lcheck 5 true e.1 e.2 = true)
    (hR : R.all (isLoc 5) = true) :
    Derivable (theory (m + 6)) (wc 5 (m + 6) R * cX 5 (m + 6) z (G4 c b))
      (cX 5 (m + 6) z (G4 c b) * wc 5 (m + 6) R) := by
  have hT : AllD 5 (m + 1) (TG c b R) := fun e he => by
    obtain ⟨h1, h2, h3⟩ := htab e he
    exact loc5 h1 h2 h3 (by omega) ih
  have h := check_sound (m := m + 1) (frame 4) ih hT hrun
  have hRok : ∀ g ∈ R, g.ok 5 = true := fun g hg => isLoc_ok (List.all_eq_true.1 hR g hg)
  have hl : ∀ g ∈ [G4 c b] ++ R, g.ok 5 = true := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · rw [List.mem_singleton.1 hg]; exact G4_ok c b
    · exact hRok g hg
  have hr : ∀ g ∈ R ++ [G4 c b], g.ok 5 = true := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hRok g hg
    · rw [List.mem_singleton.1 hg]; exact G4_ok c b
  have hc := colour_wc (K := 5) (N := m + 6) (by omega) z hl hr h
  have eR : drawn (R.map (cX 5 (m + 6) z)) = wc 5 (m + 6) R := by
    unfold wc
    congr 1
    exact List.map_congr_left (fun g hg => cX_loc z (List.all_eq_true.1 hR g hg))
  simp only [wcX, List.map_append, drawn_append, List.map_singleton, drawn_one, eR] at hc
  exact hc

theorem chkBR339 : ∀ c b c3 : Bool, ∀ r ∈ rots false c3 true,
    check 4 (TG c b (RW r)) ([G4 c b] ++ RW r) (RW r ++ [G4 c b]) (runG c b (RW r)) = true := by
  decide +kernel

theorem chkTBR : ∀ c b c3 : Bool, ∀ r ∈ rots false c3 true, ∀ e ∈ TG c b (RW r),
    e.1.all (isLoc 5) = true ∧ e.2.all (isLoc 5) = true ∧ SE.lcheck 5 true e.1 e.2 = true := by
  decide +kernel

theorem RW_loc : ∀ c3 : Bool, ∀ r ∈ rots false c3 true, (RW r).all (isLoc 5) = true := by
  decide

theorem commBR339 (m : ℕ) (ih : IH (m + 6)) (x : ℕ → Bool) (c₁ c₂ c3 : Bool) {r : Lt}
    (hr : r ∈ rots false c3 true) :
    Comm (m + 6) (boxN (m + 6) (xE c₁ c₂ x) c₂ true)
      (wc 4 (m + 6) mL * r.circ 4 (m + 6) * wc 4 (m + 6) mL') := by
  have h := gcl m ih x c₂ (x 4) (RW r) (chkBR339 c₂ (x 4) c3 r hr)
    (chkTBR c₂ (x 4) c3 r hr) (RW_loc c3 r hr)
  have eG : cX 5 (m + 6) x (G4 c₂ (x 4)) = boxN (m + 6) (xE c₁ c₂ x) c₂ true := by
    show mc _ _ _ _ = _
    refine mc_congr _ _ _ (fun i hi => ?_)
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ 5 ≤ i) with
      rfl | rfl | rfl | rfl | rfl | h5
    all_goals (simp only [ctlX, ctlOr, ctlAt, colOn, xE]; split_ifs <;>
      first | rfl | (exfalso; omega) | simp_all | omega)
  simp only [RW, wc_append, wc_one', wc5_mL, wc5_mL', rots_rebase hr, eG] at h
  unfold Comm
  rw [drawn_two, drawn_two]
  simpa only [mul_assoc] using h

/-! ## The pairs and the core -/

theorem pairs339 (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ c₃ : Bool) :
    ∀ a ∈ (pcs4 c₂ true c₁).map (cX 4 (m + 6) (xE c₁ c₂ x)),
      ∀ b ∈ ((pcs4 false c₃ true).map (cX 4 (m + 6) (yS c₃ y))).map
        (fun a => wc 4 (m + 6) mL * a * wc 4 (m + 6) mL'), Comm (m + 6) a b := by
  intro a ha b hb
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hb'
  rcases pcs4_cls hg with hr | rfl <;> rcases pcs4_cls hg' with hr' | rfl
  · rw [rots_cX hr, rots_cX hr']
    exact commRR339 m ih hr hr'
  · rw [rots_cX hr, P3'_cX]
    exact Comm.congr (Derivable.refl _) (remB m ih c₃ y).symm
      (commRBs (m + 1) ih c₂ c₁ c₃ y hr)
  · rw [P3'_cX, rots_cX hr']
    exact commBR339 m ih x c₁ c₂ c₃ hr'
  · rw [P3'_cX, P3'_cX]
    exact Comm.congr (Derivable.refl _) (remB m ih c₃ y).symm
      (commBBs (m + 1) ih c₂ c₃ (xE c₁ c₂ x) y)

/-- (339) in the frame: the box on wire `0` black on wire `2`, the
multi-controlled `H` on the wires `1, 3` white on wire `2`. -/
theorem comm339E (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ c₃ : Bool) :
    Comm (m + 6) (mc (m + 6) .box [0] (colOn 1 (m + 6) (xE c₁ c₂ x))) (BE (m + 6) c₃ y) := by
  have ex : Derivable (theory (m + 6)) (mc (m + 6) .box [0] (colOn 1 (m + 6) (xE c₁ c₂ x)))
      (wcX 4 (m + 6) (xE c₁ c₂ x) (pcs4 c₂ true c₁)) := expX (m + 6) (by omega) ih (xE c₁ c₂ x)
  have eS : Derivable (theory (m + 6)) (mc (m + 6) .box [0] (colOn 1 (m + 6) (yS c₃ y)))
      (wcX 4 (m + 6) (yS c₃ y) (pcs4 false c₃ true)) := expX (m + 6) (by omega) ih (yS c₃ y)
  have hMM := MM_inv m ih
  have eB : Derivable (theory (m + 6)) (BE (m + 6) c₃ y)
      (drawn (((pcs4 false c₃ true).map (cX 4 (m + 6) (yS c₃ y))).map
        (fun a => wc 4 (m + 6) mL * a * wc 4 (m + 6) mL'))) :=
    (expBE m ih c₃ y).trans ((dright _ (dleft _ eS)).trans (conj_drawn hMM.1 hMM.2 _))
  exact Comm.congr ex.symm eB.symm (comm_drawn _ _ (pairs339 m ih x y c₁ c₂ c₃))

/-! ## Back to the interface -/

/-- The controls of the box of (339). -/
abbrev cA339 (N : ℕ) (x : ℕ → Bool) (c₁ c₂ : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 N x))
/-- The controls of the multi-controlled `H` of (339). -/
abbrev cB339 (N : ℕ) (y : ℕ → Bool) (c₃ : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt 0 c₃) (colOn 3 N y)

/-- (339) when the colourings are black, resp. white, on wire `3`. -/
theorem comm339_core (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ c₃ : Bool)
    (hx : x 3 = true) (hy : y 3 = false) :
    Comm (m + 6) (mc (m + 6) .box [0] (cA339 (m + 6) x c₁ c₂))
      (mc (m + 6) .hg [1, 2] (cB339 (m + 6) y c₃)) := by
  have hA := swBH ih 2 (by omega) .box (Or.inl rfl) [0] [0] (colOn 1 (m + 6) (xE c₁ c₂ x))
    (cA339 (m + 6) x c₁ c₂) rfl (by decide) (by intro t ht; simp at ht; omega) rfl (fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h4
      all_goals (simp only [cA339, colOn, ctlOr, ctlAt, xE, Net.tau]; split_ifs <;>
        first | rfl | (exfalso; omega) | simp_all | omega))
  have hB := swBH ih 2 (by omega) .hg (Or.inr rfl) [1, 3] [1, 2]
    (ctlOr (ctlAt 0 c₃) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y))) (cB339 (m + 6) y c₃) rfl
    (by decide) (by intro t ht; simp at ht; omega) rfl (fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h4
      all_goals (simp only [cB339, colOn, ctlOr, ctlAt, Net.tau]; split_ifs <;>
        first | rfl | (exfalso; omega) | simp_all | omega))
  exact comm_flip (comm339E m ih x y c₁ c₂ c₃) (swsw (m + 6) 2 (by omega)) hA hB

/-- (339) from six wires on. -/
theorem comm339_ge6 (N : ℕ) (hN : 6 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ c₃ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 N x))))
      (mc N .hg [1, 2] (ctlOr (ctlAt 0 c₃) (colOn 3 N y))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 6 := ⟨N - 6, by omega⟩
  refine sep_reduce (P := fun x y => Comm (m + 6) (mc (m + 6) .box [0] (cA339 (m + 6) x c₁ c₂))
    (mc (m + 6) .hg [1, 2] (cB339 (m + 6) y c₃))) ?_ ?_
    (fun x y hx hy => comm339_core m ih x y c₁ c₂ c₃ hx hy) x y hxy
  · intro x y j hj hjN h
    have rA := swBH ih j hjN .box (Or.inl rfl) [0] [0] (cA339 (m + 6) (x ∘ Net.tau j) c₁ c₂)
      (cA339 (m + 6) x c₁ c₂) rfl (by decide) (by intro t ht; simp at ht; omega)
      (by simp only [List.map_cons, List.map_nil, Net.tau]; split_ifs <;> first | rfl | omega)
      (fun i hi => by
        simp only [cA339, ctlOr, ctlAt_tau (show 2 < j by omega), ctlAt_tau (show 1 < j by omega),
          colOn_tau (show 3 ≤ j by omega) hjN x hi])
    have rB := swBH ih j hjN .hg (Or.inr rfl) [1, 2] [1, 2] (cB339 (m + 6) (y ∘ Net.tau j) c₃)
      (cB339 (m + 6) y c₃) rfl (by decide) (by intro t ht; simp at ht; omega)
      (by simp only [List.map_cons, List.map_nil, Net.tau]; split_ifs <;> first | rfl | omega)
      (fun i hi => by
        simp only [cB339, ctlOr, ctlAt_tau (show 0 < j by omega),
          colOn_tau (show 3 ≤ j by omega) hjN y hi])
    exact Comm.congr rA rB (Comm.conj h (swsw _ j hjN))
  · intro x y h
    have hx := xAt_inv (m + 6) 3 (by omega)
    refine comm_flip h hx ?_ ?_
    · have e := eq81 (m + 6) .box [0] (cA339 (m + 6) (flipAt 3 x) c₁ c₂) 3 (flipAt 3 x 3)
        (by omega) (by decide) (by simp [cA339, ctlOr, ctlAt, colOn])
      rw [show drawn [xAt (m + 6) 3, mc (m + 6) .box [0] (cA339 (m + 6) (flipAt 3 x) c₁ c₂),
          xAt (m + 6) 3] = xAt (m + 6) 3 * mc (m + 6) .box [0] (cA339 (m + 6) (flipAt 3 x) c₁ c₂) *
          xAt (m + 6) 3 by simp [drawn, mul_assoc]] at e
      refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
      have := colOn_flip (lo := 3) (N := m + 6) (by omega) x i
      simp only [cA339, setCtl, ctlOr, ctlAt] at this ⊢
      split_ifs at this ⊢ <;> simp_all
    · have e := eq81 (m + 6) .hg [1, 2] (cB339 (m + 6) (flipAt 3 y) c₃) 3 (flipAt 3 y 3)
        (by omega) (by decide) (by simp [cB339, ctlOr, ctlAt, colOn])
      rw [show drawn [xAt (m + 6) 3, mc (m + 6) .hg [1, 2] (cB339 (m + 6) (flipAt 3 y) c₃),
          xAt (m + 6) 3] = xAt (m + 6) 3 * mc (m + 6) .hg [1, 2] (cB339 (m + 6) (flipAt 3 y) c₃) *
          xAt (m + 6) 3 by simp [drawn, mul_assoc]] at e
      refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
      have := colOn_flip (lo := 3) (N := m + 6) (by omega) y i
      simp only [cB339, setCtl, ctlOr, ctlAt] at this ⊢
      split_ifs at this ⊢ <;> simp_all

end QCert.RealCliffordCH.Sec8.D.N13
