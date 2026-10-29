/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (339) from six wires on: the frame and the tools

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

Status: not built.  Its decided steps need too much memory as written (one
declaration of four runs in `E337r1` passed 4.7 GB; `E322`, imported through
`E322x`, needs about 11 GB): see `HANDOVER.md` before building.  Nothing
imports it.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E337
import QCert.RealCliffordCH.Sec8.D.N13.Loc5

set_option Elab.async false

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

theorem chkMM1 : check 4 [] (mL ++ mL') [] [.sem 0 32 [] 4] = true := by
  decide +kernel

theorem chkMM2 : check 4 [] (mL' ++ mL) [] [.sem 0 32 [] 4] = true := by
  decide +kernel

theorem chkMM : check 4 [] (mL ++ mL') [] [.sem 0 32 [] 4] = true ∧
    check 4 [] (mL' ++ mL) [] [.sem 0 32 [] 4] = true := ⟨chkMM1, chkMM2⟩

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

set_option maxHeartbeats 2000000 in
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

/-- Conjugates of inverse circuits are inverse. -/
theorem conj_inv2 {N : ℕ} {P Q a b : Circ N} (hQP : Derivable (theory N) (Q * P) 1)
    (hPQ : Derivable (theory N) (P * Q) 1) (h : Derivable (theory N) (a * b) 1) :
    Derivable (theory N) ((P * a * Q) * (P * b * Q)) 1 := by
  have e : P * a * Q * (P * b * Q) = P * a * (Q * P) * (b * Q) := by simp only [mul_assoc]
  rw [e]
  refine (dright _ (dleft _ hQP)).trans ?_
  rw [mul_one]
  have e2 : P * a * (b * Q) = P * (a * b) * Q := by simp only [mul_assoc]
  rw [e2]
  refine (dctx P Q h).trans ?_
  rw [mul_one]
  exact hPQ

/-- A base case and inverses: commutation for every rotation. -/
theorem comm_basesC {N : ℕ} {P Q A0 A A1 A' : Circ N} (hQP : Derivable (theory N) (Q * P) 1)
    (hPQ : Derivable (theory N) (P * Q) 1) (h : Comm N A0 (P * A1 * Q))
    (e0 : A = A0 ∨ (Derivable (theory N) (A0 * A) 1 ∧ Derivable (theory N) (A * A0) 1))
    (e1 : A' = A1 ∨ (Derivable (theory N) (A1 * A') 1 ∧ Derivable (theory N) (A' * A1) 1)) :
    Comm N A (P * A' * Q) := by
  have h' : Comm N A0 (P * A' * Q) := by
    rcases e1 with rfl | ⟨i1, i2⟩
    · exact h
    · exact comm_inv_r h (conj_inv2 hQP hPQ i1) (conj_inv2 hQP hPQ i2)
  rcases e0 with rfl | ⟨i1, i2⟩
  · exact h'
  · exact Comm.inv h' i1 i2

theorem base_circ {K N : ℕ} {r r0 : Lt} {X : Prop} (e : r = r0 ∨ X) :
    r.circ K N = r0.circ K N ∨ X :=
  e.imp (fun h => by rw [h]) id

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

theorem RW_loc : ∀ c3 : Bool, ∀ r ∈ rots2 false c3 true, (RW r).all (isLoc 5) = true := by
  decide

end QCert.RealCliffordCH.Sec8.D.N13
