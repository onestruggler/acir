/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The cases of Lemmas D.9 and D.11 at the canonical position

On five local wires, the generators that touch the box wire, against the box
(Lemma D.9, (308)) and against the multi-controlled `H` (Lemma D.11, (314)),
at the position where nothing else is left to do (box wire `0`, or `1` with
wire `0` idle):

* box: `Z` and `H` on the box wire are (19) and (285); `CZ` and `CH` of the
  wires `0, 1` against the box on wire `1` are (272) and (280) once (274)
  moves the box wire (`sCB1`, `sKB1`);
* multi-controlled `H` (box wire `0`, `H` on wire `1`): it is `P ⊗ P`, the
  box, `P ⊗ P` (`HgPP.hgPP`), and `P ⊗ P` exchanges `H` and `Z` on wire `0`
  (Lemma 5.1), so `H` and `Z` on the box wire pass by (19) and (285)
  (`s303`, `sZhg`; (303) is the first);
* multi-controlled `H` with box wire `1`, `H` on wire `2`, wire `0` idle: by
  (277) its box wire moves to wire `0`, where it is `P ⊗ P` on the wires
  `0, 2` around the box `B0`, and that `P ⊗ P` exchanges the `CZ` and the
  `CH` of the wires `0, 1` (Lemma 5.1), which pass `B0` by (280) and (272)
  (`s282`, `sKhg`; (282) is the first).
-/
import QCert.RealCliffordCH.Sec8.D.N8.S290
import QCert.RealCliffordCH.Sec8.D.N8.HgPP
import QCert.RealCliffordCH.Sec8.D.N8.I274

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

abbrev lZ0 : Lt := .s (.Z 0)

/-! ## The box -/

def TCB1 : SE.Tbl := [([B1], [B0]), ([lC0, B0], [B0, lC0])]

theorem TCB1_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m TCB1 := by
  intro e he
  simp only [TCB1, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact s274 m ih
  · exact s272 m ih

theorem runCB1 : check 4 TCB1 [lC0, B1] [B1, lC0] [.rw 1 0 false, .rw 0 1 false, .rw 0 0 true] = true := by
  decide +kernel

/-- `CZ` of the wires `0, 1` passes the box on wire `1` (wire `0` idle). -/
theorem sCB1 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [lC0, B1]) (wc 5 (m + 5) [B1, lC0]) :=
  check_sound (frame 4) ih (TCB1_ok m ih) runCB1

def TKB1 : SE.Tbl := [([B1], [B0]), ([lK0, B0], [B0, lK0])]

theorem TKB1_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m TKB1 := by
  intro e he
  simp only [TKB1, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact s274 m ih
  · exact s280 m ih

theorem runKB1 : check 4 TKB1 [lK0, B1] [B1, lK0] [.rw 1 0 false, .rw 0 1 false, .rw 0 0 true] = true := by
  decide +kernel

/-- `CH` from wire `1` onto wire `0` passes the box on wire `1` (wire `0`
idle). -/
theorem sKB1 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [lK0, B1]) (wc 5 (m + 5) [B1, lK0]) :=
  check_sound (frame 4) ih (TKB1_ok m ih) runKB1

/-! ## The multi-controlled `H` as `P ⊗ P`, box, `P ⊗ P` -/

theorem ppL0_eq (m : ℕ) : wc 5 (m + 5) (ppL 0) = ppAt (m + 5) 0 1 := by
  rw [ppAt, placeG_pair _ _ (by omega)]
  show _ = atBot (m + 3 + 2) (pp : Circ 2)
  rw [← pad_atBot2, MS.pad_pp]
  rfl

theorem two_le_length {l : List ℕ} (hl : l.Nodup) {a b : ℕ} (hab : a ≠ b) (ha : a ∈ l)
    (hb : b ∈ l) : 2 ≤ l.length := by
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
  · simp at ha
  · simp at ha hb; omega
  · simp

/-- The multi-controlled `H` letter on the wires `0, 1` with the controls
`cs` (at least two of them, among the wires `2, 3, 4`) and the bulk. -/
theorem hgPP5 (m : ℕ) (cs : List (ℕ × Bool)) (a b : ℕ) (hab : a ≠ b) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (ha5 : a < 5) (hb5 : b < 5) (hal : (cs.lookup a).isSome = true)
    (hbl : (cs.lookup b).isSome = true) (h1 : cs.lookup 1 = none) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [.g .hg [0, 1] cs true])
      (wc 5 (m + 5) (ppL 0 ++ [.g .box [0] ((1, true) :: cs) true] ++ ppL 0)) := by
  have hk : 2 ≤ (ctrlWires (m + 5) [0, 1] (ctl 5 cs true)).length := by
    refine two_le_length ((List.nodup_range).filter _) hab ?_ ?_
    · simp only [ctrlWires, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
        List.contains_cons, List.contains_nil, Bool.or_eq_false_iff]
      refine ⟨by omega, by simp [ctl, ha5, hal], by simp; omega, by simp; omega, trivial⟩
    · simp only [ctrlWires, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
        List.contains_cons, List.contains_nil, Bool.or_eq_false_iff]
      refine ⟨by omega, by simp [ctl, hb5, hbl], by simp; omega, by simp; omega, trivial⟩
  have h := hgPP (m + 5) (by omega) (ctl 5 cs true) hk
  rw [wc_one]
  refine h.trans (der_of_eq ?_)
  rw [wc_append, wc_append, ppL0_eq, wc_one]
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  congr 2
  refine mc_congr _ _ _ (fun i hi => ?_)
  simp only [setCtl, ctl, Lt.circ]
  by_cases hi1 : i = 1
  · subst hi1; simp
  · rw [if_neg hi1]
    by_cases hi5 : i < 5
    · simp [hi5, List.lookup_cons, show (i == 1) = false by simpa using hi1]
    · simp [hi5]

/-- The multi-controlled `H` on the wires `0, 1` with all other wires black. -/
def hgF : Lt := .g .hg [0, 1] [(2, true), (3, true), (4, true)] true

theorem hgPP_F (m : ℕ) : Derivable (theory (m + 5)) (wc 5 (m + 5) [hgF])
    (wc 5 (m + 5) (ppL 0 ++ [bx0] ++ ppL 0)) :=
  hgPP5 m _ 2 3 (by omega) le_rfl (by omega) (by omega) (by omega) rfl rfl rfl

theorem hgPP_01 (m : ℕ) : Derivable (theory (m + 5)) (wc 5 (m + 5) [hg01])
    (wc 5 (m + 5) (ppL 0 ++ [eA] ++ ppL 0)) :=
  hgPP5 m _ 3 4 (by omega) (by omega) (by omega) (by omega) (by omega) rfl rfl rfl

/-! ## Lemma D.11 at the canonical position -/

def T303 : SE.Tbl := [([hgF], ppL 0 ++ [bx0] ++ ppL 0), ([lZ0, bx0], [bx0, lZ0])]

theorem T303_ok (m : ℕ) : AllD 5 m T303 := by
  intro e he
  simp only [T303, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact hgPP_F m
  · exact t19 m

theorem run303 : check 4 T303 [lH0, hgF] [hgF, lH0]
    [.rw 1 0 false, .sem 0 11 (ppL 0 ++ [lZ0]) 4, .rw 10 1 false, .sem 11 11 (ppL 0 ++ [lH0]) 4,
     .rw 0 0 true] = true := by
  decide +kernel

/-- (303) on five local wires: `H` on the box wire passes the
multi-controlled `H`. -/
theorem s303 (m : ℕ) :
    IH (m + 5) → Derivable (theory (m + 5)) (wc 5 (m + 5) [lH0, hgF]) (wc 5 (m + 5) [hgF, lH0]) :=
  fun ih => check_sound (frame 4) ih (T303_ok m) run303

def TZhg : SE.Tbl := [([hgF], ppL 0 ++ [bx0] ++ ppL 0), ([lH0, bx0], [bx0, lH0])]

theorem TZhg_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m TZhg := by
  intro e he
  simp only [TZhg, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact hgPP_F m
  · exact s285 m ih

theorem runZhg : check 4 TZhg [lZ0, hgF] [hgF, lZ0]
    [.rw 1 0 false, .sem 0 11 (ppL 0 ++ [lH0]) 4, .rw 10 1 false, .sem 11 11 (ppL 0 ++ [lZ0]) 4,
     .rw 0 0 true] = true := by
  decide +kernel

/-- `Z` on the box wire passes the multi-controlled `H`. -/
theorem sZhg (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [lZ0, hgF]) (wc 5 (m + 5) [hgF, lZ0]) :=
  check_sound (frame 4) ih (TZhg_ok m ih) runZhg

def T282 : SE.Tbl :=
  [([hg12], [hg02]), ([lS1, hg01, lS1], [hg02]), ([hg01], ppL 0 ++ [eA] ++ ppL 0),
   ([lS1, eA, lS1], [B0]), ([lK0, B0], [B0, lK0])]

theorem T282_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T282 := by
  intro e he
  simp only [T282, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact s277 m ih
  · exact swE m 1 (by omega) _ _ _ _ (by decide) (by decide)
  · exact hgPP_01 m
  · exact swE m 1 (by omega) _ _ _ _ (by decide) (by decide)
  · exact s280 m ih

theorem run282 : check 4 T282 [lC0, hg12] [hg12, lC0]
    [.rw 1 0 false, .rw 1 1 true, .rw 2 2 false, .sem 12 0 [lS1, lS1] 4, .sem 15 0 [lS1, lS1] 4,
     .rw 13 3 false, .sem 0 13 (pp02 ++ [lK0]) 4, .rw 12 4 false, .sem 13 13 (pp02 ++ [lC0]) 4,
     .rw 12 3 true, .sem 14 2 [] 4, .sem 11 2 [] 4, .rw 1 2 true, .rw 0 1 false,
     .rw 0 0 true] = true := by
  decide +kernel

/-- (282) on five local wires: `CZ` of the idle wire `0` and the box wire
`1` passes the multi-controlled `H`. -/
theorem s282 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [lC0, hg12]) (wc 5 (m + 5) [hg12, lC0]) :=
  check_sound (frame 4) ih (T282_ok m ih) run282

def TKhg : SE.Tbl :=
  [([hg12], [hg02]), ([lS1, hg01, lS1], [hg02]), ([hg01], ppL 0 ++ [eA] ++ ppL 0),
   ([lS1, eA, lS1], [B0]), ([lC0, B0], [B0, lC0])]

theorem TKhg_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m TKhg := by
  intro e he
  simp only [TKhg, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact s277 m ih
  · exact swE m 1 (by omega) _ _ _ _ (by decide) (by decide)
  · exact hgPP_01 m
  · exact swE m 1 (by omega) _ _ _ _ (by decide) (by decide)
  · exact s272 m ih

theorem runKhg : check 4 TKhg [lK0, hg12] [hg12, lK0]
    [.rw 1 0 false, .rw 1 1 true, .rw 2 2 false, .sem 12 0 [lS1, lS1] 4, .sem 15 0 [lS1, lS1] 4,
     .rw 13 3 false, .sem 0 13 (pp02 ++ [lC0]) 4, .rw 12 4 false, .sem 13 13 (pp02 ++ [lK0]) 4,
     .rw 12 3 true, .sem 14 2 [] 4, .sem 11 2 [] 4, .rw 1 2 true, .rw 0 1 false,
     .rw 0 0 true] = true := by
  decide +kernel

/-- `CH` from wire `1` onto the idle wire `0` passes the multi-controlled
`H` with box wire `1`. -/
theorem sKhg (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [lK0, hg12]) (wc 5 (m + 5) [hg12, lK0]) :=
  check_sound (frame 4) ih (TKhg_ok m ih) runKhg

end QCert.RealCliffordCH.Sec8.D.N8
