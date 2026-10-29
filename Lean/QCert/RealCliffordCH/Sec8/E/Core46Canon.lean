/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5, rule (46): the canonical equations as gate descriptions

The equations of Appendix D that the paper's chain for (46) cites, at their
canonical wires, with the colours of the wires `1, 2, 3` as parameters and the
wires `4, …` white (`C46.c4`): involutions (311), (312), (111); the
commutations (335)–(340), (342), (344), (345) and (308); the box wire moves
(274), (277); Definition 2.4 (112); the Klein four-group (130); the merges
(309), (310) at any wires.  `Core46Kit.fr_eq` moves them to other wires.
-/
import QCert.RealCliffordCH.Sec8.E.Core46Kit

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.E.C46

open Circuit Net

/-- Colours of the wires `1, 2, 3`, white above. -/
def xf (x1 x2 x3 : Bool) : ℕ → Bool :=
  fun j => if j = 1 then x1 else if j = 2 then x2 else if j = 3 then x3 else false

/-- Pointwise equality of two control assignments: unfold and split. -/
macro "c4eq" : tactic => `(tactic| (intro j hj; rcases j with _ | _ | _ | _ | j <;>
  simp_all [c4, xf, ctlOr, ctlAt, blackOn, colOn, setCtl] <;> omega))

theorem drawn_nil' {N : ℕ} : drawn ([] : List (Circ N)) = 1 := rfl

theorem setCtl_c4 (a : List (Option Bool)) (ha : a.length = 4) {w : ℕ} (hw : w < 4)
    (v : Option Bool) (j : ℕ) : setCtl (c4 a) w v j = c4 (a.set w v) j := by
  unfold setCtl c4
  by_cases hj : j = w
  · subst hj
    rw [if_pos rfl, if_pos hw, List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega),
      Option.getD_some]
  · rw [if_neg hj]
    split_ifs with h4
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (Ne.symm hj)]
    · rfl

/-- (277) coloured by (81). -/
theorem move277 {N : ℕ} (x : ℕ → Bool) (ih : IH N) (hN : 3 ≤ N) :
    Derivable (theory N) (mc N .hg [1, 2] (colOn 3 N x)) (mc N .hg [0, 2] (colOn 3 N x)) := by
  set ws := (List.range N).filter (fun j => decide (3 ≤ j) && !x j) with hws
  have hnd : ws.Nodup := List.nodup_range.filter _
  have hw : ∀ (tg : List ℕ), (∀ t ∈ tg, t < 3) → ∀ j ∈ ws,
      j < N ∧ j ∉ tg ∧ (blackOn 3 N j).isSome := by
    intro tg htg j hj
    simp only [hws, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_eq_eq_not, Bool.not_true] at hj
    exact ⟨hj.1, fun h => by have := htg j h; omega, by simp [blackOn, hj.1, hj.2.1]⟩
  have hf : flipOn ws (blackOn 3 N) = colOn 3 N x := by
    funext j
    simp only [flipOn, hws, List.mem_filter, List.mem_range, blackOn, colOn]
    by_cases h : 3 ≤ j ∧ j < N
    · cases hx : x j <;> simp [h, hx, h.1]
    · simp only [h, if_false]
      split_ifs with h' <;> simp_all
  have r0 := recolour .hg [1, 2] ws (blackOn 3 N) hnd (hw [1, 2] (by simp))
  have r1 := recolour .hg [0, 2] ws (blackOn 3 N) hnd (hw [0, 2] (by simp))
  rw [hf] at r0 r1
  exact r0.symm.trans ((drawn_mid _ _ (D.eq277 N hN ih)).trans r1)

section Canon

variable {n : ℕ} (ih : IH (n + 4))
include ih

theorem k_inv_box (x1 x2 x3 : Bool) :
    Derivable (theory (n + 4))
      (wI (n + 4) [.g .box [0] [none, some x1, some x2, some x3],
        .g .box [0] [none, some x1, some x2, some x3]]) (wI (n + 4) []) := by
  have e : mc (n + 4) .box [0] (c4 [none, some x1, some x2, some x3]) =
      mc (n + 4) .box [0] (colOn 1 (n + 4) (xf x1 x2 x3)) := Net.mc_congr _ _ _ (by c4eq)
  show Derivable _ (drawn [mc (n + 4) .box [0] (c4 [none, some x1, some x2, some x3]),
    mc (n + 4) .box [0] (c4 [none, some x1, some x2, some x3])]) (drawn [])
  rw [e, drawn_nil']
  exact D.eq311 (n + 4) (by omega) ih _

theorem k_inv_hg (x2 x3 : Bool) :
    Derivable (theory (n + 4))
      (wI (n + 4) [.g .hg [0, 1] [none, none, some x2, some x3],
        .g .hg [0, 1] [none, none, some x2, some x3]]) (wI (n + 4) []) := by
  have e : mc (n + 4) .hg [0, 1] (c4 [none, none, some x2, some x3]) =
      mc (n + 4) .hg [0, 1] (colOn 2 (n + 4) (xf false x2 x3)) := Net.mc_congr _ _ _ (by c4eq)
  show Derivable _ (drawn [mc (n + 4) .hg [0, 1] (c4 [none, none, some x2, some x3]),
    mc (n + 4) .hg [0, 1] (c4 [none, none, some x2, some x3])]) (drawn [])
  rw [e, drawn_nil']
  exact D.eq312 (n + 4) (by omega) ih _

theorem k_inv_pp : Derivable (theory (n + 4)) (wI (n + 4) [.p 0 1, .p 0 1]) (wI (n + 4) []) := by
  show Derivable _ (drawn [ppAt (n + 4) 0 1, ppAt (n + 4) 0 1]) (drawn [])
  rw [drawn_two, drawn_nil']
  exact pp_inv44 (M := n + 1) ih

theorem k335 (x1 x2 x3 y1 y2 y3 : Bool) :
    Derivable (theory (n + 4))
      (wI (n + 4) [.g .box [0] [none, some x1, some x2, some x3],
        .g .box [0] [none, some y1, some y2, some y3]])
      (wI (n + 4) [.g .box [0] [none, some y1, some y2, some y3],
        .g .box [0] [none, some x1, some x2, some x3]]) := by
  have e1 : mc (n + 4) .box [0] (c4 [none, some x1, some x2, some x3]) =
      mc (n + 4) .box [0] (colOn 1 (n + 4) (xf x1 x2 x3)) := Net.mc_congr _ _ _ (by c4eq)
  have e2 : mc (n + 4) .box [0] (c4 [none, some y1, some y2, some y3]) =
      mc (n + 4) .box [0] (colOn 1 (n + 4) (xf y1 y2 y3)) := Net.mc_congr _ _ _ (by c4eq)
  show Derivable _ (drawn [mc (n + 4) .box [0] (c4 [none, some x1, some x2, some x3]),
    mc (n + 4) .box [0] (c4 [none, some y1, some y2, some y3])])
    (drawn [mc (n + 4) .box [0] (c4 [none, some y1, some y2, some y3]),
    mc (n + 4) .box [0] (c4 [none, some x1, some x2, some x3])])
  rw [e1, e2]
  exact D.eq335 (n + 4) (by omega) ih _ _

theorem k336 (c1 x2 x3 c2 y2 y3 : Bool) :
    Derivable (theory (n + 4))
      (wI (n + 4) [.g .box [0] [none, some c1, some x2, some x3],
        .g .box [1] [some c2, none, some y2, some y3]])
      (wI (n + 4) [.g .box [1] [some c2, none, some y2, some y3],
        .g .box [0] [none, some c1, some x2, some x3]]) := by
  have e1 : mc (n + 4) .box [0] (c4 [none, some c1, some x2, some x3]) =
      mc (n + 4) .box [0] (ctlOr (ctlAt 1 c1) (colOn 2 (n + 4) (xf false x2 x3))) :=
    Net.mc_congr _ _ _ (by c4eq)
  have e2 : mc (n + 4) .box [1] (c4 [some c2, none, some y2, some y3]) =
      mc (n + 4) .box [1] (ctlOr (ctlAt 0 c2) (colOn 2 (n + 4) (xf false y2 y3))) :=
    Net.mc_congr _ _ _ (by c4eq)
  show Derivable _ (drawn [mc (n + 4) .box [0] (c4 [none, some c1, some x2, some x3]),
    mc (n + 4) .box [1] (c4 [some c2, none, some y2, some y3])])
    (drawn [mc (n + 4) .box [1] (c4 [some c2, none, some y2, some y3]),
    mc (n + 4) .box [0] (c4 [none, some c1, some x2, some x3])])
  rw [e1, e2]
  exact D.eq336 (n + 4) (by omega) ih _ _ c1 c2

theorem k337 (c1 x2 x3 y2 y3 : Bool) (h : x2 ≠ y2 ∨ x3 ≠ y3) :
    Derivable (theory (n + 4))
      (wI (n + 4) [.g .box [0] [none, some c1, some x2, some x3],
        .g .hg [0, 1] [none, none, some y2, some y3]])
      (wI (n + 4) [.g .hg [0, 1] [none, none, some y2, some y3],
        .g .box [0] [none, some c1, some x2, some x3]]) := by
  have e1 : mc (n + 4) .box [0] (c4 [none, some c1, some x2, some x3]) =
      mc (n + 4) .box [0] (ctlOr (ctlAt 1 c1) (colOn 2 (n + 4) (xf false x2 x3))) :=
    Net.mc_congr _ _ _ (by c4eq)
  have e2 : mc (n + 4) .hg [0, 1] (c4 [none, none, some y2, some y3]) =
      mc (n + 4) .hg [0, 1] (colOn 2 (n + 4) (xf false y2 y3)) := Net.mc_congr _ _ _ (by c4eq)
  have hd : DiffOn 2 (n + 4) (xf false x2 x3) (xf false y2 y3) := by
    rcases h with h | h
    · exact ⟨2, le_rfl, by omega, by simpa [xf] using h⟩
    · exact ⟨3, by omega, by omega, by simpa [xf] using h⟩
  show Derivable _ (drawn [mc (n + 4) .box [0] (c4 [none, some c1, some x2, some x3]),
    mc (n + 4) .hg [0, 1] (c4 [none, none, some y2, some y3])])
    (drawn [mc (n + 4) .hg [0, 1] (c4 [none, none, some y2, some y3]),
    mc (n + 4) .box [0] (c4 [none, some c1, some x2, some x3])])
  rw [e1, e2]
  exact D.eq337 (n + 4) (by omega) ih _ _ hd c1

theorem k338 (c1 x2 x3 y2 y3 : Bool) :
    Derivable (theory (n + 4))
      (wI (n + 4) [.g .box [0] [none, some c1, some x2, some x3],
        .g .hg [1, 0] [none, none, some y2, some y3]])
      (wI (n + 4) [.g .hg [1, 0] [none, none, some y2, some y3],
        .g .box [0] [none, some c1, some x2, some x3]]) := by
  have e1 : mc (n + 4) .box [0] (c4 [none, some c1, some x2, some x3]) =
      mc (n + 4) .box [0] (ctlOr (ctlAt 1 c1) (colOn 2 (n + 4) (xf false x2 x3))) :=
    Net.mc_congr _ _ _ (by c4eq)
  have e2 : mc (n + 4) .hg [1, 0] (c4 [none, none, some y2, some y3]) =
      mc (n + 4) .hg [1, 0] (colOn 2 (n + 4) (xf false y2 y3)) := Net.mc_congr _ _ _ (by c4eq)
  show Derivable _ (drawn [mc (n + 4) .box [0] (c4 [none, some c1, some x2, some x3]),
    mc (n + 4) .hg [1, 0] (c4 [none, none, some y2, some y3])])
    (drawn [mc (n + 4) .hg [1, 0] (c4 [none, none, some y2, some y3]),
    mc (n + 4) .box [0] (c4 [none, some c1, some x2, some x3])])
  rw [e1, e2]
  exact D.eq338 (n + 4) (by omega) ih _ _ c1

theorem k339 (c1 c2 x3 c3 y3 : Bool) (h : x3 ≠ y3) :
    Derivable (theory (n + 4))
      (wI (n + 4) [.g .box [0] [none, some c2, some c1, some x3],
        .g .hg [1, 2] [some c3, none, none, some y3]])
      (wI (n + 4) [.g .hg [1, 2] [some c3, none, none, some y3],
        .g .box [0] [none, some c2, some c1, some x3]]) := by
  have e1 : mc (n + 4) .box [0] (c4 [none, some c2, some c1, some x3]) =
      mc (n + 4) .box [0] (ctlOr (ctlAt 2 c1) (ctlOr (ctlAt 1 c2)
        (colOn 3 (n + 4) (xf false false x3)))) := Net.mc_congr _ _ _ (by c4eq)
  have e2 : mc (n + 4) .hg [1, 2] (c4 [some c3, none, none, some y3]) =
      mc (n + 4) .hg [1, 2] (ctlOr (ctlAt 0 c3) (colOn 3 (n + 4) (xf false false y3))) :=
    Net.mc_congr _ _ _ (by c4eq)
  have hd : DiffOn 3 (n + 4) (xf false false x3) (xf false false y3) :=
    ⟨3, le_rfl, by omega, by simpa [xf] using h⟩
  show Derivable _ (drawn [mc (n + 4) .box [0] (c4 [none, some c2, some c1, some x3]),
    mc (n + 4) .hg [1, 2] (c4 [some c3, none, none, some y3])])
    (drawn [mc (n + 4) .hg [1, 2] (c4 [some c3, none, none, some y3]),
    mc (n + 4) .box [0] (c4 [none, some c2, some c1, some x3])])
  rw [e1, e2]
  exact D.eq339 (n + 4) (by omega) ih _ _ hd c1 c2 c3

theorem k340 (x2 x3 y2 y3 : Bool) :
    Derivable (theory (n + 4))
      (wI (n + 4) [.g .hg [0, 1] [none, none, some x2, some x3],
        .g .hg [0, 1] [none, none, some y2, some y3]])
      (wI (n + 4) [.g .hg [0, 1] [none, none, some y2, some y3],
        .g .hg [0, 1] [none, none, some x2, some x3]]) := by
  have e1 : mc (n + 4) .hg [0, 1] (c4 [none, none, some x2, some x3]) =
      mc (n + 4) .hg [0, 1] (colOn 2 (n + 4) (xf false x2 x3)) := Net.mc_congr _ _ _ (by c4eq)
  have e2 : mc (n + 4) .hg [0, 1] (c4 [none, none, some y2, some y3]) =
      mc (n + 4) .hg [0, 1] (colOn 2 (n + 4) (xf false y2 y3)) := Net.mc_congr _ _ _ (by c4eq)
  show Derivable _ (drawn [mc (n + 4) .hg [0, 1] (c4 [none, none, some x2, some x3]),
    mc (n + 4) .hg [0, 1] (c4 [none, none, some y2, some y3])])
    (drawn [mc (n + 4) .hg [0, 1] (c4 [none, none, some y2, some y3]),
    mc (n + 4) .hg [0, 1] (c4 [none, none, some x2, some x3])])
  rw [e1, e2]
  exact D.eq340 (n + 4) (by omega) ih _ _

theorem k342 (c1 x3 c2 y3 : Bool) (h : x3 ≠ y3) :
    Derivable (theory (n + 4))
      (wI (n + 4) [.g .hg [0, 1] [none, none, some c1, some x3],
        .g .hg [0, 2] [none, some c2, none, some y3]])
      (wI (n + 4) [.g .hg [0, 2] [none, some c2, none, some y3],
        .g .hg [0, 1] [none, none, some c1, some x3]]) := by
  have e1 : mc (n + 4) .hg [0, 1] (c4 [none, none, some c1, some x3]) =
      mc (n + 4) .hg [0, 1] (ctlOr (ctlAt 2 c1) (colOn 3 (n + 4) (xf false false x3))) :=
    Net.mc_congr _ _ _ (by c4eq)
  have e2 : mc (n + 4) .hg [0, 2] (c4 [none, some c2, none, some y3]) =
      mc (n + 4) .hg [0, 2] (ctlOr (ctlAt 1 c2) (colOn 3 (n + 4) (xf false false y3))) :=
    Net.mc_congr _ _ _ (by c4eq)
  have hd : DiffOn 3 (n + 4) (xf false false x3) (xf false false y3) :=
    ⟨3, le_rfl, by omega, by simpa [xf] using h⟩
  show Derivable _ (drawn [mc (n + 4) .hg [0, 1] (c4 [none, none, some c1, some x3]),
    mc (n + 4) .hg [0, 2] (c4 [none, some c2, none, some y3])])
    (drawn [mc (n + 4) .hg [0, 2] (c4 [none, some c2, none, some y3]),
    mc (n + 4) .hg [0, 1] (c4 [none, none, some c1, some x3])])
  rw [e1, e2]
  exact D.eq342 (n + 4) (by omega) ih _ _ hd c1 c2

theorem k344 (c1 x3 c2 y3 : Bool) (h : x3 ≠ y3) :
    Derivable (theory (n + 4))
      (wI (n + 4) [.g .hg [0, 1] [none, none, some c1, some x3],
        .g .hg [1, 2] [some c2, none, none, some y3]])
      (wI (n + 4) [.g .hg [1, 2] [some c2, none, none, some y3],
        .g .hg [0, 1] [none, none, some c1, some x3]]) := by
  have e1 : mc (n + 4) .hg [0, 1] (c4 [none, none, some c1, some x3]) =
      mc (n + 4) .hg [0, 1] (ctlOr (ctlAt 2 c1) (colOn 3 (n + 4) (xf false false x3))) :=
    Net.mc_congr _ _ _ (by c4eq)
  have e2 : mc (n + 4) .hg [1, 2] (c4 [some c2, none, none, some y3]) =
      mc (n + 4) .hg [1, 2] (ctlOr (ctlAt 0 c2) (colOn 3 (n + 4) (xf false false y3))) :=
    Net.mc_congr _ _ _ (by c4eq)
  have hd : DiffOn 3 (n + 4) (xf false false x3) (xf false false y3) :=
    ⟨3, le_rfl, by omega, by simpa [xf] using h⟩
  show Derivable _ (drawn [mc (n + 4) .hg [0, 1] (c4 [none, none, some c1, some x3]),
    mc (n + 4) .hg [1, 2] (c4 [some c2, none, none, some y3])])
    (drawn [mc (n + 4) .hg [1, 2] (c4 [some c2, none, none, some y3]),
    mc (n + 4) .hg [0, 1] (c4 [none, none, some c1, some x3])])
  rw [e1, e2]
  exact D.eq344 (n + 4) (by omega) ih _ _ hd c1 c2

theorem k345 (x2 x3 y2 y3 : Bool) :
    Derivable (theory (n + 4))
      (wI (n + 4) [.g .hg [1, 0] [none, none, some x2, some x3],
        .g .hg [0, 1] [none, none, some y2, some y3]])
      (wI (n + 4) [.g .hg [0, 1] [none, none, some y2, some y3],
        .g .hg [1, 0] [none, none, some x2, some x3]]) := by
  have e1 : mc (n + 4) .hg [1, 0] (c4 [none, none, some x2, some x3]) =
      mc (n + 4) .hg [1, 0] (colOn 2 (n + 4) (xf false x2 x3)) := Net.mc_congr _ _ _ (by c4eq)
  have e2 : mc (n + 4) .hg [0, 1] (c4 [none, none, some y2, some y3]) =
      mc (n + 4) .hg [0, 1] (colOn 2 (n + 4) (xf false y2 y3)) := Net.mc_congr _ _ _ (by c4eq)
  show Derivable _ (drawn [mc (n + 4) .hg [1, 0] (c4 [none, none, some x2, some x3]),
    mc (n + 4) .hg [0, 1] (c4 [none, none, some y2, some y3])])
    (drawn [mc (n + 4) .hg [0, 1] (c4 [none, none, some y2, some y3]),
    mc (n + 4) .hg [1, 0] (c4 [none, none, some x2, some x3])])
  rw [e1, e2]
  exact D.eq345 (n + 4) (by omega) ih _ _

theorem k274 (x2 x3 : Bool) :
    Derivable (theory (n + 4)) (wI (n + 4) [.g .box [0] [none, none, some x2, some x3]])
      (wI (n + 4) [.g .box [1] [none, none, some x2, some x3]]) := by
  have e1 : mc (n + 4) .box [0] (c4 [none, none, some x2, some x3]) =
      mc (n + 4) .box [0] (colOn 2 (n + 4) (xf false x2 x3)) := Net.mc_congr _ _ _ (by c4eq)
  have e2 : mc (n + 4) .box [1] (c4 [none, none, some x2, some x3]) =
      mc (n + 4) .box [1] (colOn 2 (n + 4) (xf false x2 x3)) := Net.mc_congr _ _ _ (by c4eq)
  show Derivable _ (drawn [mc (n + 4) .box [0] (c4 [none, none, some x2, some x3])])
    (drawn [mc (n + 4) .box [1] (c4 [none, none, some x2, some x3])])
  rw [e1, e2, D.N15.drawn_one', D.N15.drawn_one']
  exact move274 (N := n + 4) _ ih (by omega)

theorem k277 (x3 : Bool) :
    Derivable (theory (n + 4)) (wI (n + 4) [.g .hg [1, 2] [none, none, none, some x3]])
      (wI (n + 4) [.g .hg [0, 2] [none, none, none, some x3]]) := by
  have e1 : mc (n + 4) .hg [1, 2] (c4 [none, none, none, some x3]) =
      mc (n + 4) .hg [1, 2] (colOn 3 (n + 4) (xf false false x3)) := Net.mc_congr _ _ _ (by c4eq)
  have e2 : mc (n + 4) .hg [0, 2] (c4 [none, none, none, some x3]) =
      mc (n + 4) .hg [0, 2] (colOn 3 (n + 4) (xf false false x3)) := Net.mc_congr _ _ _ (by c4eq)
  show Derivable _ (drawn [mc (n + 4) .hg [1, 2] (c4 [none, none, none, some x3])])
    (drawn [mc (n + 4) .hg [0, 2] (c4 [none, none, none, some x3])])
  rw [e1, e2, D.N15.drawn_one', D.N15.drawn_one']
  exact move277 _ ih (by omega)

theorem k112 (x2 x3 : Bool) :
    Derivable (theory (n + 4)) (wI (n + 4) [.g .hg [0, 1] [none, none, some x2, some x3]])
      (wI (n + 4) [.p 0 1, .g .box [0] [none, some true, some x2, some x3], .p 0 1]) := by
  set c := c4 [none, none, some x2, some x3] with hc
  have hk : 2 ≤ (ctrlWires (n + 4) [0, 1] c).length := by
    have hsub : ([2, 3] : List ℕ) ⊆ ctrlWires (n + 4) [0, 1] c := by
      intro j hj
      rw [MS.mem_ctrlWires]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> simp [hc, c4]
    simpa using (List.Nodup.subperm (by decide) hsub).length_le
  have h := D.N8.hgPP (n + 4) (by omega) c hk
  have e : mc (n + 4) .box [0] (setCtl c 1 (some true)) =
      mc (n + 4) .box [0] (c4 [none, some true, some x2, some x3]) := Net.mc_congr _ _ _ (by
    intro j hj; rw [hc, setCtl_c4 _ rfl (by omega)]; rfl)
  rw [e] at h
  show Derivable _ (drawn [mc (n + 4) .hg [0, 1] c]) (drawn [ppAt (n + 4) 0 1,
    mc (n + 4) .box [0] (c4 [none, some true, some x2, some x3]), ppAt (n + 4) 0 1])
  rw [D.N15.drawn_one']
  exact h

theorem k308 (x2 x3 : Bool) :
    Derivable (theory (n + 4)) (wI (n + 4) [.p 0 1, .g .box [1] [none, none, some x2, some x3]])
      (wI (n + 4) [.g .box [1] [none, none, some x2, some x3], .p 0 1]) := by
  set x := xf false x2 x3 with hx
  set ws := (List.range (n + 4)).filter (fun j => decide (2 ≤ j) && !(x j)) with hws
  have hnd : ws.Nodup := List.nodup_range.filter _
  have hmem : ∀ j ∈ ws, 2 ≤ j ∧ j < n + 4 := by
    intro j hj
    simp only [hws, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hj
    exact ⟨hj.2.1, hj.1⟩
  set U := drawn (ws.map (xAt (n + 4)))
  have hU : Derivable (theory (n + 4)) (U * U) 1 :=
    D.xs_inv (n + 4) ws hnd (fun w hw => (hmem w hw).2)
  have hUP : Derivable (theory (n + 4)) (U * ppAt (n + 4) 0 1 * U) (ppAt (n + 4) 0 1) := by
    refine D.N15.conj_of_comm hU ?_
    unfold D.Comm; rw [drawn_two, drawn_two]
    exact D.N8.pp_comm (by omega) (D.N8.highW_xs _ _ (fun j hj => (hmem j hj).1))
  have hc' : ∀ j < n + 4, colOn 2 (n + 4) x j =
      if j ∈ ws then some false else blackOn 2 (n + 4) j := by
    intro j hj
    by_cases h2 : 2 ≤ j
    · cases hxj : x j <;>
        simp [colOn, blackOn, hws, List.mem_filter, List.mem_range, h2, hj, hxj]
    · simp [colOn, blackOn, hws, List.mem_filter, List.mem_range, h2]
  have hUB : Derivable (theory (n + 4)) (U * mc (n + 4) .box [1] (blackOn 2 (n + 4)) * U)
      (mc (n + 4) .box [1] (colOn 2 (n + 4) x)) :=
    colr43 _ hnd .box [1] _ _ (fun j hj => by
      obtain ⟨h2, hN⟩ := hmem j hj
      exact ⟨hN, by simp; omega, by simp [blackOn]; omega⟩) hc'
  have e : mc (n + 4) .box [1] (colOn 2 (n + 4) x) =
      mc (n + 4) .box [1] (c4 [none, none, some x2, some x3]) := Net.mc_congr _ _ _ (by
    intro j hj; rcases j with _ | _ | _ | _ | j <;> simp_all [c4, xf, colOn] <;> omega)
  rw [e] at hUB
  have h := D.eq308 (n + 4) (by omega) ih 2 (by omega) (by omega) (pp : Circ 2)
  rw [D.N8.atBot_pp (n + 4) 0 (by omega)] at h
  exact D.N15.via_conj hU (l := [ppAt (n + 4) 0 1, mc (n + 4) .box [1] (blackOn 2 (n + 4))])
    (L := [ppAt (n + 4) 0 1, mc (n + 4) .box [1] (c4 [none, none, some x2, some x3])])
    (r := [mc (n + 4) .box [1] (blackOn 2 (n + 4)), ppAt (n + 4) 0 1])
    (R := [mc (n + 4) .box [1] (c4 [none, none, some x2, some x3]), ppAt (n + 4) 0 1])
    (List.Forall₂.cons hUP (List.Forall₂.cons hUB List.Forall₂.nil))
    (List.Forall₂.cons hUB (List.Forall₂.cons hUP List.Forall₂.nil)) h

theorem k_klein1 : Derivable (theory (n + 4)) (wI (n + 4) [.p 0 1, .p 0 2]) (wI (n + 4) [.p 1 2]) := by
  obtain ⟨k1, -⟩ := klein43 (M := n + 1) ih
  show Derivable _ (drawn [ppAt (n + 4) 0 1, ppAt (n + 4) 0 2]) (drawn [ppAt (n + 4) 1 2])
  rw [drawn_two, D.N15.drawn_one']
  exact (dright _ (pp_sym ih (a := 2) (b := 0) (by omega) (by omega) (by omega))).trans
    (k1.trans (pp_sym ih (a := 1) (b := 2) (by omega) (by omega) (by omega)))

theorem k_klein2 : Derivable (theory (n + 4)) (wI (n + 4) [.p 0 2, .p 0 1]) (wI (n + 4) [.p 1 2]) := by
  obtain ⟨-, k2⟩ := klein43 (M := n + 1) ih
  show Derivable _ (drawn [ppAt (n + 4) 0 2, ppAt (n + 4) 0 1]) (drawn [ppAt (n + 4) 1 2])
  rw [drawn_two, D.N15.drawn_one']
  exact (dleft _ (pp_sym ih (a := 2) (b := 0) (by omega) (by omega) (by omega))).trans
    (k2.trans (pp_sym ih (a := 1) (b := 2) (by omega) (by omega) (by omega)))

theorem k309 (t w : ℕ) (a : List (Option Bool)) (b : Bool) (ha : a.length = 4) (ht : t < 4)
    (hw : w < 4) (hwt : w ≠ t) (hat : a.getD t none = none) :
    Derivable (theory (n + 4))
      (wI (n + 4) [.g .box [t] (a.set w (some b)), .g .box [t] (a.set w (some !b))])
      (wI (n + 4) [.g .box [t] (a.set w none)]) := by
  have hc : c4 a t = none := by simp only [c4, if_pos ht]; exact hat
  have h := mergeAt (M := n + 1) ih (t := t) (by omega) (c4 a) hc hwt (by omega) b
  have e : ∀ v, mc (n + 4) .box [t] (setCtl (c4 a) w v) = mc (n + 4) .box [t] (c4 (a.set w v)) :=
    fun v => Net.mc_congr _ _ _ (fun j _ => setCtl_c4 a ha hw v j)
  rw [e, e, e] at h
  show Derivable _ (drawn [mc (n + 4) .box [t] (c4 (a.set w (some b))),
    mc (n + 4) .box [t] (c4 (a.set w (some !b)))]) (drawn [mc (n + 4) .box [t] (c4 (a.set w none))])
  rw [D.N15.drawn_one']
  exact h

theorem k310 (bw hw w : ℕ) (a : List (Option Bool)) (b : Bool) (ha : a.length = 4) (hb : bw < 4)
    (hh : hw < 4) (hbh : bw ≠ hw) (hwN : w < 4) (hwb : w ≠ bw) (hwh : w ≠ hw)
    (hab : a.getD bw none = none) (hah : a.getD hw none = none) :
    Derivable (theory (n + 4))
      (wI (n + 4) [.g .hg [bw, hw] (a.set w (some b)), .g .hg [bw, hw] (a.set w (some !b))])
      (wI (n + 4) [.g .hg [bw, hw] (a.set w none)]) := by
  have hcb : c4 a bw = none := by simp only [c4, if_pos hb]; exact hab
  have hch : c4 a hw = none := by simp only [c4, if_pos hh]; exact hah
  have h := mergeHgAt (M := n + 1) ih (bw := bw) (hw := hw) (by omega) (by omega) hbh (c4 a) hcb hch
    hwb hwh (by omega) b
  have e : ∀ v, mc (n + 4) .hg [bw, hw] (setCtl (c4 a) w v) =
      mc (n + 4) .hg [bw, hw] (c4 (a.set w v)) :=
    fun v => Net.mc_congr _ _ _ (fun j _ => setCtl_c4 a ha hwN v j)
  rw [e, e, e] at h
  show Derivable _ (drawn [mc (n + 4) .hg [bw, hw] (c4 (a.set w (some b))),
    mc (n + 4) .hg [bw, hw] (c4 (a.set w (some !b)))])
    (drawn [mc (n + 4) .hg [bw, hw] (c4 (a.set w none))])
  rw [D.N15.drawn_one']
  exact h

/-- Two `P ⊗ P` on disjoint pairs commute (from (130) on two triples). -/
theorem k_cpp : Derivable (theory (n + 4)) (wI (n + 4) [.p 0 1, .p 2 3])
    (wI (n + 4) [.p 2 3, .p 0 1]) := by
  have k023 : Derivable (theory (n + 4)) (wI (n + 4) [.p 0 2, .p 0 3]) (wI (n + 4) [.p 2 3]) :=
    fr_eq ih (σ := [0, 2, 3, 1]) (by decide) (by decide) (by decide) (by decide) (by decide)
      (k_klein1 ih)
  have k013a : Derivable (theory (n + 4)) (wI (n + 4) [.p 0 1, .p 0 3]) (wI (n + 4) [.p 1 3]) :=
    fr_eq ih (σ := [0, 1, 3, 2]) (by decide) (by decide) (by decide) (by decide) (by decide)
      (k_klein1 ih)
  have k013b : Derivable (theory (n + 4)) (wI (n + 4) [.p 0 3, .p 0 1]) (wI (n + 4) [.p 1 3]) :=
    fr_eq ih (σ := [0, 1, 3, 2]) (by decide) (by decide) (by decide) (by decide) (by decide)
      (k_klein2 ih)
  exact run_sound (T := [([.p 0 2, .p 0 3], [.p 2 3]), ([.p 0 1, .p 0 2], [.p 1 2]),
      ([.p 0 2, .p 0 1], [.p 1 2]), ([.p 0 1, .p 0 3], [.p 1 3]), ([.p 0 3, .p 0 1], [.p 1 3])])
    ⟨k023, k_klein1 ih, k_klein2 ih, k013a, k013b⟩
    (ss := [(1, 0, false), (0, 1, true), (0, 2, false), (1, 3, true), (1, 4, false), (0, 0, true)])
    (by decide)

/-- The facts behind (112) with the wire `3` idle. -/
def Tk112i (x2 : Bool) : List Eqn :=
  [([.g .hg [0, 1] [none, none, some x2, some false], .g .hg [0, 1] [none, none, some x2, some true]],
      [.g .hg [0, 1] [none, none, some x2, none]]),
    ([.g .hg [0, 1] [none, none, some x2, some false]],
      [.p 0 1, .g .box [0] [none, some true, some x2, some false], .p 0 1]),
    ([.g .hg [0, 1] [none, none, some x2, some true]],
      [.p 0 1, .g .box [0] [none, some true, some x2, some true], .p 0 1]),
    ([.p 0 1, .p 0 1], []),
    ([.g .box [0] [none, some true, some x2, some false], .g .box [0] [none, some true, some x2, some true]],
      [.g .box [0] [none, some true, some x2, none]])]

omit ih in
theorem run_k112i : ∀ x2 : Bool, runW (Tk112i x2) [.g .hg [0, 1] [none, none, some x2, none]]
    [(0, 0, false), (0, 1, true), (3, 2, true), (2, 3, true), (1, 4, true)] =
      some [.p 0 1, .g .box [0] [none, some true, some x2, none], .p 0 1] := by
  decide

/-- (112) with the wire `3` idle: merge it (310), apply (112) to both halves,
cancel (111) and merge the boxes (309). -/
theorem k112i (x2 : Bool) :
    Derivable (theory (n + 4)) (wI (n + 4) [.g .hg [0, 1] [none, none, some x2, none]])
      (wI (n + 4) [.p 0 1, .g .box [0] [none, some true, some x2, none], .p 0 1]) :=
  run_sound (T := Tk112i x2)
    ⟨k310 ih 0 1 3 [none, none, some x2, none] false rfl (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) rfl rfl,
      k112 ih x2 false, k112 ih x2 true, k_inv_pp ih,
      k309 ih 0 3 [none, some true, some x2, none] false rfl (by decide) (by decide) (by decide) rfl⟩
    (run_k112i x2)

end Canon

end QCert.RealCliffordCH.Sec8.E.C46
