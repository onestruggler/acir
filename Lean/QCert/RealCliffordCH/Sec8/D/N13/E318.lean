/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (318)

The multi-controlled `(-1)^a ZX` with target wire `1` and controls `0`
(black), `2` (black), `3` (colour `α`) commutes with the box on wire `0`
whose controls are `1` (colour `β`), `2` (white) and the wires `4, …` (colour
`x`), wire `3` idle.

From five wires on, by the paper's chain on five local wires (the bulk all
black, then coloured by `Kit.colour_wc`): the box, idle on wire `3`, is
written by (269) (a semantic step without wire `3`); the rotation passes the
doubly controlled rotations of (269) (semantic, without wire `4`) and the
inner box of (269) by (290), carried to the wires `1, 0` by the swap of the
wires `0, 1` (`t290s`).  For the other colours and signs of the rotation, it
is conjugated by `X` on wire `3` (semantic, without wire `4`; `X` passes the
inner box, which is idle on wire `3`, without wire `2`), and `XZ` passes as
the inverse of `ZX` (Lemma B.5).
-/
import QCert.RealCliffordCH.Sec8.D.N13.Kit

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-! ## (290) on five local wires, and on the wires `1, 0` -/

/-- The box of (290): box wire `0`, controls `1`, `4` and the bulk. -/
def Bc : Lt := .g .box [0] [(1, true), (4, true)] true
/-- The rotation of (290): `ZX` on wire `0`, controls `1, 2, 3`. -/
def Zc : Lt := .g .zx [0] [(1, true), (2, true), (3, true)] false

theorem t290c (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Bc, Zc]) (wc 5 (m + 5) [Zc, Bc]) := by
  have h := eq290 (m + 5) (by omega) ih
  have e1 : Bc.circ 5 (m + 5) = mc (m + 5) .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 (m + 5))) := by
    refine mc_congr _ _ _ (fun i hi => ?_)
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ 5 ≤ i) with rfl | rfl | rfl | rfl | rfl | h5
    all_goals (simp only [ctl, ctlX, ctlOr, ctlAt, blackOn, colOn]; split_ifs <;> first | rfl | (exfalso; omega) | simp_all | omega)
  have e2 : Zc.circ 5 (m + 5) = mc (m + 5) .zx [0] (blackOn 1 4) := by
    refine mc_congr _ _ _ (fun i hi => ?_)
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ 5 ≤ i) with rfl | rfl | rfl | rfl | rfl | h5
    all_goals (simp only [ctl, ctlX, ctlOr, ctlAt, blackOn, colOn]; split_ifs <;> first | rfl | (exfalso; omega) | simp_all | omega)
  rw [wc_two, wc_two, e1, e2]
  exact h

/-- The rotation of (318), `(-1)^a ZX` on wire `1`, controls `0`, `2` and `3`
(colour `α`). -/
def Rg (a α : Bool) : Lt := .g (Kind.sgnZX a) [1] [(0, true), (2, true), (3, α)] false
/-- The inner box of (269) for the box of (318): box wire `1`, controls `0`,
`4` and the bulk. -/
def Bi : Lt := .g .box [1] [(0, true), (4, true)] true

def T290s : SE.Tbl :=
  [([Bc, Zc], [Zc, Bc]), ([.s (.S 0), Zc, .s (.S 0)], [Rg false true]),
   ([.s (.S 0), Bc, .s (.S 0)], [Bi])]

theorem T290s_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T290s := by
  intro e he
  simp only [T290s, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact t290c m ih
  · exact swapE m 5 0 (by omega) .zx [0] _ false (by decide) (by decide)
  · exact swapE m 5 0 (by omega) .box [0] _ true (by decide) (by decide)

theorem run290s : check 4 T290s [Rg false true, Bi] [Bi, Rg false true]
    [.rw 0 1 true, .rw 3 2 true, .sem 2 2 [] 2, .rw 1 0 true, .sem 2 0 [.s (.S 0), .s (.S 0)] 2,
     .rw 0 2 false, .rw 1 1 false] = true := by
  decide +kernel

/-- (290) on the wires `1, 0`: the rotation of (318) passes the inner box. -/
theorem t290s (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Rg false true, Bi]) (wc 5 (m + 5) [Bi, Rg false true]) :=
  check_sound (frame 4) ih (T290s_ok m ih) run290s

/-! ## The chain -/

/-- `X` on wire `3`. -/
def X3 : List Lt := [.s (.H 3), .s (.Z 3), .s (.H 3)]
/-- The box of (318), with wire `4` black. -/
def Bq (β : Bool) : Lt := .g .box [0] [(1, β), (2, false), (4, true)] true
def Wq (β : Bool) : Lt := .g .zx [0] [(1, β), (2, false)] false
def Vq (β : Bool) : Lt := .g .xz [0] [(1, β), (2, false)] false

def T318 : SE.Tbl := [([Rg false true, Bi], [Bi, Rg false true])]

theorem T318_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T318 := by
  intro e he
  simp only [T318, List.mem_cons, List.mem_nil_iff, or_false] at he
  subst he
  exact t290s m ih

/-- The rotation, of any colour and sign, passes the inner box. -/
def passRB (a α : Bool) (i : ℕ) : List St :=
  match a, α with
  | false, true => [.rw i 0 false]
  | false, false =>
    [.sem i 1 (X3 ++ [Rg false true] ++ X3) 4, .sem (i + 4) 4 ([Bi] ++ X3) 2, .rw (i + 3) 0 false,
     .sem i 4 ([Bi] ++ X3) 2, .sem (i + 1) 7 [Rg false false] 4]
  | true, true =>
    [.sem (i + 2) 0 [Rg false true, Rg true true] 4, .rw (i + 1) 0 true, .sem i 2 [] 4]
  | true, false =>
    [.sem i 1 (X3 ++ [Rg true true] ++ X3) 4, .sem (i + 4) 4 ([Bi] ++ X3) 2,
     .sem (i + 5) 0 [Rg false true, Rg true true] 4, .rw (i + 4) 0 true, .sem (i + 3) 2 [] 4,
     .sem i 4 ([Bi] ++ X3) 2, .sem (i + 1) 7 [Rg true false] 4]

def run318 (a α β : Bool) : List St :=
  [.sem 1 1 [Wq β, Bi, Vq β, Bi] 3, .sem 0 2 [Wq β, Rg a α] 4] ++ passRB a α 1 ++
  [.sem 2 2 [Vq β, Rg a α] 4] ++ passRB a α 3 ++ [.sem 0 4 [Bq β] 3]

theorem chk318 : ∀ a α β : Bool,
    check 4 T318 [Rg a α, Bq β] [Bq β, Rg a α] (run318 a α β) = true := by
  decide +kernel

theorem r318 (m : ℕ) (ih : IH (m + 5)) (a α β : Bool) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Rg a α, Bq β]) (wc 5 (m + 5) [Bq β, Rg a α]) :=
  check_sound (frame 4) ih (T318_ok m ih) (chk318 a α β)

/-! ## In the conventions of the interface -/

/-- The box of (318) on four local wires (wire `4` is in the bulk). -/
def Bq4 (β : Bool) : Lt := .g .box [0] [(1, β), (2, false)] true

theorem Rg_ok : ∀ a α : Bool, (Rg a α).ok 4 = true := by decide
theorem Bq4_ok : ∀ β : Bool, (Bq4 β).ok 4 = true := by decide

theorem Rg_rebase (N : ℕ) (a α : Bool) : (Rg a α).circ 5 N = (Rg a α).circ 4 N := by
  refine mc_congr _ _ _ (fun i hi => ?_)
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ 5 ≤ i) with rfl | rfl | rfl | rfl | rfl | h5
  all_goals (simp only [ctl, ctlX, ctlOr, ctlAt, blackOn, colOn]; split_ifs <;> first | rfl | (exfalso; omega) | simp_all | omega)

theorem Bq_rebase (N : ℕ) (β : Bool) : (Bq β).circ 5 N = (Bq4 β).circ 4 N := by
  refine mc_congr _ _ _ (fun i hi => ?_)
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ 5 ≤ i) with rfl | rfl | rfl | rfl | rfl | h5
  all_goals (simp only [ctl, ctlX, ctlOr, ctlAt, blackOn, colOn]; split_ifs <;> first | rfl | (exfalso; omega) | simp_all | omega)

/-- (318) from five wires on, every colour. -/
theorem eq318_ge5 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x : ℕ → Bool) (a α β : Bool) :
    Comm N (mc N (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 true) (ctlAt 3 α))))
      (mc N .box [0] (ctlOr (ctlAt 1 β) (ctlOr (ctlAt 2 false) (colOn 4 N x)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
  have h := r318 m ih a α β
  rw [wc_two, wc_two, Rg_rebase, Bq_rebase] at h
  have h4 := colour_wc (K := 4) (N := m + 5) (by omega) x (l := [Rg a α, Bq4 β]) (r := [Bq4 β, Rg a α])
    (all_two (Rg_ok a α) (Bq4_ok β)) (all_two (Bq4_ok β) (Rg_ok a α)) h
  have e1 : cX 4 (m + 5) x (Rg a α) =
      mc (m + 5) (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 true) (ctlAt 3 α))) := by
    refine mc_congr _ _ _ (fun i hi => ?_)
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h5
    all_goals (simp only [ctl, ctlX, ctlOr, ctlAt, blackOn, colOn]; split_ifs <;> first | rfl | (exfalso; omega) | simp_all | omega)
  have e2 : cX 4 (m + 5) x (Bq4 β) =
      mc (m + 5) .box [0] (ctlOr (ctlAt 1 β) (ctlOr (ctlAt 2 false) (colOn 4 (m + 5) x))) := by
    show mc _ _ _ _ = _
    refine mc_congr _ _ _ (fun i hi => ?_)
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h5
    all_goals (simp only [ctl, ctlX, ctlOr, ctlAt, blackOn, colOn]; split_ifs <;> first | rfl | (exfalso; omega) | simp_all | omega)
  have e3 : ∀ y z : Lt, wcX 4 (m + 5) x [y, z] = drawn [cX 4 (m + 5) x y, cX 4 (m + 5) x z] :=
    fun _ _ => rfl
  rw [e3, e3, e1, e2] at h4
  exact h4

end QCert.RealCliffordCH.Sec8.D.N13
