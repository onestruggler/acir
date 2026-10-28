/-
Copyright (c) 2026 QCert contributors. All rights reserved.

Two boxes with opposite controls on wire 2 still commute when one is
conjugated by P ⊗ P on wires 0, 1. The semantic calculation has three
local wires; the bulk colours of the two boxes may be different.
-/
import QCert.RealCliffordCH.Sec8.D.N13.Sem

namespace QCert.RealCliffordCH.Sec8.D.N13
open Circuit Eng SE Net N8 Sim
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def boxTarget (one : Bool) : ℕ := if one then 1 else 0
def boxCtl (one b d : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt (if one then 0 else 1) b) (ctlAt 2 d)
def box3Lt (one b d : Bool) : Lt :=
  .g .box [boxTarget one] [(if one then 0 else 1, b), (2, d)] false
def pp3L : List Lt := [.s (.K 0), .s (.H 1), .s (.Z 0), .s (.K 0), .s (.H 1),
  .s (.Z 0), .s (.K 0), .s (.H 1), .s (.Z 0), .s (.S 0)]
def box3 (one b d : Bool) : Circ 3 := (box3Lt one b d).on 3
def bpLeft (u v b c : Bool) : List Lt :=
  [box3Lt u b true] ++ pp3L ++ [box3Lt v c false] ++ pp3L
def bpRight (u v b c : Bool) : List Lt :=
  pp3L ++ [box3Lt v c false] ++ pp3L ++ [box3Lt u b true]

set_option maxHeartbeats 0 in
theorem box_pp_check : ∀ u v b c : Bool,
    SE.lcheck 3 true (bpLeft u v b c) (bpRight u v b c) = true := by
  decide +kernel

theorem bp_ok : ∀ u v b c : Bool,
    (∀ g ∈ bpLeft u v b c, g.ok 3 = true) ∧
    (∀ g ∈ bpRight u v b c, g.ok 3 = true) := by decide

theorem box_pp_eval (u v b c : Bool) :
    opsQ.eval 3 (box3 u b true) *
        (opsQ.eval 3 (pp : Circ 3) * opsQ.eval 3 (box3 v c false) * opsQ.eval 3 pp) =
      (opsQ.eval 3 (pp : Circ 3) * opsQ.eval 3 (box3 v c false) * opsQ.eval 3 pp) *
        opsQ.eval 3 (box3 u b true) := by
  have h := SE.lcheck_sound true (bp_ok u v b c).1 (bp_ok u v b c).2 (box_pp_check u v b c)
  have ep : drawn (pp3L.map (SE.circL 3 true)) = (pp : Circ 3) := rfl
  simp only [SE.circWL, bpLeft, bpRight, List.map_append, drawn_append,
    List.map_singleton, drawn_one, ep] at h
  change opsQ.eval 3 ((pp : Circ 3) * (box3 v c false * (pp * box3 u b true))) =
    opsQ.eval 3 (box3 u b true * (pp * (box3 v c false * pp))) at h
  simpa only [map_mul, mul_assoc] using h.symm

theorem box_pp_sem (m : ℕ) (u v b c : Bool) (x y : ℕ → Option Bool)
    (hx : ∀ i < 3, x i = boxCtl u b true i)
    (hy : ∀ i < 3, y i = boxCtl v c false i) :
    S.sem (m + 3) (drawn [mc (m + 3) .box [boxTarget u] x,
        (pp : Circ (m + 3)) * mc (m + 3) .box [boxTarget v] y * pp]) =
      S.sem (m + 3) (drawn [(pp : Circ (m + 3)) * mc (m + 3) .box [boxTarget v] y * pp,
        mc (m + 3) .box [boxTarget u] x]) := by
  apply sem_of_eval
  have eX := MS.eval_mc_blk (m := m) (k := 3) (K := .box) (tg := [boxTarget u]) x
    (by simp) (by cases u <;> simp [boxTarget]) rfl
  have eY := MS.eval_mc_blk (m := m) (k := 3) (K := .box) (tg := [boxTarget v]) y
    (by simp) (by cases v <;> simp [boxTarget]) rfl
  have eP : opsQ.eval (m + 3) (pp : Circ (m + 3)) =
      blk (m := m) (k := 3) (fun _ => opsQ.eval 3 (pp : Circ 3)) :=
    MS.eval_pad_blk m (pp : Circ 3)
  have cv : ∀ (z e d : Bool), mc 3 .box [boxTarget z] (boxCtl z e d) = box3 z e d := by
    intro z e d; apply mc_congr; cases z <;> ctl_tac
  have eX3 : mc 3 .box [boxTarget u] x = box3 u b true := (mc_congr _ _ _ hx).trans (cv u b true)
  have eY3 : mc 3 .box [boxTarget v] y = box3 v c false := (mc_congr _ _ _ hy).trans (cv v c false)
  simp only [drawn_two, map_mul, eX, eY, eP, blk_mul, eX3, eY3]
  congr 1; funext h
  split_ifs <;> try simp only [mul_one, one_mul]
  · exact (box_pp_eval u v b c).symm
  · have hP : opsQ.eval 3 (pp : Circ 3) * opsQ.eval 3 (pp : Circ 3) = 1 := by
      have h := SE.lcheck_sound (K := 3) true (l₁ := pp3L ++ pp3L) (l₂ := [])
        (by decide) (by simp) (by decide +kernel)
      change opsQ.eval 3 ((pp : Circ 3) * pp) = opsQ.eval 3 1 at h
      simpa only [map_mul, map_one] using h
    rw [hP, one_mul, mul_one]

end QCert.RealCliffordCH.Sec8.D.N13
