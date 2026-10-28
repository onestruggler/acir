/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equations (320) and (321), every colour

The box on wire `0` whose controls are the wires `1, 2, 3` (colours
`b₁, b₂, b₃`) and the bulk is a product of eight gates: the triply
controlled rotations on the wires `0, …, 3` and the box idle on wire `3`
(`pcs`).  For `b₁ = b₂ = b₃ = 1` this is (320): from (295), whose box
without controls on the wires `2, 3` is the box with `2` black times the box
with `2` white (a semantic step without wire `3`); the latter passes the
rotations by (318) and (319), and the two copies of it cancel.  The other
colours, (321) among them, by `X` on the wires `1, 2, 3`: (81) for the box,
and for the eight gates semantic steps (without wire `4` for the rotations,
without wire `3` for the box) or, for `X` on wire `3` and the box idle on
it, `qcommE`.
-/
import QCert.RealCliffordCH.Sec8.D.N13.Kit2
import QCert.RealCliffordCH.Sec8.D.N13.E319

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-! ## The letters -/

/-- The box on wire `0`, controls `1, 2, 3` (colours `b₁, b₂, b₃`), `4` and
the bulk. -/
def bxC (b1 b2 b3 : Bool) : Lt := .g .box [0] [(1, b1), (2, b2), (3, b3), (4, true)] true
def P1 (b1 b2 b3 : Bool) : Lt := .g .zx [0] [(1, b1), (2, b2), (3, b3)] false
def P2 (b1 b2 b3 : Bool) : Lt := .g (Kind.sgnZX (!b1)) [1] [(0, true), (2, b2), (3, b3)] false
def P3 (b1 b2 : Bool) : Lt := .g .box [0] [(1, b1), (2, b2), (4, true)] true
def P4 (b1 b2 b3 : Bool) : Lt := .g (Kind.sgnZX b1) [1] [(0, true), (2, b2), (3, b3)] false
def P5 (b1 b2 b3 : Bool) : Lt := .g .xz [0] [(1, b1), (2, b2), (3, b3)] false

/-- The right-hand side of (320) and (321). -/
def pcs (b1 b2 b3 : Bool) : List Lt :=
  [P1 b1 b2 b3, P2 b1 b2 b3, P3 b1 b2, P4 b1 b2 b3, P5 b1 b2 b3, P2 b1 b2 b3, P3 b1 b2, P4 b1 b2 b3]

/-! ## (320) -/

theorem t295 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bxC true true true])
      (wc 5 (m + 5) [Zc, Rg false true, Bc, Rg true true, Wl true true true, Rg false true, Bc,
        Rg true true]) := by
  have h := N8.eq295_5 m ih
  have e0 : (bxC true true true).circ 5 (m + 5) = Bx (m + 5) := mc_congr _ _ _ (by ctl_tac)
  have e1 : Zc.circ 5 (m + 5) = mc (m + 5) .zx [0] (blackOn 1 4) := mc_congr _ _ _ (by ctl_tac)
  have e2 : (Rg false true).circ 5 (m + 5) =
      mc (m + 5) .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)) := mc_congr _ _ _ (by ctl_tac)
  have e3 : Bc.circ 5 (m + 5) = mc (m + 5) .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 (m + 5))) :=
    mc_congr _ _ _ (by ctl_tac)
  have e4 : (Rg true true).circ 5 (m + 5) =
      mc (m + 5) .xz [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)) := mc_congr _ _ _ (by ctl_tac)
  have e5 : (Wl true true true).circ 5 (m + 5) = mc (m + 5) .xz [0] (blackOn 1 4) :=
    mc_congr _ _ _ (by ctl_tac)
  rw [wc_one', e0]
  simp only [wc, List.map_cons, List.map_nil, e1, e2, e3, e4, e5]
  exact h

def T320 : SE.Tbl :=
  [([bxC true true true],
     [Zc, Rg false true, Bc, Rg true true, Wl true true true, Rg false true, Bc, Rg true true]),
   ([Rg true true, Bq true], [Bq true, Rg true true]),
   ([Wl true true true, Bq true], [Bq true, Wl true true true]),
   ([Rg false true, Bq true], [Bq true, Rg false true])]

theorem T320_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T320 := by
  intro e he
  simp only [T320, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact t295 m ih
  · exact r318 m ih true true true
  · exact r319 m ih true true true true
  · exact r318 m ih false true true

theorem run320 : check 4 T320 [bxC true true true] (pcs true true true)
    [.rw 0 0 false, .sem 2 1 [E1, Bq true] 3, .rw 3 1 true, .rw 4 2 true, .rw 5 3 true,
     .sem 6 2 [E1] 3] = true := by
  decide +kernel

/-! ## Every colour -/

/-- The gates `pcs` after `X` on wire `j ∈ {1, 2}`: each passes `X`, changing
its colour (semantic steps), and `X X = 1`. -/
def flipSteps12 (j : ℕ) (P' : List Lt) : List St :=
  (List.range 8).map (fun i => .sem i 4 [P'.getD i (.s (.H 0)), .s (.H j), .s (.Z j), .s (.H j)]
    (if i = 2 ∨ i = 6 then 3 else 4)) ++ [.sem 8 6 [] 0]

/-- The same for `X` on wire `3`, which the boxes pass by `qcommE`. -/
def flipSteps3 (P' : List Lt) : List St :=
  ((List.range 8).map (fun i => if i = 2 ∨ i = 6 then [.rw (i + 2) 0 true, .rw (i + 1) 1 true,
    .rw i 0 true] else [.sem i 4 [P'.getD i (.s (.H 0)), .s (.H 3), .s (.Z 3), .s (.H 3)] 4])).flatten ++
    [.sem 8 6 [] 0]

def TQ3 (b1 b2 : Bool) : SE.Tbl :=
  [([P3 b1 b2, .s (.H 3)], [.s (.H 3), P3 b1 b2]), ([P3 b1 b2, .s (.Z 3)], [.s (.Z 3), P3 b1 b2])]

theorem TQ3_ok (m : ℕ) (b1 b2 : Bool) : AllD 5 m (TQ3 b1 b2) := by
  intro e he
  simp only [TQ3, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact qcommE m 4 3 (by omega) (P3 b1 b2) (by cases b1 <;> cases b2 <;> decide)
      (by cases b1 <;> cases b2 <;> decide) _ (Or.inl rfl)
  · exact qcommE m 4 3 (by omega) (P3 b1 b2) (by cases b1 <;> cases b2 <;> decide)
      (by cases b1 <;> cases b2 <;> decide) _ (Or.inr rfl)

theorem chkFlip1 : ∀ b2 b3 : Bool, check 4 [] (xL 1 ++ pcs true b2 b3 ++ xL 1) (pcs false b2 b3)
    (flipSteps12 1 (pcs false b2 b3)) = true := by
  decide +kernel

theorem chkFlip2 : ∀ b1 b3 : Bool, check 4 [] (xL 2 ++ pcs b1 true b3 ++ xL 2) (pcs b1 false b3)
    (flipSteps12 2 (pcs b1 false b3)) = true := by
  decide +kernel

theorem chkFlip3 : ∀ b1 b2 : Bool, check 4 (TQ3 b1 b2) (xL 3 ++ pcs b1 b2 true ++ xL 3)
    (pcs b1 b2 false) (flipSteps3 (pcs b1 b2 false)) = true := by
  decide +kernel

/-- (320) and (321) on five local wires, every colour of the wires `1, 2, 3`. -/
theorem exp320 (m : ℕ) (ih : IH (m + 5)) (b1 b2 b3 : Bool) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bxC b1 b2 b3]) (wc 5 (m + 5) (pcs b1 b2 b3)) := by
  have base : Derivable (theory (m + 5)) (wc 5 (m + 5) [bxC true true true])
      (wc 5 (m + 5) (pcs true true true)) := check_sound (frame 4) ih (T320_ok m ih) run320
  have f1 : ∀ b2 b3, Derivable (theory (m + 5)) (wc 5 (m + 5) [bxC true b2 b3])
      (wc 5 (m + 5) (pcs true b2 b3)) →
      Derivable (theory (m + 5)) (wc 5 (m + 5) [bxC false b2 b3]) (wc 5 (m + 5) (pcs false b2 b3)) :=
    fun b2 b3 d => conj_exp (j := 1) d
      (flip81 .box [0] _ _ true 1 true (by omega) (by decide) rfl (by ctl_tac))
      (check_sound (frame 4) ih (allD_nil 5 m) (chkFlip1 b2 b3))
  have f2 : ∀ b1 b3, Derivable (theory (m + 5)) (wc 5 (m + 5) [bxC b1 true b3])
      (wc 5 (m + 5) (pcs b1 true b3)) →
      Derivable (theory (m + 5)) (wc 5 (m + 5) [bxC b1 false b3]) (wc 5 (m + 5) (pcs b1 false b3)) :=
    fun b1 b3 d => conj_exp (j := 2) d
      (flip81 .box [0] _ _ true 2 true (by omega) (by decide) rfl (by ctl_tac))
      (check_sound (frame 4) ih (allD_nil 5 m) (chkFlip2 b1 b3))
  have f3 : ∀ b1 b2, Derivable (theory (m + 5)) (wc 5 (m + 5) [bxC b1 b2 true])
      (wc 5 (m + 5) (pcs b1 b2 true)) →
      Derivable (theory (m + 5)) (wc 5 (m + 5) [bxC b1 b2 false]) (wc 5 (m + 5) (pcs b1 b2 false)) :=
    fun b1 b2 d => conj_exp (j := 3) d
      (flip81 .box [0] _ _ true 3 true (by omega) (by decide) rfl (by ctl_tac))
      (check_sound (frame 4) ih (TQ3_ok m b1 b2) (chkFlip3 b1 b2))
  have g1 : ∀ b1, Derivable (theory (m + 5)) (wc 5 (m + 5) [bxC b1 true true])
      (wc 5 (m + 5) (pcs b1 true true)) := by
    intro b1; cases b1
    · exact f1 _ _ base
    · exact base
  have g2 : ∀ b1 b2, Derivable (theory (m + 5)) (wc 5 (m + 5) [bxC b1 b2 true])
      (wc 5 (m + 5) (pcs b1 b2 true)) := by
    intro b1 b2; cases b2
    · exact f2 _ _ (g1 b1)
    · exact g1 b1
  cases b3
  · exact f3 _ _ (g2 b1 b2)
  · exact g2 b1 b2

end QCert.RealCliffordCH.Sec8.D.N13
