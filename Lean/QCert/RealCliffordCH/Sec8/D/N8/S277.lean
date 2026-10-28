/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (276) and (277) at every width

On five local wires.  (276), `P ⊗ P` on the wires `0, 1` around the box on
wire `1` (wire `0` idle), is a chain of semantic steps: the box written as in
(284) one width down, the `P ⊗ P` passed through each factor (a three-wire
identity, or Lemma 5.1 with wire `3` removed), and the two `P ⊗ P` cancelled
(`s276`).  (277) is the paper's chain: the multi-controlled `H` as the box
between two `P ⊗ P`, (276), the Klein four-group of the `P ⊗ P` on three
wires, (274), and back (`s277`).
-/
import QCert.RealCliffordCH.Sec8.D.N8.S274

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE

/-- `P ⊗ P` on the wires `i, i + 1` (its wire `0` on `i`). -/
def ppL (i : ℕ) : List Lt :=
  [.s (.K i), .s (.H (i + 1)), .s (.Z i), .s (.K i), .s (.H (i + 1)), .s (.Z i), .s (.K i),
    .s (.H (i + 1)), .s (.Z i), .s (.S i)]

/-- `P ⊗ P` on the wires `0, 2`. -/
def pp02 : List Lt := [.s (.S 1)] ++ ppL 0 ++ [.s (.S 1)]

def zxA : Lt := .g .zx [1] [(2, true), (3, true)] false
def xzA : Lt := .g .xz [1] [(2, true), (3, true)] false
/-- The multi-controlled `H` with box wire `2`, `H` on wire `1`, controls `4`
and the bulk. -/
def hgA : Lt := .g .hg [2, 1] [(4, true)] true
def bxQ : Lt := .g .box [2] [(1, true), (4, true)] true

theorem run276 : check 4 [] (ppL 0 ++ [B1] ++ ppL 0) [B1]
    [.sem 10 1 [zxA, hgA, xzA, hgA] 0,
     .sem 0 11 ([xzA] ++ ppL 0) 4, .sem 1 11 ([bxQ] ++ ppL 0) 3,
     .sem 2 11 ([zxA] ++ ppL 0) 4, .sem 3 11 ([bxQ] ++ ppL 0) 3,
     .sem 4 20 [] 4, .sem 0 4 [B1] 0] = true := by
  decide +kernel

/-- (276) on five local wires. -/
theorem s276 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) (ppL 0 ++ [B1] ++ ppL 0)) (wc 5 (m + 5) [B1]) :=
  check_sound (frame 4) ih (T := []) (fun _ h => by simp at h) run276

/-- The multi-controlled `H`, box wire `1`, `H` on wire `2`, wire `0` idle. -/
def hg12 : Lt := .g .hg [1, 2] [(3, true), (4, true)] true
/-- The multi-controlled `H`, box wire `0`, `H` on wire `2`, wire `1` idle. -/
def hg02 : Lt := swapG 1 .hg [0, 1] [(3, true), (4, true)] true
def hg01 : Lt := .g .hg [0, 1] [(3, true), (4, true)] true
def B0p : Lt := swapG 1 .box [0] [(2, true), (3, true), (4, true)] true

theorem hg02_eq : hg02 = .g .hg [0, 2] [(3, true), (4, true)] true := by decide

def T277 : SE.Tbl :=
  [(ppL 0 ++ [B1] ++ ppL 0, [B1]),
   ([B1], [B0]),
   ([.s (.S 1), B0, .s (.S 1)], [B0p]),
   ([.s (.S 1), hg01, .s (.S 1)], [hg02])]

theorem T277_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T277 := by
  intro e he
  simp only [T277, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact s276 m ih
  · exact s274 m ih
  · exact swE m 1 (by omega) _ _ _ _ (by decide) (by decide)
  · exact swE m 1 (by omega) _ _ _ _ (by decide) (by decide)

theorem run277 : check 4 T277 [hg12] [hg02]
    [.sem 0 1 (ppL 1 ++ [B1] ++ ppL 1) 0,
     .rw 10 0 true,
     .sem 0 20 pp02 3,
     .sem 13 20 pp02 3,
     .rw 12 1 false,
     .rw 11 2 false,
     .sem 1 21 [hg01] 2,
     .rw 0 3 false] = true := by
  decide +kernel

/-- (277) on five local wires. -/
theorem s277 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [hg12]) (wc 5 (m + 5) [hg02]) :=
  check_sound (frame 4) ih (T277_ok m ih) run277

end QCert.RealCliffordCH.Sec8.D.N8
