/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clément's relations hold in Figure 6

Every relation (1)–(22) of Clément, at every instance, is derivable in
Hadamard-Π's Figure 6 once its words are written over `𝒢ₙ` by `tr`
(`rel_fig6`).  For (1)–(19) and (22) this is a scheme on `a ≤ 4` indices
(`sch…`), checked at each of the `a!` arrangements of its indices by the
tables of `Tables.lean` (`Patterns.good_of_check`) and carried to any
distinct indices by sorting them (`Patterns.Good.apply`); for (19) the
tables conjugate Hadamard-Π's (f1) by the `X`'s of adjacent transpositions.
(20) and (21) are on increasing indices, where `tr` changes nothing, and are
`HadamardPi.c20` and `HadamardPi.c21` (`HadamardPi/Derived.lean`).
-/
import QCert.Clement2019.Patterns
import QCert.Clement2019.Tables
import QCert.HadamardPi.Derived

namespace QCert.Clement2019

open FreeMonoid
open HadamardPi (Fig6 der_map)

variable {n : ℕ}

/-- Apply a good scheme to the `tr` image of an instance. -/
theorem Good.tr {a : ℕ} {L R : List (RL a)} (hG : Good L R) (x : Fin a → Fin n)
    (hx : Function.Injective x) {w v : Word (Gen n)}
    (hw : w.toList.map Gen.raw = L.map (RL.map x)) (hv : v.toList.map Gen.raw = R.map (RL.map x)) :
    Derivable Fig6 (tr w) (tr v) := by
  rw [tr_eq, tr_eq, hw, hv]; exact hG.apply x hx

/-! The schemes, on the indices `0, …, a-1` in the order of the constructor's
arguments (as `gen/gen_tables.py`'s `SCHEMES`). -/

def sch1 : List (RL 1) × List (RL 1) := ([.z 0, .z 0], [])
def sch2 : List (RL 2) × List (RL 2) := ([.h 0 1, .h 0 1], [])
def sch3 : List (RL 2) × List (RL 2) := ([.x 0 1, .x 0 1], [])
def sch4 : List (RL 2) × List (RL 2) := ([.z 0, .z 1], [.z 1, .z 0])
def sch5 : List (RL 3) × List (RL 3) := ([.z 2, .h 0 1], [.h 0 1, .z 2])
def sch6 : List (RL 3) × List (RL 3) := ([.z 2, .x 0 1], [.x 0 1, .z 2])
def sch7 : List (RL 4) × List (RL 4) := ([.h 0 1, .h 2 3], [.h 2 3, .h 0 1])
def sch8 : List (RL 4) × List (RL 4) := ([.h 0 1, .x 2 3], [.x 2 3, .h 0 1])
def sch9 : List (RL 4) × List (RL 4) := ([.x 0 1, .x 2 3], [.x 2 3, .x 0 1])
def sch10 : List (RL 2) × List (RL 2) := ([.x 0 1, .z 1], [.z 0, .x 0 1])
def sch11 : List (RL 2) × List (RL 2) := ([.x 0 1, .z 0], [.z 1, .x 0 1])
def sch12 : List (RL 3) × List (RL 3) := ([.x 0 1, .x 0 2], [.x 1 2, .x 0 1])
def sch13 : List (RL 3) × List (RL 3) := ([.x 0 1, .x 2 0], [.x 2 1, .x 0 1])
def sch14 : List (RL 3) × List (RL 3) := ([.x 0 1, .h 0 2], [.h 1 2, .x 0 1])
def sch15 : List (RL 3) × List (RL 3) := ([.x 0 1, .h 2 0], [.h 2 1, .x 0 1])
def sch16 : List (RL 2) × List (RL 2) := ([.z 0, .z 1, .x 0 1], [.x 0 1, .z 0, .z 1])
def sch17 : List (RL 2) × List (RL 2) := ([.z 0, .z 1, .h 0 1], [.h 0 1, .z 0, .z 1])
def sch18 : List (RL 2) × List (RL 2) := ([.h 0 1, .x 0 1], [.z 1, .h 0 1])
def sch19 : List (RL 4) × List (RL 4) :=
  ([.h 0 1, .h 2 3, .h 0 2, .h 1 3], [.h 0 2, .h 1 3, .h 0 1, .h 2 3])
def sch22 : List (RL 2) × List (RL 2) := ([.x 0 1, .h 0 1], [.h 1 0, .x 0 1])
def sch20 : List (RL 4) × List (RL 4) :=
  ([.h 0 1, .h 0 2, .h 1 3, .h 0 1, .z 0, .z 1, .h 0 2, .h 1 3],
    [.h 0 2, .h 1 3, .h 0 1, .z 0, .z 1, .h 0 2, .h 1 3, .h 0 1])
def sch21 : List (RL 6) × List (RL 6) :=
  ([.h 0 1, .h 0 2, .h 1 3, .h 0 4, .h 1 5, .h 0 1, .z 0, .z 1, .h 0 4, .h 1 5, .h 0 2, .h 1 3],
    [.h 0 2, .h 1 3, .h 0 4, .h 1 5, .h 0 1, .z 0, .z 1, .h 0 4, .h 1 5, .h 0 2, .h 1 3, .h 0 1])

theorem good1 : Good sch1.1 sch1.2 := good_of_check _ _ ClementFig6.tbl1 (by decide +kernel)
theorem good2 : Good sch2.1 sch2.2 := good_of_check _ _ ClementFig6.tbl2 (by decide +kernel)
theorem good3 : Good sch3.1 sch3.2 := good_of_check _ _ ClementFig6.tbl3 (by decide +kernel)
theorem good4 : Good sch4.1 sch4.2 := good_of_check _ _ ClementFig6.tbl4 (by decide +kernel)
theorem good5 : Good sch5.1 sch5.2 := good_of_check _ _ ClementFig6.tbl5 (by decide +kernel)
theorem good6 : Good sch6.1 sch6.2 := good_of_check _ _ ClementFig6.tbl6 (by decide +kernel)
theorem good7 : Good sch7.1 sch7.2 := good_of_check _ _ ClementFig6.tbl7 (by decide +kernel)
theorem good8 : Good sch8.1 sch8.2 := good_of_check _ _ ClementFig6.tbl8 (by decide +kernel)
theorem good9 : Good sch9.1 sch9.2 := good_of_check _ _ ClementFig6.tbl9 (by decide +kernel)
theorem good10 : Good sch10.1 sch10.2 := good_of_check _ _ ClementFig6.tbl10 (by decide +kernel)
theorem good11 : Good sch11.1 sch11.2 := good_of_check _ _ ClementFig6.tbl11 (by decide +kernel)
theorem good12 : Good sch12.1 sch12.2 := good_of_check _ _ ClementFig6.tbl12 (by decide +kernel)
theorem good13 : Good sch13.1 sch13.2 := good_of_check _ _ ClementFig6.tbl13 (by decide +kernel)
theorem good14 : Good sch14.1 sch14.2 := good_of_check _ _ ClementFig6.tbl14 (by decide +kernel)
theorem good15 : Good sch15.1 sch15.2 := good_of_check _ _ ClementFig6.tbl15 (by decide +kernel)
theorem good16 : Good sch16.1 sch16.2 := good_of_check _ _ ClementFig6.tbl16 (by decide +kernel)
theorem good17 : Good sch17.1 sch17.2 := good_of_check _ _ ClementFig6.tbl17 (by decide +kernel)
theorem good18 : Good sch18.1 sch18.2 := good_of_check _ _ ClementFig6.tbl18 (by decide +kernel)
theorem good19 : Good sch19.1 sch19.2 := good_of_check _ _ ClementFig6.tbl19 (by decide +kernel)
theorem good22 : Good sch22.1 sch22.2 := good_of_check _ _ ClementFig6.tbl22 (by decide +kernel)

/-- A scheme on increasing indices, from its instance at `0, …, a-1`. -/
theorem goodId_tr {a : ℕ} {L R : List (RL a)}
    (h : Derivable Fig6 (ofList (trL L)) (ofList (trL R))) (x : Fin a → Fin n) (hx : StrictMono x)
    {w v : Word (Gen n)} (hw : w.toList.map Gen.raw = L.map (RL.map x))
    (hv : v.toList.map Gen.raw = R.map (RL.map x)) : Derivable Fig6 (tr w) (tr v) := by
  rw [tr_eq, tr_eq, hw, hv, trL_map x hx, trL_map x hx]
  exact der_map x hx h

theorem tr_sch20 : Derivable Fig6 (ofList (trL sch20.1)) (ofList (trL sch20.2)) := by
  have e1 : trL sch20.1 = [HadamardPi.hL 0 1, HadamardPi.hL 0 2, HadamardPi.hL 1 3,
      HadamardPi.hL 0 1, HadamardPi.zL 0, HadamardPi.zL 1, HadamardPi.hL 0 2,
      HadamardPi.hL 1 3] := by decide
  have e2 : trL sch20.2 = [HadamardPi.hL 0 2, HadamardPi.hL 1 3, HadamardPi.hL 0 1,
      HadamardPi.zL 0, HadamardPi.zL 1, HadamardPi.hL 0 2, HadamardPi.hL 1 3,
      HadamardPi.hL 0 1] := by decide
  rw [e1, e2]; exact HadamardPi.c20

theorem tr_sch21 : Derivable Fig6 (ofList (trL sch21.1)) (ofList (trL sch21.2)) := by
  have e1 : trL sch21.1 = [HadamardPi.hL 0 1, HadamardPi.hL 0 2, HadamardPi.hL 1 3,
      HadamardPi.hL 0 4, HadamardPi.hL 1 5, HadamardPi.hL 0 1, HadamardPi.zL 0, HadamardPi.zL 1,
      HadamardPi.hL 0 4, HadamardPi.hL 1 5, HadamardPi.hL 0 2, HadamardPi.hL 1 3] := by decide
  have e2 : trL sch21.2 = [HadamardPi.hL 0 2, HadamardPi.hL 1 3, HadamardPi.hL 0 4,
      HadamardPi.hL 1 5, HadamardPi.hL 0 1, HadamardPi.zL 0, HadamardPi.zL 1, HadamardPi.hL 0 4,
      HadamardPi.hL 1 5, HadamardPi.hL 0 2, HadamardPi.hL 1 3, HadamardPi.hL 0 1] := by decide
  rw [e1, e2]; exact HadamardPi.c21

/-- Each of Clément's relations holds in Figure 6, written over `𝒢ₙ`. -/
theorem rel_fig6 {w v : Word (Gen n)} (h : Rel w v) : Derivable Fig6 (tr w) (tr v) := by
  cases h with
  | r1 j => exact good1.tr ![j] (by vec_inj) rfl rfl
  | @r2 j k h => exact good2.tr ![j, k] (by vec_inj) rfl rfl
  | @r3 j k h => exact good3.tr ![j, k] (by vec_inj) rfl rfl
  | @r4 j k h => exact good4.tr ![j, k] (by vec_inj) rfl rfl
  | @r5 j k l h1 h2 h3 => exact good5.tr ![j, k, l] (by vec_inj) rfl rfl
  | @r6 j k l h1 h2 h3 => exact good6.tr ![j, k, l] (by vec_inj) rfl rfl
  | @r7 j k l t h1 h2 h3 h4 h5 h6 => exact good7.tr ![j, k, l, t] (by vec_inj) rfl rfl
  | @r8 j k l t h1 h2 h3 h4 h5 h6 => exact good8.tr ![j, k, l, t] (by vec_inj) rfl rfl
  | @r9 j k l t h1 h2 h3 h4 h5 h6 => exact good9.tr ![j, k, l, t] (by vec_inj) rfl rfl
  | @r10 j k h => exact good10.tr ![j, k] (by vec_inj) rfl rfl
  | @r11 j k h => exact good11.tr ![j, k] (by vec_inj) rfl rfl
  | @r12 j k l h1 h2 h3 => exact good12.tr ![j, k, l] (by vec_inj) rfl rfl
  | @r13 j k l h1 h2 h3 => exact good13.tr ![j, k, l] (by vec_inj) rfl rfl
  | @r14 j k l h1 h2 h3 => exact good14.tr ![j, k, l] (by vec_inj) rfl rfl
  | @r15 j k l h1 h2 h3 => exact good15.tr ![j, k, l] (by vec_inj) rfl rfl
  | @r16 j k h => exact good16.tr ![j, k] (by vec_inj) rfl rfl
  | @r17 j k h => exact good17.tr ![j, k] (by vec_inj) rfl rfl
  | @r18 j k h => exact good18.tr ![j, k] (by vec_inj) rfl rfl
  | @r19 j k l t h1 h2 h3 h4 h5 =>
    by_cases hkl : k = l
    · subst hkl; exact Derivable.refl _
    · exact good19.tr ![j, k, l, t] (by vec_inj) rfl rfl
  | r20 hn => exact goodId_tr tr_sch20 (Fin.castLE hn) (Fin.strictMono_castLE hn) rfl rfl
  | r21 hn => exact goodId_tr tr_sch21 (Fin.castLE hn) (Fin.strictMono_castLE hn) rfl rfl
  | @r22 hn j k h => exact good22.tr ![j, k] (by vec_inj) rfl rfl

end QCert.Clement2019
