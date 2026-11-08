/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: soundness of Figure 7, r93–r101 and r_K

Translation of `Soundness/Figure7b.agda`: each relation a lemma typed by
the relation it proves (`Goal7`), decided by computing both sides' values
(`Soundness` dispatches to them).  The Agda states them at every level `k`;
`decide` does not accept a statement with a free level, so they are stated at
the levels at which they are used, `1` (`Σ₁`) and `2` (`Σ₂`).
-/
import QCert.ToffoliHadamardRS.Decide
import QCert.ToffoliHadamardRS.Syntactics

namespace QCert.ToffoliHadamardRS.Soundness.Figure7b

/-- The value of a relation of Figure 7 is sound. -/
abbrev Goal7 {k : ℕ} {w v : Word (Gate (k + 1))} (_ : Fig7 w v) : Prop := semO w = semO v

/-- The value of `r_K` is sound. -/
abbrev GoalK {k : ℕ} {w v : Word (Gate (k + 1))} (_ : RK w v) : Prop := semO w = semO v

theorem s93 : Goal7 (Fig7.r93 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s93' : Goal7 (Fig7.r93 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s94 : Goal7 (Fig7.r94 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s94' : Goal7 (Fig7.r94 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s95 : Goal7 (Fig7.r95 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s95' : Goal7 (Fig7.r95 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s96 : Goal7 (Fig7.r96 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s96' : Goal7 (Fig7.r96 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s97 : Goal7 (Fig7.r97 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s97' : Goal7 (Fig7.r97 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s98 : Goal7 (Fig7.r98 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s98' : Goal7 (Fig7.r98 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s99 : Goal7 (Fig7.r99 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s99' : Goal7 (Fig7.r99 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s100 : Goal7 (Fig7.r100 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s100' : Goal7 (Fig7.r100 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s101 : Goal7 (Fig7.r101 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s101' : Goal7 (Fig7.r101 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem sK : GoalK (RK.rK (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem sK' : GoalK (RK.rK (k := 1)) := semO_eq_of_check (by decide +kernel)

end QCert.ToffoliHadamardRS.Soundness.Figure7b
