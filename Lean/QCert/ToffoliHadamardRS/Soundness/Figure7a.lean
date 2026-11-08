/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: soundness of Figure 7, r83–r92

Translation of `Soundness/Figure7a.agda`: each relation a lemma typed by
the relation it proves (`Goal7`), decided by computing both sides' values
(`Soundness` dispatches to them).  The Agda states them at every level `k`;
`decide` does not accept a statement with a free level, so they are stated at
the levels at which they are used, `1` (`Σ₁`) and `2` (`Σ₂`).
-/
import QCert.ToffoliHadamardRS.Decide
import QCert.ToffoliHadamardRS.Syntactics

namespace QCert.ToffoliHadamardRS.Soundness.Figure7a

/-- The value of a relation of Figure 7 is sound. -/
abbrev Goal7 {k : ℕ} {w v : Word (Gate (k + 1))} (_ : Fig7 w v) : Prop := semO w = semO v


theorem s83 : Goal7 (Fig7.r83 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s83' : Goal7 (Fig7.r83 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s84 : Goal7 (Fig7.r84 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s84' : Goal7 (Fig7.r84 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s85 : Goal7 (Fig7.r85 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s85' : Goal7 (Fig7.r85 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s86 : Goal7 (Fig7.r86 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s86' : Goal7 (Fig7.r86 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s87 : Goal7 (Fig7.r87 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s87' : Goal7 (Fig7.r87 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s88 : Goal7 (Fig7.r88 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s88' : Goal7 (Fig7.r88 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s89 : Goal7 (Fig7.r89 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s89' : Goal7 (Fig7.r89 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s90 : Goal7 (Fig7.r90 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s90' : Goal7 (Fig7.r90 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s91 : Goal7 (Fig7.r91 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s91' : Goal7 (Fig7.r91 (k := 1)) := semO_eq_of_check (by decide +kernel)

theorem s92 : Goal7 (Fig7.r92 (k := 0)) := semO_eq_of_check (by decide +kernel)

theorem s92' : Goal7 (Fig7.r92 (k := 1)) := semO_eq_of_check (by decide +kernel)

end QCert.ToffoliHadamardRS.Soundness.Figure7a
