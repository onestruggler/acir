/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Simpler presentations for many fragments of quantum circuits

C. Blake, *Simpler presentations for many fragments of quantum circuits*,
FSCD 2026, arXiv:2602.09874.  Six fragments, each a PROP presented by a rule
set with structural swaps (`QCert.Minimality.PropPresentation`):

| fragment | rules | semantics |
|---|---|---|
| qubit Clifford Cliff₂ | Figure 2 (`Clifford.pres`) | `Clifford.sem` |
| real Clifford RCliff₂ | Figure 3 (`RealClifford.pres`) | `RealClifford.sem` |
| qutrit Clifford Cliff₃ | Figure 4, (E) corrected (`QutritClifford.pres`) | `QutritClifford.sem` |
| Clifford+T CliffT₂ | Figure 5 (`CliffordT.pres`) | `CliffordT.sem` |
| Clifford+CS CliffCS₂ | Figure 6 (`CliffordCS.pres`) | `CliffordCS.sem` |
| CNOT-dihedral CNOTdihe₂ | Figure 7 (`CNOTDihedral.pres`) | `CNOTDihedral.sem` |

This file states, for each fragment, soundness, completeness (Theorem 22)
and minimality (Theorem 37).
-/
import QCert.Minimality.Clifford.Soundness
import QCert.Minimality.Clifford.Minimality
import QCert.Minimality.RealClifford.Soundness
import QCert.Minimality.RealClifford.Minimality
import QCert.Minimality.QutritClifford.Soundness
import QCert.Minimality.QutritClifford.Minimality
import QCert.Minimality.CliffordT.Soundness
import QCert.Minimality.CliffordT.Minimality
import QCert.Minimality.CliffordCS.Soundness
import QCert.Minimality.CliffordCS.Minimality
import QCert.Minimality.CNOTDihedral.Soundness
import QCert.Minimality.CNOTDihedral.Minimality
import QCert.Minimality.CNOTDihedral.Completeness
import QCert.Minimality.Clifford.Completeness
import QCert.Minimality.RealClifford.Completeness
import QCert.Minimality.QutritClifford.Completeness
import QCert.Minimality.CliffordT.Completeness
import QCert.Minimality.CliffordCS.Completeness

namespace QCert.Minimality

/-! ### Soundness (Section 3: the rule sets are sound for the semantics) -/

theorem clifford_sound {n : ℕ} {w v : Circuit Clifford.Gate n} (h : Clifford.pres.Proves n w v) :
    Clifford.sem.sem n w = Clifford.sem.sem n v := Clifford.sound h

theorem realClifford_sound {n : ℕ} {w v : Circuit RealClifford.Gate n}
    (h : RealClifford.pres.Proves n w v) : RealClifford.sem.sem n w = RealClifford.sem.sem n v :=
  RealClifford.sound h

theorem qutritClifford_sound {n : ℕ} {w v : Circuit QutritClifford.Gate n}
    (h : QutritClifford.pres.Proves n w v) :
    QutritClifford.sem.sem n w = QutritClifford.sem.sem n v := QutritClifford.sound h

theorem cliffordT_sound {n : ℕ} {w v : Circuit CliffordT.Gate n} (h : CliffordT.pres.Proves n w v) :
    CliffordT.sem.sem n w = CliffordT.sem.sem n v := CliffordT.sound h

theorem cliffordCS_sound {n : ℕ} {w v : Circuit CliffordCS.Gate n}
    (h : CliffordCS.pres.Proves n w v) : CliffordCS.sem.sem n w = CliffordCS.sem.sem n v :=
  CliffordCS.sound h

theorem cnotDihedral_sound {n : ℕ} {w v : Circuit CNOTDihedral.Gate n}
    (h : CNOTDihedral.pres.Proves n w v) : CNOTDihedral.sem.sem n w = CNOTDihedral.sem.sem n v :=
  CNOTDihedral.sound h

/-! ### Theorem 22: completeness -/

/-- Theorem 22 (1), the transfer: Cliff₂ is complete for qubit Clifford
circuits as soon as Selinger's presentation is (as formalised in
`QCert.SelingerClifford`). -/
theorem clifford_complete_of_source
    (hsrc : ∀ n (w v : Circuit QCert.SelingerClifford.Gate n),
      QCert.SelingerClifford.S.sem n w = QCert.SelingerClifford.S.sem n v →
        Derivable (QCert.SelingerClifford.Theory n) w v) :
    Clifford.pres.Complete fun n => Clifford.sem.sem n :=
  Clifford.complete_of_source hsrc

/-- Theorem 22 (1): Cliff₂ is complete for qubit Clifford circuits (through
`QCert.SelingerClifford.presentation`). -/
theorem clifford_complete : Clifford.pres.Complete fun n => Clifford.sem.sem n :=
  Clifford.complete

/-- Theorem 22 (2), the transfer: RCliff₂ is complete for real Clifford
circuits as soon as Makary, Ross and Selinger's presentation is (as
formalised in `QCert.RealStabilizer`, with real orthogonal matrices). -/
theorem realClifford_complete_of_source
    (hsrc : ∀ n (w v : Circuit QCert.RealStabilizer.Gate n),
      QCert.RealStabilizer.S.sem n w = QCert.RealStabilizer.S.sem n v →
        Derivable (QCert.RealStabilizer.Theory n) w v) :
    RealClifford.pres.Complete fun n => RealClifford.sem.sem n :=
  RealClifford.complete_of_source hsrc

/-- Theorem 22 (2): RCliff₂ is complete for real Clifford circuits (through
`QCert.RealStabilizer.presentation`). -/
theorem realClifford_complete : RealClifford.pres.Complete fun n => RealClifford.sem.sem n :=
  RealClifford.complete

/-- Theorem 22 (3), the transfer: Cliff₃ (with (E) corrected) is complete for
qutrit Clifford circuits as soon as Li, Mosca, Ross, van de Wetering and
Zhao's presentation is (as formalised in `QCert.QutritClifford`), through
its refinement by the new scalar `ω₁₂` (Lemma 50, proved). -/
theorem qutritClifford_complete_of_source
    (hsrc : ∀ n (w v : Circuit QCert.QutritClifford.Gate n),
      QCert.QutritClifford.gateSem.sem n w = QCert.QutritClifford.gateSem.sem n v →
        Derivable (QCert.QutritClifford.Theory n) w v) :
    QutritClifford.pres.Complete fun n => QutritClifford.sem.sem n :=
  QutritClifford.complete_of_source hsrc

/-- Theorem 22 (3): Cliff₃ (with (E) corrected) is complete for qutrit
Clifford circuits (through `QCert.QutritClifford.complete`). -/
theorem qutritClifford_complete :
    QutritClifford.pres.Complete fun n => QutritClifford.sem.sem n :=
  QutritClifford.complete

/-- Theorem 22 (4), the transfer: CliffT₂ is complete for Clifford+T circuits
up to two qubits as soon as Bian and Selinger's two-qubit presentation and
Greylyn's presentations of `U₂(ℤ[1/√2, i])` and `U₁(ℤ[1/√2, i])` are. -/
theorem cliffordT_complete_of_source
    (h₂ : ∀ a b : Word QCert.CliffordT2.Gen,
      FreeMonoid.lift QCert.CliffordT2.sem a = FreeMonoid.lift QCert.CliffordT2.sem b →
        Derivable QCert.CliffordT2.Rel a b)
    (h₁ : ∀ a b : Word (QCert.Greylyn.Gen 2),
      FreeMonoid.lift (QCert.Greylyn.sem 2) a = FreeMonoid.lift (QCert.Greylyn.sem 2) b →
        Derivable (QCert.Greylyn.Rel 2) a b)
    (h₀ : ∀ a b : Word (QCert.Greylyn.Gen 1),
      FreeMonoid.lift (QCert.Greylyn.sem 1) a = FreeMonoid.lift (QCert.Greylyn.sem 1) b →
        Derivable (QCert.Greylyn.Rel 1) a b) :
    CliffordT.pres.CompleteUpTo (fun n => CliffordT.sem.sem n) 2 :=
  CliffordT.complete_of_source h₂ h₁ h₀

/-- Theorem 22 (4): CliffT₂ is complete for Clifford+T circuits up to two
qubits (through `QCert.CliffordT2.theorem_2_1` and
`QCert.Greylyn.presentation`). -/
theorem cliffordT_complete : CliffordT.pres.CompleteUpTo (fun n => CliffordT.sem.sem n) 2 :=
  CliffordT.complete

/-- Theorem 22 (5) with no wire and on one wire, the transfer: from Bian and
Selinger's presentation of `Uₘ(ℤ[½, i])` in dimensions `1` and `2`, refined
by the new scalar (Lemma 50, proved). -/
theorem cliffordCS_complete₀₁_of_source
    (h₁ : ∀ a b : Word (QCert.BianSelingerUn.Gen 2),
      FreeMonoid.lift (QCert.BianSelingerUn.sem 2) a =
        FreeMonoid.lift (QCert.BianSelingerUn.sem 2) b →
        Derivable (QCert.BianSelingerUn.Rel 2) a b)
    (h₀ : ∀ a b : Word (QCert.BianSelingerUn.Gen 1),
      FreeMonoid.lift (QCert.BianSelingerUn.sem 1) a =
        FreeMonoid.lift (QCert.BianSelingerUn.sem 1) b →
        Derivable (QCert.BianSelingerUn.Rel 1) a b) :
    CliffordCS.pres.CompleteUpTo (fun n => CliffordCS.sem.sem n) 1 := by
  intro n hn w v h
  match n, hn with
  | 0, _ => exact CliffordCS.complete₀_of_source h₀ w v h
  | 1, _ => exact CliffordCS.complete₁_of_source h₁ w v h

/-- Theorem 22 (5): CliffCS₂ is complete for Clifford+CS circuits up to three
qubits.  With no wire and on one wire it is proved (`complete₀_of_source`,
`complete₁_of_source` with `QCert.BianSelingerUn.presentation`); on two and
three wires it is not yet. -/
theorem cliffordCS_complete : CliffordCS.pres.CompleteUpTo (fun n => CliffordCS.sem.sem n) 3 := by
  intro n hn w v h
  match n, hn with
  | 0, _ =>
    exact CliffordCS.complete₀_of_source
      (fun _ _ h => (QCert.BianSelingerUn.presentation 1).complete h) w v h
  | 1, _ =>
    exact CliffordCS.complete₁_of_source
      (fun _ _ h => (QCert.BianSelingerUn.presentation 2).complete h) w v h
  | 2, _ => sorry
  | 3, _ => sorry

/-- Theorem 22 (6), the transfer: CNOTdihe₂ is complete for CNOT-dihedral
circuits as soon as Amy, Chen and Ross's presentation is (as formalised in
`QCert.CNOTDihedral`). -/
theorem cnotDihedral_complete_of_source
    (hsrc : ∀ n (w v : Circuit QCert.CNOTDihedral.Gate n),
      QCert.CNOTDihedral.S.sem n w = QCert.CNOTDihedral.S.sem n v →
        Derivable (QCert.CNOTDihedral.Theory n) w v) :
    CNOTDihedral.pres.Complete fun n => CNOTDihedral.sem.sem n :=
  CNOTDihedral.complete_of_source hsrc

/-- Theorem 22 (6): CNOTdihe₂ is complete for CNOT-dihedral circuits (through
`QCert.CNOTDihedral.presentation`). -/
theorem cnotDihedral_complete : CNOTDihedral.pres.Complete fun n => CNOTDihedral.sem.sem n :=
  CNOTDihedral.complete

/-- Theorem 22 (6) as a presentation: on every number of wires, CNOTdihe₂
presents the group generated by the CNOT-dihedral gates. -/
theorem cnotDihedral_presentation (n : ℕ) :
    IsSubPresentationOf (Lift (Padded (CNOTDihedral.pres.Base fun _ => True)) n)
      (CNOTDihedral.sem.gen (n := n)) :=
  CNOTDihedral.presentation n

/-! ### Theorem 37: minimality -/

/-- Theorem 37 (1): Cliff₂ is minimal (all arities). -/
theorem clifford_minimal : Clifford.pres.Minimal := Clifford.minimal

/-- Theorem 37 (2): RCliff₂ is minimal (all arities). -/
theorem realClifford_minimal : RealClifford.pres.Minimal := RealClifford.minimal

/-- Theorem 37 (3): Cliff₃ is minimal up to two qutrit wires. -/
theorem qutritClifford_minimalUpTo_two : QutritClifford.pres.MinimalUpTo 2 :=
  QutritClifford.minimalUpTo_two

/-- Theorem 37 (4): CliffT₂ is minimal up to one qubit wire. -/
theorem cliffordT_minimalUpTo_one : CliffordT.pres.MinimalUpTo 1 := CliffordT.minimalUpTo_one

/-- Theorem 37 (5): CliffCS₂ is minimal up to two qubit wires. -/
theorem cliffordCS_minimalUpTo_two : CliffordCS.pres.MinimalUpTo 2 := CliffordCS.minimalUpTo_two

/-- Theorem 37 (6): CNOTdihe₂ is minimal (all arities). -/
theorem cnotDihedral_minimal : CNOTDihedral.pres.Minimal := CNOTDihedral.minimal

/-- Theorem 37: in CliffT₂ the two-qubit axioms (CPh), (B) and (CZ) are
independent. -/
theorem cliffordT_independent_two :
    CliffordT.pres.Independent .CPh ∧ CliffordT.pres.Independent .B ∧
      CliffordT.pres.Independent .CZ :=
  ⟨CliffordT.independent_CPh, CliffordT.independent_B, CliffordT.independent_CZ⟩

/-- Theorem 37: in CliffCS₂ the three-qubit axiom (I) is independent. -/
theorem cliffordCS_independent_I : CliffordCS.pres.Independent .I := CliffordCS.independent_I

end QCert.Minimality
