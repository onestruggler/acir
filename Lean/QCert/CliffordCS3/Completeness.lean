/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Three-qubit Clifford+CS: completeness

Section 3.1 of Bian–Selinger (arXiv:2306.08530): the three-qubit
Clifford+CS group is the subgroup of `G = U₈(ℤ[1/2, i])` of the
matrices with determinant `±1`, of index 2, and Theorem 3.1 follows from
the presentation of `G` (their Theorem 2.1,
`QCert.BianSelingerUn.presentation`) by the Reidemeister–Schreier
theorem (`QCert.reidemeister_schreier`, Theorem 4.3 of their earlier
paper arXiv:2204.02217), with the translation `f` of `Translation.lean`.

The coset data and the verification of the two hypotheses of the
Reidemeister–Schreier theorem are not given in the paper; the authors'
code obtains them through "a sequence of multiple applications of the
Reidemeister–Schreier theorem passing through a number of intermediate
representations", whose relations reach "more than 50,000 generators".
Here they are the structure `RSData`, and its existence (`rsData`) is
the one remaining `sorry`; everything else of the argument is proved:
given any such data, the relations of Figure 2 are complete
(`complete_of_rsData`).
-/
import QCert.CliffordCS3.Soundness
import QCert.CliffordCS3.Translation
import QCert.CliffordT2.ReidemeisterSchreier
import QCert.BianSelingerUn.Theorem

namespace QCert.CliffordCS3

open Matrix

/-- Coset data satisfying the hypotheses (a) and (b) of the
Reidemeister–Schreier theorem for the translation `f`. -/
structure RSData where
  /-- The cosets. -/
  C : Type
  /-- The distinguished coset. -/
  I : C
  /-- The coset action. -/
  h : C → BianSelingerUn.Gen 8 → Word Gen × C
  /-- Hypothesis (a). -/
  ha : ∀ x : Gen, (hstar h I (fG x)).2 = I ∧
    Derivable Rel (hstar h I (fG x)).1 (FreeMonoid.of x)
  /-- Hypothesis (b). -/
  hb : ∀ (c : C) (w w' : Word (BianSelingerUn.Gen 8)), BianSelingerUn.Rel 8 w w' →
    (hstar h c w).2 = (hstar h c w').2 ∧ Derivable Rel (hstar h c w).1 (hstar h c w').1

/-- The Reidemeister–Schreier data of the authors' proof (their Agda
Steps 1–8, not reproduced here). -/
theorem rsData : Nonempty RSData := by
  sorry

theorem coe_lift_semU (w : Word Gen) :
    ((FreeMonoid.lift semU w : U_ZHalfI 8) : unitaryGroup (Fin 8) ℂ) = FreeMonoid.lift sem w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih => rw [map_mul, map_mul, Subgroup.coe_mul, ih, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of]; rfl

/-- Completeness of the translation: `f*(w) ∼ f*(v)` in the theory of
`U₈(ℤ[1/2, i])` implies `w ∼ v` in the theory of Figure 2. -/
theorem completeness_translation (D : RSData) {w v : Word Gen}
    (h : Derivable (BianSelingerUn.Rel 8) (FreeMonoid.lift fG w) (FreeMonoid.lift fG v)) :
    Derivable Rel w v :=
  reidemeister_schreier D.h D.I fG D.ha D.hb h

/-- Completeness of Figure 2 from the presentation of `U₈(ℤ[1/2, i])` and
coset data. -/
theorem complete_of_rsData
    (P : IsPresentationOf (BianSelingerUn.Rel 8) (BianSelingerUn.sem 8)) (D : RSData) :
    ∀ ⦃w v : Word Gen⦄,
    FreeMonoid.lift sem w = FreeMonoid.lift sem v → Derivable Rel w v := by
  intro w v h
  have hU : FreeMonoid.lift semU w = FreeMonoid.lift semU v := by
    apply Subtype.ext; rw [coe_lift_semU, coe_lift_semU, h]
  have hG : FreeMonoid.lift (BianSelingerUn.sem 8) (FreeMonoid.lift fG w) =
      FreeMonoid.lift (BianSelingerUn.sem 8) (FreeMonoid.lift fG v) := by
    rw [lift_lift_f, lift_lift_f, hU]
  exact completeness_translation D (P.complete hG)

/-- Completeness of the relations of Figure 2 for `U(8)`. -/
theorem complete : ∀ ⦃w v : Word Gen⦄,
    FreeMonoid.lift sem w = FreeMonoid.lift sem v → Derivable Rel w v :=
  complete_of_rsData (BianSelingerUn.presentation 8) (Classical.choice rsData)

end QCert.CliffordCS3
