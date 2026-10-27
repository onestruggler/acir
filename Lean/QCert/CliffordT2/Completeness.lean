/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Two-qubit Clifford+T: completeness

Section 5.1 of Bian–Selinger (arXiv:2204.02217): words with the same
value are derivably equal under the relations of Figure 1.  As in the
paper, `⟦w⟧ = ⟦v⟧` gives `⟦f*(w)⟧ = ⟦f*(v)⟧` since `f` respects the
interpretation (`lift_lift_f`), hence `f*(w) ∼ f*(v)` by Greylyn's
Theorem 4.1 (`QCert.Greylyn.presentation`), hence the same in the
five-generator form (`Simplified.derivable_simple`), hence `w ∼ v` by
the Reidemeister–Schreier theorem (Theorem 4.3, Theorem 5.2) with the
coset data of `Cosets.lean` and the equations of `Equations.lean`.
-/
import QCert.CliffordT2.Equations
import QCert.Greylyn.Theorem

namespace QCert.CliffordT2

open Matrix

theorem coe_lift_semU (w : Word Gen) :
    ((FreeMonoid.lift semU w : U_ZInvSqrt2I 4) : unitaryGroup (Fin 4) ℂ) =
      FreeMonoid.lift sem w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih => rw [map_mul, map_mul, Subgroup.coe_mul, ih, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of]; rfl

/-- **Theorem 5.2** (completeness of the translation): `f*(w) ∼ f*(v)`
in Greylyn's theory implies `w ∼ v` in the theory of Figure 1. -/
theorem completeness_translation {w v : Word Gen}
    (h : Derivable (Greylyn.Rel 4) (FreeMonoid.lift fG w) (FreeMonoid.lift fG v)) :
    Derivable Rel w v := by
  have hs := Simplified.derivable_simple h
  rw [lift_simple_lift_fG, lift_simple_lift_fG] at hs
  exact reidemeister_schreier hT .I f' hypA hypB hs

/-- Completeness of the relations of Figure 1 for `U(4)`. -/
theorem complete : ∀ ⦃w v : Word Gen⦄,
    FreeMonoid.lift sem w = FreeMonoid.lift sem v → Derivable Rel w v := by
  intro w v h
  have hU : FreeMonoid.lift semU w = FreeMonoid.lift semU v := by
    apply Subtype.ext; rw [coe_lift_semU, coe_lift_semU, h]
  have hG : FreeMonoid.lift (Greylyn.sem 4) (FreeMonoid.lift fG w) =
      FreeMonoid.lift (Greylyn.sem 4) (FreeMonoid.lift fG v) := by
    rw [lift_lift_f, lift_lift_f, hU]
  exact completeness_translation ((Greylyn.presentation 4 le_rfl).complete hG)

end QCert.CliffordT2
