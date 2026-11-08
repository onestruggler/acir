/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: the four presentations in `U(8)`

Counterpart of `DOmega.agda`.  The Agda reads both groups in `U₈(𝔻[ω])`,
the uniform semantics of its Clifford+T family, through ring embeddings.
Here `O(8, 𝔻)` and `TofH(3) = L₈` are both subgroups of the real unitary
group `U(8)` already (`Semantics`), so the embedding is the inclusion of a
subgroup: `R₁⁺` and `R₂⁺`, over the paper's alphabet and as circuits on
three wires, are sub-presentations of `U(8)`.  Two words, or two circuits,
are then derivably equal exactly when their matrices are equal
(`QCert.IsSubPresentationOf.derivable_iff`).
-/
import QCert.ToffoliHadamardRS.Circuits.Presentation

namespace QCert.ToffoliHadamardRS

open QCert

/-- The unitary group the matrices are read in. -/
abbrev U8 := Matrix.unitaryGroup (Fin 8) ℝ

section Along

universe u₁ u₂

variable {X : Type u₁} {Γ : WRel X} {G : Type u₂} [Group G]

/-- A presentation of a subgroup is a sub-presentation of the group. -/
theorem along_subgroup {H : Subgroup G} {sem : X → H} (P : IsPresentationOf Γ sem) :
    IsSubPresentationOf Γ (fun x => (sem x : G)) := by
  have hlift : ∀ w : Word X, FreeMonoid.lift (fun x => (sem x : G)) w = (FreeMonoid.lift sem w : G) := by
    intro w
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | mul_of x w ih => rw [map_mul, map_mul, Subgroup.coe_mul, ih, FreeMonoid.lift_eval_of,
        FreeMonoid.lift_eval_of]
  refine ⟨P.grouplike, fun w v h => ?_, fun w v h => P.complete (Subtype.ext ?_)⟩
  · rw [hlift, hlift, P.sound h]
  · rwa [hlift, hlift] at h

end Along

/-- `R₁⁺` is a sub-presentation of `U(8)`. -/
theorem presentation₁ : IsSubPresentationOf R1plus (fun g => (sem1 g : U8)) :=
  along_subgroup presentation

/-- `R₂⁺` is a sub-presentation of `U(8)`. -/
theorem presentation₂ : IsSubPresentationOf R2plus (fun g => (sem2 g : U8)) :=
  along_subgroup presentationH

/-- Circuits over `Σ₁` modulo `R₁⁺` are a sub-presentation of `U(8)`. -/
theorem circuit_presentation₁ :
    IsSubPresentationOf (QCert.Lift Circuits.SRel1 3) (fun x => (Circuits.sem1 x : U8)) :=
  along_subgroup Circuits.theorem_5_2

/-- Circuits over `Σ₂` modulo `R₂⁺` are a sub-presentation of `U(8)`. -/
theorem circuit_presentation₂ :
    IsSubPresentationOf (QCert.Lift Circuits.SRel2 3) (fun x => (Circuits.sem2 x : U8)) :=
  along_subgroup Circuits.theorem_6_3

end QCert.ToffoliHadamardRS
