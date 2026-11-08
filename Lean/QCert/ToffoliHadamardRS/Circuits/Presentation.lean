/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: Theorems 5.2 and 6.3 for circuits

Translation of `Circuits/Presentation.agda`.  On three wires the circuits
of `Circuits.Syntactics` over `Σ₁` present `O(8, 𝔻)`, and those over `Σ₂`
present `TofH(3) = L₈`.

A circuit denotes the value of its reading in the paper's alphabet
(`Circuits.Iso1.ι`, `Circuits.Iso2.ι`).  The Agda composes two group
isomorphisms, the reading (`circuits≅paper`) and the paper's semantics
(`PresentationO8`, `PresentationH`).  The framework's `IsPresentationOf`
states soundness, completeness and surjectivity of a generator-level
semantics instead, so here one lemma (`transfer`) carries a presentation
along two translations that respect the relations and are inverse up to
them, which is what `circuits≅paper` is built from.
-/
import QCert.ToffoliHadamardRS.Circuits.Iso1
import QCert.ToffoliHadamardRS.Circuits.Iso2

namespace QCert.ToffoliHadamardRS.Circuits

open QCert

/-! ## Carrying a presentation along translations -/

section Transfer

universe u₁ u₂ u₃

variable {X : Type u₁} {Y : Type u₂} {Γ : WRel X} {Δ : WRel Y}

/-- In a grouplike theory every word has a left inverse. -/
theorem word_inverse (hg : Grouplike Δ) (u : Word Y) : ∃ w, Derivable Δ (w * u) 1 := by
  induction u using FreeMonoid.inductionOn' with
  | one => exact ⟨1, by rw [mul_one]⟩
  | mul_of y u ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨w', hw'⟩ := hg y
    refine ⟨w * w', ?_⟩
    have e : w * w' * (FreeMonoid.of y * u) = w * (w' * FreeMonoid.of y) * u := by
      simp only [mul_assoc]
    rw [e]
    have := ((Derivable.refl w).mul hw').mul (Derivable.refl u)
    rw [mul_one] at this
    exact this.trans hw

/-- A word is its translation read back, when each generator is. -/
theorem round_trip {f : X → Word Y} {g : Word Y →* Word X}
    (h : ∀ x, Derivable Γ (FreeMonoid.of x) (g (f x))) (w : Word X) :
    Derivable Γ w (g (FreeMonoid.lift f w)) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one, map_one]
  | mul_of x w ih => rw [map_mul, map_mul, FreeMonoid.lift_eval_of]; exact (h x).mul ih

theorem lift_comp {G : Type u₃} [Monoid G] (sem : Y → G) (f : X → Word Y) (w : Word X) :
    FreeMonoid.lift (fun x => FreeMonoid.lift sem (f x)) w =
      FreeMonoid.lift sem (FreeMonoid.lift f w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih => rw [map_mul, map_mul, map_mul, ih, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of]

/-- A presentation by `Δ` gives one by `Γ`, along translations `ι`, `κ` that
respect the relations and are inverse to each other up to them. -/
theorem transfer {G : Type u₃} [Group G] {sem : Y → G} (P : IsPresentationOf Δ sem)
    (ι : X → Word Y) (κ : Y → Word X)
    (ι_ax : ∀ ⦃w v⦄, Γ w v → Derivable Δ (FreeMonoid.lift ι w) (FreeMonoid.lift ι v))
    (κ_ax : ∀ ⦃u t⦄, Δ u t → Derivable Γ (FreeMonoid.lift κ u) (FreeMonoid.lift κ t))
    (κι : ∀ x, Derivable Γ (FreeMonoid.of x) (FreeMonoid.lift κ (ι x)))
    (ικ : ∀ y, Derivable Δ (FreeMonoid.of y) (FreeMonoid.lift ι (κ y))) :
    IsPresentationOf Γ (fun x => FreeMonoid.lift sem (ι x)) where
  grouplike x := by
    obtain ⟨u, hu⟩ := word_inverse P.grouplike (ι x)
    have := derivable_map (FreeMonoid.lift κ) κ_ax hu
    rw [map_mul, map_one] at this
    exact ⟨FreeMonoid.lift κ u, ((Derivable.refl _).mul (κι x)).trans this⟩
  sound w v h := by
    rw [lift_comp, lift_comp]
    exact derivable_sound P.sound (ι_ax h)
  complete w v h := by
    rw [lift_comp, lift_comp] at h
    have := derivable_map (FreeMonoid.lift κ) κ_ax (P.complete h)
    exact ((round_trip κι w).trans this).trans (round_trip κι v).symm
  surjective a := by
    obtain ⟨u, hu⟩ := P.surjective a
    refine ⟨FreeMonoid.lift κ u, ?_⟩
    rw [lift_comp, ← hu]
    exact (derivable_sound P.sound (round_trip ικ u)).symm

end Transfer

/-! ## Theorem 5.2, with `r_K`: circuits over `Σ₁` present `O(8, 𝔻)` -/

/-- A circuit over `Σ₁` denotes the value of its reading. -/
noncomputable def sem1 (x : Gen (Gate 1) 3) : O8 := FreeMonoid.lift ToffoliHadamardRS.sem1 (CircuitsIso1.ι x)

theorem theorem_5_2 : IsPresentationOf (QCert.Lift SRel1 3) sem1 :=
  transfer presentation CircuitsIso1.ι CircuitsIso1.κ (fun _ _ h => CircuitsIso1.ι_ax h)
    (fun _ _ h => CircuitsIso1.κ_ax h) CircuitsIso1.κι CircuitsIso1.ικ

/-! ## Theorem 6.3, with `r_K`: circuits over `Σ₂` present `TofH(3)` -/

/-- A circuit over `Σ₂` denotes the value of its reading. -/
noncomputable def sem2 (x : Gen (Gate 2) 3) : TofH3 := FreeMonoid.lift ToffoliHadamardRS.sem2 (CircuitsIso2.ι x)

theorem theorem_6_3 : IsPresentationOf (QCert.Lift SRel2 3) sem2 :=
  transfer presentationH CircuitsIso2.ι CircuitsIso2.κ (fun _ _ h => CircuitsIso2.ι_ax h)
    (fun _ _ h => CircuitsIso2.κ_ax h) CircuitsIso2.κι CircuitsIso2.ικ

end QCert.ToffoliHadamardRS.Circuits
