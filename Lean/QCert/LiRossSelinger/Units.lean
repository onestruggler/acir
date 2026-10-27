/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Grouplike theories from units of the quotient monoid

A theory is grouplike when every generator is a unit of the monoid of words
modulo the theory (`grouplike_of_isUnit`); units are closed under
products, so a generator equal in the theory to a product of units is one.
-/
import QCert.Presentation

namespace QCert

variable {X : Type*} {Γ : WRel X}

/-- The class of a word in the monoid of words modulo `Γ`. -/
abbrev cls (Γ : WRel X) (u : Word X) : (conGen Γ).Quotient := (conGen Γ).mk' u

theorem cls_mul (u v : Word X) : cls Γ (u * v) = cls Γ u * cls Γ v := map_mul _ u v

theorem cls_one : cls Γ 1 = 1 := map_one _

theorem cls_eq_iff {u v : Word X} : cls Γ u = cls Γ v ↔ Derivable Γ u v := (conGen Γ).eq

/-- If every generator is a unit modulo `Γ`, then `Γ` is grouplike. -/
theorem grouplike_of_isUnit (h : ∀ x, IsUnit (cls Γ (FreeMonoid.of x))) : Grouplike Γ := by
  intro x
  obtain ⟨u, hu⟩ := h x
  obtain ⟨v, hv⟩ := Con.mk'_surjective (c := conGen Γ) (↑u⁻¹ : (conGen Γ).Quotient)
  refine ⟨v, cls_eq_iff.1 ?_⟩
  show (conGen Γ).mk' (v * FreeMonoid.of x) = (conGen Γ).mk' 1
  have hu' : (conGen Γ).mk' (FreeMonoid.of x) = ↑u := hu.symm
  rw [map_mul, hv, hu', Units.inv_mul, map_one]

/-- A generator that is its own inverse modulo `Γ` is a unit. -/
theorem isUnit_of_sq {x : X} (h : Derivable Γ (FreeMonoid.of x * FreeMonoid.of x) 1) :
    IsUnit (cls Γ (FreeMonoid.of x)) := by
  have e : cls Γ (FreeMonoid.of x) * cls Γ (FreeMonoid.of x) = 1 := by
    show (conGen Γ).mk' _ * (conGen Γ).mk' _ = 1
    rw [← map_mul]; exact (cls_eq_iff.2 h).trans (map_one _)
  exact ⟨⟨_, _, e, e⟩, rfl⟩

/-- A generator equal modulo `Γ` to a product of units is a unit. -/
theorem isUnit_of_derivable {x : X} {l : List X}
    (h : Derivable Γ (FreeMonoid.of x) (FreeMonoid.ofList l))
    (hl : ∀ y ∈ l, IsUnit (cls Γ (FreeMonoid.of y))) : IsUnit (cls Γ (FreeMonoid.of x)) := by
  rw [cls_eq_iff.2 h]
  clear h
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [FreeMonoid.ofList_cons]
    show IsUnit ((conGen Γ).mk' _)
    rw [map_mul]
    exact (hl y (by simp)).mul (ih fun z hz => hl z (by simp [hz]))

/-- A translation of words that sends axioms to derivable equations sends
derivable equations to derivable equations. -/
theorem derivable_map {Y : Type*} {Δ : WRel Y} (f : Word X →* Word Y)
    (hf : ∀ ⦃u v⦄, Γ u v → Derivable Δ (f u) (f v)) {u v : Word X} (h : Derivable Γ u v) :
    Derivable Δ (f u) (f v) := by
  have : conGen Γ ≤ (conGen Δ).comap f (map_mul f) :=
    Con.conGen_le fun a b hab => hf hab
  exact this h

end QCert
