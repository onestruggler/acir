/-
# Group-like presentations

Translation of `Presentation/GroupLike.agda`.

A presentation is *group-like* when every generator has a left inverse
modulo the congruence.  `GroupLemmas` (the Agda's module
`Group-Lemmas Γ group-like`) has the syntactic inverse `inv` (the Agda's
`_⁻¹`: generators inverted by the chosen left inverses, products reversed),
the inverse laws, cancellation, uniqueness of inverses, and the group of
words modulo the congruence (`wordGroup`, the Agda's `•-ε-group`), a group
structure on Mathlib's quotient monoid `(conGen Γ).Quotient`.
`by_basis_change` and `bbc` are the Agda's `Basis-Change`.

**Deviation.**  The Agda's `Grouplike` is a Σ-type, so its `_⁻¹` computes;
here `Grouplike` is a proposition and `inv` is noncomputable (chosen by
`Classical.choose`).  A development that computes with inverse words
defines them itself.
-/
import EquaCert.Presentation.Base
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace EquaCert

universe u

open Word

variable {X : Type u}

/-- Every generator has a left inverse modulo the theory (the Agda's
`Grouplike`). -/
def Grouplike (Γ : WRel X) : Prop :=
  ∀ x : X, ∃ w : Word X, Derivable Γ (w * [x]ʷ) 1

namespace GroupLemmas

variable {Γ : WRel X} (gl : Grouplike Γ)

/-- The chosen left inverse of a generator. -/
noncomputable def invGen (x : X) : Word X := Classical.choose (gl x)

theorem invGen_spec (x : X) : Derivable Γ (invGen gl x * [x]ʷ) 1 :=
  Classical.choose_spec (gl x)

/-- The syntactic inverse (the Agda's `_⁻¹`): reverse the word and invert
each generator. -/
noncomputable def inv (w : Word X) : Word X :=
  (w.toList.reverse.map (invGen gl)).prod

@[simp] theorem inv_one : inv gl (1 : Word X) = 1 := rfl

@[simp] theorem inv_of (x : X) : inv gl [x]ʷ = invGen gl x := by
  simp [inv]

@[simp] theorem inv_mul (w v : Word X) : inv gl (w * v) = inv gl v * inv gl w := by
  simp [inv, FreeMonoid.toList_mul, List.reverse_append, List.map_append, List.prod_append]

variable {gl}

/-- The Agda's `inverseˡ`. -/
theorem inverse_l (g : Word X) : Derivable Γ (inv gl g * g) 1 := by
  induction g using FreeMonoid.inductionOn' with
  | one => exact Derivable.refl _
  | mul_of x w ih =>
    rw [inv_mul, inv_of]
    -- (inv w * invGen x) * (x * w) = inv w * (invGen x * x) * w
    have e : inv gl w * invGen gl x * ([x]ʷ * w) = inv gl w * (invGen gl x * [x]ʷ) * w := by
      simp [mul_assoc]
    rw [e]
    refine Derivable.trans (Derivable.cleft (Derivable.cright (invGen_spec gl x))) ?_
    simpa using ih

/-- The Agda's `inverseʳ`. -/
theorem inverse_r (g : Word X) : Derivable Γ (g * inv gl g) 1 := by
  -- g * g⁻¹ = (g⁻¹⁻¹ * g⁻¹) * (g * g⁻¹) = g⁻¹⁻¹ * (g⁻¹ * g) * g⁻¹ = g⁻¹⁻¹ * g⁻¹ = 1
  have h1 : Derivable Γ (g * inv gl g) (inv gl (inv gl g) * inv gl g * (g * inv gl g)) :=
    Derivable.sym (Derivable.trans (Derivable.cleft (inverse_l (inv gl g)))
      (by rw [one_mul]))
  have h2 : Derivable Γ (inv gl (inv gl g) * inv gl g * (g * inv gl g))
      (inv gl (inv gl g) * inv gl g) := by
    have : inv gl (inv gl g) * inv gl g * (g * inv gl g) =
        inv gl (inv gl g) * (inv gl g * g) * inv gl g := by simp [mul_assoc]
    rw [this]
    refine Derivable.trans (Derivable.cleft (Derivable.cright (inverse_l g))) ?_
    simpa using Derivable.refl _
  exact h1.trans (h2.trans (inverse_l _))

/-- The Agda's `•-cancelˡ`. -/
theorem cancel_l (gl : Grouplike Γ) {g h h' : Word X} (p : Derivable Γ (g * h) (g * h')) : Derivable Γ h h' := by
  have a : Derivable Γ h (inv gl g * (g * h)) := by
    have := Derivable.cleft (u := h) (inverse_l (gl := gl) g)
    simpa [mul_assoc] using this.sym
  have b : Derivable Γ (inv gl g * (g * h')) h' := by
    have := Derivable.cleft (u := h') (inverse_l (gl := gl) g)
    simpa [mul_assoc] using this
  exact a.trans ((Derivable.cright p).trans b)

/-- The Agda's `•-cancelʳ`. -/
theorem cancel_r (gl : Grouplike Γ) {g g' h : Word X} (p : Derivable Γ (g * h) (g' * h)) : Derivable Γ g g' := by
  have a : Derivable Γ g (g * h * inv gl h) := by
    have := Derivable.cright (u := g) (inverse_r (gl := gl) h)
    simpa [mul_assoc] using this.sym
  have b : Derivable Γ (g' * h * inv gl h) g' := by
    have := Derivable.cright (u := g') (inverse_r (gl := gl) h)
    simpa [mul_assoc] using this
  exact a.trans ((Derivable.cleft p).trans b)

/-- The Agda's `inverseˡ-unique`. -/
theorem inverse_l_unique {g h : Word X} (p : Derivable Γ (h * g) 1) :
    Derivable Γ h (inv gl g) :=
  cancel_r gl (h := g) (p.trans (inverse_l g).sym)

/-- The Agda's `inverseʳ-unique`. -/
theorem inverse_r_unique {g h : Word X} (p : Derivable Γ (g * h) 1) :
    Derivable Γ h (inv gl g) :=
  cancel_l gl (g := g) (p.trans (inverse_r g).sym)

/-- The Agda's `⁻¹-cong`. -/
theorem inv_cong {g h : Word X} (p : Derivable Γ g h) : Derivable Γ (inv gl g) (inv gl h) :=
  inverse_r_unique ((Derivable.cleft p.sym).trans (inverse_r g))

/-- The Agda's `⁻¹-involutive`. -/
theorem inv_involutive (g : Word X) : Derivable Γ (inv gl (inv gl g)) g :=
  (inverse_r_unique (inverse_l g)).sym

/-- The Agda's `⁻¹-injective`. -/
theorem inv_injective {u v : Word X} (hyp : Derivable Γ (inv gl u) (inv gl v)) :
    Derivable Γ u v :=
  (inv_involutive u).sym.trans ((inv_cong hyp).trans (inv_involutive v))

/-- The Agda's `comm-⁻¹`. -/
theorem comm_inv {v v' w w' : Word X} (hyp : Derivable Γ (v * w) (w' * v')) :
    Derivable Γ (v' * inv gl w) (inv gl w' * v) := by
  -- v' w⁻¹ = w'⁻¹ (w' v') w⁻¹ = w'⁻¹ (v w) w⁻¹ = w'⁻¹ v
  have a : Derivable Γ (v' * inv gl w) (inv gl w' * (w' * v') * inv gl w) := by
    have := Derivable.cleft (u := v' * inv gl w) (inverse_l (gl := gl) w')
    simpa [mul_assoc] using this.sym
  have b : Derivable Γ (inv gl w' * (v * w) * inv gl w) (inv gl w' * v) := by
    have := Derivable.cright (u := inv gl w' * v) (inverse_r (gl := gl) w)
    simpa [mul_assoc] using this
  exact a.trans ((Derivable.cleft (Derivable.cright hyp.sym)).trans b)

/-- The Agda's `one-sided`. -/
theorem one_sided {w u : Word X} (hyp : Derivable Γ (w * inv gl u) 1) : Derivable Γ w u := by
  have a : Derivable Γ w (w * inv gl u * u) := by
    have := Derivable.cright (u := w) (inverse_l (gl := gl) u)
    simpa [mul_assoc] using this.sym
  exact a.trans ((Derivable.cleft hyp).trans (by simpa using Derivable.refl u))

variable (gl)

/-- The group of words modulo the congruence (the Agda's `•-ε-group`): a
group structure on the quotient monoid. -/
noncomputable abbrev wordGroup : Group (conGen Γ).Quotient :=
  { (conGen Γ).monoid with
    inv := Quotient.map' (inv gl) fun _ _ h => inv_cong h
    inv_mul_cancel := by
      rintro ⟨w⟩
      exact Quotient.sound (inverse_l w) }

end GroupLemmas

/-! ## Basis change -/

section BasisChange

variable {Γ : WRel X}

/-- The Agda's `by-basis-change`: cancel a common context `b • _ • c` with
given inverses `d`, `e`. -/
theorem by_basis_change {u v : Word X} (b c d e : Word X)
    (h1 : Derivable Γ (d * b) 1) (h2 : Derivable Γ (c * e) 1)
    (eq : Derivable Γ (b * u * c) (b * v * c)) : Derivable Γ u v := by
  have a : Derivable Γ u (d * b * u * (c * e)) := by
    have := Derivable.cong (Derivable.cleft (u := u) h1) h2
    simpa [mul_assoc] using this.sym
  have b' : Derivable Γ (d * b * v * (c * e)) v := by
    have := Derivable.cong (Derivable.cleft (u := v) h1) h2
    simpa [mul_assoc] using this
  have m : Derivable Γ (d * b * u * (c * e)) (d * b * v * (c * e)) := by
    have := Derivable.cleft (u := e) (Derivable.cright (u := d) eq)
    simpa [mul_assoc] using this
  exact a.trans (m.trans b')

/-- The Agda's `bbc`: cancel a common context, using the inverses of a
group-like presentation. -/
theorem bbc (gl : Grouplike Γ) {u v : Word X} (b c : Word X)
    (eq : Derivable Γ (b * u * c) (b * v * c)) : Derivable Γ u v :=
  by_basis_change b c (GroupLemmas.inv gl b) (GroupLemmas.inv gl c)
    (GroupLemmas.inverse_l b) (GroupLemmas.inverse_r c) eq

end BasisChange

end EquaCert
