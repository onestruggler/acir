/-
# Presentations of groups and monoids

Translation of `Presentation/Definitions.agda`.

The Agda's `_===_ IsPresentationOf G` is a record: `gl : Grouplike _===_`,
an interpretation `⟦_⟧ : Word X → G` and a proof that it is a group
isomorphism from the words modulo the congruence (`GL.•-ε-group`) to `G`;
`IsSubPresentationOf` asks for a monomorphism, and the monoid versions for
monoid isomorphisms and monomorphisms from `PP.•-ε-monoid`.

Here the target is a Mathlib group (or monoid) and the interpretation is
given on generators, `sem : X → G`, read on words as the monoid
homomorphism `FreeMonoid.lift sem` (every homomorphism from the words is of
this form).  A homomorphism from the word group is then automatic, and the
records ask for what remains:

* `IsSubMonoidPresentationOf Γ sem`: soundness (the axioms hold in `M`, so
  `⟦_⟧` is well defined on the quotient, the Agda's `⟦⟧-cong`) and
  completeness (words with equal values are derivably equal: injectivity);
* `IsMonoidPresentationOf Γ sem`: in addition surjectivity;
* `IsSubPresentationOf Γ sem`: a sub-monoid presentation into a group that
  is group-like;
* `IsPresentationOf Γ sem`: in addition surjectivity.

The isomorphisms themselves are `quotientEquiv` (the quotient monoid
`(conGen Γ).Quotient` is isomorphic to `G`, resp. to the subgroup the
generators generate).  The Agda's upgrades `isPresentationOf`,
`isMonoidPresentationOf`, `monoidPresentation⇒presentation` and
`subMonoidPresentation⇒subPresentation` are theorems of the same names.

**Setoid-valued targets.**  The Agda's groups are setoids; a development
whose group equality is not `=` (scaled matrices up to a power of a unit,
operators compared pointwise) states its presentation into the quotient of
its carrier by that equality, or into a Mathlib group in which the
equality is `=`.
-/
import EquaCert.Presentation.GroupLike
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Submonoid.Membership

namespace EquaCert

universe u v

variable {X : Type u}

/-- Soundness of the axioms gives soundness of every derivation (the Agda's
`⟦⟧-cong` of an interpretation built from a sound one on axioms). -/
theorem derivable_sound {Γ : WRel X} {M : Type v} [Monoid M] {sem : X → M}
    (h : ∀ ⦃w w' : Word X⦄, Γ w w' → FreeMonoid.lift sem w = FreeMonoid.lift sem w')
    {w w' : Word X} (d : Derivable Γ w w') :
    FreeMonoid.lift sem w = FreeMonoid.lift sem w' := by
  have : conGen Γ ≤ Con.ker (FreeMonoid.lift sem) :=
    Con.conGen_le fun x y hxy => (Con.ker_rel _).2 (h hxy)
  exact (Con.ker_rel _).1 (this d)

/-- `Γ` presents a submonoid of `M`: sound and complete (the Agda's
`_IsSubMonoidPresentationOf_`). -/
structure IsSubMonoidPresentationOf (Γ : WRel X) {M : Type v} [Monoid M] (sem : X → M) :
    Prop where
  sound : ∀ ⦃w w' : Word X⦄, Γ w w' → FreeMonoid.lift sem w = FreeMonoid.lift sem w'
  complete : ∀ ⦃w w' : Word X⦄,
    FreeMonoid.lift sem w = FreeMonoid.lift sem w' → Derivable Γ w w'

/-- `Γ` presents the monoid `M` (the Agda's `_IsMonoidPresentationOf_`). -/
structure IsMonoidPresentationOf (Γ : WRel X) {M : Type v} [Monoid M] (sem : X → M) :
    Prop extends IsSubMonoidPresentationOf Γ sem where
  surjective : Function.Surjective (FreeMonoid.lift sem)

/-- `Γ` presents the subgroup of `G` the generators generate (the Agda's
`_IsSubPresentationOf_`): group-like, sound and complete. -/
structure IsSubPresentationOf (Γ : WRel X) {G : Type v} [Group G] (sem : X → G) :
    Prop where
  grouplike : Grouplike Γ
  sound : ∀ ⦃w w' : Word X⦄, Γ w w' → FreeMonoid.lift sem w = FreeMonoid.lift sem w'
  complete : ∀ ⦃w w' : Word X⦄,
    FreeMonoid.lift sem w = FreeMonoid.lift sem w' → Derivable Γ w w'

/-- `Γ` presents the group `G` (the Agda's `_IsPresentationOf_`). -/
structure IsPresentationOf (Γ : WRel X) {G : Type v} [Group G] (sem : X → G) : Prop
    extends IsSubPresentationOf Γ sem where
  surjective : Function.Surjective (FreeMonoid.lift sem)

namespace IsSubMonoidPresentationOf

variable {Γ : WRel X} {M : Type v} [Monoid M] {sem : X → M}

/-- Two words are derivably equal exactly when they have the same value. -/
theorem derivable_iff (P : IsSubMonoidPresentationOf Γ sem) {w w' : Word X} :
    Derivable Γ w w' ↔ FreeMonoid.lift sem w = FreeMonoid.lift sem w' :=
  ⟨derivable_sound P.sound, fun h => P.complete h⟩

/-- The congruence of the theory is the kernel of the semantics. -/
theorem conGen_eq_ker (P : IsSubMonoidPresentationOf Γ sem) :
    conGen Γ = Con.ker (FreeMonoid.lift sem) := by
  ext w w'
  exact (P.derivable_iff).trans (Con.ker_rel _).symm

/-- The quotient monoid is isomorphic to the values of words. -/
noncomputable def quotientEquiv (P : IsSubMonoidPresentationOf Γ sem) :
    (conGen Γ).Quotient ≃* MonoidHom.mrange (FreeMonoid.lift sem) :=
  (Con.congr P.conGen_eq_ker).trans (Con.quotientKerEquivRange (FreeMonoid.lift sem))

end IsSubMonoidPresentationOf

/-- The Agda's `isMonoidPresentationOf`: a surjective sub-monoid
presentation is a monoid presentation. -/
theorem isMonoidPresentationOf {Γ : WRel X} {M : Type v} [Monoid M] {sem : X → M}
    (P : IsSubMonoidPresentationOf Γ sem) (s : Function.Surjective (FreeMonoid.lift sem)) :
    IsMonoidPresentationOf Γ sem := ⟨P, s⟩

namespace IsMonoidPresentationOf

variable {Γ : WRel X} {M : Type v} [Monoid M] {sem : X → M}

/-- `Γ` presents `M`: the quotient monoid is isomorphic to `M`. -/
noncomputable def quotientEquiv (P : IsMonoidPresentationOf Γ sem) :
    (conGen Γ).Quotient ≃* M :=
  (Con.congr P.conGen_eq_ker).trans
    (Con.quotientKerEquivOfSurjective (FreeMonoid.lift sem) P.surjective)

end IsMonoidPresentationOf

namespace IsSubPresentationOf

variable {Γ : WRel X} {G : Type v} [Group G] {sem : X → G}

theorem toSubMonoid (P : IsSubPresentationOf Γ sem) : IsSubMonoidPresentationOf Γ sem :=
  ⟨P.sound, P.complete⟩

/-- Two words are derivably equal exactly when they have the same value. -/
theorem derivable_iff (P : IsSubPresentationOf Γ sem) {w w' : Word X} :
    Derivable Γ w w' ↔ FreeMonoid.lift sem w = FreeMonoid.lift sem w' :=
  P.toSubMonoid.derivable_iff

/-- The congruence of the theory is the kernel of the semantics. -/
theorem conGen_eq_ker (P : IsSubPresentationOf Γ sem) :
    conGen Γ = Con.ker (FreeMonoid.lift sem) := P.toSubMonoid.conGen_eq_ker

/-- The values of words form the subgroup generated by the generators. -/
theorem mrange_eq_closure (P : IsSubPresentationOf Γ sem) :
    MonoidHom.mrange (FreeMonoid.lift sem) =
      (Subgroup.closure (Set.range sem)).toSubmonoid := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    induction w using FreeMonoid.inductionOn' with
    | one => exact (Subgroup.closure (Set.range sem)).one_mem
    | mul_of x w ih =>
      rw [map_mul, FreeMonoid.lift_eval_of]
      exact (Subgroup.closure _).mul_mem (Subgroup.subset_closure ⟨x, rfl⟩) ih
  · intro g hg
    let H : Subgroup G :=
      { MonoidHom.mrange (FreeMonoid.lift sem) with
        inv_mem' := by
          rintro _ ⟨w, rfl⟩
          induction w using FreeMonoid.inductionOn' with
          | one => exact ⟨1, by simp⟩
          | mul_of x w ih =>
            obtain ⟨u, hu⟩ := ih
            obtain ⟨wx, hwx⟩ := P.grouplike x
            have hx : FreeMonoid.lift sem wx * sem x = 1 := by
              simpa using derivable_sound P.sound hwx
            refine ⟨u * wx, ?_⟩
            rw [map_mul, hu, map_mul, FreeMonoid.lift_eval_of, mul_inv_rev,
              eq_inv_of_mul_eq_one_left hx] }
    have : Subgroup.closure (Set.range sem) ≤ H :=
      (Subgroup.closure_le H).2 (by rintro _ ⟨x, rfl⟩; exact ⟨FreeMonoid.of x, by simp⟩)
    exact this hg

/-- `Γ` presents the subgroup generated by the generators: the quotient
monoid is isomorphic to it. -/
noncomputable def quotientEquiv (P : IsSubPresentationOf Γ sem) :
    (conGen Γ).Quotient ≃* Subgroup.closure (Set.range sem) :=
  (Con.congr P.conGen_eq_ker).trans
    ((Con.quotientKerEquivRange (FreeMonoid.lift sem)).trans
      (MulEquiv.submonoidCongr P.mrange_eq_closure))

end IsSubPresentationOf

/-- The Agda's `isPresentationOf`: a surjective sub-presentation is a
presentation. -/
theorem isPresentationOf {Γ : WRel X} {G : Type v} [Group G] {sem : X → G}
    (P : IsSubPresentationOf Γ sem) (s : Function.Surjective (FreeMonoid.lift sem)) :
    IsPresentationOf Γ sem := ⟨P, s⟩

/-- The Agda's `monoidPresentation⇒presentation`. -/
theorem monoidPresentation_to_presentation {Γ : WRel X} {G : Type v} [Group G] {sem : X → G}
    (mp : IsMonoidPresentationOf Γ sem) (gl : Grouplike Γ) : IsPresentationOf Γ sem :=
  ⟨⟨gl, mp.sound, mp.complete⟩, mp.surjective⟩

/-- The Agda's `subMonoidPresentation⇒subPresentation`. -/
theorem subMonoidPresentation_to_subPresentation {Γ : WRel X} {G : Type v} [Group G]
    {sem : X → G} (smp : IsSubMonoidPresentationOf Γ sem) (gl : Grouplike Γ) :
    IsSubPresentationOf Γ sem :=
  ⟨gl, smp.sound, smp.complete⟩

namespace IsPresentationOf

variable {Γ : WRel X} {G : Type v} [Group G] {sem : X → G}

/-- `Γ` presents `G`: the quotient monoid is isomorphic to `G`. -/
noncomputable def quotientEquiv (P : IsPresentationOf Γ sem) : (conGen Γ).Quotient ≃* G :=
  (Con.congr P.conGen_eq_ker).trans
    (Con.quotientKerEquivOfSurjective (FreeMonoid.lift sem) P.surjective)

/-- A sub-presentation whose generators generate the whole group is a
presentation. -/
theorem of_closure (P : IsSubPresentationOf Γ sem)
    (h : Subgroup.closure (Set.range sem) = ⊤) : IsPresentationOf Γ sem where
  toIsSubPresentationOf := P
  surjective g := by
    have : g ∈ MonoidHom.mrange (FreeMonoid.lift sem) := by
      rw [P.mrange_eq_closure, Subgroup.mem_toSubmonoid, h]; trivial
    exact this

end IsPresentationOf

end EquaCert
