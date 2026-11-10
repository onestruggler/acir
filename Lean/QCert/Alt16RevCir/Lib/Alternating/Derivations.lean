/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lafont's Fig. 11: the rules of Fig. 10 from Theorem 4's relations

Translation of `Examples/Groups/Alternating/Derivations.agda`.

The derivations are generic in the theory: any theory in which the three
relations of Theorem 4 hold has the seven rules, at every width
(`FromRelations`).  Theorem 4's own relations are one such theory (`fig10`).
`rule₃` and `rule₇` are relations of Theorem 4 themselves; the others are a
few steps each, every step replacing one factor of a word by an equal one.
Each derivation was found by a breadth-first search over the relations and
their shifts, and checked on permutations, before it was written in the
Agda.

**Deviations from the Agda.**  The Agda's `step` checks that the words
before and after are `pre • l • post` and `pre • r • post` up to
associativity by flattening them (`to-list`, two `Eq.refl`s); the
framework's words are lists already, so here the two checks are equalities
of words, proved by the monoid laws (the default of `step`'s last two
arguments: `rfl` between the lists made the elaborator time out).  The
Agda's module `FromRelations T r₁ r₂ r₃` is the namespace `FromRelations`,
each of whose lemmas takes those of `r₁`, `r₂`, `r₃` that it uses as
arguments; its chains of `≈⟨ ⟩` are `calc` chains of `Derives`.
-/
import QCert.Alt16RevCir.Lib.Alternating.Rules

namespace QCert.Alt16RevCir.Alternating

open QCert QCert.Circuit CircuitProp

/-! ## One rewriting step -/

/-- Rewrite the factor `l` of `pre * l * post` to `r`.  The words before and
after are `pre * l * post` and `pre * r * post` by the monoid laws. -/
theorem step {T : Theory} {m : ℕ} {w v : Circ m} (pre : Circ m) {l r : Circ m} (post : Circ m)
    (e : Derives T m l r)
    (hw : w = pre * l * post := by simp only [map_mul, map_one, mul_assoc, one_mul, mul_one])
    (hv : pre * r * post = v := by simp only [map_mul, map_one, mul_assoc, one_mul, mul_one]) :
    Derives T m w v := by
  subst hw hv
  exact ((Derivable.refl pre).mul e).mul (Derivable.refl post)

/-- Chains of derivations, for `calc`. -/
instance {T : Theory} {m : ℕ} : Trans (Derives T m) (Derives T m) (Derives T m) :=
  ⟨Derivable.trans⟩

/-! ## The rules from the relations -/

namespace FromRelations

variable {T : Theory}
  (r₁ : ∀ {n : ℕ}, Derives T (n + 3) (ω * ω * ω) 1)
  (r₂ : ∀ {n : ℕ}, Derives T (n + 4) (ω * shift ω * ω) (shift ω * shift ω))
  (r₃ : ∀ {n : ℕ}, Derives T (n + 5) (ω * shift (shift ω) * ω) (shift (shift ω) * ω * shift ω))

/-! The relations one and two wires up. -/

include r₁ in
private theorem r₁_up {n : ℕ} : Derives T (n + 4) (shift ω * shift ω * shift ω) 1 := by
  simpa only [map_mul, map_one] using lemma_cong_up (r₁ (n := n))

include r₁ in
private theorem r₁_upup {n : ℕ} :
    Derives T (n + 5) (shift (shift ω) * shift (shift ω) * shift (shift ω)) 1 := by
  simpa only [map_mul, map_one] using lemma_cong_up (r₁_up r₁ (n := n))

include r₂ in
private theorem r₂_up {n : ℕ} :
    Derives T (n + 5) (shift ω * shift (shift ω) * shift ω)
      (shift (shift ω) * shift (shift ω)) := by
  simpa only [map_mul] using lemma_cong_up (r₂ (n := n))

include r₁ r₂ in
theorem rule₄ {n : ℕ} : Derives T (n + 4) (ω * ω) (shift ω * ω * shift ω) :=
  calc Derives T (n + 4) (ω * ω) (shift ω * shift ω * shift ω * ω * ω) :=
        step 1 (ω * ω) (r₁_up r₁).symm
    Derives T (n + 4) _ (shift ω * ω * shift ω * ω * ω * ω) :=
        step (shift ω) (ω * ω) r₂.symm
    Derives T (n + 4) _ (shift ω * ω * shift ω) :=
        step (shift ω * ω * shift ω) 1 r₁

include r₁ r₂ in
theorem rule₆ {n : ℕ} :
    Derives T (n + 4) (ω * shift ω * shift ω * ω) (shift ω * shift ω * ω * shift ω * shift ω) :=
  calc Derives T (n + 4) (ω * shift ω * shift ω * ω)
          (ω * shift ω * ω * ω * ω * shift ω * ω) :=
        step (ω * shift ω) (shift ω * ω) r₁.symm
    Derives T (n + 4) _ (shift ω * shift ω * ω * ω * shift ω * ω) :=
        step 1 (ω * ω * shift ω * ω) r₂
    Derives T (n + 4) _ (shift ω * shift ω * ω * shift ω * shift ω) :=
        step (shift ω * shift ω * ω) 1 r₂

include r₁ r₂ r₃

theorem rule₁ {n : ℕ} : Derives T (n + 5) (ω * shift (shift ω))
    (shift (shift ω) * shift (shift ω) * shift ω * shift (shift ω) * ω) :=
  calc Derives T (n + 5) (ω * shift (shift ω)) (ω * shift (shift ω) * ω * ω * ω) :=
        step (ω * shift (shift ω)) 1 r₁.symm
    Derives T (n + 5) _ (shift (shift ω) * ω * shift ω * ω * ω) :=
        step 1 (ω * ω) r₃
    Derives T (n + 5) _ (shift (shift ω) * shift ω * shift ω * ω) :=
        step (shift (shift ω)) ω r₂
    Derives T (n + 5) _ (shift (shift ω) * shift (shift ω) * shift ω * shift (shift ω) * ω) :=
        step (shift (shift ω)) ω (lemma_cong_up (rule₄ r₁ r₂))

theorem rule₂ {n : ℕ} : Derives T (n + 5) (ω * shift ω * shift (shift ω) * ω)
    (shift (shift ω) * ω * shift ω * shift (shift ω)) :=
  calc Derives T (n + 5) (ω * shift ω * shift (shift ω) * ω)
          (ω * shift (shift ω) * shift (shift ω) * shift (shift ω) * shift ω *
            shift (shift ω) * ω) :=
        step ω (shift ω * shift (shift ω) * ω) (r₁_upup r₁).symm
    Derives T (n + 5) _ (ω * shift (shift ω) * ω * shift (shift ω)) :=
        step (ω * shift (shift ω)) 1 (rule₁ r₁ r₂ r₃).symm
    Derives T (n + 5) _ (shift (shift ω) * ω * shift ω * shift (shift ω)) :=
        step 1 (shift (shift ω)) r₃

theorem rule₅ {n : ℕ} :
    Derives T (n + 5) (ω * shift ω * shift (shift ω) * shift (shift ω) * ω)
      (shift ω * ω * shift ω * shift (shift ω) * shift (shift ω)) :=
  calc Derives T (n + 5) (ω * shift ω * shift (shift ω) * shift (shift ω) * ω)
          (ω * shift ω * shift (shift ω) * shift ω * shift ω * shift ω * shift (shift ω) * ω) :=
        step (ω * shift ω * shift (shift ω)) (shift (shift ω) * ω) (r₁_up r₁).symm
    Derives T (n + 5) _
          (ω * shift (shift ω) * shift (shift ω) * shift ω * shift ω * shift (shift ω) * ω) :=
        step ω (shift ω * shift ω * shift (shift ω) * ω) (r₂_up r₂)
    Derives T (n + 5) _
          (ω * shift (shift ω) * shift (shift ω) * shift ω * shift (shift ω) * shift (shift ω) *
            shift (shift ω) * shift ω * shift (shift ω) * ω) :=
        step (ω * shift (shift ω) * shift (shift ω) * shift ω) (shift ω * shift (shift ω) * ω)
          (r₁_upup r₁).symm
    Derives T (n + 5) _
          (ω * shift (shift ω) * shift (shift ω) * shift ω * shift (shift ω) * ω *
            shift (shift ω)) :=
        step (ω * shift (shift ω) * shift (shift ω) * shift ω * shift (shift ω)) 1
          (rule₁ r₁ r₂ r₃).symm
    Derives T (n + 5) _ (ω * ω * shift (shift ω) * shift (shift ω)) :=
        step ω (shift (shift ω)) (rule₁ r₁ r₂ r₃).symm
    Derives T (n + 5) _ (shift ω * ω * shift ω * shift (shift ω) * shift (shift ω)) :=
        step 1 (shift (shift ω) * shift (shift ω)) (rule₄ r₁ r₂)

theorem fig10 : Fig10 T where
  rule₁ := rule₁ r₁ r₂ r₃
  rule₂ := rule₂ r₁ r₂ r₃
  rule₃ := r₂
  rule₄ := rule₄ r₁ r₂
  rule₅ := rule₅ r₁ r₂ r₃
  rule₆ := rule₆ r₁ r₂
  rule₇ := r₁

end FromRelations

/-! ## Theorem 4's relations derive the rules -/

/-- The rules of Fig. 10 hold in the theory of Theorem 4's relations. -/
theorem fig10 : Fig10 SRel :=
  FromRelations.fig10 (Derivable.of (Lift.rule SRel.order)) (Derivable.of (Lift.rule SRel.near))
    (Derivable.of (Lift.rule SRel.far))

end QCert.Alt16RevCir.Alternating
