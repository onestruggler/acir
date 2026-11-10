/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The rules of Lafont's Fig. 10, in a theory

Translation of `Examples/Groups/Alternating/Rules.agda`.

Lemma 8 of the paper: any circuit reduces to a canonical form by the rules
of Fig. 10 (and the interchange law, which here is `Lift.comm3`).  The seven
rules are numbered in the figure's reading order: the rule on top, then each
row left to right.  Read as rewriting steps (left to right), each moves a
cycle down past one of Lafont's stairs:

    rule₁  ω₁ ω₃           → ω₃ ω₃ ω₂ ω₃ ω₁   (used by Lemma 7)
    rule₂  ω₁ ω₂ ω₃ ω₁     → ω₃ ω₁ ω₂ ω₃      (stairs of size ≥ 3)
    rule₃  ω₁ ω₂ ω₁        → ω₂ ω₂            (stairs of size 2)
    rule₄  ω₁ ω₁           → ω₂ ω₁ ω₂         (stairs of size 1)
    rule₅  ω₁ ω₂ ω₃ ω₃ ω₁  → ω₂ ω₁ ω₂ ω₃ ω₃   (the last stairs, 5 wires)
    rule₆  ω₁ ω₂ ω₂ ω₁     → ω₂ ω₂ ω₁ ω₂ ω₂   (the last stairs, 4 wires)
    rule₇  ω₁ ω₁ ω₁        → id               (the last stairs, 3 wires)

in the paper's numbering, `ω_i` on the wires `i, i + 1, i + 2` and the words
drawn top to bottom; here `ω_i` is `ω` shifted `i − 1` times.
`Normalization` proves Lemma 8 in any theory where the rules hold
(`Fig10 T`), and `Derivations` derives them from Theorem 4's relations
(Lafont's Fig. 11).

**Deviations from the Agda.**  The Agda's `grouplike` (a theory with the
rules is grouplike) is `Fig10.grouplike`: the name `grouplike` is
`Presentation`'s, for Theorem 4's relations.  The rules as a theory of their
own (`_RRel,_===_`, `_RVRel,_===_`, `axioms`), which only
`presentation-Fig10` uses, are not translated.
-/
import QCert.Alt16RevCir.Lib.Alternating.Syntactics

namespace QCert.Alt16RevCir.Alternating

open QCert QCert.Circuit CircuitProp

/-! ## The rules of Fig. 10 hold in a theory -/

/-- The seven rules of Fig. 10 hold in the theory `T`, at every width. -/
structure Fig10 (T : Theory) : Prop where
  rule₁ : ∀ {n : ℕ}, Derives T (n + 5) (ω * shift (shift ω))
    (shift (shift ω) * shift (shift ω) * shift ω * shift (shift ω) * ω)
  rule₂ : ∀ {n : ℕ}, Derives T (n + 5) (ω * shift ω * shift (shift ω) * ω)
    (shift (shift ω) * ω * shift ω * shift (shift ω))
  rule₃ : ∀ {n : ℕ}, Derives T (n + 4) (ω * shift ω * ω) (shift ω * shift ω)
  rule₄ : ∀ {n : ℕ}, Derives T (n + 4) (ω * ω) (shift ω * ω * shift ω)
  rule₅ : ∀ {n : ℕ}, Derives T (n + 5) (ω * shift ω * shift (shift ω) * shift (shift ω) * ω)
    (shift ω * ω * shift ω * shift (shift ω) * shift (shift ω))
  rule₆ : ∀ {n : ℕ}, Derives T (n + 4) (ω * shift ω * shift ω * ω)
    (shift ω * shift ω * ω * shift ω * shift ω)
  rule₇ : ∀ {n : ℕ}, Derives T (n + 3) (ω * ω * ω) 1

/-! ## A theory with the rules is grouplike -/

/-- By `rule₇`, `ω * ω` is an inverse of `ω`; a shifted generator has the
shifted inverse (the Agda's `grouplike`). -/
theorem Fig10.grouplike {T : Theory} (rules : Fig10 T) :
    ∀ (n : ℕ), Grouplike (Lift T n)
  | _, .gate0 g => nomatch g
  | _, .gate1 g => nomatch g
  | _, .gate2 g => nomatch g
  | _, .gate3 .ω_gate => ⟨ω * ω, rules.rule₇⟩
  | _, @Gen.up _ k g =>
    let ⟨ig, prf⟩ := Fig10.grouplike rules k g
    ⟨shift ig, by simpa using lemma_cong_up prf⟩

end QCert.Alt16RevCir.Alternating
