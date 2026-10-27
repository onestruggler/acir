/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn's presentation on five generators

Section 5.2 of Bian–Selinger (arXiv:2204.02217) uses "a simplified
presentation of Greylyn's generators and relations, using only 5
generators and 19 relations (instead of Greylyn's original 16 generators
and 123 relations)"; it is given in the authors' accompanying code
(`Greylyn-Simplified.agda`): the generators `ω₀, X₀₁, X₁₂, X₂₃, H₀₁`, the
other one- and two-level matrices as conjugates of these by the
transpositions `X₀₁, X₁₂, X₂₃`, and the relations (S1)–(S19).

Every derivation from Greylyn's relations (`QCert.Greylyn.Rel 4`) is
carried to one from (S1)–(S19) by the translation `simple`
(`derivable_simple`): each of the 123 instances of Greylyn's relations is
checked by normalizing both sides with a rewriting system, possibly
after conjugating one of (S1)–(S19) by a permutation (the authors'
"basis change").
-/
import QCert.CliffordT2.Rewrite
import QCert.Greylyn.Syntax
import Mathlib.Tactic.DeriveFintype

namespace QCert.CliffordT2.Simplified

/-- The five generators: `ω₀ = ω_[0]`, `X₀₁ = X_[0,1]`, `X₁₂ = X_[1,2]`,
`X₂₃ = X_[2,3]`, `H₀₁ = H_[0,1]`. -/
inductive SGen : Type
  | ω₀ | X₀₁ | X₁₂ | X₂₃ | H₀₁
  deriving DecidableEq, Fintype, Repr

namespace SW

/-- The letter `x`. -/
abbrev g (x : SGen) : Word SGen := FreeMonoid.of x

abbrev ω₀ : Word SGen := g .ω₀
abbrev X₀₁ : Word SGen := g .X₀₁
abbrev X₁₂ : Word SGen := g .X₁₂
abbrev X₂₃ : Word SGen := g .X₂₃
abbrev H₀₁ : Word SGen := g .H₀₁

/-- `X_[0,2] = X₁₂ X₀₁ X₁₂`. -/
def X₀₂ : Word SGen := X₁₂ * X₀₁ * X₁₂
/-- `X_[0,3] = X₂₃ X₀₂ X₂₃`. -/
def X₀₃ : Word SGen := X₂₃ * X₀₂ * X₂₃
/-- `X_[1,3] = X₂₃ X₁₂ X₂₃`. -/
def X₁₃ : Word SGen := X₂₃ * X₁₂ * X₂₃
/-- `ω_[1] = X₀₁ ω₀ X₀₁`. -/
def ω₁ : Word SGen := X₀₁ * ω₀ * X₀₁
/-- `ω_[2] = X₁₂ ω₁ X₁₂`. -/
def ω₂ : Word SGen := X₁₂ * ω₁ * X₁₂
/-- `ω_[3] = X₂₃ ω₂ X₂₃`. -/
def ω₃ : Word SGen := X₂₃ * ω₂ * X₂₃
/-- `H_[0,2] = X₁₂ H₀₁ X₁₂`. -/
def H₀₂ : Word SGen := X₁₂ * H₀₁ * X₁₂
/-- `H_[0,3] = X₂₃ H₀₂ X₂₃`. -/
def H₀₃ : Word SGen := X₂₃ * H₀₂ * X₂₃
/-- `H_[1,2] = X₀₁ X₁₂ H₀₁ X₁₂ X₀₁`. -/
def H₁₂ : Word SGen := X₀₁ * X₁₂ * H₀₁ * X₁₂ * X₀₁
/-- `H_[1,3] = X₂₃ H₁₂ X₂₃`. -/
def H₁₃ : Word SGen := X₂₃ * H₁₂ * X₂₃
/-- `H_[2,3] = X₁₂ X₂₃ H₁₂ X₂₃ X₁₂`. -/
def H₂₃ : Word SGen := X₁₂ * X₂₃ * H₁₂ * X₂₃ * X₁₂

end SW

open SW

/-- The relations (S1)–(S19). -/
inductive SRel : WRel SGen
  | s1 : SRel (ω₀ ^ 8) 1
  | s2 : SRel (H₀₁ ^ 2) 1
  | s3 : SRel (X₀₁ ^ 2) 1
  | s4 : SRel (X₁₂ ^ 2) 1
  | s5 : SRel (X₂₃ ^ 2) 1
  | s6 : SRel (ω₀ * ω₁) (ω₁ * ω₀)
  | s7 : SRel (ω₂ * H₀₁) (H₀₁ * ω₂)
  | s8 : SRel (ω₀ * X₁₂) (X₁₂ * ω₀)
  | s9 : SRel (ω₀ * X₂₃) (X₂₃ * ω₀)
  | s10 : SRel (H₀₁ * H₂₃) (H₂₃ * H₀₁)
  | s11 : SRel (H₀₁ * X₂₃) (X₂₃ * H₀₁)
  | s12 : SRel (X₀₁ * X₂₃) (X₂₃ * X₀₁)
  | s13 : SRel (X₀₁ * X₁₂ * X₀₁) (X₁₂ * X₀₁ * X₁₂)
  | s14 : SRel (X₁₂ * X₂₃ * X₁₂) (X₂₃ * X₁₂ * X₂₃)
  | s15 : SRel (ω₀ * ω₁ * X₀₁) (X₀₁ * ω₀ * ω₁)
  | s16 : SRel (ω₀ * ω₁ * H₀₁) (H₀₁ * ω₀ * ω₁)
  | s17 : SRel (H₀₁ * X₀₁) (ω₁ ^ 4 * H₀₁)
  | s18 : SRel (H₀₁ * ω₀ ^ 2 * H₀₁) (ω₀ ^ 6 * H₀₁ * ω₀ ^ 3 * ω₁ ^ 5)
  | s19 : SRel (H₀₁ * H₂₃ * H₀₂ * H₁₃) (H₀₂ * H₁₃ * H₀₁ * H₂₃)

/-! ### The translation from Greylyn's generators -/

/-- `ω_[j]`. -/
def omega : Fin 4 → Word SGen
  | 0 => ω₀
  | 1 => ω₁
  | 2 => ω₂
  | 3 => ω₃

/-- `X_[j,k]`, `j < k`. -/
def xw : Fin 4 → Fin 4 → Word SGen
  | 0, 1 => X₀₁
  | 0, 2 => X₀₂
  | 0, 3 => X₀₃
  | 1, 2 => X₁₂
  | 1, 3 => X₁₃
  | 2, 3 => X₂₃
  | _, _ => 1

/-- `H_[j,k]`, `j < k`. -/
def hw : Fin 4 → Fin 4 → Word SGen
  | 0, 1 => H₀₁
  | 0, 2 => H₀₂
  | 0, 3 => H₀₃
  | 1, 2 => H₁₂
  | 1, 3 => H₁₃
  | 2, 3 => H₂₃
  | _, _ => 1

/-- The translation of Greylyn's generators (`simple-of-greylyn`). -/
def simple : Greylyn.Gen 4 → Word SGen
  | .ω j => omega j
  | .X j k _ => xw j k
  | .H j k _ => hw j k

/-! ### The rewriting system -/

section Rules

/-- `X₀₁ X₂₃ X₁₂ X₀₁ = X₂₃ X₁₂ X₀₁ X₁₂`. -/
theorem lemma_X : Derivable SRel (X₀₁ * X₂₃ * X₁₂ * X₀₁) (X₂₃ * X₁₂ * X₀₁ * X₁₂) := by
  have h1 := (Derivable.of SRel.s12).mul_right (X₁₂ * X₀₁)
  have h2 := (Derivable.of SRel.s13).mul_left X₂₃
  simp only [mul_assoc] at h1 h2 ⊢
  exact h1.trans h2

/-- The rewriting rules of the authors' `Greylyn-Simplified-Step`. -/
def rules : List (Rule SRel) :=
  [ (Rule.ofDerivable _ _ (Derivable.of SRel.s8)).symm,
    (Rule.ofDerivable _ _ (Derivable.of SRel.s9)).symm,
    (Rule.ofDerivable _ _ (Derivable.of SRel.s11)).symm,
    (Rule.ofDerivable _ _ (Derivable.of SRel.s12)).symm,
    Rule.ofDerivable _ _ (Derivable.of SRel.s3),
    Rule.ofDerivable _ _ (Derivable.of SRel.s4),
    Rule.ofDerivable _ _ (Derivable.of SRel.s5),
    Rule.ofDerivable _ _ (Derivable.of SRel.s13),
    Rule.ofDerivable _ _ (Derivable.of SRel.s14),
    Rule.ofDerivable _ _ lemma_X,
    Rule.ofDerivable _ _ (Derivable.of SRel.s1),
    Rule.ofDerivable _ _ (Derivable.of SRel.s2) ]

end Rules

/-- Normalization proves an equation. -/
theorem by_nf (w v : Word SGen)
    (h : normalize rules 200 (FreeMonoid.toList w) = normalize rules 200 (FreeMonoid.toList v)) :
    Derivable SRel w v :=
  derivable_of_normalize rules 200 w v h

/-- The authors' basis change: `u' ∼ g u g'` and `v' ∼ g v g'` by
normalization, and `u ∼ v`. -/
theorem by_bc {u v u' v' : Word SGen} (g g' : Word SGen) (huv : Derivable SRel u v)
    (hu : normalize rules 200 (FreeMonoid.toList u') =
      normalize rules 200 (FreeMonoid.toList (g * u * g')))
    (hv : normalize rules 200 (FreeMonoid.toList (g * v * g')) =
      normalize rules 200 (FreeMonoid.toList v')) :
    Derivable SRel u' v' :=
  ((by_nf _ _ hu).trans ((huv.mul_left g).mul_right g')).trans (by_nf _ _ hv)

end QCert.CliffordT2.Simplified
