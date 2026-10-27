/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The coset data of the Reidemeister–Schreier argument

Section 5 of Bian–Selinger (arXiv:2204.02217) applies the
Reidemeister–Schreier theorem (Theorem 4.3) to the five-generator form
of Greylyn's presentation: the two-qubit Clifford+T group has index 2 in
`U₄(ℤ[1/√2, i])` (its elements are the matrices whose determinant is a
power of `i`), so there are two cosets, `I` and `Ω` (representatives `1`
and `ω_[3]`), and the authors' code (`Completeness.agda`) gives the coset
action `h` and the translation `f' = simple ∘ f` used here.

Hypothesis (a) is one equation per Clifford+T generator (the authors'
Equations 1–8) and hypothesis (b) one per coset and relation (S1)–(S19)
(Equations 9–46, `eqn (9 + 2 (k - 1))` for `(I, Sk)` and the next one for
`(Ω, Sk)`).  The cosets reached are computed (`decide`); the equations are
in `Equations.lean`.
-/
import QCert.CliffordT2.Translation
import QCert.CliffordT2.SimplifiedGreylyn
import QCert.CliffordT2.ReidemeisterSchreier

namespace QCert.CliffordT2

open W Simplified

/-- The swap gate `H₀ CZ H₀ H₁ CZ H₁ H₀ CZ H₀`. -/
def Swap : Word Gen := CX 0 * CX 1 * CX 0

/-- The two cosets, with representatives `1` and `ω_[3]`. -/
inductive Coset : Type
  | I | Ω
  deriving DecidableEq, Repr

/-- The coset action `h` of the authors' code. -/
def hT : Coset → SGen → Word Gen × Coset
  | .I, .ω₀ => (Tdg 0 * Tdg 1 * W.ω, .Ω)
  | .I, .X₀₁ => (X 1 * CX 1, .I)
  | .I, .X₁₂ => (Swap, .I)
  | .I, .X₂₃ => (CX 1, .I)
  | .I, .H₀₁ => (X 0 * CH 1 * X 0, .I)
  | .Ω, .ω₀ => (X 0 * CX 0 * T 0 * CX 0 * X 0, .I)
  | .Ω, .X₀₁ => (X 1 * CX 1, .Ω)
  | .Ω, .X₁₂ => (Swap, .Ω)
  | .Ω, .X₂₃ => (T 1 * CX 1 * Tdg 1, .Ω)
  | .Ω, .H₀₁ => (X 0 * CH 1 * X 0, .Ω)

/-- `f' = simple ∘ f`, the translation into the five generators. -/
def f' (x : Gen) : Word SGen := FreeMonoid.lift simple (fG x)

theorem lift_simple_lift_fG (w : Word Gen) :
    FreeMonoid.lift simple (FreeMonoid.lift fG w) = FreeMonoid.lift f' w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih => rw [map_mul, map_mul, map_mul, ih, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of]; rfl

/-- The words of hypothesis (a), `h**(I, f'(x))`. -/
def wordA (x : Gen) : Word Gen := (hstar hT .I (f' x)).1

theorem cosetA : ∀ x : Gen, (hstar hT .I (f' x)).2 = .I := by decide +kernel

/-- The two words of hypothesis (b) for the coset `c` and a relation. -/
def wordB (c : Coset) (w : Word SGen) : Word Gen := (hstar hT c w).1

theorem cosetB : ∀ (c : Coset) (w w' : Word SGen), SRel w w' →
    (hstar hT c w).2 = (hstar hT c w').2 := by
  intro c w w' h
  cases c <;> cases h <;> decide +kernel

end QCert.CliffordT2
