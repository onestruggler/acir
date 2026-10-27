/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The translation into Greylyn's generators

Section 5.1 of Bian–Selinger (arXiv:2204.02217) fixes the translation
`f : 𝒳 → 𝒴*` of the Clifford+T generators into Greylyn's one- and
two-level generators:

  f(ω) = ω_[0] ω_[1] ω_[2] ω_[3],   f(H₀) = H_[1,3] H_[0,2],
  f(H₁) = H_[2,3] H_[0,1],          f(S₀) = ω²_[2] ω²_[3],
  f(S₁) = ω²_[1] ω²_[3],            f(T₀) = ω_[2] ω_[3],
  f(T₁) = ω_[1] ω_[3],              f(CZ) = ω⁴_[3],

and uses that it "respects the interpretation": `⟦f(x)⟧ = ⟦x⟧`
(`lift_f`).  The matrices of Greylyn's generators (`QCert.Greylyn.mat`)
are read over ℚ(ω) (`gmatQ`), where the identity is decided.
-/
import QCert.CliffordT2.Eval
import QCert.Greylyn.Semantics

namespace QCert.CliffordT2

open Matrix Greylyn

/-- `ω_[j]` of Greylyn's generators, on 4 indices. -/
abbrev gω (j : Fin 4) : Word (Greylyn.Gen 4) := Greylyn.ω j
/-- `H_[j,k]`. -/
abbrev gH (j k : Fin 4) (h : j < k := by decide) : Word (Greylyn.Gen 4) := Greylyn.H j k h

/-- The translation `f` of Section 5.1. -/
def fG : Gen → Word (Greylyn.Gen 4)
  | .ω => gω 0 * gω 1 * gω 2 * gω 3
  | .H₀ => gH 1 3 * gH 0 2
  | .H₁ => gH 2 3 * gH 0 1
  | .S₀ => gω 2 ^ 2 * gω 3 ^ 2
  | .S₁ => gω 1 ^ 2 * gω 3 ^ 2
  | .T₀ => gω 2 * gω 3
  | .T₁ => gω 1 * gω 3
  | .CZ => gω 3 ^ 4

/-- `X` over ℚ(ω). -/
def XQ : Matrix (Fin 2) (Fin 2) QOmega := !![0, 1; 1, 0]

/-- The matrices of Greylyn's generators over ℚ(ω). -/
def gmatQ : Greylyn.Gen 4 → Matrix (Fin 4) (Fin 4) QOmega
  | .X j k _ => twoLevel j k XQ
  | .H j k _ => twoLevel j k Hm
  | .ω j => oneLevel j ωQ

theorem cmat_XQ : XQ.map QOmega.toC = Xmat := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [XQ, Xmat, -Quartic.zero_def, -Quartic.one_def]

theorem cmat_Hm : Hm.map QOmega.toC = Hmat := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [Hm, Hmat, s, QOmega.toC_invSqrt2, -Quartic.neg_def]

theorem mat_eq_cmat (y : Greylyn.Gen 4) : Greylyn.mat y = cmat (gmatQ y) := by
  cases y with
  | X j k _ => simp only [Greylyn.mat, gmatQ, cmat, twoLevel_map, cmat_XQ]
  | H j k _ => simp only [Greylyn.mat, gmatQ, cmat, twoLevel_map, cmat_Hm]
  | ω j => simp only [Greylyn.mat, gmatQ, cmat, oneLevel_map, QOmega.toC_X]

/-- The value of a word of Greylyn's generators, as a matrix. -/
theorem coe_lift_sem (u : Word (Greylyn.Gen 4)) :
    (((FreeMonoid.lift (Greylyn.sem 4) u : U_ZInvSqrt2I 4) : unitaryGroup (Fin 4) ℂ) :
      Matrix (Fin 4) (Fin 4) ℂ) = cmat (FreeMonoid.lift gmatQ u) := by
  induction u using FreeMonoid.inductionOn' with
  | one => simp [cmat_one]
  | mul_of y u ih =>
    rw [map_mul, map_mul, Subgroup.coe_mul, Submonoid.coe_mul, ih, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of, cmat_mul, coe_sem, mat_eq_cmat]

theorem gmatQ_fG : ∀ x : Gen, FreeMonoid.lift gmatQ (fG x) = matQ x := by
  decide +kernel

/-- `f` respects the interpretation. -/
theorem lift_f (x : Gen) : FreeMonoid.lift (Greylyn.sem 4) (fG x) = semU x := by
  apply Subtype.ext; apply Subtype.ext
  rw [coe_lift_sem, gmatQ_fG]
  rfl

theorem lift_lift_f (w : Word Gen) :
    FreeMonoid.lift (Greylyn.sem 4) (FreeMonoid.lift fG w) = FreeMonoid.lift semU w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih => rw [map_mul, map_mul, map_mul, ih, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of, lift_f]

end QCert.CliffordT2
