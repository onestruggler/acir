/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: the main theorems

Translation of `Theorems.agda`, with the circuit versions of
`Circuits/Presentation.agda` and the refutations of `Errata.agda`.

Amy, Ross and Wesley, *A Sound and Complete Equational Theory for 3-Qubit
Toffoli-Hadamard Circuits* (QPL 2024, arXiv:2407.11152), by translation into
Li, Ross and Selinger's presentations of `O(8, 𝔻)` and `L₈`
(`QCert.LiRossSelinger`):

* `theorem_5_2`: `R₁⁺ = Figure 4 ∪ Figure 7 ∪ {r_K}` presents `O(8, 𝔻)` on
  the alphabet `Σ₁` (soundness `soundness₁`, completeness `completeness₁`);
* `theorem_6_3`: `R₂⁺ = R₁⁺ ∪ Figure 8` presents `TofH(3) = L₈` on `Σ₂`
  (`soundness₂`, `completeness₂`);
* `r_K_independent`: `r_K` (Section 5.5, `K₁₂ = X₀ NK X₀ NK`, which Figures 4
  and 7 omit) holds of the matrices but does not follow from
  `R₁ = Figure 4 ∪ Figure 7`, so the paper's `R₁` is not complete;
* `circuits_5_2`, `circuits_6_3`: the same presentations for the circuits of
  `Circuits.Syntactics` on three wires;
* the printed equations that are false, each refuted by one matrix entry.
-/
import QCert.ToffoliHadamardRS.Circuits.Presentation
import QCert.ToffoliHadamardRS.Independence
import QCert.ToffoliHadamardRS.Errata
import QCert.ToffoliHadamardRS.GateMatrices

namespace QCert.ToffoliHadamardRS

open LiRossSelinger (sem)

/-! ## Theorem 5.2, with `r_K`: `R₁⁺` presents `O(8, 𝔻)` -/

theorem soundness₁ {w v : Word G₁} (d : Derivable R1plus w v) : semO w = semO v :=
  sound1plus_der d

theorem completeness₁ {w v : Word G₁} (h : semO w = semO v) : Derivable R1plus w v :=
  complete1 h

theorem theorem_5_2 : IsPresentationOf R1plus sem1 := presentation

/-! ## Theorem 6.3, with `r_K`: `R₂⁺` presents `TofH(3)` -/

theorem soundness₂ {w v : Word G₂} (d : Derivable R2plus w v) : semH w = semH v :=
  sound2plus_der d

theorem completeness₂ {w v : Word G₂} (h : semH w = semH v) : Derivable R2plus w v :=
  complete2 h

theorem theorem_6_3 : IsPresentationOf R2plus sem2 := presentationH

/-! ## `r_K` is independent of `R₁` -/

theorem r_K_independent :
    semO (K12 : Word G₁) = semO (X0 * NKw * X0 * NKw : Word G₁) ∧
      ¬ Derivable R1 K12 (X0 * NKw * X0 * NKw) :=
  R1_incomplete

/-! ## The circuit versions -/

theorem circuits_5_2 : IsPresentationOf (QCert.Lift Circuits.SRel1 3) Circuits.sem1 :=
  Circuits.theorem_5_2

theorem circuits_6_3 : IsPresentationOf (QCert.Lift Circuits.SRel2 3) Circuits.sem2 :=
  Circuits.theorem_6_3

/-! ## The errata: the printed equations that are false -/

/-- (33) of Figure 4, (97) and (100) of Figure 7, Section 5.5's `CCX₁₂ = X_[6,7]`
and `(r_CX)`, Section 5.6's `(-1)_[0]` and Section 5.7's decomposition of
`CCZ` (`Errata`). -/
theorem errata :
    sem₀ CCX01 ≠ sem₀ (SW12 * CCX02 * SW02) ∧
    sem₀ CCX12 ≠ FreeMonoid.lift (sem 8) (Xw 6 7) ∧
    sem₀ CX01 ≠ FreeMonoid.lift (sem 8) (Xw 2 6 * Xw 3 7) ∧
    FreeMonoid.lift (sem 8) (Mw 0) ≠ semₗ₁ (X0 * X1 * CCZw * X1 * X0) ∧
    semₗ₁ (T 0 * NKw) ≠ semₗ₁ (NKw * T 0 * m 1 * m 3) ∧
    semₗ₁ (NKw * Kq 1 3 4 5) ≠ semₗ₁ (Kq 1 3 4 5 * NKw) ∧
    semₗ₁ CCZw ≠ semₗ₁ (K12 * CZ12 * X0 * NKw * X0 * CZ12 * NKw * T 5) :=
  ⟨r033_false, x67_false, rCX_false, m0_false, r097_false, r100_false, ccz_false⟩

end QCert.ToffoliHadamardRS
