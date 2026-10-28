/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# CliffT₂ and its sources: encodings and decodings

Theorem 22 (4) transfers completeness on two qubits from Bian and Selinger's
presentation of the two-qubit Clifford+T operators (`QCert.CliffordT2`),
and on one qubit and none from Greylyn's presentation of `Uₘ(ℤ[1/√2, i])`
in dimensions `2` and `1` (`QCert.Greylyn`), where the paper names no
source.

* Two qubits (Table 3): `ω₈, H, T` are themselves, the CNOT is encoded as
  `H CZ H` on its target (`CX₁` of Bian and Selinger, qubit `1` being wire
  `0`) and the swap as three CNOTs; `S ↦ T T` and `CZ ↦ H CNOT H` decode.
* One qubit: `H ↦ H_[0,1]`, `T ↦ ω_[1]` and `ω₈ ↦ ω_[0] ω_[1]`; the
  generators decode as `X_[0,1] ↦ X = H Z H`, `H_[0,1] ↦ H`,
  `ω_[0] ↦ ω₈ T⁷` and `ω_[1] ↦ T`.
* No qubit: `ω₈ ↦ ω_[0]` and back.

Each encoding preserves the semantics because it does on every generator,
decided over `ℚ(ω)` (`flat_sem`).
-/
import QCert.Minimality.CliffordT.Semantics
import QCert.Minimality.Flat
import QCert.CliffordT2.Semantics
import QCert.Greylyn.Semantics

namespace QCert.Minimality.CliffordT

open Matrix QCert.Circuit

/-- `H` on wire `1` of two. -/
abbrev H₁ : Circuit Gate 2 := shift (g1 .H)

/-! ### Two qubits: Bian and Selinger's presentation -/

namespace BS

open QCert.CliffordT2

/-- The encoding of the generators on two wires. -/
def e : Gen Gate 2 → Word QCert.CliffordT2.Gen
  | .gate0 .ω => W.ω
  | .gate1 .H => W.H 1
  | .gate1 .T => W.T 1
  | .gate2 .CX => W.CX 1
  | .gate2 .swap => W.CX 1 * W.CX 0 * W.CX 1
  | .up (.gate0 .ω) => W.ω
  | .up (.gate1 .H) => W.H 0
  | .up (.gate1 .T) => W.T 0
  | .up (.up (.gate0 .ω)) => W.ω

/-- The encoding of two-wire circuits. -/
def E : Circuit Gate 2 →* Word QCert.CliffordT2.Gen := FreeMonoid.lift e

/-- The decoding of the letters: qubit `0` is wire `1`. -/
def d : QCert.CliffordT2.Gen → Circuit Gate 2
  | .ω => ω
  | .H₀ => H₁
  | .H₁ => H₀
  | .S₀ => S₁
  | .S₁ => S₀
  | .T₀ => T₁
  | .T₁ => T₀
  | .CZ => seq [H₀, CX, H₀]

/-- The decoding of Bian and Selinger's words. -/
def D : Word QCert.CliffordT2.Gen →* Circuit Gate 2 := FreeMonoid.lift d

theorem matQ_symm : ∀ y : QCert.CliffordT2.Gen, (QCert.CliffordT2.matQ y)ᵀ = QCert.CliffordT2.matQ y := by
  intro y; cases y <;> decide +kernel

theorem e_ok : ∀ g : Gen Gate 2,
    ofMat (d := 2) (k := 2) (FreeMonoid.lift matQ (e g)) =
      QOmega.invSqrt2 ^ scaled.exGen g • (scaled.ops.gen g).map ZOmega.toQ
  | .gate0 .ω => by decide +kernel
  | .gate1 .H => by decide +kernel
  | .gate1 .T => by decide +kernel
  | .gate2 .CX => by decide +kernel
  | .gate2 .swap => by decide +kernel
  | .up (.gate0 .ω) => by decide +kernel
  | .up (.gate1 .H) => by decide +kernel
  | .up (.gate1 .T) => by decide +kernel
  | .up (.up (.gate0 .ω)) => by decide +kernel

end BS

/-! ### One qubit and none: Greylyn's presentation -/

namespace GL

/-- `X` over `ℚ(ω)`. -/
def XQ : Matrix (Fin 2) (Fin 2) QOmega := !![0, 1; 1, 0]

/-- Greylyn's generators over `ℚ(ω)`. -/
def matG {m : ℕ} : QCert.Greylyn.Gen m → Matrix (Fin m) (Fin m) QOmega
  | .X j k _ => twoLevel j k XQ
  | .H j k _ => twoLevel j k QCert.CliffordT2.Hm
  | .ω j => oneLevel j Quartic.X

theorem mat_eq {m : ℕ} (x : QCert.Greylyn.Gen m) :
    QCert.Greylyn.mat x = (matG x).map QOmega.toC := by
  cases x with
  | X j k h =>
    simp only [QCert.Greylyn.mat, matG, twoLevel, levelMat_map]
    congr 1
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [QCert.Greylyn.Xmat, XQ, -Quartic.zero_def, -Quartic.one_def]
  | H j k h =>
    simp only [QCert.Greylyn.mat, matG, twoLevel, levelMat_map]
    congr 1
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [QCert.Greylyn.Hmat, QCert.CliffordT2.Hm, QCert.CliffordT2.s, QOmega.toC_invSqrt2,
        -Quartic.neg_def]
  | ω j =>
    simp only [QCert.Greylyn.mat, matG, oneLevel, levelMat_map]
    congr 1
    ext a b
    fin_cases a; fin_cases b
    simp [QOmega.toC_X]

/-- Greylyn's matrices as complex matrices. -/
def κ (m : ℕ) : U_ZInvSqrt2I m →* Matrix (Fin m) (Fin m) ℂ :=
  (unitaryGroup (Fin m) ℂ).subtype.comp (U_ZInvSqrt2I m).subtype

theorem κ_injective (m : ℕ) : Function.Injective (κ m) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem κ_sem {m : ℕ} (x : QCert.Greylyn.Gen m) :
    κ m (FreeMonoid.lift (QCert.Greylyn.sem m) (FreeMonoid.of x)) = (matG x).map QOmega.toC := by
  rw [FreeMonoid.lift_eval_of, ← mat_eq]; rfl

/-- The encoding of the generators on one wire. -/
def e₁ : Gen Gate 1 → Word (QCert.Greylyn.Gen 2)
  | .gate0 .ω => QCert.Greylyn.ω 0 * QCert.Greylyn.ω 1
  | .gate1 .H => QCert.Greylyn.H 0 1 (by decide)
  | .gate1 .T => QCert.Greylyn.ω 1
  | .up (.gate0 .ω) => QCert.Greylyn.ω 0 * QCert.Greylyn.ω 1

/-- The decoding of Greylyn's generators in dimension `2`. -/
def d₁ : QCert.Greylyn.Gen 2 → Circuit Gate 1
  | .X _ _ _ => X
  | .H _ _ _ => H
  | .ω j => if j = 0 then ω * Tdg else T

def D₁ : Word (QCert.Greylyn.Gen 2) →* Circuit Gate 1 := FreeMonoid.lift d₁

theorem e₁_ok : ∀ g : Gen Gate 1,
    ofMat (d := 2) (k := 1) (FreeMonoid.lift matG (e₁ g)) =
      QOmega.invSqrt2 ^ scaled.exGen g • (scaled.ops.gen g).map ZOmega.toQ
  | .gate0 .ω => by decide +kernel
  | .gate1 .H => by decide +kernel
  | .gate1 .T => by decide +kernel
  | .up (.gate0 .ω) => by decide +kernel

/-- The encoding with no wire. -/
def e₀ : Gen Gate 0 → Word (QCert.Greylyn.Gen 1)
  | .gate0 .ω => QCert.Greylyn.ω 0

/-- The decoding in dimension `1` (only `ω_[0]` is a generator there). -/
def d₀ : QCert.Greylyn.Gen 1 → Circuit Gate 0
  | .X _ _ _ => 1
  | .H _ _ _ => 1
  | .ω _ => ω

def D₀ : Word (QCert.Greylyn.Gen 1) →* Circuit Gate 0 := FreeMonoid.lift d₀

theorem e₀_ok : ∀ g : Gen Gate 0,
    ofMat (d := 2) (k := 0) (FreeMonoid.lift matG (e₀ g)) =
      QOmega.invSqrt2 ^ scaled.exGen g • (scaled.ops.gen g).map ZOmega.toQ
  | .gate0 .ω => by decide +kernel

end GL

end QCert.Minimality.CliffordT
