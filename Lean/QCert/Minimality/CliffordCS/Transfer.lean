/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# CliffCS₂ and its sources: encodings and decodings

Theorem 22 (5) transfers completeness on no wire, one and two from Bian
and Selinger's presentation of `Uₘ(ℤ[½, i])` in dimensions `1, 2, 4`
(`QCert.BianSelingerUn`), which the paper leaves implicit, and on three
wires from their three-qubit Clifford+CS presentation.  The sources'
scalars are the powers of `i`, those of CliffCS₂ the powers of `ω`, so
each source is refined by a new central scalar `w` with `w² = i`
(Appendix I, `FlatRefine`).

* No wire: `ω₈ ↦ w`; the generator `i_[0]` decodes as `ω₈²` and `w` as `ω₈`.
* One wire: `H ↦ w K_[0,1]` (`K = ω† H`), `S ↦ i_[1]`, `ω₈ ↦ w`; the
  generators decode as `X_[0,1] ↦ H S S H`, `K_[0,1] ↦ ω₈⁷ H`,
  `i_[0] ↦ ω₈² S³`, `i_[1] ↦ S`.

Each encoding preserves the semantics because it does on every generator,
decided over `ℚ(ω)` (`flat_sem`).
-/
import QCert.Minimality.CliffordCS.Semantics
import QCert.Minimality.FlatRefine
import QCert.BianSelingerUn.Soundness

namespace QCert.Minimality.CliffordCS

open Matrix QCert.Circuit OmegaParity

/-! ### Bian and Selinger's two-level generators over `ℚ(ω)` -/

namespace UN

/-- `X` over `ℚ(ω)`. -/
def XQ : Matrix (Fin 2) (Fin 2) QOmega := !![0, 1; 1, 0]

/-- `(1 - i)/2 = (1 + i)⁻¹`. -/
def kQ : QOmega := ⟨1 / 2, 0, -1 / 2, 0⟩

/-- `K = ω† H` over `ℚ(ω)`. -/
def KQ : Matrix (Fin 2) (Fin 2) QOmega := !![kQ, kQ; kQ, -kQ]

/-- The generators over `ℚ(ω)`. -/
def matU {m : ℕ} : QCert.BianSelingerUn.Gen m → Matrix (Fin m) (Fin m) QOmega
  | .X j k _ => twoLevel j k XQ
  | .K j k _ => twoLevel j k KQ
  | .i j => oneLevel j QOmega.I

theorem toC_kQ : QOmega.toC kQ = (1 + Complex.I)⁻¹ := by
  rw [QCert.BianSelingerUn.inv_one_add_I]
  have : kQ = Quartic.ofRat (1 / 2) - Quartic.ofRat (1 / 2) * QOmega.I := by decide +kernel
  have hq : QOmega.toC (Quartic.ofRat (1 / 2)) = ((1 / 2 : ℚ) : ℂ) := Quartic.lift_ofRat _ _ _
  rw [this, map_sub, map_mul, QOmega.toC_I, hq]
  push_cast
  ring

theorem mat_eq {m : ℕ} (x : QCert.BianSelingerUn.Gen m) :
    QCert.BianSelingerUn.mat x = (matU x).map QOmega.toC := by
  cases x with
  | X j k h =>
    simp only [QCert.BianSelingerUn.mat, matU, twoLevel, levelMat_map]
    congr 1
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [QCert.BianSelingerUn.Xmat, XQ, -Quartic.zero_def, -Quartic.one_def]
  | K j k h =>
    simp only [QCert.BianSelingerUn.mat, matU, twoLevel, levelMat_map]
    congr 1
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [QCert.BianSelingerUn.Kmat, KQ, toC_kQ, -Quartic.neg_def]
  | i j =>
    simp only [QCert.BianSelingerUn.mat, matU, oneLevel, levelMat_map]
    congr 1
    ext a b
    fin_cases a; fin_cases b
    simp [QOmega.toC_I]

/-- The source's matrices as complex matrices. -/
def κ (m : ℕ) : U_ZHalfI m →* Matrix (Fin m) (Fin m) ℂ :=
  (unitaryGroup (Fin m) ℂ).subtype.comp (U_ZHalfI m).subtype

theorem κ_injective (m : ℕ) : Function.Injective (κ m) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem κ_lift {m : ℕ} (a : Word (QCert.BianSelingerUn.Gen m)) :
    κ m (FreeMonoid.lift (QCert.BianSelingerUn.sem m) a) =
      (FreeMonoid.lift matU a).map QOmega.toC := by
  induction a using FreeMonoid.inductionOn' with
  | one => simp only [map_one]; exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  | mul_of x a ih =>
    rw [map_mul, map_mul, ih, map_mul, Matrix.map_mul, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of, ← mat_eq]
    rfl

theorem mapC_injective {m : ℕ} :
    Function.Injective (fun M : Matrix (Fin m) (Fin m) QOmega => M.map QOmega.toC) :=
  OmegaParity.mapC_injective

/-- The source's completeness, for its matrices over `ℚ(ω)`. -/
theorem complete_Q {m : ℕ}
    (hsrc : ∀ a b : Word (QCert.BianSelingerUn.Gen m),
      FreeMonoid.lift (QCert.BianSelingerUn.sem m) a =
        FreeMonoid.lift (QCert.BianSelingerUn.sem m) b →
        Derivable (QCert.BianSelingerUn.Rel m) a b)
    (a b : Word (QCert.BianSelingerUn.Gen m))
    (h : FreeMonoid.lift matU a = FreeMonoid.lift matU b) :
    Derivable (QCert.BianSelingerUn.Rel m) a b :=
  hsrc a b (κ_injective m (by rw [κ_lift, κ_lift, h]))

/-- The source's soundness, for its matrices over `ℚ(ω)`. -/
theorem sound_Q {m : ℕ} (a b : Word (QCert.BianSelingerUn.Gen m))
    (h : QCert.BianSelingerUn.Rel m a b) :
    FreeMonoid.lift matU a = FreeMonoid.lift matU b := by
  apply mapC_injective
  simp only
  rw [← κ_lift, ← κ_lift, QCert.BianSelingerUn.sound h]

theorem lift_ne_zero {m : ℕ} (hm : 0 < m) (a : Word (QCert.BianSelingerUn.Gen m)) :
    FreeMonoid.lift matU a ≠ 0 := by
  intro h0
  have hu := (FreeMonoid.lift (QCert.BianSelingerUn.sem m) a : unitaryGroup (Fin m) ℂ).2
  have hk : κ m (FreeMonoid.lift (QCert.BianSelingerUn.sem m) a) = 0 := by
    rw [κ_lift, h0]; exact Matrix.map_zero _ (map_zero _)
  have hm' : ((FreeMonoid.lift (QCert.BianSelingerUn.sem m) a : unitaryGroup (Fin m) ℂ) :
      Matrix (Fin m) (Fin m) ℂ) = 0 := hk
  rw [Matrix.mem_unitaryGroup_iff, hm', zero_mul] at hu
  have := congrFun (congrFun hu ⟨0, hm⟩) ⟨0, hm⟩
  simp at this

/-! ### Parity of the generators -/

theorem matU_even {m : ℕ} (x : QCert.BianSelingerUn.Gen m) : MEven (matU x) := by
  cases x with
  | X j k h => exact MEven.level _ (fun s t => by revert s t; decide +kernel)
  | K j k h => exact MEven.level _ (fun s t => by revert s t; decide +kernel)
  | i j => exact MEven.level _ (fun s t => by revert s t; decide +kernel)

/-- `i` times the identity, in dimension `m`. -/
def gi : (m : ℕ) → Word (QCert.BianSelingerUn.Gen m)
  | 0 => 1
  | m + 1 => FreeMonoid.ofList ((List.finRange (m + 1)).map QCert.BianSelingerUn.Gen.i)

end UN

/-! ### One wire -/

namespace W1

open UN

/-- The encoding of the generators on one wire. -/
def e : Gen Gate 1 → FreeMonoid (Option (QCert.BianSelingerUn.Gen 2))
  | .gate0 .ω => wl
  | .gate1 .H => wl * FreeMonoid.of (some (.K 0 1 (by decide)))
  | .gate1 .S => FreeMonoid.of (some (.i 1))
  | .up (.gate0 .ω) => wl

/-- The decoding of the refined generators in dimension `2`. -/
def d : Option (QCert.BianSelingerUn.Gen 2) → Circuit Gate 1
  | none => ω
  | some (.X _ _ _) => seq [H, S, S, H]
  | some (.K _ _ _) => ω ^ 7 * H
  | some (.i j) => if j = 0 then ω ^ 2 * (S * S * S) else S

def D : FreeMonoid (Option (QCert.BianSelingerUn.Gen 2)) →* Circuit Gate 1 := FreeMonoid.lift d

theorem e_ok : ∀ g : Gen Gate 1,
    ofMat (d := 2) (k := 1) (FreeMonoid.lift (matR matU) (e g)) =
      QOmega.invSqrt2 ^ scaled.exGen g • (scaled.ops.gen g).map ZOmega.toQ
  | .gate0 .ω => by decide +kernel
  | .gate1 .H => by decide +kernel
  | .gate1 .S => by decide +kernel
  | .up (.gate0 .ω) => by decide +kernel

theorem gi_eq : FreeMonoid.lift (matU (m := 2)) (gi 2) = QOmega.I • 1 := by decide +kernel

end W1

/-! ### No wire -/

namespace W0

open UN

def e : Gen Gate 0 → FreeMonoid (Option (QCert.BianSelingerUn.Gen 1))
  | .gate0 .ω => wl

def d : Option (QCert.BianSelingerUn.Gen 1) → Circuit Gate 0
  | none => ω
  | some (.i _) => ω ^ 2
  | some _ => 1

def D : FreeMonoid (Option (QCert.BianSelingerUn.Gen 1)) →* Circuit Gate 0 := FreeMonoid.lift d

theorem e_ok : ∀ g : Gen Gate 0,
    ofMat (d := 2) (k := 0) (FreeMonoid.lift (matR matU) (e g)) =
      QOmega.invSqrt2 ^ scaled.exGen g • (scaled.ops.gen g).map ZOmega.toQ
  | .gate0 .ω => by decide +kernel

theorem gi_eq : FreeMonoid.lift (matU (m := 1)) (gi 1) = QOmega.I • 1 := by decide +kernel

end W0

end QCert.Minimality.CliffordCS
