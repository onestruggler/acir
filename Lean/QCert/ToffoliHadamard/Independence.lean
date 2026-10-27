/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): `(r_K)` is independent of Figures 4 and 7

Let `R = I − J/4` be the reflection in the all-ones vector (`J` the
all-ones matrix).  Interpret each Toffoli–K gate `g ∈ Σ_D` as `R ⟦g⟧ R`,
and `K_[0,1,2,3]` and `CCZ` as themselves (`psi`).  Every relation of
Figure 4 holds (it is a relation among Toffoli–K gates, conjugated by
`R`), and so does every relation of Figure 7: those only involve
`K_[0,1,2,3]`, `CCZ` and permutation gates, which commute with `R`.  But
`(r_K)` fails: its right-hand side involves only `K_[0,1,2,3]` and
permutation gates, so it keeps its value `K_{1,2}`, while its left-hand
side becomes `R K_{1,2} R ≠ K_{1,2}`.  So `(r_K)` is not derivable from
Figures 4 and 7 (`rK_independent`).
-/
import QCert.ToffoliHadamard.Soundness

namespace QCert.ToffoliHadamard

open Matrix QCert.ListMat Sym1

/-- `R = I − J/4`, the reflection in the all-ones vector. -/
def reflR : Matrix (Fin 8) (Fin 8) QSqrt2 :=
  fun i j => (if i = j then 1 else 0) - Quadratic.ofRat (1 / 4)

/-- The interpretation: `R ⟦g⟧ R` for a Toffoli–K gate `g`, and
`K_[0,1,2,3]`, `CCZ` as themselves. -/
def psi (g : Sym1) : Matrix (Fin 8) (Fin 8) QSqrt2 :=
  match g with
  | .Kc | .CCZ => gateMat QSqrt2.invSqrt2 g
  | _ => reflR * gateMat QSqrt2.invSqrt2 g * reflR

/-! ## Evaluation -/

/-- `R` as a list matrix. -/
def reflL : LMat QSqrt2 :=
  (List.range 8).map fun i => (List.range 8).map fun j =>
    (if i = j then 1 else 0) - Quadratic.ofRat (1 / 4)

theorem toMat_reflL : ListMat.toMat 8 reflL = reflR := by decide +kernel

/-- `psi` as row operations: permutation gates commute with `R`. -/
def actPsi (g : Sym1) : Act QSqrt2 :=
  match g with
  | .Z0 | .Z1 | .Z2 | .CZ01 | .CZ02 | .CZ12 | .K01 | .K12 =>
    .dense (mul 8 reflL ((actOf g).apply 8 reflL))
  | _ => actOf g

theorem actPsi_toMat (g : Sym1) : (actPsi g).toMat 8 = psi g := by
  -- `R P R = P` for the permutation gates
  have perm : ∀ g : Sym1, mul 8 reflL ((actOf g).apply 8 reflL) = (actOf g).apply 8 (one 8) →
      reflR * gateMat QSqrt2.invSqrt2 g * reflR = gateMat QSqrt2.invSqrt2 g := by
    intro g h
    have := congrArg (ListMat.toMat 8) h
    rwa [toMat_mul, Act.toMat_apply, Act.toMat_apply, toMat_one, Matrix.mul_one, toMat_reflL,
      actOf_toMat, ← Matrix.mul_assoc] at this
  have dense : ∀ g : Sym1, (Act.dense (mul 8 reflL ((actOf g).apply 8 reflL))).toMat 8 =
      reflR * gateMat QSqrt2.invSqrt2 g * reflR := by
    intro g
    show ListMat.toMat 8 _ = _
    rw [toMat_mul, Act.toMat_apply, toMat_reflL, actOf_toMat, Matrix.mul_assoc]
  cases g
  case Z0 | Z1 | Z2 | CZ01 | CZ02 | CZ12 | K01 | K12 => exact dense _
  case Kc => exact actOf_toMat Kc
  case CCZ => exact actOf_toMat CCZ
  case X0 => exact (actOf_toMat X0).trans (perm X0 (by decide +kernel)).symm
  case X1 => exact (actOf_toMat X1).trans (perm X1 (by decide +kernel)).symm
  case X2 => exact (actOf_toMat X2).trans (perm X2 (by decide +kernel)).symm
  case CX01 => exact (actOf_toMat CX01).trans (perm CX01 (by decide +kernel)).symm
  case CX02 => exact (actOf_toMat CX02).trans (perm CX02 (by decide +kernel)).symm
  case CX10 => exact (actOf_toMat CX10).trans (perm CX10 (by decide +kernel)).symm
  case CX12 => exact (actOf_toMat CX12).trans (perm CX12 (by decide +kernel)).symm
  case CX20 => exact (actOf_toMat CX20).trans (perm CX20 (by decide +kernel)).symm
  case CX21 => exact (actOf_toMat CX21).trans (perm CX21 (by decide +kernel)).symm
  case CCX01 => exact (actOf_toMat CCX01).trans (perm CCX01 (by decide +kernel)).symm
  case CCX02 => exact (actOf_toMat CCX02).trans (perm CCX02 (by decide +kernel)).symm
  case CCX12 => exact (actOf_toMat CCX12).trans (perm CCX12 (by decide +kernel)).symm
  case S01 => exact (actOf_toMat S01).trans (perm S01 (by decide +kernel)).symm
  case S02 => exact (actOf_toMat S02).trans (perm S02 (by decide +kernel)).symm
  case S12 => exact (actOf_toMat S12).trans (perm S12 (by decide +kernel)).symm

/-- The matrix of a word under `psi`, over `ℚ(√2)`. -/
def evalPsi (l : List Sym1) : LMat QSqrt2 := l.foldr (fun g M => (actPsi g).apply 8 M) (one 8)

theorem lift_psi (l : List Sym1) :
    FreeMonoid.lift psi (w l) = ListMat.toMat 8 (evalPsi l) := by
  induction l with
  | nil => exact (toMat_one 8).symm
  | cons g l ih =>
    rw [show w (g :: l) = FreeMonoid.of g * w l from FreeMonoid.ofList_cons g l, map_mul,
      FreeMonoid.lift_eval_of, ih, show evalPsi (g :: l) = (actPsi g).apply 8 (evalPsi l) from rfl,
      Act.toMat_apply, actPsi_toMat]

theorem psi_eq_of_eval {l l' : List Sym1} (h : evalPsi l = evalPsi l') :
    FreeMonoid.lift psi (w l) = FreeMonoid.lift psi (w l') := by
  rw [lift_psi, lift_psi, h]

set_option maxHeartbeats 0 in
/-- Every relation of Figures 4 and 7 holds under `psi`. -/
theorem psi_sound : ∀ ⦃u v : Word Sym1⦄, Fig47 u v → FreeMonoid.lift psi u = FreeMonoid.lift psi v := by
  intro u v h
  rcases h with h | h
  · cases h <;> (apply psi_eq_of_eval; decide +kernel)
  · cases h <;> (apply psi_eq_of_eval; decide +kernel)

/-- `(r_K)` fails under `psi`. -/
theorem psi_rK : FreeMonoid.lift psi (w [K12]) ≠ FreeMonoid.lift psi (w rKrhs) := by
  rw [lift_psi, lift_psi]
  intro h
  have h' : ListMat.toMat 8 (evalPsi [K12]) 0 0 = ListMat.toMat 8 (evalPsi rKrhs) 0 0 := by rw [h]
  revert h'
  decide +kernel

/-- `(r_K)` is not derivable from Figures 4 and 7. -/
theorem rK_independent' : ¬ Derivable Fig47 (w [K12]) (w rKrhs) :=
  fun h => psi_rK (derivable_sound psi_sound h)

end QCert.ToffoliHadamard
