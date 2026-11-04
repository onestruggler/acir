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

`psi` is evaluated as scaled integer matrices (`Eval.lean`): the
permutation gates commute with `R` and keep their row operations, and for
the others `16 R D R` and `32 R K R` are integer matrices (`psiL`, checked
against the product by `decide`).
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

/-- `4 R = 4 I − J` as an integer list matrix. -/
def reflZ : LMat ℤ :=
  (List.range 8).map fun i => (List.range 8).map fun j => if i = j then 3 else -1

theorem reflR_eq : reflR = gateQ 4 (.dense reflZ) := by decide +kernel

theorem reflZ_wf : (Act.dense reflZ).WF 8 := by decide

/-- The gates that `R` does not commute with: `Z`, `CZ` and `K` gates. -/
def psiDense : Sym1 → Bool
  | .Z0 | .Z1 | .Z2 | .CZ01 | .CZ02 | .CZ12 | .K01 | .K12 => true
  | _ => false

/-- `16 R D R` for the sign gates `D` and `32 R K R` for `K₀₁`, `K₁₂`. -/
def psiL : Sym1 → LMat ℤ
  | .Z0 => [[8, -8, -8, -8, 0, 0, 0, 0], [-8, 8, -8, -8, 0, 0, 0, 0], [-8, -8, 8, -8, 0, 0, 0, 0],
    [-8, -8, -8, 8, 0, 0, 0, 0], [0, 0, 0, 0, -8, 8, 8, 8], [0, 0, 0, 0, 8, -8, 8, 8],
    [0, 0, 0, 0, 8, 8, -8, 8], [0, 0, 0, 0, 8, 8, 8, -8]]
  | .Z1 => [[8, -8, 0, 0, -8, -8, 0, 0], [-8, 8, 0, 0, -8, -8, 0, 0], [0, 0, -8, 8, 0, 0, 8, 8],
    [0, 0, 8, -8, 0, 0, 8, 8], [-8, -8, 0, 0, 8, -8, 0, 0], [-8, -8, 0, 0, -8, 8, 0, 0],
    [0, 0, 8, 8, 0, 0, -8, 8], [0, 0, 8, 8, 0, 0, 8, -8]]
  | .Z2 => [[8, 0, -8, 0, -8, 0, -8, 0], [0, -8, 0, 8, 0, 8, 0, 8], [-8, 0, 8, 0, -8, 0, -8, 0],
    [0, 8, 0, -8, 0, 8, 0, 8], [-8, 0, -8, 0, 8, 0, -8, 0], [0, 8, 0, 8, 0, -8, 0, 8],
    [-8, 0, -8, 0, -8, 0, 8, 0], [0, 8, 0, 8, 0, 8, 0, -8]]
  | .CZ01 => [[12, -4, -4, -4, -4, -4, 4, 4], [-4, 12, -4, -4, -4, -4, 4, 4],
    [-4, -4, 12, -4, -4, -4, 4, 4], [-4, -4, -4, 12, -4, -4, 4, 4], [-4, -4, -4, -4, 12, -4, 4, 4],
    [-4, -4, -4, -4, -4, 12, 4, 4], [4, 4, 4, 4, 4, 4, -4, 12], [4, 4, 4, 4, 4, 4, 12, -4]]
  | .CZ02 => [[12, -4, -4, -4, -4, 4, -4, 4], [-4, 12, -4, -4, -4, 4, -4, 4],
    [-4, -4, 12, -4, -4, 4, -4, 4], [-4, -4, -4, 12, -4, 4, -4, 4], [-4, -4, -4, -4, 12, 4, -4, 4],
    [4, 4, 4, 4, 4, -4, 4, 12], [-4, -4, -4, -4, -4, 4, 12, 4], [4, 4, 4, 4, 4, 12, 4, -4]]
  | .CZ12 => [[12, -4, -4, 4, -4, -4, -4, 4], [-4, 12, -4, 4, -4, -4, -4, 4],
    [-4, -4, 12, 4, -4, -4, -4, 4], [4, 4, 4, -4, 4, 4, 4, 12], [-4, -4, -4, 4, 12, -4, -4, 4],
    [-4, -4, -4, 4, -4, 12, -4, 4], [-4, -4, -4, 4, -4, -4, 12, 4], [4, 4, 4, 12, 4, 4, 4, -4]]
  | .K01 => [[-8, -24, 8, -8, 8, -8, 8, -8], [-24, -8, -8, 8, -8, 8, -8, 8],
    [8, -8, -8, 8, 24, 8, -8, 8], [-8, 8, 8, -8, 8, 24, 8, -8], [8, -8, 24, 8, -8, 8, -8, 8],
    [-8, 8, 8, 24, 8, -8, 8, -8], [8, -8, -8, 8, -8, 8, 24, 8], [-8, 8, 8, -8, 8, -8, 8, 24]]
  | .K12 => [[-8, 8, 8, 8, -24, -8, -8, -8], [8, -8, 24, -8, -8, 8, 8, 8],
    [8, 24, -8, -8, -8, 8, 8, 8], [8, -8, -8, 24, -8, 8, 8, 8], [-24, -8, -8, -8, -8, 8, 8, 8],
    [-8, 8, 8, 8, 8, -8, 24, -8], [-8, 8, 8, 8, 8, 24, -8, -8], [-8, 8, 8, 8, 8, -8, -8, 24]]
  | _ => []

/-- `psi` as integer row operations. -/
def actPsiZ (g : Sym1) : Act ℤ := bif psiDense g then .dense (psiL g) else actZ g

/-- The scale of `psi g`: conjugation by `R = (1/√2)^4 (4 R)` adds `8`. -/
def scPsi (g : Sym1) : ℕ := bif psiDense g then 8 + scZ g else scZ g

theorem actPsiZ_wf (g : Sym1) : (actPsiZ g).WF 8 := by cases g <;> decide

/-- `psiL` is the conjugate `4 R · ⟦g⟧ · 4 R`. -/
theorem psiL_eq : ∀ g, psiDense g = true → psiL g = mulF reflZ ((actZ g).applyF reflZ) := by
  intro g; cases g <;> decide +kernel

/-- The permutation gates commute with `R`: `4 R · P · 4 R = 16 P`. -/
theorem perm_conj : ∀ g, psiDense g = false → g ≠ Kc → g ≠ CCZ →
    mulF reflZ ((actZ g).applyF reflZ) = scaleM 16 ((actZ g).applyF (one 8)) := by
  intro g; cases g <;> decide +kernel

theorem gateQ_conj (k : ℕ) {a : Act ℤ} (hwf : a.WF 8) :
    gateQ 4 (.dense reflZ) * gateQ k a * gateQ 4 (.dense reflZ) =
      gateQ (8 + k) (.dense (mulF reflZ (a.applyF reflZ))) := by
  simp only [gateQ, Act.toMat, toMat_mulF 8 _ _ reflZ_wf, Act.toMat_applyF 8 hwf, Matrix.map_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  congr 1
  ring

theorem gateQ_scale16 (k : ℕ) (M : LMat ℤ) :
    gateQ (8 + k) (.dense (scaleM 16 M)) = gateQ k (.dense M) := by
  simp only [gateQ, Act.toMat]
  rw [show (16 : ℤ) = ((16 : ℕ) : ℤ) by rfl, toMat_scaleM_map, smul_smul]
  congr 1
  have h : (2 : QSqrt2) * QSqrt2.invSqrt2 ^ 2 = 1 := invSqrt2_sq
  rw [Int.cast_natCast, Nat.cast_ofNat, pow_add, mul_right_comm, show (16 : QSqrt2) = 2 ^ 4 by norm_num,
    show QSqrt2.invSqrt2 ^ 8 = (QSqrt2.invSqrt2 ^ 2) ^ 4 by rw [← pow_mul], ← mul_pow,
    mul_comm (QSqrt2.invSqrt2 ^ 2) 2, h, one_pow, one_mul]

theorem gateQ_applyF_one (k : ℕ) {a : Act ℤ} (hwf : a.WF 8) :
    gateQ k (.dense (a.applyF (one 8))) = gateQ k a := by
  simp only [gateQ, Act.toMat, Act.toMat_applyF 8 hwf, toMat_one, Matrix.mul_one]

theorem psi_eq (g : Sym1) : psi g = gateQ (scPsi g) (actPsiZ g) := by
  have dense : ∀ g, psiDense g = true →
      reflR * gateMat QSqrt2.invSqrt2 g * reflR = gateQ (scPsi g) (actPsiZ g) := by
    intro g hg
    rw [reflR_eq, gateMat_eq_actZ, gateQ_conj _ (actZ_wf g), ← psiL_eq g hg]
    simp [scPsi, actPsiZ, hg]
  have perm : ∀ g, psiDense g = false → g ≠ Kc → g ≠ CCZ →
      reflR * gateMat QSqrt2.invSqrt2 g * reflR = gateQ (scPsi g) (actPsiZ g) := by
    intro g hg h1 h2
    rw [reflR_eq, gateMat_eq_actZ, gateQ_conj _ (actZ_wf g), perm_conj g hg h1 h2, gateQ_scale16,
      gateQ_applyF_one _ (actZ_wf g)]
    simp [scPsi, actPsiZ, hg]
  cases g
  case Z0 | Z1 | Z2 | CZ01 | CZ02 | CZ12 | K01 | K12 => exact dense _ rfl
  case Kc => exact gateMat_eq_actZ Kc
  case CCZ => exact gateMat_eq_actZ CCZ
  all_goals exact perm _ rfl (by decide) (by decide)

/-- The matrix of a word under `psi`, as a scaled integer matrix. -/
def evalPsi : List Sym1 → SMat := evalS scPsi actPsiZ

theorem lift_psi (l : List Sym1) : FreeMonoid.lift psi (w l) = (l.map psi).prod := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [show w (g :: l) = FreeMonoid.of g * w l from FreeMonoid.ofList_cons g l, map_mul,
      FreeMonoid.lift_eval_of, ih, List.map_cons, List.prod_cons]

theorem psi_eq_of_eval {l l' : List Sym1} (h : eqS 2 (evalPsi l) (evalPsi l') = true) :
    FreeMonoid.lift psi (w l) = FreeMonoid.lift psi (w l') := by
  rw [lift_psi, lift_psi]
  exact prodQ_eq_of_eqS scPsi actPsiZ psi actPsiZ_wf psi_eq h

set_option maxHeartbeats 0 in
/-- Every relation of Figures 4 and 7 holds under `psi`. -/
theorem psi_sound : ∀ ⦃u v : Word Sym1⦄, Fig47 u v →
    FreeMonoid.lift psi u = FreeMonoid.lift psi v := by
  intro u v h
  rcases h with h | h
  · cases h <;> (apply psi_eq_of_eval; decide +kernel)
  · cases h <;> (apply psi_eq_of_eval; decide +kernel)

/-- `(r_K)` fails under `psi`. -/
theorem psi_rK : FreeMonoid.lift psi (w [K12]) ≠ FreeMonoid.lift psi (w rKrhs) := by
  rw [lift_psi, lift_psi, toMatS_evalS scPsi actPsiZ psi actPsiZ_wf psi_eq,
    toMatS_evalS scPsi actPsiZ psi actPsiZ_wf psi_eq]
  intro h
  have h' : (evalS scPsi actPsiZ [K12]).toMatS 8 QSqrt2.invSqrt2 0 0 =
      (evalS scPsi actPsiZ rKrhs).toMatS 8 QSqrt2.invSqrt2 0 0 := by rw [h]
  revert h'
  decide +kernel

/-- `(r_K)` is not derivable from Figures 4 and 7. -/
theorem rK_independent' : ¬ Derivable Fig47 (w [K12]) (w rKrhs) :=
  fun h => psi_rK (derivable_sound psi_sound h)

end QCert.ToffoliHadamard
