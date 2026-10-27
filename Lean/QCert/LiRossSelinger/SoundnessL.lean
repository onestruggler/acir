/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Li, Ross, Selinger (2021): soundness of Table 2 (Theorem 5.4)

Each relation of Table 2 lives on one or two blocks of `I ⊗ H`; moved there
by `blockMap` (`Blocks.lean`) it is an identity of `2 × 2` or `4 × 4`
matrices over `ℚ(√2)`, decided by the kernel.
-/
import QCert.LiRossSelinger.Soundness
import QCert.LiRossSelinger.Blocks
import QCert.Exact.Roots

namespace QCert.LiRossSelinger

open Matrix QCert.ListMat

/-! ## Local matrices over `ℚ(√2)` -/

/-- `−1` over `ℚ(√2)`. -/
def qNeg : LMat QSqrt2 := [[-1]]
/-- `X` over `ℚ(√2)`. -/
def qX : LMat QSqrt2 := [[0, 1], [1, 0]]
/-- `K` over `ℚ(√2)`. -/
def qK : LMat QSqrt2 :=
  let h : QSqrt2 := ⟨1 / 2, 0⟩
  [[h, h, h, h], [h, -h, h, -h], [h, h, -h, -h], [h, -h, -h, h]]
/-- `I_k ⊗ H` over `ℚ(√2)` (`1/√2 = ⟨0, 1/2⟩`). -/
def qIH (k : ℕ) : LMat QSqrt2 :=
  (List.range (k * 2)).map fun i => (List.range (k * 2)).map fun j =>
    if i / 2 = j / 2 then (if i % 2 = 1 ∧ j % 2 = 1 then ⟨0, -1 / 2⟩ else ⟨0, 1 / 2⟩) else 0

theorem toR_mk (a b : ℚ) : QSqrt2.toR ⟨a, b⟩ = (a : ℝ) + b * Real.sqrt 2 := by
  simp [QSqrt2.toR, Quadratic.lift_apply]

theorem inv_sqrt2_eq : (Real.sqrt 2)⁻¹ = 2⁻¹ * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp; linarith

theorem toR_s : QSqrt2.toR ⟨0, 1 / 2⟩ = (Real.sqrt 2)⁻¹ := QSqrt2.toR_invSqrt2

theorem toR_ms : QSqrt2.toR ⟨0, -1 / 2⟩ = -(Real.sqrt 2)⁻¹ := by
  rw [← toR_s, ← map_neg]; congr 1; ext <;> norm_num

theorem matNeg_q : matNeg = (ListMat.toMat 1 qNeg).map QSqrt2.toR := by
  ext i j; fin_cases i; fin_cases j; simp [matNeg, qNeg, ListMat.toMat, toR_mk]

theorem matX_q : matX = (ListMat.toMat 2 qX).map QSqrt2.toR := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matX, qX, ListMat.toMat, toR_mk]

theorem matK_q : matK = (ListMat.toMat 4 qK).map QSqrt2.toR := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matK, qK, ListMat.toMat, toR_mk]

theorem matIH_q (k : ℕ) : matIH k = (ListMat.toMat (k * 2) (qIH k)).map QSqrt2.toR := by
  ext i j
  rw [matIH_apply, map_apply]
  simp only [ListMat.toMat, qIH, getD_range_map _ _ _ i.2, getD_range_map _ _ _ j.2]
  have hb : ∀ t : Fin (k * 2), ((bp t).1 : ℕ) = (t : ℕ) / 2 := fun t => by simp [bp]
  have hp : ∀ t : Fin (k * 2), ((bp t).2 : ℕ) = (t : ℕ) % 2 := fun t => by simp [bp]
  have e : (bp i).1 = (bp j).1 ↔ (i : ℕ) / 2 = (j : ℕ) / 2 := by rw [Fin.ext_iff, hb, hb]
  by_cases h : (i : ℕ) / 2 = (j : ℕ) / 2
  · rw [if_pos (e.2 h), if_pos h]
    have hi := hp i; have hj := hp j
    have hi2 : (i : ℕ) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hj2 : (j : ℕ) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    generalize (bp i).2 = p at hi
    generalize (bp j).2 = q at hj
    fin_cases p <;> fin_cases q <;> simp at hi hj <;>
      simp [matH, ← hi, ← hj, toR_mk, inv_sqrt2_eq] <;> ring
  · rw [if_neg (fun h' => h (e.1 h')), if_neg h, map_zero]

/-! ## Words over `𝓕ₙ` -/

/-- The real matrix of a generator of `𝓕ₙ`. -/
noncomputable def semLMat {m : ℕ} : GenL m → Matrix (Fin (m * 2)) (Fin (m * 2)) ℝ
  | .base g => genMat g
  | .ih => matIH m

theorem semL_word {m : ℕ} (u : Word (GenL m)) :
    (((FreeMonoid.lift (semL m) u : L (m * 2)) : unitaryGroup (Fin (m * 2)) ℝ) :
      Matrix (Fin (m * 2)) (Fin (m * 2)) ℝ) = (u.toList.map semLMat).prod := by
  induction u using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g u ih =>
    rw [map_mul, Subgroup.coe_mul, Submonoid.coe_mul, ih, FreeMonoid.lift_eval_of,
      FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append, List.map_cons,
      List.prod_cons]
    cases g <;> rfl

theorem semL_toL {m : ℕ} (u : Word (Gen (m * 2))) :
    (((FreeMonoid.lift (semL m) (toL u) : L (m * 2)) : unitaryGroup (Fin (m * 2)) ℝ) :
      Matrix (Fin (m * 2)) (Fin (m * 2)) ℝ) =
    (((FreeMonoid.lift (sem (m * 2)) u : O_ZHalf (m * 2)) : unitaryGroup (Fin (m * 2)) ℝ) :
      Matrix (Fin (m * 2)) (Fin (m * 2)) ℝ) := by
  rw [semL_word, sem_word, FreeMonoid.toList_map, List.map_map]; rfl

/-! ## Blocks -/

theorem blockMap_val {m k : ℕ} (β : Fin k → Fin m) (t : Fin (k * 2)) :
    (blockMap β t : ℕ) = (t : ℕ) % 2 + 2 * (β (bp t).1 : ℕ) := by
  simp [blockMap, finProdFinEquiv]

theorem bp_fst_val {k : ℕ} (t : Fin (k * 2)) : ((bp t).1 : ℕ) = (t : ℕ) / 2 := by simp [bp]

/-- Moving a level matrix on local indices of a block-aligned map. -/
theorem levelMat_blockMap {m k j : ℕ} (β : Fin k → Fin m) (g : Fin j → Fin (k * 2))
    (hg : Function.Injective g) (idx : List ℕ) (hidx : idx = List.ofFn fun t => (g t : ℕ))
    (f : Fin j → Fin (m * 2)) (hf : f = blockMap β ∘ g) (M : LMat QSqrt2) :
    levelMat f ((ListMat.toMat j M).map QSqrt2.toR) =
      levelMat (blockMap β) ((ListMat.toMat (k * 2) (level (k * 2) idx M)).map QSqrt2.toR) := by
  rw [hidx, toMat_level g hg, levelMat_map, ← levelMat_comp, hf]

theorem matIH_sq (m : ℕ) : matIH m * matIH m = 1 := by
  rw [matIH, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul, matH_mul_matH,
    one_kronecker_one, submatrix_one_equiv]

theorem levelMat_prod_list {m j : ℕ} {F : Fin j → Fin m} (hF : Function.Injective F)
    (l : List (LMat QSqrt2)) :
    levelMat F ((ListMat.toMat j (ListMat.prod j l)).map QSqrt2.toR) =
      (l.map fun B => levelMat F ((ListMat.toMat j B).map QSqrt2.toR)).prod := by
  induction l with
  | nil =>
    rw [show ListMat.prod j [] = one j from rfl, toMat_one,
      Matrix.map_one _ (map_zero _) (map_one _), levelMat_one]; rfl
  | cons B l ih =>
    rw [show ListMat.prod j (B :: l) = mul j B (ListMat.prod j l) from rfl, toMat_mul,
      Matrix.map_mul, ← levelMat_mul hF, ih, List.map_cons, List.prod_cons]

/-- A Table 2 relation on the blocks `β`: decided on local list matrices. -/
theorem conj_local {m k : ℕ} {β : Fin k → Fin m} (hβ : Function.Injective β)
    (A : LMat QSqrt2) (l : List (LMat QSqrt2))
    (h : mul (k * 2) (mul (k * 2) (qIH k) A) (qIH k) = ListMat.prod (k * 2) l) :
    matIH m * levelMat (blockMap β) ((ListMat.toMat (k * 2) A).map QSqrt2.toR) * matIH m =
      (l.map fun B => levelMat (blockMap β) ((ListMat.toMat (k * 2) B).map QSqrt2.toR)).prod := by
  rw [ih_conj_levelMat hβ, matIH_q k, ← Matrix.map_mul, ← Matrix.map_mul, ← toMat_mul, ← toMat_mul,
    h, levelMat_prod_list (blockMap_injective hβ)]

theorem blockMap_eq {m : ℕ} {k : ℕ} (β : Fin k → Fin m) (f : Fin (k * 2) → Fin (m * 2))
    (h : ∀ t : Fin (k * 2), (f t : ℕ) = (t : ℕ) % 2 + 2 * (β (bp t).1 : ℕ)) : f = blockMap β := by
  funext t; apply Fin.ext; rw [h, blockMap_val]

theorem bp_fst_zero (t : Fin (1 * 2)) : (bp t).1 = (0 : Fin 1) := Subsingleton.elim _ _

theorem matIH_mul_assoc {m : ℕ} (A B : Matrix (Fin (m * 2)) (Fin (m * 2)) ℝ) :
    matIH m * (A * (matIH m * 1)) = B ↔ matIH m * A * matIH m = B := by
  rw [Matrix.mul_one, Matrix.mul_assoc]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- Theorem 5.4: the relations of Tables 1 and 2 are sound in `Lₙ`. -/
theorem soundL {m : ℕ} : ∀ ⦃u v : Word (GenL m)⦄, Table12 m u v →
    FreeMonoid.lift (semL m) u = FreeMonoid.lift (semL m) v := by
  intro u v h
  apply Subtype.ext; apply Subtype.ext
  cases h with
  | table1 r => rw [semL_toL, semL_toL, sound r]
  | r7a =>
    rw [semL_word, semL_word]
    simp only [IH, FreeMonoid.toList_mul, FreeMonoid.toList_of, FreeMonoid.toList_one,
      List.singleton_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      semLMat, Matrix.mul_one, matIH_sq]
  | r7b h =>
    rw [semL_word, semL_word]
    simp only [IH, toL, FreeMonoid.map_of, FreeMonoid.toList_mul, FreeMonoid.toList_of,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, semLMat, Matrix.mul_one, map_mul]
    rw [← Matrix.mul_assoc]
    let β : Fin 2 → Fin m := ![⟨0, by omega⟩, ⟨1, by omega⟩]
    have hβ : Function.Injective β := by
      intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [β, Fin.ext_iff]
    have hK : genMat (Gen.k (n := m * 2) ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, h⟩
        (by simp [Fin.lt_def]) (by simp [Fin.lt_def]) (by simp [Fin.lt_def])) =
        levelMat (blockMap β) ((ListMat.toMat (2 * 2) qK).map QSqrt2.toR) := by
      rw [genMat, matK_q]
      congr 1
      exact blockMap_eq (k := 2) β _ (fun t => by fin_cases t <;> rfl)
    rw [hK, conj_local hβ qK [qK] (by decide +kernel)]
    simp
  | r7c h =>
    rw [semL_word, semL_word]
    simp only [IH, toL, FreeMonoid.map_of, FreeMonoid.toList_mul, FreeMonoid.toList_of,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, semLMat, Matrix.mul_one, map_mul]
    rw [← Matrix.mul_assoc]
    let β : Fin 1 → Fin m := ![⟨0, by omega⟩]
    have hβ : Function.Injective β := fun i j _ => Subsingleton.elim i j
    have hN : genMat (Gen.neg (n := m * 2) ⟨0, by omega⟩) =
        levelMat (blockMap β) ((ListMat.toMat (1 * 2) (level (1 * 2) [0] qNeg)).map QSqrt2.toR) := by
      rw [genMat, matNeg_q]
      exact levelMat_blockMap β ![0] (fun i j _ => Subsingleton.elim i j) [0] (by simp) _
        (funext fun t => by fin_cases t; rfl) qNeg
    have hX : genMat (Gen.x (n := m * 2) ⟨0, by omega⟩ ⟨1, h⟩ (by simp [Fin.lt_def])) =
        levelMat (blockMap β) ((ListMat.toMat (1 * 2) qX).map QSqrt2.toR) := by
      rw [genMat, matX_q]; congr 1
      exact blockMap_eq (k := 1) β _ (fun t => by fin_cases t <;> rfl)
    rw [hN, hX, conj_local hβ _ [level (1 * 2) [0] qNeg, qX, level (1 * 2) [0] qNeg]
      (by decide +kernel)]
    simp
  | r7d_even a ha h =>
    rw [semL_word, semL_word]
    simp only [IH, toL, FreeMonoid.map_of, FreeMonoid.toList_mul, FreeMonoid.toList_of,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, semLMat, Matrix.mul_one, map_mul]
    rw [← Matrix.mul_assoc]
    let β : Fin 1 → Fin m := ![⟨a / 2, by omega⟩]
    have hβ : Function.Injective β := fun i j _ => Subsingleton.elim i j
    have hX : genMat (Gen.x (n := m * 2) ⟨a, by omega⟩ ⟨a + 1, h⟩ (by simp [Fin.lt_def])) =
        levelMat (blockMap β) ((ListMat.toMat (1 * 2) qX).map QSqrt2.toR) := by
      rw [genMat, matX_q]; congr 1
      exact blockMap_eq (k := 1) β _ (fun t => by
        rw [bp_fst_zero]; fin_cases t <;> simp [β] <;> omega)
    have hN : genMat (Gen.neg (n := m * 2) ⟨a + 1, h⟩) =
        levelMat (blockMap β) ((ListMat.toMat (1 * 2) (level (1 * 2) [1] qNeg)).map QSqrt2.toR) := by
      rw [genMat, matNeg_q]
      exact levelMat_blockMap β ![1] (fun i j _ => Subsingleton.elim i j) [1] (by simp) _
        (funext fun t => by
          fin_cases t; apply Fin.ext
          rw [Function.comp_apply, blockMap_val, bp_fst_zero]; simp [β]; omega) qNeg
    rw [hX, hN, conj_local hβ _ [level (1 * 2) [1] qNeg] (by decide +kernel)]
    simp
  | r7d_odd a ha h =>
    rw [semL_word, semL_word]
    simp only [IH, toL, FreeMonoid.map_of, FreeMonoid.toList_mul, FreeMonoid.toList_of,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, semLMat, Matrix.mul_one, map_mul]
    rw [← Matrix.mul_assoc]
    let β : Fin 2 → Fin m := ![⟨(a - 1) / 2, by omega⟩, ⟨(a + 1) / 2, by omega⟩]
    have hβ : Function.Injective β := by
      intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [β, Fin.ext_iff] <;> omega
    have hbp : ∀ t : Fin (2 * 2), ((bp t).1 : ℕ) = (t : ℕ) / 2 := bp_fst_val
    have hβv : ∀ t : Fin (2 * 2), (β (bp t).1 : ℕ) = if (t : ℕ) / 2 = 0 then (a - 1) / 2 else
        (a + 1) / 2 := by
      intro t; fin_cases t <;> rfl
    have hX : genMat (Gen.x (n := m * 2) ⟨a, by omega⟩ ⟨a + 1, by omega⟩ (by simp [Fin.lt_def])) =
        levelMat (blockMap β)
          ((ListMat.toMat (2 * 2) (level (2 * 2) [1, 2] qX)).map QSqrt2.toR) := by
      rw [genMat, matX_q]
      refine levelMat_blockMap β ![1, 2] (by
        intro i j hij; fin_cases i <;> fin_cases j <;> simp_all) [1, 2] (by simp) _
        (funext fun t => ?_) qX
      fin_cases t <;> apply Fin.ext <;> rw [Function.comp_apply, blockMap_val, hβv] <;>
        simp <;> omega
    have hK : genMat (Gen.k (n := m * 2) ⟨a - 1, by omega⟩ ⟨a, by omega⟩ ⟨a + 1, by omega⟩
        ⟨a + 2, h⟩ (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def])
        (by simp [Fin.lt_def])) =
        levelMat (blockMap β) ((ListMat.toMat (2 * 2) qK).map QSqrt2.toR) := by
      rw [genMat, matK_q]; congr 1
      exact blockMap_eq (k := 2) β _ (fun t => by
        rw [hβv]; fin_cases t <;> simp <;> omega)
    rw [hX, hK, conj_local hβ _ [level (2 * 2) [1, 2] qX, qK] (by decide +kernel)]
    simp

/-- Every generator of `𝓕ₙ` is an involution: Tables 1 and 2 are grouplike. -/
theorem grouplikeL {m : ℕ} : Grouplike (Table12 m) := by
  intro g
  refine ⟨FreeMonoid.of g, Derivable.of ?_⟩
  cases g with
  | ih => exact Table12.r7a
  | base g =>
    have := Table12.table1 (m := m) (show Table1 (m * 2) (FreeMonoid.of g * FreeMonoid.of g) 1 from by
      cases g with
      | neg a => exact Table1.r1b a
      | x a b h => exact Table1.r1a a b h
      | k a b c d h₁ h₂ h₃ => exact Table1.r1c a b c d h₁ h₂ h₃)
    simpa using this

end QCert.LiRossSelinger
