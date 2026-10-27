/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): Li–Ross–Selinger's generators as circuits

Each generator `(−1)_[a]`, `X_[a,b]`, `K_[a,b,c,d]` of `𝒢₈` is the circuit
of the abbreviations of Sections 5.3 and 5.6 (`negw`, `xab`, `kw`): their
matrices agree, decided by the kernel for all 106 generators.  So
generation of `O₈(ℤ[1/2])` by `𝒢₈` (Li–Ross–Selinger, Theorem 3.5) gives
generation by `Σ₁` (`surjective1_of`).
-/
import QCert.ToffoliHadamard.Soundness
import QCert.LiRossSelinger.Local
import QCert.LiRossSelinger.Generation

namespace QCert.ToffoliHadamard

open Matrix QCert.ListMat

/-- A generator of `𝒢₈` as a circuit over `Σ₁`. -/
def enc : LiRossSelinger.Gen 8 → List Sym1
  | .neg a => negw a
  | .x a b _ => xab a b
  | .k a b c d _ _ _ => kw a b c d

/-- The local list matrix of a generator of `𝒢₈`, over `ℚ`. -/
def locL : LiRossSelinger.Gen 8 → LMat ℚ
  | .neg a => level 8 [a] LiRossSelinger.lNeg
  | .x a b _ => level 8 [a, b] LiRossSelinger.lX
  | .k a b c d _ _ _ => level 8 [a, b, c, d] LiRossSelinger.lK

/-- `ℚ ⊆ ℚ(√2)`. -/
def ratToQ2 : ℚ →+* QSqrt2 where
  toFun r := ⟨r, 0⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp

theorem toR_comp_ratToQ2 : QSqrt2.toR.comp ratToQ2 = Rat.castHom ℝ := by
  ext r; simp [ratToQ2, QSqrt2.toR]

theorem levelMat_id {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : levelMat id M = M := by
  have : embedMat (R := ℝ) (id : Fin n → Fin n) = 1 := by
    ext i j; simp [embedMat, one_apply, eq_comm]
  simp [levelMat, this]

theorem genMat_eq_locL (g : LiRossSelinger.Gen 8) :
    LiRossSelinger.genMat g = (ListMat.toMat 8 (locL g)).map (Rat.castHom ℝ) := by
  cases g with
  | neg a =>
    rw [LiRossSelinger.genMat_neg_loc id a a.2 a rfl, LiRossSelinger.Loc.glob, levelMat_id]; rfl
  | x a b h =>
    rw [LiRossSelinger.genMat_x_loc id a b a.2 b.2 (Fin.val_ne_of_ne (ne_of_lt h)) a b h rfl rfl,
      LiRossSelinger.Loc.glob, levelMat_id]; rfl
  | k a b c d h₁ h₂ h₃ =>
    rw [LiRossSelinger.genMat_k_loc id a b c d a.2 b.2 c.2 d.2 (by
        simp only [Fin.lt_def] at h₁ h₂ h₃
        simp [List.nodup_cons]; omega) a b c d h₁ h₂ h₃ rfl rfl rfl rfl,
      LiRossSelinger.Loc.glob, levelMat_id]; rfl

theorem evalW_negw : ∀ a : Fin 8, evalW (negw a) = ListMat.map ratToQ2 (level 8 [a] LiRossSelinger.lNeg) := by
  decide +kernel

theorem evalW_xab : ∀ a b : Fin 8, a < b →
    evalW (xab a b) = ListMat.map ratToQ2 (level 8 [a, b] LiRossSelinger.lX) := by
  decide +kernel

/-! ## `K_[a,b,c,d]` as conjugated `K_[0,1,2,3]` -/

theorem semW_append (l l' : List Sym1) :
    ((l ++ l').map semMat).prod = (l.map semMat).prod * (l'.map semMat).prod := by
  rw [List.map_append, List.prod_append]

theorem semW_eq (l : List Sym1) : (l.map semMat).prod = (ListMat.toMat 8 (evalW l)).map QSqrt2.toR := by
  rw [toMat_evalW]
  induction l with
  | nil => exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  | cons g l ih => rw [List.map_cons, List.prod_cons, ih, semMat_eq, List.map_cons,
      List.prod_cons, Matrix.map_mul]

theorem semW_locL {l : List Sym1} {g : LiRossSelinger.Gen 8}
    (h : evalW l = ListMat.map ratToQ2 (locL g)) : (l.map semMat).prod = LiRossSelinger.genMat g := by
  rw [semW_eq, h, toMat_map, Matrix.map_map, genMat_eq_locL]
  congr 1
  exact congrArg DFunLike.coe toR_comp_ratToQ2

theorem xab_mat (a b : Fin 8) (h : a < b) :
    ((xab a b).map semMat).prod = LiRossSelinger.genMat (.x a b h) :=
  semW_locL (g := .x a b h) (evalW_xab a b h)

theorem genX_mul (a b : Fin 8) (h : a < b) (A : Matrix (Fin 8) (Fin 8) ℝ) (r c : Fin 8) :
    (LiRossSelinger.genMat (.x a b h) * A) r c = A (Equiv.swap a b r) c := by
  rw [LiRossSelinger.genMat_x_mul, Equiv.swap_apply_def]
  split_ifs <;> rfl

theorem levelMat_transpose {m : ℕ} (f : Fin m → Fin 8) (M : Matrix (Fin m) (Fin m) ℝ) :
    (levelMat f M)ᵀ = levelMat f Mᵀ := by
  simp only [levelMat, transpose_add, transpose_one, transpose_mul, transpose_transpose,
    transpose_sub, Matrix.mul_assoc]

theorem genX_transpose (a b : Fin 8) (h : a < b) :
    (LiRossSelinger.genMat (.x a b h))ᵀ = LiRossSelinger.genMat (.x a b h) := by
  have : LiRossSelinger.matXᵀ = LiRossSelinger.matX := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [LiRossSelinger.matX]
  simp only [LiRossSelinger.genMat, levelMat_transpose, this]

theorem mul_genX (a b : Fin 8) (h : a < b) (A : Matrix (Fin 8) (Fin 8) ℝ) (r c : Fin 8) :
    (A * LiRossSelinger.genMat (.x a b h)) r c = A r (Equiv.swap a b c) := by
  have := genX_mul a b h Aᵀ c r
  rw [show LiRossSelinger.genMat (.x a b h) * Aᵀ = (A * LiRossSelinger.genMat (.x a b h))ᵀ by
    rw [transpose_mul, genX_transpose]] at this
  simpa using this

theorem levelMat_comp_perm {m : ℕ} (σ : Equiv.Perm (Fin 8)) (f : Fin m → Fin 8)
    (M : Matrix (Fin m) (Fin m) ℝ) :
    levelMat (σ ∘ f) M = (levelMat f M).submatrix σ.symm σ.symm := by
  have hE : embedMat (R := ℝ) (σ ∘ f) = (embedMat f).submatrix σ.symm id := by
    ext r k; simp only [embedMat, Function.comp, submatrix_apply, id]
    simp only [Equiv.apply_eq_iff_eq_symm_apply]
    split_ifs <;> rfl
  rw [levelMat, levelMat, hE]
  ext r c
  simp only [add_apply, submatrix_apply, mul_apply, transpose_apply, id, one_apply,
    EmbeddingLike.apply_eq_iff_eq]

theorem conj_genX {m : ℕ} (a b : Fin 8) (h : a < b) (f : Fin m → Fin 8) (M : Matrix (Fin m) (Fin m) ℝ) :
    LiRossSelinger.genMat (.x a b h) * levelMat f M * LiRossSelinger.genMat (.x a b h) =
      levelMat (Equiv.swap a b ∘ f) M := by
  rw [levelMat_comp_perm]
  ext r c
  rw [mul_genX, genX_mul, submatrix_apply, Equiv.symm_swap]

theorem conjX_mat {m : ℕ} (i j : Fin 8) (hij : i ≤ j) (u : List Sym1) (f : Fin m → Fin 8)
    (M : Matrix (Fin m) (Fin m) ℝ) (hu : (u.map semMat).prod = levelMat f M) :
    ((conjX i j u).map semMat).prod = levelMat (Equiv.swap i j ∘ f) M := by
  unfold conjX
  by_cases h : (i : ℕ) = j
  · have : i = j := Fin.ext h
    subst this
    rw [if_pos rfl, Equiv.swap_self, Equiv.coe_refl, Function.id_comp, hu]
  · rw [if_neg h, semW_append, semW_append, hu]
    have hlt : i < j := lt_of_le_of_ne hij (fun e => h (congrArg Fin.val e))
    rw [xab_mat i j hlt, conj_genX]

theorem matK_eq : ToffoliHadamard.matK (Real.sqrt 2)⁻¹ = LiRossSelinger.matK := by
  have h2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  ext i j; fin_cases i <;> fin_cases j <;> simp [ToffoliHadamard.matK, LiRossSelinger.matK, h2]

theorem swaps_eq (a b c d : Fin 8) (h₁ : a < b) (h₂ : b < c) (h₃ : c < d) :
    (Equiv.swap 0 a ∘ (Equiv.swap 1 b ∘ (Equiv.swap 2 c ∘ (Equiv.swap 3 d ∘
      (![0, 1, 2, 3] : Fin 4 → Fin 8))))) = ![a, b, c, d] := by
  simp only [Fin.lt_def] at h₁ h₂ h₃
  have n0d : (0 : Fin 8) ≠ d := by simp [Fin.ext_iff]; omega
  have n0c : (0 : Fin 8) ≠ c := by simp [Fin.ext_iff]; omega
  have n0b : (0 : Fin 8) ≠ b := by simp [Fin.ext_iff]; omega
  have n1d : (1 : Fin 8) ≠ d := by simp [Fin.ext_iff]; omega
  have n1c : (1 : Fin 8) ≠ c := by simp [Fin.ext_iff]; omega
  have n2d : (2 : Fin 8) ≠ d := by simp [Fin.ext_iff]; omega
  have nb0 : b ≠ 0 := Ne.symm n0b
  have nba : b ≠ a := by simp [Fin.ext_iff]; omega
  have nc1 : c ≠ 1 := Ne.symm n1c
  have ncb : c ≠ b := by simp [Fin.ext_iff]; omega
  have nc0 : c ≠ 0 := Ne.symm n0c
  have nca : c ≠ a := by simp [Fin.ext_iff]; omega
  have nd2 : d ≠ 2 := Ne.symm n2d
  have ndc : d ≠ c := by simp [Fin.ext_iff]; omega
  have nd1 : d ≠ 1 := Ne.symm n1d
  have ndb : d ≠ b := by simp [Fin.ext_iff]; omega
  have nd0 : d ≠ 0 := Ne.symm n0d
  have nda : d ≠ a := by simp [Fin.ext_iff]; omega
  funext p
  fin_cases p
  · simp [Equiv.swap_apply_of_ne_of_ne, n0d, n0c, n0b]
  · simp [Equiv.swap_apply_of_ne_of_ne, n1d, n1c, nb0, nba]
  · simp [Equiv.swap_apply_of_ne_of_ne, n2d, nc1, ncb, nc0, nca]
  · simp [Equiv.swap_apply_of_ne_of_ne, nd2, ndc, nd1, ndb, nd0, nda]

theorem kw_mat (a b c d : Fin 8) (h₁ : a < b) (h₂ : b < c) (h₃ : c < d) :
    ((kw a b c d).map semMat).prod = LiRossSelinger.genMat (.k a b c d h₁ h₂ h₃) := by
  have hc : (([Sym1.Kc]).map semMat).prod = levelMat ![0, 1, 2, 3] LiRossSelinger.matK := by
    simp [semMat, gateMat, matK_eq]
  have v₁ := Fin.lt_def.1 h₁
  have v₂ := Fin.lt_def.1 h₂
  have v₃ := Fin.lt_def.1 h₃
  have e := conjX_mat 0 a (Fin.zero_le _) _ _ _
    (conjX_mat 1 b (Fin.le_def.2 (by simp; omega)) _ _ _
      (conjX_mat 2 c (Fin.le_def.2 (by simp; omega)) _ _ _
        (conjX_mat 3 d (Fin.le_def.2 (by simp; omega)) _ _ _ hc)))
  rw [swaps_eq a b c d h₁ h₂ h₃] at e
  exact e

/-- The circuit of a generator has its matrix. -/
theorem enc_mat (g : LiRossSelinger.Gen 8) :
    ((enc g).map semMat).prod = LiRossSelinger.genMat g := by
  cases g with
  | neg a => exact semW_locL (g := .neg a) (evalW_negw a)
  | x a b h => exact xab_mat a b h
  | k a b c d h₁ h₂ h₃ => exact kw_mat a b c d h₁ h₂ h₃

/-- Words over `𝒢₈` as circuits. -/
def encW : Word (LiRossSelinger.Gen 8) →* Word Sym1 := FreeMonoid.lift fun g => w (enc g)

theorem sem1_encW (u : Word (LiRossSelinger.Gen 8)) :
    FreeMonoid.lift sem1 (encW u) = FreeMonoid.lift (LiRossSelinger.sem 8) u := by
  induction u using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g u ih =>
    rw [map_mul, map_mul, ih, map_mul, encW, FreeMonoid.lift_eval_of, FreeMonoid.lift_eval_of]
    congr 1
    apply Subtype.ext; apply Subtype.ext
    rw [sem1_word, enc_mat]; rfl

/-- Generation by `Σ₁`, from generation by `𝒢₈` (Li–Ross–Selinger, Theorem 3.5). -/
theorem surjective1_of : Function.Surjective (FreeMonoid.lift sem1) := by
  intro U
  obtain ⟨u, hu⟩ := LiRossSelinger.generation (n := 8) U
  exact ⟨encW u, (sem1_encW u).trans hu⟩

end QCert.ToffoliHadamard
