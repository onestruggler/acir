/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Exact checks of identities between words of level matrices

An identity between words in the generators at symbolic indices `a, b, …`
of dimension `n` is the image, under an injective `f : Fin m → Fin n`
(the indices), of the same identity in dimension `m` at the indices
`0, 1, …`: level matrices compose (`levelMat_levelMat`) and `levelMat f` is
multiplicative for injective `f` (`levelMat_mul`).  In dimension `m` the
identity is between explicit matrices; scaling every generator by `√2`
makes them matrices over `ℤ√2` (`LGen.smat`), where `decide +kernel`
decides it, and `ℤ√2 →+* ℝ` carries it back (`lprod_eq_of_check`).

`LGen m` is a generator on any indices of `Fin m`, ordered or not, and
`LGen.mat s` its matrix with `s` standing for `1/√2`.
-/
import QCert.HadamardPi.Semantics
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Real.Irrational

namespace QCert.HadamardPi

open Matrix

section Level

variable {R S : Type*} [CommRing R] [CommRing S] {k m n : ℕ}

theorem embedMat_mul_embedMat (f : Fin m → Fin n) (g : Fin k → Fin m) :
    embedMat (R := R) f * embedMat g = embedMat (f ∘ g) := by
  ext i c
  simp only [mul_apply, embedMat, Function.comp]
  rw [Finset.sum_eq_single (g c)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

/-- Level matrices compose. -/
theorem levelMat_levelMat (f : Fin m → Fin n) (g : Fin k → Fin m)
    (M : Matrix (Fin k) (Fin k) R) : levelMat f (levelMat g M) = levelMat (f ∘ g) M := by
  simp only [levelMat, add_sub_cancel_left, ← embedMat_mul_embedMat, transpose_mul,
    Matrix.mul_assoc]

theorem levelMat_one (f : Fin m → Fin n) : levelMat f (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  simp [levelMat]

/-- `levelMat f` is multiplicative for injective `f`. -/
theorem levelMat_mul {f : Fin m → Fin n} (hf : Function.Injective f)
    (A B : Matrix (Fin m) (Fin m) R) : levelMat f (A * B) = levelMat f A * levelMat f B := by
  have hE := embedMat_transpose_mul (R := R) hf
  have hAB : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  simp only [levelMat]
  set E := embedMat (R := R) f
  have : E * (A - 1) * Eᵀ * (E * (B - 1) * Eᵀ) = E * ((A - 1) * (B - 1)) * Eᵀ := by
    calc E * (A - 1) * Eᵀ * (E * (B - 1) * Eᵀ) = E * (A - 1) * (Eᵀ * E) * (B - 1) * Eᵀ := by
          simp only [Matrix.mul_assoc]
      _ = E * ((A - 1) * (B - 1)) * Eᵀ := by rw [hE, Matrix.mul_one, Matrix.mul_assoc E]
  rw [hAB, add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, this,
    Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

theorem embedMat_map (φ : R →+* S) (f : Fin m → Fin n) :
    (embedMat (R := R) f).map φ = embedMat f := by
  ext i k; simp only [embedMat, map_apply]; split_ifs <;> simp

theorem levelMat_map (φ : R →+* S) (f : Fin m → Fin n) (M : Matrix (Fin m) (Fin m) R) :
    (levelMat f M).map φ = levelMat f (M.map φ) := by
  simp only [levelMat, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_sub _ (map_sub φ),
    Matrix.map_one _ φ.map_zero φ.map_one, transpose_map, embedMat_map]

/-- A level matrix scaled by `t`, defined from the scaled block `A`
(`= t • M`) so that it makes sense over `ℤ√2` for `t = √2`. -/
def slevel (f : Fin m → Fin n) (t : R) (A : Matrix (Fin m) (Fin m) R) :
    Matrix (Fin n) (Fin n) R :=
  t • (1 : Matrix (Fin n) (Fin n) R) + embedMat f * (A - t • 1) * (embedMat f)ᵀ

theorem slevel_smul (f : Fin m → Fin n) (t : R) (M : Matrix (Fin m) (Fin m) R) :
    slevel f t (t • M) = t • levelMat f M := by
  simp only [slevel, levelMat, smul_add, ← smul_sub, Matrix.mul_smul, Matrix.smul_mul]

theorem slevel_map (φ : R →+* S) (f : Fin m → Fin n) (t : R) (A : Matrix (Fin m) (Fin m) R) :
    (slevel f t A).map φ = slevel f (φ t) (A.map φ) := by
  simp only [slevel, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_sub _ (map_sub φ),
    Matrix.map_smul' _ _ _ (map_mul φ), Matrix.map_one _ φ.map_zero φ.map_one, transpose_map,
    embedMat_map]

end Level

/-- A generator on any indices of `Fin m` (ordered or not, equal or not):
the letters of local identities. -/
inductive LGen (m : ℕ) : Type
  | Z (i : Fin m)
  | X (i j : Fin m)
  | H (i j : Fin m)
  deriving DecidableEq

namespace LGen

variable {R S : Type*} [CommRing R] [CommRing S] {m n : ℕ}

/-- The matrix of a local generator, `s` standing for `1/√2`. -/
def mat (s : R) : LGen m → Matrix (Fin m) (Fin m) R
  | Z i => levelMat ![i] Zmat
  | X i j => levelMat ![i, j] Xmat
  | H i j => levelMat ![i, j] (Hmat s)

/-- The matrix of a local generator scaled by `t`, standing for `√2`. -/
def smat (t : R) : LGen m → Matrix (Fin m) (Fin m) R
  | Z i => slevel ![i] t !![-t]
  | X i j => slevel ![i, j] t !![0, t; t, 0]
  | H i j => slevel ![i, j] t !![1, 1; 1, -1]

theorem smat_eq {s t : R} (hts : t * s = 1) (g : LGen m) : smat t g = t • mat s g := by
  cases g with
  | Z i =>
    rw [smat, mat, ← slevel_smul]; congr 1
    ext a b; fin_cases a; fin_cases b; simp [Zmat]
  | X i j =>
    rw [smat, mat, ← slevel_smul]; congr 1
    ext a b; fin_cases a <;> fin_cases b <;> simp [Xmat]
  | H i j =>
    rw [smat, mat, ← slevel_smul]; congr 1
    ext a b; fin_cases a <;> fin_cases b <;> simp [Hmat, hts]

theorem smat_map (φ : R →+* S) (t : R) (g : LGen m) : (smat t g).map φ = smat (φ t) g := by
  cases g with
  | Z i =>
    rw [smat, smat, slevel_map]; congr 1
    ext a b; fin_cases a; fin_cases b; simp
  | X i j =>
    rw [smat, smat, slevel_map]; congr 1
    ext a b; fin_cases a <;> fin_cases b <;> simp
  | H i j =>
    rw [smat, smat, slevel_map]; congr 1
    ext a b; fin_cases a <;> fin_cases b <;> simp

/-- A local generator moved to the indices `f`. -/
def push (f : Fin m → Fin n) : LGen m → LGen n
  | Z i => Z (f i)
  | X i j => X (f i) (f j)
  | H i j => H (f i) (f j)

theorem comp_vec₁ (f : Fin m → Fin n) (i : Fin m) : f ∘ ![i] = ![f i] := by
  ext a; fin_cases a; rfl

theorem comp_vec₂ (f : Fin m → Fin n) (i j : Fin m) : f ∘ ![i, j] = ![f i, f j] := by
  ext a; fin_cases a <;> rfl

theorem mat_push (s : R) (f : Fin m → Fin n) (g : LGen m) :
    mat s (push f g) = levelMat f (mat s g) := by
  cases g <;> simp only [push, mat, levelMat_levelMat, comp_vec₁, comp_vec₂]

end LGen

section Words

variable {R S : Type*} [CommRing R] [CommRing S] {m n : ℕ}

/-- The matrix of a local word: the product of its letters. -/
def lprod (s : R) (w : List (LGen m)) : Matrix (Fin m) (Fin m) R := (w.map (LGen.mat s)).prod

/-- The scaled matrix of a local word. -/
def sprod (t : R) (w : List (LGen m)) : Matrix (Fin m) (Fin m) R := (w.map (LGen.smat t)).prod

theorem sprod_eq {s t : R} (hts : t * s = 1) (w : List (LGen m)) :
    sprod t w = t ^ w.length • lprod s w := by
  induction w with
  | nil => simp [sprod, lprod]
  | cons g w ih =>
    simp only [sprod, lprod, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, LGen.smat_eq hts, smul_mul_smul, List.length_cons, pow_succ']

theorem sprod_map (φ : R →+* S) (t : R) (w : List (LGen m)) :
    (sprod t w).map φ = sprod (φ t) w := by
  induction w with
  | nil => simp [sprod, Matrix.map_one _ φ.map_zero φ.map_one]
  | cons g w ih =>
    simp only [sprod, List.map_cons, List.prod_cons, Matrix.map_mul] at ih ⊢
    rw [ih, LGen.smat_map]

theorem lprod_push (s : R) {f : Fin m → Fin n} (hf : Function.Injective f)
    (w : List (LGen m)) : lprod s (w.map (LGen.push f)) = levelMat f (lprod s w) := by
  induction w with
  | nil => simp [lprod, levelMat_one]
  | cons g w ih =>
    simp only [lprod, List.map_map, List.map_cons, List.prod_cons] at ih ⊢
    rw [levelMat_mul hf, ← ih, LGen.mat_push]

end Words

section Check

/-- `√2 ∈ ℤ√2`. -/
def rt2 : ℤ√2 := ⟨0, 1⟩

/-- `ℤ√2 ⊆ ℝ`. -/
noncomputable def toReal : ℤ√2 →+* ℝ :=
  Zsqrtd.lift ⟨Real.sqrt 2, by rw [Real.mul_self_sqrt (by norm_num)]; norm_num⟩

@[simp] theorem toReal_rt2 : toReal rt2 = Real.sqrt 2 := by
  simp [toReal, rt2]

theorem sqrt2_mul_invSqrt2 : Real.sqrt 2 * invSqrt2 = 1 :=
  mul_inv_cancel₀ (by positivity)

/-- An identity of local words decided over `ℤ√2` holds for the real
matrices. -/
theorem lprod_eq_of_check {m : ℕ} (L R : List (LGen m))
    (h : rt2 ^ R.length • sprod rt2 L = rt2 ^ L.length • sprod rt2 R) :
    lprod invSqrt2 L = lprod invSqrt2 R := by
  have h' := congrArg (Matrix.map · toReal) h
  simp only [Matrix.map_smul' _ _ _ (map_mul toReal), map_pow, toReal_rt2, sprod_map,
    sprod_eq sqrt2_mul_invSqrt2, smul_smul] at h'
  have hc : Real.sqrt 2 ^ R.length * Real.sqrt 2 ^ L.length ≠ 0 := by positivity
  have h'' : (Real.sqrt 2 ^ R.length * Real.sqrt 2 ^ L.length) • lprod invSqrt2 L =
      (Real.sqrt 2 ^ R.length * Real.sqrt 2 ^ L.length) • lprod invSqrt2 R := by
    rw [h', mul_comm]
  have := congrArg (fun M => (Real.sqrt 2 ^ R.length * Real.sqrt 2 ^ L.length)⁻¹ • M) h''
  simpa only [inv_smul_smul₀ hc] using this

end Check

section Gen

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A generator of `𝒢ₙ` as a local generator. -/
def Gen.toL : Gen n → LGen n
  | .Z a => .Z a
  | .X a b _ => .X a b
  | .H a b _ => .H a b

theorem genMat_eq (s : R) (g : Gen n) : genMat s g = LGen.mat s g.toL := by
  cases g <;> rfl

theorem wordMat_eq (s : R) (w : Word (Gen n)) :
    wordMat s w = lprod s (w.toList.map Gen.toL) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [lprod]
  | mul_of g w ih =>
    rw [map_mul, ih, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append]
    simp [lprod, wordMat, genMat_eq]

/-- An identity between words of `𝒢ₙ` at the indices `f` follows from the
identity of local words in dimension `m`, decided over `ℤ√2`. -/
theorem wordMat_eq_of_check {m : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f)
    (L R : List (LGen m))
    (h : rt2 ^ R.length • sprod rt2 L = rt2 ^ L.length • sprod rt2 R)
    {w w' : Word (Gen n)} (hw : w.toList.map Gen.toL = L.map (LGen.push f))
    (hw' : w'.toList.map Gen.toL = R.map (LGen.push f)) :
    wordMat invSqrt2 w = wordMat invSqrt2 w' := by
  rw [wordMat_eq, wordMat_eq, hw, hw', lprod_push _ hf, lprod_push _ hf,
    lprod_eq_of_check L R h]

end Gen

end QCert.HadamardPi
