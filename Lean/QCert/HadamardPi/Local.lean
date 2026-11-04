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

/-! ### The check on basis vectors

The scaled matrices act on vectors entry by entry (`LGen.act`): `(-1)` negates one entry,
`X` exchanges two, `H` takes their sum and difference, and every other entry is multiplied by
`√2`.  Two scaled products are equal when they agree on every basis vector, which `vcheck`
decides on pairs of integers (`a + b √2` as `(a, b)`, `√2` doubling and exchanging the two):
the kernel then evaluates about `m · |w|` entries instead of the matrix products, where
`decide` on the matrices took seconds for a word of twenty letters. -/

section Act

variable {R : Type*} [CommRing R] {k m : ℕ}

/-- The indices of a local generator are distinct. -/
def LGen.ok : LGen m → Bool
  | .Z _ => true
  | .X i j => decide (i ≠ j)
  | .H i j => decide (i ≠ j)

/-- The scaled matrix of a local generator acting on a vector, entry by entry
(`smat t g *ᵥ v` for distinct indices, `smat_mulVec`). -/
def LGen.act (t : R) : LGen m → (Fin m → R) → (Fin m → R)
  | .Z i, v => fun k => if k = i then -(t * v i) else t * v k
  | .X i j, v => fun k => if k = i then t * v j else if k = j then t * v i else t * v k
  | .H i j, v => fun k => if k = i then v i + v j else if k = j then v i - v j else t * v k

theorem embedMatT_mulVecL (f : Fin k → Fin m) (v : Fin m → R) :
    (embedMat f)ᵀ *ᵥ v = fun i => v (f i) := by
  funext i
  simp only [mulVec, dotProduct, transpose_apply, embedMat, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem embedMat_mulVec₂ (p q : Fin m) (u : Fin 2 → R) :
    embedMat ![p, q] *ᵥ u = fun k => (if k = p then u 0 else 0) + (if k = q then u 1 else 0) := by
  funext k
  simp only [mulVec, dotProduct, embedMat, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, ite_mul, one_mul, zero_mul,
    @eq_comm _ p k, @eq_comm _ q k]

theorem embedMat_mulVec₁ (p : Fin m) (u : Fin 1 → R) :
    embedMat ![p] *ᵥ u = fun k => if k = p then u 0 else 0 := by
  funext k
  simp only [mulVec, dotProduct, embedMat, Fin.sum_univ_one, Matrix.cons_val_fin_one, ite_mul,
    one_mul, zero_mul, @eq_comm _ p k]

theorem Zmat_sub (t : R) : (!![-t] - t • (1 : Matrix (Fin 1) (Fin 1) R)) = !![-t - t] := by
  ext i j; fin_cases i; fin_cases j; simp

theorem Xmat_sub (t : R) :
    (!![0, t; t, 0] - t • (1 : Matrix (Fin 2) (Fin 2) R)) = !![-t, t; t, -t] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem Hmat_sub (t : R) :
    (!![1, 1; 1, -1] - t • (1 : Matrix (Fin 2) (Fin 2) R)) = !![1 - t, 1; 1, -1 - t] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sub_eq_add_neg]

theorem slevel_mulVec (f : Fin k → Fin m) (t : R) (A : Matrix (Fin k) (Fin k) R) (v : Fin m → R) :
    slevel f t A *ᵥ v = t • v + embedMat f *ᵥ ((A - t • 1) *ᵥ fun i => v (f i)) := by
  rw [slevel, add_mulVec, smul_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    embedMatT_mulVecL]

theorem mulVec_fin_one (A : Matrix (Fin 1) (Fin 1) R) (w : Fin 1 → R) :
    A *ᵥ w = ![A 0 0 * w 0] := by
  funext i; fin_cases i; simp [mulVec, dotProduct]

theorem mulVec_fin_two (A : Matrix (Fin 2) (Fin 2) R) (w : Fin 2 → R) :
    A *ᵥ w = ![A 0 0 * w 0 + A 0 1 * w 1, A 1 0 * w 0 + A 1 1 * w 1] := by
  funext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem smat_mulVec (t : R) (g : LGen m) (hg : g.ok = true) (v : Fin m → R) :
    LGen.smat t g *ᵥ v = g.act t v := by
  cases g with
  | Z i =>
    funext k
    simp only [LGen.smat, LGen.act, slevel_mulVec, Zmat_sub, embedMat_mulVec₁, mulVec_fin_one,
      Matrix.of_apply, Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs with h
    · subst h; ring
    · ring
  | X i j =>
    funext k
    simp only [LGen.smat, LGen.act, slevel_mulVec, Xmat_sub, embedMat_mulVec₂, mulVec_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> (try subst_vars) <;> ring1
  | H i j =>
    have hij : i ≠ j := by simpa [LGen.ok] using hg
    funext k
    simp only [LGen.smat, LGen.act, slevel_mulVec, Hmat_sub, embedMat_mulVec₂, mulVec_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> (try subst_vars) <;> first | ring1 | exact absurd rfl hij

/-- A local word acting on a vector, letter by letter. -/
def actLW (t : R) : List (LGen m) → (Fin m → R) → (Fin m → R)
  | [], v => v
  | g :: w, v => g.act t (actLW t w v)

theorem sprod_mulVec (t : R) : ∀ (w : List (LGen m)), w.all LGen.ok = true → ∀ v : Fin m → R,
    sprod t w *ᵥ v = actLW t w v
  | [], _, v => by simp [sprod, actLW]
  | g :: w, h, v => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [sprod, List.map_cons, List.prod_cons, actLW]
    rw [← mulVec_mulVec, ← sprod, sprod_mulVec t w h.2, smat_mulVec t g h.1]

/-- The basis vector `e j`. -/
def basisV (j : Fin m) : Fin m → R := fun k => if k = j then 1 else 0

theorem basisV_eq_single (j : Fin m) : (basisV j : Fin m → R) = Pi.single j 1 := by
  funext k; simp [basisV, Pi.single_apply]

/-- Two scaled products agree when they agree on every basis vector. -/
theorem sprod_eq_of_act (t : R) (L Rw : List (LGen m)) (hL : L.all LGen.ok = true)
    (hR : Rw.all LGen.ok = true)
    (h : ∀ j : Fin m, t ^ Rw.length • actLW t L (basisV j) = t ^ L.length • actLW t Rw (basisV j)) :
    t ^ Rw.length • sprod t L = t ^ L.length • sprod t Rw := by
  ext i j
  have := congrFun (h j) i
  rw [← sprod_mulVec t L hL, ← sprod_mulVec t Rw hR, basisV_eq_single, mulVec_single_one,
    mulVec_single_one] at this
  simpa using this

end Act

/-! ### Over `ℤ√2`, on pairs of integers -/

theorem rt2_sq : rt2 * rt2 = ⟨2, 0⟩ := by ext <;> simp [rt2]

theorem rt2_pow_even (m : ℕ) : rt2 ^ (2 * m) = ⟨2 ^ m, 0⟩ := by
  induction m with
  | zero => ext <;> simp
  | succ m ih => rw [Nat.mul_succ, pow_add, ih, pow_two, rt2_sq]; ext <;> simp [pow_succ]

/-- `a + b √2` as a pair of integers, for the computation. -/
abbrev ZPair := ℤ × ℤ

namespace ZPair

def toZ (x : ZPair) : ℤ√2 := ⟨x.1, x.2⟩
/-- `√2 · x`. -/
def sq2 (x : ZPair) : ZPair := (2 * x.2, x.1)
def add (x y : ZPair) : ZPair := (x.1 + y.1, x.2 + y.2)
def sub (x y : ZPair) : ZPair := (x.1 - y.1, x.2 - y.2)
def neg (x : ZPair) : ZPair := (-x.1, -x.2)
/-- `√2 ^ n · x`. -/
def pow2 (n : ℕ) (x : ZPair) : ZPair :=
  if n % 2 = 0 then (2 ^ (n / 2) * x.1, 2 ^ (n / 2) * x.2)
  else (2 ^ (n / 2 + 1) * x.2, 2 ^ (n / 2) * x.1)

theorem toZ_sq2 (x : ZPair) : (sq2 x).toZ = rt2 * x.toZ := by ext <;> simp [toZ, sq2, rt2]
theorem toZ_add (x y : ZPair) : (add x y).toZ = x.toZ + y.toZ := by ext <;> simp [toZ, add]
theorem toZ_sub (x y : ZPair) : (sub x y).toZ = x.toZ - y.toZ := by ext <;> simp [toZ, sub]
theorem toZ_neg (x : ZPair) : (neg x).toZ = -x.toZ := by ext <;> simp [toZ, neg]

theorem toZ_pow2 (n : ℕ) (x : ZPair) : (pow2 n x).toZ = rt2 ^ n * x.toZ := by
  unfold pow2
  set m := n / 2 with hm
  split_ifs with h
  · rw [show n = 2 * m by omega, rt2_pow_even]
    ext <;> simp [toZ]
  · rw [show n = 2 * m + 1 by omega, pow_succ rt2 (2 * m), mul_assoc (rt2 ^ (2 * m)) rt2,
      rt2_pow_even]
    ext
    · simp [toZ, rt2, pow_succ]; ring
    · simp [toZ, rt2]

end ZPair

/-- The scaled action on pairs: `√2` doubles the `√2` part and exchanges the two. -/
def LGen.act2 {m : ℕ} : LGen m → (Fin m → ZPair) → (Fin m → ZPair)
  | .Z i, v => fun k => if k = i then (v i).sq2.neg else (v k).sq2
  | .X i j, v => fun k => if k = i then (v j).sq2 else if k = j then (v i).sq2 else (v k).sq2
  | .H i j, v => fun k => if k = i then (v i).add (v j) else if k = j then (v i).sub (v j)
      else (v k).sq2

theorem toZ_act2 {m : ℕ} (g : LGen m) (v : Fin m → ZPair) :
    (fun k => (g.act2 v k).toZ) = g.act rt2 fun k => (v k).toZ := by
  funext k
  cases g <;> simp only [LGen.act2, LGen.act] <;> split_ifs <;>
    simp [ZPair.toZ_sq2, ZPair.toZ_add, ZPair.toZ_sub, ZPair.toZ_neg]

def actLP {m : ℕ} : List (LGen m) → (Fin m → ZPair) → (Fin m → ZPair)
  | [], v => v
  | g :: w, v => g.act2 (actLP w v)

theorem toZ_actLP {m : ℕ} : ∀ (w : List (LGen m)) (v : Fin m → ZPair),
    (fun k => (actLP w v k).toZ) = actLW rt2 w fun k => (v k).toZ
  | [], v => rfl
  | g :: w, v => by
    simp only [actLP, actLW]
    rw [← toZ_actLP w v, toZ_act2]

/-- The basis vector `e j` as pairs. -/
def basisP {m : ℕ} (j : Fin m) : Fin m → ZPair := fun k => if k = j then (1, 0) else (0, 0)

theorem toZ_basisP {m : ℕ} (j : Fin m) : (fun k => (basisP j k).toZ) = (basisV j : Fin m → ℤ√2) := by
  funext k; simp only [basisP, basisV]; split_ifs <;> ext <;> simp [ZPair.toZ]

/-- The check of an identity of local words on the basis vectors, as one Boolean: every entry
of `√2 ^ |R| · L e_j` and `√2 ^ |L| · R e_j` agree. -/
def vcheck {m : ℕ} (L R : List (LGen m)) : Bool :=
  L.all LGen.ok && R.all LGen.ok &&
    (List.finRange m).all fun j =>
      let a := actLP L (basisP j)
      let b := actLP R (basisP j)
      (List.finRange m).all fun k => ZPair.pow2 R.length (a k) == ZPair.pow2 L.length (b k)

theorem sprod_eq_of_vcheck {m : ℕ} (L R : List (LGen m)) (h : vcheck L R = true) :
    rt2 ^ R.length • sprod rt2 L = rt2 ^ L.length • sprod rt2 R := by
  simp only [vcheck, Bool.and_eq_true] at h
  obtain ⟨⟨hL, hR⟩, hv⟩ := h
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hv
  refine sprod_eq_of_act rt2 L R hL hR fun j => ?_
  funext k
  have e := congrArg ZPair.toZ (hv j k)
  rw [ZPair.toZ_pow2, ZPair.toZ_pow2] at e
  have hL := congrFun (toZ_actLP L (basisP j)) k
  have hR := congrFun (toZ_actLP R (basisP j)) k
  rw [toZ_basisP] at hL hR
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← hL, ← hR]
  exact e

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

/-- The same, the identity of local words decided on the basis vectors (`vcheck`). -/
theorem wordMat_eq_of_vcheck {m : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f)
    (L R : List (LGen m)) (h : vcheck L R = true)
    {w w' : Word (Gen n)} (hw : w.toList.map Gen.toL = L.map (LGen.push f))
    (hw' : w'.toList.map Gen.toL = R.map (LGen.push f)) :
    wordMat invSqrt2 w = wordMat invSqrt2 w' :=
  wordMat_eq_of_check f hf L R (sprod_eq_of_vcheck L R h) hw hw'

end Gen

end QCert.HadamardPi
