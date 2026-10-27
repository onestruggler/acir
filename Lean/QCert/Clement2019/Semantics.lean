/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clément (2019): the matrices of the generators

`(-1)[j]` is the one-level matrix `-1` at `j`, and `H[j,k]`, `X[j,k]` are
the two-level matrices of `H = (1/√2)[[1,1],[1,-1]]` and `X = [[0,1],[1,0]]`
with the first row and column at `j` and the second at `k`
(Definition 1.2: `b_jj = m₁₁`, `b_jk = m₁₂`, `b_kj = m₂₁`, `b_kk = m₂₂`), that
is `levelMat ![j, k] M`.  They are the matrices of the local generators of
`QCert.HadamardPi.Local`.  The target group is `Uₙ(ℤ[1/√2])`, the real
matrices of `Uₙ(D[ω])` (Lemma 1.1), i.e. `Oₙ(ℤ[1/√2])` (`O_ZInvSqrt2 n`).
-/
import QCert.Clement2019.Syntax
import QCert.HadamardPi.Local

namespace QCert.Clement2019

open Matrix QCert.HadamardPi

variable {n : ℕ}

/-- A generator as a local generator. -/
def Gen.toL : Gen n → LGen n
  | .Z j => .Z j
  | .H j k _ => .H j k
  | .X j k _ => .X j k

/-- The matrix of a word, with `s` standing for `1/√2`. -/
def wordMat {R : Type*} [CommRing R] (s : R) : Word (Gen n) →* Matrix (Fin n) (Fin n) R :=
  FreeMonoid.lift fun g => LGen.mat s g.toL

theorem genMat_mem_unitary (g : Gen n) :
    LGen.mat invSqrt2 g.toL ∈ unitaryGroup (Fin n) ℝ := by
  cases g with
  | Z j => exact levelMat_mem_unitaryGroup (vecCons_injective₁ j) Zmat_mem
  | H j k h => exact levelMat_mem_unitaryGroup (vecCons_injective₂ h) Hmat_mem
  | X j k h => exact levelMat_mem_unitaryGroup (vecCons_injective₂ h) Xmat_mem

theorem genMat_mem_ZInvSqrt2 (g : Gen n) (i j : Fin n) :
    LGen.mat invSqrt2 g.toL i j ∈ ZInvSqrt2 := by
  cases g with
  | Z a =>
    refine levelMat_apply_mem _ (fun k l => ?_) i j
    fin_cases k; fin_cases l; simp [Zmat, ZInvSqrt2.neg_mem, ZInvSqrt2.one_mem]
  | H a b h =>
    refine levelMat_apply_mem _ (fun k l => ?_) i j
    fin_cases k <;> fin_cases l <;> simp [Hmat, invSqrt2_mem, ZInvSqrt2.neg_mem]
  | X a b h =>
    refine levelMat_apply_mem _ (fun k l => ?_) i j
    fin_cases k <;> fin_cases l <;> simp [Xmat, ZInvSqrt2.one_mem, ZInvSqrt2.zero_mem]

/-- The semantics of a generator, an element of `Oₙ(ℤ[1/√2])`. -/
noncomputable def sem (n : ℕ) (g : Gen n) : O_ZInvSqrt2 n :=
  ⟨⟨LGen.mat invSqrt2 g.toL, genMat_mem_unitary g⟩, genMat_mem_ZInvSqrt2 g⟩

theorem lift_sem_val (w : Word (Gen n)) :
    (((FreeMonoid.lift (sem n) w : O_ZInvSqrt2 n) : unitaryGroup (Fin n) ℝ) :
      Matrix (Fin n) (Fin n) ℝ) = wordMat invSqrt2 w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    rw [map_mul, map_mul, Subgroup.coe_mul, Submonoid.coe_mul, ih]
    rfl

theorem wordMat_eq {R : Type*} [CommRing R] (s : R) (w : Word (Gen n)) :
    wordMat s w = lprod s (w.toList.map Gen.toL) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [lprod]
  | mul_of g w ih =>
    rw [map_mul, ih, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append]
    simp [lprod, wordMat]

/-- An identity between words at the indices `f`, from the identity of
local words in dimension `m` decided over `ℤ√2`. -/
theorem wordMat_eq_of_check {m : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f)
    (L R : List (LGen m))
    (h : rt2 ^ R.length • sprod rt2 L = rt2 ^ L.length • sprod rt2 R)
    {w w' : Word (Gen n)} (hw : w.toList.map Gen.toL = L.map (LGen.push f))
    (hw' : w'.toList.map Gen.toL = R.map (LGen.push f)) :
    wordMat invSqrt2 w = wordMat invSqrt2 w' := by
  rw [wordMat_eq, wordMat_eq, hw, hw', lprod_push _ hf, lprod_push _ hf,
    lprod_eq_of_check L R h]

end QCert.Clement2019
