/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Matrices as lists of rows, for evaluation by the kernel

`decide +kernel` on `Matrix` products is slow (entries of a product are
re-evaluated through `Finset` sums).  A square matrix given as a list of
rows, `LMat R`, is multiplied by list recursion (`ListMat.mul`), which the
kernel evaluates quickly, and read as an `n × n` matrix by `toMat n`
(missing entries are `0`): `toMat n (mul n A B) = toMat n A * toMat n B`.
`level m idx M` is the list form of the level matrix `levelMat`.
-/
import QCert.Matrix.Level
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

namespace QCert.ListMat

open Matrix

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A square matrix as a list of rows. -/
abbrev LMat (R : Type*) := List (List R)

/-- The `n × n` matrix of a list of rows (missing entries are `0`). -/
def toMat (n : ℕ) (L : LMat R) : Matrix (Fin n) (Fin n) R := fun i j => (L.getD i []).getD j 0

/-- Row `r` times column `j` of `B`. -/
def dot (n : ℕ) (r : List R) (B : LMat R) (j : ℕ) : R :=
  ((List.range n).map fun k => r.getD k 0 * (B.getD k []).getD j 0).sum

/-- The product of two list matrices. -/
def mul (n : ℕ) (A B : LMat R) : LMat R := A.map fun r => (List.range n).map (dot n r B)

/-- The identity matrix. -/
def one (n : ℕ) : LMat R :=
  (List.range n).map fun i => (List.range n).map fun j => if i = j then 1 else 0

/-- The product of a list of list matrices. -/
def prod (n : ℕ) (l : List (LMat R)) : LMat R := l.foldr (mul n) (one n)

theorem list_sum_range (f : ℕ → R) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem getD_range_map {α : Type*} (f : ℕ → α) (n j : ℕ) (hj : j < n) (d : α) :
    ((List.range n).map f).getD j d = f j := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem getD_map_of_lt {α β : Type*} (g : α → β) (A : List α) {i : ℕ} (hi : i < A.length)
    (d : β) (d' : α) : (A.map g).getD i d = g (A.getD i d') := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_map_of_ge {α β : Type*} (g : α → β) (A : List α) {i : ℕ} (hi : A.length ≤ i)
    (d : β) : (A.map g).getD i d = d := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem toMat_mul (n : ℕ) (A B : LMat R) : toMat n (mul n A B) = toMat n A * toMat n B := by
  ext i j
  simp only [toMat, mul, Matrix.mul_apply]
  by_cases hi : (i : ℕ) < A.length
  · rw [getD_map_of_lt _ _ hi _ [], getD_range_map _ _ _ j.2, dot, list_sum_range,
      ← Fin.sum_univ_eq_sum_range]
  · rw [getD_map_of_ge _ _ (by omega)]
    have h0 : A.getD i [] = [] := by simp [List.getD_eq_getElem?_getD, show A.length ≤ (i : ℕ) by omega]
    simp only [h0, List.getD_nil, zero_mul, Finset.sum_const_zero]

theorem toMat_one (n : ℕ) : toMat n (one n : LMat R) = 1 := by
  ext i j
  simp only [toMat, one, getD_range_map _ _ _ i.2, getD_range_map _ _ _ j.2, Matrix.one_apply,
    Fin.ext_iff]

theorem toMat_prod (n : ℕ) (l : List (LMat R)) : toMat n (prod n l) = (l.map (toMat n)).prod := by
  induction l with
  | nil => exact toMat_one n
  | cons A l ih => rw [prod, List.foldr_cons, ← prod, toMat_mul, ih]; simp

/-- The entries of a list matrix read through a ring homomorphism. -/
def map (φ : R →+* S) (L : LMat R) : LMat S := L.map (List.map φ)

theorem toMat_map (n : ℕ) (φ : R →+* S) (L : LMat R) :
    toMat n (map φ L) = (toMat n L).map φ := by
  ext i j
  simp only [toMat, map, Matrix.map_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[(i : ℕ)]? with
  | none => simp
  | some r => cases h : r[(j : ℕ)]? <;> simp [h]

/-! ## Level matrices -/

/-- The position of `i` in a list of naturals. -/
def pos : List ℕ → ℕ → Option ℕ
  | [], _ => none
  | a :: l, i => if a = i then some 0 else (pos l i).map (· + 1)

/-- The list form of the level matrix acting as `M` on the indices `idx`
(Definition 2.5 of Li–Ross–Selinger), on `m` indices. -/
def level (m : ℕ) (idx : List ℕ) (M : LMat R) : LMat R :=
  (List.range m).map fun i => (List.range m).map fun j =>
    match pos idx i, pos idx j with
    | some p, some q => (M.getD p []).getD q 0
    | _, _ => if i = j then 1 else 0

/-- Where an index lies in `List.ofFn (val ∘ f)`. -/
theorem pos_ofFn_eq {k m : ℕ} (f : Fin k → Fin m) (hf : Function.Injective f) (i : ℕ) :
    pos (List.ofFn fun t => (f t : ℕ)) i =
      if h : ∃ t, (f t : ℕ) = i then some (h.choose : ℕ) else none := by
  induction k generalizing i with
  | zero => simp [pos]
  | succ k ih =>
    rw [List.ofFn_succ, pos]
    have ih' := ih (fun t => f t.succ) (hf.comp (Fin.succ_injective _)) i
    by_cases h0 : (f 0 : ℕ) = i
    · rw [if_pos h0, dif_pos ⟨0, h0⟩]
      congr 1
      have hc := (⟨0, h0⟩ : ∃ t, (f t : ℕ) = i).choose_spec
      have : f (⟨0, h0⟩ : ∃ t, (f t : ℕ) = i).choose = f 0 := Fin.ext (hc.trans h0.symm)
      rw [hf this]; rfl
    · rw [if_neg h0, ih']
      by_cases h : ∃ t, (f (Fin.succ t) : ℕ) = i
      · have h' : ∃ t, (f t : ℕ) = i := ⟨_, h.choose_spec⟩
        rw [dif_pos h, dif_pos h']
        simp only [Option.map_some, Option.some.injEq]
        have e : f h'.choose = f h.choose.succ := Fin.ext (h'.choose_spec.trans h.choose_spec.symm)
        rw [hf e]; simp
      · have h' : ¬ ∃ t, (f t : ℕ) = i := by
          rintro ⟨t, ht⟩
          refine Fin.cases (fun ht => h0 ht) (fun t ht => h ⟨t, ht⟩) t ht
        rw [dif_neg h, dif_neg h']; rfl

/-- The list form of a level matrix is the level matrix. -/
theorem toMat_level {k m : ℕ} (f : Fin k → Fin m) (hf : Function.Injective f) (M : LMat R) :
    toMat m (level m (List.ofFn fun t => (f t : ℕ)) M) = levelMat f (toMat k M) := by
  ext i j
  simp only [toMat, level, getD_range_map _ _ _ i.2, getD_range_map _ _ _ j.2,
    pos_ofFn_eq f hf]
  by_cases hi : ∃ t, (f t : ℕ) = i
  · by_cases hj : ∃ t, (f t : ℕ) = j
    · simp only [dif_pos hi, dif_pos hj]
      have ei : f hi.choose = i := Fin.ext hi.choose_spec
      have ej : f hj.choose = j := Fin.ext hj.choose_spec
      conv_rhs => rw [← ei, ← ej]
      rw [levelMat_apply_apply hf]; rfl
    · simp only [dif_pos hi, dif_neg hj]
      rw [levelMat_apply_of_right _ _ (fun l h => hj ⟨l, congrArg Fin.val h⟩)]
      simp [Matrix.one_apply, Fin.ext_iff]
  · simp only [dif_neg hi]
    rw [levelMat_apply_of_left _ (fun l h => hi ⟨l, congrArg Fin.val h⟩)]
    simp [Matrix.one_apply, Fin.ext_iff]

end QCert.ListMat
