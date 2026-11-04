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

/-! ## Sparse gates

A gate that permutes or negates basis vectors acts on the rows of a matrix
without arithmetic; `Act.apply` multiplies by a gate on the left. -/

/-- A matrix given as a row permutation, a sign per row, or densely. -/
inductive Act (R : Type*) where
  /-- The matrix with a `1` at `(i, π i)`: row `i` of the product is row `π i`. -/
  | perm (π : List ℕ)
  /-- The diagonal matrix with `-1` at the rows marked `true`. -/
  | signs (σ : List Bool)
  /-- A dense matrix. -/
  | dense (L : LMat R)

theorem getD_map_neg (l : List R) (j : ℕ) : (l.map Neg.neg).getD j 0 = -(l.getD j 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> simp

namespace Act

/-- The `n × n` matrix of a gate. -/
def toMat (n : ℕ) : Act R → Matrix (Fin n) (Fin n) R
  | perm π => fun i j => if π.getD i n = j then 1 else 0
  | signs σ => fun i j => if i = j then (if σ.getD i false then -1 else 1) else 0
  | dense L => ListMat.toMat n L

/-- The product of a gate with a list matrix. -/
def apply (n : ℕ) : Act R → LMat R → LMat R
  | perm π, M => π.map fun i => if i < n then M.getD i [] else []
  | signs σ, M => (List.range n).map fun i =>
      if σ.getD i false then (M.getD i []).map Neg.neg else M.getD i []
  | dense L, M => mul n L M

theorem toMat_apply (n : ℕ) (a : Act R) (M : LMat R) :
    ListMat.toMat n (a.apply n M) = a.toMat n * ListMat.toMat n M := by
  cases a with
  | perm π =>
    ext i j
    simp only [ListMat.toMat, apply, toMat, Matrix.mul_apply, ite_mul, one_mul, zero_mul]
    by_cases hi : (i : ℕ) < π.length
    · rw [getD_map_of_lt _ _ hi _ 0]
      have e1 : π.getD i n = π[(i : ℕ)] := by simp [List.getD_eq_getElem?_getD, hi]
      have e2 : π.getD i 0 = π[(i : ℕ)] := by simp [List.getD_eq_getElem?_getD, hi]
      simp only [e1, e2]
      rcases lt_or_ge π[(i : ℕ)] n with hk | hk
      · rw [Finset.sum_eq_single ⟨π[(i : ℕ)], hk⟩ (fun b _ hb => by
            rw [if_neg]; intro h; exact hb (Fin.ext h.symm)) (by simp)]
        simp [hk]
      · rw [Finset.sum_eq_zero (fun b _ => by rw [if_neg]; omega)]
        simp [show ¬ π[(i : ℕ)] < n by omega]
    · rw [getD_map_of_ge _ _ (by omega)]
      rw [Finset.sum_eq_zero (fun b _ => by
        rw [if_neg]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp; omega)]
      simp
  | signs σ =>
    ext i j
    simp only [ListMat.toMat, apply, toMat, Matrix.mul_apply, ite_mul, zero_mul,
      getD_range_map _ _ _ i.2]
    rw [Finset.sum_eq_single i (fun b _ hb => by rw [if_neg (Ne.symm hb)]) (by simp)]
    simp only [if_true]
    split_ifs with h
    · rw [getD_map_neg]; simp
    · simp
  | dense L => exact toMat_mul n L M

end Act


/-! ## Fast evaluation on integer matrices

`decide +kernel` pays for every unfolding and almost nothing for arithmetic
on literals, so a product of gate matrices over `ℚ(√2)` costs seconds
(`Rat` normalisation at every entry) where the same product over `ℤ`
costs milliseconds.  A word of gates is therefore evaluated as a *scaled
integer matrix* `SMat`: a power `e` of a scalar `c` (`1/√2` or `1/2`,
fixed by the client) and an integer list matrix, read as `c ^ e • M`
(`SMat.toMatS`).  Every gate is an integer row operation `Act ℤ` with a
scale (`SMat.step`); the row operations are applied by primitive recursion
(`Act.applyF`: no `GetElem?`, no `brecOn`, no `Decidable` tests), and two
results are compared by one Boolean (`eqS`), which rescales the one with
the smaller exponent; `eqS_sound` is its soundness, given `2 * c ^ p = 1`
for the period `p` of the scale (`p = 2` for `c = 1/√2`, `p = 1` for
`c = 1/2`). -/

section Fast

variable {α β : Type*}

/-- `l.getD i d` by primitive recursion. -/
def nthD (d : α) (l : List α) : ℕ → α :=
  List.rec (motive := fun _ => ℕ → α) (fun _ => d)
    (fun a _ ih i => Nat.rec (motive := fun _ => α) a (fun i' _ => ih i') i) l

theorem nthD_eq (d : α) (l : List α) (i : ℕ) : nthD d l i = l.getD i d := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => rw [List.getD_cons_succ, ← ih i]; rfl

/-- `List.map` by primitive recursion. -/
def mapR (f : α → β) : List α → List β :=
  List.rec (motive := fun _ => List β) [] (fun a _ ih => f a :: ih)

theorem mapR_eq (f : α → β) (l : List α) : mapR f l = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => show f a :: mapR f l = _; rw [ih]; rfl

/-- The rows `π` of `M`: the product with the permutation matrix of `π`. -/
def permF (π : List ℕ) (M : LMat ℤ) : LMat ℤ := mapR (fun i => nthD [] M i) π

/-- The rows of `M` negated where `σ` is set. -/
def signF (σ : List Bool) (M : LMat ℤ) : LMat ℤ :=
  List.rec (motive := fun _ => LMat ℤ → LMat ℤ) (fun _ => [])
    (fun b _ ih M => List.rec (motive := fun _ => LMat ℤ) []
      (fun r M' _ => (bif b then mapR Neg.neg r else r) :: ih M') M) σ M

/-- The sum of two rows (the longer one's tail kept). -/
def addRow : List ℤ → List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ → List ℤ) (fun v => v)
    (fun x _ ih v => List.rec (motive := fun _ => List ℤ) (x :: ih [])
      (fun y ys _ => (x + y) :: ih ys) v)

/-- A row times a scalar. -/
def scaleRow (c : ℤ) (r : List ℤ) : List ℤ := r.map (c * ·)

/-- `∑ k, cs[k] • M[k]`: a row of a product, as a combination of the rows of
`M`; zero coefficients are skipped. -/
def combRow : List ℤ → LMat ℤ → List ℤ :=
  List.rec (motive := fun _ => LMat ℤ → List ℤ) (fun _ => [])
    (fun c _ ih M => List.rec (motive := fun _ => List ℤ) []
      (fun r M' _ => bif c == 0 then ih M' else addRow (scaleRow c r) (ih M')) M)

/-- The product `L * M`, row by row. -/
def mulF (L M : LMat ℤ) : LMat ℤ := mapR (fun cs => combRow cs M) L

theorem signF_getD (σ : List Bool) (M : LMat ℤ) (i : ℕ) (hi : i < σ.length) :
    (signF σ M).getD i [] =
      if σ.getD i false then (M.getD i []).map Neg.neg else M.getD i [] := by
  induction σ generalizing M i with
  | nil => simp at hi
  | cons b σ ih =>
    cases M with
    | nil => cases i <;> simp [signF]
    | cons r M =>
      cases i with
      | zero =>
        show (bif b then mapR Neg.neg r else r) = if b then r.map Neg.neg else r
        cases b <;> simp [mapR_eq]
      | succ i =>
        show (signF σ M).getD i [] = _
        rw [List.getD_cons_succ, List.getD_cons_succ, ih M i (by simpa using hi)]

theorem addRow_getD (u v : List ℤ) (j : ℕ) :
    (addRow u v).getD j 0 = u.getD j 0 + v.getD j 0 := by
  induction u generalizing v j with
  | nil => simp [addRow]
  | cons x u ih =>
    cases v with
    | nil =>
      cases j with
      | zero => show x = x + 0; rw [add_zero]
      | succ j => show (addRow u []).getD j 0 = _; rw [ih]; simp
    | cons y v =>
      cases j with
      | zero => rfl
      | succ j => show (addRow u v).getD j 0 = _; rw [ih]; rfl

theorem scaleRow_getD (c : ℤ) (r : List ℤ) (j : ℕ) :
    (scaleRow c r).getD j 0 = c * r.getD j 0 := by
  simp only [scaleRow, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases r[j]? <;> simp

theorem combRow_getD (cs : List ℤ) (M : LMat ℤ) (j : ℕ) :
    (combRow cs M).getD j 0 =
      ∑ k ∈ Finset.range cs.length, cs.getD k 0 * (M.getD k []).getD j 0 := by
  induction cs generalizing M with
  | nil => simp [combRow]
  | cons c cs ih =>
    cases M with
    | nil =>
      show ([] : List ℤ).getD j 0 = _
      simp
    | cons r M =>
      show (bif c == 0 then combRow cs M else addRow (scaleRow c r) (combRow cs M)).getD j 0 = _
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      cases hc : c == 0
      · simp only [cond_false, addRow_getD, scaleRow_getD, ih]; ring
      · simp only [beq_iff_eq] at hc
        simp only [cond_true, ih, hc, zero_mul, add_zero]

theorem toMat_mulF (n : ℕ) (L M : LMat ℤ) (hL : ∀ r ∈ L, r.length ≤ n) :
    toMat n (mulF L M) = toMat n L * toMat n M := by
  ext i j
  simp only [toMat, mulF, mapR_eq, Matrix.mul_apply]
  by_cases hi : (i : ℕ) < L.length
  · rw [getD_map_of_lt _ _ hi _ [], combRow_getD]
    have hmem : L.getD i [] ∈ L := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
    have hlen := hL _ hmem
    rw [Fin.sum_univ_eq_sum_range (fun k => (L.getD i []).getD k 0 * (M.getD k []).getD j 0) n]
    apply Finset.sum_subset (Finset.range_mono hlen)
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; simp
  · rw [getD_map_of_ge _ _ (by omega)]
    have h0 : L.getD i [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    simp only [h0, List.getD_nil, zero_mul, Finset.sum_const_zero]

namespace Act

/-- The fast application of a gate (`apply`, by primitive recursion). -/
def applyF : Act ℤ → LMat ℤ → LMat ℤ
  | perm π, M => permF π M
  | signs σ, M => signF σ M
  | dense L, M => mulF L M

/-- A gate fits `n` rows: a permutation's indices are below `n`, a sign gate
has `n` signs, a dense gate's rows have at most `n` entries. -/
def WF (n : ℕ) : Act ℤ → Prop
  | perm π => ∀ i ∈ π, i < n
  | signs σ => σ.length = n
  | dense L => ∀ r ∈ L, r.length ≤ n

instance decWF (n : ℕ) : ∀ a : Act ℤ, Decidable (a.WF n)
  | perm π => inferInstanceAs (Decidable (∀ i ∈ π, i < n))
  | signs σ => inferInstanceAs (Decidable (σ.length = n))
  | dense L => inferInstanceAs (Decidable (∀ r ∈ L, r.length ≤ n))

theorem toMat_applyF (n : ℕ) {a : Act ℤ} (hwf : a.WF n) (M : LMat ℤ) :
    ListMat.toMat n (a.applyF M) = a.toMat n * ListMat.toMat n M := by
  rw [← toMat_apply]
  cases a with
  | perm π =>
    show ListMat.toMat n (permF π M) =
      ListMat.toMat n (π.map fun i => if i < n then M.getD i [] else [])
    congr 1
    rw [permF, mapR_eq]
    apply List.map_congr_left
    intro i hi
    rw [nthD_eq, if_pos (hwf i hi)]
  | signs σ =>
    ext i j
    simp only [ListMat.toMat, apply, applyF]
    rw [signF_getD σ M i (by rw [hwf]; exact i.2), getD_range_map _ _ _ i.2]
  | dense L =>
    show ListMat.toMat n (mulF L M) = ListMat.toMat n (mul n L M)
    rw [toMat_mulF n L M hwf, toMat_mul]

end Act

/-- A matrix `c ^ e • M` with `M` an integer list matrix. -/
structure SMat where
  /-- The power of the scalar. -/
  e : ℕ
  /-- The integer matrix. -/
  m : LMat ℤ

variable {R : Type*} [CommRing R]

/-- The matrix `c ^ e • M`. -/
def SMat.toMatS (n : ℕ) (c : R) (A : SMat) : Matrix (Fin n) (Fin n) R :=
  c ^ A.e • (toMat n A.m).map (Int.castRingHom R)

/-- The identity. -/
def SMat.one (n : ℕ) : SMat := ⟨0, ListMat.one n⟩

/-- A gate with scale `c ^ k` applied on the left. -/
def SMat.step (k : ℕ) (a : Act ℤ) (A : SMat) : SMat := ⟨k + A.e, a.applyF A.m⟩

theorem SMat.toMatS_one (n : ℕ) (c : R) : (SMat.one n).toMatS n c = 1 := by
  simp [SMat.toMatS, SMat.one, toMat_one, Matrix.map_one]

theorem SMat.toMatS_step (n k : ℕ) (c : R) {a : Act ℤ} (hwf : a.WF n) (A : SMat) :
    (SMat.step k a A).toMatS n c =
      (c ^ k • (a.toMat n).map (Int.castRingHom R)) * A.toMatS n c := by
  simp only [SMat.toMatS, SMat.step, Act.toMat_applyF n hwf, Matrix.map_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, pow_add]
  rw [mul_comm]

/-- The entries of an integer list matrix, cast and times `c`. -/
def scaleC (c : R) (M : LMat ℤ) : LMat R := M.map (List.map fun z : ℤ => c * Int.castRingHom R z)

theorem toMat_scaleC (n : ℕ) (c : R) (M : LMat ℤ) :
    toMat n (scaleC c M) = c • (toMat n M).map (Int.castRingHom R) := by
  ext i j
  simp only [toMat, scaleC, Matrix.smul_apply, Matrix.map_apply, List.getD_eq_getElem?_getD,
    List.getElem?_map, smul_eq_mul]
  cases hM : M[(i : ℕ)]? with
  | none => simp
  | some r => cases hr : r[(j : ℕ)]? <;> simp [hr]

/-- The entries of a list matrix times `k`. -/
def scaleM (k : ℤ) (M : LMat ℤ) : LMat ℤ := M.map (List.map (k * ·))

theorem toMat_scaleM_map (n : ℕ) (k : ℤ) (M : LMat ℤ) :
    (toMat n (scaleM k M)).map (Int.castRingHom R) =
      (k : R) • (toMat n M).map (Int.castRingHom R) := by
  ext i j
  simp only [toMat, scaleM, Matrix.smul_apply, Matrix.map_apply, List.getD_eq_getElem?_getD,
    List.getElem?_map, smul_eq_mul]
  cases hM : M[(i : ℕ)]? with
  | none => simp
  | some r => cases hr : r[(j : ℕ)]? <;> simp [hr]

/-- Two scaled matrices are equal: the one with the smaller exponent is
scaled by `2 ^ (difference / p)` and the integer matrices compared, the
difference being a multiple of the period `p`. -/
def eqS (p : ℕ) (A B : SMat) : Bool :=
  bif Nat.ble A.e B.e then
    Nat.beq ((B.e - A.e) % p) 0 && (scaleM ((2 ^ ((B.e - A.e) / p) : ℕ) : ℤ) A.m == B.m)
  else
    Nat.beq ((A.e - B.e) % p) 0 && (scaleM ((2 ^ ((A.e - B.e) / p) : ℕ) : ℤ) B.m == A.m)

theorem toMatS_of_scale (n : ℕ) {c : R} {p : ℕ} (hc : (2 : R) * c ^ p = 1) (A B : SMat)
    (hle : A.e ≤ B.e) (hmod : (B.e - A.e) % p = 0)
    (hm : scaleM ((2 ^ ((B.e - A.e) / p) : ℕ) : ℤ) A.m = B.m) :
    A.toMatS n c = B.toMatS n c := by
  set q := (B.e - A.e) / p with hqdef
  have hdiv : p * q = B.e - A.e := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)
  have hq : B.e = A.e + p * q := by omega
  unfold SMat.toMatS
  rw [← hm, toMat_scaleM_map, hq, pow_add, pow_mul, smul_smul]
  congr 1
  rw [Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat, mul_assoc, ← mul_pow, mul_comm (c ^ p) 2,
    hc, one_pow, mul_one]

theorem eqS_sound (n : ℕ) {c : R} {p : ℕ} (hc : (2 : R) * c ^ p = 1) {A B : SMat}
    (h : eqS p A B = true) : A.toMatS n c = B.toMatS n c := by
  unfold eqS at h
  cases hle : Nat.ble A.e B.e <;> rw [hle] at h <;>
    simp only [cond_true, cond_false, Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at h
  · have hle' : B.e ≤ A.e := by
      have : ¬ A.e ≤ B.e := fun h' => by rw [Nat.ble_eq_true_of_le h'] at hle; cases hle
      omega
    exact (toMatS_of_scale n hc B A hle' h.1 h.2).symm
  · exact toMatS_of_scale n hc A B (Nat.le_of_ble_eq_true hle) h.1 h.2


/-! ### Words of gates -/

section Words

variable {X : Type*}

/-- The scaled integer matrix of a word, each letter given by its row
operation and scale. -/
def evalSM (n : ℕ) (sc : X → ℕ) (act : X → Act ℤ) (l : List X) : SMat :=
  l.foldr (fun g A => SMat.step (sc g) (act g) A) (SMat.one n)

theorem toMatS_evalSM (n : ℕ) (c : R) (sc : X → ℕ) (act : X → Act ℤ)
    (F : X → Matrix (Fin n) (Fin n) R) (l : List X) (hwf : ∀ g ∈ l, (act g).WF n)
    (hF : ∀ g ∈ l, F g = c ^ sc g • ((act g).toMat n).map (Int.castRingHom R)) :
    (l.map F).prod = (evalSM n sc act l).toMatS n c := by
  induction l with
  | nil => simp [evalSM, SMat.toMatS_one]
  | cons g l ih =>
    rw [List.map_cons, List.prod_cons,
      ih (fun g hg => hwf g (List.mem_cons_of_mem _ hg)) (fun g hg => hF g (List.mem_cons_of_mem _ hg)),
      show evalSM n sc act (g :: l) = SMat.step (sc g) (act g) (evalSM n sc act l) from rfl,
      SMat.toMatS_step n _ _ (hwf g (List.mem_cons_self ..)), hF g (List.mem_cons_self ..)]

end Words

end Fast

end QCert.ListMat
