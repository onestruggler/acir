/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Li, Ross, Selinger (2021): relations on a relation's own indices

A relation of Table 1 involves at most eight indices `f 0, …, f (m-1)` of
`n` (`f` injective).  Each of its generators is a level matrix along `f`
of a level matrix on `m` local indices (`Loc.glob`), so the product of a
side is the level matrix along `f` of a product of `m × m` rational
matrices, which the kernel evaluates as list matrices (`prod_eq_of_loc`).
-/
import QCert.LiRossSelinger.Semantics
import QCert.LiRossSelinger.ListMat
import QCert.LiRossSelinger.LevelLemmas

namespace QCert.LiRossSelinger

open Matrix QCert.ListMat

/-- The `1 × 1` matrix `−1` as a list. -/
def lNeg : LMat ℚ := [[-1]]

/-- `X` as a list. -/
def lX : LMat ℚ := [[0, 1], [1, 0]]

/-- `K` as a list. -/
def lK : LMat ℚ := [[1/2, 1/2, 1/2, 1/2], [1/2, -1/2, 1/2, -1/2], [1/2, 1/2, -1/2, -1/2],
  [1/2, -1/2, -1/2, 1/2]]

theorem matNeg_eq : matNeg = (ListMat.toMat 1 lNeg).map (Rat.castHom ℝ) := by
  ext i j; fin_cases i; fin_cases j; simp [matNeg, lNeg, ListMat.toMat]

theorem matX_eq : matX = (ListMat.toMat 2 lX).map (Rat.castHom ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matX, lX, ListMat.toMat]

theorem matK_eq : matK = (ListMat.toMat 4 lK).map (Rat.castHom ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [matK, lK, ListMat.toMat]

/-- A generator on the local indices `0, …, m-1`. -/
inductive Loc where
  | neg (p : ℕ)
  | x (p q : ℕ)
  | k (p q r s : ℕ)

/-- The local matrix of a generator on `m` local indices. -/
def Loc.mat (m : ℕ) : Loc → LMat ℚ
  | .neg p => level m [p] lNeg
  | .x p q => level m [p, q] lX
  | .k p q r s => level m [p, q, r, s] lK

variable {n m : ℕ}

/-- A local generator moved to the indices `f 0, …, f (m-1)`. -/
noncomputable def Loc.glob (f : Fin m → Fin n) (l : Loc) : Matrix (Fin n) (Fin n) ℝ :=
  levelMat f ((ListMat.toMat m (l.mat m)).map (Rat.castHom ℝ))

theorem glob_level {k : ℕ} (f : Fin m → Fin n) (g : Fin k → Fin m) (hg : Function.Injective g)
    (M : LMat ℚ) (idx : List ℕ) (hidx : idx = List.ofFn fun t => (g t : ℕ)) :
    levelMat f ((ListMat.toMat m (level m idx M)).map (Rat.castHom ℝ)) =
      levelMat (f ∘ g) ((ListMat.toMat k M).map (Rat.castHom ℝ)) := by
  rw [hidx, toMat_level g hg, levelMat_map, levelMat_comp]

theorem genMat_neg_loc (f : Fin m → Fin n) (p : ℕ) (hp : p < m) (a : Fin n)
    (ha : f ⟨p, hp⟩ = a) : genMat (Gen.neg a) = (Loc.neg p).glob f := by
  rw [Loc.glob, Loc.mat, glob_level f ![⟨p, hp⟩] (fun i j _ => Subsingleton.elim i j) lNeg _
    (by simp), ← matNeg_eq, genMat]
  congr 1; funext i; fin_cases i; simp [ha]

theorem genMat_x_loc (f : Fin m → Fin n) (p q : ℕ) (hp : p < m) (hq : q < m) (hpq : p ≠ q)
    (a b : Fin n) (hab : a < b) (ha : f ⟨p, hp⟩ = a) (hb : f ⟨q, hq⟩ = b) :
    genMat (Gen.x a b hab) = (Loc.x p q).glob f := by
  have hg : Function.Injective ![(⟨p, hp⟩ : Fin m), ⟨q, hq⟩] := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
  rw [Loc.glob, Loc.mat, glob_level f _ hg lX _ (by simp), ← matX_eq, genMat]
  congr 1; funext i; fin_cases i <;> simp [ha, hb]

theorem genMat_k_loc (f : Fin m → Fin n) (p q r s : ℕ) (hp : p < m) (hq : q < m) (hr : r < m)
    (hs : s < m) (hd : [p, q, r, s].Nodup) (a b c d : Fin n) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (ha : f ⟨p, hp⟩ = a) (hb : f ⟨q, hq⟩ = b) (hc : f ⟨r, hr⟩ = c)
    (hd' : f ⟨s, hs⟩ = d) : genMat (Gen.k a b c d hab hbc hcd) = (Loc.k p q r s).glob f := by
  have hg : Function.Injective ![(⟨p, hp⟩ : Fin m), ⟨q, hq⟩, ⟨r, hr⟩, ⟨s, hs⟩] := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hd
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
  rw [Loc.glob, Loc.mat, glob_level f _ hg lK _ (by simp), ← matK_eq, genMat]
  congr 1; funext i; fin_cases i <;> simp [ha, hb, hc, hd']

/-- The product of the matrices of a list of generators that are local
generators moved along `f`, decided on the local matrices. -/
theorem prod_eq_of_loc (f : Fin m → Fin n) (hf : Function.Injective f) {u v : List (Gen n)}
    (lu lv : List Loc) (hu : u.map genMat = lu.map (Loc.glob f))
    (hv : v.map genMat = lv.map (Loc.glob f))
    (h : ListMat.prod m (lu.map (Loc.mat m)) = ListMat.prod m (lv.map (Loc.mat m))) :
    (u.map genMat).prod = (v.map genMat).prod := by
  have e : ∀ l : List Loc, (l.map (Loc.glob f)).prod =
      levelMat f ((ListMat.toMat m (ListMat.prod m (l.map (Loc.mat m)))).map (Rat.castHom ℝ)) := by
    intro l
    induction l with
    | nil =>
      rw [List.map_nil, List.prod_nil, List.map_nil, show ListMat.prod m [] = one m from rfl,
        toMat_one, Matrix.map_one _ (map_zero _) (map_one _), levelMat_one]
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons,
        show ListMat.prod m (a.mat m :: l.map (Loc.mat m)) =
          mul m (a.mat m) (ListMat.prod m (l.map (Loc.mat m))) from rfl,
        toMat_mul, Matrix.map_mul, Loc.glob, levelMat_mul hf]
  rw [hu, hv, e, e, h]

end QCert.LiRossSelinger
