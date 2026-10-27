/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: generators as words of basic generators

Lemma 30 (a), (b): each generator is equal, modulo Table 3.1, to a word of
basic generators of the same extent, by the decompositions of its proof
(indices from `0`):

* `X_[j,k] ≈ X_[k-1,k] X_[j,k-1] X_[k-1,k]` for `j < k - 1`, from (13) and
  (3);
* `ω_[ι] ≈ X_[0,ι] ω_[0] X_[0,ι]` for `ι > 0`, from (10);
* `H_[0,k] ≈ X_[1,k] H_[0,1] X_[1,k]` for `k > 1`, from (15);
* `H_[j,k] ≈ X_[0,j] H_[0,k] X_[0,j]` for `0 < j < k`, from (14).
-/
import QCert.Greylyn.Pres
import QCert.Greylyn.Induction

namespace QCert.Greylyn

variable {n : ℕ}

/-- `X_[j, j+d+1]` as a word of basic generators. -/
def bXd : (j d : ℕ) → j + d + 1 < n → Word (Gen n)
  | j, 0, _ => X ⟨j, by omega⟩ ⟨j + 1, by omega⟩ (Fin.mk_lt_mk.2 (Nat.lt_succ_self j))
  | j, d + 1, h =>
    X ⟨j + d + 1, by omega⟩ ⟨j + (d + 1) + 1, h⟩ (Fin.mk_lt_mk.2 (by omega)) *
      bXd j d (by omega) *
      X ⟨j + d + 1, by omega⟩ ⟨j + (d + 1) + 1, h⟩ (Fin.mk_lt_mk.2 (by omega))

theorem bXd_basic : ∀ (j d : ℕ) (h : j + d + 1 < n), AllBasic (bXd j d h)
  | j, 0, h => by
    intro x hx
    simp only [bXd, X, FreeMonoid.toList_of, List.mem_singleton] at hx
    subst hx; rfl
  | j, d + 1, h => by
    intro x hx
    simp only [bXd, X, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
      List.mem_singleton] at hx
    rcases hx with (rfl | hx) | rfl
    · rfl
    · exact bXd_basic j d (by omega) x hx
    · rfl

theorem cl_bXd : ∀ (j d : ℕ) (h : j + d + 1 < n),
    cl (bXd j d h) = gX ⟨j, by omega⟩ ⟨j + d + 1, h⟩ (Fin.mk_lt_mk.2 (by omega))
  | j, 0, h => rfl
  | j, d + 1, h => by
    rw [bXd, map_mul, map_mul, cl_bXd j d (by omega), cl_X]
    have e := e13 (n := n) ⟨j + d + 1, by omega⟩ ⟨j + (d + 1) + 1, h⟩ ⟨j, by omega⟩
      (Fin.mk_lt_mk.2 (by omega)) (Fin.mk_lt_mk.2 (by omega))
    have e' := e3 (n := n) ⟨j + d + 1, by omega⟩ ⟨j + (d + 1) + 1, h⟩
      (Fin.mk_lt_mk.2 (by omega))
    rw [e, mul_assoc, e', mul_one]

/-- `X_[j,k]` as a word of basic generators. -/
def bX (j k : Fin n) (h : j < k) : Word (Gen n) :=
  bXd j (k - j - 1) (by have := k.2; have : (j : ℕ) < k := h; omega)

theorem bX_basic (j k : Fin n) (h : j < k) : AllBasic (bX j k h) := bXd_basic _ _ _

theorem cl_bX (j k : Fin n) (h : j < k) : cl (bX j k h) = gX j k h := by
  rw [bX, cl_bXd]
  have : (j : ℕ) < k := h
  exact gX_congr rfl (Fin.ext (by simp; omega))

/-- A basic word of a generator (Lemma 30). -/
def bw : Gen n → Word (Gen n)
  | .X j k h => bX j k h
  | .ω j =>
    if hj : (j : ℕ) = 0 then ω j
    else bX ⟨0, j.pos⟩ j (Fin.mk_lt_mk.2 (by omega)) * ω ⟨0, j.pos⟩ *
      bX ⟨0, j.pos⟩ j (Fin.mk_lt_mk.2 (by omega))
  | .H j k h =>
    if hj : (j : ℕ) = 0 then
      if hk : (k : ℕ) = 1 then H j k h
      else bX ⟨1, by have := k.2; have : (j : ℕ) < k := h; omega⟩ k
          (Fin.mk_lt_mk.2 (by have : (j : ℕ) < k := h; omega)) *
        H ⟨0, j.pos⟩ ⟨1, by have := k.2; have : (j : ℕ) < k := h; omega⟩ (by simp) *
        bX ⟨1, by have := k.2; have : (j : ℕ) < k := h; omega⟩ k
          (Fin.mk_lt_mk.2 (by have : (j : ℕ) < k := h; omega))
    else bX ⟨0, j.pos⟩ j (Fin.mk_lt_mk.2 (by omega)) *
      (bX ⟨1, by have := k.2; have : (j : ℕ) < k := h; omega⟩ k
          (Fin.mk_lt_mk.2 (by have : (j : ℕ) < k := h; omega)) *
        H ⟨0, j.pos⟩ ⟨1, by have := k.2; have : (j : ℕ) < k := h; omega⟩ (by simp) *
        bX ⟨1, by have := k.2; have : (j : ℕ) < k := h; omega⟩ k
          (Fin.mk_lt_mk.2 (by have : (j : ℕ) < k := h; omega))) *
      bX ⟨0, j.pos⟩ j (Fin.mk_lt_mk.2 (by omega))

theorem AllBasic.mul {a b : Word (Gen n)} (ha : AllBasic a) (hb : AllBasic b) :
    AllBasic (a * b) := by
  intro x hx
  rw [FreeMonoid.toList_mul, List.mem_append] at hx
  rcases hx with hx | hx
  · exact ha x hx
  · exact hb x hx

theorem AllBasic.of {x : Gen n} (h : Basic x) : AllBasic (FreeMonoid.of x) := by
  intro y hy
  rw [FreeMonoid.toList_of, List.mem_singleton] at hy
  subst hy; exact h

theorem bw_basic (y : Gen n) : AllBasic (bw y) := by
  cases y with
  | X j k h => exact bX_basic j k h
  | ω j =>
    simp only [bw]
    split_ifs with hj
    · exact AllBasic.of hj
    · refine ((bX_basic _ _ _).mul (AllBasic.of ?_)).mul (bX_basic _ _ _); rfl
  | H j k h =>
    simp only [bw]
    split_ifs with hj hk
    · exact AllBasic.of ⟨hj, hk⟩
    · refine ((bX_basic _ _ _).mul (AllBasic.of ?_)).mul (bX_basic _ _ _); exact ⟨rfl, rfl⟩
    · refine ((bX_basic _ _ _).mul (((bX_basic _ _ _).mul (AllBasic.of ?_)).mul
        (bX_basic _ _ _))).mul (bX_basic _ _ _); exact ⟨rfl, rfl⟩

/-- `H_[0,k] ≈ X_[1,k] H_[0,1] X_[1,k]`, from (15). -/
theorem gH_zero (z o k : Fin n) (hzo : z < o) (hok : o < k) :
    gH z k (hzo.trans hok) = gX o k hok * gH z o hzo * gX o k hok :=
  eq_conj_of_comm' (e3 o k hok) (e15 o k z hzo hok)

/-- `H_[j,k] ≈ X_[0,j] H_[0,k] X_[0,j]`, from (14). -/
theorem gH_pos (z j k : Fin n) (hzj : z < j) (hjk : j < k) :
    gH j k hjk = gX z j hzj * gH z k (hzj.trans hjk) * gX z j hzj :=
  eq_conj_of_comm' (e3 z j hzj) (e14 z j k hzj hjk)

/-- `ω_[ι] ≈ X_[0,ι] ω_[0] X_[0,ι]`, from (10). -/
theorem gω_pos (z j : Fin n) (hzj : z < j) : gω j = gX z j hzj * gω z * gX z j hzj :=
  eq_conj_of_comm (e3 z j hzj) (e10 z j hzj)

theorem cl_bw (y : Gen n) : cl (FreeMonoid.of y) = cl (bw y) := by
  cases y with
  | X j k h => rw [bw, cl_bX]; rfl
  | ω j =>
    simp only [bw]
    split_ifs with hj
    · rfl
    · simp only [map_mul, cl_bX, cl_ω]
      exact gω_pos _ _ _
  | H j k h =>
    simp only [bw]
    split_ifs with hj hk
    · rfl
    · simp only [map_mul, cl_bX, cl_H]
      refine (gH_congr (Fin.ext hj) rfl).trans (gH_zero _ _ _ ?_ ?_)
      · exact Fin.mk_lt_mk.2 (by omega)
      · exact Fin.mk_lt_mk.2 (by have : (j : ℕ) < k := h; omega)
    · simp only [map_mul, cl_bX, cl_H]
      rw [gH_pos ⟨0, j.pos⟩ j k (Fin.mk_lt_mk.2 (by omega)) h,
        gH_zero ⟨0, j.pos⟩ ⟨1, by have := k.2; have : (j : ℕ) < k := h; omega⟩ k
          (by simp) (Fin.mk_lt_mk.2 (by have : (j : ℕ) < k := h; omega))]

/-- Lemma 30 (a): every generator is equal to a word of basic generators. -/
theorem decomp' : ∀ y : Gen n, ∃ b, AllBasic b ∧ Derivable (Rel n) (FreeMonoid.of y) b :=
  fun y => ⟨bw y, bw_basic y, derivable_iff.2 (cl_bw y)⟩

end QCert.Greylyn
