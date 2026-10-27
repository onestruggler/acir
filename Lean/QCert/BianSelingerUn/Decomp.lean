/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: generators as words of basic generators

Lemma 3.4: each generator is a word of basic generators, by
`i_[j] ∼ X_[0,j] i_[0] X_[0,j]`, `K_[j,ℓ] ∼ X_[0,j] K_[0,ℓ] X_[0,j]`,
`K_[0,ℓ] ∼ X_[1,ℓ] K_[0,1] X_[1,ℓ]` and
`X_[j,ℓ] ∼ X_[j,j+1] X_[j+1,ℓ] X_[j,j+1]`, from (10), (13), (14), (11)
and (2).
-/
import QCert.BianSelingerUn.Pres
import QCert.BianSelingerUn.Induction

namespace QCert.BianSelingerUn

variable {n : ℕ}

/-- `X_[a, a+d+1]` as a word of basic generators. -/
def bXd : (a d : ℕ) → a + d + 1 < n → Word (Gen n)
  | a, 0, h => X ⟨a, by omega⟩ ⟨a + 1, by omega⟩ (Fin.mk_lt_mk.2 (Nat.lt_succ_self a))
  | a, d + 1, h =>
    X ⟨a, by omega⟩ ⟨a + 1, by omega⟩ (Fin.mk_lt_mk.2 (Nat.lt_succ_self a)) *
      bXd (a + 1) d (by omega) *
      X ⟨a, by omega⟩ ⟨a + 1, by omega⟩ (Fin.mk_lt_mk.2 (Nat.lt_succ_self a))

theorem bXd_basic : ∀ (a d : ℕ) (h : a + d + 1 < n), AllBasic (bXd a d h)
  | a, 0, h => by
    intro x hx
    simp only [bXd, X, FreeMonoid.toList_of, List.mem_singleton] at hx
    subst hx; rfl
  | a, d + 1, h => by
    intro x hx
    simp only [bXd, X, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
      List.mem_singleton] at hx
    rcases hx with (rfl | hx) | rfl
    · rfl
    · exact bXd_basic (a + 1) d (by omega) x hx
    · rfl

theorem cl_bXd : ∀ (a d : ℕ) (h : a + d + 1 < n),
    cl (bXd a d h) = gX ⟨a, by omega⟩ ⟨a + d + 1, h⟩ (Fin.mk_lt_mk.2 (by omega))
  | a, 0, h => rfl
  | a, d + 1, h => by
    rw [bXd, map_mul, map_mul, cl_bXd (a + 1) d (by omega), cl_X]
    have e := e11 (n := n) ⟨a, by omega⟩ ⟨a + 1, by omega⟩ ⟨a + 1 + d + 1, by omega⟩
      (Fin.mk_lt_mk.2 (by omega)) (Fin.mk_lt_mk.2 (by omega))
    have e' := e2 (n := n) ⟨a, by omega⟩ ⟨a + 1, by omega⟩ (Fin.mk_lt_mk.2 (by omega))
    rw [mul_assoc, e, ← mul_assoc, e', one_mul]
    exact gX_congr rfl (Fin.ext (by simp; omega))

/-- `X_[j,k]` as a word of basic generators. -/
def bX (j k : Fin n) (h : j < k) : Word (Gen n) :=
  bXd j (k - j - 1) (by have := k.2; have : (j : ℕ) < k := h; omega)

theorem bX_basic (j k : Fin n) (h : j < k) : AllBasic (bX j k h) := bXd_basic _ _ _

theorem cl_bX (j k : Fin n) (h : j < k) : cl (bX j k h) = gX j k h := by
  rw [bX, cl_bXd]
  have : (j : ℕ) < k := h
  exact gX_congr rfl (Fin.ext (by simp; omega))

/-- A basic word of a generator (Lemma 3.4). -/
def bw : Gen n → Word (Gen n)
  | .X j k h => bX j k h
  | .i j =>
    if hj : (j : ℕ) = 0 then i j
    else bX ⟨0, j.pos⟩ j (Fin.mk_lt_mk.2 (by omega)) * i ⟨0, j.pos⟩ *
      bX ⟨0, j.pos⟩ j (Fin.mk_lt_mk.2 (by omega))
  | .K j k h =>
    if hj : (j : ℕ) = 0 then
      if hk : (k : ℕ) = 1 then K j k h
      else bX ⟨1, by omega⟩ k (Fin.mk_lt_mk.2 (by have : (j : ℕ) < k := h; omega)) *
        K ⟨0, j.pos⟩ ⟨1, by have := k.2; have : (j : ℕ) < k := h; omega⟩ (by simp) *
        bX ⟨1, by omega⟩ k (Fin.mk_lt_mk.2 (by have : (j : ℕ) < k := h; omega))
    else bX ⟨0, j.pos⟩ j (Fin.mk_lt_mk.2 (by omega)) *
      (if hk : (k : ℕ) = 1 then K ⟨0, j.pos⟩ k (Fin.mk_lt_mk.2 (by omega))
        else bX ⟨1, by have : (j : ℕ) < k := h; omega⟩ k
            (Fin.mk_lt_mk.2 (by have : (j : ℕ) < k := h; omega)) *
          K ⟨0, j.pos⟩ ⟨1, by have := k.2; have : (j : ℕ) < k := h; omega⟩ (by simp) *
          bX ⟨1, by have : (j : ℕ) < k := h; omega⟩ k
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
  | i j =>
    simp only [bw]
    split_ifs with hj
    · exact AllBasic.of hj
    · refine ((bX_basic _ _ _).mul (AllBasic.of ?_)).mul (bX_basic _ _ _); rfl
  | K j k h =>
    simp only [bw]
    split_ifs with hj hk hk
    · exact AllBasic.of ⟨hj, hk⟩
    · refine ((bX_basic _ _ _).mul (AllBasic.of ?_)).mul (bX_basic _ _ _); exact ⟨rfl, rfl⟩
    · refine ((bX_basic _ _ _).mul (AllBasic.of ?_)).mul (bX_basic _ _ _); exact ⟨rfl, hk⟩
    · refine ((bX_basic _ _ _).mul (((bX_basic _ _ _).mul (AllBasic.of ?_)).mul
        (bX_basic _ _ _))).mul (bX_basic _ _ _); exact ⟨rfl, rfl⟩

/-- `K_[0,ℓ] ∼ X_[1,ℓ] K_[0,1] X_[1,ℓ]`, from (14). -/
theorem gK_zero (z o k : Fin n) (hzo : z < o) (hok : o < k) :
    gK z k (hzo.trans hok) = gX o k hok * gK z o hzo * gX o k hok :=
  eq_conj_of_comm (e2 o k hok) (e14 z o k hzo hok)

/-- `K_[j,ℓ] ∼ X_[0,j] K_[0,ℓ] X_[0,j]`, from (13). -/
theorem gK_pos (z j k : Fin n) (hzj : z < j) (hjk : j < k) :
    gK j k hjk = gX z j hzj * gK z k (hzj.trans hjk) * gX z j hzj :=
  eq_conj_of_comm (e2 z j hzj) (e13 z j k hzj hjk)

/-- `i_[j] ∼ X_[0,j] i_[0] X_[0,j]`, from (10). -/
theorem gi_pos (z j : Fin n) (hzj : z < j) : gi j = gX z j hzj * gi z * gX z j hzj :=
  eq_conj_of_comm (e2 z j hzj) (e10 z j hzj)

theorem cl_bw (y : Gen n) : cl (FreeMonoid.of y) = cl (bw y) := by
  cases y with
  | X j k h => rw [bw, cl_bX]; rfl
  | i j =>
    simp only [bw]
    split_ifs with hj
    · rfl
    · simp only [map_mul, cl_bX, cl_i]
      exact gi_pos _ _ _
  | K j k h =>
    simp only [bw]
    split_ifs with hj hk hk
    · rfl
    · simp only [map_mul, cl_bX, cl_K]
      refine (gK_congr (Fin.ext hj) rfl).trans (gK_zero _ _ _ ?_ ?_)
      · exact Fin.mk_lt_mk.2 (by omega)
      · exact Fin.mk_lt_mk.2 (by have : (j : ℕ) < k := h; omega)
    · simp only [map_mul, cl_bX, cl_K]
      exact gK_pos _ _ _ _ _
    · simp only [map_mul, cl_bX, cl_K]
      rw [gK_pos ⟨0, j.pos⟩ j k (Fin.mk_lt_mk.2 (by omega)) h,
        gK_zero ⟨0, j.pos⟩ ⟨1, by have := k.2; have : (j : ℕ) < k := h; omega⟩ k
          (by simp) (Fin.mk_lt_mk.2 (by have : (j : ℕ) < k := h; omega))]

/-- Lemma 3.4. -/
theorem decomp' : ∀ y : Gen n, ∃ b, AllBasic b ∧ Derivable (Rel n) (FreeMonoid.of y) b :=
  fun y => ⟨bw y, bw_basic y, derivable_iff.2 (cl_bw y)⟩

end QCert.BianSelingerUn
