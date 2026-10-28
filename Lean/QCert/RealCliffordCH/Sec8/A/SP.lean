/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Signed permutations: the semantics of Hadamard-free words

A Hadamard-free letter of `𝒫_N` (no `H_[a,b]H_[c,d]`) is a signed
permutation matrix: column `j` is `± e_{π j}`.  `SP N` records `π` and the
signs; the product is that of the matrices (`spMat_mul`), the matrix of a
proper Hadamard-free word is that of its signed permutation (`pWord_eq_spMat`),
and over `ℝ` the matrix determines the signed permutation (`spMat_inj`).
The equations of Figure 8 between Hadamard-free words hold for signed
permutations (`spW_sound`), so derivations `DH` preserve them (`DH.spW`).
-/
import QCert.RealCliffordCH.Sec8.A.Deriv

namespace QCert.RealCliffordCH.Sec8

open Matrix

/-- A signed permutation: column `j` is `e_{perm j}`, negated when `neg j`. -/
@[ext] structure SP (N : ℕ) where
  perm : Fin N → Fin N
  neg : Fin N → Bool

namespace SP

variable {N : ℕ}

instance : Mul (SP N) := ⟨fun A B => ⟨A.perm ∘ B.perm, fun j => xor (A.neg (B.perm j)) (B.neg j)⟩⟩

instance : One (SP N) := ⟨⟨id, fun _ => false⟩⟩

@[simp] theorem mul_perm (A B : SP N) (j : Fin N) : (A * B).perm j = A.perm (B.perm j) := rfl

@[simp] theorem mul_neg (A B : SP N) (j : Fin N) :
    (A * B).neg j = xor (A.neg (B.perm j)) (B.neg j) := rfl

@[simp] theorem one_perm (j : Fin N) : (1 : SP N).perm j = j := rfl

@[simp] theorem one_neg (j : Fin N) : (1 : SP N).neg j = false := rfl

instance : Monoid (SP N) where
  mul_assoc A B C := SP.ext rfl (funext fun j => by simp [Bool.xor_assoc])
  one_mul A := SP.ext rfl (funext fun j => by simp)
  mul_one A := SP.ext rfl (funext fun j => by simp)

end SP

variable {N : ℕ}

/-- The signed permutation of a Hadamard-free letter (`1` for `H_[a,b]H_[c,d]`). -/
def spL : PG N → SP N
  | .zz a c => ⟨id, fun j => xor (decide (j = a)) (decide (j = c))⟩
  | .zx a c d => ⟨Equiv.swap c d, fun j => decide (Equiv.swap c d j = a)⟩
  | .xx a b c d => ⟨Equiv.swap a b ∘ Equiv.swap c d, fun _ => false⟩
  | .hh _ _ _ _ => 1

/-- The signed permutation of a word. -/
def spW : Word (PG N) →* SP N := FreeMonoid.lift spL

theorem spW_wordOf (l : List (PG N)) : spW (wordOf l) = (l.map spL).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [wordOf, FreeMonoid.ofList_cons, map_mul, ← wordOf, ih, spW, FreeMonoid.lift_eval_of]
    rfl

/-! ## Matrices -/

/-- The matrix of a signed permutation. -/
def spMat {R : Type*} [CommRing R] (A : SP N) : Matrix (Fin N) (Fin N) R :=
  fun i j => if i = A.perm j then (if A.neg j then -1 else 1) else 0

section Ring

variable {R : Type*} [CommRing R]

theorem spMat_mul (A B : SP N) : (spMat (A * B) : Matrix _ _ R) = spMat A * spMat B := by
  ext i j
  rw [mul_apply, Finset.sum_eq_single (B.perm j)]
  · simp only [spMat, SP.mul_perm, SP.mul_neg, if_pos rfl]
    by_cases h : i = A.perm (B.perm j)
    · simp only [h, if_true]
      rcases Bool.eq_false_or_eq_true (A.neg (B.perm j)) with ha | ha <;>
        rcases Bool.eq_false_or_eq_true (B.neg j) with hb | hb <;> simp [ha, hb]
    · simp [h]
  · intro k _ hk; simp only [spMat, if_neg hk, mul_zero]
  · simp

theorem spMat_one : (spMat (1 : SP N) : Matrix _ _ R) = 1 := by
  ext i j; simp [spMat, one_apply]

theorem negM_apply' (a i j : Fin N) :
    (negM a : Matrix (Fin N) (Fin N) R) i j = if i = j then (if i = a then -1 else 1) else 0 := by
  have hf : Function.Injective ![a] := fun x y _ => Subsingleton.elim x y
  unfold negM
  by_cases hi : i = a
  · by_cases hj : j = a
    · subst hi hj
      have := levelMat_apply_apply hf (!![-1] : Matrix (Fin 1) (Fin 1) R) 0 0
      simpa using this
    · rw [levelMat_apply_of_right _ _ (fun l => by fin_cases l; exact Ne.symm hj)]
      simp [one_apply, hi, Ne.symm hj, hj]
  · rw [levelMat_apply_of_left _ (fun l => by fin_cases l; exact Ne.symm hi)]
    simp [one_apply, hi]

theorem xM_apply {c d : Fin N} (hcd : c ≠ d) (i j : Fin N) :
    (xM c d : Matrix (Fin N) (Fin N) R) i j = if i = Equiv.swap c d j then 1 else 0 := by
  have hf : Function.Injective ![c, d] := by
    intro x y h; fin_cases x <;> fin_cases y <;> simp_all [Ne.symm hcd]
  unfold xM
  have key : ∀ k l : Fin 2, levelMat ![c, d] (!![0, 1; 1, 0] : Matrix _ _ R) (![c, d] k) (![c, d] l) =
      (!![0, 1; 1, 0] : Matrix _ _ R) k l := levelMat_apply_apply hf _
  by_cases hj : j = c ∨ j = d
  · by_cases hi : i = c ∨ i = d
    · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · have := key 0 0; simp at this; simp [this, Equiv.swap_apply_left, hcd]
      · have := key 0 1; simp at this; simp [this, Equiv.swap_apply_right]
      · have := key 1 0; simp at this; simp [this, Equiv.swap_apply_left]
      · have := key 1 1; simp at this; simp [this, Equiv.swap_apply_right, Ne.symm hcd]
    · push_neg at hi
      rw [levelMat_apply_of_left _ (fun l => by fin_cases l <;> simp [Ne.symm hi.1, Ne.symm hi.2])]
      rcases hj with rfl | rfl <;> simp [one_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
        hi.1, hi.2]
  · push_neg at hj
    rw [levelMat_apply_of_right _ _ (fun l => by fin_cases l <;> simp [Ne.symm hj.1, Ne.symm hj.2])]
    simp [one_apply, Equiv.swap_apply_of_ne_of_ne hj.1 hj.2]

/-- The matrix of a proper Hadamard-free letter is that of its signed
permutation. -/
theorem pMat_eq_spMat (σ : R) {x : PG N} (hx : x.HF) (hp : x.Proper) :
    pMat σ x = spMat (spL x) := by
  cases x with
  | zz a c =>
    ext i j
    rw [show pMat σ (PG.zz a c) = (negM a * negM c : Matrix (Fin N) (Fin N) R) from rfl, mul_apply, Finset.sum_eq_single j
      (fun k _ hk => by rw [negM_apply' c k j, if_neg hk, mul_zero]) (by simp)]
    rw [negM_apply', negM_apply']
    simp only [spMat, spL, id, if_pos rfl]
    split_ifs <;> simp_all
  | zx a c d =>
    ext i j
    rw [show pMat σ (PG.zx a c d) = (negM a * xM c d : Matrix (Fin N) (Fin N) R) from rfl,
      mul_apply, Finset.sum_eq_single i
      (fun k _ hk => by rw [negM_apply' a i k, if_neg (Ne.symm hk), zero_mul]) (by simp)]
    rw [negM_apply', xM_apply hp]
    simp only [spMat, spL, if_pos rfl]
    split_ifs <;> simp_all
  | xx a b c d =>
    ext i j
    rw [show pMat σ (PG.xx a b c d) = (xM a b * xM c d : Matrix (Fin N) (Fin N) R) from rfl,
      mul_apply, Finset.sum_eq_single (Equiv.swap c d j)
      (fun k _ hk => by rw [xM_apply hp.2 k j, if_neg hk, mul_zero]) (by simp)]
    rw [xM_apply hp.1, xM_apply hp.2]
    simp [spMat, spL]
  | hh a b c d => exact absurd hx id

theorem pWord_eq_spMat (σ : R) (w : Word (PG N)) (hf : ∀ x ∈ w.toList, x.HF) (hp : ProperW w) :
    pWord σ w = spMat (spW w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one, map_one, spMat_one]
  | mul_of x w ih =>
    have hx : x ∈ (FreeMonoid.of x * w).toList := by simp
    rw [map_mul, map_mul, spMat_mul, ih (fun y hy => hf y (by simp [hy]))
      (fun y hy => hp y (by simp [hy])), pWord, FreeMonoid.lift_eval_of,
      pMat_eq_spMat σ (hf x hx) (hp x hx), spW, FreeMonoid.lift_eval_of]

end Ring

theorem spMat_inj {A B : SP N} (h : (spMat A : Matrix (Fin N) (Fin N) ℝ) = spMat B) : A = B := by
  have col : ∀ j, A.perm j = B.perm j ∧ A.neg j = B.neg j := by
    intro j
    have e := congrFun (congrFun h (A.perm j)) j
    simp only [spMat, if_true] at e
    by_cases hp : A.perm j = B.perm j
    · refine ⟨hp, ?_⟩
      rw [if_pos hp] at e
      cases ha : A.neg j <;> cases hb : B.neg j <;> simp only [ha, hb] at e ⊢ <;>
        first | rfl | (norm_num at e)
    · rw [if_neg hp] at e
      cases ha : A.neg j <;> simp only [ha] at e <;> norm_num at e
  exact SP.ext (funext fun j => (col j).1) (funext fun j => (col j).2)

end QCert.RealCliffordCH.Sec8
