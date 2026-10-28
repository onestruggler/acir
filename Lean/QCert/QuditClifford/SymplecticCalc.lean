/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Computing the symplectic action

The action of a shifted circuit is the action on the wires above wire 0
(`σC_shift`); the action of a padded circuit is the action on the bottom
wires (`σC_pad`); on one wire, `H`, `S^k` and the Paulis `X`, `Z` act as
`(a, b) ↦ (-b, a)`, `(a, b) ↦ (a, b + k a)` and trivially.
-/
import QCert.QuditClifford.Pad
import QCert.QuditClifford.Pauli

namespace QCert.QuditClifford

variable (p : ℕ) [hp : Fact p.Prime]

theorem σC_shift {n : ℕ} (w : Circ n) (v : V p (n + 1)) :
    σC p (n + 1) (Circuit.shift w) v = Fin.cons (v 0) (σC p n w (Fin.tail v)) := by
  induction w using FreeMonoid.inductionOn' generalizing v with
  | one => exact (Fin.cons_self_tail v).symm
  | mul_of y w ih =>
    simp only [map_mul, Circuit.shift_of, Function.End.mul_def, Function.comp_apply, ih, σC_of]
    simp [σGen]

omit hp in
/-- The bottom `k` coordinates of a vector on `n + k` wires. -/
def low {n k : ℕ} (v : V p (n + k)) : V p k := fun j => v ⟨j, by omega⟩

omit hp in
/-- A vector on `n + k` wires with its bottom `k` coordinates replaced. -/
def withLow {n k : ℕ} (u : V p k) (v : V p (n + k)) : V p (n + k) :=
  fun i => if h : (i : ℕ) < k then u ⟨i, h⟩ else v i

omit hp in
theorem low_withLow {n k : ℕ} (u : V p k) (v : V p (n + k)) : low p (withLow p u v) = u := by
  funext j; simp [low, withLow, j.isLt]

omit hp in
theorem withLow_low {n k : ℕ} (v : V p (n + k)) : withLow p (low p v) v = v := by
  funext i; simp only [withLow, low]; split_ifs <;> rfl

omit hp in
theorem withLow_withLow {n k : ℕ} (u u' : V p k) (v : V p (n + k)) :
    withLow p u (withLow p u' v) = withLow p u v := by
  funext i; simp only [withLow]; split_ifs <;> rfl

theorem σGen_pad (n : ℕ) : {k : ℕ} → (x : Gen Gate k) → (v : V p (n + k)) →
    σGen p (Gen.pad n x) v = withLow p (σGen p x (low p v)) v
  | _, .gate0 c, v => by simp [Gen.pad, σGen, withLow_low]
  | _, .gate1 (n := j) c, v => by
    funext i
    simp only [Gen.pad, σGen]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [withLow, low]
    · simp only [withLow, low, Function.update_apply, Fin.succ_ne_zero, if_false, Fin.val_succ]
      split_ifs with h1 h2
      · exact absurd (congrArg Fin.val h2) (by simp)
      · rfl
      · rfl
  | _, .gate2 (n := j) .CZ, v => by
    funext i
    simp only [Gen.pad, σGen]
    have e1 : 1 % (n + (j + 2)) = 1 := Nat.mod_eq_of_lt (by omega)
    have e1' : 1 % (j + 2) = 1 := Nat.mod_eq_of_lt (by omega)
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · simp [withLow, low]
    · simp [withLow, low, Function.update_apply, e1, e1']
    · simp only [withLow, low, Function.update_apply, Fin.val_succ]
      have a1 : (i.succ.succ : Fin (n + j + 2)) ≠ 1 := fun h => by
        have := congrArg Fin.val h; simp at this
      have a0 : (i.succ.succ : Fin (n + j + 2)) ≠ 0 := Fin.succ_ne_zero _
      rw [if_neg a1, if_neg a0]
      split_ifs with h1 h2 h3
      · exact absurd (congrArg Fin.val h2) (by simp)
      · exact absurd (congrArg Fin.val h3) (by simp)
      · rfl
      · rfl
  | _, .gate3 c, _ => nomatch c
  | _, .up (n := j) x, v => by
    funext i
    have ih := σGen_pad n x (Fin.tail v)
    simp only [Gen.pad, σGen]
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [withLow, low]
    · rw [Fin.cons_succ, ih]
      simp only [withLow, low, Fin.tail, Fin.val_succ]
      by_cases hi : (i' : ℕ) < j
      · rw [dif_pos hi, dif_pos (by omega)]
        have : (⟨(i' : ℕ) + 1, by omega⟩ : Fin (j + 1)) = Fin.succ ⟨i', hi⟩ := rfl
        rw [this, Fin.cons_succ]
        rfl
      · rw [dif_neg hi, dif_neg (by omega)]

/-- A circuit on the bottom `k` wires acts on the bottom `k` coordinates. -/
theorem σC_pad (n : ℕ) {k : ℕ} (w : Circ k) (v : V p (n + k)) :
    σC p (n + k) (Circuit.pad n w) v = withLow p (σC p k w (low p v)) v := by
  induction w using FreeMonoid.inductionOn' generalizing v with
  | one => exact (withLow_low p v).symm
  | mul_of y w ih =>
    simp only [map_mul, Function.End.mul_def, Function.comp_apply]
    rw [ih, show Circuit.pad n (FreeMonoid.of y) = FreeMonoid.of (Gen.pad n y) from rfl, σC_of, σC_of,
      σGen_pad, low_withLow, withLow_withLow]

/-! ### One wire -/

omit hp in
theorem V1_ext {u v : V p 1} (h : u 0 = v 0) : u = v := funext fun i => by
  rw [Subsingleton.elim i 0, h]

theorem σC_H (v : V p 1) : σC p 1 H v = fun _ => (-(v 0).2, (v 0).1) := by
  apply V1_ext; simp [H, σC_of, σGen, act1]

theorem σC_S (v : V p 1) : σC p 1 S v = fun _ => ((v 0).1, (v 0).1 + (v 0).2) := by
  apply V1_ext; simp [S, σC_of, σGen, act1]

theorem σC_S_pow (k : ℕ) (v : V p 1) :
    σC p 1 (S ^ k) v = fun _ => ((v 0).1, (v 0).2 + k * (v 0).1) := by
  induction k generalizing v with
  | zero => apply V1_ext; simp; rfl
  | succ k ih =>
    apply V1_ext
    rw [pow_succ, map_mul, Function.End.mul_def, Function.comp_apply, σC_S, ih]
    simp only [Prod.mk.injEq, true_and]; push_cast; ring

theorem σC_X : σC p 1 (X p) = 1 := by
  funext v; apply V1_ext
  simp only [X, seq_def, map_mul, Function.End.mul_def, Function.comp_apply, pow_two, σC_H, σC_S,
    σC_S_pow, natCast_pred]
  show _ = v 0
  ext <;> simp

theorem σC_Z : σC p 1 (Z p) = 1 := by
  funext v; apply V1_ext
  simp only [Z, seq_def, map_mul, Function.End.mul_def, Function.comp_apply, pow_two, σC_H, σC_S,
    σC_S_pow, natCast_pred]
  show _ = v 0
  ext <;> simp

theorem σC_negω {n : ℕ} : σC p n negω = 1 := by
  simp [negω, σC_of, σGen]; rfl

theorem σC_onWire {n : ℕ} (i : Fin n) {c : Circ 1} (hc : σC p 1 c = 1) : σC p n (onWire n i c) = 1 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero =>
      funext v
      show σC p (n + 1) (Circuit.pad n c) v = v
      rw [σC_pad, hc]; exact withLow_low p v
    | succ i =>
      funext v
      show σC p (n + 1) (Circuit.shift (onWire n ⟨i, by omega⟩ c)) v = v
      rw [σC_shift, ih]
      exact Fin.cons_self_tail v

end QCert.QuditClifford
