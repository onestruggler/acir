/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Soundness (Proposition 3.1)

Every equation of `Rule` holds in the semantics of Definition 2.3.  The
equations on at most three wires are decided over ℚ(√2) by simulation
(`Sim.check`) and carried to ℝ.  The schema (19) needs an argument at every
width: by induction on the number of controls, the multi-controlled `Z`
gate `box k` acts as the diagonal operator that is `-1` exactly when wires
`1, …, k` are all `1` (`eval_box`), so it commutes with `Z` on wire `0`.
The induction step is the recursive step of Definition 2.4 computed block
by block in the wires above the bottom three (`Block`), where each block is
one of two identities on three wires, decided.
-/
import QCert.RealCliffordCH.Sim
import QCert.RealCliffordCH.EvalLemmas
import QCert.RealCliffordCH.Block

namespace QCert.RealCliffordCH

open Matrix Circuit Sim

/-- An identity decided over ℚ(√2) holds in the semantics. -/
theorem sem_of_check {n : ℕ} {w v : Circ n} (h : check w v = true) : S.sem n w = S.sem n v :=
  S.sem_eq_of_eval QSqrt2.toR opsQ toOps_eq (eval_eq_of_check h)

/-! ## The multi-controlled `Z` gate -/

/-- The operator of the multi-controlled `Z` gate with `k` controls: `-1`
when wires `1, …, k` are all `1`. -/
def boxOp (k : ℕ) : Op Q 2 (k + 1) :=
  diagonal fun s => if ∀ i : Fin k, s i.succ = 1 then -1 else 1

/-- `Z` on wire 2 of three wires. -/
def z2Op : Op Q 2 3 := diagonal fun l => if l 2 = 1 then -1 else 1

/-- `CZ` on wires 1, 2 of three wires. -/
def cz12Op : Op Q 2 3 := diagonal fun l => if l 1 = 1 ∧ l 2 = 1 then -1 else 1

theorem eval_box_two : opsQ.eval 3 (box 2) = boxOp 2 :=
  eval_eq_of_checkM (by decide +kernel)

theorem eval_z2 : opsQ.eval 3 (shift (shift z)) = z2Op :=
  eval_eq_of_checkM (by decide +kernel)

theorem eval_cz12 : opsQ.eval 3 (shift cz) = cz12Op :=
  eval_eq_of_checkM (by decide +kernel)

/-- The recursive step of Definition 2.4 on three wires, when the wires
above are all `1`. -/
theorem step_on :
    opsQ.eval 3 (drawn [zx2, tau02, shift (shift z), tau02, xz2, tau02, shift (shift z), tau02]) =
      opsQ.eval 3 (shift cz) :=
  eval_eq_of_check (by decide +kernel)

/-- The recursive step of Definition 2.4 on three wires, when some wire
above is `0`. -/
theorem step_off :
    opsQ.eval 3 (drawn [zx2, tau02, tau02, xz2, tau02, tau02]) = opsQ.eval 3 (drawn []) :=
  eval_eq_of_check (by decide +kernel)

theorem split_symm_apply {m k : ℕ} (l : State 2 k) (h : State 2 m) (i : Fin (m + k)) :
    (split 2 m k).symm (l, h) i =
      if hi : (i : ℕ) < k then l ⟨i, hi⟩ else h ⟨i - k, by omega⟩ := rfl

theorem split_snd_apply {m k : ℕ} (s : State 2 (m + k)) (j : Fin m) :
    (split 2 m k s).2 j = s ⟨k + j, by omega⟩ := rfl

/-- The box with `k + 2` controls moved up one wire, as blocks over the wires
above the bottom three. -/
theorem onTop_boxOp (k : ℕ) :
    (onTop 1 (boxOp (k + 2)) : Op Q 2 ((k + 1) + 3)) =
      blk fun h => if ∀ j, h j = 1 then z2Op else 1 := by
  rw [boxOp, onTop_diagonal]
  refine (diagonal_eq_blk (m := k + 1) (k := 3) _).trans ?_
  congr 1; funext h
  have key : ∀ l : State 2 3,
      (∀ i : Fin (k + 2), (split 2 (k + 2 + 1) 1 ((split 2 (k + 1) 3).symm (l, h))).2 i.succ = 1) ↔
        (l 2 = 1 ∧ ∀ j, h j = 1) := by
    intro l
    simp only [split_snd_apply, split_symm_apply, Fin.val_succ]
    constructor
    · intro H
      refine ⟨?_, fun j => ?_⟩
      · have := H 0
        simpa using this
      · have := H j.succ
        simp only [Fin.val_succ] at this
        rw [dif_neg (by omega)] at this
        convert this using 2; ext; simp; omega
    · rintro ⟨hl, hh⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hl
      · simp only [Fin.val_succ]
        rw [dif_neg (by omega)]
        convert hh j using 2; ext; simp; omega
  split_ifs with hh
  · rw [z2Op]; congr 1; funext l
    by_cases hl : l 2 = 1
    · rw [if_pos ((key l).2 ⟨hl, hh⟩), if_pos hl]
    · rw [if_neg (fun H => hl ((key l).1 H).1), if_neg hl]
  · rw [← diagonal_one]; congr 1; funext l
    rw [if_neg (fun H => hh ((key l).1 H).2)]

/-- The box with `k + 3` controls, as blocks over the wires above the bottom
three. -/
theorem boxOp_blk (k : ℕ) :
    (boxOp (k + 3) : Op Q 2 ((k + 1) + 3)) =
      blk fun h => if ∀ j, h j = 1 then cz12Op else 1 := by
  rw [boxOp]
  refine (diagonal_eq_blk (m := k + 1) (k := 3) _).trans ?_
  congr 1; funext h
  have key : ∀ l : State 2 3,
      (∀ i : Fin (k + 3), (split 2 (k + 1) 3).symm (l, h) i.succ = 1) ↔
        ((l 1 = 1 ∧ l 2 = 1) ∧ ∀ j, h j = 1) := by
    intro l
    simp only [split_symm_apply, Fin.val_succ]
    constructor
    · intro H
      refine ⟨⟨?_, ?_⟩, fun j => ?_⟩
      · simpa using H 0
      · simpa using H 1
      · have := H ⟨j + 2, by omega⟩
        simp only at this
        rw [dif_neg (by omega)] at this
        convert this using 2
    · rintro ⟨⟨hl1, hl2⟩, hh⟩ ⟨i, hi⟩
      simp only
      by_cases h3 : i + 1 < 3
      · rw [dif_pos h3]
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · simpa using hl1
        · simpa using hl2
      · rw [dif_neg h3]
        exact hh _
  split_ifs with hh
  · rw [cz12Op]; congr 1; funext l
    by_cases hl : l 1 = 1 ∧ l 2 = 1
    · rw [if_pos ((key l).2 ⟨hl, hh⟩), if_pos hl]
    · rw [if_neg (fun H => hl ((key l).1 H).1), if_neg hl]
  · rw [← diagonal_one]; congr 1; funext l
    rw [if_neg (fun H => hh ((key l).1 H).2)]

/-- The recursive step: the box with `k + 3` controls. -/
theorem eval_box_succ (k : ℕ) (ih : opsQ.eval (k + 2 + 1) (box (k + 2)) = boxOp (k + 2)) :
    opsQ.eval (k + 3 + 1) (box (k + 3)) = boxOp (k + 3) := by
  have hT : opsQ.eval (k + 3 + 1) (pad (k + 1) (tau02 : Circ 3)) =
      onBottom (n := k + 1) (opsQ.eval 3 tau02) := eval_pad opsQ (k + 1) (tau02 : Circ 3)
  have hW : opsQ.eval (k + 3 + 1) (pad (k + 1) zx2) = onBottom (n := k + 1) (opsQ.eval 3 zx2) :=
    eval_pad opsQ (k + 1) zx2
  have hV : opsQ.eval (k + 3 + 1) (pad (k + 1) xz2) = onBottom (n := k + 1) (opsQ.eval 3 xz2) :=
    eval_pad opsQ (k + 1) xz2
  have hS : opsQ.eval (k + 3 + 1) (shift (box (k + 2))) = onTop 1 (boxOp (k + 2)) := by
    rw [← ih]; exact eval_shift opsQ _
  have hB : opsQ.eval (k + 3 + 1) (conj (pad (k + 1) (tau02 : Circ 3)) (shift (box (k + 2)))) =
      blk fun h => opsQ.eval 3 tau02 * ((if ∀ j, h j = 1 then z2Op else 1) * opsQ.eval 3 tau02) := by
    simp only [conj, drawn, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.prod_cons, List.prod_nil, mul_one, map_mul]
    rw [hT, hS, onTop_boxOp, onBottom_eq_blk, blk_mul, blk_mul]
  have e : box (k + 3) = drawn [pad (k + 1) zx2,
      conj (pad (k + 1) (tau02 : Circ 3)) (shift (box (k + 2))), pad (k + 1) xz2,
      conj (pad (k + 1) (tau02 : Circ 3)) (shift (box (k + 2)))] := rfl
  rw [e]
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one, map_mul]
  rw [hB, hW, hV, onBottom_eq_blk, onBottom_eq_blk, blk_mul, blk_mul, blk_mul, boxOp_blk]
  congr 1; funext h
  have on := step_on
  have off := step_off
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one, map_mul, map_one] at on off
  rw [eval_z2, eval_cz12] at on
  split_ifs
  · simp only [mul_assoc]; exact on
  · simp only [mul_assoc, one_mul]; exact off

/-- The multi-controlled `Z` gate with `k + 2` controls acts as `-1` when its
controls are all `1`. -/
theorem eval_box (k : ℕ) : opsQ.eval (k + 2 + 1) (box (k + 2)) = boxOp (k + 2) := by
  induction k with
  | zero => exact eval_box_two
  | succ k ih => exact eval_box_succ k ih

theorem eval_z_diag (n : ℕ) :
    opsQ.eval (n + 1) (z : Circ (n + 1)) = diagonal fun s => if s 0 = 1 then -1 else 1 := by
  have h1 : (ofMat (d := 2) (k := 1) qZ : Op Q 2 1) =
      diagonal fun l => if l 0 = 1 then -1 else 1 := by
    decide +kernel
  show onBottom (n := n) (ofMat (d := 2) (k := 1) qZ) = _
  rw [h1, onBottom_diagonal]
  rfl

/-- Equation (19) holds at every width. -/
theorem sound19 (k : ℕ) :
    S.sem (k + 5) (drawn [z, box (k + 4)]) = S.sem (k + 5) (drawn [box (k + 4), z]) := by
  apply S.sem_eq_of_eval QSqrt2.toR opsQ toOps_eq
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one, map_mul]
  have hb : opsQ.eval (k + 5) (box (k + 4)) = boxOp (k + 4) := eval_box (k + 2)
  rw [hb, boxOp, eval_z_diag (k + 4), diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1; funext s; ring

/-! ## All the rules -/

/-- Proposition 3.1, for the equations of `Rule`. -/
theorem rule_sound : ∀ k w v, Rule k w v → S.sem k w = S.sem k v := by
  intro k w v r
  cases r with
  | e1 => exact sem_of_check (by decide +kernel)
  | e2 => exact sem_of_check (by decide +kernel)
  | e3 => exact sem_of_check (by decide +kernel)
  | e4 => exact sem_of_check (by decide +kernel)
  | e5 => exact sem_of_check (by decide +kernel)
  | e6 => exact sem_of_check (by decide +kernel)
  | e7 => exact sem_of_check (by decide +kernel)
  | e9 => exact sem_of_check (by decide +kernel)
  | e10 => exact sem_of_check (by decide +kernel)
  | e11 => exact sem_of_check (by decide +kernel)
  | e12 => exact sem_of_check (by decide +kernel)
  | e13 => exact sem_of_check (by decide +kernel)
  | e14 => exact sem_of_check (by decide +kernel)
  | e15 => exact sem_of_check (by decide +kernel)
  | e16 => exact sem_of_check (by decide +kernel)
  | e17 => exact sem_of_check (by decide +kernel)
  | e18 => exact sem_of_check (by decide +kernel)
  | e19 k => exact sound19 k
  | f1 => exact sem_of_check (by decide +kernel)
  | f2 => exact sem_of_check (by decide +kernel)
  | f3 => exact sem_of_check (by decide +kernel)
  | f4 => exact sem_of_check (by decide +kernel)
  | g => exact sem_of_check (by decide +kernel)

/-- Proposition 3.1 (Soundness): every equation of the theory, structural
rules included, holds in the semantics. -/
theorem sound (n : ℕ) {w v : Circ n} (h : theory n w v) : S.sem n w = S.sem n v :=
  S.lift_sound (S.padded_sound rule_sound) n w v h

end QCert.RealCliffordCH
