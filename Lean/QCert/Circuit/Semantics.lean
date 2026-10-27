/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Matrix semantics of circuits

A basis state of `n` qudits of dimension `d` is a function `Fin n → Fin d`,
the digit on each wire, and an operator is a matrix indexed by basis states.
A gate on the bottom `k` of `n + k` wires is the Kronecker product of its
matrix with the identity on the top `n` wires, and a circuit shifted up by
`k` wires is the identity on the bottom `k` wires tensored with its
operator (`onBottom`, `onTop`, both through the splitting `split` of the
wires).  The semantics of a circuit is then fixed by the matrices of its
gates (`GateSem`), and the structural rules are sound for every gate set
(`lift_sound`).

A conventional `d^k × d^k` matrix is read on `k` wires with wire `0` the
least significant digit (`ofMat`): wire `0` is the bottom wire of a
diagram, the last tensor factor.
-/
import QCert.Circuit.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.BigOperators.Fin

namespace QCert

open Matrix
open scoped Kronecker

/-- Basis states of `n` qudits of dimension `d`: the digit on each wire. -/
abbrev State (d n : ℕ) := Fin n → Fin d

/-- Operators on `n` qudits of dimension `d`. -/
abbrev Op (R : Type*) (d n : ℕ) := Matrix (State d n) (State d n) R

/-- The wires of `n + k` wires split into the bottom `k` and the top `n`. -/
def split (d n k : ℕ) : State d (n + k) ≃ State d k × State d n where
  toFun s := (fun i => s ⟨i, by omega⟩, fun j => s ⟨k + j, by omega⟩)
  invFun p i := if h : (i : ℕ) < k then p.1 ⟨i, h⟩ else p.2 ⟨i - k, by omega⟩
  left_inv s := by
    funext i
    by_cases h : (i : ℕ) < k
    · simp [h]
    · simp only [h, dite_false]
      congr 1; ext; simp; omega
  right_inv p := by
    ext i
    · simp
    · simp

section Ops

variable {R : Type*} [CommRing R] {d : ℕ}

/-- An operator on `k` wires acting on the bottom `k` of `n + k` wires. -/
def onBottom {n k : ℕ} (G : Op R d k) : Op R d (n + k) :=
  (G ⊗ₖ (1 : Op R d n)).submatrix (split d n k) (split d n k)

/-- An operator on `n` wires moved up onto the top `n` of `n + k` wires. -/
def onTop (k : ℕ) {n : ℕ} (M : Op R d n) : Op R d (n + k) :=
  ((1 : Op R d k) ⊗ₖ M).submatrix (split d n k) (split d n k)

variable {n k : ℕ}

theorem onBottom_mul (A B : Op R d k) :
    onBottom (n := n) (A * B) = onBottom A * onBottom B := by
  simp only [onBottom, submatrix_mul_equiv, ← mul_kronecker_mul, mul_one]

theorem onBottom_one : onBottom (n := n) (1 : Op R d k) = 1 := by
  simp [onBottom, submatrix_one_equiv]

theorem onTop_mul (A B : Op R d n) : onTop k (A * B) = onTop k A * onTop k B := by
  simp only [onTop, submatrix_mul_equiv, ← mul_kronecker_mul, mul_one]

theorem onTop_one : onTop k (1 : Op R d n) = 1 := by
  simp [onTop, submatrix_one_equiv]

theorem onTop_smul (c : R) (M : Op R d n) : onTop k (c • M) = c • onTop k M := by
  simp [onTop, kronecker_smul, submatrix_smul]

/-- Operators on disjoint wires commute. -/
theorem onBottom_onTop_comm (A : Op R d k) (B : Op R d n) :
    onBottom A * onTop k B = onTop k B * onBottom A := by
  simp only [onBottom, onTop, submatrix_mul_equiv, ← mul_kronecker_mul, mul_one, one_mul]

theorem onTop_apply (M : Op R d n) (s t : State d (n + k)) :
    onTop k M s t = if (split d n k s).1 = (split d n k t).1
      then M (split d n k s).2 (split d n k t).2 else 0 := by
  simp only [onTop, submatrix_apply, kroneckerMap_apply, one_apply]
  split_ifs <;> simp

private theorem state_congr {m : ℕ} (s : State d m) {i j : ℕ} (hi : i < m) (hj : j < m)
    (h : i = j) : s ⟨i, hi⟩ = s ⟨j, hj⟩ := by
  subst h; rfl

/-- Moving up one wire after `k` wires is moving up `k + 1` wires. -/
theorem onTop_one_onTop (M : Op R d n) :
    onTop 1 (onTop k M) = onTop (k + 1) M := by
  ext s t
  rw [onTop_apply, onTop_apply, onTop_apply]
  have h2 : ∀ u : State d (n + k + 1),
      (split d n k (split d (n + k) 1 u).2).2 = (split d n (k + 1) u).2 := by
    intro u; funext j
    simp only [split, Equiv.coe_fn_mk]
    exact state_congr u _ _ (by omega)
  have h1 : ((split d (n + k) 1 s).1 = (split d (n + k) 1 t).1 ∧
      (split d n k (split d (n + k) 1 s).2).1 = (split d n k (split d (n + k) 1 t).2).1) ↔
      (split d n (k + 1) s).1 = (split d n (k + 1) t).1 := by
    simp only [split, Equiv.coe_fn_mk, funext_iff]
    constructor
    · rintro ⟨ha, hb⟩ i
      by_cases hi : (i : ℕ) = 0
      · have := ha 0
        simp only [Fin.val_zero] at this
        rw [state_congr s _ (by omega : (0 : ℕ) < n + k + 1) hi,
          state_congr t _ (by omega : (0 : ℕ) < n + k + 1) hi]
        exact this
      · have := hb ⟨i - 1, by omega⟩
        simp only at this
        rw [state_congr s _ (by omega : 1 + (i - 1) < n + k + 1) (by omega : (i : ℕ) = 1 + (i - 1)),
          state_congr t _ (by omega : 1 + (i - 1) < n + k + 1) (by omega : (i : ℕ) = 1 + (i - 1))]
        exact this
    · intro h
      refine ⟨fun i => ?_, fun j => ?_⟩
      · have := h ⟨i, by omega⟩
        simpa using this
      · have := h ⟨1 + j, by omega⟩
        simpa using this
  by_cases hst : (split d n (k + 1) s).1 = (split d n (k + 1) t).1
  · obtain ⟨ha, hb⟩ := h1.2 hst
    simp only [ha, hb, hst, if_true, h2]
  · have : ¬ ((split d (n + k) 1 s).1 = (split d (n + k) 1 t).1 ∧
        (split d n k (split d (n + k) 1 s).2).1 = (split d n k (split d (n + k) 1 t).2).1) :=
      fun h => hst (h1.1 h)
    simp only [hst, if_false]
    by_cases ha : (split d (n + k) 1 s).1 = (split d (n + k) 1 t).1
    · have hb : ¬ (split d n k (split d (n + k) 1 s).2).1 =
          (split d n k (split d (n + k) 1 t).2).1 := fun hb => this ⟨ha, hb⟩
      simp [ha, hb]
    · simp [ha]

end Ops

section Unitary

variable {R : Type*} [CommRing R] [StarRing R] {d n k : ℕ}

theorem star_onBottom (G : Op R d k) : star (onBottom (n := n) G) = onBottom (star G) := by
  simp only [onBottom, star_eq_conjTranspose, conjTranspose_submatrix, conjTranspose_kronecker,
    conjTranspose_one]

theorem star_onTop (M : Op R d n) : star (onTop k M) = onTop k (star M) := by
  simp only [onTop, star_eq_conjTranspose, conjTranspose_submatrix, conjTranspose_kronecker,
    conjTranspose_one]

/-- `onBottom` on unitaries. -/
def onBottomU : unitaryGroup (State d k) R →* unitaryGroup (State d (n + k)) R where
  toFun U := ⟨onBottom U.1, by
    rw [mem_unitaryGroup_iff, star_onBottom, ← onBottom_mul, (mem_unitaryGroup_iff.1 U.2),
      onBottom_one]⟩
  map_one' := Subtype.ext onBottom_one
  map_mul' _ _ := Subtype.ext (onBottom_mul _ _)

/-- `onTop` on unitaries. -/
def onTopU (k : ℕ) : unitaryGroup (State d n) R →* unitaryGroup (State d (n + k)) R where
  toFun U := ⟨onTop k U.1, by
    rw [mem_unitaryGroup_iff, star_onTop, ← onTop_mul, (mem_unitaryGroup_iff.1 U.2), onTop_one]⟩
  map_one' := Subtype.ext onTop_one
  map_mul' _ _ := Subtype.ext (onTop_mul _ _)

/-- A unit scalar as a unitary operator on `n` wires. -/
def scalarU (c : unitary R) : unitaryGroup (State d n) R :=
  ⟨(c : R) • 1, by
    rw [mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, mul_one,
      Unitary.mul_star_self_of_mem c.2, one_smul]⟩

end Unitary

/-- Reading a conventional `d^k × d^k` matrix on `k` wires, wire `0` being
the least significant digit of the index. -/
def ofMat {R : Type*} {d k : ℕ} (M : Matrix (Fin (d ^ k)) (Fin (d ^ k)) R) : Op R d k :=
  M.submatrix finFunctionFinEquiv finFunctionFinEquiv

theorem ofMat_mem_unitaryGroup {R : Type*} [CommRing R] [StarRing R] {d k : ℕ}
    {M : Matrix (Fin (d ^ k)) (Fin (d ^ k)) R} (h : M ∈ unitaryGroup (Fin (d ^ k)) R) :
    ofMat M ∈ unitaryGroup (State d k) R := by
  rw [mem_unitaryGroup_iff] at h ⊢
  simp only [ofMat, star_eq_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv]
  rw [← star_eq_conjTranspose, h, submatrix_one_equiv]

/-- The matrices of a gate set: a unit scalar for each 0-ary gate, and a
unitary operator on its own wires for each gate on one, two or three
wires. -/
structure GateSem (Gate : ℕ → Type) (R : Type*) [CommRing R] [StarRing R] (d : ℕ) where
  scalar : Gate 0 → unitary R
  gate1 : Gate 1 → unitaryGroup (State d 1) R
  gate2 : Gate 2 → unitaryGroup (State d 2) R
  gate3 : Gate 3 → unitaryGroup (State d 3) R

namespace GateSem

variable {Gate : ℕ → Type} {R : Type*} [CommRing R] [StarRing R] {d : ℕ}
  (S : GateSem Gate R d)

/-- The operator of a generator. -/
def gen : {n : ℕ} → Gen Gate n → unitaryGroup (State d n) R
  | _, .gate0 g => scalarU (S.scalar g)
  | _, .gate1 g => onBottomU (S.gate1 g)
  | _, .gate2 g => onBottomU (S.gate2 g)
  | _, .gate3 g => onBottomU (S.gate3 g)
  | _, .up g => onTopU 1 (gen g)

/-- The operator of a circuit, composed in operator order. -/
def sem (n : ℕ) : Circuit Gate n →* unitaryGroup (State d n) R := FreeMonoid.lift S.gen

theorem sem_shift {n : ℕ} (w : Circuit Gate n) :
    S.sem (n + 1) (Circuit.shift w) = onTopU 1 (S.sem n w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, Circuit.shift_of, ih, map_mul (S.sem n), map_mul (onTopU 1)]
    rfl

private theorem up_up {n : ℕ} (g : Gen Gate n) :
    (S.gen g.up.up : Op R d (n + 2)) = onTop 2 (S.gen g : Op R d n) :=
  onTop_one_onTop (k := 1) _

private theorem up_up_up {n : ℕ} (g : Gen Gate n) :
    (S.gen g.up.up.up : Op R d (n + 3)) = onTop 3 (S.gen g : Op R d n) := by
  show onTop 1 (S.gen g.up.up : Op R d (n + 2)) = _
  rw [up_up]; exact onTop_one_onTop (k := 2) _

/-- The structural rules are sound for every gate set: rules that hold
give a lifted rule set that holds. -/
theorem lift_sound {Rules : CRel Gate}
    (h : ∀ n w v, Rules n w v → S.sem n w = S.sem n v) :
    ∀ n w v, Lift Rules n w v → S.sem n w = S.sem n v := by
  intro n w v hr
  induction hr with
  | rule hr => exact h _ _ _ hr
  | shift _ ih => rw [sem_shift, sem_shift, ih]
  | comm1 c g =>
    apply Subtype.ext
    simp only [sem, map_mul, FreeMonoid.lift_eval_of, Submonoid.coe_mul]
    exact (onBottom_onTop_comm (k := 1) _ _).symm
  | comm2 c g =>
    apply Subtype.ext
    simp only [sem, map_mul, FreeMonoid.lift_eval_of, Submonoid.coe_mul]
    rw [up_up]
    exact (onBottom_onTop_comm (k := 2) _ _).symm
  | comm3 c g =>
    apply Subtype.ext
    simp only [sem, map_mul, FreeMonoid.lift_eval_of, Submonoid.coe_mul]
    rw [up_up_up]
    exact (onBottom_onTop_comm (k := 3) _ _).symm
  | scalar c =>
    apply Subtype.ext
    show onTop 1 ((S.scalar c : R) • (1 : Op R d _)) = (S.scalar c : R) • 1
    rw [onTop_smul, onTop_one]

end GateSem

end QCert
