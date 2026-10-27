/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# CNOT-dihedral circuits: the phase-affine semantics

Every CNOT-dihedral gate maps a basis state `|x⟩` to `ω^{p(x)} |f(x)⟩`
(§3, "phase polynomials", Definition 3.5), so a circuit is a pair of a map
`f` on basis states and a phase `p` with values in `ℤ/8`.  `PA n` is the
monoid of such pairs, composed in operator order, and `pa n` reads a
circuit in it.  `toOp` turns a pair into its matrix, and the matrix
semantics `S.sem` is `toOp ∘ pa` (`sem_eq_toOp`), so circuit identities are
decided on pairs, `2ⁿ` basis states at a time, rather than on matrices.
-/
import QCert.CNOTDihedral.Semantics
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

namespace QCert.CNOTDihedral

open Matrix

/-- A phase-affine operator on `n` wires: `|x⟩ ↦ ω^{ph x} |f x⟩`. -/
@[ext]
structure PA (n : ℕ) where
  f : State 2 n → State 2 n
  ph : State 2 n → ZMod 8

namespace PA

variable {n : ℕ}

/-- Composition in operator order: `a * b` applies `b` first. -/
instance : Mul (PA n) := ⟨fun a b => ⟨a.f ∘ b.f, fun x => b.ph x + a.ph (b.f x)⟩⟩
instance : One (PA n) := ⟨⟨id, 0⟩⟩

@[simp] theorem mul_f (a b : PA n) : (a * b).f = a.f ∘ b.f := rfl
@[simp] theorem mul_ph (a b : PA n) (x : State 2 n) :
    (a * b).ph x = b.ph x + a.ph (b.f x) := rfl
@[simp] theorem one_f : (1 : PA n).f = id := rfl
@[simp] theorem one_ph (x : State 2 n) : (1 : PA n).ph x = 0 := rfl

instance : Monoid (PA n) where
  mul_assoc a b c := by ext x <;> simp [add_assoc]
  one_mul a := by ext x <;> simp
  mul_one a := by ext x <;> simp

/-- A pair on `k` wires acting on the bottom `k` of `m + k` wires. -/
def onBottom {m k : ℕ} (a : PA k) : PA (m + k) where
  f s := (split 2 m k).symm (a.f (split 2 m k s).1, (split 2 m k s).2)
  ph s := a.ph (split 2 m k s).1

/-- A pair on `m` wires moved up onto the top `m` of `m + k` wires. -/
def onTop (k : ℕ) {m : ℕ} (a : PA m) : PA (m + k) where
  f s := (split 2 m k).symm ((split 2 m k s).1, a.f (split 2 m k s).2)
  ph s := a.ph (split 2 m k s).2

/-- A scalar `ω^c`. -/
def scalar (c : ZMod 8) : PA n := ⟨id, fun _ => c⟩

end PA

/-! ### Deciding equality of pairs -/

/-- All basis states on `n` wires. -/
def allStates : (n : ℕ) → List (State 2 n)
  | 0 => [Fin.elim0]
  | n + 1 => (allStates n).flatMap fun s => [Fin.cons 0 s, Fin.cons 1 s]

theorem mem_allStates : ∀ {n : ℕ} (s : State 2 n), s ∈ allStates n
  | 0, s => by simp [allStates]; funext i; exact i.elim0
  | n + 1, s => by
    simp only [allStates, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨Fin.tail s, mem_allStates _, ?_⟩
    have h : s = Fin.cons (s 0) (Fin.tail s) := (Fin.cons_self_tail s).symm
    rcases Fin.exists_fin_two.mp ⟨s 0, rfl⟩ with h0 | h0 <;> rw [h0] at h <;> simp [← h]

/-- Equality of basis states, as a Boolean. -/
def stBeq : {n : ℕ} → State 2 n → State 2 n → Bool
  | 0, _, _ => true
  | _ + 1, s, t => s 0 == t 0 && stBeq (Fin.tail s) (Fin.tail t)

theorem eq_of_stBeq : ∀ {n : ℕ} {s t : State 2 n}, stBeq s t = true → s = t
  | 0, s, t, _ => funext fun i => i.elim0
  | n + 1, s, t, h => by
    simp only [stBeq, Bool.and_eq_true, beq_iff_eq] at h
    rw [← Fin.cons_self_tail s, ← Fin.cons_self_tail t, h.1, eq_of_stBeq h.2]

/-- Equality of pairs, decided on every basis state. -/
def PA.check {n : ℕ} (a b : PA n) : Bool :=
  (allStates n).all fun x => stBeq (a.f x) (b.f x) && a.ph x == b.ph x

theorem PA.eq_of_check {n : ℕ} {a b : PA n} (h : PA.check a b = true) : a = b := by
  simp only [PA.check, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨af, aph⟩ := a
  obtain ⟨bf, bph⟩ := b
  congr 1
  · funext x; exact eq_of_stBeq (h x (mem_allStates x)).1
  · funext x; exact (h x (mem_allStates x)).2

/-! ### The gates -/

/-- `X`: `|x⟩ ↦ |x ⊕ 1⟩`. -/
def paX : PA 1 := ⟨fun s i => s i + 1, 0⟩
/-- `T`: `|x⟩ ↦ ω^x |x⟩`. -/
def paT : PA 1 := ⟨id, fun s => if s 0 = 1 then 1 else 0⟩
/-- `CNOT`, control on wire `1`: `|x₀ x₁⟩ ↦ |x₀ ⊕ x₁, x₁⟩` (wire `0` first). -/
def paCX : PA 2 := ⟨fun s => ![s 0 + s 1, s 1], 0⟩
/-- `SWAP`: `|x₀ x₁⟩ ↦ |x₁ x₀⟩`. -/
def paSW : PA 2 := ⟨fun s => ![s 1, s 0], 0⟩

/-- The pair of a generator. -/
def paGen : {n : ℕ} → Gen Gate n → PA n
  | _, .gate0 .ω => PA.scalar 1
  | _, .gate1 .X => PA.onBottom paX
  | _, .gate1 .T => PA.onBottom paT
  | _, .gate2 .CX => PA.onBottom paCX
  | _, .gate2 .SW => PA.onBottom paSW
  | _, .gate3 g => nomatch g
  | _, .up g => PA.onTop 1 (paGen g)

/-- The pair of a circuit. -/
def pa (n : ℕ) : Circuit Gate n →* PA n := FreeMonoid.lift paGen

/-! ### Matrices -/

noncomputable section

/-- The matrix of a pair: the entry at `(f x, x)` is `ω^{ph x}`. -/
def toOp {n : ℕ} (a : PA n) : Op ℂ 2 n :=
  fun s t => if s = a.f t then ω ^ (a.ph t).val else 0

theorem val_one8 : (1 : ZMod 8).val = 1 := rfl

theorem ω_pow_eight : ω ^ 8 = 1 := by
  rw [show 8 = 4 * 2 from rfl, pow_mul, ω_pow_four]; norm_num

theorem ω_pow_val_add (x y : ZMod 8) : ω ^ (x + y).val = ω ^ x.val * ω ^ y.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) 8, pow_add, pow_mul, ω_pow_eight, one_pow,
    mul_one]

theorem toOp_mul {n : ℕ} (a b : PA n) : toOp (a * b) = toOp a * toOp b := by
  ext s t
  simp only [toOp, mul_apply, PA.mul_f, PA.mul_ph, Function.comp_apply]
  rw [Finset.sum_eq_single (b.f t)]
  · simp only [if_true]
    split_ifs <;> simp [ω_pow_val_add, mul_comm]
  · intro u _ hu; simp [hu]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem toOp_one {n : ℕ} : toOp (1 : PA n) = 1 := by
  ext s t
  simp only [toOp, PA.one_f, PA.one_ph, id, one_apply]
  split_ifs <;> simp

theorem toOp_onBottom {m k : ℕ} (a : PA k) :
    toOp (PA.onBottom (m := m) a) = onBottom (toOp a) := by
  ext s t
  rw [onBottom_apply]
  simp only [toOp, PA.onBottom]
  have e : s = (split 2 m k).symm (a.f (split 2 m k t).1, (split 2 m k t).2) ↔
      (split 2 m k s).1 = a.f (split 2 m k t).1 ∧ (split 2 m k s).2 = (split 2 m k t).2 := by
    rw [Equiv.eq_symm_apply, Prod.ext_iff]
  by_cases h1 : (split 2 m k s).1 = a.f (split 2 m k t).1 <;>
    by_cases h2 : (split 2 m k s).2 = (split 2 m k t).2 <;> simp [e, h1, h2]

theorem toOp_onTop {m : ℕ} (a : PA m) :
    toOp (PA.onTop 1 a) = onTop 1 (toOp a) := by
  ext s t
  rw [onTop_apply]
  simp only [toOp, PA.onTop]
  have e : s = (split 2 m 1).symm ((split 2 m 1 t).1, a.f (split 2 m 1 t).2) ↔
      (split 2 m 1 s).1 = (split 2 m 1 t).1 ∧ (split 2 m 1 s).2 = a.f (split 2 m 1 t).2 := by
    rw [Equiv.eq_symm_apply, Prod.ext_iff]
  by_cases h1 : (split 2 m 1 s).1 = (split 2 m 1 t).1 <;>
    by_cases h2 : (split 2 m 1 s).2 = a.f (split 2 m 1 t).2 <;> simp [e, h1, h2]

theorem toOp_scalar {n : ℕ} : toOp (PA.scalar (n := n) 1) = ω • (1 : Op ℂ 2 n) := by
  ext s t
  have h1 : (1 : ZMod 8).val = 1 := rfl
  simp only [toOp, PA.scalar, id, smul_apply, one_apply, smul_eq_mul, h1]
  split_ifs <;> simp

/-- A one- or two-wire pair agrees with a conventional matrix when it does on
every pair of indices. -/
theorem toOp_eq_ofMat {k : ℕ} (a : PA k) (M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)
    (h : ∀ i j, toOp a (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm j) = M i j) :
    toOp a = ofMat M := by
  ext s t
  have := h (finFunctionFinEquiv s) (finFunctionFinEquiv t)
  simpa [ofMat] using this

theorem toOp_paX : toOp paX = ofMat matX := by
  apply toOp_eq_ofMat
  intro i j
  fin_cases i <;> fin_cases j <;> simp [toOp, paX, matX, funext_iff, Fin.forall_fin_one] <;> decide

theorem toOp_paT : toOp paT = ofMat matT := by
  apply toOp_eq_ofMat
  intro i j
  fin_cases i <;> fin_cases j <;> simp +decide [toOp, paT, matT, val_one8]

theorem toOp_paCX : toOp paCX = ofMat matCX := by
  apply toOp_eq_ofMat
  intro i j
  fin_cases i <;> fin_cases j <;> simp [toOp, paCX, matCX, funext_iff, Fin.forall_fin_two] <;>
    decide

theorem toOp_paSW : toOp paSW = ofMat matSW := by
  apply toOp_eq_ofMat
  intro i j
  fin_cases i <;> fin_cases j <;> simp [toOp, paSW, matSW, funext_iff, Fin.forall_fin_two] <;>
    decide

theorem toOp_paGen {n : ℕ} (g : Gen Gate n) : toOp (paGen g) = (S.gen g).1 := by
  induction g with
  | gate0 c => cases c; exact toOp_scalar
  | gate1 c =>
    cases c
    · show toOp (PA.onBottom paX) = onBottom (ofMat matX); rw [toOp_onBottom, toOp_paX]
    · show toOp (PA.onBottom paT) = onBottom (ofMat matT); rw [toOp_onBottom, toOp_paT]
  | gate2 c =>
    cases c
    · show toOp (PA.onBottom paCX) = onBottom (ofMat matCX); rw [toOp_onBottom, toOp_paCX]
    · show toOp (PA.onBottom paSW) = onBottom (ofMat matSW); rw [toOp_onBottom, toOp_paSW]
  | gate3 c => exact nomatch c
  | up g ih => show toOp (PA.onTop 1 (paGen g)) = onTop 1 _; rw [toOp_onTop, ih]

/-- The matrix semantics is the matrix of the phase-affine pair. -/
theorem sem_eq_toOp {n : ℕ} (w : Circuit Gate n) : (S.sem n w).1 = toOp (pa n w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [toOp_one]
  | mul_of g w ih =>
    rw [map_mul, map_mul, Submonoid.coe_mul, ih, toOp_mul]
    congr 1
    show (S.gen g).1 = toOp (paGen g)
    exact (toOp_paGen g).symm

/-- Circuits with the same pair have the same matrix. -/
theorem sem_eq_of_pa {n : ℕ} {w v : Circuit Gate n} (h : pa n w = pa n v) :
    S.sem n w = S.sem n v :=
  Subtype.ext (by rw [sem_eq_toOp, sem_eq_toOp, h])

/-! ### The matrix determines the pair -/

theorem ω_ne_zero : ω ≠ 0 := by
  intro h; have := ω_pow_four; rw [h] at this; norm_num at this

theorem ω_pow_ne_one {d : ℕ} (h0 : 0 < d) (h8 : d < 8) : ω ^ d ≠ 1 := by
  intro h
  have h2 : Complex.I ^ d = 1 := by
    rw [← ω_sq, ← pow_mul, mul_comm, pow_mul, h, one_pow]
  interval_cases d
  · simp [Complex.ext_iff] at h2
  · simp at h2; norm_num at h2
  · simp [pow_succ, Complex.ext_iff] at h2
  · rw [ω_pow_four] at h; norm_num at h
  · simp [pow_succ, Complex.ext_iff] at h2
  · simp [pow_succ, Complex.ext_iff] at h2; norm_num at h2
  · simp [pow_succ, Complex.ext_iff] at h2

theorem ω_pow_val_inj {x y : ZMod 8} (h : ω ^ x.val = ω ^ y.val) : x = y := by
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  apply ZMod.val_injective
  rcases le_total x.val y.val with hxy | hxy
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hxy
    rw [hd, pow_add] at h
    have : ω ^ d = 1 := by
      have h' : ω ^ x.val * 1 = ω ^ x.val * ω ^ d := by rw [mul_one]; exact h
      exact (mul_left_cancel₀ (pow_ne_zero _ ω_ne_zero) h').symm
    by_contra hne
    exact ω_pow_ne_one (by omega) (by omega) this
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hxy
    rw [hd, pow_add] at h
    have : ω ^ d = 1 := by
      have h' : ω ^ y.val * 1 = ω ^ y.val * ω ^ d := by rw [mul_one]; exact h.symm
      exact (mul_left_cancel₀ (pow_ne_zero _ ω_ne_zero) h').symm
    by_contra hne
    exact ω_pow_ne_one (by omega) (by omega) this

/-- The matrix of a pair determines the pair. -/
theorem toOp_injective {n : ℕ} {a b : PA n} (h : toOp a = toOp b) : a = b := by
  have key : ∀ t, a.f t = b.f t ∧ a.ph t = b.ph t := by
    intro t
    have e := congrFun (congrFun h (a.f t)) t
    simp only [toOp] at e
    by_cases hf : a.f t = b.f t
    · rw [if_pos hf] at e
      exact ⟨hf, ω_pow_val_inj e⟩
    · rw [if_neg hf] at e
      exact absurd e (pow_ne_zero _ ω_ne_zero)
  obtain ⟨af, aph⟩ := a
  obtain ⟨bf, bph⟩ := b
  congr 1
  · funext t; exact (key t).1
  · funext t; exact (key t).2

/-- Circuits with the same matrix have the same phase-affine pair. -/
theorem pa_eq_of_sem {n : ℕ} {w v : Circuit Gate n} (h : S.sem n w = S.sem n v) :
    pa n w = pa n v :=
  toOp_injective (by rw [← sem_eq_toOp, ← sem_eq_toOp, h])

end

end QCert.CNOTDihedral
