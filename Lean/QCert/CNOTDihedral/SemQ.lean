/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The phase-affine semantics of classes

The pair of a circuit (`pa`) depends only on its class (soundness), so it
is a monoid homomorphism `paQ : Q n →* PA n`.  This file computes it on the
gates at given positions, with states read through `bit s i` (the bit on
wire `i`, `0` off the circuit) and the unit vectors `ei i`:

* `X` on wire `i` adds `ei i`; `CNOT` with control `i + 1` and target `i`
  adds `bit s (i + 1) • ei i`; `SWAP` relabels the wires (`swq i`);
* `T` on wire `i` has phase `bit s i` (read in `ℤ/8`), `ω` phase `1`;
* moving up a wire acts on the tail of the state (`paQ_sh`).
-/
import QCert.CNOTDihedral.Calc

namespace QCert.CNOTDihedral

open Circuit

/-- Derivations preserve the phase-affine pair. -/
theorem pa_sound {n : ℕ} {w v : Circ n} (h : Eqv n w v) : pa n w = pa n v :=
  derivable_sound (sem := paGen) (fun w v h => pa_eq_of_sem (theory_sound n w v h)) h

/-- The phase-affine pair of a class. -/
def paQ {n : ℕ} : Q n →* PA n :=
  (conGen (Theory n)).lift (pa n) (fun _ _ h => (Con.ker_rel _).2 (pa_sound h))

@[simp] theorem paQ_mk {n : ℕ} (w : Circ n) : paQ (mk w) = pa n w := rfl

/-! ### Bits and unit vectors -/

/-- The bit on wire `i` (`0` off the circuit). -/
def bit {n : ℕ} (s : State 2 n) (i : ℕ) : Fin 2 := if h : i < n then s ⟨i, h⟩ else 0

/-- The unit vector on wire `i` (`0` off the circuit). -/
def ei {n : ℕ} (i : ℕ) : State 2 n := fun j => if (j : ℕ) = i then 1 else 0

/-- A bit read as a phase. -/
def toZ8 (b : Fin 2) : ZMod 8 := (b.val : ZMod 8)

@[simp] theorem bit_val {n : ℕ} (s : State 2 n) (j : Fin n) : bit s j = s j := by
  simp [bit, j.isLt]

theorem bit_out {n : ℕ} (s : State 2 n) {i : ℕ} (h : n ≤ i) : bit s i = 0 := by
  simp [bit, show ¬ i < n by omega]

@[simp] theorem bit_cons_zero {n : ℕ} (a : Fin 2) (s : State 2 n) :
    bit (Fin.cons a s : State 2 (n + 1)) 0 = a := by
  simp [bit]

@[simp] theorem bit_cons_succ {n : ℕ} (a : Fin 2) (s : State 2 n) (i : ℕ) :
    bit (Fin.cons a s : State 2 (n + 1)) (i + 1) = bit s i := by
  by_cases h : i < n
  · simp only [bit, h, show i + 1 < n + 1 by omega, dif_pos]
    exact Fin.cons_succ (α := fun _ => Fin 2) a s ⟨i, h⟩
  · simp [bit, h, show ¬ i + 1 < n + 1 by omega]

theorem bit_tail {n : ℕ} (s : State 2 (n + 1)) (i : ℕ) : bit (Fin.tail s) i = bit s (i + 1) := by
  conv_rhs => rw [← Fin.cons_self_tail s]
  rw [bit_cons_succ]

theorem bit_add {n : ℕ} (s t : State 2 n) (i : ℕ) : bit (s + t) i = bit s i + bit t i := by
  by_cases h : i < n <;> simp [bit, h]

theorem bit_smul {n : ℕ} (a : Fin 2) (s : State 2 n) (i : ℕ) : bit (a • s) i = a * bit s i := by
  by_cases h : i < n <;> simp [bit, h]

theorem bit_zero {n : ℕ} (i : ℕ) : bit (0 : State 2 n) i = 0 := by
  by_cases h : i < n <;> simp [bit, h]

@[simp] theorem ei_apply {n : ℕ} (i : ℕ) (j : Fin n) : (ei i : State 2 n) j = if (j : ℕ) = i then 1 else 0 :=
  rfl

theorem bit_ei {n : ℕ} (i j : ℕ) : bit (ei i : State 2 n) j = if j < n ∧ j = i then 1 else 0 := by
  by_cases h : j < n <;> simp [bit, ei, h]

theorem ei_zero_succ {n : ℕ} : (ei 0 : State 2 (n + 1)) = Fin.cons 1 0 := by
  funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp [ei]

theorem ei_succ {n : ℕ} (i : ℕ) : (ei (i + 1) : State 2 (n + 1)) = Fin.cons 0 (ei i) := by
  funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp [ei]

theorem cons_add {n : ℕ} (a b : Fin 2) (s t : State 2 n) :
    (Fin.cons a s : State 2 (n + 1)) + Fin.cons b t = Fin.cons (a + b) (s + t) := by
  funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem cons_smul {n : ℕ} (a b : Fin 2) (s : State 2 n) :
    a • (Fin.cons b s : State 2 (n + 1)) = Fin.cons (a * b) (a • s) := by
  funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem toZ8_add_of {a b : Fin 2} : toZ8 (a + b) = toZ8 a + toZ8 b - 2 * toZ8 a * toZ8 b := by
  fin_cases a <;> fin_cases b <;> decide

/-! ### The pairs `onTop` and `onBottom` -/

namespace PA

theorem ext' {n : ℕ} {a b : PA n} (hf : ∀ s, a.f s = b.f s) (hph : ∀ s, a.ph s = b.ph s) :
    a = b := PA.ext (funext hf) (funext hph)

theorem onTop_f {m : ℕ} (a : PA m) (s : State 2 (m + 1)) :
    (PA.onTop 1 a).f s = Fin.cons (s 0) (a.f (Fin.tail s)) := by
  have e : (fun j : Fin m => s ⟨1 + j, by omega⟩) = Fin.tail s := by
    funext j; simp only [Fin.tail]; congr 1; ext; simp; omega
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [PA.onTop, split]
  · simp only [PA.onTop, split, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Fin.val_succ,
      show ¬ ((j : ℕ) + 1 < 1) by omega, dif_neg, not_false_eq_true, Fin.cons_succ]
    rw [e]
    exact congrArg _ (Fin.ext (by simp))

theorem onTop_ph {m : ℕ} (a : PA m) (s : State 2 (m + 1)) :
    (PA.onTop 1 a).ph s = a.ph (Fin.tail s) := by
  have e : (fun j : Fin m => s ⟨1 + j, by omega⟩) = Fin.tail s := by
    funext j; simp only [Fin.tail]; congr 1; ext; simp; omega
  simp only [PA.onTop, split, Equiv.coe_fn_mk]
  rw [e]

theorem onTop_mul {m : ℕ} (a b : PA m) : PA.onTop 1 (a * b) = PA.onTop 1 a * PA.onTop 1 b := by
  ext s
  · simp [onTop_f]
  · simp [onTop_ph, onTop_f]

theorem onTop_one {m : ℕ} : PA.onTop 1 (1 : PA m) = 1 := by
  ext s
  · simp [onTop_f]
  · simp [onTop_ph]

theorem onBottom_f {m k : ℕ} (a : PA k) (s : State 2 (m + k)) (j : Fin (m + k)) :
    (PA.onBottom (m := m) a).f s j =
      if h : (j : ℕ) < k then a.f (fun i => s ⟨i, by omega⟩) ⟨j, h⟩ else s j := by
  simp only [PA.onBottom, split, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]
  split_ifs with h
  · rfl
  · congr 1; ext; simp; omega

theorem onBottom_ph {m k : ℕ} (a : PA k) (s : State 2 (m + k)) :
    (PA.onBottom (m := m) a).ph s = a.ph (fun i => s ⟨i, by omega⟩) := rfl

end PA

theorem pa_shift {n : ℕ} (w : Circ n) : pa (n + 1) (Circuit.shift w) = PA.onTop 1 (pa n w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [PA.onTop_one]
  | mul_of g w ih =>
    rw [map_mul, Circuit.shift_of, map_mul, map_mul, ih, PA.onTop_mul]
    rfl

theorem paQ_sh {n : ℕ} (a : Q n) : paQ (sh a) = PA.onTop 1 (paQ a) := by
  obtain ⟨w, rfl⟩ := mk_surjective a
  exact pa_shift w

theorem paQ_sh_f {n : ℕ} (a : Q n) (s : State 2 (n + 1)) :
    (paQ (sh a)).f s = Fin.cons (s 0) ((paQ a).f (Fin.tail s)) := by
  rw [paQ_sh, PA.onTop_f]

theorem paQ_sh_ph {n : ℕ} (a : Q n) (s : State 2 (n + 1)) :
    (paQ (sh a)).ph s = (paQ a).ph (Fin.tail s) := by
  rw [paQ_sh, PA.onTop_ph]

/-! ### The gates -/

theorem fin2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp

theorem paQ_of {n : ℕ} (g : Gen Gate n) : paQ (mk (FreeMonoid.of g)) = paGen g :=
  FreeMonoid.lift_eval_of paGen g

theorem onBottom1_f {n : ℕ} (a : PA 1) (s : State 2 (n + 1)) :
    (PA.onBottom (m := n) a).f s = Fin.cons (a.f (fun _ => s 0) 0) (Fin.tail s) := by
  have e : (fun i : Fin 1 => s ⟨i, by omega⟩) = fun _ => s 0 := by
    funext i; rw [Fin.fin_one_eq_zero i]; rfl
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [PA.onBottom_f, dif_pos (by simp), e, Fin.cons_zero]; rfl
  · rw [PA.onBottom_f, dif_neg (by simp), Fin.cons_succ]; rfl

theorem onBottom1_ph {n : ℕ} (a : PA 1) (s : State 2 (n + 1)) :
    (PA.onBottom (m := n) a).ph s = a.ph (fun _ => s 0) := by
  rw [PA.onBottom_ph]
  congr 1; funext i; rw [Fin.fin_one_eq_zero i]; rfl

theorem onBottom2_f {n : ℕ} (a : PA 2) (s : State 2 (n + 2)) :
    (PA.onBottom (m := n) a).f s =
      Fin.cons (a.f ![s 0, s 1] 0) (Fin.cons (a.f ![s 0, s 1] 1) (Fin.tail (Fin.tail s))) := by
  have e : (fun i : Fin 2 => s ⟨i, by omega⟩) = ![s 0, s 1] := by
    funext i; fin_cases i <;> rfl
  funext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  · rw [PA.onBottom_f, dif_pos (by simp), e, Fin.cons_zero]; rfl
  · rw [PA.onBottom_f, dif_pos (by simp), e, Fin.cons_succ, Fin.cons_zero]; rfl
  · rw [PA.onBottom_f, dif_neg (by simp), Fin.cons_succ, Fin.cons_succ]; rfl

theorem paQ_qX {n : ℕ} (i : ℕ) : paQ (qX i : Q n) = ⟨fun s => s + ei i, 0⟩ := by
  induction n generalizing i with
  | zero =>
    have : (qX i : Q 0) = 1 := qX_out (Nat.zero_le _)
    rw [this, map_one]
    exact PA.ext' (fun s => funext fun j => j.elim0) (fun s => rfl)
  | succ n ih =>
    cases i with
    | zero =>
      rw [qX_zero, paQ_of]
      refine PA.ext' (fun s => ?_) (fun s => rfl)
      show (PA.onBottom (m := n) paX).f s = s + ei 0
      rw [onBottom1_f]
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [paX, ei, Fin.tail]
    | succ i =>
      rw [← sh_qX, paQ_sh, ih]
      refine PA.ext' (fun s => ?_) (fun s => ?_)
      · rw [PA.onTop_f]
        funext j
        refine Fin.cases ?_ (fun j => ?_) j <;> simp [ei, Fin.tail]
      · rw [PA.onTop_ph]; rfl

theorem paQ_qT {n : ℕ} (i : ℕ) : paQ (qT i : Q n) = ⟨id, fun s => toZ8 (bit s i)⟩ := by
  induction n generalizing i with
  | zero =>
    have : (qT i : Q 0) = 1 := qT_out (Nat.zero_le _)
    rw [this, map_one]
    exact PA.ext' (fun s => funext fun j => j.elim0) (fun s => by simp [bit, toZ8])
  | succ n ih =>
    cases i with
    | zero =>
      rw [qT_zero, paQ_of]
      refine PA.ext' (fun s => ?_) (fun s => ?_)
      · show (PA.onBottom (m := n) paT).f s = s
        rw [onBottom1_f]
        exact Fin.cons_self_tail s
      · show (PA.onBottom (m := n) paT).ph s = toZ8 (bit s 0)
        rw [onBottom1_ph]
        have hb : bit s 0 = s 0 := by simp [bit]
        rw [hb]
        show (if s 0 = 1 then (1 : ZMod 8) else 0) = toZ8 (s 0)
        rcases fin2_cases (s 0) with h | h <;> simp [h, toZ8]
    | succ i =>
      rw [← sh_qT, paQ_sh, ih]
      refine PA.ext' (fun s => ?_) (fun s => ?_)
      · rw [PA.onTop_f]; exact Fin.cons_self_tail s
      · rw [PA.onTop_ph]; show toZ8 _ = toZ8 _; rw [bit_tail]

theorem paQ_qω {n : ℕ} : paQ (qω : Q n) = ⟨id, fun _ => 1⟩ := rfl

theorem paQ_qCX {n : ℕ} (i : ℕ) :
    paQ (qCX i : Q n) = ⟨fun s => s + bit s (i + 1) • ei i, 0⟩ := by
  induction n generalizing i with
  | zero =>
    have : (qCX i : Q 0) = 1 := qCX_out (by omega)
    rw [this, map_one]
    exact PA.ext' (fun s => funext fun j => j.elim0) (fun s => rfl)
  | succ n ih =>
    cases i with
    | zero =>
      cases n with
      | zero =>
        have : (qCX 0 : Q 1) = 1 := qCX_out (by omega)
        rw [this, map_one]
        refine PA.ext' (fun s => ?_) (fun s => rfl)
        show s = s + bit s (0 + 1) • ei 0
        rw [bit_out _ (by omega)]; simp
      | succ n =>
        rw [qCX_zero, paQ_of]
        refine PA.ext' (fun s => ?_) (fun s => rfl)
        show (PA.onBottom (m := n) paCX).f s = s + bit s (0 + 1) • ei 0
        rw [onBottom2_f]
        have hb : bit s (0 + 1) = s 1 := by simp [bit]
        rw [hb]
        funext j
        refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
          simp [paCX, ei, Fin.tail]
    | succ i =>
      rw [← sh_qCX, paQ_sh, ih]
      refine PA.ext' (fun s => ?_) (fun s => ?_)
      · rw [PA.onTop_f]
        show Fin.cons (s 0) (Fin.tail s + bit (Fin.tail s) (i + 1) • ei i) =
          s + bit s (i + 1 + 1) • ei (i + 1)
        rw [bit_tail]
        funext j
        refine Fin.cases ?_ (fun j => ?_) j <;> simp [ei, Fin.tail]
      · rw [PA.onTop_ph]; rfl

/-- The relabelling of wires by `SWAP` on wires `i, i + 1`. -/
def swq {n : ℕ} (i : ℕ) : Equiv.Perm (Fin n) :=
  if h : i + 1 < n then Equiv.swap ⟨i, by omega⟩ ⟨i + 1, h⟩ else 1

theorem swq_succ_zero {n : ℕ} (i : ℕ) : swq (n := n + 1) (i + 1) 0 = 0 := by
  unfold swq
  split_ifs with h
  · exact Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
  · rfl

theorem swq_succ_succ {n : ℕ} (i : ℕ) (j : Fin n) :
    swq (n := n + 1) (i + 1) j.succ = (swq i j).succ := by
  unfold swq
  by_cases h : i + 1 < n
  · rw [dif_pos (by omega), dif_pos h]
    have e : (⟨i + 1, by omega⟩ : Fin (n + 1)) = Fin.succ ⟨i, by omega⟩ := rfl
    have e' : (⟨i + 1 + 1, by omega⟩ : Fin (n + 1)) = Fin.succ ⟨i + 1, h⟩ := rfl
    rw [e, e', Function.Injective.swap_apply (Fin.succ_injective _)]
  · rw [dif_neg (by omega), dif_neg h]; rfl

theorem swq_zero_zero {n : ℕ} : swq (n := n + 2) 0 0 = 1 := by
  unfold swq; rw [dif_pos (by omega)]; exact Equiv.swap_apply_left _ _

theorem swq_zero_one {n : ℕ} : swq (n := n + 2) 0 1 = 0 := by
  unfold swq; rw [dif_pos (by omega)]; exact Equiv.swap_apply_right _ _

theorem swq_zero_succ_succ {n : ℕ} (j : Fin n) : swq (n := n + 2) 0 j.succ.succ = j.succ.succ := by
  unfold swq; rw [dif_pos (by omega)]
  exact Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])

theorem paQ_qSW {n : ℕ} (i : ℕ) : paQ (qSW i : Q n) = ⟨fun s => s ∘ swq i, 0⟩ := by
  induction n generalizing i with
  | zero =>
    have : (qSW i : Q 0) = 1 := qSW_out (by omega)
    rw [this, map_one]
    exact PA.ext' (fun s => funext fun j => j.elim0) (fun s => rfl)
  | succ n ih =>
    cases i with
    | zero =>
      cases n with
      | zero =>
        have : (qSW 0 : Q 1) = 1 := qSW_out (by omega)
        rw [this, map_one]
        refine PA.ext' (fun s => ?_) (fun s => rfl)
        show s = s ∘ swq 0
        funext j
        simp [swq]
      | succ n =>
        rw [qSW_zero, paQ_of]
        refine PA.ext' (fun s => ?_) (fun s => rfl)
        show (PA.onBottom (m := n) paSW).f s = s ∘ swq 0
        rw [onBottom2_f]
        funext j
        refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
        · rw [Fin.cons_zero, Function.comp_apply, swq_zero_zero]; rfl
        · rw [Fin.cons_succ, Fin.cons_zero, Function.comp_apply]
          rw [show (Fin.succ 0 : Fin (n + 1 + 1)) = 1 from rfl, swq_zero_one]; rfl
        · rw [Fin.cons_succ, Fin.cons_succ, Function.comp_apply, swq_zero_succ_succ]; rfl
    | succ i =>
      rw [← sh_qSW, paQ_sh, ih]
      refine PA.ext' (fun s => ?_) (fun s => ?_)
      · rw [PA.onTop_f]
        funext j
        refine Fin.cases ?_ (fun j => ?_) j
        · rw [Fin.cons_zero]; show s 0 = s (swq (i + 1) 0); rw [swq_succ_zero]
        · rw [Fin.cons_succ]; show Fin.tail s (swq i j) = s (swq (i + 1) j.succ)
          rw [swq_succ_succ]; rfl
      · rw [PA.onTop_ph]; rfl

end QCert.CNOTDihedral
