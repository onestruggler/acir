/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The semantic operators `P_g D_q`

Section 3.3 of Blake (arXiv:2603.06466): an operator of a phase-affine
circuit on `n` qudits first multiplies the basis vector `|x⟩` by `ω^{q(x)}`
and then relabels it to `|g(x)⟩`, where `g` is a map of labels and
`q : 𝔽_d^n → 𝔽_d` a phase function.  `PA d n` holds the pair `(g, q)` (as
`f`, `q`), and composes as the paper's Definition 13:
`P_{g₂} D_{q₂} ∘ P_{g₁} D_{q₁} = P_{g₂ ∘ g₁} D_{q₁ + q₂ ∘ g₁}`.

A label vector `v : Fin n → ZMod d` carries on wire `i` the label `v i`
(wire `0` the bottom wire).  Given an additive character `ψ` of `𝔽_d` (the
map `a ↦ ω^a`), `toOp ψ p` is the matrix of `P_g D_q` on basis states
(`State d n`), and gate data `GateData` (a pair for each gate) give a
`GateSem`, whose circuit semantics is the matrix of the composite pair
(`GateData.sem_val`).  When `ψ` is injective, the matrix determines the
pair (`toOp_injective`, the paper's Remark 2).
-/
import QCert.Circuit.Semantics
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.AddChar

namespace QCert.PhaseAffine

open Matrix

/-- Label vectors of `n` qudits, read in `𝔽_d` (`v i` is the label on wire
`i`). -/
abbrev Lab (d n : ℕ) := Fin n → ZMod d

/-- The operator `P_f D_q`: the phase `ω^{q(x)}`, then the relabelling
`x ↦ f x`. -/
@[ext] structure PA (d n : ℕ) where
  /-- The relabelling. -/
  f : Lab d n → Lab d n
  /-- The phase function. -/
  q : Lab d n → ZMod d

namespace PA

variable {d n : ℕ}

/-- Composition in operator order: `p * p'` applies `p'` first. -/
instance : Mul (PA d n) := ⟨fun p p' => ⟨p.f ∘ p'.f, fun v => p'.q v + p.q (p'.f v)⟩⟩

instance : One (PA d n) := ⟨⟨id, fun _ => 0⟩⟩

@[simp] theorem mul_f (p p' : PA d n) : (p * p').f = p.f ∘ p'.f := rfl
@[simp] theorem mul_q (p p' : PA d n) (v : Lab d n) :
    (p * p').q v = p'.q v + p.q (p'.f v) := rfl
@[simp] theorem one_f : (1 : PA d n).f = id := rfl
@[simp] theorem one_q (v : Lab d n) : (1 : PA d n).q v = 0 := rfl

instance : Monoid (PA d n) where
  mul_assoc a b c := by
    ext v
    · rfl
    · simp only [mul_q, mul_f, Function.comp_apply, add_assoc]
  one_mul a := by ext v <;> simp
  mul_one a := by ext v <;> simp

theorem pow_succ_f (p : PA d n) (m : ℕ) (v : Lab d n) :
    (p ^ (m + 1)).f v = (p ^ m).f (p.f v) := by
  rw [pow_succ]; rfl

theorem pow_f (p : PA d n) (m : ℕ) : (p ^ m).f = p.f^[m] := by
  induction m with
  | zero => rfl
  | succ m ih => funext v; rw [pow_succ_f, ih, Function.iterate_succ_apply]

/-- A diagonal operator `D_q`. -/
def diag (q : Lab d n → ZMod d) : PA d n := ⟨id, q⟩

/-- A relabelling `P_f` with no phase. -/
def perm (f : Lab d n → Lab d n) : PA d n := ⟨f, fun _ => 0⟩

/-- The scalar `ω^c`. -/
def scalar (c : ZMod d) : PA d n := diag fun _ => c

@[simp] theorem diag_f (q : Lab d n → ZMod d) : (diag q).f = id := rfl
@[simp] theorem diag_q (q : Lab d n → ZMod d) : (diag q).q = q := rfl
@[simp] theorem perm_f (f : Lab d n → Lab d n) : (perm f).f = f := rfl
@[simp] theorem perm_q (f : Lab d n → Lab d n) (v : Lab d n) : (perm f).q v = 0 := rfl

theorem diag_mul (q q' : Lab d n → ZMod d) : diag q * diag q' = diag (q + q') := by
  ext v <;> simp [diag, add_comm]

theorem diag_pow (q : Lab d n → ZMod d) (m : ℕ) : diag q ^ m = diag (m • q) := by
  induction m with
  | zero => ext v <;> simp [diag]
  | succ m ih => rw [pow_succ, ih, diag_mul, succ_nsmul]

theorem perm_mul (f f' : Lab d n → Lab d n) : perm f * perm f' = perm (f ∘ f') := by
  ext v <;> simp [perm]

theorem perm_pow (f : Lab d n → Lab d n) (m : ℕ) : perm f ^ m = perm f^[m] := by
  ext v
  · rw [pow_f]; rfl
  · induction m generalizing v with
    | zero => rfl
    | succ m ih => rw [pow_succ]; simp [ih]

/-! ### Operators on some of the wires -/

/-- The labels of the bottom `k` of `n + k` wires. -/
def low {n k : ℕ} (v : Lab d (n + k)) : Lab d k := fun i => v ⟨i, by omega⟩

/-- The labels of the top `n` of `n + 1` wires. -/
def high {n : ℕ} (v : Lab d (n + 1)) : Lab d n := fun j => v ⟨1 + j, by omega⟩

/-- An operator on the bottom `k` of `n + k` wires. -/
def onBottom (n : ℕ) {k : ℕ} (p : PA d k) : PA d (n + k) where
  f v i := if h : (i : ℕ) < k then p.f (low v) ⟨i, h⟩ else v i
  q v := p.q (low v)

/-- An operator moved up one wire. -/
def onTop {n : ℕ} (p : PA d n) : PA d (n + 1) where
  f v i := if h : (i : ℕ) = 0 then v i else p.f (high v) ⟨i - 1, by omega⟩
  q v := p.q (high v)

theorem onBottom_f_lt (m : ℕ) {k : ℕ} (p : PA d k) (v : Lab d (m + k)) (i : Fin (m + k))
    (h : (i : ℕ) < k) : (onBottom m p).f v i = p.f (low v) ⟨i, h⟩ := dif_pos h

theorem onBottom_f_ge (m : ℕ) {k : ℕ} (p : PA d k) (v : Lab d (m + k)) (i : Fin (m + k))
    (h : ¬ (i : ℕ) < k) : (onBottom m p).f v i = v i := dif_neg h

@[simp] theorem onBottom_q (m : ℕ) {k : ℕ} (p : PA d k) (v : Lab d (m + k)) :
    (onBottom m p).q v = p.q (low v) := rfl

theorem onTop_f_zero (p : PA d n) (v : Lab d (n + 1)) (i : Fin (n + 1)) (h : (i : ℕ) = 0) :
    (onTop p).f v i = v i := dif_pos h

theorem onTop_f_pos (p : PA d n) (v : Lab d (n + 1)) (i : Fin (n + 1)) (h : ¬ (i : ℕ) = 0) :
    (onTop p).f v i = p.f (high v) ⟨i - 1, by omega⟩ := dif_neg h

@[simp] theorem onTop_q (p : PA d n) (v : Lab d (n + 1)) : (onTop p).q v = p.q (high v) := rfl

@[simp] theorem low_onBottom (m : ℕ) {k : ℕ} (p : PA d k) (v : Lab d (m + k)) :
    low ((onBottom m p).f v) = p.f (low v) := by
  funext i; simp only [low]; rw [onBottom_f_lt _ _ _ _ i.2]

@[simp] theorem high_onTop (p : PA d n) (v : Lab d (n + 1)) :
    high ((onTop p).f v) = p.f (high v) := by
  funext j
  simp only [high]
  rw [onTop_f_pos _ _ _ (by simp)]
  congr 1; ext; simp

theorem onBottom_mul (m : ℕ) {k : ℕ} (p p' : PA d k) :
    onBottom m (p * p') = onBottom m p * onBottom m p' := by
  ext v i
  · by_cases h : (i : ℕ) < k
    · simp only [mul_f, Function.comp_apply, onBottom_f_lt _ _ _ _ h, low_onBottom]
    · simp only [mul_f, Function.comp_apply, onBottom_f_ge _ _ _ _ h]
  · simp only [mul_q, onBottom_q, low_onBottom]

theorem onBottom_one (m : ℕ) {k : ℕ} : onBottom m (1 : PA d k) = 1 := by
  ext v i
  · simp only [onBottom, one_f, id]
    split_ifs <;> rfl
  · rfl

theorem onTop_mul (p p' : PA d n) : onTop (p * p') = onTop p * onTop p' := by
  ext v i
  · by_cases h : (i : ℕ) = 0
    · simp only [mul_f, Function.comp_apply, onTop_f_zero _ _ _ h]
    · simp only [mul_f, Function.comp_apply, onTop_f_pos _ _ _ h, high_onTop]
  · simp only [mul_q, onTop_q, high_onTop]

theorem onTop_one : onTop (1 : PA d n) = 1 := by
  ext v i
  · simp only [onTop, one_f, id]
    split_ifs with h
    · rfl
    · simp only [high]; congr 1; ext; simp; omega
  · rfl

/-- `onBottom` as a monoid homomorphism. -/
def onBottomHom (m : ℕ) {k : ℕ} : PA d k →* PA d (m + k) where
  toFun := onBottom m
  map_one' := onBottom_one m
  map_mul' := onBottom_mul m

/-- `onTop` as a monoid homomorphism. -/
def onTopHom : PA d n →* PA d (n + 1) where
  toFun := onTop
  map_one' := onTop_one
  map_mul' := onTop_mul

@[simp] theorem onBottomHom_apply (m : ℕ) {k : ℕ} (p : PA d k) :
    onBottomHom m p = onBottom m p := rfl
@[simp] theorem onTopHom_apply (p : PA d n) : onTopHom p = onTop p := rfl

theorem onBottom_scalar (m : ℕ) {k : ℕ} (c : ZMod d) :
    onBottom m (scalar c : PA d k) = scalar c := by
  ext v i
  · simp only [onBottom, scalar, diag, id]
    split_ifs <;> rfl
  · rfl

theorem onTop_scalar (c : ZMod d) : onTop (scalar c : PA d n) = scalar c := by
  ext v i
  · simp only [onTop, scalar, diag, id]
    split_ifs with h
    · rfl
    · simp only [high]; congr 1; ext; simp; omega
  · rfl

private theorem lab_congr {m : ℕ} (v : Lab d m) {i j : ℕ} (hi : i < m) (hj : j < m)
    (h : i = j) : v ⟨i, hi⟩ = v ⟨j, hj⟩ := by
  subst h; rfl

theorem onBottom_onBottom1 (m n' : ℕ) (p : PA d 1) :
    onBottom m (onBottom n' p) = onBottom (m + n') p := by
  ext v i
  · simp only [onBottom, low]
    split_ifs with h1 h2 h2 <;> first | rfl | omega
  · rfl

theorem onBottom_onBottom2 (m n' : ℕ) (p : PA d 2) :
    onBottom m (onBottom n' p) = onBottom (m + n') p := by
  ext v i
  · simp only [onBottom, low]
    split_ifs with h1 h2 h2 <;> first | rfl | omega
  · rfl

theorem onBottom_onBottom3 (m n' : ℕ) (p : PA d 3) :
    onBottom m (onBottom n' p) = onBottom (m + n') p := by
  ext v i
  · simp only [onBottom, low]
    split_ifs with h1 h2 h2 <;> first | rfl | omega
  · rfl

theorem onBottom_onTop (m : ℕ) (p : PA d n) :
    onBottom m (onTop p) = onTop (onBottom m p) := by
  ext v i
  · simp only [onBottom, onTop, low, high]
    split_ifs <;> first | rfl | omega | exact lab_congr v _ _ (by omega)
  · rfl

end PA

/-! ### Gate data and the circuit semantics -/

/-- The operators `P_g D_q` of a gate set: a phase for each scalar, and a
pair for each gate on its own wires. -/
structure GateData (Gate : ℕ → Type) (d : ℕ) where
  scalar : Gate 0 → ZMod d
  gate1 : Gate 1 → PA d 1
  gate2 : Gate 2 → PA d 2
  gate3 : Gate 3 → PA d 3

namespace GateData

variable {Gate : ℕ → Type} {d : ℕ} (D : GateData Gate d)

/-- The operator of a generator. -/
def gen : {n : ℕ} → Gen Gate n → PA d n
  | _, .gate0 g => PA.scalar (D.scalar g)
  | _, .gate1 g => PA.onBottom _ (D.gate1 g)
  | _, .gate2 g => PA.onBottom _ (D.gate2 g)
  | _, .gate3 g => PA.onBottom _ (D.gate3 g)
  | _, .up g => PA.onTop (gen g)

/-- The operator of a circuit. -/
def sem (n : ℕ) : Circuit Gate n →* PA d n := FreeMonoid.lift D.gen

@[simp] theorem sem_of {n : ℕ} (g : Gen Gate n) : D.sem n (FreeMonoid.of g) = D.gen g :=
  FreeMonoid.lift_eval_of _ _

theorem sem_shift {n : ℕ} (w : Circuit Gate n) :
    D.sem (n + 1) (Circuit.shift w) = PA.onTop (D.sem n w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [PA.onTop_one]
  | mul_of g w ih =>
    rw [map_mul, map_mul, Circuit.shift_of, ih, map_mul, PA.onTop_mul]
    rfl

theorem gen_pad (m : ℕ) {k : ℕ} (g : Gen Gate k) :
    D.gen (g.pad m) = PA.onBottom m (D.gen g) := by
  induction g with
  | gate0 c => exact (PA.onBottom_scalar m _).symm
  | gate1 c => exact (PA.onBottom_onBottom1 _ _ _).symm
  | gate2 c => exact (PA.onBottom_onBottom2 _ _ _).symm
  | gate3 c => exact (PA.onBottom_onBottom3 _ _ _).symm
  | up g ih =>
    show PA.onTop (D.gen (g.pad m)) = _
    rw [ih]; exact (PA.onBottom_onTop m _).symm

theorem sem_pad (m : ℕ) {k : ℕ} (w : Circuit Gate k) :
    D.sem (m + k) (Circuit.pad m w) = PA.onBottom m (D.sem k w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [PA.onBottom_one]
  | mul_of g w ih =>
    rw [map_mul (Circuit.pad m), map_mul, ih, map_mul (D.sem k), PA.onBottom_mul]
    congr 1
    exact D.gen_pad m g

end GateData

/-! ### Matrices -/

section Matrices

variable {d : ℕ} [NeZero d] {A : Type*} [CommRing A]

/-- The labels in `𝔽_d` of a basis state. -/
def lbl {n : ℕ} : State d n ≃ Lab d n :=
  Equiv.piCongrRight fun _ => (ZMod.finEquiv d).toEquiv

@[simp] theorem lbl_apply {n : ℕ} (s : State d n) (i : Fin n) :
    lbl s i = ZMod.finEquiv d (s i) := rfl

/-- The matrix of `P_f D_q` on basis states, given the character
`ψ : a ↦ ω^a`: the column of `|t⟩` holds `ω^{q(t)}` in the row of `|f(t)⟩`. -/
def toOp (ψ : AddChar (ZMod d) A) {n : ℕ} (p : PA d n) : Op A d n :=
  fun s t => if lbl s = p.f (lbl t) then ψ (p.q (lbl t)) else 0

variable (ψ : AddChar (ZMod d) A)

private theorem sum_single {n : ℕ} (a : Lab d n) (F : State d n → A) :
    ∑ u : State d n, (if lbl u = a then F u else 0) = F (lbl.symm a) := by
  rw [Finset.sum_eq_single (lbl.symm a)]
  · simp
  · intro u _ hu
    rw [if_neg]
    intro h; exact hu (by rw [← h]; simp)
  · simp

theorem toOp_mul {n : ℕ} (p p' : PA d n) : toOp ψ (p * p') = toOp ψ p * toOp ψ p' := by
  ext s t
  simp only [toOp, mul_apply]
  have : ∀ u : State d n,
      ((if lbl s = p.f (lbl u) then ψ (p.q (lbl u)) else 0) *
        if lbl u = p'.f (lbl t) then ψ (p'.q (lbl t)) else 0) =
      if lbl u = p'.f (lbl t) then
        (if lbl s = p.f (lbl u) then ψ (p.q (lbl u)) else 0) * ψ (p'.q (lbl t)) else 0 := by
    intro u; split_ifs <;> simp
  simp only [this]
  rw [sum_single]
  simp only [Equiv.apply_symm_apply, PA.mul_f, PA.mul_q, Function.comp_apply]
  split_ifs <;> simp [AddChar.map_add_eq_mul, mul_comm]

theorem toOp_one {n : ℕ} : toOp ψ (1 : PA d n) = 1 := by
  ext s t
  simp only [toOp, PA.one_f, id, PA.one_q, AddChar.map_zero_eq_one, one_apply]
  simp [lbl.injective.eq_iff]

theorem toOp_scalar {n : ℕ} (c : ZMod d) : toOp ψ (PA.scalar c : PA d n) = ψ c • 1 := by
  ext s t
  simp only [toOp, PA.scalar, PA.diag_f, id, PA.diag_q, smul_apply, one_apply, smul_eq_mul]
  simp [lbl.injective.eq_iff]

theorem toOp_onBottom {m k : ℕ} (p : PA d k) :
    toOp ψ (PA.onBottom m p) = onBottom (n := m) (toOp ψ p) := by
  ext s t
  rw [onBottom_apply']
  simp only [toOp]
  have hlow : ∀ u : State d (m + k),
      PA.low (lbl u) = lbl (fun i : Fin k => u ⟨i, by omega⟩) :=
    fun u => rfl
  by_cases hC : ∀ i (hi : i < m + k), k ≤ i → s ⟨i, hi⟩ = t ⟨i, hi⟩
  · rw [if_pos hC]
    simp only [PA.onBottom, ← hlow]
    congr 1
    apply propext
    constructor
    · intro h; funext i
      have := congrFun h ⟨i, by omega⟩
      simpa [i.2] using this
    · intro h; funext i
      by_cases hi : (i : ℕ) < k
      · rw [dif_pos hi, ← h]; rfl
      · rw [dif_neg hi]; simp [hC i i.2 (by omega)]
  · rw [if_neg hC, if_neg]
    intro h
    apply hC
    intro i hi hk
    have := congrFun h ⟨i, hi⟩
    simp only [PA.onBottom, dif_neg (show ¬ i < k by omega), lbl_apply] at this
    exact (ZMod.finEquiv d).injective this

theorem toOp_onTop {n : ℕ} (p : PA d n) :
    toOp ψ (PA.onTop p) = onTop 1 (toOp ψ p) := by
  ext s t
  rw [onTop_apply]
  simp only [toOp, PA.onTop_q]
  have hhigh : ∀ u : State d (n + 1), PA.high (lbl u) = lbl (split d n 1 u).2 :=
    fun u => rfl
  have h0 : ∀ u : State d (n + 1), (split d n 1 u).1 0 = u 0 := fun u => rfl
  by_cases hC : (split d n 1 s).1 = (split d n 1 t).1
  · rw [if_pos hC, hhigh]
    congr 1
    apply propext
    constructor
    · intro h; funext j
      have := congrFun h ⟨1 + j, by omega⟩
      rw [PA.onTop_f_pos _ _ _ (by simp)] at this
      exact this.trans (congrArg (p.f (PA.high (lbl t))) (Fin.ext (by simp)))
    · intro h; funext i
      by_cases hi : (i : ℕ) = 0
      · rw [PA.onTop_f_zero _ _ _ hi]
        have := congrFun hC 0
        rw [h0, h0] at this
        rw [show i = 0 from Fin.ext hi, lbl_apply, lbl_apply, this]
      · rw [PA.onTop_f_pos _ _ _ hi, hhigh, ← h]
        exact congrArg (lbl s) (Fin.ext (by simp; omega))
  · rw [if_neg hC, if_neg]
    intro h
    apply hC
    funext i
    have := congrFun h 0
    rw [PA.onTop_f_zero _ _ _ rfl, lbl_apply, lbl_apply] at this
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact (ZMod.finEquiv d).injective this

variable [StarRing A]

theorem toOp_mem_unitaryGroup (hψ : ∀ a, star (ψ a) = ψ (-a)) {n : ℕ} (p : PA d n)
    (hf : Function.Injective p.f) : toOp ψ p ∈ unitaryGroup (State d n) A := by
  rw [mem_unitaryGroup_iff']
  ext s t
  simp only [mul_apply, star_apply, toOp, one_apply]
  have : ∀ u : State d n,
      (star (if lbl u = p.f (lbl s) then ψ (p.q (lbl s)) else 0) *
        if lbl u = p.f (lbl t) then ψ (p.q (lbl t)) else 0) =
      if lbl u = p.f (lbl s) then
        (if p.f (lbl s) = p.f (lbl t) then ψ (- p.q (lbl s)) * ψ (p.q (lbl t)) else 0)
      else 0 := by
    intro u; split_ifs with h1 h2 h3 <;> simp_all
  simp only [this]
  rw [sum_single]
  simp only [hf.eq_iff, lbl.injective.eq_iff]
  split_ifs with h
  · subst h; rw [← AddChar.map_add_eq_mul]; simp
  · rfl

omit [NeZero d] in
theorem psi_mem_unitary (hψ : ∀ a, star (ψ a) = ψ (-a)) (a : ZMod d) : ψ a ∈ unitary A := by
  rw [Unitary.mem_iff, hψ, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  simp

end Matrices

namespace GateData

variable {Gate : ℕ → Type} {d : ℕ} [NeZero d] {A : Type*} [CommRing A] [StarRing A]
  (D : GateData Gate d) (ψ : AddChar (ZMod d) A) (hψ : ∀ a, star (ψ a) = ψ (-a))

/-- The relabellings of the gates are injective. -/
structure Injective : Prop where
  gate1 : ∀ g, Function.Injective (D.gate1 g).f
  gate2 : ∀ g, Function.Injective (D.gate2 g).f
  gate3 : ∀ g, Function.Injective (D.gate3 g).f

/-- The matrices `toOp ψ` of the gates, as a `GateSem`. -/
def toGateSem (hD : D.Injective) : GateSem Gate A d where
  scalar g := ⟨ψ (D.scalar g), psi_mem_unitary ψ hψ _⟩
  gate1 g := ⟨toOp ψ (D.gate1 g), toOp_mem_unitaryGroup ψ hψ _ (hD.gate1 g)⟩
  gate2 g := ⟨toOp ψ (D.gate2 g), toOp_mem_unitaryGroup ψ hψ _ (hD.gate2 g)⟩
  gate3 g := ⟨toOp ψ (D.gate3 g), toOp_mem_unitaryGroup ψ hψ _ (hD.gate3 g)⟩

theorem toGateSem_gen (hD : D.Injective) {n : ℕ} (g : Gen Gate n) :
    ((D.toGateSem ψ hψ hD).gen g).1 = toOp ψ (D.gen g) := by
  induction g with
  | gate0 c => exact (toOp_scalar ψ _).symm
  | gate1 c => exact (toOp_onBottom ψ _).symm
  | gate2 c => exact (toOp_onBottom ψ _).symm
  | gate3 c => exact (toOp_onBottom ψ _).symm
  | up g ih =>
    show onTop 1 _ = _
    rw [ih]; exact (toOp_onTop ψ _).symm

/-- The matrix of a circuit is the matrix of its pair `(g, q)`. -/
theorem toGateSem_sem (hD : D.Injective) {n : ℕ} (w : Circuit Gate n) :
    ((D.toGateSem ψ hψ hD).sem n w).1 = toOp ψ (D.sem n w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [GateSem.sem, toOp_one]
  | mul_of g w ih =>
    rw [map_mul, map_mul, Submonoid.coe_mul, ih, toOp_mul]
    congr 1
    simpa [GateSem.sem] using D.toGateSem_gen ψ hψ hD g

end GateData

/-- With an injective character, the matrix determines the pair (Remark 2). -/
theorem toOp_injective {d : ℕ} [NeZero d] {A : Type*} [CommRing A] (ψ : AddChar (ZMod d) A)
    (hinj : Function.Injective ψ) {n : ℕ} : Function.Injective (toOp ψ (n := n)) := by
  intro p p' h
  by_cases hA : (0 : A) = 1
  · have hs : ∀ a b : ZMod d, a = b := fun a b =>
      hinj ((subsingleton_of_zero_eq_one hA).elim _ _)
    exact PA.ext (funext fun v => funext fun i => hs _ _) (funext fun v => hs _ _)
  have hne : ∀ a, ψ a ≠ 0 := by
    intro a ha
    have h1 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul]; simp
    rw [ha, zero_mul] at h1
    exact hA h1
  have key : ∀ t : State d n, p.f (lbl t) = p'.f (lbl t) ∧ p.q (lbl t) = p'.q (lbl t) := by
    intro t
    have e := congrFun (congrFun h (lbl.symm (p.f (lbl t)))) t
    simp only [toOp, Equiv.apply_symm_apply, if_true] at e
    split_ifs at e with h'
    · exact ⟨h', hinj e⟩
    · exact absurd e (hne _)
  refine PA.ext (funext fun v => ?_) (funext fun v => ?_)
  · obtain ⟨h1, -⟩ := key (lbl.symm v); simpa using h1
  · obtain ⟨-, h2⟩ := key (lbl.symm v); simpa using h2

end QCert.PhaseAffine
