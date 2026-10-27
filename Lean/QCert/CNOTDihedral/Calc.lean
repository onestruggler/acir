/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Calculating in the theory

The circuits of `n` wires modulo the theory form a group `Q n` (every
generator being invertible, `grouplike`); `mk` sends a circuit to its class,
and two circuits are derivably equal exactly when their classes are equal
(`mk_eq_iff`).  Moving up a wire is a group homomorphism `sh`, and the
phase-affine semantics factors through `Q n` (`paQ`).

The gates at given positions are elements of `Q n`: `qX i`, `qT i` on wire
`i`, `qCX i` (control `i + 1`, target `i`) and `qSW i` on wires `i, i + 1`,
and the scalar `qω`.  A gate that does not fit is `1`.  Gates on disjoint
wires commute, the scalar is central, and the relations of Figure 1 hold
on the bottom wires of every circuit.
-/
import QCert.CNOTDihedral.Soundness
import QCert.CNOTDihedral.Derivation

namespace QCert.CNOTDihedral

open Circuit

/-- Every generator has a left inverse modulo the theory. -/
theorem grouplike (n : ℕ) : Grouplike (Theory n) := by
  intro x
  induction x with
  | @gate0 k c =>
    cases c
    refine ⟨om ^ 7, ?_⟩
    have h := Eqv.rule k Rel.R10
    simp only [Circuit.pad, map_pow, map_one, FreeMonoid.map_of, Gen.pad] at h
    rw [← pow_succ]
    exact h
  | @gate1 k c =>
    cases c
    · exact ⟨FreeMonoid.of (Gen.gate1 Gate.X), Eqv.rule _ Rel.R1⟩
    · refine ⟨T₀ ^ 7, ?_⟩
      have h := Eqv.rule k Rel.R7
      simp only [Circuit.pad, map_pow, map_one, FreeMonoid.map_of, Gen.pad] at h
      rw [← pow_succ]
      exact h
  | gate2 c =>
    cases c
    · exact ⟨FreeMonoid.of (Gen.gate2 Gate.CX), Eqv.rule _ Rel.R4⟩
    · exact ⟨FreeMonoid.of (Gen.gate2 Gate.SW), Eqv.rule _ Rel.swap_swap⟩
  | gate3 c => exact nomatch c
  | up g ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨Circuit.shift u, ?_⟩
    have := Eqv.shift hu
    simpa [map_mul] using this

/-! ### The group of circuits modulo the theory -/

/-- The circuits of `n` wires modulo the theory. -/
abbrev Q (n : ℕ) := (conGen (Theory n)).Quotient

/-- The class of a circuit. -/
abbrev mk {n : ℕ} : Circ n →* Q n := (conGen (Theory n)).mk'

theorem mk_eq_iff {n : ℕ} {w v : Circ n} : mk w = mk v ↔ Eqv n w v :=
  Con.eq _

theorem mk_surjective {n : ℕ} : Function.Surjective (mk : Circ n → Q n) :=
  fun q => Con.mk'_surjective q

theorem exists_left_inv {n : ℕ} (q : Q n) : ∃ r, r * q = 1 := by
  obtain ⟨w, rfl⟩ := mk_surjective q
  induction w using FreeMonoid.inductionOn with
  | one => exact ⟨1, by simp⟩
  | of x =>
    obtain ⟨u, hu⟩ := grouplike n x
    exact ⟨mk u, by rw [← map_mul, mk_eq_iff.2 hu, map_one]⟩
  | mul x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨b * a, by rw [map_mul, mul_assoc, ← mul_assoc a, ha, one_mul, hb]⟩

/-- The circuits modulo the theory form a group. -/
noncomputable instance instGroupQ {n : ℕ} : Group (Q n) :=
  { (inferInstance : Monoid (Q n)) with
    inv := fun q => Classical.choose (exists_left_inv q)
    inv_mul_cancel := fun q => Classical.choose_spec (exists_left_inv q) }

/-- A structural rule or a rule of the theory, as an equation. -/
theorem mk_lift {n : ℕ} {w v : Circ n} (h : Theory n w v) : mk w = mk v :=
  mk_eq_iff.2 (Derivable.of h)

/-- A relation of Figure 1 on the bottom wires. -/
theorem mk_rule {k : ℕ} (m : ℕ) {w v : Circ k} (h : Rel k w v) :
    mk (Circuit.pad m w) = mk (Circuit.pad m v) :=
  mk_eq_iff.2 (Eqv.rule m h)

/-! ### Moving up a wire -/

/-- Moving up one wire, on classes. -/
def sh {n : ℕ} : Q n →* Q (n + 1) :=
  (conGen (Theory n)).lift (mk.comp Circuit.shift)
    (fun _ _ h => (Con.ker_rel _).2 (mk_eq_iff.2 (Eqv.shift h)))

@[simp] theorem sh_mk {n : ℕ} (w : Circ n) : sh (mk w) = mk (Circuit.shift w) := rfl

/-! ### Structural facts -/

theorem mk_comm1 {n : ℕ} (h : Gate 1) (u : Q n) : mk (g1 h) * sh u = sh u * mk (g1 h) := by
  obtain ⟨u, rfl⟩ := mk_surjective u
  induction u using FreeMonoid.inductionOn with
  | one => simp
  | of x => rw [sh_mk, shift_of, ← map_mul, ← map_mul]; exact (mk_lift (Lift.comm1 h x)).symm
  | mul x y hx hy =>
    simp only [map_mul] at hx hy ⊢
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]

theorem mk_comm2 {n : ℕ} (h : Gate 2) (u : Q n) :
    mk (g2 h) * sh (sh u) = sh (sh u) * mk (g2 h) := by
  obtain ⟨u, rfl⟩ := mk_surjective u
  induction u using FreeMonoid.inductionOn with
  | one => simp
  | of x =>
    rw [sh_mk, sh_mk, shift_of, shift_of, ← map_mul, ← map_mul]
    exact (mk_lift (Lift.comm2 h x)).symm
  | mul x y hx hy =>
    simp only [map_mul] at hx hy ⊢
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]

/-- The scalar `ω`. -/
def qω {n : ℕ} : Q n := mk om

@[simp] theorem sh_qω {n : ℕ} : sh (qω : Q n) = qω := mk_lift (Lift.scalar Gate.ω)

/-- The scalar is central. -/
theorem qω_comm_mk {n : ℕ} (x : Gen Gate n) : qω * mk (FreeMonoid.of x) = mk (FreeMonoid.of x) * qω := by
  induction x with
  | gate0 c => cases c; rfl
  | @gate1 m h =>
    rw [← sh_qω]; exact (mk_comm1 h qω).symm
  | @gate2 m h =>
    rw [← sh_qω, ← sh_qω]; exact (mk_comm2 h qω).symm
  | gate3 c => exact nomatch c
  | @up m g ih =>
    rw [← sh_qω, ← shift_of, ← sh_mk, ← map_mul, ih, map_mul]

theorem qω_comm {n : ℕ} (u : Q n) : qω * u = u * qω := by
  obtain ⟨u, rfl⟩ := mk_surjective u
  induction u using FreeMonoid.inductionOn with
  | one => simp
  | of x => exact qω_comm_mk x
  | mul x y hx hy =>
    simp only [map_mul] at hx hy ⊢
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]

/-! ### Gates on given wires -/

/-- A one-wire gate on wire `i` of `n` wires (empty if it does not fit). -/
def onW1 (g : Gate 1) : (n i : ℕ) → Circ n
  | _ + 1, 0 => g1 g
  | n + 1, i + 1 => shift (onW1 g n i)
  | 0, _ => 1

/-- A two-wire gate on wires `i, i+1` of `n` wires (empty if it does not
fit). -/
def onW2 (g : Gate 2) : (n i : ℕ) → Circ n
  | n + 1, i + 1 => shift (onW2 g n i)
  | _ + 2, 0 => g2 g
  | _, _ => 1

/-- `X` on wire `i`. -/
def qX {n : ℕ} (i : ℕ) : Q n := mk (onW1 Gate.X n i)
/-- `T` on wire `i`. -/
def qT {n : ℕ} (i : ℕ) : Q n := mk (onW1 Gate.T n i)
/-- `CNOT` with control `i + 1` and target `i`. -/
def qCX {n : ℕ} (i : ℕ) : Q n := mk (onW2 Gate.CX n i)
/-- `SWAP` on wires `i, i + 1`. -/
def qSW {n : ℕ} (i : ℕ) : Q n := mk (onW2 Gate.SW n i)

@[simp] theorem sh_qX {n : ℕ} (i : ℕ) : sh (qX i : Q n) = qX (i + 1) := rfl
@[simp] theorem sh_qT {n : ℕ} (i : ℕ) : sh (qT i : Q n) = qT (i + 1) := rfl
@[simp] theorem sh_qCX {n : ℕ} (i : ℕ) : sh (qCX i : Q n) = qCX (i + 1) := rfl
@[simp] theorem sh_qSW {n : ℕ} (i : ℕ) : sh (qSW i : Q n) = qSW (i + 1) := rfl

theorem qX_zero {n : ℕ} : (qX 0 : Q (n + 1)) = mk (g1 Gate.X) := rfl
theorem qT_zero {n : ℕ} : (qT 0 : Q (n + 1)) = mk (g1 Gate.T) := rfl
theorem qCX_zero {n : ℕ} : (qCX 0 : Q (n + 2)) = mk (g2 Gate.CX) := rfl
theorem qSW_zero {n : ℕ} : (qSW 0 : Q (n + 2)) = mk (g2 Gate.SW) := rfl

theorem qX_out {n i : ℕ} (h : n ≤ i) : (qX i : Q n) = 1 := by
  induction n generalizing i with
  | zero => simp [qX, onW1]
  | succ n ih =>
    obtain ⟨i, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [← sh_qX, ih (by omega), map_one]

theorem qT_out {n i : ℕ} (h : n ≤ i) : (qT i : Q n) = 1 := by
  induction n generalizing i with
  | zero => simp [qT, onW1]
  | succ n ih =>
    obtain ⟨i, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [← sh_qT, ih (by omega), map_one]

theorem onW2_out (g : Gate 2) : ∀ {n i : ℕ}, n ≤ i + 1 → onW2 g n i = 1
  | 0, _, _ => rfl
  | 1, 0, _ => rfl
  | n + 1, i + 1, h => by
    show shift (onW2 g n i) = 1
    rw [onW2_out g (by omega), map_one]
  | n + 2, 0, h => by omega

theorem qCX_out {n i : ℕ} (h : n ≤ i + 1) : (qCX i : Q n) = 1 := by
  simp [qCX, onW2_out _ h]

theorem qSW_out {n i : ℕ} (h : n ≤ i + 1) : (qSW i : Q n) = 1 := by
  simp [qSW, onW2_out _ h]

/-! ### Commutation of gates on disjoint wires -/

/-- A gate on wire `0` commutes with anything one wire up. -/
theorem qX0_comm_sh {n : ℕ} (u : Q n) : qX 0 * sh u = sh u * qX 0 := mk_comm1 Gate.X u
theorem qT0_comm_sh {n : ℕ} (u : Q n) : qT 0 * sh u = sh u * qT 0 := mk_comm1 Gate.T u
theorem qCX0_comm_sh2 {n : ℕ} (u : Q n) : qCX 0 * sh (sh u) = sh (sh u) * qCX 0 :=
  mk_comm2 Gate.CX u
theorem qSW0_comm_sh2 {n : ℕ} (u : Q n) : qSW 0 * sh (sh u) = sh (sh u) * qSW 0 :=
  mk_comm2 Gate.SW u

/-- Iterated moving up. -/
def shk : (k : ℕ) → {n : ℕ} → Q n →* Q (n + k)
  | 0, _ => MonoidHom.id _
  | k + 1, _ => sh.comp (shk k)

/-- `Comm a b`: `a` and `b` commute. -/
abbrev Comm {G : Type*} [Mul G] (a b : G) : Prop := a * b = b * a

theorem comm_sh {n : ℕ} {a b : Q n} (h : Comm a b) : Comm (sh a) (sh b) := by
  unfold Comm at *; rw [← map_mul, h, map_mul]

theorem comm_symm {G : Type*} [Mul G] {a b : G} (h : Comm a b) : Comm b a := h.symm

/-- One-wire gates on different wires commute. -/
theorem comm_11 (g h : Gate 1) : ∀ {n : ℕ} {i j : ℕ}, i ≠ j →
    Comm (mk (onW1 g n i)) (mk (onW1 h n j))
  | 0, _, _, _ => by simp [onW1, Comm]
  | n + 1, 0, 0, hij => absurd rfl hij
  | n + 1, 0, j + 1, _ => mk_comm1 g (mk (onW1 h n j))
  | n + 1, i + 1, 0, _ => (mk_comm1 h (mk (onW1 g n i))).symm
  | n + 1, i + 1, j + 1, hij => comm_sh (comm_11 g h (n := n) (by omega))

/-- A one-wire gate commutes with a two-wire gate on other wires. -/
theorem comm_12 (g : Gate 1) (h : Gate 2) : ∀ {n : ℕ} {i j : ℕ}, (i + 1 ≤ j ∨ j + 2 ≤ i) →
    Comm (mk (onW1 g n i)) (mk (onW2 h n j))
  | 0, _, _, _ => by simp [onW1, Comm]
  | n + 1, 0, 0, hij => by omega
  | n + 1, 0, j + 1, _ => mk_comm1 g (mk (onW2 h n j))
  | n + 1, 1, 0, hij => by omega
  | n + 1, i + 2, 0, _ => by
    cases n with
    | zero => simp [onW2, Comm]
    | succ n => exact (mk_comm2 h (mk (onW1 g n i))).symm
  | n + 1, i + 1, j + 1, hij => comm_sh (comm_12 g h (n := n) (by omega))

/-- Two-wire gates on disjoint wires commute. -/
theorem comm_22 (g h : Gate 2) : ∀ {n : ℕ} {i j : ℕ}, (i + 2 ≤ j ∨ j + 2 ≤ i) →
    Comm (mk (onW2 g n i)) (mk (onW2 h n j))
  | 0, _, _, _ => by simp [onW2, Comm]
  | n + 1, 0, 0, hij => by omega
  | n + 1, 0, 1, hij => by omega
  | n + 1, 1, 0, hij => by omega
  | n + 1, 0, j + 2, _ => by
    cases n with
    | zero => simp [onW2, Comm]
    | succ n => exact mk_comm2 g (mk (onW2 h n j))
  | n + 1, i + 2, 0, _ => by
    cases n with
    | zero => simp [onW2, Comm]
    | succ n => exact (mk_comm2 h (mk (onW2 g n i))).symm
  | n + 1, i + 1, j + 1, hij => comm_sh (comm_22 g h (n := n) (by omega))

end QCert.CNOTDihedral
