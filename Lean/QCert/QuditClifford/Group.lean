/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The group of circuits modulo the rules

Circuits on `n` wires modulo derivability form a monoid `CG p g n` (the
quotient of the free monoid by the congruence of the theory), and since
every generator has an inverse modulo the rules (`grouplike`), a group.
The matrix semantics factors through it (`semG`), and moving a circuit up
one wire is a homomorphism `ι : CG n →* CG (n + 1)`.

Completeness of the rules is injectivity of `semG` (`mk_eq_mk`): two
circuits are derivably equal exactly when their classes are equal.

`OddGen p g` packages the standing hypotheses of Theorem 4.10: `p` is an
odd prime and `g` generates `ℤ_p^*`.  The group structure needs it, since
`H³` is an inverse of `H` only through `g` (`H_pow_four`).
-/
import QCert.QuditClifford.Theory
import Mathlib.Algebra.Group.Units.Defs

namespace QCert.QuditClifford

variable (p : ℕ) [hp : Fact p.Prime]

/-- `p` is an odd prime and `g` generates the multiplicative group `ℤ_p^*`. -/
class OddGen (g : ZMod p) : Prop where
  hp2 : p ≠ 2
  hg : ∀ a : ZMod p, a ≠ 0 → ∃ k : ℕ, g ^ k = a

theorem OddGen.ne_zero (g : ZMod p) [h : OddGen p g] : g ≠ 0 :=
  ne_zero_of_generates p h.hp2 g h.hg

variable (g : ZMod p)

/-- The congruence of the theory on `n`-wire circuits. -/
def Cn (n : ℕ) : Con (Circ n) := conGen (Theory p g n)

/-- Circuits modulo the rules. -/
def CG (n : ℕ) : Type := (Cn p g n).Quotient

instance (n : ℕ) : Monoid (CG p g n) := inferInstanceAs (Monoid (Cn p g n).Quotient)

/-- The class of a circuit. -/
def mk (n : ℕ) : Circ n →* CG p g n := (Cn p g n).mk'

variable {p g}

theorem mk_eq_mk {n : ℕ} {w v : Circ n} :
    mk p g n w = mk p g n v ↔ Derives (Padded (Rule p g)) n w v :=
  Con.eq (Cn p g n)

theorem mk_surjective (n : ℕ) : Function.Surjective (mk p g n) :=
  Con.mk'_surjective

/-- Induction over classes of circuits, one generator at a time. -/
theorem CG.induction_on {n : ℕ} {P : CG p g n → Prop} (x : CG p g n) (h1 : P 1)
    (hmul : ∀ (y : Gen Gate n) (x : CG p g n), P x → P (mk p g n (FreeMonoid.of y) * x)) : P x := by
  obtain ⟨w, rfl⟩ := mk_surjective n x
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact h1
  | mul_of y w ih => rw [map_mul]; exact hmul y _ ih

/-- In a monoid in which every element has a left inverse, every element is a
unit. -/
theorem isUnit_of_forall_left_inv {M : Type*} [Monoid M] (h : ∀ a : M, ∃ b, b * a = 1)
    (a : M) : IsUnit a := by
  obtain ⟨b, hb⟩ := h a
  obtain ⟨c, hc⟩ := h b
  have hca : c = a := by
    calc c = c * (b * a) := by rw [hb, mul_one]
      _ = a := by rw [← mul_assoc, hc, one_mul]
  exact ⟨⟨a, b, by rw [← hca, hc], hb⟩, rfl⟩

/-! ### Moving up one wire -/

variable (p g) in
theorem le_ker_shift (n : ℕ) : Cn p g n ≤ Con.ker ((mk p g (n + 1)).comp Circuit.shift) :=
  Con.conGen_le fun _ _ h => (Con.ker_rel _).2 (by
    show mk p g (n + 1) (Circuit.shift _) = mk p g (n + 1) (Circuit.shift _)
    exact mk_eq_mk.2 (derives_shift p g (Derivable.of h)))

variable (p g) in
/-- Moving a class of circuits up one wire. -/
def ι (n : ℕ) : CG p g n →* CG p g (n + 1) :=
  (Cn p g n).lift ((mk p g (n + 1)).comp Circuit.shift) (le_ker_shift p g n)

@[simp] theorem ι_mk {n : ℕ} (w : Circ n) : ι p g n (mk p g n w) = mk p g (n + 1) (Circuit.shift w) :=
  rfl

variable [OddGen p g]

theorem CG.left_inv {n : ℕ} (x : CG p g n) : ∃ y, y * x = 1 := by
  refine CG.induction_on (P := fun x => ∃ y, y * x = 1) x ⟨1, mul_one 1⟩ ?_
  intro y x ⟨b, hb⟩
  obtain ⟨u, hu⟩ := grouplike p (OddGen.hp2 g) g (OddGen.hg) n y
  refine ⟨b * mk p g n u, ?_⟩
  have hu' : mk p g n u * mk p g n (FreeMonoid.of y) = 1 := by
    rw [← map_mul, ← map_one (mk p g n)]; exact mk_eq_mk.2 hu
  rw [mul_assoc, ← mul_assoc (mk p g n u), hu', one_mul, hb]

/-- Circuits modulo the rules form a group. -/
noncomputable instance (n : ℕ) : Group (CG p g n) :=
  groupOfIsUnit (isUnit_of_forall_left_inv CG.left_inv)

/-! ### The semantics on classes -/

theorem le_ker_sem (n : ℕ) : Cn p g n ≤ Con.ker (sem p n) :=
  Con.conGen_le fun _ _ h =>
    (Con.ker_rel _).2 (theory_sound p (OddGen.hp2 g) g (OddGen.ne_zero p g) h)

/-- The matrix of a class of circuits. -/
noncomputable def semG (n : ℕ) : CG p g n →* Matrix.unitaryGroup (State p n) ℂ :=
  (Cn p g n).lift (sem p n) (le_ker_sem n)

@[simp] theorem semG_mk {n : ℕ} (w : Circ n) : semG n (mk p g n w) = sem p n w := rfl

end QCert.QuditClifford
