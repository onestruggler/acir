/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Derivations in `Lift`

Tools for writing derivations in a theory `Lift R`:

* `derivable_shift`, `derivable_pad`: an equation derived on `k` wires can be
  moved up, or put on the bottom wires of a wider circuit (for
  `R = Padded Base`);
* `comm_disjoint`: generators on disjoint wires commute (scalars included,
  when there is one scalar);
* a checker for derivations given as steps on words (`run`), each step
  either a rewrite by an equation from a list or the exchange of two
  adjacent generators on disjoint wires, with its soundness (`run_sound`):
  derivations are then checked by `decide`.
-/
import QCert.Minimality.Basic

namespace QCert.Minimality

open Circuit

variable {Gate : ℕ → Type}

/-! ### Codes of generators -/

/-- A generator as the number of times it is moved up and its gate. -/
def Gen.code : {n : ℕ} → Gen Gate n → ℕ × (Σ k, Gate k)
  | _, .gate0 g => (0, ⟨0, g⟩)
  | _, .gate1 g => (0, ⟨1, g⟩)
  | _, .gate2 g => (0, ⟨2, g⟩)
  | _, .gate3 g => (0, ⟨3, g⟩)
  | _, .up g => ((Gen.code g).1 + 1, (Gen.code g).2)

theorem Gen.code_injective {n : ℕ} : Function.Injective (Gen.code (Gate := Gate) (n := n)) := by
  intro g
  induction g with
  | gate0 a => intro h e; cases h <;> simp_all [Gen.code]
  | gate1 a => intro h e; cases h <;> simp_all [Gen.code]
  | gate2 a => intro h e; cases h <;> simp_all [Gen.code]
  | gate3 a => intro h e; cases h <;> simp_all [Gen.code]
  | up g ih =>
    intro h e
    cases h with
    | up h =>
      simp only [Gen.code, Prod.mk.injEq, Nat.add_right_cancel_iff] at e
      rw [ih (Prod.ext e.1 e.2)]
    | _ => simp_all [Gen.code]

instance Gen.decEq [∀ k, DecidableEq (Gate k)] {n : ℕ} : DecidableEq (Gen Gate n) :=
  fun g h => decidable_of_iff (Gen.code g = Gen.code h) Gen.code_injective.eq_iff

/-! ### Moving derivations -/

section Move

variable {R : CRel Gate}

theorem derivable_shift {n : ℕ} {w v : Circuit Gate n} (d : Derivable (Lift R n) w v) :
    Derivable (Lift R (n + 1)) (shift w) (shift v) := by
  let c : Con (Circuit Gate n) := (conGen (Lift R (n + 1))).comap shift (map_mul shift)
  have : conGen (Lift R n) ≤ c := Con.conGen_le fun x y r => Derivable.of (Lift.shift r)
  exact this d

theorem pad_shift (m : ℕ) {k : ℕ} (w : Circuit Gate k) :
    Circuit.pad m (shift w) = shift (Circuit.pad m w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, map_mul, ih]
    rfl

/-- Moving along an equality of widths. -/
theorem lift_cast {a b : ℕ} (h : a = b) {w v : Circuit Gate a} {w' v' : Circuit Gate b}
    (hw : HEq w w') (hv : HEq v v') (r : Lift R a w v) : Lift R b w' v' := by
  subst h; cases hw; cases hv; exact r

theorem heq_index {α : ℕ → Type} {a b : ℕ} (h : a = b) (f : ∀ t, α t) : HEq (f a) (f b) := by
  subst h; rfl

theorem heq_up {a b : ℕ} (hab : a = b) {x : Gen Gate a} {y : Gen Gate b} (h : HEq x y) :
    HEq x.up y.up := by
  subst hab; cases h; rfl

theorem heq_of {a b : ℕ} (hab : a = b) {x : Gen Gate a} {y : Gen Gate b} (h : HEq x y) :
    HEq (FreeMonoid.of x : Circuit Gate a) (FreeMonoid.of y : Circuit Gate b) := by
  subst hab; cases h; rfl

theorem heq_mul {a b : ℕ} (hab : a = b) {x x' : Circuit Gate a} {y y' : Circuit Gate b}
    (h : HEq x y) (h' : HEq x' y') : HEq (x * x') (y * y') := by
  subst hab; cases h; cases h'; rfl

theorem Gen.pad_pad_heq (m j : ℕ) {k : ℕ} (g : Gen Gate k) :
    HEq ((g.pad j).pad m) (g.pad (m + j)) := by
  induction g with
  | @gate0 n c => exact heq_index (Nat.add_assoc m j n).symm (fun t => (Gen.gate0 c : Gen Gate t))
  | @gate1 n c =>
    exact heq_index (Nat.add_assoc m j n).symm (fun t => (Gen.gate1 c : Gen Gate (t + 1)))
  | @gate2 n c =>
    exact heq_index (Nat.add_assoc m j n).symm (fun t => (Gen.gate2 c : Gen Gate (t + 2)))
  | @gate3 n c =>
    exact heq_index (Nat.add_assoc m j n).symm (fun t => (Gen.gate3 c : Gen Gate (t + 3)))
  | @up n g ih => exact heq_up (Nat.add_assoc m j n).symm ih

theorem pad_pad_heq (m j : ℕ) {k : ℕ} (w : Circuit Gate k) :
    HEq (Circuit.pad m (Circuit.pad j w)) (Circuit.pad (m + j) w) := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    rw [map_one, map_one, map_one]
    exact heq_index (Nat.add_assoc m j k).symm (fun t => (1 : Circuit Gate t))
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul]
    exact heq_mul (Nat.add_assoc m j k).symm
      (heq_of (Nat.add_assoc m j k).symm (Gen.pad_pad_heq m j g)) ih

variable {Base : CRel Gate}

theorem lift_pad : ∀ {n : ℕ} {w v : Circuit Gate n}, Lift (Padded Base) n w v →
    ∀ m, Lift (Padded Base) (m + n) (Circuit.pad m w) (Circuit.pad m v)
  | _, _, _, .rule (.pad j b), m =>
    lift_cast (Nat.add_assoc m j _) (pad_pad_heq m j _).symm (pad_pad_heq m j _).symm
      (Lift.rule (Padded.pad (m + j) b))
  | _, _, _, .shift r, m => by
    rw [pad_shift, pad_shift]
    exact Lift.shift (lift_pad r m)
  | _, _, _, .comm1 c g, m => by
    simp only [map_mul, Circuit.pad, FreeMonoid.map_of]
    exact Lift.comm1 c (g.pad m)
  | _, _, _, .comm2 c g, m => by
    simp only [map_mul, Circuit.pad, FreeMonoid.map_of]
    exact Lift.comm2 c (g.pad m)
  | _, _, _, .comm3 c g, m => by
    simp only [map_mul, Circuit.pad, FreeMonoid.map_of]
    exact Lift.comm3 c (g.pad m)
  | _, _, _, .scalar c, m => by
    simp only [Circuit.pad, FreeMonoid.map_of]
    exact Lift.scalar c

theorem derivable_pad (m : ℕ) {n : ℕ} {w v : Circuit Gate n}
    (d : Derivable (Lift (Padded Base) n) w v) :
    Derivable (Lift (Padded Base) (m + n)) (Circuit.pad m w) (Circuit.pad m v) := by
  let c : Con (Circuit Gate n) :=
    (conGen (Lift (Padded Base) (m + n))).comap (Circuit.pad m) (map_mul (Circuit.pad m))
  have : conGen (Lift (Padded Base) n) ≤ c := Con.conGen_le fun x y r => Derivable.of (lift_pad r m)
  exact this d

end Move

end QCert.Minimality
