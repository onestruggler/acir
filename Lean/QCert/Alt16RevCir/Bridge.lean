/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The semantics of the two translations between Lafont's cycles on sixteen points and the gates on four wires

Translation of `Bridge.agda`.  A circuit on four wires denotes a function on
the sixteen states (`Semantics`), a word in Lafont's cycles an even
permutation of the sixteen positions (`Lib/Alternating`), and the Gray code
numbers the states by the positions (`Numbering`).  Along that numbering
each translation keeps the meaning of what it translates:

* `f_sem`: the word of a circuit permutes the positions as the circuit maps
  the states;

* `g_sem`: the circuit of a word in the cycles maps the states as the word
  permutes the positions.

Both are proved on the generators by evaluation at the sixteen positions
(`f_sem_gen` for the twelve gates, `g_sem_gen` for the fourteen cycles), and
then by induction on the word.  Everything is stated position by position:
two even permutations are never compared as such.

**Deviations from the Agda.**  The Agda evaluates the permutation of a closed
word in the cycles at a position by `refl`.  Mathlib's permutations are not
meant for the kernel, so a word in the cycles is evaluated on the positions
as numbers: a cycle is the function `cycN d` at its position `d = pos y`,
a word the composite `actN`, and `sem_val` says that this is the value of
its permutation.  The fourteen cycles are not enumerated: a generator `y`
of sixteen points has `pos y ≤ 13` and circuit `Ω (pos y)` (`g_pos`), and
`g_sem_gen` is decided for the fourteen positions at once.
-/
import QCert.Alt16RevCir.Numbering
import QCert.Alt16RevCir.Translation
import QCert.Alt16RevCir.Lib.Alternating.Interpretation

namespace QCert.Alt16RevCir

open QCert QCert.Circuit CircuitProp
open Alternating (Alt)

/-! ## Words in the cycles on the positions as numbers -/

/-- The cycle of the positions `d`, `d + 1`, `d + 2`. -/
def cycN (d x : ℕ) : ℕ :=
  if x = d then d + 1 else if x = d + 1 then d + 2 else if x = d + 2 then d else x

/-- The position of a generator: the number of its shifts. -/
def pos : {n : ℕ} → Alternating.Gn n → ℕ
  | _, .gate0 g => nomatch g
  | _, .gate1 g => nomatch g
  | _, .gate2 g => nomatch g
  | _, .gate3 .ω_gate => 0
  | _, .up y => pos y + 1

/-- The cycles at the positions of a list, in diagram order. -/
def actN : List ℕ → ℕ → ℕ
  | [], x => x
  | d :: l, x => actN l (cycN d x)

private theorem cycN_zero (d : ℕ) : cycN (d + 1) 0 = 0 := by
  unfold cycN; split_ifs <;> omega

private theorem cycN_succ (d x : ℕ) : cycN (d + 1) (x + 1) = cycN d x + 1 := by
  unfold cycN; split_ifs <;> omega

/-- The permutation of a generator is the cycle at its position. -/
theorem semG_val : ∀ {n : ℕ} (y : Alternating.Gn n) (i : Fin n),
    (Alt.perm (Alternating.semG y) i).val = cycN (pos y) i.val
  | _, .gate0 g, _ => nomatch g
  | _, .gate1 g, _ => nomatch g
  | _, .gate2 g, _ => nomatch g
  | _, .gate3 .ω_gate, i => by
    rw [Alternating.perm_semG_ω]
    exact Alternating.cycle_val i
  | _, .up y, i => by
    rw [Alternating.perm_semG_up]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Alternating.lift₀_zero]
      exact (cycN_zero (pos y)).symm
    · rw [Alternating.lift₀_succ, Fin.val_succ, Fin.val_succ, semG_val y j]
      exact (cycN_succ (pos y) j.val).symm

/-- The permutation of a word in the cycles, on numbers. -/
theorem sem_val {n : ℕ} (u : Alternating.Circ n) (i : Fin n) :
    (Alt.perm (Alternating.sem u) i).val = actN ((FreeMonoid.toList u).map pos) i.val := by
  induction u using FreeMonoid.inductionOn' generalizing i with
  | one => rw [Alternating.sem_one]; rfl
  | mul_of y u ih =>
    rw [Alternating.sem_mul, ih, Alternating.sem_of, semG_val]
    rfl

/-! ## A gate as a word in the cycles -/

private theorem f_sem_ok (x : Gn 4)
    (h : ∀ i : Fin 16,
      actN ((FreeMonoid.toList (f x)).map pos) i.val = (dec (semG x (enc i))).val)
    (i : Fin 16) : Alt.perm (Alternating.sem (f x)) i = dec (semG x (enc i)) :=
  Fin.ext ((sem_val (f x) i).trans (h i))

/-- The word of a gate carries the position of a state to the position of
the state the gate sends it to. -/
theorem f_sem_gen : ∀ (x : Gn 4) (i : Fin 16),
    Alt.perm (Alternating.sem (f x)) i = dec (semG x (enc i))
  | .gate0 g => nomatch g
  | .gate1 .X_gate => f_sem_ok _ (by decide +kernel)
  | .gate2 .CX_gate => f_sem_ok _ (by decide +kernel)
  | .gate2 .Ex_gate => f_sem_ok _ (by decide +kernel)
  | .gate3 .CCX_gate => f_sem_ok _ (by decide +kernel)
  | .up (.gate0 g) => nomatch g
  | .up (.gate1 .X_gate) => f_sem_ok _ (by decide +kernel)
  | .up (.gate2 .CX_gate) => f_sem_ok _ (by decide +kernel)
  | .up (.gate2 .Ex_gate) => f_sem_ok _ (by decide +kernel)
  | .up (.gate3 .CCX_gate) => f_sem_ok _ (by decide +kernel)
  | .up (.up (.gate0 g)) => nomatch g
  | .up (.up (.gate1 .X_gate)) => f_sem_ok _ (by decide +kernel)
  | .up (.up (.gate2 .CX_gate)) => f_sem_ok _ (by decide +kernel)
  | .up (.up (.gate2 .Ex_gate)) => f_sem_ok _ (by decide +kernel)
  | .up (.up (.up (.gate0 g))) => nomatch g
  | .up (.up (.up (.gate1 .X_gate))) => f_sem_ok _ (by decide +kernel)
  | .up (.up (.up (.up (.gate0 g)))) => nomatch g

/-- The same for a circuit, letter by letter: the position reached after `w`
is that of the state reached after `w`. -/
theorem f_sem (w : Circ 4) (i : Fin 16) :
    Alt.perm (Alternating.sem (FreeMonoid.lift f w)) i = dec (sem w (enc i)) := by
  induction w using FreeMonoid.inductionOn' generalizing i with
  | one => exact (Alternating.sem_one i).trans (dec_enc i).symm
  | mul_of x w ih =>
    rw [map_mul, FreeMonoid.lift_eval_of, Alternating.sem_mul, ih, f_sem_gen, enc_dec, sem_mul,
      sem_of]

/-! ## A cycle as a circuit -/

/-- A generator read `c` points up is the circuit of the cycle at its
position. -/
theorem gd_pos : ∀ {n : ℕ} (c : ℕ) (y : Alternating.Gn n), gd c y = Ω (c + pos y)
  | _, _, .gate0 g => nomatch g
  | _, _, .gate1 g => nomatch g
  | _, _, .gate2 g => nomatch g
  | _, _, .gate3 .ω_gate => rfl
  | _, c, .up y =>
    (gd_pos (c + 1) y).trans (congrArg Ω (by show c + 1 + pos y = c + (pos y + 1); omega))

theorem g_pos (y : Alternating.Gn 16) : g y = Ω (pos y) :=
  (gd_pos 0 y).trans (congrArg Ω (Nat.zero_add _))

/-- There are fourteen cycles; a fifteenth would be a generator on two
points. -/
theorem pos_le : ∀ {n : ℕ} (y : Alternating.Gn n), pos y + 3 ≤ n
  | _, .gate0 g => nomatch g
  | _, .gate1 g => nomatch g
  | _, .gate2 g => nomatch g
  | _, .gate3 .ω_gate => Nat.le_add_left _ _
  | _, .up y => Nat.succ_le_succ (pos_le y)

private theorem Ω_sem : ∀ (d : Fin 14) (i : Fin 16),
    (dec (sem (Ω d.val) (enc i))).val = cycN d.val i.val := by
  decide +kernel

/-- The circuit `Ω d` of the cycle `ω` `d` points up sends the state at a
position to the state at the position the cycle sends it to. -/
theorem g_sem_gen (y : Alternating.Gn 16) (i : Fin 16) :
    dec (sem (g y) (enc i)) = Alt.perm (Alternating.sem (FreeMonoid.of y)) i := by
  have h : pos y < 14 := by have := pos_le y; omega
  apply Fin.ext
  rw [g_pos, Alternating.sem_of, semG_val]
  exact Ω_sem ⟨pos y, h⟩ i

/-- The same for a word in the cycles, letter by letter. -/
theorem g_sem (u : Alternating.Circ 16) (i : Fin 16) :
    dec (sem (FreeMonoid.lift g u) (enc i)) = Alt.perm (Alternating.sem u) i := by
  induction u using FreeMonoid.inductionOn' generalizing i with
  | one => exact (dec_enc i).trans (Alternating.sem_one i).symm
  | mul_of y u ih =>
    rw [map_mul, FreeMonoid.lift_eval_of, sem_mul, Alternating.sem_mul, ← g_sem_gen, ← ih,
      enc_dec]

end QCert.Alt16RevCir
