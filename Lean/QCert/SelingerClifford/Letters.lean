/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits as words of letters

A letter is a gate at an absolute position: `H i`, `S i` on wire `i`,
`CZ i` on wires `i, i+1`, and the scalar `om`.  A word of letters is read
in **time order** (`wc n [a, b]` applies `a` first), as Selinger's
supplement writes circuits.  `Holds k l r` says that `l = r` is derivable
on every number `n ≥ k` of wires.  Letters on disjoint wires commute
(`Holds.comm`), equations move up a wire (`Holds.up`) and are a congruence
(`Holds.congr`), and every relation of Figure 8 is an instance
(`Holds.of_rel`).
-/
import QCert.SelingerClifford.Derivation

namespace QCert.SelingerClifford

open Circuit

/-- A gate at an absolute position. -/
inductive Lt
  | om
  | H (i : ℕ)
  | S (i : ℕ)
  | CZ (i : ℕ)
  deriving DecidableEq, Repr

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

namespace Lt

/-- The circuit of a letter on `n` wires. -/
def circ (n : ℕ) : Lt → Circ n
  | .om => g0 Gate.ω
  | .H i => onW1 Gate.H n i
  | .S i => onW1 Gate.S n i
  | .CZ i => onW2 Gate.CZ n i

/-- The letter one wire up. -/
def up : Lt → Lt
  | .om => .om
  | .H i => .H (i + 1)
  | .S i => .S (i + 1)
  | .CZ i => .CZ (i + 1)

/-- One more than the highest wire of a letter (`0` for the scalar). -/
def hi : Lt → ℕ
  | .om => 0
  | .H i => i + 1
  | .S i => i + 1
  | .CZ i => i + 2

/-- The lowest wire of a letter. -/
def lo : Lt → ℕ
  | .om => 0
  | .H i => i
  | .S i => i
  | .CZ i => i

/-- Two letters act on disjoint wires (a scalar is disjoint from all). -/
def disj (a b : Lt) : Bool :=
  a == .om || b == .om || decide (a.hi ≤ b.lo) || decide (b.hi ≤ a.lo)

end Lt

/-- A word of letters on `n` wires, in time order. -/
def wc (n : ℕ) : List Lt → Circ n
  | [] => 1
  | a :: l => wc n l * Lt.circ n a

theorem wc_append (n : ℕ) (l l' : List Lt) : wc n (l ++ l') = wc n l' * wc n l := by
  induction l with
  | nil => simp [wc]
  | cons a l ih => simp [wc, ih, mul_assoc]

/-- `l = r` is derivable on every number `n ≥ k` of wires. -/
def Holds (k : ℕ) (l r : List Lt) : Prop := ∀ n, k ≤ n → Eqv n (wc n l) (wc n r)

namespace Holds

variable {k k' : ℕ} {l r u : List Lt}

theorem refl (k : ℕ) (l : List Lt) : Holds k l l := fun _ _ => Eqv.refl _
theorem symm (h : Holds k l r) : Holds k r l := fun n hn => (h n hn).symm
theorem trans (h : Holds k l r) (h' : Holds k r u) : Holds k l u :=
  fun n hn => (h n hn).trans (h' n hn)
theorem mono (h : Holds k l r) (hk : k ≤ k') : Holds k' l r :=
  fun n hn => h n (hk.trans hn)

/-- Equations are a congruence. -/
theorem congr (p q : List Lt) (h : Holds k l r) : Holds k (p ++ l ++ q) (p ++ r ++ q) := by
  intro n hn
  rw [wc_append, wc_append, wc_append, wc_append]
  exact Eqv.mul_left _ (Eqv.mul_right _ (h n hn))

end Holds

/-! ### Letters on disjoint wires commute -/

section Comm

variable {n : ℕ}

/-- The scalar is the same one wire up. -/
theorem om_shift : Eqv (n + 1) (Circuit.shift (g0 Gate.ω : Circ n)) (g0 Gate.ω) :=
  Derivable.of (Lift.scalar Gate.ω)

/-- A one-wire gate commutes with the scalar. -/
theorem onW1_comm_om (g : Gate 1) : ∀ (n i : ℕ),
    Eqv n (onW1 g n i * g0 Gate.ω) (g0 Gate.ω * onW1 g n i)
  | n + 1, 0 => by
    refine ((Eqv.mul_left _ om_shift).symm.trans ?_).trans (Eqv.mul_right _ om_shift)
    exact (Derivable.of (Lift.comm1 g (Gen.gate0 Gate.ω))).symm
  | n + 1, i + 1 => by
    have ih := Eqv.shift (onW1_comm_om g n i)
    simp only [map_mul] at ih
    exact ((Eqv.mul_left _ om_shift).symm.trans ih).trans (Eqv.mul_right _ om_shift)
  | 0, _ => by simp only [onW1, one_mul, mul_one]; exact Eqv.refl _

/-- A two-wire gate commutes with the scalar. -/
theorem onW2_comm_om (g : Gate 2) : ∀ (n i : ℕ),
    Eqv n (onW2 g n i * g0 Gate.ω) (g0 Gate.ω * onW2 g n i)
  | n + 2, 0 => by
    have h2 : Eqv (n + 2) (Circuit.shift (Circuit.shift (g0 Gate.ω : Circ n))) (g0 Gate.ω) :=
      (Eqv.shift om_shift).trans om_shift
    refine ((Eqv.mul_left _ h2).symm.trans ?_).trans (Eqv.mul_right _ h2)
    exact (Derivable.of (Lift.comm2 g (Gen.gate0 Gate.ω))).symm
  | n + 1, i + 1 => by
    have ih := Eqv.shift (onW2_comm_om g n i)
    simp only [map_mul] at ih
    exact ((Eqv.mul_left _ om_shift).symm.trans ih).trans (Eqv.mul_right _ om_shift)
  | 0, _ => by simp only [onW2, one_mul, mul_one]; exact Eqv.refl _
  | 1, 0 => by simp only [onW2, one_mul, mul_one]; exact Eqv.refl _

/-- A letter commutes with the scalar. -/
theorem circ_comm_om (n : ℕ) : ∀ a : Lt,
    Eqv n (Lt.circ n a * g0 Gate.ω) (g0 Gate.ω * Lt.circ n a)
  | .om => Eqv.refl _
  | .H i => onW1_comm_om _ n i
  | .S i => onW1_comm_om _ n i
  | .CZ i => onW2_comm_om _ n i

/-- A one-wire gate on wire `0` commutes with any circuit one wire up. -/
theorem comm1_shift (g : Gate 1) (c : Circ n) :
    Eqv (n + 1) (Circuit.shift c * g1 g) (g1 g * Circuit.shift c) := by
  induction c using FreeMonoid.inductionOn' with
  | one => simp only [map_one, one_mul, mul_one]; exact Eqv.refl _
  | mul_of x c ih =>
    rw [map_mul, Circuit.shift_of, mul_assoc]
    refine (Eqv.mul_left _ ih).trans ?_
    rw [← mul_assoc, ← mul_assoc]
    exact Eqv.mul_right _ (Derivable.of (Lift.comm1 g x))

/-- A two-wire gate on wires `0, 1` commutes with any circuit two wires
up. -/
theorem comm2_shift2 (g : Gate 2) (c : Circ n) :
    Eqv (n + 2) (Circuit.shift (Circuit.shift c) * g2 g)
      (g2 g * Circuit.shift (Circuit.shift c)) := by
  induction c using FreeMonoid.inductionOn' with
  | one => simp only [map_one, one_mul, mul_one]; exact Eqv.refl _
  | mul_of x c ih =>
    rw [map_mul, map_mul, Circuit.shift_of, Circuit.shift_of, mul_assoc]
    refine (Eqv.mul_left _ ih).trans ?_
    rw [← mul_assoc, ← mul_assoc]
    exact Eqv.mul_right _ (Derivable.of (Lift.comm2 g x))

/-- Commutation one wire up. -/
theorem comm_shift {c d : Circ n} (h : Eqv n (c * d) (d * c)) :
    Eqv (n + 1) (Circuit.shift c * Circuit.shift d) (Circuit.shift d * Circuit.shift c) := by
  have := Eqv.shift h
  simpa only [map_mul] using this

theorem onW1_onW1 (g h : Gate 1) : ∀ (n i j : ℕ), i ≠ j →
    Eqv n (onW1 g n i * onW1 h n j) (onW1 h n j * onW1 g n i)
  | 0, _, _, _ => by simp only [onW1, one_mul]; exact Eqv.refl _
  | n + 1, 0, 0, hij => absurd rfl hij
  | n + 1, 0, j + 1, _ => (comm1_shift g (onW1 h n j)).symm
  | n + 1, i + 1, 0, _ => comm1_shift h (onW1 g n i)
  | n + 1, i + 1, j + 1, hij => comm_shift (onW1_onW1 g h n i j (by omega))

theorem onW1_onW2 (g : Gate 1) (h : Gate 2) : ∀ (n i j : ℕ), (i + 1 ≤ j ∨ j + 2 ≤ i) →
    Eqv n (onW1 g n i * onW2 h n j) (onW2 h n j * onW1 g n i)
  | 0, _, _, _ => by simp only [onW1, onW2, one_mul]; exact Eqv.refl _
  | n + 1, 0, 0, hij => by omega
  | n + 1, 0, j + 1, _ => (comm1_shift g (onW2 h n j)).symm
  | n + 1, 1, 0, hij => by omega
  | n + 1, i + 2, 0, _ => by
    cases n with
    | zero => simp only [onW2, one_mul, mul_one]; exact Eqv.refl _
    | succ n => exact comm2_shift2 h (onW1 g n i)
  | n + 1, i + 1, j + 1, hij => comm_shift (onW1_onW2 g h n i j (by omega))

theorem onW2_onW2 (g h : Gate 2) : ∀ (n i j : ℕ), (i + 2 ≤ j ∨ j + 2 ≤ i) →
    Eqv n (onW2 g n i * onW2 h n j) (onW2 h n j * onW2 g n i)
  | 0, _, _, _ => by simp only [onW2, one_mul]; exact Eqv.refl _
  | n + 1, 0, 0, hij => by omega
  | n + 1, 0, 1, hij => by omega
  | n + 1, 1, 0, hij => by omega
  | n + 1, 0, j + 2, _ => by
    cases n with
    | zero => simp only [onW2, one_mul, mul_one]; exact Eqv.refl _
    | succ n => exact (comm2_shift2 g (onW2 h n j)).symm
  | n + 1, i + 2, 0, _ => by
    cases n with
    | zero => simp only [onW2, one_mul, mul_one]; exact Eqv.refl _
    | succ n => exact comm2_shift2 h (onW2 g n i)
  | n + 1, i + 1, j + 1, hij => comm_shift (onW2_onW2 g h n i j (by omega))

/-- Letters on disjoint wires commute. -/
theorem circ_comm (n : ℕ) (a b : Lt) (h : a.disj b = true) :
    Eqv n (Lt.circ n a * Lt.circ n b) (Lt.circ n b * Lt.circ n a) := by
  rcases a with _ | i | i | i <;> rcases b with _ | j | j | j <;>
    simp only [Lt.disj, Lt.hi, Lt.lo, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
      reduceCtorEq, false_or, or_false] at h
  all_goals first
    | exact Eqv.refl _
    | exact circ_comm_om n _
    | exact (circ_comm_om n _).symm
    | exact onW1_onW1 _ _ n _ _ (by omega)
    | exact onW1_onW2 _ _ n _ _ (by omega)
    | exact (onW1_onW2 _ _ n _ _ (by omega)).symm
    | exact onW2_onW2 _ _ n _ _ (by omega)

end Comm

namespace Holds

/-- Letters on disjoint wires commute. -/
theorem comm {a b : Lt} (h : a.disj b = true) : Holds 0 [a, b] [b, a] :=
  fun n _ => by simpa [wc] using (circ_comm n a b h).symm

end Holds


/-! ### Moving equations up a wire, and the relations as equations -/

section Up

theorem wc_up (n : ℕ) : ∀ l : List Lt,
    Eqv (n + 1) (wc (n + 1) (l.map Lt.up)) (Circuit.shift (wc n l))
  | [] => by simp [wc]; exact Eqv.refl _
  | a :: l => by
    simp only [List.map_cons, wc, map_mul]
    refine Eqv.mul (wc_up n l) ?_
    rcases a with _ | i | i | i
    · exact om_shift.symm
    all_goals exact Eqv.refl _

/-- An equation moved up one wire. -/
theorem Holds.up {k : ℕ} {l r : List Lt} (h : Holds k l r) :
    Holds (k + 1) (l.map Lt.up) (r.map Lt.up) := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (wc_up n l).trans ((Eqv.shift (h n (by omega))).trans (wc_up n r).symm)

theorem pad_shift (m : ℕ) {k : ℕ} (c : Circ k) :
    Circuit.pad m (Circuit.shift c) = Circuit.shift (Circuit.pad m c) := by
  induction c using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x c ih => simp only [map_mul, ih]; rfl

theorem pad_onW1 (m : ℕ) (g : Gate 1) : ∀ (k i : ℕ), i + 1 ≤ k →
    Circuit.pad m (onW1 g k i) = onW1 g (m + k) i
  | 0, _, h => by omega
  | k + 1, 0, _ => rfl
  | k + 1, i + 1, h => by
    show Circuit.pad m (Circuit.shift (onW1 g k i)) = Circuit.shift (onW1 g (m + k) i)
    rw [pad_shift, pad_onW1 m g k i (by omega)]

theorem pad_onW2 (m : ℕ) (g : Gate 2) : ∀ (k i : ℕ), i + 2 ≤ k →
    Circuit.pad m (onW2 g k i) = onW2 g (m + k) i
  | 0, _, h => by omega
  | 1, _, h => by omega
  | k + 2, 0, _ => rfl
  | k + 1, i + 1, h => by
    show Circuit.pad m (Circuit.shift (onW2 g k i)) = Circuit.shift (onW2 g (m + k) i)
    rw [pad_shift, pad_onW2 m g k i (by omega)]

theorem pad_circ (m : ℕ) {k : ℕ} : ∀ (a : Lt), a.hi ≤ k →
    Circuit.pad m (Lt.circ k a) = Lt.circ (m + k) a
  | .om, _ => rfl
  | .H i, h => pad_onW1 m _ k i h
  | .S i, h => pad_onW1 m _ k i h
  | .CZ i, h => pad_onW2 m _ k i h

theorem pad_wc (m : ℕ) {k : ℕ} : ∀ (l : List Lt), (∀ a ∈ l, a.hi ≤ k) →
    Circuit.pad m (wc k l) = wc (m + k) l
  | [], _ => by simp [wc]
  | a :: l, h => by
    simp only [wc, map_mul]
    rw [pad_wc m l (fun b hb => h b (by simp [hb])), pad_circ m a (h a (by simp))]

/-- A relation of Figure 8, written as a word of letters, holds on every
number of wires at least its own. -/
theorem Holds.of_rel {k : ℕ} {w v : Circ k} (rel : Rel k w v) (l r : List Lt)
    (hl : wc k l = w) (hr : wc k r = v)
    (vl : (l.all fun a => decide (a.hi ≤ k)) = true)
    (vr : (r.all fun a => decide (a.hi ≤ k)) = true) : Holds k l r := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
  have := Eqv.rule m rel
  simp only [List.all_eq_true, decide_eq_true_eq] at vl vr
  rwa [← hl, ← hr, pad_wc m l vl, pad_wc m r vr] at this

end Up

end QCert.SelingerClifford
