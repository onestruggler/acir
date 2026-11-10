/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A proof engine for equations between concrete circuits over the gates X, CX, CCX and Ex

Translation of `Engine.agda` (after `Examples.Independence.Engine`), for
this folder's gates and any relation on them lifted to a PROP.  An equation
is a pair of letter lists with a derivation (`Eqn`, the Agda's record with
constructor `eqn` and fields `lhs⁼`, `rhs⁼`, `prf`).  A derivation of a new
equation is a list of steps run on the letters: `Step.rw i e` rewrites the
occurrence of the left side of `e` at position `i` to its right side.  `run`
executes the steps, and `run_sound` turns a successful run into a
derivation.  Equations are transformed by `symE` and `liftE` (one wire up;
the Agda's `sym⁼`, `lift⁼`), built from equations between words by `eqnW`
(the Agda's `eqnʷ`), and read as equations between words by `Eqn.to`
(`eqn→`).  Lists are in the order of words: diagram order, the head first.

There is no step for the commutation of letters on disjoint wires: the
derivations run here come from a Knuth–Bendix completion in which a
commutation is a rule like any other.

**Deviations from the Agda.**

* *Letters are names.*  The Agda's letter lists are lists of generators
  (`List (Gen n)`), written with letters defined beside them (`x0`, `cx1`, …)
  or as strings (`Letters`).  Here a letter list is a list of names in an
  alphabet `α` (an enumeration, with `Alpha α n`: each name has a number,
  `Alpha.code`, and denotes a generator, `Alpha.gen`), and the word of a
  list is `word l` (the Agda's `⟪_⟫`, through `gen`).  The kernel then
  compares two letters by comparing two numerals, where comparing two
  generators costs it a traversal of an indexed family for each.  The
  alphabets on two, three and four wires (`L2`, `L3`, `L4`) are defined
  here, with the names the Agda gives the letters where it uses them.
* The Agda closes `derive l r steps refl`, the type checker running the
  steps.  Here the run is one Boolean (`check`) with a soundness lemma, and a
  derivation is `derive l r steps (by decide +kernel)`.
* `run` rewrites at a position by walking to it with an accumulator
  (`rwAt`), where the Agda's uses `take` and `drop`: the kernel evaluates
  lazily, and this keeps the word it carries evaluated.
* `liftE` takes the map of names that shifting is (`u`, with
  `gen (u a) = (gen a).up`), and `padE` (not in the Agda's engine; its
  `FourWire.bot`) the one that widening is.
* Words are `FreeMonoid`, which is `List`, so the Agda's side conditions on
  `to-list`s are equations between words, proved by `rfl`, or decided by the
  kernel for a long word (`Eqn.toB`, with `eqW`).
-/
import QCert.Alt16RevCir.Syntactics
import Mathlib.Tactic.DeriveFintype

namespace QCert.Alt16RevCir.Engine

open QCert QCert.Circuit CircuitProp

/-! ## Equality of letters -/

private def eqg : {k : ℕ} → Gate k → Gate k → Bool
  | _, .X_gate, .X_gate => true
  | _, .CX_gate, .CX_gate => true
  | _, .CX_gate, .Ex_gate => false
  | _, .Ex_gate, .CX_gate => false
  | _, .Ex_gate, .Ex_gate => true
  | _, .CCX_gate, .CCX_gate => true

private theorem eqg_sound : ∀ {k : ℕ} (a b : Gate k), eqg a b = true → a = b
  | _, .X_gate, .X_gate, _ => rfl
  | _, .CX_gate, .CX_gate, _ => rfl
  | _, .Ex_gate, .Ex_gate, _ => rfl
  | _, .CCX_gate, .CCX_gate, _ => rfl
  | _, .CX_gate, .Ex_gate, h => by simp [eqg] at h
  | _, .Ex_gate, .CX_gate, h => by simp [eqg] at h

/-- Generators compared constructor by constructor. -/
def eqG : {n : ℕ} → Gn n → Gn n → Bool
  | _, .gate0 a, .gate0 b => eqg a b
  | _, .gate0 _, .gate1 _ => false
  | _, .gate0 _, .gate2 _ => false
  | _, .gate0 _, .gate3 _ => false
  | _, .gate0 _, .up _ => false
  | _, .gate1 _, .gate0 _ => false
  | _, .gate1 a, .gate1 b => eqg a b
  | _, .gate1 _, .gate2 _ => false
  | _, .gate1 _, .gate3 _ => false
  | _, .gate1 _, .up _ => false
  | _, .gate2 _, .gate0 _ => false
  | _, .gate2 _, .gate1 _ => false
  | _, .gate2 a, .gate2 b => eqg a b
  | _, .gate2 _, .gate3 _ => false
  | _, .gate2 _, .up _ => false
  | _, .gate3 _, .gate0 _ => false
  | _, .gate3 _, .gate1 _ => false
  | _, .gate3 _, .gate2 _ => false
  | _, .gate3 a, .gate3 b => eqg a b
  | _, .gate3 _, .up _ => false
  | _, .up _, .gate0 _ => false
  | _, .up _, .gate1 _ => false
  | _, .up _, .gate2 _ => false
  | _, .up _, .gate3 _ => false
  | _, .up x, .up y => eqG x y

theorem eqG_sound : ∀ {n : ℕ} (x y : Gn n), eqG x y = true → x = y
  | _, .gate0 a, .gate0 b, h => congrArg Gen.gate0 (eqg_sound a b h)
  | _, .gate1 a, .gate1 b, h => congrArg Gen.gate1 (eqg_sound a b h)
  | _, .gate2 a, .gate2 b, h => congrArg Gen.gate2 (eqg_sound a b h)
  | _, .gate3 a, .gate3 b, h => congrArg Gen.gate3 (eqg_sound a b h)
  | _, .up x, .up y, h => congrArg Gen.up (eqG_sound x y h)
  | _, .gate0 _, .gate1 _, h => by simp [eqG] at h
  | _, .gate0 _, .gate2 _, h => by simp [eqG] at h
  | _, .gate0 _, .gate3 _, h => by simp [eqG] at h
  | _, .gate0 _, .up _, h => by simp [eqG] at h
  | _, .gate1 _, .gate0 _, h => by simp [eqG] at h
  | _, .gate1 _, .gate2 _, h => by simp [eqG] at h
  | _, .gate1 _, .gate3 _, h => by simp [eqG] at h
  | _, .gate1 _, .up _, h => by simp [eqG] at h
  | _, .gate2 _, .gate0 _, h => by simp [eqG] at h
  | _, .gate2 _, .gate1 _, h => by simp [eqG] at h
  | _, .gate2 _, .gate3 _, h => by simp [eqG] at h
  | _, .gate2 _, .up _, h => by simp [eqG] at h
  | _, .gate3 _, .gate0 _, h => by simp [eqG] at h
  | _, .gate3 _, .gate1 _, h => by simp [eqG] at h
  | _, .gate3 _, .gate2 _, h => by simp [eqG] at h
  | _, .gate3 _, .up _, h => by simp [eqG] at h
  | _, .up _, .gate0 _, h => by simp [eqG] at h
  | _, .up _, .gate1 _, h => by simp [eqG] at h
  | _, .up _, .gate2 _, h => by simp [eqG] at h
  | _, .up _, .gate3 _, h => by simp [eqG] at h

/-- Lists of generators compared letter by letter. -/
def eqL {n : ℕ} : List (Gn n) → List (Gn n) → Bool
  | [], [] => true
  | x :: xs, y :: ys => eqG x y && eqL xs ys
  | _, _ => false

theorem eqL_sound {n : ℕ} : ∀ (xs ys : List (Gn n)), eqL xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [eqG_sound x y h.1, eqL_sound xs ys h.2]
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h

/-! ## Alphabets: names for letters -/

/-- An alphabet of names for generators of `n`-wire circuits: each name has
a number, and denotes a generator. -/
class Alpha (α : Type) (n : outParam ℕ) where
  code : α → ℕ
  code_inj : ∀ a b : α, code a = code b → a = b
  gen : α → Gn n

section Words

variable {α : Type} {n : ℕ} [Alpha α n]

/-- Two names compared by their numbers. -/
def eqA (a b : α) : Bool := Nat.beq (Alpha.code a) (Alpha.code b)

theorem eqA_sound {a b : α} (h : eqA a b = true) : a = b :=
  Alpha.code_inj a b (Nat.eq_of_beq_eq_true h)

/-- Lists of names compared name by name. -/
def eqLA : List α → List α → Bool
  | [], [] => true
  | a :: l, b :: r => eqA a b && eqLA l r
  | _, _ => false

theorem eqLA_sound : ∀ (l r : List α), eqLA l r = true → l = r
  | [], [], _ => rfl
  | a :: l, b :: r, h => by
    simp only [eqLA, Bool.and_eq_true] at h
    rw [eqA_sound h.1, eqLA_sound l r h.2]
  | [], _ :: _, h => by simp [eqLA] at h
  | _ :: _, [], h => by simp [eqLA] at h

/-! ## Letter lists as circuits -/

/-- The circuit of a letter list (the Agda's `⟪_⟫`). -/
def word (l : List α) : Circ n := FreeMonoid.ofList (l.map Alpha.gen)

theorem word_nil : word ([] : List α) = 1 := rfl

theorem word_cons (a : α) (l : List α) : word (a :: l) = FreeMonoid.of (Alpha.gen a) * word l := rfl

/-- The Agda's `⟪++⟫`. -/
theorem word_append (l l' : List α) : word (l ++ l') = word l * word l' := by
  simp only [word, List.map_append, FreeMonoid.ofList_append]

/-- A circuit and a letter list with the same letters, decided. -/
def eqW (w : Circ n) (l : List α) : Bool := eqL (FreeMonoid.toList w) (l.map Alpha.gen)

theorem eqW_sound {w : Circ n} {l : List α} (h : eqW w l = true) : w = word l :=
  eqL_sound _ _ h

end Words

/-! ## Equations -/

section Kit

variable (SRel : CRel Gate)

/-- An equation between letter lists, with its derivation. -/
structure Eqn (α : Type) {n : ℕ} [Alpha α n] where
  eqn ::
  lhs : List α
  rhs : List α
  prf : Der SRel n (word lhs) (word rhs)

variable {SRel} {α : Type} {n : ℕ} [Alpha α n]

/-- Both sides exchanged (the Agda's `sym⁼`). -/
def symE (e : Eqn SRel α) : Eqn SRel α := ⟨e.rhs, e.lhs, e.prf.symm⟩

/-- An equation between words, read as one between letter lists: the lists
are the words' letters (the Agda's `eqnʷ`). -/
def eqnW {w v : Circ n} (l r : List α) (p : Der SRel n w v) (e₁ : word l = w)
    (e₂ : v = word r) : Eqn SRel α :=
  ⟨l, r, by rw [e₁, ← e₂]; exact p⟩

/-- And back: an equation between any two words with those letters (the
Agda's `eqn→`). -/
theorem Eqn.to (e : Eqn SRel α) {w v : Circ n} (e₁ : w = word e.lhs) (e₂ : word e.rhs = v) :
    Der SRel n w v := by
  rw [e₁, ← e₂]; exact e.prf

/-- The same, the letters compared by the kernel. -/
theorem Eqn.toB (e : Eqn SRel α) {w v : Circ n} (h₁ : eqW w e.lhs = true)
    (h₂ : eqW v e.rhs = true) : Der SRel n w v :=
  e.to (eqW_sound h₁) (eqW_sound h₂).symm

/-- The word of a list of names mapped to names of shifted letters. -/
theorem word_map_up {β : Type} [Alpha β (n + 1)] (u : α → β)
    (hu : ∀ a, Alpha.gen (u a) = (Alpha.gen a).up) (l : List α) :
    word (l.map u) = shift (word l) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, word_cons, word_cons, ih, hu, map_mul, shift_of]

/-- One wire up (the Agda's `lift⁼`), along the map `u` of names that
shifting is. -/
def liftE {β : Type} [Alpha β (n + 1)] (u : α → β)
    (hu : ∀ a, Alpha.gen (u a) = (Alpha.gen a).up) (e : Eqn SRel α) : Eqn SRel β :=
  ⟨e.lhs.map u, e.rhs.map u, by
    rw [word_map_up u hu, word_map_up u hu]; exact lemma_cong_up e.prf⟩

/-- The word of a list of names mapped to names of widened letters. -/
theorem word_map_pad {m : ℕ} {β : Type} [Alpha β (m + n)] (u : α → β)
    (hu : ∀ a, Alpha.gen (u a) = (Alpha.gen a).pad m) (l : List α) :
    word (l.map u) = Circuit.pad m (word l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, word_cons, word_cons, ih, hu, map_mul]; rfl

/-- On the bottom wires of a circuit `m` wires wider (`CircuitProp.pad`),
along the map `u` of names that widening is. -/
def padE {m : ℕ} {β : Type} [Alpha β (m + n)] (u : α → β)
    (hu : ∀ a, Alpha.gen (u a) = (Alpha.gen a).pad m) (hn : n ≤ 4) (e : Eqn SRel α) :
    Eqn SRel β :=
  ⟨e.lhs.map u, e.rhs.map u, by
    rw [word_map_pad u hu, word_map_pad u hu]; exact CircuitProp.pad hn e.prf m⟩

/-! ## Running a derivation -/

/-- A step: `rw i e` rewrites the left side of `e` at position `i` to its
right side. -/
inductive Step (SRel : CRel Gate) (α : Type) {n : ℕ} [Alpha α n] where
  | rw : ℕ → Eqn SRel α → Step SRel α

/-- What is left of `xs` after its prefix `l`. -/
def strip : List α → List α → Option (List α)
  | [], xs => some xs
  | _ :: _, [] => none
  | a :: l, x :: xs => bif eqA a x then strip l xs else none

theorem strip_sound : ∀ (l xs rest : List α), strip l xs = some rest → xs = l ++ rest
  | [], xs, rest, h => by
    simp only [strip, Option.some.injEq] at h
    rw [h]; rfl
  | _ :: _, [], _, h => by simp [strip] at h
  | a :: l, x :: xs, rest, h => by
    simp only [strip] at h
    cases hc : eqA a x
    · simp [hc] at h
    · simp only [hc, cond_true] at h
      rw [eqA_sound hc, strip_sound l xs rest h]; rfl

/-- The occurrence of `l` at position `i` of `acc.reverse ++ xs`, counted
from the start of `xs`, replaced by `r`. -/
def rwAt (l r : List α) : ℕ → List α → List α → Option (List α)
  | 0, acc, xs =>
    match strip l xs with
    | some rest => some (List.reverseAux acc (r ++ rest))
    | none => none
  | _ + 1, _, [] => none
  | i + 1, acc, x :: xs => rwAt l r i (x :: acc) xs

/-- Run the steps. -/
def run : List (Step SRel α) → List α → Option (List α)
  | [], xs => some xs
  | .rw i e :: ss, xs =>
    match rwAt e.lhs e.rhs i [] xs with
    | some ys => run ss ys
    | none => none

/-- The steps turn `l` into `r`. -/
def check (ss : List (Step SRel α)) (l r : List α) : Bool :=
  match run ss l with
  | some y => eqLA y r
  | none => false

theorem rwAt_sound {l r : List α} (p : Der SRel n (word l) (word r)) :
    ∀ (i : ℕ) (acc xs ys : List α), rwAt l r i acc xs = some ys →
      Der SRel n (word (acc.reverse ++ xs)) (word ys)
  | 0, acc, xs, ys, h => by
    simp only [rwAt] at h
    cases hs : strip l xs with
    | none => simp [hs] at h
    | some rest =>
      simp only [hs, Option.some.injEq] at h
      subst h
      rw [strip_sound l xs rest hs, List.reverseAux_eq, word_append, word_append, word_append,
        word_append]
      exact (Derivable.refl _).mul (p.mul (Derivable.refl _))
  | _ + 1, _, [], _, h => by simp [rwAt] at h
  | i + 1, acc, x :: xs, ys, h => by
    simp only [rwAt] at h
    have e := rwAt_sound p i (x :: acc) xs ys h
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using e

theorem run_sound : ∀ (ss : List (Step SRel α)) (xs ys : List α), run ss xs = some ys →
    Der SRel n (word xs) (word ys)
  | [], xs, ys, h => by
    simp only [run, Option.some.injEq] at h
    subst h; exact Derivable.refl _
  | .rw i e :: ss, xs, ys, h => by
    simp only [run] at h
    cases hr : rwAt e.lhs e.rhs i [] xs with
    | none => simp [hr] at h
    | some zs =>
      simp only [hr] at h
      exact (rwAt_sound e.prf i [] xs zs hr).trans (run_sound ss zs ys h)

theorem check_sound {ss : List (Step SRel α)} {l r : List α} (h : check ss l r = true) :
    Der SRel n (word l) (word r) := by
  unfold check at h
  cases hr : run ss l with
  | none => simp [hr] at h
  | some y =>
    simp only [hr] at h
    rw [← eqLA_sound _ _ h]; exact run_sound ss l y hr

/-- A derivation: an equation from the steps that turn `l` into `r`. -/
def derive (l r : List α) (ss : List (Step SRel α)) (h : check ss l r = true) : Eqn SRel α :=
  ⟨l, r, check_sound h⟩

end Kit

/-! ## The alphabets on two, three and four wires

The names of the generators at each width: the letters that the Agda defines
beside its derivations (`x0 x1 cx0 ex0 : Gen 2` in `Width2.Derivations`, eight
in `Width3.Derivations`, twelve in `FourWire`). -/

/-- The four letters on two wires. -/
inductive L2
  | x0 | x1 | cx0 | ex0
  deriving DecidableEq, Fintype

def L2.code : L2 → ℕ
  | .x0 => 0 | .x1 => 1 | .cx0 => 2 | .ex0 => 3

def L2.gen : L2 → Gn 2
  | .x0 => .gate1 .X_gate
  | .x1 => .up (.gate1 .X_gate)
  | .cx0 => .gate2 .CX_gate
  | .ex0 => .gate2 .Ex_gate

instance : Alpha L2 2 := ⟨L2.code, by decide, L2.gen⟩

/-- The eight letters on three wires. -/
inductive L3
  | x0 | x1 | x2 | cx0 | cx1 | ex0 | ex1 | ccx
  deriving DecidableEq, Fintype

def L3.code : L3 → ℕ
  | .x0 => 0 | .x1 => 1 | .x2 => 2 | .cx0 => 3 | .cx1 => 4 | .ex0 => 5 | .ex1 => 6 | .ccx => 7

def L3.gen : L3 → Gn 3
  | .x0 => .gate1 .X_gate
  | .x1 => .up (.gate1 .X_gate)
  | .x2 => .up (.up (.gate1 .X_gate))
  | .cx0 => .gate2 .CX_gate
  | .cx1 => .up (.gate2 .CX_gate)
  | .ex0 => .gate2 .Ex_gate
  | .ex1 => .up (.gate2 .Ex_gate)
  | .ccx => .gate3 .CCX_gate

instance : Alpha L3 3 := ⟨L3.code, by decide, L3.gen⟩

/-- The twelve letters on four wires. -/
inductive L4
  | x0 | x1 | x2 | x3 | cx0 | cx1 | cx2 | ex0 | ex1 | ex2 | ccx0 | ccx1
  deriving DecidableEq, Fintype

def L4.code : L4 → ℕ
  | .x0 => 0 | .x1 => 1 | .x2 => 2 | .x3 => 3 | .cx0 => 4 | .cx1 => 5 | .cx2 => 6
  | .ex0 => 7 | .ex1 => 8 | .ex2 => 9 | .ccx0 => 10 | .ccx1 => 11

def L4.gen : L4 → Gn 4
  | .x0 => .gate1 .X_gate
  | .x1 => .up (.gate1 .X_gate)
  | .x2 => .up (.up (.gate1 .X_gate))
  | .x3 => .up (.up (.up (.gate1 .X_gate)))
  | .cx0 => .gate2 .CX_gate
  | .cx1 => .up (.gate2 .CX_gate)
  | .cx2 => .up (.up (.gate2 .CX_gate))
  | .ex0 => .gate2 .Ex_gate
  | .ex1 => .up (.gate2 .Ex_gate)
  | .ex2 => .up (.up (.gate2 .Ex_gate))
  | .ccx0 => .gate3 .CCX_gate
  | .ccx1 => .up (.gate3 .CCX_gate)

instance : Alpha L4 4 := ⟨L4.code, by decide, L4.gen⟩

end QCert.Alt16RevCir.Engine
