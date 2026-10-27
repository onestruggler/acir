/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A rewriting engine for two-wire derivations

Two-wire circuits are written as lists of letters (`Lt`): `H`, `Z` on
wire 0 (`h`, `z`) and on wire 1 (`H`, `Z`), `CZ` (`C`), `CH` (`K`) and the
swap of Equation (8) (`S`), in operator order.  An equation between two
lists holds when their classes in the quotient monoid `Q2` agree (`E`).

A derivation is a list of steps, each rewriting the current word with one
equation of a table, at a place given by the words `u`, `v` around it, up to
the commutation of single-qubit gates on different wires: the current word
must have the same canonical form (`canon`, which moves wire-1 letters before
wire-0 letters within each run of single-qubit letters) as `u ++ lhs ++ v`.
`check` runs a derivation and is evaluated by `decide`; `check_sound` makes
it an equation.

Tables (`Lib`) grow by equations proved by a run over the table so far, and
by the mirror image (`rev`, every letter being an involution, Lemma B.3)
and the upside-down image (`sig`, conjugation by the swap) of an equation
already in the table.
-/
import QCert.RealCliffordCH.Decode

namespace QCert.RealCliffordCH.Two

open Circuit

/-- The letters of two-wire circuits. -/
inductive Lt | h | z | H | Z | C | K | S
  deriving DecidableEq, Repr

/-- The circuit of a letter. -/
def Lt.circ : Lt → Circ 2
  | .h => RealCliffordCH.h
  | .z => RealCliffordCH.z
  | .H => shift RealCliffordCH.h
  | .Z => shift RealCliffordCH.z
  | .C => cz
  | .K => ch
  | .S => swap

/-- The circuit of a word of letters, in operator order. -/
def toC (l : List Lt) : Circ 2 := (l.map Lt.circ).prod

theorem toC_nil : toC [] = 1 := rfl

theorem toC_cons (x : Lt) (l : List Lt) : toC (x :: l) = x.circ * toC l := by
  simp [toC]

theorem toC_append (a b : List Lt) : toC (a ++ b) = toC a * toC b := by
  simp [toC, List.prod_append]

/-- Two words are equal in the theory. -/
def E (a b : List Lt) : Prop := cl (toC a) = cl (toC b)

theorem E.refl (a : List Lt) : E a a := rfl
theorem E.symm {a b : List Lt} (h : E a b) : E b a := Eq.symm h
theorem E.trans {a b c : List Lt} (h : E a b) (h' : E b c) : E a c := Eq.trans h h'

theorem E.append {a b c d : List Lt} (h : E a b) (h' : E c d) : E (a ++ c) (b ++ d) := by
  unfold E at *; rw [toC_append, toC_append, map_mul, map_mul, h, h']

theorem E.derivable {a b : List Lt} (h : E a b) : Derivable (theory 2) (toC a) (toC b) :=
  cl_eq.1 h

/-! ## Canonical forms up to disjoint commutations -/

def isW0 : Lt → Bool
  | .h | .z => true
  | _ => false

def isW1 : Lt → Bool
  | .H | .Z => true
  | _ => false

/-- Insert a letter in front of a canonical word. -/
def push (x : Lt) : List Lt → List Lt
  | [] => [x]
  | y :: ys => if isW0 x && isW1 y then y :: push x ys else x :: y :: ys

/-- The canonical form: in each run of single-qubit letters, the letters of
wire 1 first, then those of wire 0, each in their order. -/
def canon : List Lt → List Lt
  | [] => []
  | x :: xs => push x (canon xs)

theorem comm_letters {x y : Lt} (hx : isW0 x = true) (hy : isW1 y = true) :
    cl x.circ * cl y.circ = cl y.circ * cl x.circ := by
  cases x <;> cases y <;> simp [isW0, isW1] at hx hy
  · exact comm01 .H .H
  · exact comm01 .H .Z
  · exact comm01 .Z .H
  · exact comm01 .Z .Z

theorem push_E (x : Lt) (l : List Lt) : E (x :: l) (push x l) := by
  induction l with
  | nil => exact E.refl _
  | cons y ys ih =>
    unfold push
    split_ifs with hxy
    · rw [Bool.and_eq_true] at hxy
      have h1 : E (x :: y :: ys) (y :: x :: ys) := by
        unfold E; simp only [toC_cons, map_mul, ← mul_assoc, comm_letters hxy.1 hxy.2]
      refine h1.trans ?_
      unfold E at ih ⊢; rw [toC_cons, map_mul, ih, toC_cons, map_mul]
    · exact E.refl _

theorem canon_E (l : List Lt) : E l (canon l) := by
  induction l with
  | nil => exact E.refl _
  | cons x xs ih =>
    refine E.trans ?_ (push_E x (canon xs))
    unfold E at ih ⊢; rw [toC_cons, toC_cons, map_mul, map_mul, ih]

theorem E_of_canon {a b : List Lt} (h : canon a = canon b) : E a b :=
  (canon_E a).trans (h ▸ (canon_E b).symm)

/-! ## Runs -/

/-- A step: `cur ≈ u ++ lhs ++ v` (up to `canon`) becomes `u ++ rhs ++ v`,
with equation number `k` of the table, reversed when `dir`. -/
structure Step where
  u : List Lt
  v : List Lt
  k : ℕ
  dir : Bool

abbrev Tbl := List (List Lt × List Lt)

/-- The two sides of an equation, in the direction of the step. -/
def orient (dir : Bool) (e : List Lt × List Lt) : List Lt × List Lt :=
  if dir then (e.2, e.1) else e

def applyStep (T : Tbl) (cur : List Lt) (s : Step) : Option (List Lt) :=
  match T[s.k]? with
  | none => none
  | some e =>
    if canon (s.u ++ (orient s.dir e).1 ++ s.v) = canon cur
    then some (s.u ++ (orient s.dir e).2 ++ s.v) else none

def runSteps (T : Tbl) : List Lt → List Step → Option (List Lt)
  | cur, [] => some cur
  | cur, s :: ss => match applyStep T cur s with
    | none => none
    | some nxt => runSteps T nxt ss

/-- Run a derivation from `w` and compare with `v`. -/
def check (T : Tbl) (w v : List Lt) (steps : List Step) : Bool :=
  match runSteps T w steps with
  | none => false
  | some u => canon u == canon v

/-- Every equation of the table holds. -/
def AllE : Tbl → Prop
  | [] => True
  | e :: t => E e.1 e.2 ∧ AllE t

theorem AllE.get {T : Tbl} (h : AllE T) {k : ℕ} {e : List Lt × List Lt} (he : T[k]? = some e) :
    E e.1 e.2 := by
  induction T generalizing k with
  | nil => simp at he
  | cons x t ih =>
    cases k with
    | zero => simp at he; subst he; exact h.1
    | succ k => simp at he; exact ih h.2 he

theorem AllE.append {T : Tbl} (h : AllE T) {e : List Lt × List Lt} (he : E e.1 e.2) :
    AllE (T ++ [e]) := by
  induction T with
  | nil => exact ⟨he, trivial⟩
  | cons x t ih => exact ⟨h.1, ih h.2⟩

theorem orient_E {e : List Lt × List Lt} (h : E e.1 e.2) (dir : Bool) :
    E (orient dir e).1 (orient dir e).2 := by
  cases dir
  · exact h
  · exact h.symm

theorem applyStep_E {T : Tbl} (hT : AllE T) {cur nxt : List Lt} {s : Step}
    (h : applyStep T cur s = some nxt) : E cur nxt := by
  unfold applyStep at h
  cases hk : T[s.k]? with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some e =>
    rw [hk] at h
    simp only at h
    split_ifs at h with hc
    cases h
    refine (E_of_canon hc.symm).trans ?_
    exact ((E.refl s.u).append (orient_E (hT.get hk) s.dir)).append (E.refl s.v)

theorem runSteps_E {T : Tbl} (hT : AllE T) :
    ∀ {cur u : List Lt} {ss : List Step}, runSteps T cur ss = some u → E cur u := by
  intro cur u ss h
  induction ss generalizing cur with
  | nil => simp [runSteps] at h; subst h; exact E.refl _
  | cons s ss ih =>
    unfold runSteps at h
    split at h
    · exact absurd h (by simp)
    · rename_i nxt hn
      exact (applyStep_E hT hn).trans (ih h)

theorem check_sound {T : Tbl} (hT : AllE T) {w v : List Lt} {ss : List Step}
    (h : check T w v ss = true) : E w v := by
  unfold check at h
  split at h
  · exact absurd h (by simp)
  · rename_i u hu
    exact (runSteps_E hT hu).trans (E_of_canon (by simpa using h))

/-! ## Mirror images and swap conjugates -/

/-- Each letter is an involution. -/
theorem letter_invol (x : Lt) : cl x.circ * cl x.circ = 1 := by
  cases x
  · exact h0h0
  · exact z0z0
  · exact h1h1
  · exact z1z1
  · exact cqcq
  · exact kqkq
  · exact sw_sw

theorem rev_inv (a : List Lt) : cl (toC a) * cl (toC a.reverse) = 1 := by
  induction a with
  | nil => simp [toC_nil]
  | cons x xs ih =>
    rw [List.reverse_cons, toC_append, toC_cons, map_mul, map_mul, toC_cons, toC_nil, mul_one,
      mul_assoc, ← mul_assoc (cl (toC xs)), ih, one_mul, letter_invol]

theorem rev_inv' (a : List Lt) : cl (toC a.reverse) * cl (toC a) = 1 := by
  have := rev_inv a.reverse; rwa [List.reverse_reverse] at this

/-- Lemma B.3: the mirror image of an equation. -/
theorem E.rev {a b : List Lt} (h : E a b) : E a.reverse b.reverse := by
  unfold E at *
  calc cl (toC a.reverse) = cl (toC a.reverse) * (cl (toC b) * cl (toC b.reverse)) := by
        rw [rev_inv, mul_one]
    _ = (cl (toC a.reverse) * cl (toC a)) * cl (toC b.reverse) := by rw [h, mul_assoc]
    _ = cl (toC b.reverse) := by rw [rev_inv', one_mul]

/-- The upside-down image of a letter: conjugation by the swap. -/
def sigL : Lt → List Lt
  | .h => [.H]
  | .z => [.Z]
  | .H => [.h]
  | .Z => [.z]
  | .C => [.C]
  | .K => [.S, .K, .S]
  | .S => [.S]

def sig (a : List Lt) : List Lt := a.flatMap sigL

theorem sigL_conj (x : Lt) : cl (toC (sigL x)) = sw * cl x.circ * sw := by
  cases x <;> simp only [sigL, Lt.circ, toC_cons, toC_nil, mul_one, map_mul]
  · exact (sw_conj (sw_conj' sw_h1)).symm
  · exact (sw_conj (sw_conj' sw_z1)).symm
  · exact (sw_conj sw_h1).symm
  · exact (sw_conj sw_z1).symm
  · exact (sw_conj sw_cq).symm
  · simp only [mul_assoc]
  · show sw = sw * sw * sw
    rw [sw_sw, one_mul]

theorem sig_conj (a : List Lt) : cl (toC (sig a)) = sw * cl (toC a) * sw := by
  induction a with
  | nil => simp [sig, toC_nil, sw_sw]
  | cons x xs ih =>
    rw [show sig (x :: xs) = sigL x ++ sig xs from List.flatMap_cons .., toC_append, map_mul,
      sigL_conj, ih, toC_cons, map_mul]
    calc sw * cl x.circ * sw * (sw * cl (toC xs) * sw)
        = sw * cl x.circ * (sw * sw) * cl (toC xs) * sw := by simp only [mul_assoc]
      _ = sw * (cl x.circ * cl (toC xs)) * sw := by rw [sw_sw, mul_one]; simp only [mul_assoc]

/-- The upside-down image of an equation. -/
theorem E.sig {a b : List Lt} (h : E a b) : E (sig a) (sig b) := by
  unfold E at *; rw [sig_conj, sig_conj, h]

/-! ## Tables -/

/-- A table of equations that all hold. -/
structure Lib where
  T : Tbl
  ok : AllE T

/-- Add an equation that holds. -/
def Lib.snoc (L : Lib) (e : List Lt × List Lt) (h : E e.1 e.2) : Lib := ⟨L.T ++ [e], L.ok.append h⟩

/-- An equation proved by a run over the table. -/
theorem Lib.run (L : Lib) (w v : List Lt) (ss : List Step) (h : check L.T w v ss = true) :
    E w v := check_sound L.ok h

/-- The mirror image of equation `i` of the table, in canonical form. -/
theorem Lib.byRev (L : Lib) (i : ℕ) (e : List Lt × List Lt)
    (h : (L.T[i]?).map (fun p => (canon p.1.reverse, canon p.2.reverse)) = some e) :
    E e.1 e.2 := by
  cases hi : L.T[i]? with
  | none => rw [hi] at h; simp at h
  | some p =>
    rw [hi] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
    exact (canon_E _).symm.trans ((L.ok.get hi).rev.trans (canon_E _))

/-- The upside-down image of equation `i` of the table, in canonical form. -/
theorem Lib.bySig (L : Lib) (i : ℕ) (e : List Lt × List Lt)
    (h : (L.T[i]?).map (fun p => (canon (sig p.1), canon (sig p.2))) = some e) :
    E e.1 e.2 := by
  cases hi : L.T[i]? with
  | none => rw [hi] at h; simp at h
  | some p =>
    rw [hi] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
    exact (canon_E _).symm.trans ((L.ok.get hi).sig.trans (canon_E _))

/-- The mirror image of the upside-down image of equation `i`. -/
theorem Lib.byRevSig (L : Lib) (i : ℕ) (e : List Lt × List Lt)
    (h : (L.T[i]?).map (fun p => (canon (sig p.1).reverse, canon (sig p.2).reverse)) = some e) :
    E e.1 e.2 := by
  cases hi : L.T[i]? with
  | none => rw [hi] at h; simp at h
  | some p =>
    rw [hi] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
    exact (canon_E _).symm.trans ((L.ok.get hi).sig.rev.trans (canon_E _))

end QCert.RealCliffordCH.Two
