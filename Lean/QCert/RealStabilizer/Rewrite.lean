/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A checker for derivations between words of letters

A derivation is a list of steps, each either a rewrite with a known
equation (`Step.rw e pos s rev`: the equation `e` of a database, moved up
`s` wires, applied left to right or right to left at position `pos`) or a
move of one letter past letters on disjoint wires (`Step.mv i j`).  `run`
executes the steps; `run_sound` says that a successful run is a derivation,
given that every equation of the database holds.  The check is a Boolean
computation, so `decide +kernel` verifies long derivations.
-/
import QCert.RealStabilizer.Letters

namespace QCert.RealStabilizer

/-- An equation `l = r` that holds on `k` or more wires. -/
structure Eqn where
  k : ℕ
  l : List Lt
  r : List Lt
  deriving DecidableEq

/-- A step of a derivation. -/
inductive Step
  /-- Rewrite with equation `e` of the database, moved up `s` wires, at
  position `pos`, left to right (`rev = false`) or right to left. -/
  | rw (e pos s : ℕ) (rev : Bool)
  /-- Move the letter at position `i` to position `j`, past letters on
  disjoint wires. -/
  | mv (i j : ℕ)
  deriving DecidableEq

/-- A list of letters moved up `s` wires. -/
def upN : ℕ → List Lt → List Lt
  | 0, l => l
  | s + 1, l => (upN s l).map Lt.up

/-- Replace the segment `l` at position `pos` of `w` by `r`. -/
def replaceAt (l r w : List Lt) (pos : ℕ) : Option (List Lt) :=
  if (w.drop pos).take l.length = l ∧ pos + l.length ≤ w.length then
    some (w.take pos ++ r ++ w.drop (pos + l.length))
  else none

/-- All letters of `u` are on wires disjoint from `a`. -/
def allDisj (a : Lt) (u : List Lt) : Bool := u.all fun b => a.disj b

/-- Move the letter at position `i` to position `j`. -/
def moveAt (w : List Lt) (i j : ℕ) : Option (List Lt) :=
  match w[i]? with
  | none => none
  | some a =>
    if i < j then
      if allDisj a ((w.drop (i + 1)).take (j - i)) && decide (j < w.length) then
        some (w.take i ++ (w.drop (i + 1)).take (j - i) ++ [a] ++ w.drop (j + 1))
      else none
    else
      if allDisj a ((w.drop j).take (i - j)) then
        some (w.take j ++ [a] ++ (w.drop j).take (i - j) ++ w.drop (i + 1))
      else none

/-- Execute one step at width bound `k`. -/
def exec (k : ℕ) (db : List Eqn) : Step → List Lt → Option (List Lt)
  | .rw e pos s rev, w =>
    match db[e]? with
    | none => none
    | some q =>
      if q.k + s ≤ k then
        if rev then replaceAt (upN s q.r) (upN s q.l) w pos
        else replaceAt (upN s q.l) (upN s q.r) w pos
      else none
  | .mv i j, w => moveAt w i j

/-- Execute a derivation. -/
def run (k : ℕ) (db : List Eqn) : List Step → List Lt → Option (List Lt)
  | [], w => some w
  | s :: ss, w =>
    match exec k db s w with
    | none => none
    | some w' => run k db ss w'

/-- The derivation `steps` turns `w` into `v`. -/
def derives (k : ℕ) (db : List Eqn) (steps : List Step) (w v : List Lt) : Bool :=
  decide (run k db steps w = some v)

/-! ### Soundness -/

theorem holds_upN {k : ℕ} {l r : List Lt} (h : Holds k l r) :
    ∀ s : ℕ, Holds (k + s) (upN s l) (upN s r)
  | 0 => h
  | s + 1 => (holds_upN h s).up

theorem replaceAt_sound {k : ℕ} {l r w w' : List Lt} {pos : ℕ} (h : Holds k l r)
    (hw : replaceAt l r w pos = some w') : Holds k w w' := by
  unfold replaceAt at hw
  split_ifs at hw with hc
  obtain ⟨h1, h2⟩ := hc
  cases hw
  have e : w = w.take pos ++ l ++ w.drop (pos + l.length) := by
    conv_lhs => rw [← List.take_append_drop pos w]
    rw [List.append_assoc]
    congr 1
    conv_lhs => rw [← List.take_append_drop l.length (w.drop pos)]
    rw [h1, List.drop_drop, Nat.add_comm]
  rw [e]
  have := Holds.congr (w.take pos) (w.drop (pos + l.length)) h
  convert this using 1
  rw [← e]

theorem allDisj_move {a : Lt} : ∀ {u : List Lt}, allDisj a u = true →
    Holds 0 (a :: u) (u ++ [a])
  | [], _ => Holds.refl _ _
  | b :: u, h => by
    simp only [allDisj, List.all_cons, Bool.and_eq_true] at h
    have h1 : Holds 0 (a :: b :: u) (b :: a :: u) := by
      simpa using Holds.congr [] u (Holds.comm h.1)
    have h2 : Holds 0 (b :: a :: u) (b :: (u ++ [a])) := by
      simpa using Holds.congr [b] [] (allDisj_move h.2)
    exact h1.trans h2

theorem split_fwd (w : List Lt) {i j : ℕ} (hi : i < w.length) (hij : i ≤ j) :
    w = w.take i ++ w[i] :: ((w.drop (i + 1)).take (j - i) ++ w.drop (j + 1)) := by
  have h2 : w.drop (i + 1) = (w.drop (i + 1)).take (j - i) ++ w.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop (j - i) (w.drop (i + 1))]
    rw [List.drop_drop]
    congr 2
    omega
  rw [← h2, ← List.drop_eq_getElem_cons hi, List.take_append_drop]

theorem split_bwd (w : List Lt) {i j : ℕ} (hi : i < w.length) (hij : j ≤ i) :
    w = w.take j ++ ((w.drop j).take (i - j) ++ w[i] :: w.drop (i + 1)) := by
  have h2 : w.drop j = (w.drop j).take (i - j) ++ w[i] :: w.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop (i - j) (w.drop j)]
    rw [List.drop_drop, show j + (i - j) = i by omega, List.drop_eq_getElem_cons hi]
  rw [← h2, List.take_append_drop]

theorem moveAt_sound {w w' : List Lt} {i j : ℕ} (hw : moveAt w i j = some w') :
    Holds 0 w w' := by
  unfold moveAt at hw
  match ha : w[i]? with
  | none => rw [ha] at hw; cases hw
  | some a =>
    rw [ha] at hw
    dsimp only at hw
    have hi : i < w.length := by
      rcases List.getElem?_eq_some_iff.1 ha with ⟨hi, _⟩; exact hi
    have hai : w[i] = a := by
      rcases List.getElem?_eq_some_iff.1 ha with ⟨_, h⟩; exact h
    by_cases hij : i < j
    · rw [if_pos hij] at hw
      by_cases hc : (allDisj a ((w.drop (i + 1)).take (j - i)) && decide (j < w.length)) = true
      swap
      · rw [if_neg hc] at hw; cases hw
      rw [if_pos hc] at hw
      cases hw
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hd, hj⟩ := hc
      have e := split_fwd w hi hij.le
      rw [hai] at e
      have h2 := Holds.congr (w.take i) (w.drop (j + 1)) (allDisj_move hd)
      rw [List.append_assoc, List.cons_append, ← e] at h2
      simpa [List.append_assoc] using h2
    · rw [if_neg hij] at hw
      by_cases hc : allDisj a ((w.drop j).take (i - j)) = true
      swap
      · rw [if_neg hc] at hw; cases hw
      rw [if_pos hc] at hw
      cases hw
      have e := split_bwd w hi (by omega : j ≤ i)
      rw [hai] at e
      have h2 := Holds.congr (w.take j) (w.drop (i + 1)) (allDisj_move hc).symm
      rw [List.append_assoc, List.append_assoc, List.singleton_append, ← e] at h2
      simpa [List.append_assoc] using h2

theorem exec_sound {k : ℕ} {db : List Eqn} (hdb : ∀ q ∈ db, Holds q.k q.l q.r)
    {s : Step} {w w' : List Lt} (h : exec k db s w = some w') : Holds k w w' := by
  cases s with
  | rw e pos sh rev =>
    simp only [exec] at h
    match hq : db[e]? with
    | none => rw [hq] at h; cases h
    | some q =>
      rw [hq] at h
      dsimp only at h
      have hq' := hdb q (List.mem_of_getElem? hq)
      by_cases hk : q.k + sh ≤ k
      swap
      · rw [if_neg hk] at h; cases h
      rw [if_pos hk] at h
      cases rev
      · exact replaceAt_sound ((holds_upN hq' sh).mono hk) h
      · exact replaceAt_sound ((holds_upN hq' sh).symm.mono hk) h
  | mv i j => exact (moveAt_sound h).mono (Nat.zero_le _)

theorem run_sound {k : ℕ} {db : List Eqn} (hdb : ∀ q ∈ db, Holds q.k q.l q.r) :
    ∀ {steps : List Step} {w w' : List Lt}, run k db steps w = some w' → Holds k w w'
  | [], w, w', h => by simp only [run, Option.some.injEq] at h; subst h; exact Holds.refl _ _
  | s :: ss, w, w', h => by
    simp only [run] at h
    match he : exec k db s w with
    | none => rw [he] at h; cases h
    | some w'' =>
      rw [he] at h
      exact (exec_sound hdb he).trans (run_sound hdb h)

/-- A derivation checked by `derives` is sound. -/
theorem Holds.of_derives {k : ℕ} {db : List Eqn} (hdb : ∀ q ∈ db, Holds q.k q.l q.r)
    {steps : List Step} {w v : List Lt} (h : derives k db steps w v = true) : Holds k w v :=
  run_sound hdb (of_decide_eq_true h)

end QCert.RealStabilizer

namespace QCert.RealStabilizer

/-- Building the hypothesis of `Holds.of_derives` entry by entry. -/
theorem db_ok_cons {q : Eqn} {db : List Eqn} (h : Holds q.k q.l q.r)
    (t : ∀ x ∈ db, Holds x.k x.l x.r) : ∀ x ∈ q :: db, Holds x.k x.l x.r := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact h
  · exact t x hx

theorem db_ok_nil : ∀ x ∈ ([] : List Eqn), Holds x.k x.l x.r := fun _ h => absurd h List.not_mem_nil

end QCert.RealStabilizer
