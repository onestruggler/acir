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

The kernel pays for every unfolding, so the steps are written for it: a
rewrite walks to its position once and strips the equation's side from the
word there (`replaceAt`, through `stripPrefix`), where a first version
took, dropped, compared and re-appended the word several times through
`Decidable` instances on `List Lt`; a move carries the letter past the
letters it crosses in one pass (`moveFwd`, `pullBack`); the equation is
looked up by primitive recursion (`nthE`), and the tests are `Lt.beq`,
`Nat.ble` and `Lt.disj` under `bif`.
-/
import QCert.SelingerClifford.Letters

namespace QCert.SelingerClifford

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

namespace Lt

/-- Boolean equality of letters, by `Nat.beq` on the wire. -/
def beq : Lt → Lt → Bool
  | om, om => true
  | H i, H j => i.beq j
  | S i, S j => i.beq j
  | CZ i, CZ j => i.beq j
  | _, _ => false

theorem eq_of_beq : ∀ {a b : Lt}, beq a b = true → a = b
  | om, om, _ => rfl
  | H _, H _, h => congrArg H (Nat.eq_of_beq_eq_true h)
  | S _, S _, h => congrArg S (Nat.eq_of_beq_eq_true h)
  | CZ _, CZ _, h => congrArg CZ (Nat.eq_of_beq_eq_true h)
  | om, H _, h | om, S _, h | om, CZ _, h | H _, om, h | H _, S _, h | H _, CZ _, h
  | S _, om, h | S _, H _, h | S _, CZ _, h | CZ _, om, h | CZ _, H _, h | CZ _, S _, h =>
    nomatch h

end Lt

/-- Boolean equality of words. -/
def eqL : List Lt → List Lt → Bool
  | [], [] => true
  | a :: l, b :: m => a.beq b && eqL l m
  | _, _ => false

theorem eq_of_eqL : ∀ {l m : List Lt}, eqL l m = true → l = m
  | [], [], _ => rfl
  | a :: l, b :: m, h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [Lt.eq_of_beq h.1, eq_of_eqL h.2]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- A list of letters moved up `s` wires. -/
def upN : ℕ → List Lt → List Lt
  | 0, l => l
  | s + 1, l => (upN s l).map Lt.up

/-- The equation `e` of the database, by primitive recursion. -/
def nthE (db : List Eqn) : ℕ → Option Eqn :=
  List.rec (motive := fun _ => ℕ → Option Eqn) (fun _ => none)
    (fun q _ ih e => Nat.rec (motive := fun _ => Option Eqn) (some q) (fun e' _ => ih e') e) db

theorem nthE_mem : ∀ {db : List Eqn} {e : ℕ} {q : Eqn}, nthE db e = some q → q ∈ db
  | [], e, q, h => nomatch h
  | q' :: db, 0, q, h => by
    have h' : some q' = some q := h
    cases h'; exact List.mem_cons_self
  | q' :: db, e + 1, q, h =>
    List.mem_cons_of_mem _ (nthE_mem (db := db) (e := e) (show nthE db e = some q from h))

/-- The word `w` with its prefix `l` stripped. -/
def stripPrefix : List Lt → List Lt → Option (List Lt)
  | [], w => some w
  | a :: l, b :: w => bif a.beq b then stripPrefix l w else none
  | _ :: _, [] => none

theorem stripPrefix_eq : ∀ {l w rest : List Lt}, stripPrefix l w = some rest → w = l ++ rest
  | [], w, rest, h => by simp only [stripPrefix, Option.some.injEq] at h; rw [h]; rfl
  | a :: l, b :: w, rest, h => by
    simp only [stripPrefix] at h
    cases hab : a.beq b with
    | false => rw [hab] at h; exact nomatch h
    | true =>
      rw [hab] at h
      rw [Lt.eq_of_beq hab, stripPrefix_eq h]; rfl
  | _ :: _, [], rest, h => nomatch h

/-- Replace the segment `l` at position `pos` of `w` by `r`. -/
def replaceAt (l r : List Lt) : List Lt → ℕ → Option (List Lt)
  | w, 0 => (stripPrefix l w).map (r ++ ·)
  | [], _ + 1 => none
  | a :: w, pos + 1 => (replaceAt l r w pos).map (a :: ·)

/-- All letters of `u` are on wires disjoint from `a`. -/
def allDisj (a : Lt) (u : List Lt) : Bool := u.all fun b => a.disj b

/-- `a` moved past the next `d` letters, each on wires disjoint from it. -/
def moveFwd (a : Lt) : ℕ → List Lt → Option (List Lt)
  | 0, w => some (a :: w)
  | _ + 1, [] => none
  | d + 1, b :: w => bif a.disj b then (moveFwd a d w).map (b :: ·) else none

/-- The letter at position `d` brought to the front, past the `d` letters
before it, each on wires disjoint from it. -/
def pullBack : ℕ → List Lt → Option (Lt × List Lt)
  | 0, a :: w => some (a, w)
  | 0, [] => none
  | _ + 1, [] => none
  | d + 1, b :: w =>
    match pullBack d w with
    | some (a, w') => bif a.disj b then some (a, b :: w') else none
    | none => none

/-- Move the letter at position `i` to position `j`, both relative to the
start of `w`, one of them `0`. -/
def moveFrom (w : List Lt) (i j : ℕ) : Option (List Lt) :=
  bif Nat.blt i j then
    match w with
    | a :: rest => moveFwd a j rest
    | [] => none
  else
    match pullBack i w with
    | some (a, w') => some (a :: w')
    | none => none

/-- Walk `p` letters into the word, then move. -/
def moveWalk : ℕ → List Lt → ℕ → ℕ → Option (List Lt)
  | 0, w, i, j => moveFrom w i j
  | _ + 1, [], _, _ => none
  | p + 1, a :: w, i, j => (moveWalk p w i j).map (a :: ·)

/-- Move the letter at position `i` to position `j`. -/
def moveAt (w : List Lt) (i j : ℕ) : Option (List Lt) :=
  moveWalk (min i j) w (i - min i j) (j - min i j)

/-- Execute one step at width bound `k`. -/
def exec (k : ℕ) (db : List Eqn) : Step → List Lt → Option (List Lt)
  | .rw e pos s rev, w =>
    match nthE db e with
    | none => none
    | some q =>
      bif Nat.ble (q.k + s) k then
        bif rev then replaceAt (upN s q.r) (upN s q.l) w pos
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
  match run k db steps w with
  | some w' => eqL w' v
  | none => false

/-! ### Soundness -/

theorem holds_upN {k : ℕ} {l r : List Lt} (h : Holds k l r) :
    ∀ s : ℕ, Holds (k + s) (upN s l) (upN s r)
  | 0 => h
  | s + 1 => (holds_upN h s).up

theorem replaceAt_sound {k : ℕ} {l r : List Lt} (h : Holds k l r) :
    ∀ {w w' : List Lt} {pos : ℕ}, replaceAt l r w pos = some w' → Holds k w w'
  | w, w', 0, hw => by
    simp only [replaceAt, Option.map_eq_some_iff] at hw
    obtain ⟨rest, hr, rfl⟩ := hw
    rw [stripPrefix_eq hr]
    simpa using Holds.congr [] rest h
  | [], w', _ + 1, hw => nomatch hw
  | a :: w, w', pos + 1, hw => by
    simp only [replaceAt, Option.map_eq_some_iff] at hw
    obtain ⟨w'', hw'', rfl⟩ := hw
    simpa using Holds.congr [a] [] (replaceAt_sound h hw'')

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

theorem moveFwd_sound (a : Lt) : ∀ {d : ℕ} {w w' : List Lt}, moveFwd a d w = some w' →
    Holds 0 (a :: w) w'
  | 0, w, w', h => by
    simp only [moveFwd, Option.some.injEq] at h; rw [h]; exact Holds.refl _ _
  | _ + 1, [], w', h => nomatch h
  | d + 1, b :: w, w', h => by
    simp only [moveFwd] at h
    cases hab : a.disj b with
    | false => rw [hab] at h; exact nomatch h
    | true =>
      rw [hab] at h
      simp only [cond_true, Option.map_eq_some_iff] at h
      obtain ⟨w'', hw'', rfl⟩ := h
      have h1 : Holds 0 (a :: b :: w) (b :: a :: w) := by
        simpa using Holds.congr [] w (Holds.comm hab)
      have h2 : Holds 0 (b :: a :: w) (b :: w'') := by
        simpa using Holds.congr [b] [] (moveFwd_sound a hw'')
      exact h1.trans h2

theorem pullBack_sound : ∀ {d : ℕ} {w : List Lt} {a : Lt} {w' : List Lt},
    pullBack d w = some (a, w') → Holds 0 w (a :: w')
  | 0, b :: w, a, w', h => by
    simp only [pullBack, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact Holds.refl _ _
  | 0, [], _, _, h => nomatch h
  | _ + 1, [], _, _, h => nomatch h
  | d + 1, b :: w, a, w', h => by
    simp only [pullBack] at h
    match hp : pullBack d w with
    | none => rw [hp] at h; exact nomatch h
    | some (a', w'') =>
      rw [hp] at h
      dsimp only at h
      cases hab : a'.disj b with
      | false => rw [hab] at h; exact nomatch h
      | true =>
        rw [hab] at h
        simp only [cond_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨ha, hw⟩ := h
        subst hw
        rw [← ha]
        have h1 : Holds 0 (b :: w) (b :: a' :: w'') := by
          simpa using Holds.congr [b] [] (pullBack_sound hp)
        have h2 : Holds 0 (b :: a' :: w'') (a' :: b :: w'') := by
          simpa using Holds.congr [] w'' (Holds.comm hab).symm
        exact h1.trans h2

theorem moveFrom_sound {w w' : List Lt} {i j : ℕ} (h : moveFrom w i j = some w') :
    Holds 0 w w' := by
  unfold moveFrom at h
  cases hij : Nat.blt i j with
  | true =>
    rw [hij, cond_true] at h
    cases w with
    | nil => exact nomatch h
    | cons a rest => exact moveFwd_sound a h
  | false =>
    rw [hij, cond_false] at h
    match hp : pullBack i w with
    | none => rw [hp] at h; exact nomatch h
    | some (a, w'') =>
      rw [hp] at h
      simp only [Option.some.injEq] at h
      rw [← h]
      exact pullBack_sound hp

theorem moveWalk_sound : ∀ {p : ℕ} {w w' : List Lt} {i j : ℕ}, moveWalk p w i j = some w' →
    Holds 0 w w'
  | 0, w, w', i, j, h => moveFrom_sound h
  | _ + 1, [], _, _, _, h => nomatch h
  | p + 1, a :: w, w', i, j, h => by
    simp only [moveWalk, Option.map_eq_some_iff] at h
    obtain ⟨w'', hw'', rfl⟩ := h
    simpa using Holds.congr [a] [] (moveWalk_sound hw'')

theorem moveAt_sound {w w' : List Lt} {i j : ℕ} (hw : moveAt w i j = some w') :
    Holds 0 w w' :=
  moveWalk_sound hw

theorem exec_sound {k : ℕ} {db : List Eqn} (hdb : ∀ q ∈ db, Holds q.k q.l q.r)
    {s : Step} {w w' : List Lt} (h : exec k db s w = some w') : Holds k w w' := by
  cases s with
  | rw e pos sh rev =>
    simp only [exec] at h
    match hq : nthE db e with
    | none => rw [hq] at h; exact nomatch h
    | some q =>
      rw [hq] at h
      dsimp only at h
      have hq' := hdb q (nthE_mem hq)
      cases hk : Nat.ble (q.k + sh) k with
      | false => rw [hk] at h; exact nomatch h
      | true =>
        rw [hk] at h
        have hle : q.k + sh ≤ k := Nat.le_of_ble_eq_true hk
        cases rev
        · exact replaceAt_sound ((holds_upN hq' sh).mono hle) h
        · exact replaceAt_sound ((holds_upN hq' sh).symm.mono hle) h
  | mv i j => exact (moveAt_sound h).mono (Nat.zero_le _)

theorem run_sound {k : ℕ} {db : List Eqn} (hdb : ∀ q ∈ db, Holds q.k q.l q.r) :
    ∀ {steps : List Step} {w w' : List Lt}, run k db steps w = some w' → Holds k w w'
  | [], w, w', h => by simp only [run, Option.some.injEq] at h; subst h; exact Holds.refl _ _
  | s :: ss, w, w', h => by
    simp only [run] at h
    match he : exec k db s w with
    | none => rw [he] at h; exact nomatch h
    | some w'' =>
      rw [he] at h
      exact (exec_sound hdb he).trans (run_sound hdb h)

/-- A derivation checked by `derives` is sound. -/
theorem Holds.of_derives {k : ℕ} {db : List Eqn} (hdb : ∀ q ∈ db, Holds q.k q.l q.r)
    {steps : List Step} {w v : List Lt} (h : derives k db steps w v = true) : Holds k w v := by
  unfold derives at h
  match hr : run k db steps w with
  | none => rw [hr] at h; exact nomatch h
  | some w' =>
    rw [hr] at h
    rw [← eq_of_eqL h]
    exact run_sound hdb hr

end QCert.SelingerClifford

namespace QCert.SelingerClifford

/-- Building the hypothesis of `Holds.of_derives` entry by entry. -/
theorem db_ok_cons {q : Eqn} {db : List Eqn} (h : Holds q.k q.l q.r)
    (t : ∀ x ∈ db, Holds x.k x.l x.r) : ∀ x ∈ q :: db, Holds x.k x.l x.r := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact h
  · exact t x hx

theorem db_ok_nil : ∀ x ∈ ([] : List Eqn), Holds x.k x.l x.r := fun _ h => absurd h List.not_mem_nil

end QCert.SelingerClifford
