/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A rewriting engine for derivations on a fixed number of wires

Circuits on `N + 1` wires are written as lists of letters (`L`): `H`, `Z` on
wire `j`, `CZ` and `CH` on the wires `j, j + 1` (`CH` with its `H` on wire
`j`), the swap of Equation (8) on the wires `j, j + 1`, in the order of the
drawing (`circW`, through `drawn`).  A derivation is a list of steps, each
one of

* `rw i k dir`: rewrite the factor at position `i` with equation `k` of a
  table of equations that hold (`Tbl`, `AllD`), from right to left when
  `dir`;
* `sw i`: exchange the letters at positions `i`, `i + 1`, which act on
  disjoint wires (the structural rules);
* `sem i len r`: Lemma 5.1, replace the `len` letters at position `i` by
  `r` when the two windows avoid wire `0`, or both avoid the top wire, and
  have the same semantics on the remaining `N` wires, decided by
  `Fast.check`.  This needs completeness on `N` wires (`IH (N + 1)`).

`check` runs a derivation and compares with the expected word; it is a
Boolean, decided by `decide +kernel`, and `check_sound` makes it a
derivation of the theory.
-/
import QCert.RealCliffordCH.Sec8.Weak
import QCert.RealCliffordCH.Sec8.Fast

namespace QCert.RealCliffordCH.Sec8.Eng

open Circuit

/-- The letters: gates placed on given wires. -/
inductive L
  | H (j : ℕ)
  | Z (j : ℕ)
  | C (j : ℕ)
  | K (j : ℕ)
  | S (j : ℕ)
  deriving DecidableEq, Repr

namespace L

/-- The lowest wire. -/
def lo : L → ℕ
  | H j | Z j | C j | K j | S j => j

/-- The number of wires. -/
def wd : L → ℕ
  | H _ | Z _ => 1
  | C _ | K _ | S _ => 2

/-- The letter one wire down. -/
def down : L → L
  | H j => H (j - 1) | Z j => Z (j - 1) | C j => C (j - 1) | K j => K (j - 1) | S j => S (j - 1)

/-- The circuit of a letter on `n` wires. -/
def circ (n : ℕ) : L → Circ n
  | H j => place1 n j h
  | Z j => place1 n j z
  | C j => place2 n j cz
  | K j => place2 n j ch
  | S j => place2 n j swap

end L

/-- A word of letters as a circuit, in drawn order. -/
def circW (n : ℕ) (l : List L) : Circ n := drawn (l.map (L.circ n))

theorem circW_nil (n : ℕ) : circW n [] = 1 := rfl

theorem circW_cons (n : ℕ) (x : L) (l : List L) : circW n (x :: l) = circW n l * x.circ n := by
  simp [circW, drawn, List.prod_append]

theorem circW_append (n : ℕ) (a b : List L) : circW n (a ++ b) = circW n b * circW n a := by
  simp [circW, drawn, List.prod_append]

/-! ## Letters on wires that avoid the bottom or the top wire -/

theorem place1_succ (N j : ℕ) (w : Circ 1) : place1 (N + 1) (j + 1) w = shift (place1 N j w) := rfl
theorem place2_succ (N j : ℕ) (w : Circ 2) : place2 (N + 1) (j + 1) w = shift (place2 N j w) := rfl

theorem circ_shift (N : ℕ) (x : L) (hx : 1 ≤ x.lo) : x.circ (N + 1) = shift (x.down.circ N) := by
  cases x with
  | H j => obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp [L.lo] at hx; omega⟩; rfl
  | Z j => obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp [L.lo] at hx; omega⟩; rfl
  | C j => obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp [L.lo] at hx; omega⟩; rfl
  | K j => obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp [L.lo] at hx; omega⟩; rfl
  | S j => obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp [L.lo] at hx; omega⟩; rfl

theorem circW_shift (N : ℕ) (l : List L) (hl : ∀ x ∈ l, 1 ≤ x.lo) :
    circW (N + 1) l = shift (circW N (l.map L.down)) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [circW_cons, List.map_cons, circW_cons, map_mul, ih (fun y hy => hl y (by simp [hy])),
      circ_shift N x (hl x (by simp))]

theorem padTop_shift {n : ℕ} (w : Circ n) : padTop (shift w) = shift (padTop w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih => rw [map_mul, map_mul, map_mul, map_mul, ih]; rfl

theorem padTop_pad1 (k : ℕ) (w : Circ 1) : padTop (Circuit.pad k w) = Circuit.pad (k + 1) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, ih]
    congr 1
    match g with
    | .gate0 c => exact nomatch c
    | .gate1 c => rfl
    | .up g => exact match g with | .gate0 c => nomatch c

theorem padTop_pad2 (k : ℕ) (w : Circ 2) : padTop (Circuit.pad k w) = Circuit.pad (k + 1) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, ih]
    congr 1
    match g with
    | .gate0 c => exact nomatch c
    | .gate1 c => rfl
    | .gate2 c => rfl
    | .up g =>
      match g with
      | .gate0 c => exact nomatch c
      | .gate1 c => rfl
      | .up g => exact match g with | .gate0 c => nomatch c

theorem place1_top : ∀ (N j : ℕ) (w : Circ 1), j + 1 ≤ N → place1 (N + 1) j w = padTop (place1 N j w)
  | N + 1, 0, w, _ => (padTop_pad1 N w).symm
  | N + 1, j + 1, w, h => by
    rw [place1_succ, place1_succ, place1_top N j w (by omega), padTop_shift]
  | 0, _, _, h => by omega

theorem place2_top : ∀ (N j : ℕ) (w : Circ 2), j + 2 ≤ N → place2 (N + 1) j w = padTop (place2 N j w)
  | N + 2, 0, w, _ => (padTop_pad2 N w).symm
  | N + 1, j + 1, w, h => by
    rw [place2_succ, place2_succ, place2_top N j w (by omega), padTop_shift]
  | 0, _, _, h => by omega
  | 1, 0, _, h => by omega

theorem circ_top (N : ℕ) (x : L) (hx : x.lo + x.wd ≤ N) : x.circ (N + 1) = padTop (x.circ N) := by
  cases x with
  | H j => exact place1_top N j _ hx
  | Z j => exact place1_top N j _ hx
  | C j => exact place2_top N j _ hx
  | K j => exact place2_top N j _ hx
  | S j => exact place2_top N j _ hx

theorem circW_top (N : ℕ) (l : List L) (hl : ∀ x ∈ l, x.lo + x.wd ≤ N) :
    circW (N + 1) l = padTop (circW N l) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [circW_cons, circW_cons, map_mul, ih (fun y hy => hl y (by simp [hy])),
      circ_top N x (hl x (by simp))]

/-! ## Disjoint letters commute -/

/-- A one-wire gate on wire 0 commutes with any circuit one wire up. -/
theorem comm1_shift {N : ℕ} (g : Gate 1) (w : Circ N) :
    Derivable (theory (N + 1)) (shift w * g1 g) (g1 g * shift w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one, one_mul, mul_one]
  | mul_of x w ih =>
    have hx : Derivable (theory (N + 1)) (FreeMonoid.of x.up * g1 g) (g1 g * FreeMonoid.of x.up) :=
      Derivable.of (Lift.comm1 g x)
    have h1 := dleft (FreeMonoid.of x.up) ih
    have h2 := dright (shift w) hx
    rw [map_mul, Circuit.shift_of, mul_assoc]
    refine h1.trans ?_
    rw [← mul_assoc, ← mul_assoc]
    exact h2

/-- A two-wire gate on wires 0, 1 commutes with any circuit two wires up. -/
theorem comm2_shift {N : ℕ} (g : Gate 2) (w : Circ N) :
    Derivable (theory (N + 2)) (shift (shift w) * g2 g) (g2 g * shift (shift w)) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one, map_one, one_mul, mul_one]
  | mul_of x w ih =>
    have hx : Derivable (theory (N + 2)) (FreeMonoid.of x.up.up * g2 g) (g2 g * FreeMonoid.of x.up.up) :=
      Derivable.of (Lift.comm2 g x)
    have h1 := dleft (FreeMonoid.of x.up.up) ih
    have h2 := dright (shift (shift w)) hx
    rw [map_mul, map_mul, Circuit.shift_of, Circuit.shift_of, mul_assoc]
    refine h1.trans ?_
    rw [← mul_assoc, ← mul_assoc]
    exact h2

/-- A circuit on the bottom wire commutes with any circuit one wire up. -/
theorem comm_pad1 {k : ℕ} (u : Circ 1) (w : Circ k) :
    Derivable (theory (k + 1)) (shift w * Circuit.pad k u) (Circuit.pad k u * shift w) := by
  induction u using FreeMonoid.inductionOn' with
  | one => rw [map_one, one_mul, mul_one]
  | mul_of x u ih =>
    have hx : Derivable (theory (k + 1)) (shift w * Circuit.pad k (FreeMonoid.of x))
        (Circuit.pad k (FreeMonoid.of x) * shift w) := by
      match x with
      | .gate0 c => exact nomatch c
      | .gate1 c => exact comm1_shift c w
      | .up x => exact match x with | .gate0 c => nomatch c
    rw [map_mul, ← mul_assoc]
    refine (dright _ hx).trans ?_
    rw [mul_assoc, mul_assoc]
    exact dleft _ ih

/-- A circuit on the bottom two wires commutes with any circuit two wires up. -/
theorem comm_pad2 {k : ℕ} (u : Circ 2) (w : Circ k) :
    Derivable (theory (k + 2)) (shift (shift w) * Circuit.pad k u)
      (Circuit.pad k u * shift (shift w)) := by
  induction u using FreeMonoid.inductionOn' with
  | one => rw [map_one, one_mul, mul_one]
  | mul_of x u ih =>
    have hx : Derivable (theory (k + 2)) (shift (shift w) * Circuit.pad k (FreeMonoid.of x))
        (Circuit.pad k (FreeMonoid.of x) * shift (shift w)) := by
      match x with
      | .gate0 c => exact nomatch c
      | .gate1 c => exact comm1_shift c (shift w)
      | .gate2 c => exact comm2_shift c w
      | .up x =>
        match x with
        | .gate0 c => exact nomatch c
        | .gate1 c =>
          have := derivable_shift (comm1_shift c w)
          rw [map_mul, map_mul] at this
          exact this
        | .up x => exact match x with | .gate0 c => nomatch c
    rw [map_mul, ← mul_assoc]
    refine (dright _ hx).trans ?_
    rw [mul_assoc, mul_assoc]
    exact dleft _ ih

/-- Two letters on disjoint wires, the first below the second. -/
def below (x y : L) : Bool := decide (x.lo + x.wd ≤ y.lo)

theorem down_lo (y : L) : y.down.lo = y.lo - 1 := by cases y <;> rfl
theorem down_wd (y : L) : y.down.wd = y.wd := by cases y <;> rfl

theorem comm_below : ∀ (N : ℕ) (x y : L), x.lo + x.wd ≤ y.lo →
    Derivable (theory N) (y.circ N * x.circ N) (x.circ N * y.circ N)
  | 0, x, y, _ => by
    have h0 : ∀ z : L, z.circ 0 = 1 := by intro z; cases z <;> rfl
    rw [h0, h0]
  | N + 1, x, y, hxy => by
    by_cases hx : x.lo = 0
    · cases x with
      | H j =>
        change j = 0 at hx; subst hx
        have hy : 1 ≤ y.lo := by change 0 + 1 ≤ y.lo at hxy; omega
        rw [circ_shift N y hy]
        exact comm_pad1 RealCliffordCH.h (y.down.circ N)
      | Z j =>
        change j = 0 at hx; subst hx
        have hy : 1 ≤ y.lo := by change 0 + 1 ≤ y.lo at hxy; omega
        rw [circ_shift N y hy]
        exact comm_pad1 RealCliffordCH.z (y.down.circ N)
      | C j =>
        change j = 0 at hx; subst hx
        have hy : 2 ≤ y.lo := by change 0 + 2 ≤ y.lo at hxy; omega
        cases N with
        | zero => rw [show (L.C 0).circ (0 + 1) = 1 from rfl, one_mul, mul_one]
        | succ N =>
          rw [circ_shift (N + 1) y (by omega), circ_shift N y.down (by rw [down_lo]; omega)]
          exact comm_pad2 cz (y.down.down.circ N)
      | K j =>
        change j = 0 at hx; subst hx
        have hy : 2 ≤ y.lo := by change 0 + 2 ≤ y.lo at hxy; omega
        cases N with
        | zero => rw [show (L.K 0).circ (0 + 1) = 1 from rfl, one_mul, mul_one]
        | succ N =>
          rw [circ_shift (N + 1) y (by omega), circ_shift N y.down (by rw [down_lo]; omega)]
          exact comm_pad2 ch (y.down.down.circ N)
      | S j =>
        change j = 0 at hx; subst hx
        have hy : 2 ≤ y.lo := by change 0 + 2 ≤ y.lo at hxy; omega
        cases N with
        | zero => rw [show (L.S 0).circ (0 + 1) = 1 from rfl, one_mul, mul_one]
        | succ N =>
          rw [circ_shift (N + 1) y (by omega), circ_shift N y.down (by rw [down_lo]; omega)]
          exact comm_pad2 swap (y.down.down.circ N)
    · rw [circ_shift N x (by omega), circ_shift N y (by omega), ← map_mul, ← map_mul]
      exact derivable_shift (comm_below N x.down y.down (by rw [down_lo, down_lo, down_wd]; omega))

/-- Two letters on disjoint wires commute. -/
def disj (x y : L) : Bool := below x y || below y x

theorem comm_disj (N : ℕ) (x y : L) (h : disj x y = true) :
    Derivable (theory N) (y.circ N * x.circ N) (x.circ N * y.circ N) := by
  simp only [disj, below, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact comm_below N x y h
  · exact (comm_below N y x h).symm

/-! ## Steps and runs -/

/-- A table of equations between words of letters. -/
abbrev Tbl := List (List L × List L)

/-- Every equation of the table holds on `n` wires. -/
def AllD (n : ℕ) (T : Tbl) : Prop :=
  ∀ e ∈ T, Derivable (theory n) (circW n e.1) (circW n e.2)

/-- A step of a derivation. -/
inductive Step
  /-- rewrite at position `i` with equation `k` of the table (backwards when `dir`) -/
  | rw (i k : ℕ) (dir : Bool)
  /-- exchange the disjoint letters at positions `i`, `i + 1` -/
  | sw (i : ℕ)
  /-- Lemma 5.1: replace the `len` letters at `i` by `r` -/
  | sem (i len : ℕ) (r : List L)
  deriving Repr

/-- An equation in the direction of a step. -/
def orient (dir : Bool) (e : List L × List L) : List L × List L := if dir then (e.2, e.1) else e

/-- Two windows idle on the bottom wire, or on the top wire, of `N + 1`
wires, with the same semantics. -/
def semOK (N : ℕ) (a b : List L) : Bool :=
  ((a ++ b).all (fun x => decide (1 ≤ x.lo)) &&
      Fast.check (circW N (a.map L.down)) (circW N (b.map L.down))) ||
    ((a ++ b).all (fun x => decide (x.lo + x.wd ≤ N)) && Fast.check (circW N a) (circW N b))

/-- Apply a step. -/
def applyStep (N : ℕ) (T : Tbl) (cur : List L) : Step → Option (List L)
  | .rw i k dir =>
    match T[k]? with
    | none => none
    | some e =>
      if (cur.drop i).take (orient dir e).1.length == (orient dir e).1 then
        some (cur.take i ++ (orient dir e).2 ++ cur.drop (i + (orient dir e).1.length))
      else none
  | .sw i =>
    match (cur.drop i).take 2 with
    | [x, y] => if disj x y then some (cur.take i ++ [y, x] ++ cur.drop (i + 2)) else none
    | _ => none
  | .sem i len r =>
    if ((cur.drop i).take len).length == len && semOK N ((cur.drop i).take len) r then
      some (cur.take i ++ r ++ cur.drop (i + len))
    else none

/-- Run a derivation. -/
def runSteps (N : ℕ) (T : Tbl) : List L → List Step → Option (List L)
  | cur, [] => some cur
  | cur, s :: ss =>
    match applyStep N T cur s with
    | none => none
    | some nxt => runSteps N T nxt ss

/-- Run a derivation from `w` and compare the result with `v`. -/
def check (N : ℕ) (T : Tbl) (w v : List L) (ss : List Step) : Bool :=
  match runSteps N T w ss with
  | none => false
  | some u => u == v

section Sound

variable {N : ℕ}

theorem replace (u a b v : List L) (h : Derivable (theory (N + 1)) (circW (N + 1) a) (circW (N + 1) b)) :
    Derivable (theory (N + 1)) (circW (N + 1) (u ++ a ++ v)) (circW (N + 1) (u ++ b ++ v)) := by
  rw [circW_append, circW_append, circW_append, circW_append, ← mul_assoc, ← mul_assoc]
  exact dctx _ _ h

theorem split_at (cur : List L) (i len : ℕ) :
    cur = cur.take i ++ (cur.drop i).take len ++ cur.drop (i + len) := by
  rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

theorem semOK_sound (ih : IH (N + 1)) {a b : List L} (h : semOK N a b = true) :
    Derivable (theory (N + 1)) (circW (N + 1) a) (circW (N + 1) b) := by
  simp only [semOK, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hl, hc⟩ | ⟨hl, hc⟩
  · rw [circW_shift N a (fun x hx => hl x (List.mem_append_left _ hx)),
      circW_shift N b (fun x hx => hl x (List.mem_append_right _ hx))]
    exact sem_step_shift ih (Fast.sem_of_fast hc)
  · rw [circW_top N a (fun x hx => hl x (List.mem_append_left _ hx)),
      circW_top N b (fun x hx => hl x (List.mem_append_right _ hx))]
    exact sem_step_top ih (Fast.sem_of_fast hc)

theorem applyStep_sound (ih : IH (N + 1)) {T : Tbl} (hT : AllD (N + 1) T) {cur nxt : List L}
    {s : Step} (h : applyStep N T cur s = some nxt) :
    Derivable (theory (N + 1)) (circW (N + 1) cur) (circW (N + 1) nxt) := by
  cases s with
  | rw i k dir =>
    simp only [applyStep] at h
    split at h
    · exact absurd h (by simp)
    · rename_i e he
      split_ifs at h with hm
      cases h
      have hmem : e ∈ T := List.mem_of_getElem? he
      have he' : Derivable (theory (N + 1)) (circW (N + 1) (orient dir e).1)
          (circW (N + 1) (orient dir e).2) := by
        unfold orient; split_ifs
        · exact (hT e hmem).symm
        · exact hT e hmem
      rw [beq_iff_eq] at hm
      conv_lhs => rw [split_at cur i (orient dir e).1.length, hm]
      exact replace _ _ _ _ he'
  | sw i =>
    simp only [applyStep] at h
    split at h
    · rename_i x y hxy
      split_ifs at h with hd
      cases h
      conv_lhs => rw [split_at cur i 2, hxy]
      refine replace _ _ _ _ ?_
      rw [circW_cons, circW_cons, circW_cons, circW_cons, circW_nil, one_mul, one_mul]
      exact comm_disj (N + 1) x y hd
    · exact absurd h (by simp)
  | sem i len r =>
    simp only [applyStep] at h
    split_ifs at h with hm
    cases h
    rw [Bool.and_eq_true] at hm
    conv_lhs => rw [split_at cur i len]
    exact replace _ _ _ _ (semOK_sound ih hm.2)

theorem runSteps_sound (ih : IH (N + 1)) {T : Tbl} (hT : AllD (N + 1) T) :
    ∀ {cur u : List L} {ss : List Step}, runSteps N T cur ss = some u →
      Derivable (theory (N + 1)) (circW (N + 1) cur) (circW (N + 1) u) := by
  intro cur u ss h
  induction ss generalizing cur with
  | nil => simp only [runSteps, Option.some.injEq] at h; subst h; exact Derivable.refl _
  | cons s ss ihs =>
    simp only [runSteps] at h
    split at h
    · exact absurd h (by simp)
    · rename_i nxt hn
      exact (applyStep_sound ih hT hn).trans (ihs h)

/-- A run that passes `check` is a derivation. -/
theorem check_sound (ih : IH (N + 1)) {T : Tbl} (hT : AllD (N + 1) T) {w v : List L}
    {ss : List Step} (h : check N T w v ss = true) :
    Derivable (theory (N + 1)) (circW (N + 1) w) (circW (N + 1) v) := by
  unfold check at h
  split at h
  · exact absurd h (by simp)
  · rename_i u hu
    rw [beq_iff_eq] at h
    subst h
    exact runSteps_sound ih hT hu

end Sound

end QCert.RealCliffordCH.Sec8.Eng
