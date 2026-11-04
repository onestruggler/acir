/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): checked tables of equations

Derivations found outside Lean (`gen/` scripts, scratch) are replayed here
by the kernel.  An *equation* is a pair of lists of letters.  A *table* is
a list of equations, each proved by a certificate over the equations
before it; `checkTable` replays every certificate and `checkTable_valid`
turns one `decide +kernel` of it into derivability of every equation.

Two kinds of step:

* a plain step `(i, k, d)` replaces, at position `i`, the left side of
  equation `k` by its right side (`d = true`) or conversely;
* when every letter is an involution (`x x ≈ ε`), an equation `l = r` is
  the relator `l · rev r ≈ ε`, and so is every rotation of it or of its
  reverse; a rotation `u v` gives the rule `u → rev v`.  A rotation step
  `(i, k, rot, cut, rv)` applies the rule cut at `cut` from the relator of
  equation `k`, reversed when `rv`, rotated left by `rot`.

Certificates are packed into one natural number per equation (`decode`,
`decodeRot`).
-/
import QCert.Presentation
import QCert.CliffordT2.Derivation
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QCert.ToffoliHadamard.Engine

universe u

variable {α : Type u} [DecidableEq α] {Γ : WRel α}

/-- An equation between lists of letters. -/
abbrev Eqn (α : Type u) := List α × List α

/-- Every equation of the table is derivable. -/
def Valid (Γ : WRel α) (E : List (Eqn α)) : Prop :=
  ∀ e ∈ E, Derivable Γ (FreeMonoid.ofList e.1) (FreeMonoid.ofList e.2)

omit [DecidableEq α] in
theorem Valid.nil : Valid Γ ([] : List (Eqn α)) := by
  intro e he; simp at he

omit [DecidableEq α] in
theorem Valid.cons {e : Eqn α} {E : List (Eqn α)}
    (h : Derivable Γ (FreeMonoid.ofList e.1) (FreeMonoid.ofList e.2)) (hE : Valid Γ E) :
    Valid Γ (e :: E) := by
  intro f hf
  rcases List.mem_cons.1 hf with rfl | hf
  exacts [h, hE f hf]

omit [DecidableEq α] in
theorem Valid.append {E F : List (Eqn α)} (hE : Valid Γ E) (hF : Valid Γ F) :
    Valid Γ (E ++ F) := by
  intro e he
  rcases List.mem_append.1 he with h | h
  exacts [hE e h, hF e h]

omit [DecidableEq α] in
theorem Valid.get {E : List (Eqn α)} (hE : Valid Γ E) {k : ℕ} {e : Eqn α} (h : E[k]? = some e) :
    Derivable Γ (FreeMonoid.ofList e.1) (FreeMonoid.ofList e.2) :=
  hE e (List.mem_of_getElem? h)

/-! ## Replacing a factor -/

/-- `l` is a prefix of `w`: the rest of `w`. -/
def dropPrefix : List α → List α → Option (List α)
  | [], w => some w
  | _ :: _, [] => none
  | a :: l, b :: w => if a = b then dropPrefix l w else none

theorem dropPrefix_eq {l w r : List α} (h : dropPrefix l w = some r) : w = l ++ r := by
  induction l generalizing w with
  | nil => simp [dropPrefix] at h; simp [h]
  | cons a l ih =>
    cases w with
    | nil => simp [dropPrefix] at h
    | cons b w =>
      simp only [dropPrefix] at h
      split_ifs at h with hab
      · subst hab; simp [ih h]

/-- Replace, at position `i`, an occurrence of `l` by `r`. -/
def replaceAt (l r : List α) : ℕ → List α → Option (List α)
  | 0, w => (dropPrefix l w).map (r ++ ·)
  | _ + 1, [] => none
  | i + 1, a :: w => (replaceAt l r i w).map (a :: ·)

theorem replaceAt_eq {l r : List α} {i : ℕ} {w w' : List α} (h : replaceAt l r i w = some w') :
    ∃ p q, w = p ++ l ++ q ∧ w' = p ++ r ++ q := by
  induction i generalizing w w' with
  | zero =>
    simp only [replaceAt, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    exact ⟨[], q, by simp [dropPrefix_eq hq], by simp⟩
  | succ i ih =>
    cases w with
    | nil => simp [replaceAt] at h
    | cons a w =>
      simp only [replaceAt, Option.map_eq_some_iff] at h
      obtain ⟨w'', hw'', rfl⟩ := h
      obtain ⟨p, q, rfl, rfl⟩ := ih hw''
      exact ⟨a :: p, q, by simp, by simp⟩

omit [DecidableEq α] in
theorem derivable_middle {l r : List α}
    (h : Derivable Γ (FreeMonoid.ofList l) (FreeMonoid.ofList r)) (p q : List α) :
    Derivable Γ (FreeMonoid.ofList (p ++ l ++ q)) (FreeMonoid.ofList (p ++ r ++ q)) := by
  simp only [FreeMonoid.ofList_append]
  exact (h.mul_left _).mul_right _

theorem derivable_replaceAt {l r : List α}
    (h : Derivable Γ (FreeMonoid.ofList l) (FreeMonoid.ofList r)) {i : ℕ} {w w' : List α}
    (hw : replaceAt l r i w = some w') :
    Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  obtain ⟨p, q, rfl, rfl⟩ := replaceAt_eq hw
  exact derivable_middle h p q

/-! ## Plain steps -/

/-- A plain step `(i, k, d)`. -/
def step (E : List (Eqn α)) (w : List α) : ℕ × ℕ × Bool → Option (List α)
  | (i, k, d) =>
    match E[k]? with
    | none => none
    | some e => if d then replaceAt e.1 e.2 i w else replaceAt e.2 e.1 i w

/-- Replay plain steps. -/
def run (E : List (Eqn α)) : List α → List (ℕ × ℕ × Bool) → Option (List α)
  | w, [] => some w
  | w, s :: ss => (step E w s).bind fun w' => run E w' ss

theorem step_sound {E : List (Eqn α)} (hE : Valid Γ E) {w w' : List α} {s : ℕ × ℕ × Bool}
    (h : step E w s = some w') : Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  obtain ⟨i, k, d⟩ := s
  simp only [step] at h
  split at h
  · simp at h
  · rename_i e he
    have hd := hE.get he
    cases d
    · exact derivable_replaceAt hd.symm h
    · exact derivable_replaceAt hd h

theorem run_sound {E : List (Eqn α)} (hE : Valid Γ E) {w v : List α}
    {ss : List (ℕ × ℕ × Bool)} (h : run E w ss = some v) :
    Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList v) := by
  induction ss generalizing w with
  | nil => simp only [run, Option.some.injEq] at h; subst h; rfl
  | cons s ss ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨w', h1, h2⟩ := h
    exact (step_sound hE h1).trans (ih h2)

/-- Decode `n` plain steps: base `2²⁵`, digit `2 (4096 i + k) + d`. -/
def decode : ℕ → ℕ → List (ℕ × ℕ × Bool)
  | 0, _ => []
  | n + 1, c =>
    let s := c % 33554432
    (s / 2 / 4096, s / 2 % 4096, s % 2 == 1) :: decode n (c / 33554432)

/-! ## Rotation steps -/

/-- The relator of an equation `l = r`: `l · rev r`. -/
def relator (e : Eqn α) : List α := e.1 ++ e.2.reverse

/-- The rule cut from a relator `ρ`: reversed when `rv`, rotated left by
`rot`, split after `cut` letters `u v`; the rule is `u → rev v`. -/
def cutRule (ρ : List α) (rot cut : ℕ) (rv : Bool) : Eqn α :=
  let b := if rv then ρ.reverse else ρ
  let r := b.drop rot ++ b.take rot
  (r.take cut, (r.drop cut).reverse)

/-- A rotation step `(i, k, rot, cut, rv)`. -/
def rstep (E : List (Eqn α)) (w : List α) : ℕ × ℕ × ℕ × ℕ × Bool → Option (List α)
  | (i, k, rot, cut, rv) =>
    match E[k]? with
    | none => none
    | some e =>
      let p := cutRule (relator e) rot cut rv
      replaceAt p.1 p.2 i w

/-- Replay rotation steps. -/
def rrun (E : List (Eqn α)) : List α → List (ℕ × ℕ × ℕ × ℕ × Bool) → Option (List α)
  | w, [] => some w
  | w, s :: ss => (rstep E w s).bind fun w' => rrun E w' ss

section Involutions

variable (hinv : ∀ x : α, Derivable Γ (FreeMonoid.ofList [x, x]) 1)
include hinv

omit [DecidableEq α] in
/-- `l · rev l ≈ ε`. -/
theorem mul_reverse (l : List α) :
    Derivable Γ (FreeMonoid.ofList (l ++ l.reverse)) 1 := by
  induction l with
  | nil => simp; rfl
  | cons x l ih =>
    have h1 := derivable_middle (Γ := Γ) ih [x] [x]
    have e1 : [x] ++ (l ++ l.reverse) ++ [x] = x :: l ++ (x :: l).reverse := by simp
    have e2 : [x] ++ ([] : List α) ++ [x] = [x, x] := rfl
    rw [e1] at h1
    simp only [FreeMonoid.ofList_nil, FreeMonoid.ofList_append] at h1 ⊢
    refine h1.trans ?_
    simpa using hinv x

omit [DecidableEq α] in
/-- `rev l · l ≈ ε`. -/
theorem reverse_mul (l : List α) :
    Derivable Γ (FreeMonoid.ofList (l.reverse ++ l)) 1 := by
  simpa using mul_reverse hinv l.reverse

omit [DecidableEq α] in
/-- `a ≈ b` gives `a · rev b ≈ ε`. -/
theorem relator_of {a b : List α}
    (h : Derivable Γ (FreeMonoid.ofList a) (FreeMonoid.ofList b)) :
    Derivable Γ (FreeMonoid.ofList (a ++ b.reverse)) 1 := by
  rw [FreeMonoid.ofList_append]
  have := h.mul_right (FreeMonoid.ofList b.reverse)
  rw [← FreeMonoid.ofList_append] at this
  exact this.trans (mul_reverse hinv b)

omit [DecidableEq α] in
/-- `u · v ≈ ε` gives `u ≈ rev v`. -/
theorem split_of {u v : List α} (h : Derivable Γ (FreeMonoid.ofList (u ++ v)) 1) :
    Derivable Γ (FreeMonoid.ofList u) (FreeMonoid.ofList v.reverse) := by
  have h1 : Derivable Γ (FreeMonoid.ofList (u ++ v) * FreeMonoid.ofList v.reverse)
      (FreeMonoid.ofList v.reverse) := by
    simpa using h.mul_right (FreeMonoid.ofList v.reverse)
  have h2 : Derivable Γ (FreeMonoid.ofList u)
      (FreeMonoid.ofList (u ++ v) * FreeMonoid.ofList v.reverse) := by
    have := (mul_reverse hinv v).mul_left (FreeMonoid.ofList u)
    rw [mul_one] at this
    simpa [FreeMonoid.ofList_append, mul_assoc] using this.symm
  exact h2.trans h1

omit [DecidableEq α] in
/-- Relators are closed under rotation. -/
theorem rotate_of {u v : List α} (h : Derivable Γ (FreeMonoid.ofList (u ++ v)) 1) :
    Derivable Γ (FreeMonoid.ofList (v ++ u)) 1 := by
  -- v u ≈ v (u v) rev v ≈ v rev v ≈ ε
  have h1 := (h.mul_left (FreeMonoid.ofList v)).mul_right (FreeMonoid.ofList v.reverse)
  have e1 : FreeMonoid.ofList v * FreeMonoid.ofList (u ++ v) * FreeMonoid.ofList v.reverse =
      FreeMonoid.ofList (v ++ u) * FreeMonoid.ofList (v ++ v.reverse) := by
    simp [FreeMonoid.ofList_append, mul_assoc]
  have e2 : FreeMonoid.ofList v * (1 : FreeMonoid α) * FreeMonoid.ofList v.reverse =
      FreeMonoid.ofList (v ++ v.reverse) := by simp [FreeMonoid.ofList_append]
  rw [e1, e2] at h1
  have h3 : Derivable Γ (FreeMonoid.ofList (v ++ u) * FreeMonoid.ofList (v ++ v.reverse))
      (FreeMonoid.ofList (v ++ u)) := by
    simpa using (mul_reverse hinv v).mul_left (FreeMonoid.ofList (v ++ u))
  exact h3.symm.trans (h1.trans (mul_reverse hinv v))

omit [DecidableEq α] in
/-- Relators are closed under reversal. -/
theorem reverse_of {ρ : List α} (h : Derivable Γ (FreeMonoid.ofList ρ) 1) :
    Derivable Γ (FreeMonoid.ofList ρ.reverse) 1 := by
  -- rev ρ ≈ rev ρ · ρ ≈ ε
  have h1 := h.mul_left (FreeMonoid.ofList ρ.reverse)
  rw [mul_one, ← FreeMonoid.ofList_append] at h1
  exact h1.symm.trans (reverse_mul hinv ρ)

omit [DecidableEq α] in
theorem cutRule_sound {ρ : List α} (h : Derivable Γ (FreeMonoid.ofList ρ) 1)
    (rot cut : ℕ) (rv : Bool) :
    Derivable Γ (FreeMonoid.ofList (cutRule ρ rot cut rv).1)
      (FreeMonoid.ofList (cutRule ρ rot cut rv).2) := by
  unfold cutRule
  set b := if rv then ρ.reverse else ρ with hb
  have hb' : Derivable Γ (FreeMonoid.ofList b) 1 := by
    cases rv
    · simpa [hb] using h
    · simpa [hb] using reverse_of hinv h
  have hr : Derivable Γ (FreeMonoid.ofList (b.drop rot ++ b.take rot)) 1 :=
    rotate_of hinv (by simpa using hb')
  set r := b.drop rot ++ b.take rot
  have : Derivable Γ (FreeMonoid.ofList (r.take cut ++ r.drop cut)) 1 := by
    simpa using hr
  exact split_of hinv this

theorem rstep_sound {E : List (Eqn α)} (hE : Valid Γ E) {w w' : List α}
    {s : ℕ × ℕ × ℕ × ℕ × Bool} (h : rstep E w s = some w') :
    Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  obtain ⟨i, k, rot, cut, rv⟩ := s
  simp only [rstep] at h
  split at h
  · simp at h
  · rename_i e he
    exact derivable_replaceAt (cutRule_sound hinv (relator_of hinv (hE.get he)) rot cut rv) h

theorem rrun_sound {E : List (Eqn α)} (hE : Valid Γ E) {w v : List α}
    {ss : List (ℕ × ℕ × ℕ × ℕ × Bool)} (h : rrun E w ss = some v) :
    Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList v) := by
  induction ss generalizing w with
  | nil => simp only [rrun, Option.some.injEq] at h; subst h; rfl
  | cons s ss ih =>
    simp only [rrun, Option.bind_eq_some_iff] at h
    obtain ⟨w', h1, h2⟩ := h
    exact (rstep_sound hinv hE h1).trans (ih h2)

end Involutions

/-- Decode `n` rotation steps: base `2⁴⁴`, a digit packing
`i < 2¹¹, k < 2¹⁴, rot < 2⁹, cut < 2⁹, rv`. -/
def decodeRot : ℕ → ℕ → List (ℕ × ℕ × ℕ × ℕ × Bool)
  | 0, _ => []
  | n + 1, c =>
    let s := c % 17592186044416
    (s / 8589934592, s / 524288 % 16384, s / 1024 % 512, s / 2 % 512, s % 2 == 1) ::
      decodeRot n (c / 17592186044416)

/-! ## Tables -/

/-- A table entry: an equation, the number of steps and the packed steps;
the steps are plain (`rot = false`) or rotation steps. -/
structure Entry (α : Type u) where
  lhs : List α
  rhs : List α
  rot : Bool
  n : ℕ
  code : ℕ

/-- Replay one entry against the equations before it. -/
def Entry.check (E : List (Eqn α)) (t : Entry α) : Bool :=
  if t.rot then rrun E t.lhs (decodeRot t.n t.code) == some t.rhs
  else run E t.lhs (decode t.n t.code) == some t.rhs

/-- Check every entry against the base and the entries before it. -/
def checkTable (E : List (Eqn α)) : List (Entry α) → Bool
  | [] => true
  | t :: T => t.check E && checkTable (E ++ [(t.lhs, t.rhs)]) T

/-- The equations of a table. -/
def eqns (T : List (Entry α)) : List (Eqn α) := T.map fun t => (t.lhs, t.rhs)

/-- A checked table over a valid base is valid.  Rotation steps need every
letter to be an involution. -/
theorem checkTable_valid {E : List (Eqn α)} (hE : Valid Γ E)
    (hinv : ∀ x : α, Derivable Γ (FreeMonoid.ofList [x, x]) 1) {T : List (Entry α)}
    (h : checkTable E T = true) : Valid Γ (E ++ eqns T) := by
  induction T generalizing E with
  | nil => simpa [eqns] using hE
  | cons t T ih =>
    simp only [checkTable, Bool.and_eq_true] at h
    have ht : Derivable Γ (FreeMonoid.ofList t.lhs) (FreeMonoid.ofList t.rhs) := by
      have h1 := h.1
      unfold Entry.check at h1
      split at h1
      · exact rrun_sound hinv hE (by simpa using h1)
      · exact run_sound hE (by simpa using h1)
    have hE' : Valid Γ (E ++ [(t.lhs, t.rhs)]) :=
      hE.append (by intro e he; simp at he; subst he; exact ht)
    have := ih hE' h.2
    simpa [eqns] using this

/-- Check entries with plain steps against a fixed list of equations (the
entries do not use one another). -/
def checkFlat (E : List (Eqn α)) (T : List (Entry α)) : Bool :=
  T.all fun t => !t.rot && t.check E

theorem checkFlat_valid {E : List (Eqn α)} (hE : Valid Γ E) {T : List (Entry α)}
    (h : checkFlat E T = true) : Valid Γ (eqns T) := by
  intro e he
  simp only [eqns, List.mem_map] at he
  obtain ⟨t, ht, rfl⟩ := he
  have h1 := List.all_eq_true.1 h t ht
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
  obtain ⟨hr, h1⟩ := h1
  unfold Entry.check at h1
  rw [if_neg (by simp [hr])] at h1
  exact run_sound hE (by simpa using h1)

/-- The same for tables with plain steps only, which need no involutions. -/
def checkPlain (E : List (Eqn α)) : List (Entry α) → Bool
  | [] => true
  | t :: T => (!t.rot && t.check E) && checkPlain (E ++ [(t.lhs, t.rhs)]) T

theorem checkPlain_valid {E : List (Eqn α)} (hE : Valid Γ E) {T : List (Entry α)}
    (h : checkPlain E T = true) : Valid Γ (E ++ eqns T) := by
  induction T generalizing E with
  | nil => simpa [eqns] using hE
  | cons t T ih =>
    simp only [checkPlain, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hr, h1⟩, h2⟩ := h
    have ht : Derivable Γ (FreeMonoid.ofList t.lhs) (FreeMonoid.ofList t.rhs) := by
      unfold Entry.check at h1
      rw [if_neg (by simp [hr])] at h1
      exact run_sound hE (by simpa using h1)
    have hE' : Valid Γ (E ++ [(t.lhs, t.rhs)]) :=
      hE.append (by intro e he; simp at he; subst he; exact ht)
    have := ih hE' h2
    simpa [eqns] using this


/-! ## Replay on codes

The kernel pays for every unfolding and almost nothing for arithmetic on
literals (GMP), so the tables are replayed on words coded as numbers (as
`CliffordT2/FastRewrite.lean` does): a word `a₀ a₁ … aₙ₋₁` is
`κ a₀ + 32 κ a₁ + ⋯ + 32ⁿ⁻¹ κ aₙ₋₁` for a coding `κ` of the letters by
`1 … 31` (`enc`).  A plain step is then a few operations on numbers, and a
rotation step a few more (`revN` reverses a code digit by digit).  The
equations are compiled once to the codes and lengths of their sides and of
their relator (`CEqn`), kept most recent first (`nthRev`), and every test is
a `Nat.beq`/`Nat.ble` under `bif`; the loops are explicit `Nat.rec`.  A
letter is *good* when its code is in `1 … 31`; the checker tests every
letter of the table (`goodW`), so that `κ` need only be injective on good
letters (`T i` for large `i` has code `0` in `Macro.lean`).  The soundness
of the replay is proved once (`checkTable'_valid`, `checkFlat'_valid`,
`checkPlain'_valid`), from the arithmetic of the coding. -/

section Codes

omit [DecidableEq α]

variable (κ : α → ℕ)

/-- A letter with a code in `1 … 31`. -/
def Good (a : α) : Prop := 0 < κ a ∧ κ a < 32

/-- Every letter of a word is good. -/
def GoodW (w : List α) : Prop := ∀ a ∈ w, Good κ a

/-- `Good`, decided. -/
def goodB (a : α) : Bool := Nat.blt 0 (κ a) && Nat.blt (κ a) 32

/-- `GoodW`, decided. -/
def goodW (w : List α) : Bool := w.all (goodB κ)

/-- The number coding a word, the first letter as the lowest digit. -/
def enc : List α → ℕ
  | [] => 0
  | a :: w => κ a + 32 * enc w

theorem enc_append (u v : List α) : enc κ (u ++ v) = enc κ u + 32 ^ u.length * enc κ v := by
  induction u with
  | nil => simp [enc]
  | cons a u ih => simp only [List.cons_append, enc, ih, List.length_cons, pow_succ]; ring

variable {κ}

theorem goodB_spec {a : α} (h : goodB κ a = true) : Good κ a := by
  simp only [goodB, Bool.and_eq_true, Nat.blt_eq] at h
  exact h

theorem goodW_spec {w : List α} (h : goodW κ w = true) : GoodW κ w :=
  fun a ha => goodB_spec (List.all_eq_true.1 h a ha)

theorem GoodW.append {u v : List α} (hu : GoodW κ u) (hv : GoodW κ v) : GoodW κ (u ++ v) := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  exacts [hu a h, hv a h]

theorem GoodW.take {w : List α} (hw : GoodW κ w) (p : ℕ) : GoodW κ (w.take p) :=
  fun a ha => hw a (List.mem_of_mem_take ha)

theorem GoodW.drop {w : List α} (hw : GoodW κ w) (p : ℕ) : GoodW κ (w.drop p) :=
  fun a ha => hw a (List.mem_of_mem_drop ha)

theorem GoodW.reverse {w : List α} (hw : GoodW κ w) : GoodW κ w.reverse :=
  fun a ha => hw a (List.mem_reverse.1 ha)

theorem enc_lt {w : List α} (hw : GoodW κ w) : enc κ w < 32 ^ w.length := by
  induction w with
  | nil => simp [enc]
  | cons a w ih =>
    simp only [enc, List.length_cons, pow_succ]
    have h1 := (hw a (by simp)).2
    have h2 := ih (fun b hb => hw b (by simp [hb]))
    nlinarith

theorem enc_take_drop {w : List α} (hw : GoodW κ w) (p : ℕ) :
    enc κ w % 32 ^ p = enc κ (w.take p) ∧ enc κ w / 32 ^ p = enc κ (w.drop p) := by
  by_cases hp : p ≤ w.length
  · have e := enc_append κ (w.take p) (w.drop p)
    rw [List.take_append_drop, List.length_take_of_le hp] at e
    have hlt := enc_lt (GoodW.take hw p)
    rw [List.length_take_of_le hp] at hlt
    have hpos : 0 < 32 ^ p := by positivity
    constructor
    · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    · rw [e, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, zero_add]
  · rw [not_le] at hp
    have hlt := enc_lt hw
    have : 32 ^ w.length ≤ 32 ^ p := Nat.pow_le_pow_right (by norm_num) hp.le
    rw [List.take_of_length_le hp.le, List.drop_of_length_le hp.le]
    have h' : enc κ w < 32 ^ p := lt_of_lt_of_le hlt this
    exact ⟨Nat.mod_eq_of_lt h', by simp [enc, Nat.div_eq_of_lt h']⟩

/-- `κ` is injective on good letters: two good words with the same code are
equal. -/
theorem enc_injective_good (hinj : ∀ a b, Good κ a → κ a = κ b → a = b) {u v : List α}
    (hu : GoodW κ u) (hv : GoodW κ v) (h : enc κ u = enc κ v) : u = v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => rfl
    | cons b v => simp only [enc] at h; have := (hv b (by simp)).1; omega
  | cons a u ih =>
    cases v with
    | nil => simp only [enc] at h; have := (hu a (by simp)).1; omega
    | cons b v =>
      simp only [enc] at h
      have ha := (hu a (by simp)).2
      have hb := (hv b (by simp)).2
      have h1 : κ a = κ b := by omega
      have h2 : enc κ u = enc κ v := by omega
      rw [hinj a b (hu a (by simp)) h1,
        ih (fun x hx => hu x (by simp [hx])) (fun x hx => hv x (by simp [hx])) h2]

theorem length_le_of_pow {w : List α} (hw : GoodW κ w) {p : ℕ}
    (h : p = 0 ∨ 32 ^ p ≤ 32 * enc κ w) : p ≤ w.length := by
  rcases h with h | h
  · omega
  · by_contra hp
    rw [not_le] at hp
    have hlt := enc_lt hw
    have : 32 ^ (w.length + 1) ≤ 32 ^ p := Nat.pow_le_pow_right (by norm_num) hp
    rw [pow_succ] at this
    omega

/-- The code of the reverse of the `n` lowest digits of `c`, before `acc`. -/
def revN (n : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih c acc => ih (c / 32) (acc * 32 + c % 32)) n

theorem revN_enc {w : List α} (hw : GoodW κ w) (acc : ℕ) :
    revN w.length (enc κ w) acc = enc κ w.reverse + 32 ^ w.length * acc := by
  induction w generalizing acc with
  | nil => simp [revN, enc]
  | cons a w ih =>
    have ha := hw a (by simp)
    have hw' : GoodW κ w := fun x hx => hw x (by simp [hx])
    show revN w.length ((κ a + 32 * enc κ w) / 32) (acc * 32 + (κ a + 32 * enc κ w) % 32) = _
    have e1 : (κ a + 32 * enc κ w) / 32 = enc κ w := by
      rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt ha.2, zero_add]
    have e2 : (κ a + 32 * enc κ w) % 32 = κ a := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha.2]
    rw [e1, e2, ih hw', List.reverse_cons, enc_append, List.length_reverse, List.length_cons,
      pow_succ]
    simp only [enc]
    ring

/-! ### Compiled equations and steps -/

/-- A compiled equation: the codes and lengths of its sides, and the codes
of its relator and of the reverse of its relator, with their length. -/
structure CEqn where
  /-- The code of the left side. -/
  lc : ℕ
  /-- The length of the left side. -/
  ll : ℕ
  /-- The code of the right side. -/
  rc : ℕ
  /-- The length of the right side. -/
  rl : ℕ
  /-- The code of the relator `l · rev r`. -/
  ρ : ℕ
  /-- The code of the reverse of the relator. -/
  ρr : ℕ
  /-- The length of the relator. -/
  n : ℕ

variable (κ)

/-- An equation compiled. -/
def compile (e : Eqn α) : CEqn :=
  ⟨enc κ e.1, e.1.length, enc κ e.2, e.2.length, enc κ (relator e), enc κ (relator e).reverse,
    (relator e).length⟩

/-- The equations of a table compiled, the last one first. -/
def compileAll (E : List (Eqn α)) : List CEqn := (E.map (compile κ)).reverse

variable {κ}

/-- `tbl[i]?` by primitive recursion. -/
def nthC (tbl : List CEqn) : ℕ → Option CEqn :=
  List.rec (motive := fun _ => ℕ → Option CEqn) (fun _ => none)
    (fun a _ ih i => Nat.rec (motive := fun _ => Option CEqn) (some a) (fun i' _ => ih i') i) tbl

theorem nthC_eq (tbl : List CEqn) (i : ℕ) : nthC tbl i = tbl[i]? := by
  induction tbl generalizing i with
  | nil => cases i <;> rfl
  | cons a tbl ih => cases i with
    | zero => rfl
    | succ i => exact ih i

/-- Equation `k` of a table of `len` equations kept last first. -/
def nthRev (C : List CEqn) (len k : ℕ) : Option CEqn :=
  bif Nat.blt k len then nthC C (len - 1 - k) else none

theorem nthRev_spec {E : List (Eqn α)} {k : ℕ} {c : CEqn}
    (h : nthRev (compileAll κ E) E.length k = some c) :
    ∃ e, E[k]? = some e ∧ compile κ e = c := by
  unfold nthRev at h
  cases hk : Nat.blt k E.length <;> rw [hk] at h
  · simp at h
  · have hk' : k < E.length := Nat.blt_eq.mp hk
    simp only [cond_true, nthC_eq, compileAll] at h
    rw [List.getElem?_reverse (by simp; omega)] at h
    simp only [List.length_map] at h
    rw [show E.length - 1 - (E.length - 1 - k) = k by omega, List.getElem?_map] at h
    cases he : E[k]? with
    | none => rw [he] at h; simp at h
    | some e => rw [he] at h; exact ⟨e, rfl, Option.some.inj h⟩

/-- Replace, at position `p`, the factor with code `lc` and length `ll` by
the one with code `rc` and length `rl`. -/
def replaceB (lc ll rc rl p c : ℕ) : Option ℕ :=
  bif (p.beq 0 || Nat.ble (32 ^ p) (32 * c)) && Nat.beq (c / 32 ^ p % 32 ^ ll) lc then
    some (c % 32 ^ p + 32 ^ p * (rc + 32 ^ rl * (c / 32 ^ p / 32 ^ ll)))
  else none

theorem replaceB_sound (hinj : ∀ a b, Good κ a → κ a = κ b → a = b) {l r w : List α}
    (hl : GoodW κ l) (hr : GoodW κ r) (hw : GoodW κ w) {p c' : ℕ}
    (hlr : Derivable Γ (FreeMonoid.ofList l) (FreeMonoid.ofList r))
    (h : replaceB (enc κ l) l.length (enc κ r) r.length p (enc κ w) = some c') :
    ∃ w', c' = enc κ w' ∧ GoodW κ w' ∧
      Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  unfold replaceB at h
  cases hc : ((p.beq 0 || Nat.ble (32 ^ p) (32 * enc κ w)) &&
      Nat.beq (enc κ w / 32 ^ p % 32 ^ l.length) (enc κ l)) <;> rw [hc] at h
  · simp at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq] at hc
  obtain ⟨hp, hm⟩ := hc
  simp only [cond_true, Option.some.injEq] at h
  have hpw := length_le_of_pow hw hp
  obtain ⟨hmod, hdiv⟩ := enc_take_drop hw p
  obtain ⟨hmod2, hdiv2⟩ := enc_take_drop (GoodW.drop hw p) l.length
  rw [hdiv, hmod2] at hm
  have htake : (w.drop p).take l.length = l :=
    enc_injective_good hinj (GoodW.take (GoodW.drop hw p) _) hl hm
  have hw' : w = w.take p ++ l ++ (w.drop p).drop l.length := by
    conv_lhs => rw [← List.take_append_drop p w, ← List.take_append_drop l.length (w.drop p)]
    rw [htake, List.append_assoc]
  refine ⟨w.take p ++ r ++ (w.drop p).drop l.length, ?_, ?_, ?_⟩
  · rw [← h, hmod, hdiv, hdiv2, enc_append, enc_append, List.length_append,
      List.length_take_of_le hpw, pow_add]
    ring
  · exact GoodW.append (GoodW.append (GoodW.take hw p) hr) (GoodW.drop (GoodW.drop hw p) _)
  · have := derivable_middle hlr (w.take p) ((w.drop p).drop l.length)
    rwa [← hw'] at this

/-- A plain step `(i, k, d)` packed as `2 (4096 i + k) + d`, on codes. -/
def stepC (C : List CEqn) (len c s : ℕ) : Option ℕ :=
  match nthRev C len (s / 2 % 4096) with
  | none => none
  | some e =>
    bif (s % 2).beq 1 then replaceB e.lc e.ll e.rc e.rl (s / 2 / 4096) c
    else replaceB e.rc e.rl e.lc e.ll (s / 2 / 4096) c

/-- Replay `n` packed plain steps on codes. -/
def runC (C : List CEqn) (len n : ℕ) : ℕ → ℕ → Option ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Option ℕ) (fun _ c => some c)
    (fun _ ih code c =>
      match stepC C len c (code % 33554432) with
      | some c' => ih (code / 33554432) c'
      | none => none) n

/-- The rule cut from a relator, on codes: `b` the code of the relator or
of its reverse, `m` its length. -/
def cutC (b m rot cut : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let r := b / 32 ^ rot + 32 ^ (m - rot) * (b % 32 ^ rot)
  (r % 32 ^ cut, bif Nat.ble cut m then cut else m, revN (m - cut) (r / 32 ^ cut) 0, m - cut)

/-- A rotation step `(i, k, rot, cut, rv)`, packed as in `decodeRot`, on
codes. -/
def rstepC (C : List CEqn) (len c s : ℕ) : Option ℕ :=
  match nthRev C len (s / 524288 % 16384) with
  | none => none
  | some e =>
    match cutC (bif (s % 2).beq 1 then e.ρr else e.ρ) e.n (s / 1024 % 512) (s / 2 % 512) with
    | (lc, ll, rc, rl) => replaceB lc ll rc rl (s / 8589934592) c

/-- Replay `n` packed rotation steps on codes. -/
def rrunC (C : List CEqn) (len n : ℕ) : ℕ → ℕ → Option ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Option ℕ) (fun _ c => some c)
    (fun _ ih code c =>
      match rstepC C len c (code % 17592186044416) with
      | some c' => ih (code / 17592186044416) c'
      | none => none) n

variable (κ)

/-- Every equation of a list has good sides. -/
def GoodE (E : List (Eqn α)) : Prop := ∀ e ∈ E, GoodW κ e.1 ∧ GoodW κ e.2

variable {κ}

theorem GoodE.get {E : List (Eqn α)} (hE : GoodE κ E) {k : ℕ} {e : Eqn α} (h : E[k]? = some e) :
    GoodW κ e.1 ∧ GoodW κ e.2 :=
  hE e (List.mem_of_getElem? h)

theorem GoodE.append {E F : List (Eqn α)} (hE : GoodE κ E) (hF : GoodE κ F) :
    GoodE κ (E ++ F) := by
  intro e he
  rcases List.mem_append.1 he with h | h
  exacts [hE e h, hF e h]

theorem GoodE.relator {E : List (Eqn α)} (hE : GoodE κ E) {k : ℕ} {e : Eqn α}
    (h : E[k]? = some e) : GoodW κ (relator e) :=
  GoodW.append (hE.get h).1 (GoodW.reverse (hE.get h).2)

theorem stepC_sound (hinj : ∀ a b, Good κ a → κ a = κ b → a = b) {E : List (Eqn α)}
    (hE : Valid Γ E) (hEg : GoodE κ E) {w : List α} (hw : GoodW κ w) {s c' : ℕ}
    (h : stepC (compileAll κ E) E.length (enc κ w) s = some c') :
    ∃ w', c' = enc κ w' ∧ GoodW κ w' ∧
      Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  unfold stepC at h
  split at h
  · simp at h
  · rename_i e hx
    obtain ⟨e', he', rfl⟩ := nthRev_spec hx
    have hd := hE.get he'
    have hg := hEg.get he'
    simp only [compile] at h
    cases hs : (s % 2).beq 1 <;> rw [hs] at h
    · exact replaceB_sound hinj hg.2 hg.1 hw hd.symm h
    · exact replaceB_sound hinj hg.1 hg.2 hw hd h

theorem runC_sound (hinj : ∀ a b, Good κ a → κ a = κ b → a = b) {E : List (Eqn α)}
    (hE : Valid Γ E) (hEg : GoodE κ E) (n : ℕ) :
    ∀ (code : ℕ) (w : List α) (c' : ℕ), GoodW κ w →
      runC (compileAll κ E) E.length n code (enc κ w) = some c' →
      ∃ w', c' = enc κ w' ∧ GoodW κ w' ∧
        Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  induction n with
  | zero =>
    intro code w c' hw h
    simp only [runC, Nat.rec_zero, Option.some.injEq] at h
    exact ⟨w, h.symm, hw, Derivable.refl _⟩
  | succ n ih =>
    intro code w c' hw h
    simp only [runC] at h
    split at h
    · rename_i c₁ h₁
      obtain ⟨w₁, rfl, hw₁, d₁⟩ := stepC_sound hinj hE hEg hw h₁
      obtain ⟨w₂, rfl, hw₂, d₂⟩ := ih (code / 33554432) w₁ c' hw₁ h
      exact ⟨w₂, rfl, hw₂, d₁.trans d₂⟩
    · simp at h

/-- The sides of a rule cut from a good relator are good. -/
theorem cutRule_good {ρ : List α} (hρ : GoodW κ ρ) (rot cut : ℕ) (rv : Bool) :
    GoodW κ (cutRule ρ rot cut rv).1 ∧ GoodW κ (cutRule ρ rot cut rv).2 := by
  have hb : GoodW κ (if rv then ρ.reverse else ρ) := by
    cases rv
    · simpa using hρ
    · simpa using GoodW.reverse hρ
  have hr := GoodW.append (GoodW.drop hb rot) (GoodW.take hb rot)
  exact ⟨GoodW.take hr cut, GoodW.reverse (GoodW.drop hr cut)⟩

/-- `cutC` on the code of a relator is `cutRule` on the relator. -/
theorem cutC_eq {ρ : List α} (hρ : GoodW κ ρ) (rot cut : ℕ) (rv : Bool) :
    cutC (bif rv then enc κ ρ.reverse else enc κ ρ) ρ.length rot cut =
      (enc κ (cutRule ρ rot cut rv).1, (cutRule ρ rot cut rv).1.length,
        enc κ (cutRule ρ rot cut rv).2, (cutRule ρ rot cut rv).2.length) := by
  simp only [cutRule]
  have hb : GoodW κ (if rv then ρ.reverse else ρ) := by
    cases rv
    · simpa using hρ
    · simpa using GoodW.reverse hρ
  have eb : (bif rv then enc κ ρ.reverse else enc κ ρ) = enc κ (if rv then ρ.reverse else ρ) := by
    cases rv <;> rfl
  have lb : (if rv then ρ.reverse else ρ).length = ρ.length := by cases rv <;> simp
  rw [eb, ← lb]
  set b := if rv then ρ.reverse else ρ with hbdef
  have hr : GoodW κ (b.drop rot ++ b.take rot) := GoodW.append (GoodW.drop hb rot) (GoodW.take hb rot)
  have er : enc κ (b.drop rot ++ b.take rot) =
      enc κ b / 32 ^ rot + 32 ^ (b.length - rot) * (enc κ b % 32 ^ rot) := by
    rw [enc_append, (enc_take_drop hb rot).1, (enc_take_drop hb rot).2, List.length_drop]
  have lr : (b.drop rot ++ b.take rot).length = b.length := by
    simp only [List.length_append, List.length_drop, List.length_take]; omega
  set r := b.drop rot ++ b.take rot with hrdef
  simp only [cutC]
  rw [← er]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact (enc_take_drop hr cut).1
  · show (bif Nat.ble cut b.length then cut else b.length) = (r.take cut).length
    rw [List.length_take, lr]
    cases h : Nat.ble cut b.length
    · have : ¬ cut ≤ b.length := fun h' => by rw [Nat.ble_eq_true_of_le h'] at h; cases h
      simp [min_eq_right (not_le.1 this).le]
    · simp [min_eq_left (Nat.le_of_ble_eq_true h)]
  · show revN (b.length - cut) (enc κ r / 32 ^ cut) 0 = enc κ (r.drop cut).reverse
    have hd : (r.drop cut).length = r.length - cut := List.length_drop
    rw [(enc_take_drop hr cut).2, ← lr, ← hd, revN_enc (GoodW.drop hr cut) 0, mul_zero, add_zero]
  · show b.length - cut = (r.drop cut).reverse.length
    rw [List.length_reverse, List.length_drop, lr]

theorem rstepC_sound (hinj : ∀ a b, Good κ a → κ a = κ b → a = b)
    (hinv : ∀ x : α, Derivable Γ (FreeMonoid.ofList [x, x]) 1) {E : List (Eqn α)}
    (hE : Valid Γ E) (hEg : GoodE κ E) {w : List α} (hw : GoodW κ w) {s c' : ℕ}
    (h : rstepC (compileAll κ E) E.length (enc κ w) s = some c') :
    ∃ w', c' = enc κ w' ∧ GoodW κ w' ∧
      Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  unfold rstepC at h
  split at h
  · simp at h
  · rename_i e hx
    obtain ⟨e', he', rfl⟩ := nthRev_spec hx
    have hρ := hEg.relator he'
    have hd := cutRule_sound hinv (relator_of hinv (hE.get he')) (s / 1024 % 512) (s / 2 % 512)
      ((s % 2).beq 1)
    have hg := cutRule_good hρ (s / 1024 % 512) (s / 2 % 512) ((s % 2).beq 1)
    simp only [compile] at h
    rw [cutC_eq hρ] at h
    simp only at h
    exact replaceB_sound hinj hg.1 hg.2 hw hd h

theorem rrunC_sound (hinj : ∀ a b, Good κ a → κ a = κ b → a = b)
    (hinv : ∀ x : α, Derivable Γ (FreeMonoid.ofList [x, x]) 1) {E : List (Eqn α)}
    (hE : Valid Γ E) (hEg : GoodE κ E) (n : ℕ) :
    ∀ (code : ℕ) (w : List α) (c' : ℕ), GoodW κ w →
      rrunC (compileAll κ E) E.length n code (enc κ w) = some c' →
      ∃ w', c' = enc κ w' ∧ GoodW κ w' ∧
        Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  induction n with
  | zero =>
    intro code w c' hw h
    simp only [rrunC, Nat.rec_zero, Option.some.injEq] at h
    exact ⟨w, h.symm, hw, Derivable.refl _⟩
  | succ n ih =>
    intro code w c' hw h
    simp only [rrunC] at h
    split at h
    · rename_i c₁ h₁
      obtain ⟨w₁, rfl, hw₁, d₁⟩ := rstepC_sound hinj hinv hE hEg hw h₁
      obtain ⟨w₂, rfl, hw₂, d₂⟩ := ih (code / 17592186044416) w₁ c' hw₁ h
      exact ⟨w₂, rfl, hw₂, d₁.trans d₂⟩
    · simp at h

/-! ### Tables on codes -/

variable (κ)

/-- An entry replayed on codes against a compiled table. -/
def Entry.checkC (C : List CEqn) (len : ℕ) (t : Entry α) : Bool :=
  goodW κ t.lhs && goodW κ t.rhs &&
    match (bif t.rot then rrunC C len t.n t.code (enc κ t.lhs)
      else runC C len t.n t.code (enc κ t.lhs)) with
    | some c => Nat.beq c (enc κ t.rhs)
    | none => false

/-- `checkTable` on codes: the compiled table grows with every entry. -/
def checkTableC (C : List CEqn) (len : ℕ) : List (Entry α) → Bool
  | [] => true
  | t :: T => t.checkC κ C len && checkTableC (compile κ (t.lhs, t.rhs) :: C) (len + 1) T

/-- `checkFlat` on codes. -/
def checkFlatC (C : List CEqn) (len : ℕ) (T : List (Entry α)) : Bool :=
  T.all fun t => !t.rot && t.checkC κ C len

/-- `checkPlain` on codes. -/
def checkPlainC (C : List CEqn) (len : ℕ) : List (Entry α) → Bool
  | [] => true
  | t :: T =>
    (!t.rot && t.checkC κ C len) && checkPlainC (compile κ (t.lhs, t.rhs) :: C) (len + 1) T

/-- `checkTable` on codes, from the equations themselves. -/
def checkTable' (E : List (Eqn α)) (T : List (Entry α)) : Bool :=
  (E.all fun e => goodW κ e.1 && goodW κ e.2) && checkTableC κ (compileAll κ E) E.length T

/-- `checkFlat` on codes, from the equations themselves. -/
def checkFlat' (E : List (Eqn α)) (T : List (Entry α)) : Bool :=
  (E.all fun e => goodW κ e.1 && goodW κ e.2) && checkFlatC κ (compileAll κ E) E.length T

/-- `checkPlain` on codes, from the equations themselves. -/
def checkPlain' (E : List (Eqn α)) (T : List (Entry α)) : Bool :=
  (E.all fun e => goodW κ e.1 && goodW κ e.2) && checkPlainC κ (compileAll κ E) E.length T

variable {κ}

theorem goodE_spec {E : List (Eqn α)} (h : (E.all fun e => goodW κ e.1 && goodW κ e.2) = true) :
    GoodE κ E := by
  intro e he
  have := List.all_eq_true.1 h e he
  simp only [Bool.and_eq_true] at this
  exact ⟨goodW_spec this.1, goodW_spec this.2⟩

theorem compileAll_cons (E : List (Eqn α)) (e : Eqn α) :
    compileAll κ (E ++ [e]) = compile κ e :: compileAll κ E := by
  simp [compileAll]

/-- A checked entry is a derivable good equation.  Rotation steps need
every letter to be an involution; a plain entry does not use `hinv`. -/
theorem Entry.checkC_sound (hinj : ∀ a b, Good κ a → κ a = κ b → a = b) {t : Entry α}
    (hinv : t.rot = true → ∀ x : α, Derivable Γ (FreeMonoid.ofList [x, x]) 1)
    {E : List (Eqn α)} (hE : Valid Γ E) (hEg : GoodE κ E)
    (h : t.checkC κ (compileAll κ E) E.length = true) :
    GoodW κ t.lhs ∧ GoodW κ t.rhs ∧
      Derivable Γ (FreeMonoid.ofList t.lhs) (FreeMonoid.ofList t.rhs) := by
  unfold Entry.checkC at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hl, hr⟩, h⟩ := h
  have hl' := goodW_spec hl
  have hr' := goodW_spec hr
  refine ⟨hl', hr', ?_⟩
  split at h
  · rename_i c hc
    have hc' : c = enc κ t.rhs := Nat.beq_eq.mp h
    subst hc'
    cases hrot : t.rot <;> rw [hrot] at hc
    · obtain ⟨w', hw', hg', d⟩ := runC_sound hinj hE hEg t.n t.code t.lhs _ hl' hc
      rw [← enc_injective_good hinj hr' hg' hw'] at d
      exact d
    · obtain ⟨w', hw', hg', d⟩ := rrunC_sound hinj (hinv hrot) hE hEg t.n t.code t.lhs _ hl' hc
      rw [← enc_injective_good hinj hr' hg' hw'] at d
      exact d
  · cases h

theorem checkTableC_valid (hinj : ∀ a b, Good κ a → κ a = κ b → a = b)
    (hinv : ∀ x : α, Derivable Γ (FreeMonoid.ofList [x, x]) 1) {T : List (Entry α)} :
    ∀ {E : List (Eqn α)}, Valid Γ E → GoodE κ E →
      checkTableC κ (compileAll κ E) E.length T = true → Valid Γ (E ++ eqns T) := by
  induction T with
  | nil => intro E hE _ _; simpa [eqns] using hE
  | cons t T ih =>
    intro E hE hEg h
    simp only [checkTableC, Bool.and_eq_true] at h
    obtain ⟨hl, hr, ht⟩ := Entry.checkC_sound hinj (fun _ => hinv) hE hEg h.1
    have hE' : Valid Γ (E ++ [(t.lhs, t.rhs)]) :=
      hE.append (by intro e he; simp at he; subst he; exact ht)
    have hEg' : GoodE κ (E ++ [(t.lhs, t.rhs)]) :=
      hEg.append (by intro e he; simp at he; subst he; exact ⟨hl, hr⟩)
    have h2 := h.2
    rw [← compileAll_cons, show E.length + 1 = (E ++ [(t.lhs, t.rhs)]).length by simp] at h2
    have := ih hE' hEg' h2
    simpa [eqns] using this

theorem checkPlainC_valid (hinj : ∀ a b, Good κ a → κ a = κ b → a = b) {T : List (Entry α)} :
    ∀ {E : List (Eqn α)}, Valid Γ E → GoodE κ E →
      checkPlainC κ (compileAll κ E) E.length T = true → Valid Γ (E ++ eqns T) := by
  induction T with
  | nil => intro E hE _ _; simpa [eqns] using hE
  | cons t T ih =>
    intro E hE hEg h
    simp only [checkPlainC, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hrot, h1⟩, h2⟩ := h
    obtain ⟨hl, hr, ht⟩ :=
      Entry.checkC_sound hinj (fun h => by rw [hrot] at h; cases h) hE hEg h1
    have hE' : Valid Γ (E ++ [(t.lhs, t.rhs)]) :=
      hE.append (by intro e he; simp at he; subst he; exact ht)
    have hEg' : GoodE κ (E ++ [(t.lhs, t.rhs)]) :=
      hEg.append (by intro e he; simp at he; subst he; exact ⟨hl, hr⟩)
    rw [← compileAll_cons, show E.length + 1 = (E ++ [(t.lhs, t.rhs)]).length by simp] at h2
    have := ih hE' hEg' h2
    simpa [eqns] using this

theorem checkFlatC_valid (hinj : ∀ a b, Good κ a → κ a = κ b → a = b) {E : List (Eqn α)}
    (hE : Valid Γ E) (hEg : GoodE κ E) {T : List (Entry α)}
    (h : checkFlatC κ (compileAll κ E) E.length T = true) : Valid Γ (eqns T) := by
  intro e he
  simp only [eqns, List.mem_map] at he
  obtain ⟨t, ht, rfl⟩ := he
  have h1 := List.all_eq_true.1 h t ht
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
  exact (Entry.checkC_sound hinj (fun h => by rw [h1.1] at h; cases h) hE hEg h1.2).2.2

/-- A table checked on codes over a valid base is valid. -/
theorem checkTable'_valid (hinj : ∀ a b, Good κ a → κ a = κ b → a = b) {E : List (Eqn α)}
    (hE : Valid Γ E) (hinv : ∀ x : α, Derivable Γ (FreeMonoid.ofList [x, x]) 1)
    {T : List (Entry α)} (h : checkTable' κ E T = true) : Valid Γ (E ++ eqns T) := by
  simp only [checkTable', Bool.and_eq_true] at h
  exact checkTableC_valid hinj hinv hE (goodE_spec h.1) h.2

/-- Entries with plain steps checked on codes against a valid list. -/
theorem checkFlat'_valid (hinj : ∀ a b, Good κ a → κ a = κ b → a = b) {E : List (Eqn α)}
    (hE : Valid Γ E) {T : List (Entry α)} (h : checkFlat' κ E T = true) : Valid Γ (eqns T) := by
  simp only [checkFlat', Bool.and_eq_true] at h
  exact checkFlatC_valid hinj hE (goodE_spec h.1) h.2

/-- A table with plain steps checked on codes over a valid base is valid. -/
theorem checkPlain'_valid (hinj : ∀ a b, Good κ a → κ a = κ b → a = b) {E : List (Eqn α)}
    (hE : Valid Γ E) {T : List (Entry α)} (h : checkPlain' κ E T = true) :
    Valid Γ (E ++ eqns T) := by
  simp only [checkPlain', Bool.and_eq_true] at h
  exact checkPlainC_valid hinj hE (goodE_spec h.1) h.2

end Codes

end QCert.ToffoliHadamard.Engine
