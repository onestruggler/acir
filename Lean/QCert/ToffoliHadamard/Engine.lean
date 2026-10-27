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

end QCert.ToffoliHadamard.Engine
