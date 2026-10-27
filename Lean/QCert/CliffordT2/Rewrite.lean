/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Checked rewriting

General tools for proving equations in a theory `Γ` by computation:

* a `Rule Γ` is an equation between two lists of letters together with
  its derivation;
* `runSteps rules w steps` replays a list of rewriting steps
  `(position, rule, direction)` on `w`; when it ends in `v`, `w` and `v`
  are derivably equal (`derivable_of_runSteps`).  Rewriting certificates
  found outside Lean are checked this way by `decide +kernel`;
* `normalize rules n w` rewrites `w` with the rules, left to right, at the
  leftmost position, at most `n` times; two words with the same result are
  derivably equal (`derivable_of_normalize`).
-/
import QCert.CliffordT2.Derivation

namespace QCert

universe u

variable {α : Type u} [DecidableEq α]

/-- An equation `lhs = rhs` between lists of letters, with a derivation. -/
structure Rule (Γ : WRel α) where
  lhs : List α
  rhs : List α
  sound : Derivable Γ (FreeMonoid.ofList lhs) (FreeMonoid.ofList rhs)

/-- A rule from an equation between words. -/
def Rule.ofDerivable {Γ : WRel α} (w v : Word α) (h : Derivable Γ w v) : Rule Γ :=
  ⟨FreeMonoid.toList w, FreeMonoid.toList v, by simpa using h⟩

/-- The rule read from right to left. -/
def Rule.symm {Γ : WRel α} (r : Rule Γ) : Rule Γ := ⟨r.rhs, r.lhs, r.sound.symm⟩

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

variable {Γ : WRel α}

omit [DecidableEq α] in
theorem derivable_ofList_append_middle {l r : List α}
    (h : Derivable Γ (FreeMonoid.ofList l) (FreeMonoid.ofList r)) (p q : List α) :
    Derivable Γ (FreeMonoid.ofList (p ++ l ++ q)) (FreeMonoid.ofList (p ++ r ++ q)) := by
  simp only [FreeMonoid.ofList_append]
  exact (h.mul_left _).mul_right _

theorem derivable_of_replaceAt (ρ : Rule Γ) {i : ℕ} {w w' : List α}
    (h : replaceAt ρ.lhs ρ.rhs i w = some w') :
    Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  obtain ⟨p, q, rfl, rfl⟩ := replaceAt_eq h
  exact derivable_ofList_append_middle ρ.sound p q

/-- One rewriting step `(i, k, d)`: rule `k` at position `i`, left to right
when `d` is true and right to left otherwise. -/
def applyStep (rules : List (Rule Γ)) (w : List α) : ℕ × ℕ × Bool → Option (List α)
  | (i, k, d) =>
    match rules[k]? with
    | none => none
    | some ρ => if d then replaceAt ρ.lhs ρ.rhs i w else replaceAt ρ.rhs ρ.lhs i w

theorem derivable_of_applyStep (rules : List (Rule Γ)) {w w' : List α} {s : ℕ × ℕ × Bool}
    (h : applyStep rules w s = some w') :
    Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  obtain ⟨i, k, d⟩ := s
  simp only [applyStep] at h
  split at h
  · simp at h
  · rename_i ρ _
    cases d
    · exact derivable_of_replaceAt ρ.symm h
    · exact derivable_of_replaceAt ρ h

/-- Replay a list of steps. -/
def runSteps (rules : List (Rule Γ)) : List α → List (ℕ × ℕ × Bool) → Option (List α)
  | w, [] => some w
  | w, s :: ss => (applyStep rules w s).bind fun w' => runSteps rules w' ss

theorem derivable_of_runSteps' (rules : List (Rule Γ)) {w v : List α}
    {ss : List (ℕ × ℕ × Bool)} (h : runSteps rules w ss = some v) :
    Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList v) := by
  induction ss generalizing w with
  | nil => simp only [runSteps, Option.some.injEq] at h; subst h; rfl
  | cons s ss ih =>
    simp only [runSteps, Option.bind_eq_some_iff] at h
    obtain ⟨w', h1, h2⟩ := h
    exact (derivable_of_applyStep rules h1).trans (ih h2)

/-- A certificate: replaying the steps on `w` gives `v`. -/
theorem derivable_of_runSteps (rules : List (Rule Γ)) (w v : Word α)
    (ss : List (ℕ × ℕ × Bool))
    (h : runSteps rules (FreeMonoid.toList w) ss = some (FreeMonoid.toList v)) :
    Derivable Γ w v := by
  simpa using derivable_of_runSteps' rules h

/-! ### Normalization -/

/-- The first rule whose left side is a prefix of `w`, applied there. -/
def rewriteHead : List (Rule Γ) → List α → Option (List α)
  | [], _ => none
  | ρ :: rules, w =>
    match dropPrefix ρ.lhs w with
    | some q => some (ρ.rhs ++ q)
    | none => rewriteHead rules w

/-- One rewriting step at the leftmost position where a rule applies. -/
def rewrite1 (rules : List (Rule Γ)) : List α → Option (List α)
  | [] => none
  | a :: w =>
    match rewriteHead rules (a :: w) with
    | some w' => some w'
    | none => (rewrite1 rules w).map (a :: ·)

/-- At most `n` rewriting steps. -/
def normalize (rules : List (Rule Γ)) : ℕ → List α → List α
  | 0, w => w
  | n + 1, w =>
    match rewrite1 rules w with
    | some w' => normalize rules n w'
    | none => w

theorem derivable_rewriteHead (rules : List (Rule Γ)) {w w' : List α}
    (h : rewriteHead rules w = some w') :
    Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  induction rules with
  | nil => simp [rewriteHead] at h
  | cons ρ rules ih =>
    simp only [rewriteHead] at h
    split at h
    · rename_i q hq
      simp only [Option.some.injEq] at h
      subst h
      have := derivable_ofList_append_middle ρ.sound [] q
      simpa [dropPrefix_eq hq] using this
    · exact ih h

theorem derivable_rewrite1 (rules : List (Rule Γ)) {w w' : List α}
    (h : rewrite1 rules w = some w') :
    Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  induction w generalizing w' with
  | nil => simp [rewrite1] at h
  | cons a w ih =>
    simp only [rewrite1] at h
    split at h
    · rename_i w'' hw''
      simp only [Option.some.injEq] at h
      subst h
      exact derivable_rewriteHead rules hw''
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      have := (ih hv).mul_left (FreeMonoid.of a)
      simpa [FreeMonoid.ofList_cons] using this

theorem derivable_normalize (rules : List (Rule Γ)) (n : ℕ) (w : List α) :
    Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList (normalize rules n w)) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    simp only [normalize]
    split
    · rename_i w' hw'
      exact (derivable_rewrite1 rules hw').trans (ih w')
    · rfl

/-- Two words with the same normal form are derivably equal. -/
theorem derivable_of_normalize (rules : List (Rule Γ)) (n : ℕ) (w v : Word α)
    (h : normalize rules n (FreeMonoid.toList w) = normalize rules n (FreeMonoid.toList v)) :
    Derivable Γ w v := by
  have h1 := derivable_normalize rules n (FreeMonoid.toList w)
  have h2 := derivable_normalize rules n (FreeMonoid.toList v)
  rw [h] at h1
  simpa using h1.trans h2.symm

end QCert
