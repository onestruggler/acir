/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A checker for derivations on concrete indices

A derivation in the theory of Figure 6 between two words on concrete
indices (`Fin m` with `m` a numeral) is given as a list of steps, each the
rewriting of a segment of the current word by an instance of a relation of
Figure 6 (named by its label and its indices, `Step.rel`), or by an already
derived equation (`Step.lem`), at a position and in a direction.
`runSteps` performs the rewriting and `derive_of` turns a successful run
into a derivation, so that a derivation found by a search is checked by
evaluation (`decide +kernel`).  Derivations at `Fin m` are moved to any
increasing indices by `Derivable.map` (`Embed.lean`).
-/
import QCert.HadamardPi.Embed

namespace QCert.HadamardPi

open FreeMonoid

variable {m : ℕ}

instance : DecidableEq (Gen m) := fun g g' =>
  match g, g' with
  | .Z a, .Z a' => if h : a = a' then isTrue (by subst h; rfl) else isFalse (by
      intro e; cases e; exact h rfl)
  | .X a b _, .X a' b' _ => if h : a = a' ∧ b = b' then isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
      else isFalse (by intro e; cases e; exact h ⟨rfl, rfl⟩)
  | .H a b _, .H a' b' _ => if h : a = a' ∧ b = b' then isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
      else isFalse (by intro e; cases e; exact h ⟨rfl, rfl⟩)
  | .Z _, .X _ _ _ => isFalse (by intro e; cases e)
  | .Z _, .H _ _ _ => isFalse (by intro e; cases e)
  | .X _ _ _, .Z _ => isFalse (by intro e; cases e)
  | .X _ _ _, .H _ _ _ => isFalse (by intro e; cases e)
  | .H _ _ _, .Z _ => isFalse (by intro e; cases e)
  | .H _ _ _, .X _ _ _ => isFalse (by intro e; cases e)

/-- Letters on concrete indices, the order proved by `decide`. -/
abbrev zL (a : Fin m) : Gen m := .Z a
/-- `X_[a,b]` on concrete indices. -/
abbrev xL (a b : Fin m) (h : a < b := by decide) : Gen m := .X a b h
/-- `H_[a,b]` on concrete indices. -/
abbrev hL (a b : Fin m) (h : a < b := by decide) : Gen m := .H a b h

/-- The labels of Figure 6. -/
inductive Tag
  | a1 | a2 | a3 | b1 | b2 | b3 | b4 | b5 | b6 | c1 | c2 | c3 | c4 | c5 | d1 | d2 | d3 | d4

/-- The instance of a relation at the given indices (in the order
`a, b, c, …` of the figure), if its side conditions hold. -/
def ruleG : Tag → List (Fin m) → Option (List (Gen m) × List (Gen m))
  | .a1, [a] => some ([.Z a, .Z a], [])
  | .a2, [a, b] => if h : a < b then some ([.X a b h, .X a b h], []) else none
  | .a3, [a, b] => if h : a < b then some ([.H a b h, .H a b h], []) else none
  | .b1, [a, b] => if a ≠ b then some ([.Z a, .Z b], [.Z b, .Z a]) else none
  | .b2, [a, b, c] => if h : b < c ∧ a ≠ b ∧ a ≠ c then
      some ([.Z a, .X b c h.1], [.X b c h.1, .Z a]) else none
  | .b3, [a, b, c, d] => if h : a < b ∧ c < d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d then
      some ([.X a b h.1, .X c d h.2.1], [.X c d h.2.1, .X a b h.1]) else none
  | .b4, [a, b, c] => if h : b < c ∧ a ≠ b ∧ a ≠ c then
      some ([.Z a, .H b c h.1], [.H b c h.1, .Z a]) else none
  | .b5, [a, b, c, d] => if h : a < b ∧ c < d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d then
      some ([.X a b h.1, .H c d h.2.1], [.H c d h.2.1, .X a b h.1]) else none
  | .b6, [a, b, c, d] => if h : a < b ∧ c < d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d then
      some ([.H a b h.1, .H c d h.2.1], [.H c d h.2.1, .H a b h.1]) else none
  | .c1, [a, b] => if h : a < b then some ([.Z a, .X a b h], [.X a b h, .Z b]) else none
  | .c2, [a, b, c] => if h : a < b ∧ b < c then
      some ([.X b c h.2, .X a b h.1], [.X a b h.1, .X a c (h.1.trans h.2)]) else none
  | .c3, [a, b, c] => if h : a < b ∧ b < c then
      some ([.X a c (h.1.trans h.2), .X b c h.2], [.X b c h.2, .X a b h.1]) else none
  | .c4, [a, b, c] => if h : a < b ∧ b < c then
      some ([.H b c h.2, .X a b h.1], [.X a b h.1, .H a c (h.1.trans h.2)]) else none
  | .c5, [a, b, c] => if h : a < b ∧ b < c then
      some ([.H a c (h.1.trans h.2), .X b c h.2], [.X b c h.2, .H a b h.1]) else none
  | .d1, [a, b] => if h : a < b then
      some ([.Z a, .Z b, .H a b h], [.H a b h, .Z a, .Z b]) else none
  | .d2, [a, b] => if h : a < b then some ([.Z b, .H a b h], [.H a b h, .X a b h]) else none
  | .d3, [a, b, c, d] => if h : a < b ∧ c < d ∧ a < c ∧ b < d ∧ b ≠ c then
      some ((List.replicate 4 [.H c d h.2.1, .H a c h.2.2.1, .H b d h.2.2.2.1]).flatten,
        [.H a b h.1, .H c d h.2.1]) else none
  | .d4, [a, b, c, d, e, f] => if h : a < c ∧ b < d ∧ a < b ∧ c < e ∧ d < f ∧ e < f ∧
      b ≠ c ∧ b ≠ e ∧ c ≠ d ∧ d ≠ e then
      some ((List.replicate 3 [.H a c h.1, .H b d h.2.1, .H a b h.2.2.1, .H a c h.1, .H b d h.2.1,
          .X c e h.2.2.2.1, .X d f h.2.2.2.2.1]).flatten,
        [.H c e h.2.2.2.1, .H d f h.2.2.2.2.1, .H e f h.2.2.2.2.2.1, .H c e h.2.2.2.1,
          .H d f h.2.2.2.2.1, .X c e h.2.2.2.1, .X d f h.2.2.2.2.1]) else none
  | _, _ => none

theorem ruleG_sound {t : Tag} {ix : List (Fin m)} {P Q : List (Gen m)}
    (h : ruleG t ix = some (P, Q)) : Derivable Fig6 (ofList P) (ofList Q) := by
  unfold ruleG at h
  split at h <;> (try split_ifs at h with hc) <;> (try simp only [Option.some.injEq,
    Prod.mk.injEq, reduceCtorEq] at h) <;> (try obtain ⟨rfl, rfl⟩ := h)
  · exact Derivable.of (Fig6.a1 _)
  · exact Derivable.of (Fig6.a2 hc)
  · exact Derivable.of (Fig6.a3 hc)
  · exact Derivable.of (Fig6.b1 hc)
  · exact Derivable.of (Fig6.b2 hc.1 hc.2.1 hc.2.2)
  · exact Derivable.of (Fig6.b3 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2)
  · exact Derivable.of (Fig6.b4 hc.1 hc.2.1 hc.2.2)
  · exact Derivable.of (Fig6.b5 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2)
  · exact Derivable.of (Fig6.b6 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2)
  · exact Derivable.of (Fig6.c1 hc)
  · exact Derivable.of (Fig6.c2 hc.1 hc.2)
  · exact Derivable.of (Fig6.c3 hc.1 hc.2)
  · exact Derivable.of (Fig6.c4 hc.1 hc.2)
  · exact Derivable.of (Fig6.c5 hc.1 hc.2)
  · exact Derivable.of (Fig6.d1 hc)
  · exact Derivable.of (Fig6.d2 hc)
  · have := Derivable.of (Fig6.d3 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2)
    simpa [pow_succ, ofList_append] using this
  · have := Derivable.of (Fig6.d4 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1
      hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2)
    simpa [pow_succ, ofList_append, mul_assoc] using this

/-- A step: a relation of Figure 6 at given indices, or an already derived
equation, applied at a position, left to right (`true`) or right to left. -/
inductive Step (m : ℕ)
  | rel (t : Tag) (ix : List (Fin m)) (pos : ℕ) (fwd : Bool)
  | lem (P Q : List (Gen m)) (h : Derivable Fig6 (ofList P) (ofList Q)) (pos : ℕ) (fwd : Bool)

/-- The equation a step rewrites by, in its direction. -/
def Step.pair : Step m → Option (List (Gen m) × List (Gen m))
  | .rel t ix _ fwd => (ruleG t ix).map fun p => if fwd then p else p.swap
  | .lem P Q _ _ fwd => some (if fwd then (P, Q) else (Q, P))

def Step.pos : Step m → ℕ
  | .rel _ _ pos _ => pos
  | .lem _ _ _ pos _ => pos

theorem Step.pair_sound {st : Step m} {P Q : List (Gen m)} (h : st.pair = some (P, Q)) :
    Derivable Fig6 (ofList P) (ofList Q) := by
  cases st with
  | rel t ix pos fwd =>
    simp only [Step.pair, Option.map_eq_some_iff] at h
    obtain ⟨⟨P', Q'⟩, h1, h2⟩ := h
    have := ruleG_sound h1
    cases fwd
    · simp only [Bool.false_eq_true, if_false, Prod.swap_prod_mk, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2; exact this.symm
    · simp only [if_true, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2; exact this
  | lem P' Q' hd pos fwd =>
    simp only [Step.pair, Option.some.injEq] at h
    cases fwd
    · simp only [Bool.false_eq_true, if_false, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hd.symm
    · simp only [if_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hd

/-- Rewrite the segment `P` at position `pos` of `w` into `Q`. -/
def rewriteAt (P Q : List (Gen m)) (pos : ℕ) (w : List (Gen m)) : Option (List (Gen m)) :=
  if (w.drop pos).take P.length = P then some (w.take pos ++ Q ++ w.drop (pos + P.length))
  else none

/-- Run a list of steps from a word. -/
def runSteps : List (Step m) → List (Gen m) → Option (List (Gen m))
  | [], w => some w
  | st :: sts, w =>
    match st.pair with
    | some (P, Q) =>
      match rewriteAt P Q st.pos w with
      | some w' => runSteps sts w'
      | none => none
    | none => none

theorem rewriteAt_sound {P Q : List (Gen m)} (hd : Derivable Fig6 (ofList P) (ofList Q))
    {pos : ℕ} {w w' : List (Gen m)} (h : rewriteAt P Q pos w = some w') :
    Derivable Fig6 (ofList w) (ofList w') := by
  unfold rewriteAt at h
  split_ifs at h with hm
  cases h
  exact rw_at w pos hd hm

theorem runSteps_sound : ∀ (sts : List (Step m)) {w w' : List (Gen m)},
    runSteps sts w = some w' → Derivable Fig6 (ofList w) (ofList w')
  | [], w, w', h => by
    simp only [runSteps, Option.some.injEq] at h; subst h; exact Derivable.refl _
  | st :: sts, w, w', h => by
    simp only [runSteps] at h
    split at h
    · rename_i P Q hp
      split at h
      · rename_i w1 hw1
        exact (rewriteAt_sound (Step.pair_sound hp) hw1).trans (runSteps_sound sts h)
      · cases h
    · cases h

/-- A derivation checked by running its steps. -/
theorem derive_of (sts : List (Step m)) {L R : List (Gen m)} (h : runSteps sts L = some R) :
    Derivable Fig6 (ofList L) (ofList R) :=
  runSteps_sound sts h

end QCert.HadamardPi
