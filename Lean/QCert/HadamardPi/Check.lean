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

/-! ### Running the steps in one traversal

`rewriteAt` compares the segment with `take`/`drop` and the `DecidableEq` instance, and rebuilds
the word with `take`/`++`/`drop`; `rewriteAt'` walks to the position once, compares the letters
by their indices (`genBeq`, `Nat.beq` on the values, which the kernel evaluates natively) and
rebuilds the word on the way back.  `runCheck` runs a derivation with it and compares the result
letter by letter (`runCheck_sound`); on the tables of `QCert.Clement2019.Tables` this halves the
kernel's work. -/

/-- Letters compared by their indices. -/
def genBeq : Gen m → Gen m → Bool
  | .Z a, .Z a' => Nat.beq a.val a'.val
  | .X a b _, .X a' b' _ => Nat.beq a.val a'.val && Nat.beq b.val b'.val
  | .H a b _, .H a' b' _ => Nat.beq a.val a'.val && Nat.beq b.val b'.val
  | _, _ => false

theorem eq_of_genBeq : ∀ {g g' : Gen m}, genBeq g g' = true → g = g'
  | .Z a, .Z a', h => by
    have e : a = a' := Fin.ext (Nat.eq_of_beq_eq_true h)
    subst e; rfl
  | .X a b _, .X a' b' _, h => by
    simp only [genBeq, Bool.and_eq_true] at h
    have e1 : a = a' := Fin.ext (Nat.eq_of_beq_eq_true h.1)
    have e2 : b = b' := Fin.ext (Nat.eq_of_beq_eq_true h.2)
    subst e1 e2; rfl
  | .H a b _, .H a' b' _, h => by
    simp only [genBeq, Bool.and_eq_true] at h
    have e1 : a = a' := Fin.ext (Nat.eq_of_beq_eq_true h.1)
    have e2 : b = b' := Fin.ext (Nat.eq_of_beq_eq_true h.2)
    subst e1 e2; rfl
  | .Z _, .X _ _ _, h | .Z _, .H _ _ _, h | .X _ _ _, .Z _, h | .X _ _ _, .H _ _ _, h
  | .H _ _ _, .Z _, h | .H _ _ _, .X _ _ _, h => by simp [genBeq] at h

/-- Words compared letter by letter. -/
def wordBeq : List (Gen m) → List (Gen m) → Bool
  | [], [] => true
  | g :: w, g' :: w' => genBeq g g' && wordBeq w w'
  | _, _ => false

theorem eq_of_wordBeq : ∀ {w w' : List (Gen m)}, wordBeq w w' = true → w = w'
  | [], [], _ => rfl
  | g :: w, g' :: w', h => by
    simp only [wordBeq, Bool.and_eq_true] at h
    rw [eq_of_genBeq h.1, eq_of_wordBeq h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [wordBeq] at h

/-- `w` with the prefix `P` removed. -/
def stripPrefix : List (Gen m) → List (Gen m) → Option (List (Gen m))
  | [], w => some w
  | _ :: _, [] => none
  | p :: P, g :: w => bif genBeq p g then stripPrefix P w else none

theorem stripPrefix_eq : ∀ {P w r : List (Gen m)}, stripPrefix P w = some r → w = P ++ r
  | [], w, r, h => by simp only [stripPrefix, Option.some.injEq] at h; subst h; rfl
  | _ :: _, [], r, h => by simp [stripPrefix] at h
  | p :: P, g :: w, r, h => by
    simp only [stripPrefix] at h
    cases hb : genBeq p g with
    | false => rw [hb] at h; simp at h
    | true =>
      rw [hb, cond_true] at h
      rw [eq_of_genBeq hb, stripPrefix_eq h]
      rfl

/-- Rewrite the segment `P` at position `pos` of `w` into `Q`, in one traversal
(`rewriteAt` when it succeeds, `rewriteAt'_eq`). -/
def rewriteAt' (P Q : List (Gen m)) : ℕ → List (Gen m) → Option (List (Gen m))
  | 0, w => (stripPrefix P w).map (Q ++ ·)
  | _ + 1, [] => none
  | n + 1, g :: w => (rewriteAt' P Q n w).map (g :: ·)

theorem rewriteAt'_eq (P Q : List (Gen m)) : ∀ (pos : ℕ) (w w' : List (Gen m)),
    rewriteAt' P Q pos w = some w' → rewriteAt P Q pos w = some w'
  | 0, w, w', h => by
    simp only [rewriteAt', Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    rw [stripPrefix_eq hr]
    simp [rewriteAt]
  | _ + 1, [], w', h => by simp [rewriteAt'] at h
  | n + 1, g :: w, w', h => by
    simp only [rewriteAt', Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    have ih := rewriteAt'_eq P Q n w r hr
    unfold rewriteAt at ih ⊢
    split_ifs at ih with h1
    simp only [Option.some.injEq] at ih
    rw [if_pos (by simpa using h1), ← ih]
    simp [Nat.succ_add]

/-- Run a list of steps from a word, in one traversal per step. -/
def runSteps' : List (Step m) → List (Gen m) → Option (List (Gen m))
  | [], w => some w
  | st :: sts, w =>
    match st.pair with
    | some (P, Q) =>
      match rewriteAt' P Q st.pos w with
      | some w' => runSteps' sts w'
      | none => none
    | none => none

theorem runSteps'_eq : ∀ (sts : List (Step m)) {w w' : List (Gen m)},
    runSteps' sts w = some w' → runSteps sts w = some w'
  | [], w, w', h => h
  | st :: sts, w, w', h => by
    simp only [runSteps'] at h
    simp only [runSteps]
    split at h
    · rename_i P Q hp
      split at h
      · rename_i w1 hw1
        simp only [hp, rewriteAt'_eq P Q _ _ _ hw1]
        exact runSteps'_eq sts h
      · cases h
    · cases h

/-- The steps lead from `L` to `R`. -/
def runCheck (sts : List (Step m)) (L R : List (Gen m)) : Bool :=
  match runSteps' sts L with
  | some w => wordBeq w R
  | none => false

theorem runCheck_sound {sts : List (Step m)} {L R : List (Gen m)} (h : runCheck sts L R = true) :
    runSteps sts L = some R := by
  unfold runCheck at h
  split at h
  · rename_i w hw
    rw [runSteps'_eq sts hw, eq_of_wordBeq h]
  · cases h

/-- A derivation checked by `runCheck`. -/
theorem derive_of' (sts : List (Step m)) {L R : List (Gen m)} (h : runCheck sts L R = true) :
    Derivable Fig6 (ofList L) (ofList R) :=
  runSteps_sound sts (runCheck_sound h)

/-- A derivation moved along a strictly increasing map of indices. -/
theorem der_map {n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) {L R : List (Gen m)}
    (h : Derivable Fig6 (ofList L) (ofList R)) :
    Derivable Fig6 (ofList (L.map (Gen.map f hf))) (ofList (R.map (Gen.map f hf))) := by
  have := Derivable.map f hf h
  rwa [wmap_ofList, wmap_ofList] at this

end QCert.HadamardPi
