/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A checker for derivations from Clément's relations on concrete indices

As `QCert.HadamardPi.Check` for Figure 6: a derivation between two words on
concrete indices (`Fin m`, `m` a numeral) is a list of steps, each the
rewriting of a segment of the current word by an instance of one of
Clément's relations (named by its tag and its indices, `CStep.rel`) or by an
already derived equation (`CStep.lem`).  `runC` performs the rewriting and
`deriveC_of` turns a successful run, checked by `decide +kernel`, into a
derivation in `RelK full`.  The tags `t20`, `t21` take any four, resp. six,
distinct indices (the placement of (20), (21)) and are available when
`full`.  A derivation at `Fin m` moves to any distinct indices by `derC_map`.
-/
import QCert.Clement2019.RelK
import QCert.HadamardPi.Derive

namespace QCert.Clement2019

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

/-- `(-1)[a]` on concrete indices. -/
abbrev cz (a : Fin m) : Gen m := .Z a
/-- `X[a,b]` on concrete indices, `a ≠ b` proved by `decide`. -/
abbrev cx (a b : Fin m) (h : a ≠ b := by decide) : Gen m := .X a b h
/-- `H[a,b]` on concrete indices, `a ≠ b` proved by `decide`. -/
abbrev ch (a b : Fin m) (h : a ≠ b := by decide) : Gen m := .H a b h

/-- The labels of Clément's relations (1)–(21). -/
inductive CTag
  | t1 | t2 | t3 | t4 | t5 | t6 | t7 | t8 | t9 | t10 | t11 | t12 | t13 | t14 | t15 | t16
  | t17 | t18 | t19 | t20 | t21

theorem inj_of_nodup {k : ℕ} {f : Fin k → Fin m} (h : (List.ofFn f).Nodup) :
    Function.Injective f := List.nodup_ofFn.mp h

/-- The instance of a relation at the given indices (in the order of the
constructor's arguments, `j, k, l, t`; for (20), (21) the placement), if its
side conditions hold. -/
def ruleC (full : Bool) : CTag → List (Fin m) → Option (List (Gen m) × List (Gen m))
  | .t1, [j] => some ([.Z j, .Z j], [])
  | .t2, [j, k] => if h : j ≠ k then some ([.H j k h, .H j k h], []) else none
  | .t3, [j, k] => if h : j ≠ k then some ([.X j k h, .X j k h], []) else none
  | .t4, [j, k] => if j ≠ k then some ([.Z j, .Z k], [.Z k, .Z j]) else none
  | .t5, [j, k, l] => if h : j ≠ k ∧ l ≠ j ∧ l ≠ k then
      some ([.Z l, .H j k h.1], [.H j k h.1, .Z l]) else none
  | .t6, [j, k, l] => if h : j ≠ k ∧ l ≠ j ∧ l ≠ k then
      some ([.Z l, .X j k h.1], [.X j k h.1, .Z l]) else none
  | .t7, [j, k, l, t] => if h : j ≠ k ∧ l ≠ t ∧ j ≠ l ∧ j ≠ t ∧ k ≠ l ∧ k ≠ t then
      some ([.H j k h.1, .H l t h.2.1], [.H l t h.2.1, .H j k h.1]) else none
  | .t8, [j, k, l, t] => if h : j ≠ k ∧ l ≠ t ∧ j ≠ l ∧ j ≠ t ∧ k ≠ l ∧ k ≠ t then
      some ([.H j k h.1, .X l t h.2.1], [.X l t h.2.1, .H j k h.1]) else none
  | .t9, [j, k, l, t] => if h : j ≠ k ∧ l ≠ t ∧ j ≠ l ∧ j ≠ t ∧ k ≠ l ∧ k ≠ t then
      some ([.X j k h.1, .X l t h.2.1], [.X l t h.2.1, .X j k h.1]) else none
  | .t10, [j, k] => if h : j ≠ k then some ([.X j k h, .Z k], [.Z j, .X j k h]) else none
  | .t11, [j, k] => if h : j ≠ k then some ([.X j k h, .Z j], [.Z k, .X j k h]) else none
  | .t12, [j, k, l] => if h : j ≠ k ∧ j ≠ l ∧ k ≠ l then
      some ([.X j k h.1, .X j l h.2.1], [.X k l h.2.2, .X j k h.1]) else none
  | .t13, [j, k, l] => if h : j ≠ k ∧ j ≠ l ∧ k ≠ l then
      some ([.X j k h.1, .X l j (Ne.symm h.2.1)], [.X l k (Ne.symm h.2.2), .X j k h.1]) else none
  | .t14, [j, k, l] => if h : j ≠ k ∧ j ≠ l ∧ k ≠ l then
      some ([.X j k h.1, .H j l h.2.1], [.H k l h.2.2, .X j k h.1]) else none
  | .t15, [j, k, l] => if h : j ≠ k ∧ j ≠ l ∧ k ≠ l then
      some ([.X j k h.1, .H l j (Ne.symm h.2.1)], [.H l k (Ne.symm h.2.2), .X j k h.1]) else none
  | .t16, [j, k] => if h : j ≠ k then
      some ([.Z j, .Z k, .X j k h], [.X j k h, .Z j, .Z k]) else none
  | .t17, [j, k] => if h : j ≠ k then
      some ([.Z j, .Z k, .H j k h], [.H j k h, .Z j, .Z k]) else none
  | .t18, [j, k] => if h : j ≠ k then some ([.H j k h, .X j k h], [.Z k, .H j k h]) else none
  | .t19, [j, k, l, t] => if h : j ≠ k ∧ l ≠ t ∧ j ≠ l ∧ k ≠ t ∧ j ≠ t then
      some ([.H j k h.1, .H l t h.2.1, .H j l h.2.2.1, .H k t h.2.2.2.1],
        [.H j l h.2.2.1, .H k t h.2.2.2.1, .H j k h.1, .H l t h.2.1]) else none
  | .t20, [a, b, c, d] => if full = true then
      if h : (List.ofFn ![a, b, c, d]).Nodup then
        some (l20L ![a, b, c, d] (inj_of_nodup h), l20R ![a, b, c, d] (inj_of_nodup h))
      else none else none
  | .t21, [a, b, c, d, e, f] => if full = true then
      if h : (List.ofFn ![a, b, c, d, e, f]).Nodup then
        some (l21L ![a, b, c, d, e, f] (inj_of_nodup h), l21R ![a, b, c, d, e, f] (inj_of_nodup h))
      else none else none
  | _, _ => none

theorem ruleC_sound {full : Bool} {t : CTag} {ix : List (Fin m)} {P Q : List (Gen m)}
    (h : ruleC full t ix = some (P, Q)) : Derivable (RelK full) (ofList P) (ofList Q) := by
  unfold ruleC at h
  split at h <;> (try split_ifs at h with hc) <;> (try simp only [Option.some.injEq,
    Prod.mk.injEq, reduceCtorEq] at h) <;> (try obtain ⟨rfl, rfl⟩ := h)
  · exact Derivable.of (RelK.r1 _)
  · exact Derivable.of (RelK.r2 hc)
  · exact Derivable.of (RelK.r3 hc)
  · exact Derivable.of (RelK.r4 hc)
  · exact Derivable.of (RelK.r5 hc.1 hc.2.1 hc.2.2)
  · exact Derivable.of (RelK.r6 hc.1 hc.2.1 hc.2.2)
  · exact Derivable.of (RelK.r7 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2)
  · exact Derivable.of (RelK.r8 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2)
  · exact Derivable.of (RelK.r9 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2)
  · exact Derivable.of (RelK.r10 hc)
  · exact Derivable.of (RelK.r11 hc)
  · exact Derivable.of (RelK.r12 hc.1 hc.2.1 hc.2.2)
  · exact Derivable.of (RelK.r13 hc.1 hc.2.1 hc.2.2)
  · exact Derivable.of (RelK.r14 hc.1 hc.2.1 hc.2.2)
  · exact Derivable.of (RelK.r15 hc.1 hc.2.1 hc.2.2)
  · exact Derivable.of (RelK.r16 hc)
  · exact Derivable.of (RelK.r17 hc)
  · exact Derivable.of (RelK.r18 hc)
  · exact Derivable.of (RelK.r19 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2)
  · exact Derivable.of (RelK.r20 hc _ _)
  · exact Derivable.of (RelK.r21 hc _ _)

/-- A step: a relation at given indices, or an already derived equation,
applied at a position, left to right (`true`) or right to left. -/
inductive CStep (full : Bool) (m : ℕ)
  | rel (t : CTag) (ix : List (Fin m)) (pos : ℕ) (fwd : Bool)
  | lem (P Q : List (Gen m)) (h : Derivable (RelK full) (ofList P) (ofList Q)) (pos : ℕ)
      (fwd : Bool)

variable {full : Bool}

/-- The equation a step rewrites by, in its direction. -/
def CStep.pair : CStep full m → Option (List (Gen m) × List (Gen m))
  | .rel t ix _ fwd => (ruleC full t ix).map fun p => if fwd then p else p.swap
  | .lem P Q _ _ fwd => some (if fwd then (P, Q) else (Q, P))

def CStep.pos : CStep full m → ℕ
  | .rel _ _ pos _ => pos
  | .lem _ _ _ pos _ => pos

theorem CStep.pair_sound {st : CStep full m} {P Q : List (Gen m)} (h : st.pair = some (P, Q)) :
    Derivable (RelK full) (ofList P) (ofList Q) := by
  cases st with
  | rel t ix pos fwd =>
    simp only [CStep.pair, Option.map_eq_some_iff] at h
    obtain ⟨⟨P', Q'⟩, h1, h2⟩ := h
    have := ruleC_sound h1
    cases fwd
    · simp only [Bool.false_eq_true, if_false, Prod.swap_prod_mk, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2; exact this.symm
    · simp only [if_true, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2; exact this
  | lem P' Q' hd pos fwd =>
    simp only [CStep.pair, Option.some.injEq] at h
    cases fwd
    · simp only [Bool.false_eq_true, if_false, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hd.symm
    · simp only [if_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hd

/-- Rewrite the segment `P` at position `pos` of `w` into `Q`. -/
def rewriteC (P Q : List (Gen m)) (pos : ℕ) (w : List (Gen m)) : Option (List (Gen m)) :=
  if (w.drop pos).take P.length = P then some (w.take pos ++ Q ++ w.drop (pos + P.length))
  else none

/-- Run a list of steps from a word. -/
def runC : List (CStep full m) → List (Gen m) → Option (List (Gen m))
  | [], w => some w
  | st :: sts, w =>
    match st.pair with
    | some (P, Q) =>
      match rewriteC P Q st.pos w with
      | some w' => runC sts w'
      | none => none
    | none => none

theorem rewriteC_sound {P Q : List (Gen m)} (hd : Derivable (RelK full) (ofList P) (ofList Q))
    {pos : ℕ} {w w' : List (Gen m)} (h : rewriteC P Q pos w = some w') :
    Derivable (RelK full) (ofList w) (ofList w') := by
  unfold rewriteC at h
  split_ifs at h with hm
  cases h
  exact HadamardPi.rw_at w pos hd hm

theorem runC_sound : ∀ (sts : List (CStep full m)) {w w' : List (Gen m)},
    runC sts w = some w' → Derivable (RelK full) (ofList w) (ofList w')
  | [], w, w', h => by
    simp only [runC, Option.some.injEq] at h; subst h; exact Derivable.refl _
  | st :: sts, w, w', h => by
    simp only [runC] at h
    split at h
    · rename_i P Q hp
      split at h
      · rename_i w1 hw1
        exact (rewriteC_sound (CStep.pair_sound hp) hw1).trans (runC_sound sts h)
      · cases h
    · cases h

/-- A derivation checked by running its steps. -/
theorem deriveC_of (sts : List (CStep full m)) {L R : List (Gen m)} (h : runC sts L = some R) :
    Derivable (RelK full) (ofList L) (ofList R) :=
  runC_sound sts h

/-- A derivation moved along an injective map of indices. -/
theorem derC_map {n : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f) {L R : List (Gen m)}
    (h : Derivable (RelK full) (ofList L) (ofList R)) :
    Derivable (RelK full) (ofList (L.map (Gen.map f hf))) (ofList (R.map (Gen.map f hf))) :=
  Derivable.mapC f hf h

end QCert.Clement2019
