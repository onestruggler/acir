/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Derivations in Table 1, checked by the kernel and moved along embeddings

The relations of Table 1 only ask their indices to be ordered or distinct,
so a derivation on local indices `0, …, m-1` holds along any strictly
monotone embedding `Fin m ↪o Fin n` (`derivable_rename`).  On local
indices, a derivation is a list of rewriting steps (a relation family,
its indices, a direction and a position), checked by evaluation
(`check_sound`): a square of the Main Lemma is derived once on its own
indices and moved into place.  The steps are found by a search script
(scratch, `gen/`).
-/
import QCert.LiRossSelinger.Units
import QCert.LiRossSelinger.Syntax

namespace QCert.LiRossSelinger

deriving instance DecidableEq for Gen

variable {m n : ℕ}

/-! ## Renaming along an order embedding -/

/-- A generator with its indices renamed along `f`. -/
def Gen.rename (f : Fin m ↪o Fin n) : Gen m → Gen n
  | .neg a => .neg (f a)
  | .x a b h => .x (f a) (f b) (f.strictMono h)
  | .k a b c d h₁ h₂ h₃ => .k (f a) (f b) (f c) (f d) (f.strictMono h₁) (f.strictMono h₂)
      (f.strictMono h₃)

/-- A word with its indices renamed. -/
def renW (f : Fin m ↪o Fin n) : Word (Gen m) →* Word (Gen n) := FreeMonoid.map (Gen.rename f)

theorem nodup_rename (f : Fin m ↪o Fin n) {l : List (Fin m)} (h : l.Nodup) : (l.map f).Nodup :=
  h.map f.injective

theorem table1_rename (f : Fin m ↪o Fin n) {u v : Word (Gen m)} (h : Table1 m u v) :
    Table1 n (renW f u) (renW f v) := by
  cases h with
  | r1a a b h => exact Table1.r1a _ _ _
  | r1b a => exact Table1.r1b _
  | r1c a b c d h₁ h₂ h₃ => exact Table1.r1c _ _ _ _ _ _ _
  | r2a a b c d h₁ h₂ h => exact Table1.r2a _ _ _ _ _ _ (by simpa using nodup_rename f h)
  | r2b a b c h₁ h => exact Table1.r2b _ _ _ _ (by simpa using nodup_rename f h)
  | r2c a b c d e f' h₁ h₂ h₃ h₄ h => exact Table1.r2c _ _ _ _ _ _ _ _ _ _ (by simpa using nodup_rename f h)
  | r2d a b h => exact Table1.r2d _ _ (fun e => h (f.injective e))
  | r2e a b c d e h₁ h₂ h₃ h => exact Table1.r2e _ _ _ _ _ _ _ _ (by simpa using nodup_rename f h)
  | r2f a b c d e f' g h' h₁ h₂ h₃ h₄ h₅ h₆ hd =>
    exact Table1.r2f _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using nodup_rename f hd)
  | r3a a a' b h₁ h₂ => exact Table1.r3a _ _ _ (f.strictMono h₁) (f.strictMono h₂)
  | r3b a b b' h₁ h₂ => exact Table1.r3b _ _ _ (f.strictMono h₁) (f.strictMono h₂)
  | r3c a b h => exact Table1.r3c _ _ _
  | r3d a a' b c d h₁ h₂ h₃ h₄ =>
    exact Table1.r3d _ _ _ _ _ (f.strictMono h₁) (f.strictMono h₂) (f.strictMono h₃) (f.strictMono h₄)
  | r3e a b b' c d h₁ h₂ h₃ h₄ =>
    exact Table1.r3e _ _ _ _ _ (f.strictMono h₁) (f.strictMono h₂) (f.strictMono h₃) (f.strictMono h₄)
  | r3f a b c c' d h₁ h₂ h₃ h₄ =>
    exact Table1.r3f _ _ _ _ _ (f.strictMono h₁) (f.strictMono h₂) (f.strictMono h₃) (f.strictMono h₄)
  | r3g a b c d d' h₁ h₂ h₃ h₄ =>
    exact Table1.r3g _ _ _ _ _ (f.strictMono h₁) (f.strictMono h₂) (f.strictMono h₃) (f.strictMono h₄)
  | r4a a b c d h₁ h₂ h₃ => exact Table1.r4a _ _ _ _ _ _ _
  | r4b a b c d h₁ h₂ h₃ => exact Table1.r4b _ _ _ _ _ _ _
  | r4c a b c d h₁ h₂ h₃ => exact Table1.r4c _ _ _ _ _ _ _
  | r5a a b c d e f' h₁ h₂ h₃ h₄ h₅ => exact Table1.r5a _ _ _ _ _ _ _ _ _ _ _
  | r6a a b c d e f' g h' h₁ h₂ h₃ h₄ h₅ h₆ h₇ => exact Table1.r6a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem derivable_rename (f : Fin m ↪o Fin n) {u v : Word (Gen m)}
    (h : Derivable (Table1 m) u v) : Derivable (Table1 n) (renW f u) (renW f v) :=
  derivable_map (renW f) (fun _ _ r => Derivable.of (table1_rename f r)) h

/-! ## Relation instances on concrete indices -/

/-- The families of Table 1. -/
inductive Fam
  | r1a | r1b | r1c | r2a | r2b | r2c | r2d | r2e | r2f | r3a | r3b | r3c | r3d | r3e | r3f | r3g
  | r4a | r4b | r4c | r5a | r6a
  deriving DecidableEq

/-- The two sides of an instance of a family at the given indices (in the
order of the constructor's index arguments). -/
def sides : Fam → List (Fin m) → Option (List (Gen m) × List (Gen m))
  | .r1a, [a, b] => if h : a < b then some ([.x a b h, .x a b h], []) else none
  | .r1b, [a] => some ([.neg a, .neg a], [])
  | .r1c, [a, b, c, d] =>
    if h : a < b ∧ b < c ∧ c < d then
      some ([.k a b c d h.1 h.2.1 h.2.2, .k a b c d h.1 h.2.1 h.2.2], []) else none
  | .r2a, [a, b, c, d] =>
    if h : a < b ∧ c < d ∧ [a, b, c, d].Nodup then
      some ([.x a b h.1, .x c d h.2.1], [.x c d h.2.1, .x a b h.1]) else none
  | .r2b, [a, b, c] =>
    if h : a < b ∧ [a, b, c].Nodup then some ([.x a b h.1, .neg c], [.neg c, .x a b h.1]) else none
  | .r2c, [a, b, c, d, e, f] =>
    if h : a < b ∧ c < d ∧ d < e ∧ e < f ∧ [a, b, c, d, e, f].Nodup then
      some ([.x a b h.1, .k c d e f h.2.1 h.2.2.1 h.2.2.2.1],
        [.k c d e f h.2.1 h.2.2.1 h.2.2.2.1, .x a b h.1]) else none
  | .r2d, [a, b] => if a ≠ b then some ([.neg a, .neg b], [.neg b, .neg a]) else none
  | .r2e, [a, b, c, d, e] =>
    if h : b < c ∧ c < d ∧ d < e ∧ [a, b, c, d, e].Nodup then
      some ([.neg a, .k b c d e h.1 h.2.1 h.2.2.1], [.k b c d e h.1 h.2.1 h.2.2.1, .neg a])
    else none
  | .r2f, [a, b, c, d, e, f, g, i] =>
    if h : a < b ∧ b < c ∧ c < d ∧ e < f ∧ f < g ∧ g < i ∧ [a, b, c, d, e, f, g, i].Nodup then
      some ([.k a b c d h.1 h.2.1 h.2.2.1, .k e f g i h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1],
        [.k e f g i h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1, .k a b c d h.1 h.2.1 h.2.2.1]) else none
  | .r3a, [a, a', b] =>
    if h : a < a' ∧ a' < b then
      some ([.x a a' h.1, .x a b (h.1.trans h.2)], [.x a' b h.2, .x a a' h.1]) else none
  | .r3b, [a, b, b'] =>
    if h : a < b ∧ b < b' then
      some ([.x b b' h.2, .x a b h.1], [.x a b' (h.1.trans h.2), .x b b' h.2]) else none
  | .r3c, [a, b] => if h : a < b then some ([.x a b h, .neg b], [.neg a, .x a b h]) else none
  | .r3d, [a, a', b, c, d] =>
    if h : a < a' ∧ a' < b ∧ b < c ∧ c < d then
      some ([.x a a' h.1, .k a b c d (h.1.trans h.2.1) h.2.2.1 h.2.2.2],
        [.k a' b c d h.2.1 h.2.2.1 h.2.2.2, .x a a' h.1]) else none
  | .r3e, [a, b, b', c, d] =>
    if h : a < b ∧ b < b' ∧ b' < c ∧ c < d then
      some ([.x b b' h.2.1, .k a b c d h.1 (h.2.1.trans h.2.2.1) h.2.2.2],
        [.k a b' c d (h.1.trans h.2.1) h.2.2.1 h.2.2.2, .x b b' h.2.1]) else none
  | .r3f, [a, b, c, c', d] =>
    if h : a < b ∧ b < c ∧ c < c' ∧ c' < d then
      some ([.x c c' h.2.2.1, .k a b c d h.1 h.2.1 (h.2.2.1.trans h.2.2.2)],
        [.k a b c' d h.1 (h.2.1.trans h.2.2.1) h.2.2.2, .x c c' h.2.2.1]) else none
  | .r3g, [a, b, c, d, d'] =>
    if h : a < b ∧ b < c ∧ c < d ∧ d < d' then
      some ([.x d d' h.2.2.2, .k a b c d h.1 h.2.1 h.2.2.1],
        [.k a b c d' h.1 h.2.1 (h.2.2.1.trans h.2.2.2), .x d d' h.2.2.2]) else none
  | .r4a, [a, b, c, d] =>
    if h : a < b ∧ b < c ∧ c < d then
      some ([.x a b h.1, .k a b c d h.1 h.2.1 h.2.2],
        [.k a b c d h.1 h.2.1 h.2.2, .x b d (h.2.1.trans h.2.2), .neg b, .neg d]) else none
  | .r4b, [a, b, c, d] =>
    if h : a < b ∧ b < c ∧ c < d then
      some ([.x b c h.2.1, .k a b c d h.1 h.2.1 h.2.2],
        [.neg a, .k a b c d h.1 h.2.1 h.2.2, .neg a, .k a b c d h.1 h.2.1 h.2.2, .neg a]) else none
  | .r4c, [a, b, c, d] =>
    if h : a < b ∧ b < c ∧ c < d then
      some ([.x c d h.2.2, .k a b c d h.1 h.2.1 h.2.2],
        [.k a b c d h.1 h.2.1 h.2.2, .x b d (h.2.1.trans h.2.2)]) else none
  | .r5a, [a, b, c, d, e, f] =>
    if h : a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f then
      some ([.k a b c d h.1 h.2.1 h.2.2.1, .k b d e f (h.2.1.trans h.2.2.1) h.2.2.2.1 h.2.2.2.2],
        [.k c d e f h.2.2.1 h.2.2.2.1 h.2.2.2.2, .k a b c e h.1 h.2.1 (h.2.2.1.trans h.2.2.2.1)])
    else none
  | .r6a, [a, b, c, d, e, f, g, i] =>
    if h : a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f ∧ f < g ∧ g < i then
      let ae := h.1.trans (h.2.1.trans (h.2.2.1.trans h.2.2.2.1))
      let core : List (Gen m) := [.k e f g i h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2,
        .k a b c d h.1 h.2.1 h.2.2.1, .x d e h.2.2.2.1, .k a b c d h.1 h.2.1 h.2.2.1,
        .k e f g i h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2]
      some ([.neg a, .neg e, .x a e ae] ++ core ++ [.x a e ae, .neg a, .neg e], core)
    else none
  | _, _ => none

theorem sides_sound {f : Fam} {ps : List (Fin m)} {u v : List (Gen m)}
    (h : sides f ps = some (u, v)) : Table1 m (FreeMonoid.ofList u) (FreeMonoid.ofList v) := by
  unfold sides at h
  split at h
  · -- r1a
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r1a _ _ hc
  · -- r1b
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r1b _
  · -- r1c
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r1c _ _ _ _ hc.1 hc.2.1 hc.2.2
  · -- r2a
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r2a _ _ _ _ hc.1 hc.2.1 hc.2.2
  · -- r2b
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r2b _ _ _ hc.1 hc.2
  · -- r2c
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r2c _ _ _ _ _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  · -- r2d
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r2d _ _ hc
  · -- r2e
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r2e _ _ _ _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  · -- r2f
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r2f _ _ _ _ _ _ _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2
  · -- r3a
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r3a _ _ _ hc.1 hc.2
  · -- r3b
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r3b _ _ _ hc.1 hc.2
  · -- r3c
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r3c _ _ hc
  · -- r3d
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r3d _ _ _ _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  · -- r3e
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r3e _ _ _ _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  · -- r3f
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r3f _ _ _ _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  · -- r3g
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r3g _ _ _ _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  · -- r4a
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r4a _ _ _ _ hc.1 hc.2.1 hc.2.2
  · -- r4b
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r4b _ _ _ _ hc.1 hc.2.1 hc.2.2
  · -- r4c
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r4c _ _ _ _ hc.1 hc.2.1 hc.2.2
  · -- r5a
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r5a _ _ _ _ _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  · -- r6a
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Table1.r6a _ _ _ _ _ _ _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2
  · exact absurd h (by simp)

/-! ## Rewriting steps -/

/-- A rewriting step: a family with its indices, the direction (`true`: from
left to right side) and the position in the word. -/
structure Step (m : ℕ) where
  fam : Fam
  ps : List (Fin m)
  dir : Bool
  pos : ℕ

/-- Replace `l` at position `pos` of `w` by `r`. -/
def rewriteAt (w : List (Gen m)) (pos : ℕ) (l r : List (Gen m)) : Option (List (Gen m)) :=
  if (w.drop pos).take l.length = l then
    some (w.take pos ++ r ++ w.drop (pos + l.length)) else none

theorem rewriteAt_sound {w w' l r : List (Gen m)} {pos : ℕ}
    (hlr : Derivable (Table1 m) (FreeMonoid.ofList l) (FreeMonoid.ofList r))
    (h : rewriteAt w pos l r = some w') :
    Derivable (Table1 m) (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  unfold rewriteAt at h
  split_ifs at h with hc
  obtain rfl := Option.some.inj h
  have hw : w = w.take pos ++ l ++ w.drop (pos + l.length) := by
    conv_lhs => rw [← List.take_append_drop pos w]
    rw [List.append_assoc]
    congr 1
    conv_lhs => rw [← List.take_append_drop l.length (w.drop pos)]
    rw [hc, List.drop_drop]
  conv_lhs => rw [hw]
  simp only [FreeMonoid.ofList_append]
  exact ((Derivable.refl _).mul hlr).mul (Derivable.refl _)

/-- Apply a step to a word. -/
def applyStep (w : List (Gen m)) (st : Step m) : Option (List (Gen m)) :=
  match sides st.fam st.ps with
  | none => none
  | some (u, v) => if st.dir then rewriteAt w st.pos u v else rewriteAt w st.pos v u

theorem applyStep_sound {w w' : List (Gen m)} {st : Step m} (h : applyStep w st = some w') :
    Derivable (Table1 m) (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  unfold applyStep at h
  split at h
  · exact absurd h (by simp)
  · rename_i u v hs
    have hrel := sides_sound hs
    split_ifs at h
    · exact rewriteAt_sound (Derivable.of hrel) h
    · exact rewriteAt_sound (Derivable.of hrel).symm h

/-- Apply a list of steps. -/
def runSteps (w : List (Gen m)) : List (Step m) → Option (List (Gen m))
  | [] => some w
  | st :: sts => match applyStep w st with
    | none => none
    | some w' => runSteps w' sts

theorem runSteps_sound {w w' : List (Gen m)} {sts : List (Step m)} (h : runSteps w sts = some w') :
    Derivable (Table1 m) (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  induction sts generalizing w with
  | nil => obtain rfl := Option.some.inj h; exact Derivable.refl _
  | cons st sts ih =>
    unfold runSteps at h
    split at h
    · exact absurd h (by simp)
    · rename_i w'' hw''
      exact (applyStep_sound hw'').trans (ih h)

/-- A derivation, checked by evaluation. -/
def checkSteps (w w' : List (Gen m)) (sts : List (Step m)) : Bool := runSteps w sts == some w'

theorem checkSteps_sound {w w' : List (Gen m)} {sts : List (Step m)}
    (h : checkSteps w w' sts = true) :
    Derivable (Table1 m) (FreeMonoid.ofList w) (FreeMonoid.ofList w') :=
  runSteps_sound (by simpa [checkSteps] using h)

end QCert.LiRossSelinger
