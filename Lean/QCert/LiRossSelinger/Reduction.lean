/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Li, Ross, Selinger (2021): completeness from the Main Lemma

The normal word `nw s` of a state is the sequence of syllables of
Algorithm 1 down to the identity (`nw s = nw (N s) · N`).  Completeness
(Theorem 4.10) follows from two statements:

* `MainLemmaBasic` — Lemma A.20 for the basic edges that do not raise the
  level: for `s ≠ I`, a basic generator `G` with `level (G s) ≤ level s`,
  and `N` the normal syllable at `s`, some normal syllables `N*` from `G s`
  and a word `G*` from `N s`, all of whose states lie below `level s`,
  close the square: `N* G ≈ G* N`.
* `BasicDecomp` — Lemma A.19: every generator is derivably a word of basic
  generators, whose states, applied to any `s`, stay at or below the level
  of the edge, `max (level s) (level (G s))`.

The proof (`complete_of`) is an induction on the edge level
`max (level s) (level (G s))`, basic edges before the others at each level.
A basic edge that raises the level is closed by the square at its higher
endpoint (every generator is an involution).  This replaces the paper's
Lemmas 4.8, 4.9 and A.21: the induction of Lemma 4.8 is on `level s`, which
does not cover the "retrograde" edges that Lemma A.20 leaves out.
-/
import QCert.LiRossSelinger.Algorithm
import QCert.Synthesis

namespace QCert.LiRossSelinger

open Matrix Classical

variable {n : ℕ}

noncomputable section

/-! ## Normal words -/

/-- The normal word of a state: the syllables of Algorithm 1, the first one
rightmost. -/
def nw : O_ZHalf n → Word (Gen n) :=
  (wellFounded_lt.onFun (f := level)).fix fun U ih =>
    if hU : U = 1 then 1 else ih (next U) (level_next_lt U hU) * FreeMonoid.ofList (syll U)

theorem nw_eq (U : O_ZHalf n) :
    nw U = if U = 1 then 1 else nw (next U) * FreeMonoid.ofList (syll U) := by
  rw [nw, WellFounded.fix_eq]
  split_ifs <;> rfl

theorem nw_one : nw (1 : O_ZHalf n) = 1 := by rw [nw_eq, if_pos rfl]

theorem nw_ne_one {U : O_ZHalf n} (hU : U ≠ 1) :
    nw U = nw (next U) * FreeMonoid.ofList (syll U) := by rw [nw_eq, if_neg hU]

theorem syll_one : syll (1 : O_ZHalf n) = [] := by
  rw [syll, dif_neg (by rw [(pivotJ_eq_zero_iff 1).2 rfl]; omega)]

theorem next_one : next (1 : O_ZHalf n) = 1 := by simp [next, syll_one]

/-- The normal word reduces its state to the identity. -/
theorem nw_reduces (U : O_ZHalf n) : FreeMonoid.lift (sem n) (nw U) * U = 1 := by
  induction U using (wellFounded_lt.onFun (f := level)).induction with
  | _ U ih =>
    by_cases hU : U = 1
    · rw [hU, nw_one, map_one, one_mul]
    · rw [nw_ne_one hU, map_mul, mul_assoc]
      exact ih (next U) (level_next_lt U hU)

/-- The syllables of the first `m` normal steps from `U`. -/
def npath : ℕ → O_ZHalf n → List (Gen n)
  | 0, _ => []
  | m + 1, U => npath m (next U) ++ syll U

/-- The state after `m` normal steps. -/
def iterN : ℕ → O_ZHalf n → O_ZHalf n
  | 0, U => U
  | m + 1, U => iterN m (next U)

theorem iterN_eq (m : ℕ) (U : O_ZHalf n) :
    iterN m U = FreeMonoid.lift (sem n) (FreeMonoid.ofList (npath m U)) * U := by
  induction m generalizing U with
  | zero => simp [iterN, npath]
  | succ m ih =>
    rw [iterN, ih, npath, FreeMonoid.ofList_append, map_mul, mul_assoc]; rfl

theorem nw_npath (m : ℕ) (U : O_ZHalf n) :
    nw U = nw (iterN m U) * FreeMonoid.ofList (npath m U) := by
  induction m generalizing U with
  | zero => simp [iterN, npath]
  | succ m ih =>
    by_cases hU : U = 1
    · subst hU
      have : ∀ m, iterN m (1 : O_ZHalf n) = 1 ∧ npath m (1 : O_ZHalf n) = [] := by
        intro m; induction m with
        | zero => simp [iterN, npath]
        | succ m ihm => simp [iterN, npath, next_one, syll_one, ihm.1, ihm.2]
      simp [(this (m + 1)).1, (this (m + 1)).2]
    · rw [nw_ne_one hU, ih (next U), iterN, npath, FreeMonoid.ofList_append, mul_assoc]

/-! ## The two statements -/

/-- The basic generators: `X_[a,a+1]`, `(−1)_[0]`, `K_[0,1,2,3]` (Definition A.17,
from `0`). -/
def IsBasic : Gen n → Prop
  | .neg a => a.val = 0
  | .x a b _ => b.val = a.val + 1
  | .k a b c d _ _ _ => a.val = 0 ∧ b.val = 1 ∧ c.val = 2 ∧ d.val = 3

/-- Every state along a word `l` applied to `t` (rightmost letter first) lies
below `L`. -/
def PathBelow (l : List (Gen n)) (t : O_ZHalf n) (L : Level) : Prop :=
  ∀ i ≤ l.length, level (FreeMonoid.lift (sem n) (FreeMonoid.ofList (l.drop i)) * t) < L

/-- Lemma A.20 for the basic edges that do not raise the level. -/
def MainLemmaBasic (n : ℕ) : Prop :=
  ∀ (s : O_ZHalf n) (g : Gen n), IsBasic g → s ≠ 1 → level (sem n g * s) ≤ level s →
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n g * s)) * FreeMonoid.of g)
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s))

/-- Lemma A.19: every generator is derivably a word of basic generators that
stays at or below the level of the edge at every intermediate state. -/
def BasicDecomp (n : ℕ) : Prop :=
  ∀ (s : O_ZHalf n) (g : Gen n), ∃ h : List (Gen n), (∀ x ∈ h, IsBasic x) ∧
    Derivable (Table1 n) (FreeMonoid.of g) (FreeMonoid.ofList h) ∧
    ∀ i ≤ h.length,
      level (FreeMonoid.lift (sem n) (FreeMonoid.ofList (h.drop i)) * s) ≤
        max (level s) (level (sem n g * s))

/-! ## The induction -/

/-- The step of a normal-word argument at a state and a generator. -/
def Step (U : O_ZHalf n) (g : Gen n) : Prop :=
  Derivable (Table1 n) (nw (sem n g * U) * FreeMonoid.of g) (nw U)

/-- The level of an edge. -/
def edgeLevel (U : O_ZHalf n) (g : Gen n) : Level := max (level U) (level (sem n g * U))

theorem sem_sq (g : Gen n) : sem n g * sem n g = 1 := by
  have := derivable_sound sound (Derivable.of (show Table1 n (FreeMonoid.of g * FreeMonoid.of g) 1 by
    cases g with
    | neg a => exact Table1.r1b a
    | x a b h => exact Table1.r1a a b h
    | k a b c d h₁ h₂ h₃ => exact Table1.r1c a b c d h₁ h₂ h₃))
  simpa using this

theorem sq_derivable (g : Gen n) : Derivable (Table1 n) (FreeMonoid.of g * FreeMonoid.of g) 1 := by
  apply Derivable.of
  cases g with
  | neg a => exact Table1.r1b a
  | x a b h => exact Table1.r1a a b h
  | k a b c d h₁ h₂ h₃ => exact Table1.r1c a b c d h₁ h₂ h₃

theorem sem_ne_one (g : Gen n) : sem n g ≠ 1 := by
  intro h
  have hm : genMat g = 1 := by
    have := congrArg (fun U : O_ZHalf n => mat U) h
    exact this
  cases g with
  | neg a =>
    have e := congrFun (congrFun hm a) a
    rw [← Matrix.mul_one (genMat _), genMat_neg_mul, one_apply] at e
    simp at e; norm_num at e
  | x a b hab =>
    have e := congrFun (congrFun hm a) a
    rw [← Matrix.mul_one (genMat _), genMat_x_mul, one_apply] at e
    simp [Ne.symm (ne_of_lt hab)] at e
  | k a b c d h₁ h₂ h₃ =>
    have e := congrFun (congrFun hm b) b
    rw [← Matrix.mul_one (genMat _), genMat_k_mul, one_apply] at e
    have hab := ne_of_lt h₁
    have hbc := ne_of_lt h₂
    have hbd := ne_of_lt (h₂.trans h₃)
    simp [Ne.symm hab, one_apply, hab, hbc, hbd, Ne.symm hbc, Ne.symm hbd] at e
    norm_num at e

/-- Steps along a word give the step for the word. -/
theorem path_step (l : List (Gen n)) (t : O_ZHalf n)
    (h : ∀ i (hi : i < l.length),
      Step (FreeMonoid.lift (sem n) (FreeMonoid.ofList (l.drop (i + 1))) * t) l[i]) :
    Derivable (Table1 n) (nw (FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * t) *
      FreeMonoid.ofList l) (nw t) := by
  induction l with
  | nil => simpa using Derivable.refl (nw t)
  | cons g l ih =>
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    have hrest := ih (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa using this)
    rw [FreeMonoid.ofList_cons, map_mul, mul_assoc, FreeMonoid.lift_eval_of, ← mul_assoc]
    exact (h0.mul (Derivable.refl _)).trans hrest

theorem drop_cons_getElem (l : List (Gen n)) (i : ℕ) (hi : i < l.length) :
    l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons hi

theorem state_succ (l : List (Gen n)) (t : O_ZHalf n) (i : ℕ) (hi : i < l.length) :
    sem n l[i] * (FreeMonoid.lift (sem n) (FreeMonoid.ofList (l.drop (i + 1))) * t) =
      FreeMonoid.lift (sem n) (FreeMonoid.ofList (l.drop i)) * t := by
  rw [drop_cons_getElem l i hi, FreeMonoid.ofList_cons, map_mul, FreeMonoid.lift_eval_of, mul_assoc]

/-- Theorem 4.10's induction: every step holds, given Lemmas A.19 and A.20. -/
theorem step_all (hml : MainLemmaBasic n) (hbd : BasicDecomp n) (U : O_ZHalf n) (g : Gen n) :
    Step U g := by
  suffices H : ∀ L : Level, ∀ U g, edgeLevel U g = L → Step U g from H _ U g rfl
  intro L
  induction L using WellFoundedLT.induction with
  | _ L ih =>
  have below : ∀ (U : O_ZHalf n) (g : Gen n), edgeLevel U g < L → Step U g :=
    fun U g h => ih _ h U g rfl
  -- a basic edge not raising the level
  have nonretro : ∀ (U : O_ZHalf n) (g : Gen n), IsBasic g → edgeLevel U g = L →
      level (sem n g * U) ≤ level U →
      Step U g := by
    intro U g hb hE hle
    have hU1 : U ≠ 1 := by
      intro h1; subst h1
      have : level (sem n g * 1) ≤ mkLevel 0 0 0 := by
        rw [show (1 : O_ZHalf n) = 1 from rfl] at hle
        have e : level (1 : O_ZHalf n) = mkLevel 0 0 0 := (level_eq_zero_iff 1).2 rfl
        rwa [e] at hle
      have h0 : level (sem n g * 1) = mkLevel 0 0 0 := le_antisymm this bot_le
      exact sem_ne_one g (by simpa using (level_eq_zero_iff _).1 h0)
    obtain ⟨m, gs, hpath, hder⟩ := hml U g hb hU1 hle
    have hLU : L = level U := by rw [← hE]; exact max_eq_left hle
    have hsem := derivable_sound sound hder
    have hq : iterN m (sem n g * U) =
        FreeMonoid.lift (sem n) (FreeMonoid.ofList gs) * next U := by
      rw [iterN_eq, next, ← mul_assoc, ← mul_assoc]
      congr 1
      simpa [map_mul, FreeMonoid.lift_eval_of] using hsem
    have hp := path_step gs (next U) (fun i hi => below _ _ (by
      rw [edgeLevel, state_succ gs (next U) i hi, hLU]
      exact max_lt (hpath (i + 1) (by omega)) (hpath i (by omega))))
    unfold Step
    rw [nw_npath m (sem n g * U), mul_assoc]
    refine ((Derivable.refl _).mul hder).trans ?_
    rw [← mul_assoc, hq, nw_ne_one hU1]
    exact hp.mul (Derivable.refl _)
  -- every basic edge at level `L`
  have basic : ∀ (U : O_ZHalf n) (g : Gen n), IsBasic g → edgeLevel U g = L → Step U g := by
    intro U g hb hE
    by_cases hle : level (sem n g * U) ≤ level U
    · exact nonretro U g hb hE hle
    · -- closed at the higher endpoint
      have hlt : level U < level (sem n g * U) := lt_of_not_ge hle
      have hgg : sem n g * (sem n g * U) = U := by rw [← mul_assoc, sem_sq, one_mul]
      have h' := nonretro (sem n g * U) g hb (by
        rw [edgeLevel, hgg, ← hE, edgeLevel, max_comm]) (by rw [hgg]; exact hlt.le)
      unfold Step at h' ⊢
      rw [hgg] at h'
      have e := (h'.symm).mul (Derivable.refl (FreeMonoid.of g))
      rw [mul_assoc] at e
      exact e.trans (by simpa using (Derivable.refl (nw U)).mul (sq_derivable g))
  -- every edge at level `L`
  intro U g hE
  obtain ⟨h, hbas, hder, hlev⟩ := hbd U g
  have hsem : FreeMonoid.lift (sem n) (FreeMonoid.ofList h) = sem n g := by
    have := derivable_sound sound hder; simpa using this.symm
  have hp := path_step h U (fun i hi => by
    have hle : edgeLevel (FreeMonoid.lift (sem n) (FreeMonoid.ofList (h.drop (i + 1))) * U) h[i] ≤ L := by
      rw [edgeLevel, state_succ h U i hi, ← hE]
      exact max_le (hlev (i + 1) (by omega)) (hlev i (by omega))
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact below _ _ hlt
    · exact basic _ _ (hbas _ (List.getElem_mem hi)) heq)
  unfold Step
  rw [hsem] at hp
  exact ((Derivable.refl _).mul hder).trans hp

/-- Theorem 4.10 from Lemmas A.19 and A.20. -/
theorem complete_of (hml : MainLemmaBasic n) (hbd : BasicDecomp n) :
    ∀ ⦃u v : Word (Gen n)⦄, FreeMonoid.lift (sem n) u = FreeMonoid.lift (sem n) v →
      Derivable (Table1 n) u v :=
  (NormalWords.isPresentationOf
    ⟨nw, nw_reduces, fun M x => step_all hml hbd M x⟩ grouplike sound).complete

end

end QCert.LiRossSelinger
