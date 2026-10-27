/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completing a square of the Main Lemma

`MainLemmaBasic` asks, for a state `s` and a basic generator `G` that does
not raise the level, for `m` normal syllables from `G s` and a path `P` from
`next s` with `npath m (G s) · G ≈ P · syll s`.  The two ends of `P` are
below the level of `s` for free: `next s` because a syllable lowers the
level, and the other end because it is `iterN m (G s)` (by soundness), which
is below `level s` as soon as `m > 0` or `G s` is.  So only the inner states
of `P` need checking (`square`); with `P` of length at most one there are
none (`square_short`).
-/
import QCert.LiRossSelinger.Reduction

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

theorem level_next_le (U : O_ZHalf n) : level (next U) ≤ level U := by
  by_cases h : U = 1
  · subst h; rw [next_one]
  · exact (level_next_lt U h).le

theorem level_iterN_le (m : ℕ) (U : O_ZHalf n) : level (iterN m U) ≤ level U := by
  induction m generalizing U with
  | zero => exact le_rfl
  | succ m ih => exact (ih (next U)).trans (level_next_le U)

theorem level_pos {s : O_ZHalf n} (hs : s ≠ 1) : mkLevel 0 0 0 < level s :=
  lt_of_le_of_ne bot_le (fun h => hs ((level_eq_zero_iff s).1 h.symm))

theorem level_iterN_lt {m : ℕ} (hm : 0 < m) (U : O_ZHalf n) {s : O_ZHalf n} (hs : s ≠ 1)
    (hU : level U ≤ level s) : level (iterN m U) < level s := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  by_cases h1 : U = 1
  · subst h1
    have : ∀ m, iterN m (1 : O_ZHalf n) = 1 := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => rw [iterN, next_one, ih]
    rw [this, (level_eq_zero_iff 1).2 rfl]
    exact level_pos hs
  · exact lt_of_le_of_lt (level_iterN_le m (next U)) (lt_of_lt_of_le (level_next_lt U h1) hU)

/-- A square of the Main Lemma, given the inner states of its bottom path. -/
theorem square {s : O_ZHalf n} {g : Gen n} (hs : s ≠ 1) (hle : level (sem n g * s) ≤ level s)
    (m : ℕ) (P : List (Gen n)) (hm : 0 < m ∨ level (sem n g * s) < level s)
    (hder : Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n g * s)) * FreeMonoid.of g)
      (FreeMonoid.ofList P * FreeMonoid.ofList (syll s)))
    (hmid : ∀ i, 0 < i → i < P.length →
      level (FreeMonoid.lift (sem n) (FreeMonoid.ofList (P.drop i)) * next s) < level s) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n g * s)) * FreeMonoid.of g)
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  refine ⟨m, P, ?_, hder⟩
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · have hsem := derivable_sound sound hder
    simp only [map_mul, FreeMonoid.lift_eval_of] at hsem
    have hend : FreeMonoid.lift (sem n) (FreeMonoid.ofList (P.drop 0)) * next s =
        iterN m (sem n g * s) := by
      rw [List.drop_zero, iterN_eq, next, ← mul_assoc, ← hsem, mul_assoc]
    rw [hend]
    rcases hm with hm | hlt
    · exact level_iterN_lt hm _ hs hle
    · exact lt_of_le_of_lt (level_iterN_le m _) hlt
  rcases lt_or_eq_of_le hi with hlt | rfl
  · exact hmid i hi0 hlt
  · rw [List.drop_length]
    simpa using level_next_lt s hs

theorem npath_one (U : O_ZHalf n) : npath 1 U = syll U := by simp [npath]

/-- A square whose bottom path has at most one edge, closed by one syllable. -/
theorem square_short {s : O_ZHalf n} {g : Gen n} (hs : s ≠ 1)
    (hle : level (sem n g * s) ≤ level s) (P : List (Gen n)) (hP : P.length ≤ 1)
    (hder : Derivable (Table1 n) (FreeMonoid.ofList (syll (sem n g * s)) * FreeMonoid.of g)
      (FreeMonoid.ofList P * FreeMonoid.ofList (syll s))) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n g * s)) * FreeMonoid.of g)
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) :=
  square hs hle 1 P (Or.inl one_pos) (by rwa [npath_one])
    (fun i hi0 hi => absurd hi (by omega))

end QCert.LiRossSelinger
