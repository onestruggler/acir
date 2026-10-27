/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: completeness

The normal words of Algorithm 16 (`nw`) reduce every state to the identity
(Theorem 18, `nw_reduces`), and `Step` holds for every state and generator
(Lemma 32 and its extension to all generators): by induction on the level
from the Main Lemma (Lemma 31) for basic generators (`steps_of`), and from
basic generators to all (Lemma 30, `step_all`).  With soundness this is
Theorem 34, completeness.

The Main Lemma is the one place that needs `n ≤ 4` (Subcase 4.3.3 of its
proof, with Lemma 39).
-/
import QCert.Greylyn.BaseCase
import QCert.Synthesis

namespace QCert.Greylyn

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

/-- The edges out of `I` (proof of Lemma 32, base case: "an easy case
distinction shows that the claim holds for all basic generators"). -/
theorem base_step : ∀ x, Basic x → Step (1 : St n) x :=
  fun x _ => step_one_all x

/-- Lemma 31 (Main Lemma): for a state `s ≠ I` of dimension `n ≤ 4`, its
normal edge `s ⇒ t` (`t = N s`, `N` the syllable of `s`) and a basic edge
`s → r = x s`, there are a state `q`, normal edges `r ⇒ q` labelled `N'`
and simple edges `t → q` labelled `G'` with `N' x ≈ G' N`, all of whose
states have level below that of `s`. -/
theorem main_lemma (hn : n ≤ 4) (s : St n) (hs : s ≠ 1) (x : Gen n) (hx : Basic x) :
    ∃ (q : St n) (N' G' : Word (Gen n)), NormalPath (sem n x * s) N' q ∧
      ⟪G'⟫ * (⟪syl s⟫ * s) = q ∧ AllBelow (level s) (⟪syl s⟫ * s) G' ∧
      Derivable (Rel n) (N' * FreeMonoid.of x) (G' * syl s) := by
  sorry

/-- The inductive step of Lemma 32: Lemma 31 closes the square at `s`, and
`Step` holds along its path by the induction hypothesis. -/
theorem main_step (hn : n ≤ 4) : ∀ (s : St n) x, s ≠ 1 → Basic x →
    (∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) → Step s x := by
  intro s x hs hx hstep
  obtain ⟨q, N', G', hN, hq, hG, hrel⟩ := main_lemma hn s hs x hx
  exact step_of_square hs N' G' q hN.nw_eq hq hG hrel hstep

/-- Lemma 30 with its level part (c): a generator is a word of basic
generators whose intermediate states have level at most the larger level of
the two ends, so `Step` along simple edges below a level follows from
`Step` along basic edges below it. -/
theorem lift_basic : ∀ L : ℕ ×ₗ ℕ ×ₗ ℕ, (∀ (u : St n) x, Basic x → level u < L → Step u x) →
    ∀ u y, level u < L → level (sem n y * u) < L → Step u y :=
  lift_basic'

/-- Lemma 30 (a): every generator is a word of basic generators. -/
theorem decomp : ∀ y : Gen n, ∃ b, AllBasic b ∧ Derivable (Rel n) (FreeMonoid.of y) b :=
  decomp'

/-- Lemma 32 for every edge (`n ≤ 4`). -/
theorem step (hn : n ≤ 4) (s : St n) (y : Gen n) : Step s y :=
  step_all (steps_of base_step (main_step hn) lift_basic) decomp s y

/-- The normal words of Algorithm 16, with Theorem 18 and Lemma 32. -/
noncomputable def normalWords (hn : n ≤ 4) : NormalWords (Rel n) (sem n) where
  nw := nw
  reduces := nw_reduces
  step := step hn

end QCert.Greylyn
