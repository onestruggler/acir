/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: completeness

The normal words of Algorithm 2.14 (`nw`) reduce every state to the
identity (Theorem 2.16, `nw_reduces`), and `Step` holds for every state and
generator (Lemma 3.6), by induction on the level from the Main Lemma
(Lemma 3.7) for basic generators (`steps_of`), and from basic generators to
all (Lemma 3.4, `step_all`).  With soundness this is Theorem 3.1.
-/
import QCert.BianSelingerUn.MainX2
import QCert.Synthesis

namespace QCert.BianSelingerUn

variable {n : ℕ}

/-- The edges out of `I` (proof of Lemma 3.6, base case). -/
theorem base_step : ∀ x, Basic x → Step (1 : St n) x := base_step'

/-- Lemma 3.7 (Main Lemma), with the induction hypothesis of Lemma 3.6. -/
theorem main_lemma : ∀ (s : St n) x, s ≠ 1 → Basic x →
    (∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) → Step s x := by
  intro s x hs hx hstep
  cases x with
  | X a b hab => exact main_X hs hab hx hstep
  | K a b hab => exact main_K hs hab hx.1 hx.2 hstep
  | i a => exact main_i hs a hx hstep

/-- Lemma 3.4 with its level remark: a generator is a word of basic
generators whose intermediate states have level at most the larger level of
the two ends, so `Step` along simple edges below a level follows from
`Step` along basic edges below it. -/
theorem lift_basic : ∀ L : ℕ ×ₗ ℕ ×ₗ ℕ, (∀ (u : St n) x, Basic x → level u < L → Step u x) →
    ∀ u y, level u < L → level (sem n y * u) < L → Step u y :=
  lift_basic'

/-- Lemma 3.4: every generator is a word of basic generators. -/
theorem decomp : ∀ y : Gen n, ∃ b, AllBasic b ∧ Derivable (Rel n) (FreeMonoid.of y) b :=
  decomp'

/-- Lemma 3.6 for every edge. -/
theorem step (s : St n) (y : Gen n) : Step s y :=
  step_all (steps_of base_step main_lemma lift_basic) decomp s y

/-- The normal words of Algorithm 2.14, with Theorem 2.16 and Lemma 3.6. -/
noncomputable def normalWords : NormalWords (Rel n) (sem n) where
  nw := nw
  reduces := nw_reduces
  step := step

end QCert.BianSelingerUn
