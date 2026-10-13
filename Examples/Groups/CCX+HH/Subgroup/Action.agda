------------------------------------------------------------------------
-- Presentations of groups
--
-- The four-state quotient read directly from Table 1.
--
-- The labels record two independent parities:
-- M : 10, X : 11, K : 01.  The first is determinant parity; the
-- second agrees with the rational spinor square-class of 2.  Only the
-- explicit action and its syntactic proof are used below.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Subgroup.Action where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH.Subgroup.State as State

data Coset : Set where
  c00 c10 c11 c01 : Coset

dyadic-step : ∀ {N} → Coset → T.Gen N → Coset
dyadic-step c00 (T.M-gen _) = c10
dyadic-step c10 (T.M-gen _) = c00
dyadic-step c11 (T.M-gen _) = c01
dyadic-step c01 (T.M-gen _) = c11
dyadic-step c00 (T.X-gen _ _ _) = c11
dyadic-step c10 (T.X-gen _ _ _) = c01
dyadic-step c11 (T.X-gen _ _ _) = c00
dyadic-step c01 (T.X-gen _ _ _) = c10
dyadic-step c00 (T.K-gen _ _ _ _ _ _ _) = c01
dyadic-step c10 (T.K-gen _ _ _ _ _ _ _) = c11
dyadic-step c11 (T.K-gen _ _ _ _ _ _ _) = c10
dyadic-step c01 (T.K-gen _ _ _ _ _ _ _) = c00

module At (N : ℕ) where
  open State (dyadic-step {N}) public using (state)

  state-relations : ∀ c {u v} → u T.=== v → state c u ≡ state c v
  state-relations c00 (T.r1a _) = refl
  state-relations c10 (T.r1a _) = refl
  state-relations c11 (T.r1a _) = refl
  state-relations c01 (T.r1a _) = refl
  state-relations c00 T.r1b = refl
  state-relations c10 T.r1b = refl
  state-relations c11 T.r1b = refl
  state-relations c01 T.r1b = refl
  state-relations c00 (T.r1c _ _ _) = refl
  state-relations c10 (T.r1c _ _ _) = refl
  state-relations c11 (T.r1c _ _ _) = refl
  state-relations c01 (T.r1c _ _ _) = refl
  state-relations c00 (T.r2a _ _ _ _ _ _) = refl
  state-relations c10 (T.r2a _ _ _ _ _ _) = refl
  state-relations c11 (T.r2a _ _ _ _ _ _) = refl
  state-relations c01 (T.r2a _ _ _ _ _ _) = refl
  state-relations c00 (T.r2b _ _ _) = refl
  state-relations c10 (T.r2b _ _ _) = refl
  state-relations c11 (T.r2b _ _ _) = refl
  state-relations c01 (T.r2b _ _ _) = refl
  state-relations c00 (T.r2c _ _ _ _ _ _ _ _ _ _ _ _) = refl
  state-relations c10 (T.r2c _ _ _ _ _ _ _ _ _ _ _ _) = refl
  state-relations c11 (T.r2c _ _ _ _ _ _ _ _ _ _ _ _) = refl
  state-relations c01 (T.r2c _ _ _ _ _ _ _ _ _ _ _ _) = refl
  state-relations c00 (T.r2d _) = refl
  state-relations c10 (T.r2d _) = refl
  state-relations c11 (T.r2d _) = refl
  state-relations c01 (T.r2d _) = refl
  state-relations c00 (T.r2e _ _ _ _ _ _ _) = refl
  state-relations c10 (T.r2e _ _ _ _ _ _ _) = refl
  state-relations c11 (T.r2e _ _ _ _ _ _ _) = refl
  state-relations c01 (T.r2e _ _ _ _ _ _ _) = refl
  state-relations c00 (T.r2f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = refl
  state-relations c10 (T.r2f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = refl
  state-relations c11 (T.r2f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = refl
  state-relations c01 (T.r2f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = refl
  state-relations c00 (T.r3a _ _ _) = refl
  state-relations c10 (T.r3a _ _ _) = refl
  state-relations c11 (T.r3a _ _ _) = refl
  state-relations c01 (T.r3a _ _ _) = refl
  state-relations c00 (T.r3b _ _ _) = refl
  state-relations c10 (T.r3b _ _ _) = refl
  state-relations c11 (T.r3b _ _ _) = refl
  state-relations c01 (T.r3b _ _ _) = refl
  state-relations c00 (T.r3c _) = refl
  state-relations c10 (T.r3c _) = refl
  state-relations c11 (T.r3c _) = refl
  state-relations c01 (T.r3c _) = refl
  state-relations c00 (T.r3d _ _ _ _ _) = refl
  state-relations c10 (T.r3d _ _ _ _ _) = refl
  state-relations c11 (T.r3d _ _ _ _ _) = refl
  state-relations c01 (T.r3d _ _ _ _ _) = refl
  state-relations c00 (T.r3e _ _ _ _ _ _) = refl
  state-relations c10 (T.r3e _ _ _ _ _ _) = refl
  state-relations c11 (T.r3e _ _ _ _ _ _) = refl
  state-relations c01 (T.r3e _ _ _ _ _ _) = refl
  state-relations c00 (T.r3f _ _ _ _ _ _) = refl
  state-relations c10 (T.r3f _ _ _ _ _ _) = refl
  state-relations c11 (T.r3f _ _ _ _ _ _) = refl
  state-relations c01 (T.r3f _ _ _ _ _ _) = refl
  state-relations c00 (T.r3g _ _ _ _ _) = refl
  state-relations c10 (T.r3g _ _ _ _ _) = refl
  state-relations c11 (T.r3g _ _ _ _ _) = refl
  state-relations c01 (T.r3g _ _ _ _ _) = refl
  state-relations c00 (T.r4a _ _ _ _) = refl
  state-relations c10 (T.r4a _ _ _ _) = refl
  state-relations c11 (T.r4a _ _ _ _) = refl
  state-relations c01 (T.r4a _ _ _ _) = refl
  state-relations c00 (T.r4b _ _ _) = refl
  state-relations c10 (T.r4b _ _ _) = refl
  state-relations c11 (T.r4b _ _ _) = refl
  state-relations c01 (T.r4b _ _ _) = refl
  state-relations c00 (T.r4c _ _ _ _) = refl
  state-relations c10 (T.r4c _ _ _ _) = refl
  state-relations c11 (T.r4c _ _ _ _) = refl
  state-relations c01 (T.r4c _ _ _ _) = refl
  state-relations c00 (T.r5a _ _ _ _ _ _ _) = refl
  state-relations c10 (T.r5a _ _ _ _ _ _ _) = refl
  state-relations c11 (T.r5a _ _ _ _ _ _ _) = refl
  state-relations c01 (T.r5a _ _ _ _ _ _ _) = refl
  state-relations c00 (T.r6a _ _ _ _ _ _ _ _) = refl
  state-relations c10 (T.r6a _ _ _ _ _ _ _ _) = refl
  state-relations c11 (T.r6a _ _ _ _ _ _ _ _) = refl
  state-relations c01 (T.r6a _ _ _ _ _ _ _ _) = refl

  open State.Congruence (dyadic-step {N}) (T._===_ {N}) state-relations
    public using (state-cong)
