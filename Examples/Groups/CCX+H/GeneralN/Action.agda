------------------------------------------------------------------------
-- Presentations of groups
--
-- The four-state right action of the scaled two-level presentation.
-- Dyadic letters translate the two parity labels.  IH acts by the
-- shear (d,s) ↦ (d,s+d), fixing 00 and 01 and exchanging 10 and 11.
-- Tables 1 and 2 preserve this action at every dimension.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.Action where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
open import Examples.Groups.CCX+HH.Subgroup.Action public
  using (Coset ; c00 ; c10 ; c11 ; c01)
import Examples.Groups.CCX+HH.Subgroup.Action as Dyadic
import Examples.Groups.CCX+HH.Subgroup.State as State

shear : Coset → Coset
shear c00 = c00
shear c10 = c11
shear c11 = c10
shear c01 = c01

step : ∀ {N} → Coset → T.Genᴸ N → Coset
step c T.⌊ g ⌋ = Dyadic.dyadic-step c g
step c T.IH = shear c

module At (N : ℕ) where
  open State (step {N}) public using (state)
  private module D = Dyadic.At N

  state-lift : ∀ c (w : Word (U.Gen N)) →
    state c T.⌊ w ⌋ʷ ≡ D.state c w
  state-lift c [ g ]ʷ = Eq.refl
  state-lift c ε = Eq.refl
  state-lift c (w • v) =
    Eq.trans (state-lift (state c T.⌊ w ⌋ʷ) v)
      (Eq.cong (λ d → D.state d v) (state-lift c w))

  state-relations : ∀ c {u v} → u T.===ᴸ v →
    state c u ≡ state c v
  state-relations c (T.table1 {u} {v} ax) =
    Eq.trans (state-lift c u)
      (Eq.trans (D.state-relations c ax) (Eq.sym (state-lift c v)))
  state-relations c00 T.r7a = Eq.refl
  state-relations c10 T.r7a = Eq.refl
  state-relations c11 T.r7a = Eq.refl
  state-relations c01 T.r7a = Eq.refl
  state-relations c00 (T.r7b _ _ _ _ _ _ _) = Eq.refl
  state-relations c10 (T.r7b _ _ _ _ _ _ _) = Eq.refl
  state-relations c11 (T.r7b _ _ _ _ _ _ _) = Eq.refl
  state-relations c01 (T.r7b _ _ _ _ _ _ _) = Eq.refl
  state-relations c00 (T.r7c _ _ _) = Eq.refl
  state-relations c10 (T.r7c _ _ _) = Eq.refl
  state-relations c11 (T.r7c _ _ _) = Eq.refl
  state-relations c01 (T.r7c _ _ _) = Eq.refl
  state-relations c00 (T.r7d₀ _ _ _) = Eq.refl
  state-relations c10 (T.r7d₀ _ _ _) = Eq.refl
  state-relations c11 (T.r7d₀ _ _ _) = Eq.refl
  state-relations c01 (T.r7d₀ _ _ _) = Eq.refl
  state-relations c00 (T.r7d₁ _ _ _ _ _ _ _) = Eq.refl
  state-relations c10 (T.r7d₁ _ _ _ _ _ _ _) = Eq.refl
  state-relations c11 (T.r7d₁ _ _ _ _ _ _ _) = Eq.refl
  state-relations c01 (T.r7d₁ _ _ _ _ _ _ _) = Eq.refl

  open State.Congruence (step {N}) (T._===ᴸ_ {N}) state-relations
    public using (state-cong)
