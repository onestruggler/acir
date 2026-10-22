------------------------------------------------------------------------
-- Presentations of groups
--
-- Two-level words read as stored tries, and the comparison of a circuit
-- with a two-level word by computation
--
-- Bridge.TwoLevel n gives each one- or two-level generator on 2ⁿ
-- indices a scaled operator, and a two-level word the product of its
-- letters' (⟦_⟧Y).  Its stored reading ⟦_⟧YM tabulates that product
-- letter by letter, as Interpretation.⟦_⟧M does for circuits; `Y-ix`
-- says the two agree.  Then a circuit and a two-level word denote the
-- same matrix when their stored matrices agree once each is scaled by
-- the other's power of γ (`by-tries`), an equation of tries decided by
-- one boolean (`Same`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; _^_)

module Examples.Groups.Clifford+CS.TwoLevelTries (n : ℕ) where

open import Data.Bool using (true)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; len ; ⟦_⟧M ; ⟦⟧-ix)
open import Examples.Groups.Clifford+CS.Semantics.Decide using (eqM ; eqM-sound)
open import Examples.Groups.Clifford+CS.MacroEval using (ChkF ; F-≡)
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
import Examples.Groups.Clifford+CS.Bridge as Bridge

open Bridge.TwoLevel n using (⟦_⟧ʸ ; ⟦_⟧Y)

private
  N : ℕ
  N = 2 ^ n

------------------------------------------------------------------------
-- The stored reading

⟦_⟧YM : Word (TL.Gen N) → Mat n
⟦ [ y ]ʷ ⟧YM = matOf (proj₂ ⟦ y ⟧ʸ)
⟦ ε ⟧YM      = idM
⟦ u • t ⟧YM  = mulM ⟦ u ⟧YM ⟦ t ⟧YM

Y-ix : (u : Word (TL.Gen N)) → proj₂ ⟦ u ⟧Y ≐ ix ⟦ u ⟧YM
Y-ix [ y ]ʷ  = ≐-sym (ix-matOf (proj₂ ⟦ y ⟧ʸ))
Y-ix ε       = ≐-sym ix-id
Y-ix (u • t) = ≐-trans (⊙-cong (Y-ix u) (Y-ix t)) (≐-sym (ix-mul ⟦ u ⟧YM ⟦ t ⟧YM))

------------------------------------------------------------------------
-- A circuit and a two-level word with the same matrix

by-tries : (w : Circuit n) (u : Word (TL.Gen N)) →
           scaleM (γ^ proj₁ ⟦ u ⟧Y) ⟦ w ⟧M ≡ scaleM (γ^ len w) ⟦ u ⟧YM →
           ⟦ w ⟧ ~ ⟦ u ⟧Y
by-tries w u eq =
  ≐-trans (·-cong Eq.refl (⟦⟧-ix w))
    (≐-trans (≐-sym (ix-scaleM _ _))
      (≐-trans (ix-≡ eq)
        (≐-trans (ix-scaleM _ _) (·-cong Eq.refl (≐-sym (Y-ix u))))))

-- The same, decided by one boolean on the row-operation reading of the
-- circuit.  The words are explicit: they cannot be read back off it.
Same : Circuit n → Word (TL.Gen N) → Set
Same w u = ChkF w (proj₁ ⟦ u ⟧Y) ⟦ u ⟧YM

by-same : (w : Circuit n) (u : Word (TL.Gen N)) → Same w u → ⟦ w ⟧ ~ ⟦ u ⟧Y
by-same w u e =
  by-tries w u (F-≡ w (proj₁ ⟦ u ⟧Y) ⟦ u ⟧YM e)
