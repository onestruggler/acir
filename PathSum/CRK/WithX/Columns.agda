------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits over {H, X, CNOT, R_k, R_k†}: lemma 4.1 and the isometry
-- restriction (Amy, QPL 2018, section 4.1)
--
-- Section 4.1 decides whether a circuit is the identity through its
-- isometry restriction ⟦C⟧|f(x,y)=x, and lemma 4.1 says that for a
-- well-formed path-sum the restriction decides it.  For circuits over
-- PathSum.CRK.WithX -- the gate set of the Clifford+T identities the
-- paper takes from Selinger and Bian [29], with X read as
-- |x⟩ ↦ |1 ⊕ x⟩ -- well-formedness is PathSum.CRK.WithX.WellFormed's:
-- every column of ⟦ C ⟧ has trace-form norm 2^(norm C)
-- (⟦⟧-unit-columns, X pairing z[w≔0] with z[w≔1] and swapping them),
-- so ⟦ C ⟧ is WellFormed (circuit-WellFormed).  This module re-exports
-- those two facts and ⟦⟧-state, and adds what follows from them in the
-- form PathSum.Examples.CaseIdentity and the root use:
--
-- * lemma 4.1 at every such circuit (lemma-4-1-circuit):
--   ⟦ C ⟧ ≋ |x⟩ ↦ |x⟩ exactly when its restricted sum at every x is 1;
-- * the restriction, reified by PathSum.Gauss (reification-circuit),
--   stated at PathSum.Gauss's Reification of the state the circuit runs
--   to, as PathSum.Gauss.reification-circuit states it for circuits
--   without X.  The forms an interpretation state holds are affine --
--   c ⊕ S, with the constant an X puts there -- and PathSum.Gauss
--   eliminates over exactly those, so the elimination applies to these
--   circuits unchanged: either some diagonal entry vanishes and ⟦ C ⟧
--   is not the identity, or the restriction is a path-sum with the
--   identity's outputs and only internal path variables that is the
--   identity exactly when ⟦ C ⟧ is.  (PathSum.CRK.WithX.WellFormed's
--   reification-WithX is the same fact, packaged with ⟦ C ⟧ in place of
--   the state's path-sum.)
--
-- No order bound beyond the phase's own is stated: proposition 2.14 is
-- not proved for the gate set with X.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.CRK.WithX.Columns (M₀ : ℕ) where

open import Data.Product.Base using (proj₂)
open import Function.Bundles using (_⇔_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (idPS)
open import PathSum.CRK.Circuit M using (init)
open import PathSum.CRK.WithX M₀ using (Circuit; norm; run; ⟦_⟧)
open import PathSum.Denotation M₀ using (_≋_)
open import PathSum.Gauss M₀ using (Reification; reification)
open import PathSum.Isometry M₀ using (Restriction-id; lemma-4-1)

-- Unit columns and well-formedness, from PathSum.CRK.WithX.WellFormed.

open import PathSum.CRK.WithX.WellFormed M₀ public
  using (⟦⟧-unit-columns; circuit-WellFormed; ⟦⟧-state)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Lemma 4.1 at every circuit

lemma-4-1-circuit : (C : Circuit n) →
                    (⟦ C ⟧ ≋ idPS ⇔ Restriction-id ⟦ C ⟧)
lemma-4-1-circuit C = lemma-4-1 ⟦ C ⟧ (circuit-WellFormed C)


------------------------------------------------------------------------
-- The isometry restriction, reified

-- ⟦ C ⟧ is the path-sum of the state the circuit runs to, so Gaussian
-- elimination applies to it as it stands, and well-formedness is what
-- makes its verdict exact.

reification-circuit : (C : Circuit n) →
                      Reification (proj₂ (run C init)) (norm C)
reification-circuit C =
  reification {k = norm C} (proj₂ (run C init)) (circuit-WellFormed C)
