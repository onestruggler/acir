------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of the P′ rules by Reidemeister–Schreier
--
-- The P′ rules are complete for the determinant-one subgroup as soon
-- as their translation into the two-level generators reflects
-- equivalence; the two-level presentation is complete already
-- (Clifford+CS-TwoLevel's MainLemma.relations-complete), so that is
-- the analogue of Clément's Theorem 4.10 with no imported hypothesis.
-- The Reidemeister–Schreier method for monoids gives it, and
-- `Normalization/Reidemeister-Schreier` implements the method.  This
-- module is the instantiation: Γ is the theory of P′ (`Rules`), Δ the
-- two-level theory, C the four cosets with ⟨0⟩ distinguished, f the
-- reading `asG`, and h the coset action.
--
-- The engine's two hypotheses are the method's conditions, and naming
-- them says exactly what is left: `Item-a` is one equation per letter
-- of P′ — reading a letter into the two-level generators and back
-- through the action returns it, at ⟨0⟩ — and `Item-b` one per rule of
-- the two-level presentation per coset — the action respects it.
-- Given those two, `reidemeister-schreier` is the theorem.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc ; _≤_)

module Examples.Groups.Clifford+CS.Auxiliary.RS
  (N′ : ℕ) (big : 16 ≤ suc N′) where

open import Data.Product using (_,_)
open import Word.Base using (Word ; _ᵗ ; [_]ʷ)

open import Normalization.Reidemeister-Schreier using (module Star-Injective-Full)

import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; asG)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (_R,_===_)
open import Examples.Groups.Clifford+CS.Auxiliary.Cosets using (Coset ; ⟨0⟩)
open import Examples.Groups.Clifford+CS.Auxiliary.CosetAction N′ big using (act)

private
  N : ℕ
  N = suc N′

------------------------------------------------------------------------
-- The instantiation

module RSF = Star-Injective-Full (N R,_===_) (TL._===_ {N}) Coset ⟨0⟩

------------------------------------------------------------------------
-- The two conditions

Item-a : Set
Item-a = ∀ (x : GenP N) → RSF._~_ ([ x ]ʷ , ⟨0⟩) ((act ᵗ) ⟨0⟩ (asG x))

Item-b : Set
Item-b = ∀ (c : Coset) {u t : Word (TL.Gen N)} →
         TL._===_ u t → RSF._~_ ((act ᵗ) c u) ((act ᵗ) c t)

------------------------------------------------------------------------
-- What they give: the translation of a P′-word into the two-level
-- generators reflects equivalence.

module Complete (item-a : Item-a) (item-b : Item-b) where

  open RSF.Reidemeister-Schreier-Full asG act item-a item-b public
    using (reidemeister-schreier ; fʷ-inj)
