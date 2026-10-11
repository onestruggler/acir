------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 1 of arXiv:2609.40106 presents the qupit Clifford group.
--
-- The paper's Theorem 4.10: the rules C0–C15 are sound and complete for
-- n-qudit Clifford circuits over -ω, H, S, CZ.  Here the group is the
-- one the rule set with -1 presents (Semantics.Clifford±: the exact
-- Clifford group of Clifford.Qupit, the central extension of the
-- projective Clifford group by ⟨ω⟩, times ⟨-1⟩), and the theorem is the
-- composite of two isomorphisms already proved:
--
--     Word group of Figure 1  ≅  Word group of _Exact±,_===_   (Iso)
--                             ≅  Clifford± n                   (Presentation)
--
-- the first being `new`, which reads -ω as -1 • ω.  So a Figure-1
-- circuit denotes the element its translation denotes, and two Figure-1
-- circuits are equal by the rules exactly when they denote the same
-- element — at every width n, every odd prime p and every primitive
-- root g.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Presentation
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (Group)
import Algebra.Morphism.Construct.Composition as Compose
open import Function using (_∘_)

open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.Morphism using (module GroupMorphism)

import Examples.Groups.Clifford+MinusOne.Qupit.Syntactics
  p-3 p-prime g* g-gen as N
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Syntactics
  p-3 p-prime g* g-gen as F
import Examples.Groups.Clifford+MinusOne.Qupit.Translation
  p-3 p-prime g* g-gen as T
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Derived
  p-3 p-prime g* g-gen as D
import Examples.Groups.Clifford+MinusOne.Qupit.Iso
  p-3 p-prime g* g-gen as I
import Examples.Groups.Clifford+MinusOne.Qupit.Semantics
  p-3 p-prime g* g-gen as Sem
import Examples.Groups.Clifford+MinusOne.Qupit.Presentation
  p-3 p-prime g* g-gen as P

------------------------------------------------------------------------
-- new, as a group isomorphism

-- The isomorphism of Iso run the other way: Figure 1's words into the
-- rule set with -1.
module New-Iso (n : ℕ) where

  private
    module GM = GroupMorphism (F._F,_===_ n) (n N.Exact±,_===_)
                  I.grouplike-F I.grouplike±

  open GM.StarGroupIsomorphism T.new T.fig
         D.new-well-defined T.new-left-inv-gen
         I.fig-well-defined T.fig-left-inv-gen
    public using (isGroupIsomorphism)

------------------------------------------------------------------------
-- The theorem

presentation-Figure1 : ∀ (n : ℕ) →
                       (F._F,_===_ n) IsPresentationOf (Sem.Clifford± n)
presentation-Figure1 n = record
  { gl  = I.grouplike-F
  ; ⟦_⟧ = PN.⟦_⟧ ∘ T.Gʷ
  ; iso = Compose.isGroupIsomorphism (Group.trans (Sem.Clifford± n))
            (New-Iso.isGroupIsomorphism n) PN.iso
  }
  where
  module PN = _IsPresentationOf_ (P.presentation± n)
