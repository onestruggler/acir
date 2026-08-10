------------------------------------------------------------------------
-- Presentations of groups
--
-- The interpretation of a collapsing presentation in the terminal
-- group, and its soundness.
--
-- Every generator denotes the identity, which is the only thing it
-- could denote.  Soundness is likewise forced: the target's equality
-- relates every pair of elements, so no axiom can fail.
--
-- Parameterised by the same gen≈ε as Normalization; see the note there.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel ; [_]ʷ ; ε)

import Presentation.Base as PB

module Examples.Groups.Trivial.Interpretation
  {A : Set} (Γ : WRel A)
  (gen≈ε : ∀ x → PB._≈_ Γ [ x ]ʷ ε)
  where

open import Algebra.Bundles using (Group)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Normalization.StarPresentation using (module GroupSem)
open import Presentation.GroupLike using (Grouplike)

open import Examples.Groups.Trivial.Semantics using (gp)

open PB Γ using (_≈_)
open _≈_

------------------------------------------------------------------------
-- The interpretation

-- The unique semantics: every generator denotes the identity.
⟦_⟧₀ : A → Group.Carrier gp
⟦_⟧₀ _ = Group.ε gp

module GS = GroupSem Γ (Eq.setoid ⊤) gp ⟦_⟧₀

------------------------------------------------------------------------
-- Soundness

-- Every axiom is respected: the target group's equality is trivial.
fʷ-cong-ax : ∀ {w v} → Γ w v → Group._≈_ gp GS.⟦ w ⟧ GS.⟦ v ⟧
fʷ-cong-ax _ = _

------------------------------------------------------------------------
-- Group-like

-- ε left-inverts every generator, since [ x ]ʷ ≈ ε.
grouplike : Grouplike Γ
grouplike x = ε , trans left-unit (gen≈ε x)
