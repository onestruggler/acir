------------------------------------------------------------------------
-- Presentations of groups
--
-- Decidable circuit equality in the complete relation at every width.
-- Exact matrix comparison returns either a derivation from the stated
-- circuit axioms or a proof that no such derivation exists.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Decision where

open import Relation.Nullary.Decidable using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Examples.Groups.CCX+HH.Syntactics using (Circuit)
import Examples.Groups.CCX+HH.Semantics as C
import Examples.Groups.CCX+HH.Presentation as P
import Examples.Groups.CCX+HH.Normalization as N
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_≟ᴰ_)
import Examples.Groups.CCX+HH.EncodingSemantics.DecidableMatrix as Matrix

infix 4 _≟_

_≟_ : ∀ {n} (u v : Circuit n) → Dec (u P.≈ v)
u ≟ v with Matrix.equality _≟ᴰ_ (C.interpret u) (C.interpret v)
... | yes eq = yes (P.completeness {u = u} {v = v} eq)
... | no neq = no (λ proof → neq (P.soundness {u = u} {v = v} proof))

normal-equality : ∀ {n} (u v : Circuit n) → Dec (N.nf u ≡ N.nf v)
normal-equality u v with u ≟ v
... | yes eq = yes (N.cong eq)
... | no neq = no (λ eq → neq (N.complete eq))
