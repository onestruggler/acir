------------------------------------------------------------------------
-- Presentations of groups
--
-- Decidable circuit equality in the complete relation at every width.
-- Exact comparison over Z[1/sqrt(2)] returns either a derivation from
-- the circuit axioms or a proof that no such derivation exists.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.Decision where

open import Relation.Nullary.Decidable using (Dec ; yes ; no)
open import Examples.Groups.CCX+H.Syntactics using (Circuit)
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as C
import Examples.Groups.CCX+H.Presentation as P
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (_≟ᴰ_)
import Examples.Groups.CCX+HH.EncodingSemantics.DecidableMatrix as Matrix

infix 4 _≟_

_≟_ : ∀ {n} (u v : Circuit n) → Dec (P._⊢_≈_ n u v)
_≟_ {n} u v with Matrix.equality _≟ᴰ_ (C.interpret u) (C.interpret v)
... | yes eq = yes (P.complete n {u} {v} eq)
... | no neq = no (λ proof → neq (P.sound n {u} {v} proof))
