------------------------------------------------------------------------
-- Presentations of groups
--
-- Sₙ as a PROP: the swap rules on their own wires, padded by
-- Circuit.TopPad, give the same congruence as Circuit.Prop's swap rules
-- at every width, lifted by Lift-To-Prop
--
-- An instance of Circuit.Prop.TopPad with no family rules: the
-- relation of Symmetric-Prop is empty, so the swap rules are all there
-- is, and Circuit.Prop.TopPad has them already.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric-Prop.TopPad where

open import Data.Nat using (ℕ)
open import Presentation.Construct.Base using (EmptyRel)
open import Word.Base using (WRel)

import Circuit.Prop.TopPad

open import Examples.Groups.Symmetric-Prop.Syntactics

-- No rules of its own, on its own wires either.
_Base,_===_ : (n : ℕ) → WRel (Gen n)
_Base,_===_ n = EmptyRel

module P = Circuit.Prop.TopPad Gate σ-gate
module E = P.Lift≅Top-Pad-Prop _SRel,_===_ _Base,_===_

open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)

------------------------------------------------------------------------
-- The two have the same rules, and so the same congruence

same : E.E.SameRules
same = E.same record { pad = λ () ; unpad = λ () ; srel-⇓ = λ () }

open E.E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.E.Equivalent.Iso same grouplike public using (glᵀ ; lr≅tp)
