------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_ ; auto)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Presentation.Tactics.Lists
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open import Presentation.Tactics.Words

open Monoid-Equational
open Rewriting
open Associative
open InContext

open import Presentation.Tactics.Lists using (MaybeEq ; _=m?_ ; isJust ; fromJust)
open import Examples.Groups.Clifford+CS-3qubit.MaybeEq-Instances
open import Examples.Groups.Clifford+CS-3qubit.CosetNF
open import Examples.Groups.Clifford+CS-3qubit.Gate

open import Examples.Groups.Clifford+CS-3qubit.Step7.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step7.Order

module Examples.Groups.Clifford+CS-3qubit.Step7.MvI where

  mvI-step : Step-Function Gate Rel
  mvI-step (iI-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ xs) = just (xs , at-head (axiom ax-iI-iI-iI-iI=ε))
  mvI-step (iI-gen ∷ CCX0-gen ∷ xs) = just (CCX0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CCX0=CCX0-iI))
  mvI-step (iI-gen ∷ CX01-gen ∷ xs) = just (CX01-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CX01=CX01-iI))
  mvI-step (iI-gen ∷ X0-gen ∷ xs) = just (X0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-X0=X0-iI))
  mvI-step (iI-gen ∷ Swap01-gen ∷ xs) = just (Swap01-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-Swap01=Swap01-iI))
  mvI-step (iI-gen ∷ Swap12-gen ∷ xs) = just (Swap12-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-Swap12=Swap12-iI))
  mvI-step (iI-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-S0=S0-iI))
  mvI-step (iI-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CS01=CS01-iI))
  mvI-step (iI-gen ∷ CCZ-gen ∷ xs) = just (CCZ-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CCZ=CCZ-iI))
  mvI-step (iI-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-K0=K0-iI))
  mvI-step _ = nothing

  module mvI = Rewriting.Step (step-cong mvI-step)

  module mvID = Rewriting.Step (step-cong (def-step then mvI-step))
