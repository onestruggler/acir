------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
--
-- K0QD-act's clauses are in PD6-1 .. PD6-3, one function per generator.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_ ; auto)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
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
open import Examples.Groups.Clifford+CS-3qubit.Gate
open import Examples.Groups.Clifford+CS-3qubit.CosetNF as CosetNF
open CosetNF.Legacy

open import Examples.Groups.Clifford+CS-3qubit.Step3.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD3
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD4
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD5

open import Examples.Groups.Clifford+CS-3qubit.Step3.PD6-1
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD6-2
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD6-3

module Examples.Groups.Clifford+CS-3qubit.Step3.PD6 where

  K0QD-act : let X = Gate in let Γ = Rel in (g : X) -> (rep : Word X) ->  Maybe (∃ λ (rep' : Word X) -> ∃ λ (g' : Word X) -> Γ ⊢ [ g ]ʷ • rep === rep' • g')
  K0QD-act iI-gen rep = K0QD-act-iI-gen rep
  K0QD-act S0-gen rep = K0QD-act-S0-gen rep
  K0QD-act S1-gen rep = K0QD-act-S1-gen rep
  K0QD-act S2-gen rep = K0QD-act-S2-gen rep
  K0QD-act CS01-gen rep = K0QD-act-CS01-gen rep
  K0QD-act CS02-gen rep = K0QD-act-CS02-gen rep
  K0QD-act CS12-gen rep = K0QD-act-CS12-gen rep
  K0QD-act CCZ-gen rep = K0QD-act-CCZ-gen rep
  K0QD-act K0-gen rep = K0QD-act-K0-gen rep
  K0QD-act X0-gen rep = K0QD-act-X0-gen rep
  K0QD-act X1-gen rep = K0QD-act-X1-gen rep
  K0QD-act X2-gen rep = K0QD-act-X2-gen rep
  K0QD-act CX10-gen rep = K0QD-act-CX10-gen rep
  K0QD-act CX12-gen rep = K0QD-act-CX12-gen rep
  K0QD-act CX20-gen rep = K0QD-act-CX20-gen rep
  K0QD-act CX21-gen rep = K0QD-act-CX21-gen rep
  K0QD-act CCX0-gen rep = K0QD-act-CCX0-gen rep
  K0QD-act Swap12-gen rep = K0QD-act-Swap12-gen rep
  K0QD-act CK10-gen rep = K0QD-act-CK10-gen rep
  K0QD-act CK20-gen rep = K0QD-act-CK20-gen rep
  K0QD-act CCK'-gen rep = K0QD-act-CCK'-gen rep
  K0QD-act _ _ = nothing

  module K0QD = CosAct' (record { nf = PD.nfhn' ; lemma-nf = PD.lemma-nfhn' }) K0QD-act (\ x y -> nothing)


