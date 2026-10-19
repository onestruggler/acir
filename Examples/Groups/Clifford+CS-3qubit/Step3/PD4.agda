------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
--
-- p105-act's clauses are in PD4-1 .. PD4-2, one function per generator.
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

open import Examples.Groups.Clifford+CS-3qubit.Step3.PD4-1
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD4-2

module Examples.Groups.Clifford+CS-3qubit.Step3.PD4 where

p105-act : let X = Gate in let Γ = Rel in (g : X) -> (rep : Word X) ->  Maybe (∃ λ (rep' : Word X) -> ∃ λ (g' : Word X) -> Γ ⊢ [ g ]ʷ • rep === rep' • g')
p105-act Swap01-gen rep = p105-act-Swap01-gen rep
p105-act CX01-gen rep = p105-act-CX01-gen rep
p105-act CX02-gen rep = p105-act-CX02-gen rep
p105-act CCX1-gen rep = p105-act-CCX1-gen rep
p105-act CCX2-gen rep = p105-act-CCX2-gen rep
p105-act X1-gen rep = p105-act-X1-gen rep
p105-act X2-gen rep = p105-act-X2-gen rep
p105-act CX12-gen rep = p105-act-CX12-gen rep
p105-act CX21-gen rep = p105-act-CX21-gen rep
p105-act Swap12-gen rep = p105-act-Swap12-gen rep
p105-act X0-gen rep = p105-act-X0-gen rep
p105-act CX10-gen rep = p105-act-CX10-gen rep
p105-act CX20-gen rep = p105-act-CX20-gen rep
p105-act CCX0-gen rep = p105-act-CCX0-gen rep
p105-act _ _ = nothing

module P = CosAct' (record { nf = P384.nfhn' ; lemma-nf = P384.lemma-nfhn' }) p105-act (\ x y -> nothing)

