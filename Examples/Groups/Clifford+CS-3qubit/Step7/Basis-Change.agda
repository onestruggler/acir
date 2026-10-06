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

module Examples.Groups.Clifford+CS-3qubit.Step7.Basis-Change where

  lemma-Swap12-CCX2=CCX1-Swap12 : Rel ⊢ Swap12 • CCX2 === CCX1 • Swap12
  lemma-Swap12-CCX2=CCX1-Swap12 = axiom ax-Swap12-CCX2=CCX1-Swap12

  lemma-Swap12-CCX1=CCX2-Swap12 : Rel ⊢ Swap12 • CCX1 === CCX2 • Swap12
  lemma-Swap12-CCX1=CCX2-Swap12 = axiom ax-Swap12-CCX1=CCX2-Swap12 -- ListNF

  lemma-Swap12-CX01=CX02-Swap12 : Rel ⊢ Swap12 • CX01 === CX02 • Swap12
  lemma-Swap12-CX01=CX02-Swap12 = axiom ax-Swap12-CX01=CX02-Swap12 -- ListNF
  
  lemma-Swap12-CX02=CX01-Swap12 : Rel ⊢ Swap12 • CX02 === CX01 • Swap12
  lemma-Swap12-CX02=CX01-Swap12 = axiom ax-Swap12-CX02=CX01-Swap12 -- ListNF


  lemma-Swap12-CX10=CX20-Swap12 : Rel ⊢ Swap12 • CX10 === CX20 • Swap12
  lemma-Swap12-CX10=CX20-Swap12 = axiom ax-Swap12-CX10=CX20-Swap12 -- ListNF
  lemma-Swap12-CX20=CX10-Swap12 : Rel ⊢ Swap12 • CX20 === CX10 • Swap12
  lemma-Swap12-CX20=CX10-Swap12 = axiom ax-Swap12-CX20=CX10-Swap12 -- ListNF.listnfeq'
  lemma-Swap12-CCX0=CCX0-Swap12 : Rel ⊢ Swap12 • CCX0 === CCX0 • Swap12
  lemma-Swap12-CCX0=CCX0-Swap12 = axiom ax-Swap12-CCX0=CCX0-Swap12 -- ListNF.listnfeq'
  
  
  lemma-Swap12-X1=X2-Swap12 : Rel ⊢ Swap12 • X1 === X2 • Swap12
  lemma-Swap12-X1=X2-Swap12 = axiom ax-Swap12-X1=X2-Swap12 -- ListNF.listnfeq'


  lemma-Swap12-X2=X1-Swap12 : Rel ⊢ Swap12 • X2 === X1 • Swap12
  lemma-Swap12-X2=X1-Swap12 = axiom ax-Swap12-X2=X1-Swap12 -- ListNF.listnfeq'
  
  mvSwap12-step : Step-Function Gate Rel
  mvSwap12-step (Swap12-gen ∷ Swap12-gen ∷ xs) = just (xs , at-head (axiom ax-Swap12-Swap12=ε))
  mvSwap12-step (Swap12-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-K0=K0-Swap12))
  mvSwap12-step (Swap12-gen ∷ X0-gen ∷ xs) = just (X0-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-X0=X0-Swap12))
  mvSwap12-step (Swap12-gen ∷ X1-gen ∷ xs) = just (X2-gen ∷ Swap12-gen ∷ xs , at-head (lemma-Swap12-X1=X2-Swap12))
  mvSwap12-step (Swap12-gen ∷ X2-gen ∷ xs) = just (X1-gen ∷ Swap12-gen ∷ xs , at-head (lemma-Swap12-X2=X1-Swap12))
  mvSwap12-step (Swap12-gen ∷ CCZ-gen ∷ xs) = just (CCZ-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CCZ=CCZ-Swap12))
  mvSwap12-step (Swap12-gen ∷ CCX0-gen ∷ xs) = just (CCX0-gen ∷ Swap12-gen ∷ xs , at-head (lemma-Swap12-CCX0=CCX0-Swap12))
  mvSwap12-step (Swap12-gen ∷ CCX2-gen ∷ xs) = just (CCX1-gen ∷ Swap12-gen ∷ xs , at-head lemma-Swap12-CCX2=CCX1-Swap12)
  mvSwap12-step (Swap12-gen ∷ CCX1-gen ∷ xs) = just (CCX2-gen ∷ Swap12-gen ∷ xs , at-head lemma-Swap12-CCX1=CCX2-Swap12)
  mvSwap12-step (Swap12-gen ∷ CS01-gen ∷ xs) = just (CS02-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CS01=CS02-Swap12))
  mvSwap12-step (Swap12-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CS12=CS12-Swap12))
  mvSwap12-step (Swap12-gen ∷ CS02-gen ∷ xs) = just (CS01-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CS02=CS01-Swap12))
  mvSwap12-step (Swap12-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-S0=S0-Swap12))
  mvSwap12-step (Swap12-gen ∷ S1-gen ∷ xs) = just (S2-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-S1=S2-Swap12))
  mvSwap12-step (Swap12-gen ∷ S2-gen ∷ xs) = just (S1-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-S2=S1-Swap12))
  mvSwap12-step (Swap12-gen ∷ iI-gen ∷ xs) = just (iI-gen ∷ Swap12-gen ∷ xs , at-head (symm (axiom ax-iI-Swap12=Swap12-iI)))
  mvSwap12-step (Swap12-gen ∷ CX01-gen ∷ xs) = just (CX02-gen ∷ Swap12-gen ∷ xs , at-head lemma-Swap12-CX01=CX02-Swap12)
  mvSwap12-step (Swap12-gen ∷ CX02-gen ∷ xs) = just (CX01-gen ∷ Swap12-gen ∷ xs , at-head lemma-Swap12-CX02=CX01-Swap12)
  mvSwap12-step (Swap12-gen ∷ CX10-gen ∷ xs) = just (CX20-gen ∷ Swap12-gen ∷ xs , at-head (lemma-Swap12-CX10=CX20-Swap12))
  mvSwap12-step (Swap12-gen ∷ CX20-gen ∷ xs) = just (CX10-gen ∷ Swap12-gen ∷ xs , at-head (lemma-Swap12-CX20=CX10-Swap12))
  mvSwap12-step (Swap12-gen ∷ CX12-gen ∷ xs) = just (CX21-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CX12=CX21-Swap12))
  mvSwap12-step (Swap12-gen ∷ CX21-gen ∷ xs) = just (CX12-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CX21=CX12-Swap12))
  mvSwap12-step _ = nothing

  module MvSwap12 = Rewriting.Step (step-cong mvSwap12-step)

  open Basis-Change2 mvSwap12-step public


  lemma-Swap01-CCX1=CCX0-Swap01 : Rel ⊢ Swap01 • CCX1 === CCX0 • Swap01
  lemma-Swap01-CCX1=CCX0-Swap01 =
    equational Swap01 • CCX1
      by right trans (symm right-unit) (symm (cong refl (axiom ax-Swap01-Swap01=ε)))
    equals Swap01 • CCX1 • Swap01 • Swap01
      by general-assoc auto
    equals Swap01 • (CCX1 • Swap01) • Swap01
      by right left symm (axiom ax-Swap01-CCX0=CCX1-Swap01)
    equals Swap01 • (Swap01 • CCX0) • Swap01
      by general-assoc auto
    equals (Swap01 • Swap01) • CCX0 • Swap01
      by trans (cong (axiom ax-Swap01-Swap01=ε) refl) left-unit
    equals CCX0 • Swap01

  lemma-Swap01-CCX0=CCX1-Swap01 : Rel ⊢ Swap01 • CCX0 === CCX1 • Swap01
  lemma-Swap01-CCX0=CCX1-Swap01 = axiom ax-Swap01-CCX0=CCX1-Swap01


  lemma-Swap01-CX20=CX21-Swap01 : Rel ⊢ Swap01 • CX20 === CX21 • Swap01
  lemma-Swap01-CX20=CX21-Swap01 = axiom ax-Swap01-CX20=CX21-Swap01 -- ListNF.listnfeq'

  lemma-Swap01-CCX2=CCX2-Swap01 : Rel ⊢ Swap01 • CCX2 === CCX2 • Swap01
  lemma-Swap01-CCX2=CCX2-Swap01 = axiom ax-Swap01-CCX2=CCX2-Swap01 -- ListNF.listnfeq'

  lemma-Swap01-CX12=CX02-Swap01 : Rel ⊢ Swap01 • CX12 === CX02 • Swap01
  lemma-Swap01-CX12=CX02-Swap01 = axiom ax-Swap01-CX12=CX02-Swap01 -- ListNF.listnfeq'
  lemma-Swap01-CX02=CX12-Swap01 : Rel ⊢ Swap01 • CX02 === CX12 • Swap01
  lemma-Swap01-CX02=CX12-Swap01 = axiom ax-Swap01-CX02=CX12-Swap01 -- ListNF.listnfeq'
  lemma-Swap01-CCX0=CCX0-Swap01 : Rel ⊢ Swap01 • CCX0 === CCX1 • Swap01
  lemma-Swap01-CCX0=CCX0-Swap01 = axiom ax-Swap01-CCX0=CCX1-Swap01 -- ListNF.listnfeq'
  
  lemma-Swap01-X0=X1-Swap01 : Rel ⊢ Swap01 • X0 === X1 • Swap01
  lemma-Swap01-X0=X1-Swap01 = axiom ax-Swap01-X0=X1-Swap01 -- ListNF.listnfeq'

  lemma-Swap01-X1=X0-Swap01 : Rel ⊢ Swap01 • X1 === X0 • Swap01
  lemma-Swap01-X1=X0-Swap01 = axiom ax-Swap01-X1=X0-Swap01
  
  lemma-Swap01-CX21=CX20-Swap01 : Rel ⊢ Swap01 • CX21 === CX20 • Swap01
  lemma-Swap01-CX21=CX20-Swap01 = axiom ax-Swap01-CX21=CX20-Swap01 -- ListNF.listnfeq'
  lemma-CX01-CX10-CX01=Swap01 : Rel ⊢ CX01 • CX10 • CX01 === Swap01
  lemma-CX01-CX10-CX01=Swap01 = symm (axiom ax-Swap01=CX01-CX10-CX01) -- ListNF.listnfeq'


  mvSwap01-step : Step-Function Gate Rel
  mvSwap01-step (Swap01-gen ∷ Swap01-gen ∷ xs) = just (xs , at-head (axiom ax-Swap01-Swap01=ε))
  mvSwap01-step (Swap01-gen ∷ K0-gen ∷ Swap01-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ Swap01-gen ∷ K0-gen ∷ Swap01-gen ∷ xs , at-head (axiom ax-Swap01-K0-Swap01-K0=K0-Swap01-K0-Swap01))
  mvSwap01-step (Swap01-gen ∷ X2-gen ∷ xs) = just (X2-gen ∷ Swap01-gen ∷ xs , at-head (axiom ax-Swap01-X2=X2-Swap01))
  mvSwap01-step (Swap01-gen ∷ X0-gen ∷ xs) = just (X1-gen ∷ Swap01-gen ∷ xs , at-head (lemma-Swap01-X0=X1-Swap01))
  mvSwap01-step (Swap01-gen ∷ X1-gen ∷ xs) = just (X0-gen ∷ Swap01-gen ∷ xs , at-head (lemma-Swap01-X1=X0-Swap01))
  mvSwap01-step (Swap01-gen ∷ CCZ-gen ∷ xs) = just (CCZ-gen ∷ Swap01-gen ∷ xs , at-head (axiom ax-Swap01-CCZ=CCZ-Swap01))
  mvSwap01-step (Swap01-gen ∷ CCX0-gen ∷ xs) = just (CCX1-gen ∷ Swap01-gen ∷ xs , at-head (lemma-Swap01-CCX0=CCX1-Swap01))
  mvSwap01-step (Swap01-gen ∷ CCX1-gen ∷ xs) = just (CCX0-gen ∷ Swap01-gen ∷ xs , at-head lemma-Swap01-CCX1=CCX0-Swap01)
  mvSwap01-step (Swap01-gen ∷ CCX2-gen ∷ xs) = just (CCX2-gen ∷ Swap01-gen ∷ xs , at-head lemma-Swap01-CCX2=CCX2-Swap01)
  mvSwap01-step (Swap01-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ Swap01-gen ∷ xs , at-head (axiom ax-Swap01-CS01=CS01-Swap01))
  mvSwap01-step (Swap01-gen ∷ CS02-gen ∷ xs) = just (CS12-gen ∷ Swap01-gen ∷ xs , at-head (axiom ax-Swap01-CS02=CS12-Swap01))
  mvSwap01-step (Swap01-gen ∷ CS12-gen ∷ xs) = just (CS02-gen ∷ Swap01-gen ∷ xs , at-head (axiom ax-Swap01-CS12=CS02-Swap01))
  mvSwap01-step (Swap01-gen ∷ S0-gen ∷ xs) = just (S1-gen ∷ Swap01-gen ∷ xs , at-head (axiom ax-Swap01-S0=S1-Swap01))
  mvSwap01-step (Swap01-gen ∷ S1-gen ∷ xs) = just (S0-gen ∷ Swap01-gen ∷ xs , at-head (axiom ax-Swap01-S1=S0-Swap01))
  mvSwap01-step (Swap01-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ Swap01-gen ∷ xs , at-head (axiom ax-Swap01-S2=S2-Swap01))
  mvSwap01-step (Swap01-gen ∷ iI-gen ∷ xs) = just (iI-gen ∷ Swap01-gen ∷ xs , at-head (symm (axiom ax-iI-Swap01=Swap01-iI)))
  mvSwap01-step (Swap01-gen ∷ CX10-gen ∷ xs) = just (CX01-gen ∷ Swap01-gen ∷ xs , at-head (axiom ax-Swap01-CX10=CX01-Swap01))
  mvSwap01-step (Swap01-gen ∷ CX01-gen ∷ xs) = just (CX10-gen ∷ Swap01-gen ∷ xs , at-head (axiom ax-Swap01-CX01=CX10-Swap01))
  mvSwap01-step (Swap01-gen ∷ CX12-gen ∷ xs) = just (CX02-gen ∷ Swap01-gen ∷ xs , at-head (lemma-Swap01-CX12=CX02-Swap01))
  mvSwap01-step (Swap01-gen ∷ CX21-gen ∷ xs) = just (CX20-gen ∷ Swap01-gen ∷ xs , at-head (lemma-Swap01-CX21=CX20-Swap01))
  mvSwap01-step (Swap01-gen ∷ CX02-gen ∷ xs) = just (CX12-gen ∷ Swap01-gen ∷ xs , at-head (lemma-Swap01-CX02=CX12-Swap01))
  mvSwap01-step (Swap01-gen ∷ CX20-gen ∷ xs) = just (CX21-gen ∷ Swap01-gen ∷ xs , at-head (lemma-Swap01-CX20=CX21-Swap01))
  mvSwap01-step _ = nothing

  module MvSwap01 = Rewriting.Step (step-cong mvSwap01-step)

  module B01 =  Basis-Change2 mvSwap01-step

  swap012-step : Step-Function Gate Rel
  swap012-step (Swap12-gen ∷ Swap01-gen ∷ Swap12-gen ∷ xs) = just (Swap01-gen ∷ Swap12-gen ∷ Swap01-gen ∷ xs , at-head (axiom ax-Swap12-Swap01-Swap12=Swap01-Swap12-Swap01))
  swap012-step _ = nothing

  swap-step = mvSwap01-step then mvSwap12-step then swap012-step
  
  module MvSwap = Rewriting.Step (step-cong (swap-step))

  open MvSwap renaming (up-to-rewrite to up-to-swap) public
  
  module B02 =  Basis-Change2 (mvSwap01-step then mvSwap12-step then swap012-step)

  
