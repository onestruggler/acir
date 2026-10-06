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

open import Examples.Groups.Clifford+CS-3qubit.Step5.Rel

module Examples.Groups.Clifford+CS-3qubit.Step5.S8 where

  isS1 : Gate -> Bool
  isS1 _ = false

  isS2 : Gate -> Bool
  isS2 CCX0-gen = true
  isS2 x = isS1 x


  isS3 : Gate -> Bool
  isS3 CCX1-gen = true
  isS3 x = isS2 x

  isS4 : Gate -> Bool
  isS4 CCX2-gen = true
  isS4 x = isS3 x

  isS5 : Gate -> Bool
  isS5 CX01-gen = true
  isS5 x = isS4 x

  isS6 : Gate -> Bool
  isS6 CX10-gen = true
  isS6 x = isS5 x

  isS7 : Gate -> Bool
  isS7 CX02-gen = true
  isS7 CX20-gen = true
  isS7 CX12-gen = true
  isS7 CX21-gen = true
  isS7 x = isS6 x

  isS8 : Gate -> Bool
  isS8 X0-gen = true
  isS8 X1-gen = true
  isS8 X2-gen = true
  isS8 x = isS7 x

 
  S2-step : Step-Function Gate Rel
  S2-step (CCX0-gen ∷ CCX0-gen ∷ xs) = just (xs , at-head (axiom ax-CCX0-CCX0=ε))
  S2-step _ = nothing

  module S2 = Rewriting.Step (step-cong S2-step)

  S3-S2-act : let X = Gate in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S3-S2-act CCX1-gen [] = just ( CCX1-gen ∷ [] , [] , refl )
  S3-S2-act CCX1-gen (CCX1-gen ∷ [] ) = just ( [] , [] , up-to-assoc auto (axiom ax-CCX1-CCX1=ε) )
  S3-S2-act CCX1-gen (CCX0-gen ∷ CCX1-gen ∷ [] ) = just ( CCX0-gen ∷ CCX1-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CCX0-CCX1=CCX0-CCX1-CCX0) )
  S3-S2-act CCX0-gen [] = just ( [] , CCX0-gen ∷ [] , refl )
  S3-S2-act CCX0-gen (CCX1-gen ∷ [] ) = just ( CCX0-gen ∷ CCX1-gen ∷ [] , [] , refl )
  S3-S2-act CCX0-gen (CCX0-gen ∷ CCX1-gen ∷ [] ) = just ( CCX1-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CCX0-CCX0-CCX1=CCX1) )
  S3-S2-act _ _ = nothing

  module S3 = CosAct (record { listnf = (S2.multistep 1000) ; lemma-listnf = (S2.lemma-multistep 1000) }) S3-S2-act (\ x y -> nothing)

  S4-S3-act : let X = Gate in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S4-S3-act CCX2-gen [] = just ( CCX2-gen ∷ [] , [] , refl )
  S4-S3-act CCX2-gen (CCX2-gen ∷ [] ) = just ( [] , [] , up-to-assoc auto (axiom ax-CCX2-CCX2=ε) )
  S4-S3-act CCX2-gen (CCX1-gen ∷ CCX2-gen ∷ [] ) = just ( CCX1-gen ∷ CCX2-gen ∷ [] , CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CCX1-CCX2=CCX1-CCX2-CCX1) )
  S4-S3-act CCX2-gen (CCX0-gen ∷ CCX2-gen ∷ [] ) = just ( CCX0-gen ∷ CCX2-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CCX0-CCX2=CCX0-CCX2-CCX0) )
  S4-S3-act CCX1-gen [] = just ( [] , CCX1-gen ∷ [] , refl )
  S4-S3-act CCX1-gen (CCX2-gen ∷ [] ) = just ( CCX1-gen ∷ CCX2-gen ∷ [] , [] , refl )
  S4-S3-act CCX1-gen (CCX1-gen ∷ CCX2-gen ∷ [] ) = just ( CCX2-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CCX1-CCX1-CCX2=CCX2) )
  S4-S3-act CCX1-gen (CCX0-gen ∷ CCX2-gen ∷ [] ) = just ( CCX0-gen ∷ CCX2-gen ∷ [] , CCX0-gen ∷ CCX1-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CCX0-CCX2=CCX0-CCX2-CCX0-CCX1-CCX0) )
  S4-S3-act CCX0-gen [] = just ( [] , CCX0-gen ∷ [] , refl )
  S4-S3-act CCX0-gen (CCX2-gen ∷ [] ) = just ( CCX0-gen ∷ CCX2-gen ∷ [] , [] , refl )
  S4-S3-act CCX0-gen (CCX1-gen ∷ CCX2-gen ∷ [] ) = just ( CCX1-gen ∷ CCX2-gen ∷ [] , CCX0-gen ∷ CCX1-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CCX1-CCX2=CCX1-CCX2-CCX0-CCX1-CCX0) )
  S4-S3-act CCX0-gen (CCX0-gen ∷ CCX2-gen ∷ [] ) = just ( CCX2-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CCX0-CCX0-CCX2=CCX2) )
  S4-S3-act _ _ = nothing


  module S4 = CosAct (record { listnf = S3.lactnf ; lemma-listnf = S3.lemma-lactnf }) S4-S3-act (\ x y -> nothing)

  S5-S4-act : let X = Gate in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S5-S4-act CX01-gen [] = just ( CX01-gen ∷ [] , [] , refl )
  S5-S4-act CX01-gen (CX01-gen ∷ [] ) = just ( [] , [] , up-to-assoc auto (axiom ax-CX01-CX01=ε) )
  S5-S4-act CX01-gen (CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] ) = just ( CCX2-gen ∷ CX01-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CX01-CX01-CCX2-CX01=CCX2-CX01) )
  S5-S4-act CX01-gen (CCX2-gen ∷ CX01-gen ∷ [] ) = just ( CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] , [] , refl )
  S5-S4-act CX01-gen (CCX0-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] ) = just ( CCX0-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] , CCX1-gen ∷ CCX2-gen ∷ CCX1-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX1-CCX2-CCX1-CCX0) )
  S5-S4-act CCX2-gen [] = just ( [] , CCX2-gen ∷ [] , refl )
  S5-S4-act CCX2-gen (CX01-gen ∷ [] ) = just ( CCX2-gen ∷ CX01-gen ∷ [] , [] , refl )
  S5-S4-act CCX2-gen (CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] ) = just ( CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] , CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CX01-CCX2-CX01=CX01-CCX2-CX01-CCX2) )
  S5-S4-act CCX2-gen (CCX2-gen ∷ CX01-gen ∷ [] ) = just ( CX01-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CCX2-CCX2-CX01=CX01) )
  S5-S4-act CCX2-gen (CCX0-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] ) = just ( CCX0-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] , CCX0-gen ∷ CCX1-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX0-CCX1-CCX0) )
  S5-S4-act CCX1-gen [] = just ( [] , CCX1-gen ∷ [] , refl )
  S5-S4-act CCX1-gen (CX01-gen ∷ [] ) = just ( CX01-gen ∷ [] , CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CX01=CX01-CCX1) )
  S5-S4-act CCX1-gen (CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] ) = just ( CCX2-gen ∷ CX01-gen ∷ [] , CCX1-gen ∷ CCX2-gen ∷ CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CX01-CCX2-CX01=CCX2-CX01-CCX1-CCX2-CCX1) )
  S5-S4-act CCX1-gen (CCX2-gen ∷ CX01-gen ∷ [] ) = just ( CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] , CCX1-gen ∷ CCX2-gen ∷ CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CCX2-CX01=CX01-CCX2-CX01-CCX1-CCX2-CCX1) )
  S5-S4-act CCX1-gen (CCX0-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] ) = just ( CCX0-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX0) )
  S5-S4-act CCX0-gen [] = just ( [] , CCX0-gen ∷ [] , refl )
  S5-S4-act CCX0-gen (CX01-gen ∷ [] ) = just ( CX01-gen ∷ [] , CCX0-gen ∷ CCX1-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CX01=CX01-CCX0-CCX1-CCX0) )
  S5-S4-act CCX0-gen (CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] ) = just ( CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CX01-CCX2-CX01=CX01-CCX2-CX01-CCX0) )
  S5-S4-act CCX0-gen (CCX2-gen ∷ CX01-gen ∷ [] ) = just ( CCX0-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] , [] , refl )
  S5-S4-act CCX0-gen (CCX0-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] ) = just ( CCX2-gen ∷ CX01-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CCX0-CCX0-CCX2-CX01=CCX2-CX01) )
  S5-S4-act _ _ = nothing

  module S5 = CosAct (record { listnf = S4.lactnf ; lemma-listnf = S4.lemma-lactnf }) S5-S4-act (\ x y -> nothing)

  S6-S5-act : let X = Gate in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S6-S5-act CX10-gen [] = just ( CX10-gen ∷ [] , [] , refl )
  S6-S5-act CX10-gen (CX10-gen ∷ [] ) = just ( [] , [] , up-to-assoc auto (axiom ax-CX10-CX10=ε) )
  S6-S5-act CX10-gen (CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CCX2-gen ∷ CX10-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CX10-CX10-CCX2-CX10=CCX2-CX10) )
  S6-S5-act CX10-gen (CX01-gen ∷ CX10-gen ∷ [] ) = just ( CX01-gen ∷ CX10-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CX01-CX10=CX01-CX10-CX01) )
  S6-S5-act CX10-gen (CX01-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CX01-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CX01-CCX2-CX10=CX01-CCX2-CX10-CX01) )
  S6-S5-act CX10-gen (CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] , [] , refl )
  S6-S5-act CX01-gen [] = just ( [] , CX01-gen ∷ [] , refl )
  S6-S5-act CX01-gen (CX10-gen ∷ [] ) = just ( CX01-gen ∷ CX10-gen ∷ [] , [] , refl )
  S6-S5-act CX01-gen (CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-CX10-CCX2-CX10=CX10-CCX2-CX10-CX01) )
  S6-S5-act CX01-gen (CX01-gen ∷ CX10-gen ∷ [] ) = just ( CX10-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CX01-CX01-CX10=CX10) )
  S6-S5-act CX01-gen (CX01-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CCX2-gen ∷ CX10-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CX01-CX01-CCX2-CX10=CCX2-CX10) )
  S6-S5-act CX01-gen (CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CX01-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] , [] , refl )
  S6-S5-act CCX2-gen [] = just ( [] , CCX2-gen ∷ [] , refl )
  S6-S5-act CCX2-gen (CX10-gen ∷ [] ) = just ( CCX2-gen ∷ CX10-gen ∷ [] , [] , refl )
  S6-S5-act CCX2-gen (CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] , CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CX10-CCX2-CX10=CX10-CCX2-CX10-CCX2) )
  S6-S5-act CCX2-gen (CX01-gen ∷ CX10-gen ∷ [] ) = just ( CX01-gen ∷ CX10-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CX01-CX10=CX01-CX10-CX01-CCX2-CX01) )
  S6-S5-act CCX2-gen (CX01-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CX01-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CX01-CCX2-CX10=CX01-CCX2-CX10-CX01-CCX2-CX01) )
  S6-S5-act CCX2-gen (CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CX10-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CCX2-CCX2-CX10=CX10) )
  S6-S5-act CCX1-gen [] = just ( [] , CCX1-gen ∷ [] , refl )
  S6-S5-act CCX1-gen (CX10-gen ∷ [] ) = just ( CX10-gen ∷ [] , CCX0-gen ∷ CCX1-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CX10=CX10-CCX0-CCX1-CCX0) )
  S6-S5-act CCX1-gen (CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] , CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CX10-CCX2-CX10=CX10-CCX2-CX10-CCX1) )
  S6-S5-act CCX1-gen (CX01-gen ∷ CX10-gen ∷ [] ) = just ( CX01-gen ∷ CX10-gen ∷ [] , CCX0-gen ∷ CCX1-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CX01-CX10=CX01-CX10-CCX0-CCX1-CCX0) )
  S6-S5-act CCX1-gen (CX01-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CCX2-gen ∷ CX10-gen ∷ [] , CCX0-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX1-gen ∷ CCX2-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CX01-CCX2-CX10=CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0) )
  S6-S5-act CCX1-gen (CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CX01-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] , CCX0-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX1-gen ∷ CCX2-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CCX2-CX10=CX01-CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0) )
  S6-S5-act CCX0-gen [] = just ( [] , CCX0-gen ∷ [] , refl )
  S6-S5-act CCX0-gen (CX10-gen ∷ [] ) = just ( CX10-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CX10=CX10-CCX0) )
  S6-S5-act CCX0-gen (CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CCX2-gen ∷ CX10-gen ∷ [] , CCX0-gen ∷ CCX2-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CX10-CCX2-CX10=CCX2-CX10-CCX0-CCX2-CCX0) )
  S6-S5-act CCX0-gen (CX01-gen ∷ CX10-gen ∷ [] ) = just ( CX01-gen ∷ CX10-gen ∷ [] , CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CX01-CX10=CX01-CX10-CCX1) )
  S6-S5-act CCX0-gen (CX01-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CX01-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] , CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CX01-CCX2-CX10=CX01-CCX2-CX10-CCX1) )
  S6-S5-act CCX0-gen (CCX2-gen ∷ CX10-gen ∷ [] ) = just ( CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] , CCX0-gen ∷ CCX2-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CCX2-CX10=CX10-CCX2-CX10-CCX0-CCX2-CCX0) )
  S6-S5-act _ _ = nothing

  module S6 = CosAct (record { listnf = S5.lactnf ; lemma-listnf = S5.lemma-lactnf }) S6-S5-act (\ x y -> nothing)

  

  S7-S6-act : let X = Gate in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S7-S6-act CX02-gen [] = just ( [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX02=CX01-CCX2-CX01-CCX2) )
  S7-S6-act CX02-gen (CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX20-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CX02-CX02-CX20=CX20) )
  S7-S6-act CX02-gen (CX20-gen ∷ [] ) = just ( CX02-gen ∷ CX20-gen ∷ [] , [] , refl )
  S7-S6-act CX02-gen (CX12-gen ∷ CX21-gen ∷ [] ) = just ( CX12-gen ∷ CX21-gen ∷ [] , CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-CX12-CX21=CX12-CX21-CCX2-CX01-CCX2) )
  S7-S6-act CX02-gen (CX21-gen ∷ [] ) = just ( CX21-gen ∷ [] , CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-CX21=CX21-CCX2-CX01-CCX2) )
  S7-S6-act CX02-gen (CX21-gen ∷ CX20-gen ∷ [] ) = just ( CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-CX21-CX20=CX01-CX02-CX20-CX01) )
  S7-S6-act CX02-gen (CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX21-gen ∷ CX20-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-CX01-CX02-CX20=CX21-CX20-CX01) )
  S7-S6-act CX20-gen [] = just ( CX20-gen ∷ [] , [] , refl )
  S7-S6-act CX20-gen (CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX02-gen ∷ CX20-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CX02-CX20=CX02-CX20-CX01-CCX2-CX01-CCX2) )
  S7-S6-act CX20-gen (CX20-gen ∷ [] ) = just ( [] , [] , up-to-assoc auto (axiom ax-CX20-CX20=ε) )
  S7-S6-act CX20-gen (CX12-gen ∷ CX21-gen ∷ [] ) = just ( CX12-gen ∷ CX21-gen ∷ [] , CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CX12-CX21=CX12-CX21-CX10) )
  S7-S6-act CX20-gen (CX21-gen ∷ [] ) = just ( CX21-gen ∷ CX20-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CX20-CX21=CX21-CX20) )
  S7-S6-act CX20-gen (CX21-gen ∷ CX20-gen ∷ [] ) = just ( CX21-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CX20-CX21-CX20=CX21) )
  S7-S6-act CX20-gen (CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] , CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CX01-CX02-CX20=CX01-CX02-CX20-CCX2-CX01-CCX2) )
  S7-S6-act CX12-gen [] = just ( [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX12=CX10-CCX2-CX10-CCX2) )
  S7-S6-act CX12-gen (CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX02-gen ∷ CX20-gen ∷ [] , CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CX02-CX20=CX02-CX20-CCX2-CX10-CCX2) )
  S7-S6-act CX12-gen (CX20-gen ∷ [] ) = just ( CX20-gen ∷ [] , CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CX20=CX20-CCX2-CX10-CCX2) )
  S7-S6-act CX12-gen (CX12-gen ∷ CX21-gen ∷ [] ) = just ( CX21-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CX12-CX12-CX21=CX21) )
  S7-S6-act CX12-gen (CX21-gen ∷ [] ) = just ( CX12-gen ∷ CX21-gen ∷ [] , [] , refl )
  S7-S6-act CX12-gen (CX21-gen ∷ CX20-gen ∷ [] ) = just ( CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] , CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CX21-CX20=CX01-CX02-CX20-CCX2-CX10-CCX2-CX01) )
  S7-S6-act CX12-gen (CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX21-gen ∷ CX20-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CX01-CX02-CX20=CX21-CX20-CX01-CCX2-CX10-CCX2) )
  S7-S6-act CX21-gen [] = just ( CX21-gen ∷ [] , [] , refl )
  S7-S6-act CX21-gen (CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX02-gen ∷ CX20-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CX02-CX20=CX02-CX20-CX01) )
  S7-S6-act CX21-gen (CX20-gen ∷ [] ) = just ( CX21-gen ∷ CX20-gen ∷ [] , [] , refl )
  S7-S6-act CX21-gen (CX12-gen ∷ CX21-gen ∷ [] ) = just ( CX12-gen ∷ CX21-gen ∷ [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CX12-CX21=CX12-CX21-CX10-CCX2-CX10-CCX2) )
  S7-S6-act CX21-gen (CX21-gen ∷ [] ) = just ( [] , [] , up-to-assoc auto (axiom ax-CX21-CX21=ε) )
  S7-S6-act CX21-gen (CX21-gen ∷ CX20-gen ∷ [] ) = just ( CX20-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CX21-CX21-CX20=CX20) )
  S7-S6-act CX21-gen (CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CX01-CX02-CX20=CX01-CX02-CX20-CX01) )
  S7-S6-act CX10-gen [] = just ( [] , CX10-gen ∷ [] , refl )
  S7-S6-act CX10-gen (CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX02-gen ∷ CX20-gen ∷ [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CX02-CX20=CX02-CX20-CX10-CCX2-CX10-CCX2) )
  S7-S6-act CX10-gen (CX20-gen ∷ [] ) = just ( CX20-gen ∷ [] , CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CX20=CX20-CX10) )
  S7-S6-act CX10-gen (CX12-gen ∷ CX21-gen ∷ [] ) = just ( CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] , CX01-gen ∷ CX10-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CX12-CX21=CX01-CX02-CX20-CX01-CX10-CCX2-CX01-CCX2) )
  S7-S6-act CX10-gen (CX21-gen ∷ [] ) = just ( CX21-gen ∷ CX20-gen ∷ [] , CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CX21=CX21-CX20-CX10) )
  S7-S6-act CX10-gen (CX21-gen ∷ CX20-gen ∷ [] ) = just ( CX21-gen ∷ [] , CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CX21-CX20=CX21-CX10) )
  S7-S6-act CX10-gen (CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX12-gen ∷ CX21-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX10-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CX01-CX02-CX20=CX12-CX21-CX01-CCX2-CX10-CX01-CCX2) )
  S7-S6-act CX01-gen [] = just ( [] , CX01-gen ∷ [] , refl )
  S7-S6-act CX01-gen (CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] , [] , refl )
  S7-S6-act CX01-gen (CX20-gen ∷ [] ) = just ( CX21-gen ∷ CX20-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-CX20=CX21-CX20-CX01) )
  S7-S6-act CX01-gen (CX12-gen ∷ CX21-gen ∷ [] ) = just ( CX12-gen ∷ CX21-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-CX12-CX21=CX12-CX21-CX01-CCX2-CX01-CCX2) )
  S7-S6-act CX01-gen (CX21-gen ∷ [] ) = just ( CX21-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-CX21=CX21-CX01) )
  S7-S6-act CX01-gen (CX21-gen ∷ CX20-gen ∷ [] ) = just ( CX20-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-CX21-CX20=CX20-CX01) )
  S7-S6-act CX01-gen (CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX02-gen ∷ CX20-gen ∷ [] , [] , up-to-assoc auto (axiom ax-CX01-CX01-CX02-CX20=CX02-CX20) )
  S7-S6-act CCX2-gen [] = just ( [] , CCX2-gen ∷ [] , refl )
  S7-S6-act CCX2-gen (CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX02-gen ∷ CX20-gen ∷ [] , CCX0-gen ∷ CCX2-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CX02-CX20=CX02-CX20-CCX0-CCX2-CCX0) )
  S7-S6-act CCX2-gen (CX20-gen ∷ [] ) = just ( CX20-gen ∷ [] , CCX0-gen ∷ CCX2-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CX20=CX20-CCX0-CCX2-CCX0) )
  S7-S6-act CCX2-gen (CX12-gen ∷ CX21-gen ∷ [] ) = just ( CX12-gen ∷ CX21-gen ∷ [] , CCX1-gen ∷ CCX2-gen ∷ CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CX12-CX21=CX12-CX21-CCX1-CCX2-CCX1) )
  S7-S6-act CCX2-gen (CX21-gen ∷ [] ) = just ( CX21-gen ∷ [] , CCX1-gen ∷ CCX2-gen ∷ CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CX21=CX21-CCX1-CCX2-CCX1) )
  S7-S6-act CCX2-gen (CX21-gen ∷ CX20-gen ∷ [] ) = just ( CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] , CCX0-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX0-gen ∷ CCX1-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CX21-CX20=CX01-CX02-CX20-CCX0-CCX2-CX01-CCX0-CCX1-CCX0) )
  S7-S6-act CCX2-gen (CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX21-gen ∷ CX20-gen ∷ [] , CX01-gen ∷ CCX0-gen ∷ CCX2-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CX01-CX02-CX20=CX21-CX20-CX01-CCX0-CCX2-CCX0) )
  S7-S6-act CCX1-gen [] = just ( [] , CCX1-gen ∷ [] , refl )
  S7-S6-act CCX1-gen (CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX02-gen ∷ CX20-gen ∷ [] , CX01-gen ∷ CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CX02-CX20=CX02-CX20-CX01-CCX1) )
  S7-S6-act CCX1-gen (CX20-gen ∷ [] ) = just ( CX21-gen ∷ CX20-gen ∷ [] , CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CX20=CX21-CX20-CCX1) )
  S7-S6-act CCX1-gen (CX12-gen ∷ CX21-gen ∷ [] ) = just ( CX12-gen ∷ CX21-gen ∷ [] , CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CX12-CX21=CX12-CX21-CCX2) )
  S7-S6-act CCX1-gen (CX21-gen ∷ [] ) = just ( CX21-gen ∷ [] , CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CX21=CX21-CCX1) )
  S7-S6-act CCX1-gen (CX21-gen ∷ CX20-gen ∷ [] ) = just ( CX20-gen ∷ [] , CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CX21-CX20=CX20-CCX1) )
  S7-S6-act CCX1-gen (CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] , CX01-gen ∷ CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CX01-CX02-CX20=CX01-CX02-CX20-CX01-CCX1) )
  S7-S6-act CCX0-gen [] = just ( [] , CCX0-gen ∷ [] , refl )
  S7-S6-act CCX0-gen (CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX02-gen ∷ CX20-gen ∷ [] , CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CX02-CX20=CX02-CX20-CCX2) )
  S7-S6-act CCX0-gen (CX20-gen ∷ [] ) = just ( CX20-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CX20=CX20-CCX0) )
  S7-S6-act CCX0-gen (CX12-gen ∷ CX21-gen ∷ [] ) = just ( CX12-gen ∷ CX21-gen ∷ [] , CX10-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CX12-CX21=CX12-CX21-CX10-CCX0) )
  S7-S6-act CCX0-gen (CX21-gen ∷ [] ) = just ( CX21-gen ∷ CX20-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CX21=CX21-CX20-CCX0) )
  S7-S6-act CCX0-gen (CX21-gen ∷ CX20-gen ∷ [] ) = just ( CX21-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CX21-CX20=CX21-CCX0) )
  S7-S6-act CCX0-gen (CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] ) = just ( CX01-gen ∷ CX02-gen ∷ CX20-gen ∷ [] , CCX2-gen ∷ CX01-gen ∷ CCX1-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CX01-CX02-CX20=CX01-CX02-CX20-CCX2-CX01-CCX1-CCX2) )
  S7-S6-act _ _ = nothing

  module S7 = CosAct (record { listnf = S6.lactnf ; lemma-listnf = S6.lemma-lactnf }) S7-S6-act (\ x y -> nothing)

  S8-S7-act : let X = Gate in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S8-S7-act X0-gen [] = just ( X0-gen ∷ [] , [] , refl )
  S8-S7-act X0-gen (X0-gen ∷ [] ) = just ( [] , [] , up-to-assoc auto (axiom ax-X0-X0=ε) )
  S8-S7-act X0-gen (X0-gen ∷ X1-gen ∷ [] ) = just ( X1-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X0-X0-X1=X1) )
  S8-S7-act X0-gen (X0-gen ∷ X1-gen ∷ X2-gen ∷ [] ) = just ( X1-gen ∷ X2-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X0-X0-X1-X2=X1-X2) )
  S8-S7-act X0-gen (X0-gen ∷ X2-gen ∷ [] ) = just ( X2-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X0-X0-X2=X2) )
  S8-S7-act X0-gen (X1-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ [] , [] , refl )
  S8-S7-act X0-gen (X1-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ X2-gen ∷ [] , [] , refl )
  S8-S7-act X0-gen (X2-gen ∷ [] ) = just ( X0-gen ∷ X2-gen ∷ [] , [] , refl )
  S8-S7-act X1-gen [] = just ( X1-gen ∷ [] , [] , refl )
  S8-S7-act X1-gen (X0-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X1-X0=X0-X1) )
  S8-S7-act X1-gen (X0-gen ∷ X1-gen ∷ [] ) = just ( X0-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X1-X0-X1=X0) )
  S8-S7-act X1-gen (X0-gen ∷ X1-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X2-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X1-X0-X1-X2=X0-X2) )
  S8-S7-act X1-gen (X0-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ X2-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X1-X0-X2=X0-X1-X2) )
  S8-S7-act X1-gen (X1-gen ∷ [] ) = just ( [] , [] , up-to-assoc auto (axiom ax-X1-X1=ε) )
  S8-S7-act X1-gen (X1-gen ∷ X2-gen ∷ [] ) = just ( X2-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X1-X1-X2=X2) )
  S8-S7-act X1-gen (X2-gen ∷ [] ) = just ( X1-gen ∷ X2-gen ∷ [] , [] , refl )
  S8-S7-act X2-gen [] = just ( X2-gen ∷ [] , [] , refl )
  S8-S7-act X2-gen (X0-gen ∷ [] ) = just ( X0-gen ∷ X2-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X2-X0=X0-X2) )
  S8-S7-act X2-gen (X0-gen ∷ X1-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ X2-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X2-X0-X1=X0-X1-X2) )
  S8-S7-act X2-gen (X0-gen ∷ X1-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X2-X0-X1-X2=X0-X1) )
  S8-S7-act X2-gen (X0-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X2-X0-X2=X0) )
  S8-S7-act X2-gen (X1-gen ∷ [] ) = just ( X1-gen ∷ X2-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X2-X1=X1-X2) )
  S8-S7-act X2-gen (X1-gen ∷ X2-gen ∷ [] ) = just ( X1-gen ∷ [] , [] , up-to-assoc auto (axiom ax-X2-X1-X2=X1) )
  S8-S7-act X2-gen (X2-gen ∷ [] ) = just ( [] , [] , up-to-assoc auto (axiom ax-X2-X2=ε) )
  S8-S7-act CX01-gen [] = just ( [] , CX01-gen ∷ [] , refl )
  S8-S7-act CX01-gen (X0-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-X0=X0-X1-CX01) )
  S8-S7-act CX01-gen (X0-gen ∷ X1-gen ∷ [] ) = just ( X0-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-X0-X1=X0-CX01) )
  S8-S7-act CX01-gen (X0-gen ∷ X1-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X2-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-X0-X1-X2=X0-X2-CX01) )
  S8-S7-act CX01-gen (X0-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ X2-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-X0-X2=X0-X1-X2-CX01) )
  S8-S7-act CX01-gen (X1-gen ∷ [] ) = just ( X1-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-X1=X1-CX01) )
  S8-S7-act CX01-gen (X1-gen ∷ X2-gen ∷ [] ) = just ( X1-gen ∷ X2-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-X1-X2=X1-X2-CX01) )
  S8-S7-act CX01-gen (X2-gen ∷ [] ) = just ( X2-gen ∷ [] , CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-X2=X2-CX01) )
  S8-S7-act CX02-gen [] = just ( [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX02=CX01-CCX2-CX01-CCX2) )
  S8-S7-act CX02-gen (X0-gen ∷ [] ) = just ( X0-gen ∷ X2-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-X0=X0-X2-CX01-CCX2-CX01-CCX2) )
  S8-S7-act CX02-gen (X0-gen ∷ X1-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ X2-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-X0-X1=X0-X1-X2-CX01-CCX2-CX01-CCX2) )
  S8-S7-act CX02-gen (X0-gen ∷ X1-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-X0-X1-X2=X0-X1-CX01-CCX2-CX01-CCX2) )
  S8-S7-act CX02-gen (X0-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-X0-X2=X0-CX01-CCX2-CX01-CCX2) )
  S8-S7-act CX02-gen (X1-gen ∷ [] ) = just ( X1-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-X1=X1-CX01-CCX2-CX01-CCX2) )
  S8-S7-act CX02-gen (X1-gen ∷ X2-gen ∷ [] ) = just ( X1-gen ∷ X2-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-X1-X2=X1-X2-CX01-CCX2-CX01-CCX2) )
  S8-S7-act CX02-gen (X2-gen ∷ [] ) = just ( X2-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-X2=X2-CX01-CCX2-CX01-CCX2) )
  S8-S7-act CX10-gen [] = just ( [] , CX10-gen ∷ [] , refl )
  S8-S7-act CX10-gen (X0-gen ∷ [] ) = just ( X0-gen ∷ [] , CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-X0=X0-CX10) )
  S8-S7-act CX10-gen (X0-gen ∷ X1-gen ∷ [] ) = just ( X1-gen ∷ [] , CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-X0-X1=X1-CX10) )
  S8-S7-act CX10-gen (X0-gen ∷ X1-gen ∷ X2-gen ∷ [] ) = just ( X1-gen ∷ X2-gen ∷ [] , CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-X0-X1-X2=X1-X2-CX10) )
  S8-S7-act CX10-gen (X0-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X2-gen ∷ [] , CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-X0-X2=X0-X2-CX10) )
  S8-S7-act CX10-gen (X1-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ [] , CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-X1=X0-X1-CX10) )
  S8-S7-act CX10-gen (X1-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ X2-gen ∷ [] , CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-X1-X2=X0-X1-X2-CX10) )
  S8-S7-act CX10-gen (X2-gen ∷ [] ) = just ( X2-gen ∷ [] , CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-X2=X2-CX10) )
  S8-S7-act CX12-gen [] = just ( [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX12=CX10-CCX2-CX10-CCX2) )
  S8-S7-act CX12-gen (X0-gen ∷ [] ) = just ( X0-gen ∷ [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-X0=X0-CX10-CCX2-CX10-CCX2) )
  S8-S7-act CX12-gen (X0-gen ∷ X1-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ X2-gen ∷ [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-X0-X1=X0-X1-X2-CX10-CCX2-CX10-CCX2) )
  S8-S7-act CX12-gen (X0-gen ∷ X1-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-X0-X1-X2=X0-X1-CX10-CCX2-CX10-CCX2) )
  S8-S7-act CX12-gen (X0-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X2-gen ∷ [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-X0-X2=X0-X2-CX10-CCX2-CX10-CCX2) )
  S8-S7-act CX12-gen (X1-gen ∷ [] ) = just ( X1-gen ∷ X2-gen ∷ [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-X1=X1-X2-CX10-CCX2-CX10-CCX2) )
  S8-S7-act CX12-gen (X1-gen ∷ X2-gen ∷ [] ) = just ( X1-gen ∷ [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-X1-X2=X1-CX10-CCX2-CX10-CCX2) )
  S8-S7-act CX12-gen (X2-gen ∷ [] ) = just ( X2-gen ∷ [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-X2=X2-CX10-CCX2-CX10-CCX2) )
  S8-S7-act CX20-gen [] = just ( [] , CX20-gen ∷ [] , refl )
  S8-S7-act CX20-gen (X0-gen ∷ [] ) = just ( X0-gen ∷ [] , CX20-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-X0=X0-CX20) )
  S8-S7-act CX20-gen (X0-gen ∷ X1-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ [] , CX20-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-X0-X1=X0-X1-CX20) )
  S8-S7-act CX20-gen (X0-gen ∷ X1-gen ∷ X2-gen ∷ [] ) = just ( X1-gen ∷ X2-gen ∷ [] , CX20-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-X0-X1-X2=X1-X2-CX20) )
  S8-S7-act CX20-gen (X0-gen ∷ X2-gen ∷ [] ) = just ( X2-gen ∷ [] , CX20-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-X0-X2=X2-CX20) )
  S8-S7-act CX20-gen (X1-gen ∷ [] ) = just ( X1-gen ∷ [] , CX20-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-X1=X1-CX20) )
  S8-S7-act CX20-gen (X1-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ X2-gen ∷ [] , CX20-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-X1-X2=X0-X1-X2-CX20) )
  S8-S7-act CX20-gen (X2-gen ∷ [] ) = just ( X0-gen ∷ X2-gen ∷ [] , CX20-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-X2=X0-X2-CX20) )
  S8-S7-act CX21-gen [] = just ( [] , CX21-gen ∷ [] , refl )
  S8-S7-act CX21-gen (X0-gen ∷ [] ) = just ( X0-gen ∷ [] , CX21-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-X0=X0-CX21) )
  S8-S7-act CX21-gen (X0-gen ∷ X1-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ [] , CX21-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-X0-X1=X0-X1-CX21) )
  S8-S7-act CX21-gen (X0-gen ∷ X1-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X2-gen ∷ [] , CX21-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-X0-X1-X2=X0-X2-CX21) )
  S8-S7-act CX21-gen (X0-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ X2-gen ∷ [] , CX21-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-X0-X2=X0-X1-X2-CX21) )
  S8-S7-act CX21-gen (X1-gen ∷ [] ) = just ( X1-gen ∷ [] , CX21-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-X1=X1-CX21) )
  S8-S7-act CX21-gen (X1-gen ∷ X2-gen ∷ [] ) = just ( X2-gen ∷ [] , CX21-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-X1-X2=X2-CX21) )
  S8-S7-act CX21-gen (X2-gen ∷ [] ) = just ( X1-gen ∷ X2-gen ∷ [] , CX21-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-X2=X1-X2-CX21) )
  S8-S7-act CCX2-gen [] = just ( [] , CCX2-gen ∷ [] , refl )
  S8-S7-act CCX2-gen (X0-gen ∷ [] ) = just ( X0-gen ∷ [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-X0=X0-CX10-CCX2-CX10) )
  S8-S7-act CCX2-gen (X0-gen ∷ X1-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ X2-gen ∷ [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-X0-X1=X0-X1-X2-CX10-CCX2-CX10-CX01-CCX2-CX01-CCX2) )
  S8-S7-act CCX2-gen (X0-gen ∷ X1-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-X0-X1-X2=X0-X1-CX10-CCX2-CX10-CX01-CCX2-CX01-CCX2) )
  S8-S7-act CCX2-gen (X0-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X2-gen ∷ [] , CX10-gen ∷ CCX2-gen ∷ CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-X0-X2=X0-X2-CX10-CCX2-CX10) )
  S8-S7-act CCX2-gen (X1-gen ∷ [] ) = just ( X1-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-X1=X1-CX01-CCX2-CX01) )
  S8-S7-act CCX2-gen (X1-gen ∷ X2-gen ∷ [] ) = just ( X1-gen ∷ X2-gen ∷ [] , CX01-gen ∷ CCX2-gen ∷ CX01-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-X1-X2=X1-X2-CX01-CCX2-CX01) )
  S8-S7-act CCX2-gen (X2-gen ∷ [] ) = just ( X2-gen ∷ [] , CCX2-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-X2=X2-CCX2) )
  S8-S7-act CCX1-gen [] = just ( [] , CCX1-gen ∷ [] , refl )
  S8-S7-act CCX1-gen (X0-gen ∷ [] ) = just ( X0-gen ∷ [] , CX21-gen ∷ CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-X0=X0-CX21-CCX1) )
  S8-S7-act CCX1-gen (X0-gen ∷ X1-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ [] , CX21-gen ∷ CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-X0-X1=X0-X1-CX21-CCX1) )
  S8-S7-act CCX1-gen (X0-gen ∷ X1-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X2-gen ∷ [] , CX21-gen ∷ CX01-gen ∷ CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-X0-X1-X2=X0-X2-CX21-CX01-CCX1) )
  S8-S7-act CCX1-gen (X0-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ X2-gen ∷ [] , CX21-gen ∷ CX01-gen ∷ CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-X0-X2=X0-X1-X2-CX21-CX01-CCX1) )
  S8-S7-act CCX1-gen (X1-gen ∷ [] ) = just ( X1-gen ∷ [] , CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-X1=X1-CCX1) )
  S8-S7-act CCX1-gen (X1-gen ∷ X2-gen ∷ [] ) = just ( X1-gen ∷ X2-gen ∷ [] , CX01-gen ∷ CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-X1-X2=X1-X2-CX01-CCX1) )
  S8-S7-act CCX1-gen (X2-gen ∷ [] ) = just ( X2-gen ∷ [] , CX01-gen ∷ CCX1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-X2=X2-CX01-CCX1) )
  S8-S7-act CCX0-gen [] = just ( [] , CCX0-gen ∷ [] , refl )
  S8-S7-act CCX0-gen (X0-gen ∷ [] ) = just ( X0-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-X0=X0-CCX0) )
  S8-S7-act CCX0-gen (X0-gen ∷ X1-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ [] , CX20-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-X0-X1=X0-X1-CX20-CCX0) )
  S8-S7-act CCX0-gen (X0-gen ∷ X1-gen ∷ X2-gen ∷ [] ) = just ( X1-gen ∷ X2-gen ∷ [] , CX20-gen ∷ CX10-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-X0-X1-X2=X1-X2-CX20-CX10-CCX0) )
  S8-S7-act CCX0-gen (X0-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X2-gen ∷ [] , CX10-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-X0-X2=X0-X2-CX10-CCX0) )
  S8-S7-act CCX0-gen (X1-gen ∷ [] ) = just ( X1-gen ∷ [] , CX20-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-X1=X1-CX20-CCX0) )
  S8-S7-act CCX0-gen (X1-gen ∷ X2-gen ∷ [] ) = just ( X0-gen ∷ X1-gen ∷ X2-gen ∷ [] , CX20-gen ∷ CX10-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-X1-X2=X0-X1-X2-CX20-CX10-CCX0) )
  S8-S7-act CCX0-gen (X2-gen ∷ [] ) = just ( X2-gen ∷ [] , CX10-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-X2=X2-CX10-CCX0) )
  S8-S7-act _ _ = nothing

  module S8 = CosAct (record { listnf = S7.lactnf ; lemma-listnf = S7.lemma-lactnf }) S8-S7-act (\ x y -> nothing)


  desugar-swap-step : Step-Function Gate Rel

  desugar-swap-step (Swap01-gen ∷ xs) = just (CX01-gen ∷ CX10-gen ∷ CX01-gen ∷ xs , at-head (axiom ax-Swap01=CX01-CX10-CX01))
  desugar-swap-step (Swap12-gen ∷ xs) = just (CX12-gen ∷ CX21-gen ∷ CX12-gen ∷ xs , at-head (axiom ax-Swap12=CX12-CX21-CX12))
  -- Catch-all
  desugar-swap-step _ = nothing

  module Desugar-Swap = Rewriting.Step (step-cong desugar-swap-step)

  nf-desugar-swap : ListNF Rel
  nf-desugar-swap = record { listnf = Desugar-Swap.multistep 1000 ; lemma-listnf = Desugar-Swap.lemma-multistep 1000 }


  nfp : ListNF Rel
  nfp = record { listnf = S8.lactnf ; lemma-listnf = S8.lemma-lactnf } ∘ nf-desugar-swap

  nf-p : ListNF Rel
  nf-p = nfp

  nf-s6 : ListNF Rel
  nf-s6 = record { listnf = S6.lactnf ; lemma-listnf = S6.lemma-lactnf } ∘ nf-desugar-swap

  nf-s7 : ListNF Rel
  nf-s7 = record { listnf = S7.lactnf ; lemma-listnf = S7.lemma-lactnf } ∘ nf-desugar-swap

  isS7-Swap : Gate -> Bool
  isS7-Swap (Swap01-gen) = true
  isS7-Swap (Swap12-gen) = true
  isS7-Swap x = isS7 x


  nf-s7e : ListNF Rel
  nf-s7e = extend-nf isS7-Swap nf-s7

  isS8-Swap : Gate -> Bool
  isS8-Swap (Swap01-gen) = true
  isS8-Swap (Swap12-gen) = true
  isS8-Swap x = isS8 x


  nf-s8e : ListNF Rel
  nf-s8e = extend-nf isS8-Swap nfp
