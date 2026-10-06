------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_ ; auto)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _*_)
open import Data.Nat.Properties using (_≟_ ; _≤?_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)

open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open import Presentation.Tactics.Words
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Presentation.Tactics.Lists

open import Presentation.Tactics.Lists using (MaybeEq ; _=m?_ ; isJust ; fromJust)
open import Examples.Groups.Clifford+CS-3qubit.CosetNF

open import Examples.Groups.Clifford+CS-3qubit.Step2.Theorem using (module TwoLevel-Simplified)
open TwoLevel-Simplified

open Strict
open Monoid-Subtheories
open Monoid-Equational
open Rewriting
open Associative
open InContext
open Step-of-Equality


module Examples.Groups.Clifford+CS-3qubit.Step2.Lafont-S8 where


  step-a893 : Step-Function Gen Rel

  step-a893 =
    step-of-rel (axiom [S8a]) then
    step-of-rel (axiom [S8b]) then
    step-of-rel (axiom [S8c]) then
    step-of-rel (axiom [S8d]) then
    step-of-rel (axiom [S8e]) then
    step-of-rel (axiom [S8f]) then
    step-of-rel (axiom [S8g]) then
    step-of-rel (axiom [S8h]) then
    step-of-rel (axiom [S8i]) then
    step-of-rel (axiom [S8j]) then
    step-of-rel (axiom [S8k]) then
    step-of-rel (axiom [S8l]) then
    step-of-rel (axiom [S8m]) then
    step-of-rel (axiom [S8n]) then
    step-of-rel (axiom [S8o]) then

    step-of-rel (axiom [S9a]) then
    step-of-rel (axiom [S9b]) then
    step-of-rel (axiom [S9c]) then
    step-of-rel (axiom [S9d]) then
    step-of-rel (axiom [S9e]) then
    step-of-rel (axiom [S9f]) then

    step-of-rel (axiom [S3a]) then
    step-of-rel (axiom [S3b]) then
    step-of-rel (axiom [S3c]) then
    step-of-rel (axiom [S3d]) then
    step-of-rel (axiom [S3e]) then
    step-of-rel (axiom [S3f]) then
    step-of-rel (axiom [S3g])


  module Lafont-Rewrite = Rewriting.Step (Rewriting.step-cong step-a893) renaming (general-rewrite to rewrite-s8)

  open Lafont-Rewrite


  s8-id : List Gen
  s8-id = []
  s8-idp : Rel ⊢ word-of-list s8-id === ε
  s8-idp = rewrite-s8 20 auto

  s7-id : List Gen
  s7-id = []
  s7-idp : Rel ⊢ word-of-list s7-id === ε
  s7-idp = rewrite-s8 20 auto


  s6-id : List Gen
  s6-id = []
  s6-idp : Rel ⊢ word-of-list s6-id === ε
  s6-idp = rewrite-s8 20 auto


  s5-id : List Gen
  s5-id = []
  s5-idp : Rel ⊢ word-of-list s5-id === ε
  s5-idp = rewrite-s8 20 auto

  s4-id : List Gen
  s4-id = []
  s4-idp : Rel ⊢ word-of-list s4-id === ε
  s4-idp = rewrite-s8 20 auto

  s3-id : List Gen
  s3-id = []
  s3-idp : Rel ⊢ word-of-list s3-id === ε
  s3-idp = rewrite-s8 20 auto


  isS1 : Gen -> Bool
  isS1 _ = false

  isS2 : Gen -> Bool
  isS2 X₀₁-gen = true
  isS2 x = isS1 x


  isS3 : Gen -> Bool
  isS3 X₁₂-gen = true
  isS3 x = isS2 x

  isS4 : Gen -> Bool
  isS4 X₂₃-gen = true
  isS4 x = isS3 x

  isS5 : Gen -> Bool
  isS5 X₃₄-gen = true
  isS5 x = isS4 x

  isS6 : Gen -> Bool
  isS6 X₄₅-gen = true
  isS6 x = isS5 x

  isS7 : Gen -> Bool
  isS7 X₅₆-gen = true
  isS7 x = isS6 x

  isS8 : Gen -> Bool
  isS8 X₆₇-gen = true
  isS8 x = isS7 x

 
  S2-step : Step-Function Gen Rel
  S2-step (X₀₁-gen ∷ X₀₁-gen ∷ xs) = just (xs , at-head (axiom [S3a]))
  S2-step _ = nothing

  module S2 = Rewriting.Step (step-cong S2-step)

  S3-S2-act : let X = Gen in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S3-S2-act X₀₁-gen (X₀₁-gen ∷ X₁₂-gen ∷ [] ) = just ( X₁₂-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S3-S2-act X₀₁-gen (X₁₂-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ [] , [] , refl )
  S3-S2-act X₀₁-gen [] = just ( [] , X₀₁-gen ∷ [] , refl )
  S3-S2-act X₁₂-gen (X₀₁-gen ∷ X₁₂-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S3-S2-act X₁₂-gen (X₁₂-gen ∷ [] ) = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S3-S2-act X₁₂-gen [] = just ( X₁₂-gen ∷ [] , [] , refl )
  S3-S2-act _ _ = nothing

  S3-S2-ract : let X = Gen in let Γ = Rel in (rep : List X) ->  (g : X) -> Maybe (∃ λ (g' : List X) -> ∃ λ (rep' : List X) -> Γ ⊢ word-of-list (rep ++ g ∷ []) === word-of-list (g' ++ rep'))
  S3-S2-ract (X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₀₁-gen = just ( [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S3-S2-ract (X₁₂-gen ∷ [] ) X₀₁-gen = just ( [] , X₁₂-gen ∷ X₀₁-gen ∷ [] , refl )
  S3-S2-ract [] X₀₁-gen = just ( X₀₁-gen ∷ [] , [] , refl )
  S3-S2-ract (X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₁₂-gen = just ( X₀₁-gen ∷ [] , X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S3-S2-ract (X₁₂-gen ∷ [] ) X₁₂-gen = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S3-S2-ract [] X₁₂-gen = just ( [] , X₁₂-gen ∷ [] , refl )
  S3-S2-ract _ _ = nothing

  module S3 = CosAct (record { listnf = (S2.multistep 1000) ; lemma-listnf = (S2.lemma-multistep 1000) }) S3-S2-act S3-S2-ract

  S4-S3-act : let X = Gen in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S4-S3-act X₀₁-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S4-S3-act X₀₁-gen (X₁₂-gen ∷ X₂₃-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ [] , [] , refl )
  S4-S3-act X₀₁-gen (X₂₃-gen ∷ [] ) = just ( X₂₃-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S4-S3-act X₀₁-gen [] = just ( [] , X₀₁-gen ∷ [] , refl )
  S4-S3-act X₁₂-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S4-S3-act X₁₂-gen (X₁₂-gen ∷ X₂₃-gen ∷ [] ) = just ( X₂₃-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S4-S3-act X₁₂-gen (X₂₃-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ [] , [] , refl )
  S4-S3-act X₁₂-gen [] = just ( [] , X₁₂-gen ∷ [] , refl )
  S4-S3-act X₂₃-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S4-S3-act X₂₃-gen (X₁₂-gen ∷ X₂₃-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S4-S3-act X₂₃-gen (X₂₃-gen ∷ [] ) = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S4-S3-act X₂₃-gen [] = just ( X₂₃-gen ∷ [] , [] , refl )
  S4-S3-act _ _ = nothing

  module S4-b = CosAct (record { listnf = S3.lactnfc s3-id ; lemma-listnf = S3.lemma-lactnfc s3-id s3-idp }) S4-S3-act (\ x y -> nothing)


  S4-S3-ract : let X = Gen in let Γ = Rel in (rep : List X) ->  (g : X) -> Maybe (∃ λ (g' : List X) -> ∃ λ (rep' : List X) -> Γ ⊢ word-of-list (rep ++ g ∷ []) === word-of-list (g' ++ rep'))
  S4-S3-ract (X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₀₁-gen = just ( [] , X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S4-S3-ract (X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₀₁-gen = just ( [] , X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , refl )
  S4-S3-ract (X₂₃-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S4-S3-ract [] X₀₁-gen = just ( X₀₁-gen ∷ [] , [] , refl )
  S4-S3-ract (X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₁₂-gen = just ( X₀₁-gen ∷ [] , X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S4-S3-ract (X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₁₂-gen = just ( [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S4-S3-ract (X₂₃-gen ∷ [] ) X₁₂-gen = just ( [] , X₂₃-gen ∷ X₁₂-gen ∷ [] , refl )
  S4-S3-ract [] X₁₂-gen = just ( X₁₂-gen ∷ [] , [] , refl )
  S4-S3-ract (X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₂₃-gen = just ( X₁₂-gen ∷ [] , X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S4-b.lactnfeq auto) )
  S4-S3-ract (X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₂₃-gen = just ( X₁₂-gen ∷ [] , X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S4-S3-ract (X₂₃-gen ∷ [] ) X₂₃-gen = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S4-S3-ract [] X₂₃-gen = just ( [] , X₂₃-gen ∷ [] , refl )
  S4-S3-ract _ _ = nothing




  module S4 = CosAct (record { listnf = S3.lactnfc s3-id ; lemma-listnf = S3.lemma-lactnfc s3-id s3-idp }) S4-S3-act S4-S3-ract
  module S4r = CosAct (record { listnf = S3.ractnf ; lemma-listnf = S3.lemma-ractnf }) S4-S3-act S4-S3-ract

  S5-S4-act : let X = Gen in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S5-S4-act X₀₁-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S5-S4-act X₀₁-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] , [] , refl )
  S5-S4-act X₀₁-gen (X₂₃-gen ∷ X₃₄-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-act X₀₁-gen (X₃₄-gen ∷ [] ) = just ( X₃₄-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-act X₀₁-gen [] = just ( [] , X₀₁-gen ∷ [] , refl )
  S5-S4-act X₁₂-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-act X₁₂-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S5-S4-act X₁₂-gen (X₂₃-gen ∷ X₃₄-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] , [] , refl )
  S5-S4-act X₁₂-gen (X₃₄-gen ∷ [] ) = just ( X₃₄-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-act X₁₂-gen [] = just ( [] , X₁₂-gen ∷ [] , refl )
  S5-S4-act X₂₃-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-act X₂₃-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-act X₂₃-gen (X₂₃-gen ∷ X₃₄-gen ∷ [] ) = just ( X₃₄-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S5-S4-act X₂₃-gen (X₃₄-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ [] , [] , refl )
  S5-S4-act X₂₃-gen [] = just ( [] , X₂₃-gen ∷ [] , refl )
  S5-S4-act X₃₄-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-act X₃₄-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-act X₃₄-gen (X₂₃-gen ∷ X₃₄-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-act X₃₄-gen (X₃₄-gen ∷ [] ) = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S5-S4-act X₃₄-gen [] = just ( X₃₄-gen ∷ [] , [] , refl )
  S5-S4-act _ _ = nothing

  module S5-b = CosAct (record { listnf = S4.lactnfc s5-id ; lemma-listnf = S4.lemma-lactnfc s5-id s5-idp }) S5-S4-act (\ x y -> nothing)


  S5-S4-ract : let X = Gen in let Γ = Rel in (rep : List X) ->  (g : X) -> Maybe (∃ λ (g' : List X) -> ∃ λ (rep' : List X) -> Γ ⊢ word-of-list (rep ++ g ∷ []) === word-of-list (g' ++ rep'))
  S5-S4-ract (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₀₁-gen = just ( [] , X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-ract (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₀₁-gen = just ( [] , X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , refl )
  S5-S4-ract (X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-ract (X₃₄-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-ract [] X₀₁-gen = just ( X₀₁-gen ∷ [] , [] , refl )
  S5-S4-ract (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₁₂-gen = just ( X₀₁-gen ∷ [] , X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-ract (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₁₂-gen = just ( [] , X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-ract (X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₁₂-gen = just ( [] , X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , refl )
  S5-S4-ract (X₃₄-gen ∷ [] ) X₁₂-gen = just ( X₁₂-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-ract [] X₁₂-gen = just ( X₁₂-gen ∷ [] , [] , refl )
  S5-S4-ract (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₂₃-gen = just ( X₁₂-gen ∷ [] , X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S5-b.lactnfeq auto) )
  S5-S4-ract (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₂₃-gen = just ( X₁₂-gen ∷ [] , X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-ract (X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₂₃-gen = just ( [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-ract (X₃₄-gen ∷ [] ) X₂₃-gen = just ( [] , X₃₄-gen ∷ X₂₃-gen ∷ [] , refl )
  S5-S4-ract [] X₂₃-gen = just ( X₂₃-gen ∷ [] , [] , refl )
  S5-S4-ract (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₃₄-gen = just ( X₂₃-gen ∷ [] , X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S5-b.lactnfeq auto) )
  S5-S4-ract (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₃₄-gen = just ( X₂₃-gen ∷ [] , X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (S5-b.lactnfeq auto) )
  S5-S4-ract (X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₃₄-gen = just ( X₂₃-gen ∷ [] , X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-ract (X₃₄-gen ∷ [] ) X₃₄-gen = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S5-S4-ract [] X₃₄-gen = just ( [] , X₃₄-gen ∷ [] , refl )
  S5-S4-ract _ _ = nothing



  module S5 = CosAct (record { listnf = S4.lactnfc s5-id ; lemma-listnf = S4.lemma-lactnfc s5-id s5-idp }) S5-S4-act S5-S4-ract
  module S5r = CosAct (record { listnf = S4r.ractnf ; lemma-listnf = S4r.lemma-ractnf }) S5-S4-act S5-S4-ract



  S6-S5-act : let X = Gen in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S6-S5-act X₀₁-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₀₁-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , [] , refl )
  S6-S5-act X₀₁-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₀₁-gen (X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₀₁-gen (X₄₅-gen ∷ [] ) = just ( X₄₅-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₀₁-gen [] = just ( [] , X₀₁-gen ∷ [] , refl )
  S6-S5-act X₁₂-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₁₂-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₁₂-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , [] , refl )
  S6-S5-act X₁₂-gen (X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₁₂-gen (X₄₅-gen ∷ [] ) = just ( X₄₅-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₁₂-gen [] = just ( [] , X₁₂-gen ∷ [] , refl )
  S6-S5-act X₂₃-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₂₃-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₂₃-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₂₃-gen (X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , [] , refl )
  S6-S5-act X₂₃-gen (X₄₅-gen ∷ [] ) = just ( X₄₅-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₂₃-gen [] = just ( [] , X₂₃-gen ∷ [] , refl )
  S6-S5-act X₃₄-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₃₄-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₃₄-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₃₄-gen (X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₄₅-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₃₄-gen (X₄₅-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ [] , [] , refl )
  S6-S5-act X₃₄-gen [] = just ( [] , X₃₄-gen ∷ [] , refl )
  S6-S5-act X₄₅-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₄₅-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₄₅-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₄₅-gen (X₃₄-gen ∷ X₄₅-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₄₅-gen (X₄₅-gen ∷ [] ) = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S6-S5-act X₄₅-gen [] = just ( X₄₅-gen ∷ [] , [] , refl )
  S6-S5-act _ _ = nothing


  module S6-b = CosAct (record { listnf = S5.lactnfc s6-id ; lemma-listnf = S5.lemma-lactnfc s6-id s6-idp }) S6-S5-act (\ x y -> nothing)


  S6-S5-ract : let X = Gen in let Γ = Rel in (rep : List X) ->  (g : X) -> Maybe (∃ λ (g' : List X) -> ∃ λ (rep' : List X) -> Γ ⊢ word-of-list (rep ++ g ∷ []) === word-of-list (g' ++ rep'))
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₀₁-gen = just ( [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₀₁-gen = just ( [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , refl )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract (X₄₅-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract [] X₀₁-gen = just ( X₀₁-gen ∷ [] , [] , refl )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₁₂-gen = just ( X₀₁-gen ∷ [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₁₂-gen = just ( [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₁₂-gen = just ( [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , refl )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₁₂-gen = just ( X₁₂-gen ∷ [] , X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract (X₄₅-gen ∷ [] ) X₁₂-gen = just ( X₁₂-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract [] X₁₂-gen = just ( X₁₂-gen ∷ [] , [] , refl )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₂₃-gen = just ( X₁₂-gen ∷ [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S6-b.lactnfeq auto) )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₂₃-gen = just ( X₁₂-gen ∷ [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₂₃-gen = just ( [] , X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₂₃-gen = just ( [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , refl )
  S6-S5-ract (X₄₅-gen ∷ [] ) X₂₃-gen = just ( X₂₃-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract [] X₂₃-gen = just ( X₂₃-gen ∷ [] , [] , refl )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₃₄-gen = just ( X₂₃-gen ∷ [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S6-b.lactnfeq auto) )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₃₄-gen = just ( X₂₃-gen ∷ [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (S6-b.lactnfeq auto) )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₃₄-gen = just ( X₂₃-gen ∷ [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₃₄-gen = just ( [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract (X₄₅-gen ∷ [] ) X₃₄-gen = just ( [] , X₄₅-gen ∷ X₃₄-gen ∷ [] , refl )
  S6-S5-ract [] X₃₄-gen = just ( X₃₄-gen ∷ [] , [] , refl )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₄₅-gen = just ( X₃₄-gen ∷ [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S6-b.lactnfeq auto) )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₄₅-gen = just ( X₃₄-gen ∷ [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (S6-b.lactnfeq auto) )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₄₅-gen = just ( X₃₄-gen ∷ [] , X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (S6-b.lactnfeq auto) )
  S6-S5-ract (X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₄₅-gen = just ( X₃₄-gen ∷ [] , X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract (X₄₅-gen ∷ [] ) X₄₅-gen = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S6-S5-ract [] X₄₅-gen = just ( [] , X₄₅-gen ∷ [] , refl )
  S6-S5-ract _ _ = nothing


  module S6 = CosAct (record { listnf = S5.lactnfc s6-id ; lemma-listnf = S5.lemma-lactnfc s6-id s6-idp }) S6-S5-act S6-S5-ract
  module S6r = CosAct (record { listnf = S5r.ractnf ; lemma-listnf = S5r.lemma-ractnf }) S6-S5-act S6-S5-ract


  S7-S6-act : let X = Gen in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S7-S6-act X₀₁-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₀₁-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , [] , refl )
  S7-S6-act X₀₁-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₀₁-gen (X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₀₁-gen (X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₄₅-gen ∷ X₅₆-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₀₁-gen (X₅₆-gen ∷ [] ) = just ( X₅₆-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₀₁-gen [] = just ( [] , X₀₁-gen ∷ [] , refl )
  S7-S6-act X₁₂-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₁₂-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₁₂-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , [] , refl )
  S7-S6-act X₁₂-gen (X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₁₂-gen (X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₄₅-gen ∷ X₅₆-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₁₂-gen (X₅₆-gen ∷ [] ) = just ( X₅₆-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₁₂-gen [] = just ( [] , X₁₂-gen ∷ [] , refl )
  S7-S6-act X₂₃-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₂₃-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₂₃-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₂₃-gen (X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , [] , refl )
  S7-S6-act X₂₃-gen (X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₄₅-gen ∷ X₅₆-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₂₃-gen (X₅₆-gen ∷ [] ) = just ( X₅₆-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₂₃-gen [] = just ( [] , X₂₃-gen ∷ [] , refl )
  S7-S6-act X₃₄-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₃₄-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₃₄-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₃₄-gen (X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₄₅-gen ∷ X₅₆-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₃₄-gen (X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , [] , refl )
  S7-S6-act X₃₄-gen (X₅₆-gen ∷ [] ) = just ( X₅₆-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₃₄-gen [] = just ( [] , X₃₄-gen ∷ [] , refl )
  S7-S6-act X₄₅-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₄₅-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₄₅-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₄₅-gen (X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₄₅-gen (X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₅₆-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₄₅-gen (X₅₆-gen ∷ [] ) = just ( X₄₅-gen ∷ X₅₆-gen ∷ [] , [] , refl )
  S7-S6-act X₄₅-gen [] = just ( [] , X₄₅-gen ∷ [] , refl )
  S7-S6-act X₅₆-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₅₆-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₅₆-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₅₆-gen (X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₅₆-gen (X₄₅-gen ∷ X₅₆-gen ∷ [] ) = just ( X₄₅-gen ∷ X₅₆-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₅₆-gen (X₅₆-gen ∷ [] ) = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S7-S6-act X₅₆-gen [] = just ( X₅₆-gen ∷ [] , [] , refl )
  S7-S6-act _ _ = nothing

  module S7-b = CosAct (record { listnf = S6.lactnfc s7-id ; lemma-listnf = S6.lemma-lactnfc s7-id s7-idp }) S7-S6-act (\ x y -> nothing)

  S7-S6-ract : let X = Gen in let Γ = Rel in (rep : List X) ->  (g : X) -> Maybe (∃ λ (g' : List X) -> ∃ λ (rep' : List X) -> Γ ⊢ word-of-list (rep ++ g ∷ []) === word-of-list (g' ++ rep'))
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₀₁-gen = just ( [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₀₁-gen = just ( [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , refl )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract [] X₀₁-gen = just ( X₀₁-gen ∷ [] , [] , refl )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₁₂-gen = just ( X₀₁-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₁₂-gen = just ( [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₁₂-gen = just ( [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , refl )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₁₂-gen = just ( X₁₂-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ [] ) X₁₂-gen = just ( X₁₂-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ [] ) X₁₂-gen = just ( X₁₂-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract [] X₁₂-gen = just ( X₁₂-gen ∷ [] , [] , refl )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₂₃-gen = just ( X₁₂-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S7-b.lactnfeq auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₂₃-gen = just ( X₁₂-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₂₃-gen = just ( [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₂₃-gen = just ( [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , refl )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ [] ) X₂₃-gen = just ( X₂₃-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ [] ) X₂₃-gen = just ( X₂₃-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract [] X₂₃-gen = just ( X₂₃-gen ∷ [] , [] , refl )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₃₄-gen = just ( X₂₃-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S7-b.lactnfeq auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₃₄-gen = just ( X₂₃-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (S7-b.lactnfeq auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₃₄-gen = just ( X₂₃-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₃₄-gen = just ( [] , X₅₆-gen ∷ X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ [] ) X₃₄-gen = just ( [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] , refl )
  S7-S6-ract (X₅₆-gen ∷ [] ) X₃₄-gen = just ( X₃₄-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract [] X₃₄-gen = just ( X₃₄-gen ∷ [] , [] , refl )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₄₅-gen = just ( X₃₄-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S7-b.lactnfeq auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₄₅-gen = just ( X₃₄-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (S7-b.lactnfeq auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₄₅-gen = just ( X₃₄-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (S7-b.lactnfeq auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₄₅-gen = just ( X₃₄-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ [] ) X₄₅-gen = just ( [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ [] ) X₄₅-gen = just ( [] , X₅₆-gen ∷ X₄₅-gen ∷ [] , refl )
  S7-S6-ract [] X₄₅-gen = just ( X₄₅-gen ∷ [] , [] , refl )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₅₆-gen = just ( X₄₅-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S7-b.lactnfeq auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₅₆-gen = just ( X₄₅-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (S7-b.lactnfeq auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₅₆-gen = just ( X₄₅-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (S7-b.lactnfeq auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₅₆-gen = just ( X₄₅-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (S7-b.lactnfeq auto) )
  S7-S6-ract (X₅₆-gen ∷ X₄₅-gen ∷ [] ) X₅₆-gen = just ( X₄₅-gen ∷ [] , X₅₆-gen ∷ X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract (X₅₆-gen ∷ [] ) X₅₆-gen = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S7-S6-ract [] X₅₆-gen = just ( [] , X₅₆-gen ∷ [] , refl )
  S7-S6-ract _ _ = nothing

  module S7 = CosAct (record { listnf = S6.lactnfc s7-id ; lemma-listnf = S6.lemma-lactnfc s7-id s7-idp }) S7-S6-act S7-S6-ract
  module S7r = CosAct (record { listnf = S6r.ractnf ; lemma-listnf = S6r.lemma-ractnf }) S7-S6-act S7-S6-ract


  S8-S7-act : let X = Gen in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S8-S7-act X₀₁-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₀₁-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , [] , refl )
  S8-S7-act X₀₁-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₀₁-gen (X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₀₁-gen (X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₀₁-gen (X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₅₆-gen ∷ X₆₇-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₀₁-gen (X₆₇-gen ∷ [] ) = just ( X₆₇-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₀₁-gen [] = just ( [] , X₀₁-gen ∷ [] , refl )
  S8-S7-act X₁₂-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₁₂-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₁₂-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , [] , refl )
  S8-S7-act X₁₂-gen (X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₁₂-gen (X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₁₂-gen (X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₅₆-gen ∷ X₆₇-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₁₂-gen (X₆₇-gen ∷ [] ) = just ( X₆₇-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₁₂-gen [] = just ( [] , X₁₂-gen ∷ [] , refl )
  S8-S7-act X₂₃-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₂₃-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₂₃-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₂₃-gen (X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , [] , refl )
  S8-S7-act X₂₃-gen (X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₂₃-gen (X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₅₆-gen ∷ X₆₇-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₂₃-gen (X₆₇-gen ∷ [] ) = just ( X₆₇-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₂₃-gen [] = just ( [] , X₂₃-gen ∷ [] , refl )
  S8-S7-act X₃₄-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₃₄-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₃₄-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₃₄-gen (X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₃₄-gen (X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , [] , refl )
  S8-S7-act X₃₄-gen (X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₅₆-gen ∷ X₆₇-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₃₄-gen (X₆₇-gen ∷ [] ) = just ( X₆₇-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₃₄-gen [] = just ( [] , X₃₄-gen ∷ [] , refl )
  S8-S7-act X₄₅-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₄₅-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₄₅-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₄₅-gen (X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₄₅-gen (X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₅₆-gen ∷ X₆₇-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₄₅-gen (X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , [] , refl )
  S8-S7-act X₄₅-gen (X₆₇-gen ∷ [] ) = just ( X₆₇-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₄₅-gen [] = just ( [] , X₄₅-gen ∷ [] , refl )
  S8-S7-act X₅₆-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₅₆-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₅₆-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₅₆-gen (X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₅₆-gen (X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₅₆-gen (X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₆₇-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₅₆-gen (X₆₇-gen ∷ [] ) = just ( X₅₆-gen ∷ X₆₇-gen ∷ [] , [] , refl )
  S8-S7-act X₅₆-gen [] = just ( [] , X₅₆-gen ∷ [] , refl )
  S8-S7-act X₆₇-gen (X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₀₁-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₆₇-gen (X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₁₂-gen ∷ X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₆₇-gen (X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₂₃-gen ∷ X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₆₇-gen (X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₃₄-gen ∷ X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₆₇-gen (X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₄₅-gen ∷ X₅₆-gen ∷ X₆₇-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₆₇-gen (X₅₆-gen ∷ X₆₇-gen ∷ [] ) = just ( X₅₆-gen ∷ X₆₇-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₆₇-gen (X₆₇-gen ∷ [] ) = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S8-S7-act X₆₇-gen [] = just ( X₆₇-gen ∷ [] , [] , refl )
  S8-S7-act _ _ = nothing

  module S8-b = CosAct (record { listnf = S7.lactnfc s8-id ; lemma-listnf = S7.lemma-lactnfc s8-id s8-idp }) S8-S7-act (\ x y -> nothing)

  S8-S7-ract : let X = Gen in let Γ = Rel in (rep : List X) ->  (g : X) -> Maybe (∃ λ (g' : List X) -> ∃ λ (rep' : List X) -> Γ ⊢ word-of-list (rep ++ g ∷ []) === word-of-list (g' ++ rep'))
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₀₁-gen = just ( [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₀₁-gen = just ( [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , refl )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ [] ) X₀₁-gen = just ( X₀₁-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract [] X₀₁-gen = just ( X₀₁-gen ∷ [] , [] , refl )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₁₂-gen = just ( X₀₁-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₁₂-gen = just ( [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₁₂-gen = just ( [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , refl )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₁₂-gen = just ( X₁₂-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ) X₁₂-gen = just ( X₁₂-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ [] ) X₁₂-gen = just ( X₁₂-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ [] ) X₁₂-gen = just ( X₁₂-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract [] X₁₂-gen = just ( X₁₂-gen ∷ [] , [] , refl )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₂₃-gen = just ( X₁₂-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₂₃-gen = just ( X₁₂-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₂₃-gen = just ( [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₂₃-gen = just ( [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , refl )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ) X₂₃-gen = just ( X₂₃-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ [] ) X₂₃-gen = just ( X₂₃-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ [] ) X₂₃-gen = just ( X₂₃-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract [] X₂₃-gen = just ( X₂₃-gen ∷ [] , [] , refl )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₃₄-gen = just ( X₂₃-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₃₄-gen = just ( X₂₃-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₃₄-gen = just ( X₂₃-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₃₄-gen = just ( [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ) X₃₄-gen = just ( [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] , refl )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ [] ) X₃₄-gen = just ( X₃₄-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ [] ) X₃₄-gen = just ( X₃₄-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract [] X₃₄-gen = just ( X₃₄-gen ∷ [] , [] , refl )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₄₅-gen = just ( X₃₄-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₄₅-gen = just ( X₃₄-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₄₅-gen = just ( X₃₄-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₄₅-gen = just ( X₃₄-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ) X₄₅-gen = just ( [] , X₆₇-gen ∷ X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ [] ) X₄₅-gen = just ( [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] , refl )
  S8-S7-ract (X₆₇-gen ∷ [] ) X₄₅-gen = just ( X₄₅-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract [] X₄₅-gen = just ( X₄₅-gen ∷ [] , [] , refl )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₅₆-gen = just ( X₄₅-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₅₆-gen = just ( X₄₅-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₅₆-gen = just ( X₄₅-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₅₆-gen = just ( X₄₅-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ) X₅₆-gen = just ( X₄₅-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ [] ) X₅₆-gen = just ( [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ [] ) X₅₆-gen = just ( [] , X₆₇-gen ∷ X₅₆-gen ∷ [] , refl )
  S8-S7-ract [] X₅₆-gen = just ( X₅₆-gen ∷ [] , [] , refl )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) X₆₇-gen = just ( X₅₆-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) X₆₇-gen = just ( X₅₆-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) X₆₇-gen = just ( X₅₆-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) X₆₇-gen = just ( X₅₆-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ) X₆₇-gen = just ( X₅₆-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-ract (X₆₇-gen ∷ X₅₆-gen ∷ [] ) X₆₇-gen = just ( X₅₆-gen ∷ [] , X₆₇-gen ∷ X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract (X₆₇-gen ∷ [] ) X₆₇-gen = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S8-S7-ract [] X₆₇-gen = just ( [] , X₆₇-gen ∷ [] , refl )
  S8-S7-ract _ _ = nothing


  module S8 = CosAct (record { listnf = S7.lactnfc s8-id ; lemma-listnf = S7.lemma-lactnfc s8-id s8-idp }) S8-S7-act S8-S7-ract
  module S8r = CosAct (record { listnf = S7r.ractnf ; lemma-listnf = S7r.lemma-ractnf }) S8-S7-act S8-S7-ract



  nf-s8 : ListNF Rel
  nf-s8 = record { listnf = S8.lactnfc s8-id ; lemma-listnf = S8.lemma-lactnfc s8-id s8-idp }

  nf-s7 : ListNF Rel
  nf-s7 = record { listnf = S7.lactnfc s7-id ; lemma-listnf = S7.lemma-lactnfc s7-id s7-idp }

  nf-s6 : ListNF Rel
  nf-s6 = record { listnf = S6.lactnfc s6-id ; lemma-listnf = S6.lemma-lactnfc s6-id s6-idp }

  nf-s5 : ListNF Rel
  nf-s5 = record { listnf = S5.lactnfc s5-id ; lemma-listnf = S5.lemma-lactnfc s5-id s5-idp }


  nf-s4 : ListNF Rel
  nf-s4 = record { listnf = S4.lactnfc s4-id ; lemma-listnf = S4.lemma-lactnfc s4-id s4-idp }


  nf-s3 : ListNF Rel
  nf-s3 = record { listnf = S3.lactnfc s3-id ; lemma-listnf = S3.lemma-lactnfc s3-id s3-idp }


  nf-s8e : ListNF Rel
  nf-s8e = extend-nf isS8 nf-s8

  nf-s6e : ListNF Rel
  nf-s6e = extend-nf isS6 nf-s6

  nf-s5e : ListNF Rel
  nf-s5e = extend-nf isS5 nf-s5


  nf-s4e : ListNF Rel
  nf-s4e = extend-nf isS4 nf-s4


  nf-s3e : ListNF Rel
  nf-s3e = extend-nf isS3 nf-s3




  nf-rs8 : ListNF Rel
  nf-rs8 = record { listnf = S8r.ractnf ; lemma-listnf = S8r.lemma-ractnf  }

  nf-rs7 : ListNF Rel
  nf-rs7 = record { listnf = S7r.ractnf ; lemma-listnf = S7r.lemma-ractnf  }

  nf-rs6 : ListNF Rel
  nf-rs6 = record { listnf = S6r.ractnf ; lemma-listnf = S6r.lemma-ractnf  }

  nf-rs5 : ListNF Rel
  nf-rs5 = record { listnf = S5r.ractnf ; lemma-listnf = S5r.lemma-ractnf  }


  nf-rs4 : ListNF Rel
  nf-rs4 = record { listnf = S4r.ractnf ; lemma-listnf = S4r.lemma-ractnf  }


  nf-rs3 : ListNF Rel
  nf-rs3 = record { listnf = S3.ractnf ; lemma-listnf = S3.lemma-ractnf  }


  nf-rs8e : ListNF Rel
  nf-rs8e = extend-nf isS8 nf-rs8

  nf-rs6e : ListNF Rel
  nf-rs6e = extend-nf isS6 nf-rs6

  nf-rs5e : ListNF Rel
  nf-rs5e = extend-nf isS5 nf-rs5


  nf-rs4e : ListNF Rel
  nf-rs4e = extend-nf isS4 nf-rs4


  nf-rs3e : ListNF Rel
  nf-rs3e = extend-nf isS3 nf-rs3


  S2u-step : Step-Function Gen Rel
  S2u-step (X₆₇-gen ∷ X₆₇-gen ∷ xs) = just (xs , at-head (axiom [S3g]))
  S2u-step _ = nothing

  module S2u = Rewriting.Step (step-cong S2u-step)



  S3-S2-uact : let X = Gen in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S3-S2-uact X₆₇-gen (X₆₇-gen ∷ X₅₆-gen ∷ [] ) = just ( X₅₆-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S3-S2-uact X₆₇-gen (X₅₆-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ [] , [] , refl )
  S3-S2-uact X₆₇-gen [] = just ( [] , X₆₇-gen ∷ [] , refl )
  S3-S2-uact X₅₆-gen (X₆₇-gen ∷ X₅₆-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S3-S2-uact X₅₆-gen (X₅₆-gen ∷ [] ) = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S3-S2-uact X₅₆-gen [] = just ( X₅₆-gen ∷ [] , [] , refl )
  S3-S2-uact _ _ = nothing


  module S3u = CosAct (record { listnf = (S2u.multistep 1000) ; lemma-listnf = (S2u.lemma-multistep 1000) }) S3-S2-uact S3-S2-ract


  S4-S3-uact : let X = Gen in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S4-S3-uact X₆₇-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S4-S3-uact X₆₇-gen (X₅₆-gen ∷ X₄₅-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] , [] , refl )
  S4-S3-uact X₆₇-gen (X₄₅-gen ∷ [] ) = just ( X₄₅-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S4-S3-uact X₆₇-gen [] = just ( [] , X₆₇-gen ∷ [] , refl )
  S4-S3-uact X₅₆-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] , X₆₇-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S4-S3-uact X₅₆-gen (X₅₆-gen ∷ X₄₅-gen ∷ [] ) = just ( X₄₅-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S4-S3-uact X₅₆-gen (X₄₅-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ [] , [] , refl )
  S4-S3-uact X₅₆-gen [] = just ( [] , X₅₆-gen ∷ [] , refl )
  S4-S3-uact X₄₅-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S4-S3-uact X₄₅-gen (X₅₆-gen ∷ X₄₅-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S4-S3-uact X₄₅-gen (X₄₅-gen ∷ [] ) = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S4-S3-uact X₄₅-gen [] = just ( X₄₅-gen ∷ [] , [] , refl )
  S4-S3-uact _ _ = nothing

  module S4u = CosAct (record { listnf = S3u.lactnf ; lemma-listnf = S3u.lemma-lactnf }) S4-S3-uact S4-S3-ract


  S5-S4-uact : let X = Gen in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S5-S4-uact X₆₇-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S5-S4-uact X₆₇-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] , [] , refl )
  S5-S4-uact X₆₇-gen (X₄₅-gen ∷ X₃₄-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-uact X₆₇-gen (X₃₄-gen ∷ [] ) = just ( X₃₄-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-uact X₆₇-gen [] = just ( [] , X₆₇-gen ∷ [] , refl )
  S5-S4-uact X₅₆-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] , X₆₇-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S5-S4-uact X₅₆-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S5-S4-uact X₅₆-gen (X₄₅-gen ∷ X₃₄-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] , [] , refl )
  S5-S4-uact X₅₆-gen (X₃₄-gen ∷ [] ) = just ( X₃₄-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-uact X₅₆-gen [] = just ( [] , X₅₆-gen ∷ [] , refl )
  S5-S4-uact X₄₅-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] , X₅₆-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S5-S4-uact X₄₅-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] , X₅₆-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S5-S4-uact X₄₅-gen (X₄₅-gen ∷ X₃₄-gen ∷ [] ) = just ( X₃₄-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S5-S4-uact X₄₅-gen (X₃₄-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ [] , [] , refl )
  S5-S4-uact X₄₅-gen [] = just ( [] , X₄₅-gen ∷ [] , refl )
  S5-S4-uact X₃₄-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-uact X₃₄-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-uact X₃₄-gen (X₄₅-gen ∷ X₃₄-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S5-S4-uact X₃₄-gen (X₃₄-gen ∷ [] ) = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S5-S4-uact X₃₄-gen [] = just ( X₃₄-gen ∷ [] , [] , refl )
  S5-S4-uact _ _ = nothing

  module S5u = CosAct (record { listnf = S4u.lactnf ; lemma-listnf = S4u.lemma-lactnf }) S5-S4-uact S5-S4-ract

  S6-S5-uact : let X = Gen in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S6-S5-uact X₆₇-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₆₇-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , [] , refl )
  S6-S5-uact X₆₇-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₆₇-gen (X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₆₇-gen (X₂₃-gen ∷ [] ) = just ( X₂₃-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₆₇-gen [] = just ( [] , X₆₇-gen ∷ [] , refl )
  S6-S5-uact X₅₆-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , X₆₇-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S6-S5-uact X₅₆-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₅₆-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , [] , refl )
  S6-S5-uact X₅₆-gen (X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₅₆-gen (X₂₃-gen ∷ [] ) = just ( X₂₃-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₅₆-gen [] = just ( [] , X₅₆-gen ∷ [] , refl )
  S6-S5-uact X₄₅-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , X₅₆-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S6-S5-uact X₄₅-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , X₅₆-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S6-S5-uact X₄₅-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₄₅-gen (X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , [] , refl )
  S6-S5-uact X₄₅-gen (X₂₃-gen ∷ [] ) = just ( X₂₃-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₄₅-gen [] = just ( [] , X₄₅-gen ∷ [] , refl )
  S6-S5-uact X₃₄-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , X₄₅-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S6-S5-uact X₃₄-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , X₄₅-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S6-S5-uact X₃₄-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , X₄₅-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S6-S5-uact X₃₄-gen (X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₂₃-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₃₄-gen (X₂₃-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ [] , [] , refl )
  S6-S5-uact X₃₄-gen [] = just ( [] , X₃₄-gen ∷ [] , refl )
  S6-S5-uact X₂₃-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₂₃-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₂₃-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₂₃-gen (X₃₄-gen ∷ X₂₃-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₂₃-gen (X₂₃-gen ∷ [] ) = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S6-S5-uact X₂₃-gen [] = just ( X₂₃-gen ∷ [] , [] , refl )
  S6-S5-uact _ _ = nothing


  module S6u = CosAct (record { listnf = S5u.lactnf ; lemma-listnf = S5u.lemma-lactnf }) S6-S5-uact S6-S5-ract


  S7-S6-uact : let X = Gen in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S7-S6-uact X₆₇-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₆₇-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , [] , refl )
  S7-S6-uact X₆₇-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₆₇-gen (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₆₇-gen (X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₂₃-gen ∷ X₁₂-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₆₇-gen (X₁₂-gen ∷ [] ) = just ( X₁₂-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₆₇-gen [] = just ( [] , X₆₇-gen ∷ [] , refl )
  S7-S6-uact X₅₆-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₆₇-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S7-S6-uact X₅₆-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₅₆-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , [] , refl )
  S7-S6-uact X₅₆-gen (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₅₆-gen (X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₂₃-gen ∷ X₁₂-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₅₆-gen (X₁₂-gen ∷ [] ) = just ( X₁₂-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₅₆-gen [] = just ( [] , X₅₆-gen ∷ [] , refl )
  S7-S6-uact X₄₅-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₅₆-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S7-S6-uact X₄₅-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₅₆-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S7-S6-uact X₄₅-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₄₅-gen (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , [] , refl )
  S7-S6-uact X₄₅-gen (X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₂₃-gen ∷ X₁₂-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₄₅-gen (X₁₂-gen ∷ [] ) = just ( X₁₂-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₄₅-gen [] = just ( [] , X₄₅-gen ∷ [] , refl )
  S7-S6-uact X₃₄-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₄₅-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S7-S6-uact X₃₄-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₄₅-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S7-S6-uact X₃₄-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₄₅-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S7-S6-uact X₃₄-gen (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₂₃-gen ∷ X₁₂-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₃₄-gen (X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , [] , refl )
  S7-S6-uact X₃₄-gen (X₁₂-gen ∷ [] ) = just ( X₁₂-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₃₄-gen [] = just ( [] , X₃₄-gen ∷ [] , refl )
  S7-S6-uact X₂₃-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₃₄-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S7-S6-uact X₂₃-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₃₄-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S7-S6-uact X₂₃-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₃₄-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S7-S6-uact X₂₃-gen (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₃₄-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S7-S6-uact X₂₃-gen (X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₁₂-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₂₃-gen (X₁₂-gen ∷ [] ) = just ( X₂₃-gen ∷ X₁₂-gen ∷ [] , [] , refl )
  S7-S6-uact X₂₃-gen [] = just ( [] , X₂₃-gen ∷ [] , refl )
  S7-S6-uact X₁₂-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₁₂-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₁₂-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₁₂-gen (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₁₂-gen (X₂₃-gen ∷ X₁₂-gen ∷ [] ) = just ( X₂₃-gen ∷ X₁₂-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₁₂-gen (X₁₂-gen ∷ [] ) = just ( [] , [] ,  (rewrite-s8 100 auto) )
  S7-S6-uact X₁₂-gen [] = just ( X₁₂-gen ∷ [] , [] , refl )
  S7-S6-uact _ _ = nothing


  module S7u = CosAct (record { listnf = S6u.lactnf ; lemma-listnf = S6u.lemma-lactnf }) S7-S6-uact S7-S6-ract

  S8-S7-uact : let X = Gen in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  S8-S7-uact X₆₇-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₆₇-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , [] , refl )
  S8-S7-uact X₆₇-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₆₇-gen (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₆₇-gen (X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₆₇-gen (X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₁₂-gen ∷ X₀₁-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₆₇-gen (X₀₁-gen ∷ [] ) = just ( X₀₁-gen ∷ [] , X₆₇-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₆₇-gen [] = just ( [] , X₆₇-gen ∷ [] , refl )
  S8-S7-uact X₅₆-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₆₇-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₅₆-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₅₆-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , [] , refl )
  S8-S7-uact X₅₆-gen (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₅₆-gen (X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₅₆-gen (X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₁₂-gen ∷ X₀₁-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₅₆-gen (X₀₁-gen ∷ [] ) = just ( X₀₁-gen ∷ [] , X₅₆-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₅₆-gen [] = just ( [] , X₅₆-gen ∷ [] , refl )
  S8-S7-uact X₄₅-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₅₆-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₄₅-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₅₆-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₄₅-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₄₅-gen (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , [] , refl )
  S8-S7-uact X₄₅-gen (X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₄₅-gen (X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₁₂-gen ∷ X₀₁-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₄₅-gen (X₀₁-gen ∷ [] ) = just ( X₀₁-gen ∷ [] , X₄₅-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₄₅-gen [] = just ( [] , X₄₅-gen ∷ [] , refl )
  S8-S7-uact X₃₄-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₄₅-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₃₄-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₄₅-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₃₄-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₄₅-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₃₄-gen (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₃₄-gen (X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , [] , refl )
  S8-S7-uact X₃₄-gen (X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₁₂-gen ∷ X₀₁-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₃₄-gen (X₀₁-gen ∷ [] ) = just ( X₀₁-gen ∷ [] , X₃₄-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₃₄-gen [] = just ( [] , X₃₄-gen ∷ [] , refl )
  S8-S7-uact X₂₃-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₃₄-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₂₃-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₃₄-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₂₃-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₃₄-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₂₃-gen (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₃₄-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₂₃-gen (X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₁₂-gen ∷ X₀₁-gen ∷ [] , [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₂₃-gen (X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , [] , refl )
  S8-S7-uact X₂₃-gen (X₀₁-gen ∷ [] ) = just ( X₀₁-gen ∷ [] , X₂₃-gen ∷ [] ,  (rewrite-s8 100 auto) )
  S8-S7-uact X₂₃-gen [] = just ( [] , X₂₃-gen ∷ [] , refl )
  S8-S7-uact X₁₂-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₂₃-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₁₂-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₂₃-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₁₂-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₂₃-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₁₂-gen (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₂₃-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₁₂-gen (X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₂₃-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₁₂-gen (X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₀₁-gen ∷ [] , [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₁₂-gen (X₀₁-gen ∷ [] ) = just ( X₁₂-gen ∷ X₀₁-gen ∷ [] , [] , refl )
  S8-S7-uact X₁₂-gen [] = just ( [] , X₁₂-gen ∷ [] , refl )
  S8-S7-uact X₀₁-gen (X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₆₇-gen ∷ X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₁₂-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₀₁-gen (X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₅₆-gen ∷ X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₁₂-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₀₁-gen (X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₄₅-gen ∷ X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₁₂-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₀₁-gen (X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₃₄-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₁₂-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₀₁-gen (X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ [] , X₁₂-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₀₁-gen (X₁₂-gen ∷ X₀₁-gen ∷ [] ) = just ( X₁₂-gen ∷ X₀₁-gen ∷ [] , X₁₂-gen ∷ [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₀₁-gen (X₀₁-gen ∷ [] ) = just ( [] , [] ,  (S8-b.lactnfeq auto) )
  S8-S7-uact X₀₁-gen [] = just ( X₀₁-gen ∷ [] , [] , refl )
  S8-S7-uact _ _ = nothing

  module S8u = CosAct (record { listnf = S7u.lactnf ; lemma-listnf = S7u.lemma-lactnf }) S8-S7-uact S8-S7-ract



  nf-us8 : ListNF Rel
  nf-us8 = record { listnf = S8u.lactnf ; lemma-listnf = S8u.lemma-lactnf  }

  nf-us7 : ListNF Rel
  nf-us7 = record { listnf = S7u.lactnf ; lemma-listnf = S7u.lemma-lactnf  }

  nf-us6 : ListNF Rel
  nf-us6 = record { listnf = S6u.lactnf ; lemma-listnf = S6u.lemma-lactnf  }

  nf-us5 : ListNF Rel
  nf-us5 = record { listnf = S5u.lactnf ; lemma-listnf = S5u.lemma-lactnf  }


  nf-us4 : ListNF Rel
  nf-us4 = record { listnf = S4u.lactnf ; lemma-listnf = S4u.lemma-lactnf  }


  nf-us3 : ListNF Rel
  nf-us3 = record { listnf = S3u.lactnf ; lemma-listnf = S3u.lemma-lactnf  }


  nf-us8e : ListNF Rel
  nf-us8e = extend-nf isS8 nf-us8

  nf-us6e : ListNF Rel
  nf-us6e = extend-nf isS6 nf-us6

  nf-us5e : ListNF Rel
  nf-us5e = extend-nf isS5 nf-us5


  nf-us4e : ListNF Rel
  nf-us4e = extend-nf isS4 nf-us4


  nf-us3e : ListNF Rel
  nf-us3e = extend-nf isS3 nf-us3

