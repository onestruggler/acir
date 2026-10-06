------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Presentation.Tactics.Equality as Eq using (_≡_; auto)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _*_)
open import Data.Nat.Properties using (_≟_ ; _≤?_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Presentation.Tactics.Lists using (MaybeEq ; _=m?_ ; isJust ; fromJust)
open import Presentation.Tactics.Lists
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open import Presentation.Tactics.Words

open import Examples.Groups.Clifford+CS-3qubit.CosetNF

open import Examples.Groups.Clifford+CS-3qubit.Step2.Theorem using (module TwoLevel-Simplified)
open TwoLevel-Simplified

open import Examples.Groups.Clifford+CS-3qubit.Step2.Lafont-S8

module Examples.Groups.Clifford+CS-3qubit.Step2.TwoLevel-Simplified-Lemmas where

  open Monoid-Equational

  module TwoLevel-Simplified-Step where
    open Rewriting
    open InContext
    open Associative
    open Step-of-Equality

    lemma-i₁^4 : Rel ⊢ i₁ ^ 4 === ε
    lemma-i₁^4 =
      equational i₁ ^ 4
        by refl
      equals (X₀₁ • i₀ • X₀₁) • (X₀₁ • i₀ • X₀₁) • (X₀₁ • i₀ • X₀₁) • (X₀₁ • i₀ • X₀₁)
        by general-assoc auto
      equals (X₀₁ • i₀) • (X₀₁ • X₀₁) • i₀ • (X₀₁ • X₀₁) • i₀ • (X₀₁ • X₀₁) • i₀ • X₀₁
        by (right left axiom [S3a])
      equals (X₀₁ • i₀) • ε • i₀ • (X₀₁ • X₀₁) • i₀ • (X₀₁ • X₀₁) • i₀ • X₀₁
        by (right right right left axiom [S3a])
      equals (X₀₁ • i₀) • ε • i₀ • ε • i₀ • (X₀₁ • X₀₁) • i₀ • X₀₁
        by (right right (right right right left axiom [S3a]))
      equals (X₀₁ • i₀) • ε • i₀ • ε • i₀ • (ε) • i₀ • X₀₁
        by general-assoc auto
      equals X₀₁ • i₀ ^ 4 • X₀₁
        by (right left axiom [S1])
      equals X₀₁ • ε • X₀₁
        by cong refl left-unit
      equals X₀₁ • X₀₁
        by axiom [S3a]
      equals ε

    lemma-[S14]' : Rel ⊢ K₀₁ ^ 2 === i₁ ^ 3 • i₀ ^ 3
    lemma-[S14]' =
      equational K₀₁ ^ 2
        by symm right-unit
      equals K₀₁ ^ 2 • ε
        by (right symm (axiom [S1]))
      equals K₀₁ ^ 2 • i₀ • i₀ ^ 3
        by general-assoc auto
      equals K₀₁ ^ 2 • i₀ • ε • i₀ ^ 3
        by (right right left symm lemma-i₁^4)
      equals K₀₁ ^ 2 • i₀ • (i₁ • i₁ ^ 3) • i₀ ^ 3
        by general-assoc auto
      equals (K₀₁ ^ 2 • i₀ • i₁) • i₁ ^ 3 • i₀ ^ 3
        by (left axiom [S14])
      equals ε • i₁ ^ 3 • i₀ ^ 3
        by left-unit
      equals i₁ ^ 3 • i₀ ^ 3

    lemma-[S4a]1 : Rel ⊢ X₀₁ • i₀ • i₀ • X₀₁ • i₀ === i₀ • X₀₁ • i₀ • i₀ • X₀₁
    lemma-[S4a]1 =
      equational X₀₁ • i₀ • i₀ • X₀₁ • i₀
        by general-assoc auto
      equals X₀₁ • i₀ • ε • i₀ • X₀₁ • i₀
        by (right right left symm (axiom [S3a]))
      equals X₀₁ • i₀ • (X₀₁ • X₀₁) • i₀ • X₀₁ • i₀
        by general-assoc auto
      equals (X₀₁ • i₀ • X₀₁) • (X₀₁ • i₀ • X₀₁) • i₀
        by (right axiom [S4a])
      equals (X₀₁ • i₀ • X₀₁) • i₀ • X₀₁ • i₀ • X₀₁
        by general-assoc auto
      equals ((X₀₁ • i₀ • X₀₁) • i₀) • X₀₁ • i₀ • X₀₁
        by (left axiom [S4a])
      equals (i₀ • (X₀₁ • i₀ • X₀₁)) • X₀₁ • i₀ • X₀₁
        by general-assoc auto
      equals i₀ • X₀₁ • i₀ • (X₀₁ • X₀₁) • i₀ • X₀₁
        by (right right right left axiom [S3a])
      equals i₀ • X₀₁ • i₀ • ε • i₀ • X₀₁
        by general-assoc auto
      equals i₀ • X₀₁ • i₀ • i₀ • X₀₁


    lemma-[S4a]2 : Rel ⊢ X₀₁ • i₀ • i₀ • i₀ • X₀₁ • i₀ === i₀ • X₀₁ • i₀ • i₀ • i₀ • X₀₁
    lemma-[S4a]2 =
      equational X₀₁ • i₀ • i₀ • i₀ • X₀₁ • i₀
        by general-assoc auto
      equals X₀₁ • i₀ • ε • i₀ • i₀ • X₀₁ • i₀
        by (right right left symm (axiom [S3a]))
      equals X₀₁ • i₀ • (X₀₁ • X₀₁) • i₀ • i₀ • X₀₁ • i₀
        by general-assoc auto
      equals (X₀₁ • i₀ • X₀₁) • X₀₁ • i₀ • i₀ • X₀₁ • i₀
        by (right lemma-[S4a]1)
      equals (X₀₁ • i₀ • X₀₁) • i₀ • X₀₁ • i₀ • i₀ • X₀₁
        by general-assoc auto
      equals ((X₀₁ • i₀ • X₀₁) • i₀) • X₀₁ • i₀ • i₀ • X₀₁
        by (left axiom [S4a])
      equals (i₀ • (X₀₁ • i₀ • X₀₁)) • X₀₁ • i₀ • i₀ • X₀₁
        by general-assoc auto
      equals i₀ • X₀₁ • i₀ • (X₀₁ • X₀₁) • i₀ • i₀ • X₀₁
        by (right right right left axiom [S3a])
      equals i₀ • X₀₁ • i₀ • ε • i₀ • i₀ • X₀₁
        by general-assoc auto
      equals i₀ • X₀₁ • i₀ • i₀ • i₀ • X₀₁


    -- We define a rewrite system for simplifying words in the new
    -- generators. This takes care of a few things such as commuting
    -- generators, simplifying permutations made of Xⱼₖ generators,
    -- and reducing powers of generators.



    X-step : Step-Function Gen Rel

    X-step (X₀₁-gen ∷ X₀₁-gen ∷ t) = just (t , at-head (axiom [S3a]))
    X-step (X₁₂-gen ∷ X₁₂-gen ∷ t) = just (t , at-head (axiom [S3b]))
    X-step (X₂₃-gen ∷ X₂₃-gen ∷ t) = just (t , at-head (axiom [S3c]))
    X-step (X₃₄-gen ∷ X₃₄-gen ∷ t) = just (t , at-head (axiom [S3d]))
    X-step (X₄₅-gen ∷ X₄₅-gen ∷ t) = just (t , at-head (axiom [S3e]))
    X-step (X₅₆-gen ∷ X₅₆-gen ∷ t) = just (t , at-head (axiom [S3f]))
    X-step (X₆₇-gen ∷ X₆₇-gen ∷ t) = just (t , at-head (axiom [S3g]))

    X-step (X₁₂-gen ∷ i₀-gen ∷ t) = just (i₀-gen ∷ X₁₂-gen ∷ t , at-head (symm (axiom [S5a])))
    X-step (X₂₃-gen ∷ i₀-gen ∷ t) = just (i₀-gen ∷ X₂₃-gen ∷ t , at-head (symm (axiom [S5b])))
    X-step (X₃₄-gen ∷ i₀-gen ∷ t) = just (i₀-gen ∷ X₃₄-gen ∷ t , at-head (symm (axiom [S5c])))
    X-step (X₄₅-gen ∷ i₀-gen ∷ t) = just (i₀-gen ∷ X₄₅-gen ∷ t , at-head (symm (axiom [S5d])))
    X-step (X₅₆-gen ∷ i₀-gen ∷ t) = just (i₀-gen ∷ X₅₆-gen ∷ t , at-head (symm (axiom [S5e])))
    X-step (X₆₇-gen ∷ i₀-gen ∷ t) = just (i₀-gen ∷ X₆₇-gen ∷ t , at-head (symm (axiom [S5f])))


    X-step x = nothing


    step : Step-Function Gen Rel

    step =
      step-of-rel (axiom [S1]) then

      step-of-rel (axiom [S3a]) then
      step-of-rel (axiom [S3b]) then
      step-of-rel (axiom [S3c]) then
      step-of-rel (axiom [S3d]) then
      step-of-rel (axiom [S3e]) then
      step-of-rel (axiom [S3f]) then
      step-of-rel (axiom [S3g]) then

      step-of-rel (axiom [S4a]) then
      step-of-rel (lemma-[S4a]1) then
      step-of-rel (lemma-[S4a]2) then
      step-of-rel (axiom [S4b]) then

      step-of-rel (axiom [S5a]) then
      step-of-rel (axiom [S5b]) then
      step-of-rel (axiom [S5c]) then
      step-of-rel (axiom [S5d]) then
      step-of-rel (axiom [S5e]) then
      step-of-rel (axiom [S5f]) then

      step-of-rel (axiom [S6]) then

      step-of-rel (axiom [S7a]) then
      step-of-rel (axiom [S7b]) then
      step-of-rel (axiom [S7c]) then
      step-of-rel (axiom [S7d]) then
      step-of-rel (axiom [S7e]) then

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

      step-of-rel (axiom [S10]) then
      step-of-rel (axiom [S11]) then
      step-of-rel (axiom [S12]) then
      step-of-rel (lemma-[S14]') then
      step-of-rel (axiom [S15]) 


    lemma-X₀₁-i₂ : Rel ⊢ X₀₁ • X₁₂ • X₀₁ • i₀ === X₁₂ • X₀₁ • i₀ • X₁₂
    lemma-X₀₁-i₂ =
      equational X₀₁ • X₁₂ • X₀₁ • i₀
        by general-assoc auto
      equals (X₀₁ • X₁₂ • X₀₁) • i₀
        by left symm (axiom [S9a])
      equals (X₁₂ • X₀₁ • X₁₂) • i₀
        by general-assoc auto
      equals X₁₂ • X₀₁ • X₁₂ • i₀
        by right right symm (axiom [S5a])
      equals X₁₂ • X₀₁ • i₀ • X₁₂


    lemma-X₂₃-X₀₁-i₀ : Rel ⊢ X₂₃ • X₀₁ • i₀ === X₀₁ • i₀ • X₂₃
    lemma-X₂₃-X₀₁-i₀ =
      equational X₂₃ • X₀₁ • i₀
        by symm assoc
      equals (X₂₃ • X₀₁) • i₀
        by left axiom [S8a]
      equals (X₀₁ • X₂₃) • i₀
        by assoc
      equals X₀₁ • X₂₃ • i₀
        by right symm (axiom [S5b])
      equals X₀₁ • i₀ • X₂₃
  
    xki-step : Step-Function Gen Rel

    xki-step (X₁₂-gen ∷ i₀-gen ∷ t) = just (i₀-gen ∷ X₁₂-gen ∷ t , at-head (symm (axiom [S5a])))
    xki-step (X₂₃-gen ∷ i₀-gen ∷ t) = just (i₀-gen ∷ X₂₃-gen ∷ t , at-head (symm (axiom [S5b])))
    xki-step (X₃₄-gen ∷ i₀-gen ∷ t) = just (i₀-gen ∷ X₃₄-gen ∷ t , at-head (symm (axiom [S5c])))
    xki-step (X₄₅-gen ∷ i₀-gen ∷ t) = just (i₀-gen ∷ X₄₅-gen ∷ t , at-head (symm (axiom [S5d])))
    xki-step (X₅₆-gen ∷ i₀-gen ∷ t) = just (i₀-gen ∷ X₅₆-gen ∷ t , at-head (symm (axiom [S5e])))
    xki-step (X₆₇-gen ∷ i₀-gen ∷ t) = just (i₀-gen ∷ X₆₇-gen ∷ t , at-head (symm (axiom [S5f])))

    xki-step (X₂₃-gen ∷ K₀₁-gen ∷ t) = just (K₀₁-gen ∷ X₂₃-gen ∷ t , at-head (symm (axiom [S7a])))
    xki-step (X₃₄-gen ∷ K₀₁-gen ∷ t) = just (K₀₁-gen ∷ X₃₄-gen ∷ t , at-head (symm (axiom [S7b])))
    xki-step (X₄₅-gen ∷ K₀₁-gen ∷ t) = just (K₀₁-gen ∷ X₄₅-gen ∷ t , at-head (symm (axiom [S7c])))
    xki-step (X₅₆-gen ∷ K₀₁-gen ∷ t) = just (K₀₁-gen ∷ X₅₆-gen ∷ t , at-head (symm (axiom [S7d])))
    xki-step (X₆₇-gen ∷ K₀₁-gen ∷ t) = just (K₀₁-gen ∷ X₆₇-gen ∷ t , at-head (symm (axiom [S7e])))


    xki-step (X₀₁-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ i₀-gen ∷ t) = just (X₁₂-gen ∷ X₀₁-gen ∷ i₀-gen ∷ X₁₂-gen ∷ t , at-head (lemma-X₀₁-i₂))


    xki-step (X₀₁-gen ∷ K₀₁-gen ∷ t) = just (K₀₁-gen ∷ X₀₁-gen ∷ i₀-gen ∷ X₀₁-gen ∷ X₀₁-gen ∷ i₀-gen ∷ X₀₁-gen ∷ t , at-head (symm (axiom [S10])))
    xki-step (X₂₃-gen ∷ X₀₁-gen ∷ i₀-gen ∷ t) = just (X₀₁-gen ∷ i₀-gen ∷ X₂₃-gen ∷ t , at-head (lemma-X₂₃-X₀₁-i₀))


    xki-step x = nothing


    comm-x-step : Step-Function Gen Rel

    comm-x-step =

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
      step-of-rel (axiom [S8o])



    yang-baxter-step : Step-Function Gen Rel
    yang-baxter-step =
      step-of-rel (symm (axiom [S9a])) then
      step-of-rel (symm (axiom [S9b])) then
      step-of-rel (symm (axiom [S9c])) then
      step-of-rel (symm (axiom [S9d])) then
      step-of-rel (symm (axiom [S9e])) then
      step-of-rel (symm (axiom [S9f]))


    x-order-step : Step-Function Gen Rel
    x-order-step =
      step-of-rel (axiom [S3a]) then
      step-of-rel (axiom [S3b]) then
      step-of-rel (axiom [S3c]) then
      step-of-rel (axiom [S3d]) then
      step-of-rel (axiom [S3e]) then
      step-of-rel (axiom [S3f]) then
      step-of-rel (axiom [S3g])


  module TwoLevel-Rewrite = Rewriting.Step (Rewriting.step-cong TwoLevel-Simplified-Step.step) renaming (general-rewrite to rewrite-stwolevel)

  open Rewriting
  open TwoLevel-Simplified-Step
  module TwoLevel-Rewrite2 = Rewriting.Step-With-Standardization ( step-cong (
    ( x-order-step) then
    ( yang-baxter-step) then
    ( xki-step) then
    ( comm-x-step))) (nf-s8e .listnf) (nf-s8e .lemma-listnf) renaming (general-rewrite to rewrite-stl)

  module TwoLevel-Rewrite3 = Rewriting.Step ( step-cong (
    ( x-order-step) then
    ( yang-baxter-step) then
    ( xki-step) then
    ( comm-x-step)))


  module TR = Rewriting.Step-With-Standardization ( step-cong 
    xki-step) (nf-s8e .listnf) (nf-s8e .lemma-listnf) renaming (general-rewrite to rewrite-stl)

  module TRr = Rewriting.Step-With-Standardization ( step-cong 
    xki-step) (nf-rs8e .listnf) (nf-rs8e .lemma-listnf) renaming (general-rewrite to rewrite-stlr)

  module TRu = Rewriting.Step-With-Standardization ( step-cong 
    xki-step) (nf-us8e .listnf) (nf-us8e .lemma-listnf) renaming (general-rewrite to rewrite-stlu)

  module TRn = Rewriting.Step-With-Standardization (\ x -> nothing ) (nf-us8e .listnf) (nf-us8e .lemma-listnf) renaming (general-rewrite to rewrite-stlu)


  open TwoLevel-Rewrite
  open Associative

  -- The new generators also have a group structure.

  lemma-K₀₁^8=ε : Rel ⊢ K₀₁ ^ 8 === ε
  lemma-K₀₁^8=ε = rewrite-stwolevel 500 auto

  group-like : Grouplike Rel
  group-like i₀-gen = (i₀ ^ 3 , trans (general-assoc auto) (axiom [S1]))
  group-like K₀₁-gen = (K₀₁ ^ 7 , trans (general-assoc auto) (lemma-K₀₁^8=ε))
  group-like X₀₁-gen = (X₀₁ , axiom [S3a])
  group-like X₁₂-gen = (X₁₂ , axiom [S3b])
  group-like X₂₃-gen = (X₂₃ , axiom [S3c])
  group-like X₃₄-gen = (X₃₄ , axiom [S3d])
  group-like X₄₅-gen = (X₄₅ , axiom [S3e])
  group-like X₅₆-gen = (X₅₆ , axiom [S3f])
  group-like X₆₇-gen = (X₆₇ , axiom [S3g])


  open Inverse Gen Rel group-like public
  module BC = Basis-Change-With-Standardization group-like (xki-step) (nf-s8e .listnf) (nf-s8e .lemma-listnf)
  module BCr = Basis-Change-With-Standardization group-like (xki-step) (nf-rs8e .listnf) (nf-rs8e .lemma-listnf)
  module BCu = Basis-Change-With-Standardization group-like (xki-step) (nf-us8e .listnf) (nf-us8e .lemma-listnf)
  module BC3 = Basis-Change3 group-like (x-order-step then yang-baxter-step then xki-step then comm-x-step)

  module TR2 = TwoLevel-Rewrite2
  module TR3 = TwoLevel-Rewrite3
