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
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Relation.Nullary using (Dec ; yes ; no ; does)
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
open import Examples.Groups.Clifford+CS-3qubit.Theorem
open CliffordCS

module Examples.Groups.Clifford+CS-3qubit.Step8.Comm where

  -- Commutativity.
  comm : (x y : Gen) -> Maybe (commutes Rel x y)

  comm S0-gen S1-gen = just (symm (axiom ax-S1-S0=S0-S1))
  comm S0-gen S2-gen = just (symm (axiom ax-S2-S0=S0-S2))
  comm S0-gen CS01-gen = just (symm (axiom ax-CS01-S0=S0-CS01))
  comm S0-gen CS12-gen = just (symm (axiom ax-CS12-S0=S0-CS12))
  comm S0-gen iI-gen = just (symm (axiom ax-iI-S0=S0-iI))
  comm S0-gen K1-gen = just (symm (axiom ax-K1-S0=S0-K1))
  comm S0-gen K2-gen = just (symm (axiom ax-K2-S0=S0-K2))
  comm S1-gen S0-gen = just (axiom ax-S1-S0=S0-S1)
  comm S1-gen S2-gen = just (symm (axiom ax-S2-S1=S1-S2))
  comm S1-gen CS01-gen = just (symm (axiom ax-CS01-S1=S1-CS01))
  comm S1-gen CS12-gen = just (symm (axiom ax-CS12-S1=S1-CS12))
  comm S1-gen iI-gen = just (symm (axiom ax-iI-S1=S1-iI))
  comm S1-gen K0-gen = just (axiom ax-S1-K0=K0-S1)
  comm S1-gen K2-gen = just (symm (axiom ax-K2-S1=S1-K2))
  comm S2-gen S0-gen = just (axiom ax-S2-S0=S0-S2)
  comm S2-gen S1-gen = just (axiom ax-S2-S1=S1-S2)
  comm S2-gen CS01-gen = just (symm (axiom ax-CS01-S2=S2-CS01))
  comm S2-gen CS12-gen = just (symm (axiom ax-CS12-S2=S2-CS12))
  comm S2-gen iI-gen = just (symm (axiom ax-iI-S2=S2-iI))
  comm S2-gen K0-gen = just (axiom ax-S2-K0=K0-S2)
  comm S2-gen K1-gen = just (axiom ax-S2-K1=K1-S2)
  comm CS01-gen S0-gen = just (axiom ax-CS01-S0=S0-CS01)
  comm CS01-gen S1-gen = just (axiom ax-CS01-S1=S1-CS01)
  comm CS01-gen S2-gen = just (axiom ax-CS01-S2=S2-CS01)
  comm CS01-gen CS12-gen = just (symm (axiom ax-CS12-CS01=CS01-CS12))
  comm CS01-gen iI-gen = just (symm (axiom ax-iI-CS01=CS01-iI))
  comm CS01-gen K2-gen = just (axiom ax-CS01-K2=K2-CS01)
  comm CS12-gen S0-gen = just (axiom ax-CS12-S0=S0-CS12)
  comm CS12-gen S1-gen = just (axiom ax-CS12-S1=S1-CS12)
  comm CS12-gen S2-gen = just (axiom ax-CS12-S2=S2-CS12)
  comm CS12-gen CS01-gen = just (axiom ax-CS12-CS01=CS01-CS12)
  comm CS12-gen CS12-gen = just refl
  comm CS12-gen iI-gen = just (symm (axiom ax-iI-CS12=CS12-iI))
  comm CS12-gen K0-gen = just (axiom ax-CS12-K0=K0-CS12)
  comm iI-gen S0-gen = just (axiom ax-iI-S0=S0-iI)
  comm iI-gen S1-gen = just (axiom ax-iI-S1=S1-iI)
  comm iI-gen S2-gen = just (axiom ax-iI-S2=S2-iI)
  comm iI-gen CS01-gen = just (axiom ax-iI-CS01=CS01-iI)
  comm iI-gen CS12-gen = just (axiom ax-iI-CS12=CS12-iI)
  comm iI-gen K0-gen = just (axiom ax-iI-K0=K0-iI)
  comm iI-gen K1-gen = just (axiom ax-iI-K1=K1-iI)
  comm iI-gen K2-gen = just (axiom ax-iI-K2=K2-iI)
  comm K0-gen S1-gen = just (symm (axiom ax-S1-K0=K0-S1))
  comm K0-gen S2-gen = just (symm (axiom ax-S2-K0=K0-S2))
  comm K0-gen CS12-gen = just (symm (axiom ax-CS12-K0=K0-CS12))
  comm K0-gen iI-gen = just (symm (axiom ax-iI-K0=K0-iI))
  comm K0-gen K1-gen = just (symm (axiom ax-K1-K0=K0-K1))
  comm K0-gen K2-gen = just (symm (axiom ax-K2-K0=K0-K2))
  comm K1-gen S0-gen = just (axiom ax-K1-S0=S0-K1)
  comm K1-gen S2-gen = just (symm (axiom ax-S2-K1=K1-S2))
  comm K1-gen iI-gen = just (symm (axiom ax-iI-K1=K1-iI))
  comm K1-gen K0-gen = just (axiom ax-K1-K0=K0-K1)
  comm K1-gen K2-gen = just (symm (axiom ax-K2-K1=K1-K2))
  comm K2-gen S0-gen = just (axiom ax-K2-S0=S0-K2)
  comm K2-gen S1-gen = just (axiom ax-K2-S1=S1-K2)
  comm K2-gen CS01-gen = just (symm (axiom ax-CS01-K2=K2-CS01))
  comm K2-gen iI-gen = just (symm (axiom ax-iI-K2=K2-iI))
  comm K2-gen K0-gen = just (axiom ax-K2-K0=K0-K2)
  comm K2-gen K1-gen = just (axiom ax-K2-K1=K1-K2)
  comm x y = nothing

  -- We number the generators for the purpose of ordering them.
  ord : Gen -> ℕ
  ord S0-gen = 0
  ord S1-gen = 1
  ord S2-gen = 2
  ord CS01-gen = 3
  ord CS12-gen = 4
  ord iI-gen = 8
  ord K0-gen = 5
  ord K1-gen = 6
  ord K2-gen = 7
  
  -- Ordering of generators.
  less : Gen -> Gen -> Bool
  less x y with ord x ≤? ord y
  less x y | yes _ = true
  less x y | no _ = false
  
  open Commuting Gen Rel comm less public

  nf-comm : ListNF Rel
  nf-comm = record { listnf = comm-canonical ; lemma-listnf = lemma-comm-canonical }
