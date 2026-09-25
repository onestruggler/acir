------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffordT-Lemmas: properties of 2-qubit Clifford+T operators and tactics
-- for them, on top of the Clifford decision procedure: duality, the
-- commutation of T with Clifford operators, and inverses.  Ported from the
-- Agda code accompanying Bian and Selinger, "Generators and relations for
-- 2-qubit Clifford+T operators" (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.CliffordT-Lemmas where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_)
open import Data.Nat.Properties using (_≤?_ ; _≟_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no ; does)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (auto)
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open import Presentation.Tactics.Lists
open import Presentation.Tactics.Words
open import Examples.Groups.Clifford+T-2qubit.Generator as Generator
open import Examples.Groups.Clifford+T-2qubit.Clifford-Lemmas as Clifford-Lemmas

-- ----------------------------------------------------------------------
-- * Duality

module Clifford+T-Duality where

  -- Here, we prove some properties of duality (i.e., exchanging the
  -- roles of qubits 0 and 1) and swap gates. In particular, we prove
  -- that duality is the same as swapping on both sides. As a
  -- corollary, a Clifford+T relation holds if and only if its dual
  -- holds.

  open Monoid-Equational
  open Clifford-Lemmas
  open Clifford-Duality hiding (lemma-dual)
  open Clifford+T
  open Clifford-Rewriting
  open Associative

  -- Lemma: The swap gate is self-inverse.
  lemma-order-swap : Clifford+T.Rel ⊢ Swap • Swap === ε
  lemma-order-swap = rewrite-clifford 20 auto

  -- Lemma: T0 is conjugate to T1 by a swap gate.
  lemma-T1-Swap : Clifford+T.Rel ⊢ T1 • Swap === Swap • T0
  lemma-T1-Swap =
      equational T1 • Swap
              by rewrite-clifford 10 auto
          equals (T1 • H0) • (H1 • CZ • H0 • H1 • CZ • H0 • H1 • CZ)
              by left (axiom comm-H0-T1 reversed)
          equals (H0 • T1) • (H1 • CZ • H0 • H1 • CZ • H0 • H1 • CZ)
              by general-assoc auto
          equals H0 • (T1 • H1 • CZ • H0 • H1 • CZ • H0) • (H1 • CZ)
              by right left axiom swap-T0 reversed
          equals H0 • (H1 • CZ • H0 • H1 • CZ • H0 • T0) • (H1 • CZ)
              by general-assoc auto
          equals (H0 • H1 • CZ • H0 • H1 • CZ • H0) • (T0 • H1) • CZ
              by right left axiom comm-T0-H1
          equals (H0 • H1 • CZ • H0 • H1 • CZ • H0) • (H1 • T0) • CZ
              by general-assoc auto
          equals (H0 • H1 • CZ • H0 • H1 • CZ • H0 • H1) • (T0 • CZ)
              by right axiom comm-T0-CZ
          equals (H0 • H1 • CZ • H0 • H1 • CZ • H0 • H1) • (CZ • T0)
              by rewrite-clifford 10 auto
          equals Swap • T0

  -- A symmetric version of the previous lemma.
  lemma-T0-Swap : Clifford+T.Rel ⊢ T0 • Swap === Swap • T1
  lemma-T0-Swap =
      equational T0 • Swap
              by general-assoc auto
          equals ε • (T0 • Swap)
              by left lemma-order-swap reversed
          equals (Swap • Swap) • (T0 • Swap)
              by general-assoc auto
          equals Swap • (Swap • T0) • Swap
              by right left lemma-T1-Swap reversed
          equals Swap • (T1 • Swap) • Swap
              by general-assoc auto
          equals (Swap • T1) • (Swap • Swap)
              by right lemma-order-swap
          equals (Swap • T1) • ε
              by general-assoc auto
          equals Swap • T1

  -- Lemma: Duality is the same as swapping.
  lemma-swap : (w : Word Clifford+T.Generator) -> Clifford+T.Rel ⊢ w • Swap === Swap • dual w
  lemma-swap ([ W-gen ]ʷ) = rewrite-clifford 10 auto
  lemma-swap ([ H0-gen ]ʷ) = rewrite-clifford 10 auto
  lemma-swap ([ H1-gen ]ʷ) = rewrite-clifford 10 auto
  lemma-swap ([ S0-gen ]ʷ) = rewrite-clifford 10 auto
  lemma-swap ([ S1-gen ]ʷ) = rewrite-clifford 10 auto
  lemma-swap ([ T0-gen ]ʷ) = lemma-T0-Swap
  lemma-swap ([ T1-gen ]ʷ) = lemma-T1-Swap
  lemma-swap ([ CZ-gen ]ʷ) = rewrite-clifford 200 auto
  lemma-swap ε = general-assoc auto
  lemma-swap (w • u) =
      equational (w • u) • Swap
              by assoc
          equals w • (u • Swap)
              by right lemma-swap u
          equals w • (Swap • dual u)
              by assoc reversed
          equals (w • Swap) • dual u
              by left lemma-swap w
          equals (Swap • dual w) • dual u
              by assoc
          equals Swap • dual (w • u)

  -- Lemma: The set of Clifford+T relations is closed under duality.
  lemma-dual : {w u : Word Clifford+T.Generator} -> Clifford+T.Rel ⊢ w === u -> Clifford+T.Rel ⊢ dual w === dual u
  lemma-dual {w} {u} hyp =
      equational dual w
              by left-unit reversed
          equals ε • dual w
              by left lemma-order-swap reversed
          equals (Swap • Swap) • dual w
              by assoc
          equals Swap • (Swap • dual w)
              by right (lemma-swap w) reversed
          equals Swap • (w • Swap)
              by right left hyp
          equals Swap • (u • Swap)
              by right lemma-swap u
          equals Swap • (Swap • dual u)
              by assoc reversed
          equals (Swap • Swap) • dual u
              by left lemma-order-swap
          equals ε • dual u
              by left-unit
          equals dual u

-- ----------------------------------------------------------------------
-- * Some lemmas

open Monoid-Equational
open Monoid-Lemmas
open Associative
open Clifford+T
open Clifford+T-Duality

-- Here, we prove some basic properties of the Clifford+T relations.
-- These properties are simple enough to be proved directly, without
-- relying on automation; but they are in turns used in defining
-- several tactics later.

-- Lemma: S0 and T0 commute.
lemma-comm-S0-T0 : Clifford+T.Rel ⊢ S0 • T0 === T0 • S0
lemma-comm-S0-T0 =
    equational S0 • T0
            by left axiom square-T0 reversed
        equals (T0 • T0) • T0
            by assoc
        equals T0 • (T0 • T0)
            by right axiom square-T0
        equals T0 • S0

-- Lemma: S1 and T1 commute.
lemma-comm-S1-T1 : Clifford+T.Rel ⊢ S1 • T1 === T1 • S1
lemma-comm-S1-T1 =
    equational S1 • T1
            by left axiom square-T1 reversed
        equals (T1 • T1) • T1
            by assoc
        equals T1 • (T1 • T1)
            by right axiom square-T1
        equals T1 • S1

-- Lemma: Order of T0.
lemma-order-T0 : Clifford+T.Rel ⊢ T0 ^ 8 === ε
lemma-order-T0 =
    equational T0 ^ 8
            by general-assoc auto
        equals (T0 • T0) ^ 4
            by lemma-cong-power 4 (axiom square-T0)
        equals S0 ^ 4
            by axiom order-S0
        equals ε

-- Lemma: Order of T1.
lemma-order-T1 : Clifford+T.Rel ⊢ T1 ^ 8 === ε
lemma-order-T1 = 
    equational T1 ^ 8
            by general-assoc auto
        equals (T1 • T1) ^ 4
            by lemma-cong-power 4 (axiom square-T1)
        equals S1 ^ 4
            by axiom order-S1
        equals ε

-- Lemma: T1 and CZ commute. (Recall from Generator.agda that the
-- commutativity of T0 and CZ is an axiom, but that of T1 and CZ is
-- derivable).
lemma-comm-T1-CZ : Clifford+T.Rel ⊢ T1 • CZ === CZ • T1
lemma-comm-T1-CZ = lemma-dual (axiom comm-T0-CZ)

-- ----------------------------------------------------------------------
-- * Data required for applying word tactics to Clifford+T generators

module Clifford+T-Data where

  -- Here, we provide some basic data about which Clifford+T
  -- generators commute, an ordering on the generators, and
  -- information about their inverses. This is then used to
  -- instantiate various tactics.

  -- Information about commuting generators.
  comm : (x y : Clifford+T.Generator) -> Maybe (commutes Clifford+T.Rel x y)
  comm W-gen y = just (axiom (comm-W y))
  comm y W-gen = just (axiom (comm-W y) reversed)
  comm H0-gen H1-gen = just (axiom comm-H0-H1)
  comm H0-gen S1-gen = just (axiom comm-H0-S1)
  comm H0-gen T1-gen = just (axiom comm-H0-T1)
  comm H1-gen H0-gen = just (axiom comm-H0-H1 reversed)
  comm H1-gen S0-gen = just (axiom comm-S0-H1 reversed)
  comm H1-gen T0-gen = just (axiom comm-T0-H1 reversed)
  comm S0-gen H1-gen = just (axiom comm-S0-H1)
  comm S0-gen S1-gen = just (axiom comm-S0-S1)
  comm S0-gen T0-gen = just (lemma-comm-S0-T0)
  comm S0-gen T1-gen = just (axiom comm-S0-T1)
  comm S0-gen CZ-gen = just (axiom comm-S0-CZ)
  comm S1-gen H0-gen = just (axiom comm-H0-S1 reversed)
  comm S1-gen S0-gen = just (axiom comm-S0-S1 reversed)
  comm S1-gen T0-gen = just (axiom comm-T0-S1 reversed)
  comm S1-gen T1-gen = just (lemma-comm-S1-T1)
  comm S1-gen CZ-gen = just (axiom comm-S1-CZ)
  comm T0-gen H1-gen = just (axiom comm-T0-H1)
  comm T0-gen S1-gen = just (axiom comm-T0-S1)
  comm T0-gen S0-gen = just (lemma-comm-S0-T0 reversed)
  comm T0-gen T1-gen = just (axiom comm-T0-T1)
  comm T0-gen CZ-gen = just (axiom comm-T0-CZ)
  comm T1-gen H0-gen = just (axiom comm-H0-T1 reversed)
  comm T1-gen S0-gen = just (axiom comm-S0-T1 reversed)
  comm T1-gen T0-gen = just (axiom comm-T0-T1 reversed)
  comm T1-gen S1-gen = just (lemma-comm-S1-T1 reversed)
  comm T1-gen CZ-gen = just lemma-comm-T1-CZ
  comm CZ-gen S0-gen = just (axiom comm-S0-CZ reversed)
  comm CZ-gen S1-gen = just (axiom comm-S1-CZ reversed)
  comm CZ-gen T0-gen = just (axiom comm-T0-CZ reversed)
  comm CZ-gen T1-gen = just (lemma-comm-T1-CZ reversed)
  comm x y = nothing

  -- We number the generators for the purpose of ordering them.
  ord : Clifford+T.Generator -> ℕ
  ord W-gen = 0
  ord H0-gen = 1
  ord H1-gen = 2
  ord S0-gen = 3
  ord S1-gen = 4
  ord T0-gen = 5
  ord T1-gen = 6
  ord CZ-gen = 7

  -- An order on the generators. This is used by the Commuting
  -- tactics.
  less : Clifford+T.Generator -> Clifford+T.Generator -> Bool
  less x y with ord x ≤? ord y
  less x y | yes _ = true
  less x y | no _ = false

  -- Information about the inverses of generators. This is used by the
  -- Inverse tactics and the Group-Lemmas.
  group-like : Grouplike Clifford+T.Rel
  group-like W-gen = (W⁻¹ , trans (general-assoc auto) (axiom order-W))
  group-like H0-gen = (H0 , axiom order-H0)
  group-like H1-gen = (H1 , axiom order-H1)
  group-like S0-gen = (S0⁻¹ , trans (general-assoc auto) (axiom order-S0))
  group-like S1-gen = (S1⁻¹ , trans (general-assoc auto) (axiom order-S1))
  group-like T0-gen = (T0⁻¹ , trans (general-assoc auto) lemma-order-T0)
  group-like T1-gen = (T1⁻¹ , trans (general-assoc auto) lemma-order-T1)
  group-like CZ-gen = (CZ , axiom order-CZ)

-- Now we instantiate various modules with this information, to obtain
-- lemmas and tactics:

module Commuting-Clifford+T = Commuting Clifford+T.Generator Clifford+T.Rel Clifford+T-Data.comm Clifford+T-Data.less
module Inverse-Clifford+T = Inverse Clifford+T.Generator Clifford+T.Rel Clifford+T-Data.group-like
module Group-Lemmas-Clifford+T = Group-Lemmas Clifford+T.Generator Clifford+T.Rel Clifford+T-Data.group-like

-- ----------------------------------------------------------------------
-- * Other convenient lemmas

-- The following lemmas can be proven using some of the tactics
-- defined above. In particular, they require some reasoning about
-- inverses.

open Inverse-Clifford+T
open Clifford-Rewriting

-- Lemma: Order of CH0.
lemma-order-CH0 : Clifford+T.Rel ⊢ CH0 • CH0 === ε
lemma-order-CH0 =
  equational CH0 • CH0
          by definition
      equals (S0 • H0 • T0 • CX0 • T0⁻¹ • H0 • S0⁻¹) ^ 2
          by rewrite-clifford 10 auto
      equals (S0 • H0 • T0 • CX0) • (T0⁻¹ • T0) • (CX0 • T0⁻¹ • H0 • S0⁻¹)
          by right left lemma-left-inverse
      equals (S0 • H0 • T0 • CX0) • ε • (CX0 • T0⁻¹ • H0 • S0⁻¹)
          by rewrite-clifford 10 auto
      equals (S0 • H0) • (T0 • T0⁻¹) • (H0 • S0⁻¹)
          by right left lemma-right-inverse
      equals (S0 • H0) • ε • (H0 • S0⁻¹)
          by rewrite-clifford 10 auto
      equals ε

-- Lemma: Order of CH1.
lemma-order-CH1 : Clifford+T.Rel ⊢ CH1 • CH1 === ε
lemma-order-CH1 =
  equational CH1 • CH1
          by definition
      equals (S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹) ^ 2
          by rewrite-clifford 10 auto
      equals (S1 • H1 • T1 • CX1) • (T1⁻¹ • T1) • (CX1 • T1⁻¹ • H1 • S1⁻¹)
          by right left lemma-left-inverse
      equals (S1 • H1 • T1 • CX1) • ε • (CX1 • T1⁻¹ • H1 • S1⁻¹)
          by rewrite-clifford 10 auto
      equals (S1 • H1) • (T1 • T1⁻¹) • (H1 • S1⁻¹)
          by right left lemma-right-inverse
      equals (S1 • H1) • ε • (H1 • S1⁻¹)
          by rewrite-clifford 10 auto
      equals ε

-- Lemma: T1 is conjugate to T0.
lemma-Swap-T0-Swap⁻¹ : Clifford+T.Rel ⊢ Swap • T0 • Swap ⁻¹ === T1
lemma-Swap-T0-Swap⁻¹ =
    equational Swap • T0 • Swap ⁻¹
            by general-assoc auto
        equals (Swap • T0) • Swap ⁻¹
            by left lemma-T1-Swap reversed
        equals (T1 • Swap) • Swap ⁻¹
            by general-assoc auto
        equals T1 • (Swap • Swap ⁻¹)
            by right lemma-right-inverse
        equals T1 • ε
            by right-unit
        equals T1

-- Lemma: Moving X0 past T0.
lemma-X0-T0 : Clifford+T.Rel ⊢ X0 • T0 === T0 ⁻¹ • W • X0
lemma-X0-T0 =
    equational X0 • T0
            by general-assoc auto
        equals ε • (X0 • T0) • ε
            by left lemma-left-inverse reversed
        equals (T0 ⁻¹ • T0) • (X0 • T0) • ε
            by right right lemma-right-inverse reversed
        equals (T0 ⁻¹ • T0) • (X0 • T0) • (X0 • X0 ⁻¹)
            by general-assoc auto
        equals T0 ⁻¹ • (T0 • X0) ^ 2 • X0 ⁻¹
            by right left axiom lemma-order-T0X0
        equals T0 ⁻¹ • W • X0 ⁻¹
            by right right rewrite-clifford 10 auto
        equals T0 ⁻¹ • W • X0

-- Lemma: Moving T0 past X0 ⁻¹.
lemma-T0-X0⁻¹ : Clifford+T.Rel ⊢ T0 • X0 ⁻¹ === X0 ⁻¹ • T0 ⁻¹ • W
lemma-T0-X0⁻¹ = lemma-comm-inv (claim reversed)
  where
    claim : Clifford+T.Rel ⊢ X0 • T0 === (T0 ⁻¹ • W) • X0
    claim = trans lemma-X0-T0 (assoc reversed)

-- Lemma: T0⁻¹ has T-count 1.
lemma-T0⁻¹ : Clifford+T.Rel ⊢ T0⁻¹ === T0 • S0 ^ 3
lemma-T0⁻¹ =
    equational T0⁻¹
            by general-assoc auto
        equals T0 • (T0 ^ 2) ^ 3
            by right lemma-cong-power 3 (axiom square-T0)
        equals T0 • S0 ^ 3

-- Lemma: T1⁻¹ has T-count 1.
lemma-T1⁻¹ : Clifford+T.Rel ⊢ T1⁻¹ === T1 • S1 ^ 3
lemma-T1⁻¹ =
    equational T1⁻¹
            by general-assoc auto
        equals T1 • (T1 ^ 2) ^ 3
            by right lemma-cong-power 3 (axiom square-T1)
        equals T1 • S1 ^ 3

-- Lemma: an equivalent formulation of rel-A
lemma-rel-A : Clifford+T.Rel ⊢ (T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1) ^ 2 === ε
lemma-rel-A =
  equational (T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1) ^ 2
          by left axiom rel-A reversed 
      equals (CX1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹) • (T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1)
          by general-assoc auto
      equals (CX1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1) • (T1⁻¹ • T1) • (H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1)
          by right left lemma-left-inverse
      equals (CX1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1) • ε • (H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1)
          by rewrite-clifford 10 auto
      equals (CX1 • T1 • H1 • T1⁻¹ • CX1 • X1) • (T1 • T1⁻¹) • (CX1 • X1 • T1 • H1 • T1⁻¹ • CX1)
          by right left lemma-right-inverse
      equals (CX1 • T1 • H1 • T1⁻¹ • CX1 • X1) • ε • (CX1 • X1 • T1 • H1 • T1⁻¹ • CX1)
          by rewrite-clifford 10 auto
      equals (CX1 • T1 • H1) • (T1⁻¹ • T1) • (H1 • T1⁻¹ • CX1)
          by right left lemma-left-inverse
      equals (CX1 • T1 • H1) • ε • (H1 • T1⁻¹ • CX1)
          by rewrite-clifford 10 auto
      equals CX1 • (T1 • T1⁻¹) • CX1
          by right left lemma-right-inverse
      equals CX1 • ε • CX1
          by rewrite-clifford 10 auto
      equals ε

-- Lemma: an equivalent formulation of rel-B
lemma-rel-B : Clifford+T.Rel ⊢ (CX1 • T1 • H1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • H1 • T1⁻¹) ^ 2 === ε
lemma-rel-B =
  equational (CX1 • T1 • H1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • H1 • T1⁻¹) ^ 2
          by right axiom rel-B 
      equals (CX1 • T1 • H1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • H1 • T1⁻¹) • (T1 • H1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • H1 • T1⁻¹ • CX1)
          by general-assoc auto
      equals (CX1 • T1 • H1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • H1) • (T1⁻¹ • T1) • (H1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • H1 • T1⁻¹ • CX1)
          by right left lemma-left-inverse
      equals (CX1 • T1 • H1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • H1) • ε • (H1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • H1 • T1⁻¹ • CX1)
          by rewrite-clifford 10 auto
      equals (CX1 • T1 • H1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1) • (T1⁻¹ • T1) • (H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • H1 • T1⁻¹ • CX1)
          by right left lemma-left-inverse
      equals (CX1 • T1 • H1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1) • ε • (H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • H1 • T1⁻¹ • CX1)
          by rewrite-clifford 10 auto
      equals (CX1 • T1 • H1 • T1 • H1 • T1⁻¹ • CX1 • X1) • (T1 • T1⁻¹) • (CX1 • X1 • T1 • H1 • T1⁻¹ • H1 • T1⁻¹ • CX1)
          by right left lemma-right-inverse
      equals (CX1 • T1 • H1 • T1 • H1 • T1⁻¹ • CX1 • X1) • ε • (CX1 • X1 • T1 • H1 • T1⁻¹ • H1 • T1⁻¹ • CX1)
          by rewrite-clifford 10 auto
      equals (CX1 • T1 • H1 • T1 • H1) • (T1⁻¹ • T1) • (H1 • T1⁻¹ • H1 • T1⁻¹ • CX1)
          by right left lemma-left-inverse
      equals (CX1 • T1 • H1 • T1 • H1) • ε • (H1 • T1⁻¹ • H1 • T1⁻¹ • CX1)
          by rewrite-clifford 10 auto
      equals (CX1 • T1 • H1) • (T1 • T1⁻¹) • (H1 • T1⁻¹ • CX1)
          by right left lemma-right-inverse
      equals (CX1 • T1 • H1) • ε • (H1 • T1⁻¹ • CX1)
          by rewrite-clifford 10 auto
      equals CX1 • (T1 • T1⁻¹) • CX1
          by right left lemma-right-inverse
      equals CX1 • ε • CX1
          by rewrite-clifford 10 auto
      equals ε

-- ----------------------------------------------------------------------
-- * Automation for proving equations of the form C • T0 === T0 • C

module Commutes-T0 where

  open Clifford-Rewriting
  open Commuting-Clifford+T
  open Clifford

  -- This module provides a tactic general-comm-T0, which can be used
  -- for proving certain equations of the form C • T0 === T0 • C.
  -- Specifically, this tactic can be used when C is a Clifford
  -- operator that actually commutes with T0. We check this by first
  -- reducing C to normal form and then checking that it does not
  -- contain any H0-generators. The completeness of this method relies
  -- on particular properties of the normalization procedure we
  -- defined in Clifford-Lemmas.agda.

  general-comm-T0 : ∀ {c} -> (n : ℕ) -> let d = clifford-multistep n (list-of-word c) in comm-canonical (d ++ list-of-word T0) ≡ comm-canonical (list-of-word T0 ++ d) -> Clifford+T.Rel ⊢ c • T0 === T0 • c
  general-comm-T0 {c} n eq =
    let d = clifford-multistep n (list-of-word c)
    in
      equational c • T0
              by left lemma-list-of-word c
          equals word-of-list (list-of-word c) • T0
              by left inclusion (lemma-clifford-multistep n (list-of-word c))
          equals word-of-list d • T0
              by right lemma-list-of-word T0
          equals word-of-list d • word-of-list (list-of-word T0)
              by lemma-append d (list-of-word T0)
          equals word-of-list (d ++ list-of-word T0)
              by lemma-comm-canonical (d ++ list-of-word T0)
          equals word-of-list (comm-canonical (d ++ list-of-word T0))
              by refl' (Eq.cong word-of-list eq)
          equals word-of-list (comm-canonical (list-of-word T0 ++ d))
              by lemma-comm-canonical (list-of-word T0 ++ d) reversed
          equals word-of-list (list-of-word T0 ++ d)
              by lemma-append (list-of-word T0) d reversed
          equals word-of-list (list-of-word T0) • word-of-list d
              by left lemma-list-of-word T0 reversed
          equals T0 • word-of-list d
              by right inclusion (lemma-clifford-multistep n (list-of-word c)) reversed
          equals T0 • word-of-list (list-of-word c)
              by right lemma-list-of-word c reversed
          equals T0 • c
