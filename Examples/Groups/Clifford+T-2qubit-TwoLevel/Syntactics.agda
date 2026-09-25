------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators and relations of Greylyn, "Generators and relations
-- for the group U₄(ℤ[1/√2,i])" (M.Sc. thesis, arXiv:1408.6204): the
-- one- and two-level matrices
--
--   X_[j,k] (j < k),   H_[j,k] (j < k),   ω_[j],
--
-- and the twenty relations of its Table 1.
--
-- The generators are those of Clifford+CS-TwoLevel, whose semantics
-- is generic in the scalars: the K-generator acts as c [[1,1],[1,-1]]
-- and the i-generator as a phase.  Here c = 1/√2 and the phase is ω,
-- so they are H_[j,k] and ω_[j].
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics where

open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Word.Base

open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics public
  using (Gen ; X-gen ; K-gen ; i-gen ; X)

private
  variable
    n : ℕ
    j k l m : Fin n

------------------------------------------------------------------------
-- Generators

pattern H-gen a b p = K-gen a b p
pattern ω-gen a = i-gen a

H : (a b : Fin n) → .(a < b) → Word (Gen n)
H a b p = [ H-gen a b p ]ʷ

ω : Fin n → Word (Gen n)
ω a = [ ω-gen a ]ʷ

------------------------------------------------------------------------
-- The relations of Table 1
--
-- Numbered (1)–(20) in the order of the table.  In each relation the
-- indices are distinct, and whenever X_[a,b] or H_[a,b] occurs, a < b.

infix 4 _===_

data _===_ {n : ℕ} : WRel (Gen n) where
  -- (1)–(3): the orders of the generators.
  order-ω : ω j ^ 8 === ε
  order-H : .(p : j < k) → H j k p ^ 2 === ε
  order-X : .(p : j < k) → X j k p ^ 2 === ε

  -- (4)–(9): generators with disjoint indices commute.
  comm-ωω : j ≢ k → ω j • ω k === ω k • ω j
  comm-ωH : .(p : k < l) → j ≢ k → j ≢ l → ω j • H k l p === H k l p • ω j
  comm-ωX : .(p : k < l) → j ≢ k → j ≢ l → ω j • X k l p === X k l p • ω j
  comm-HH : .(p : j < k) .(q : l < m) → j ≢ l → j ≢ m → k ≢ l → k ≢ m →
            H j k p • H l m q === H l m q • H j k p
  comm-HX : .(p : j < k) .(q : l < m) → j ≢ l → j ≢ m → k ≢ l → k ≢ m →
            H j k p • X l m q === X l m q • H j k p
  comm-XX : .(p : j < k) .(q : l < m) → j ≢ l → j ≢ m → k ≢ l → k ≢ m →
            X j k p • X l m q === X l m q • X j k p

  -- (10)–(15): X_[j,k] swaps the indices j and k of other generators.
  swap-Xω  : .(p : j < k) → X j k p • ω k === ω j • X j k p
  swap-Xω′ : .(p : j < k) → X j k p • ω j === ω k • X j k p
  swap-XX  : .(p : j < k) .(q : k < l) → X j k p • X j l (FinP.<-trans p q) === X k l q • X j k p
  swap-XX′ : .(p : l < j) .(q : j < k) → X j k q • X l j p === X l k (FinP.<-trans p q) • X j k q
  swap-XH  : .(p : j < k) .(q : k < l) → X j k p • H j l (FinP.<-trans p q) === H k l q • X j k p
  swap-XH′ : .(p : l < j) .(q : j < k) → X j k q • H l j p === H l k (FinP.<-trans p q) • X j k q

  -- (16)–(17): ω_[j] ω_[k] is a scalar on the indices j and k.
  scalar-X : .(p : j < k) → ω j • ω k • X j k p === X j k p • ω j • ω k
  scalar-H : .(p : j < k) → ω j • ω k • H j k p === H j k p • ω j • ω k

  -- (18)–(20): further properties of H.
  rel-18 : .(p : j < k) → H j k p • X j k p === ω k ^ 4 • H j k p
  rel-19 : .(p : j < k) → H j k p • ω j ^ 2 • H j k p === ω j ^ 6 • H j k p • ω j ^ 3 • ω k ^ 5
  rel-20 : .(jk : j < k) .(kl : k < l) .(lm : l < m) →
           H j k jk • H l m lm • H j l (FinP.<-trans jk kl) • H k m (FinP.<-trans kl lm)
           === H j l (FinP.<-trans jk kl) • H k m (FinP.<-trans kl lm) • H j k jk • H l m lm
