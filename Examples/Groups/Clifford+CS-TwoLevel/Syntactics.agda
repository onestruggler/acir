------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators and relations of Bian–Selinger, "Generators and
-- relations for Uₙ(ℤ[½,i])", §3.1: the one- and two-level matrices
--
--   X_[j,k] (j < k),   K_[j,k] (j < k),   i_[j],
--
-- and the relations of their Figure 1.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Syntactics where

open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Word.Base

private
  variable
    n : ℕ
    j k l m : Fin n

------------------------------------------------------------------------
-- Generators
--
-- The proof that the indices are in order is irrelevant, so a
-- generator is determined by its indices.

data Gen (n : ℕ) : Set where
  X-gen : (a b : Fin n) → .(a < b) → Gen n
  K-gen : (a b : Fin n) → .(a < b) → Gen n
  i-gen : (a : Fin n) → Gen n

-- The generators as words.
X K : (a b : Fin n) → .(a < b) → Word (Gen n)
X a b p = [ X-gen a b p ]ʷ
K a b p = [ K-gen a b p ]ʷ

i : Fin n → Word (Gen n)
i a = [ i-gen a ]ʷ

-- K† = K⁻¹, which the paper writes as K⁷.
K† : (a b : Fin n) → .(a < b) → Word (Gen n)
K† a b p = K a b p ^ 7

------------------------------------------------------------------------
-- The relations of Figure 1
--
-- In each relation the indices are distinct, and whenever X_[a,b] or
-- K_[a,b] occurs, a < b.

infix 4 _===_

data _===_ {n : ℕ} : WRel (Gen n) where
  -- (1)–(3): the orders of the generators.
  order-i : i j ^ 4 === ε
  order-X : .(p : j < k) → X j k p ^ 2 === ε
  order-K : .(p : j < k) → K j k p ^ 8 === ε

  -- (4)–(9): generators with disjoint indices commute.
  comm-ii : j ≢ k → i j • i k === i k • i j
  comm-iX : .(p : k < l) → j ≢ k → j ≢ l → i j • X k l p === X k l p • i j
  comm-iK : .(p : k < l) → j ≢ k → j ≢ l → i j • K k l p === K k l p • i j
  comm-XX : .(p : j < k) .(q : l < m) → j ≢ l → j ≢ m → k ≢ l → k ≢ m →
            X j k p • X l m q === X l m q • X j k p
  comm-XK : .(p : j < k) .(q : l < m) → j ≢ l → j ≢ m → k ≢ l → k ≢ m →
            X j k p • K l m q === K l m q • X j k p
  comm-KK : .(p : j < k) .(q : l < m) → j ≢ l → j ≢ m → k ≢ l → k ≢ m →
            K j k p • K l m q === K l m q • K j k p

  -- (10)–(12′): X_[j,k] swaps the indices j and k of other generators.
  swap-iX  : .(p : j < k) → i k • X j k p === X j k p • i j
  swap-XX  : (p : j < k) (q : k < l) →
             X k l q • X j k p === X j k p • X j l (FinP.<-trans p q)
  swap-XX′ : (p : j < k) (q : k < l) →
             X j l (FinP.<-trans p q) • X k l q === X k l q • X j k p
  swap-KX  : (p : j < k) (q : k < l) →
             K k l q • X j k p === X j k p • K j l (FinP.<-trans p q)
  swap-KX′ : (p : j < k) (q : k < l) →
             K j l (FinP.<-trans p q) • X k l q === X k l q • K j k p

  -- (13)–(17): further properties of K.
  rel-13 : .(p : j < k) → K j k p • i k ^ 2 === X j k p • K j k p
  rel-14 : .(p : j < k) → K j k p • i k ^ 3 === i k • K j k p • i k • K j k p
  rel-15 : .(p : j < k) → K j k p • i j • i k === i j • i k • K j k p
  rel-16 : .(p : j < k) → K j k p ^ 2 • i j • i k === ε
  rel-17 : .(jk : j < k) .(lm : l < m) .(jl : j < l) .(km : k < m) → k ≢ l →
           K j k jk • K l m lm • K j l jl • K k m km
           === K j l jl • K k m km • K j k jk • K l m lm
