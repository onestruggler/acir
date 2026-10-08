------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators and relations of Fang, Heunen and Kaarsgaard,
-- "Hadamard-Pi: Equational Quantum Programming" (POPL 2026,
-- arXiv:2506.06835), §4.2: the one- and two-level matrices
--
--   Z_[a],   X_[a,b] (a < b),   H_[a,b] (a < b)
--
-- of the generating set 𝒢ₙ of Oₙ(ℤ[1/√2]) (Definition 4.6), and the
-- relations (a1)–(d4) of Figure 4.
--
-- The generators are those of Clifford+CS-TwoLevel, whose semantics is
-- generic in the scalars: the K-generator acts as c [[1,1],[1,-1]] and
-- the i-generator as a phase.  Here c = 1/√2 and the phase is -1, so
-- they are H_[a,b] and Z_[a].
--
-- Figure 4 asks only that the indices be distinct; a generator X_[a,b]
-- or H_[a,b] needs a < b, so each relation holds for the orderings of
-- its indices that make all its subscripts increasing.  For (d3) these
-- are a < b < c < d and a < c < b < d, for (d4) the six interleavings
-- of b < d and c < e between a and f; their constructors take exactly
-- those order constraints, and distinctness.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics where

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
    a b c d e f : Fin n

------------------------------------------------------------------------
-- Generators

pattern H-gen a b p = K-gen a b p
pattern Z-gen a = i-gen a

H : (a b : Fin n) → .(a < b) → Word (Gen n)
H a b p = [ H-gen a b p ]ʷ

Z : Fin n → Word (Gen n)
Z a = [ Z-gen a ]ʷ

------------------------------------------------------------------------
-- The relations of Figure 4

infix 4 _===_

data _===_ {n : ℕ} : WRel (Gen n) where
  -- (a1)–(a3): the generators are involutions.
  a1 : Z a ^ 2 === ε
  a2 : .(p : a < b) → X a b p ^ 2 === ε
  a3 : .(p : a < b) → H a b p ^ 2 === ε

  -- (b1)–(b6): generators with disjoint indices commute.
  b1 : a ≢ b → Z a • Z b === Z b • Z a
  b2 : .(p : b < c) → a ≢ b → a ≢ c → Z a • X b c p === X b c p • Z a
  b3 : .(p : a < b) .(q : c < d) → a ≢ c → a ≢ d → b ≢ c → b ≢ d →
       X a b p • X c d q === X c d q • X a b p
  b4 : .(p : b < c) → a ≢ b → a ≢ c → Z a • H b c p === H b c p • Z a
  b5 : .(p : a < b) .(q : c < d) → a ≢ c → a ≢ d → b ≢ c → b ≢ d →
       X a b p • H c d q === H c d q • X a b p
  b6 : .(p : a < b) .(q : c < d) → a ≢ c → a ≢ d → b ≢ c → b ≢ d →
       H a b p • H c d q === H c d q • H a b p

  -- (c1)–(c5): X_[a,b] swaps the indices a and b of other generators.
  c1 : .(p : a < b) → Z a • X a b p === X a b p • Z b
  c2 : (p : a < b) (q : b < c) →
       X b c q • X a b p === X a b p • X a c (FinP.<-trans p q)
  c3 : (p : a < b) (q : b < c) →
       X a c (FinP.<-trans p q) • X b c q === X b c q • X a b p
  c4 : (p : a < b) (q : b < c) →
       H b c q • X a b p === X a b p • H a c (FinP.<-trans p q)
  c5 : (p : a < b) (q : b < c) →
       H a c (FinP.<-trans p q) • X b c q === X b c q • H a b p

  -- (d1)–(d4): further properties of H.
  d1 : .(p : a < b) → Z a • Z b • H a b p === H a b p • Z a • Z b
  d2 : .(p : a < b) → Z b • H a b p === H a b p • X a b p
  d3 : (ab : a < b) (ac : a < c) (bd : b < d) (cd : c < d) → b ≢ c →
       (H c d cd • H a c ac • H b d bd) ^ 4 === H a b ab • H c d cd
  d4 : (ab : a < b) (ac : a < c) (bd : b < d) (ce : c < e) (df : d < f) (ef : e < f) →
       b ≢ c → b ≢ e → d ≢ c → d ≢ e →
       (H a c ac • H b d bd • H a b ab • H a c ac • H b d bd • X c e ce • X d f df) ^ 3
       === H c e ce • H d f df • H e f ef • H c e ce • H d f df • X c e ce • X d f df
