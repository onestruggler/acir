------------------------------------------------------------------------
-- Presentations of groups
--
-- The complete equational theory of Fang, Heunen and Kaarsgaard for
-- the 1- and 2-level generators (Clément, Figure 6)
--
-- The theory the paper imports: its Theorem 4.4, quoted from
-- [Fang, Heunen and Kaarsgaard, Hadamard-π], says that two words over
-- G_N with the same matrix are equal modulo these equations.  As in the
-- caption, all the indices of an equation are distinct, the two indices
-- of every X and H are in increasing order, except in (e1) and (e2),
-- which relate a decreasing letter to increasing ones (for b < c).
-- These conditions are hypotheses of the constructors; where a
-- distinctness follows from the orders it is not asked again.
--
-- Figure 7 (Auxiliary.Syntactics) is the paper's simplification of it,
-- and Lemma A.1 derives every equation here from Figure 7
-- (Auxiliary.LemmaA1).  The paper's word order is kept.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Figure6 where

open import Data.Fin using (Fin ; _<_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Word.Base using (WRel ; ε ; _•_ ; _^_)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics using (Gen ; −1 ; X ; H)

private
  variable
    N : ℕ

infix 4 _F,_===_
data _F,_===_ : (N : ℕ) → WRel (Gen N) where

  a1 : ∀ {a : Fin N} → N F, −1 a • −1 a === ε
  a2 : ∀ {a b : Fin N} → a < b → N F, X a b • X a b === ε

  b1 : ∀ {a b : Fin N} → a ≢ b → N F, −1 a • −1 b === −1 b • −1 a
  b2 : ∀ {a b c : Fin N} → a ≢ b → a ≢ c → b < c →
       N F, −1 a • X b c === X b c • −1 a
  b3 : ∀ {a b c d : Fin N} → a < b → c < d → a ≢ c → a ≢ d → b ≢ c → b ≢ d →
       N F, X a b • X c d === X c d • X a b

  c1 : ∀ {a b : Fin N} → a < b → N F, −1 a • X a b === X a b • −1 b
  c2 : ∀ {a b c : Fin N} → a < b → b < c → N F, X b c • X a b === X a b • X a c
  c3 : ∀ {a b c : Fin N} → a < b → b < c → N F, X a c • X b c === X b c • X a b

  a3 : ∀ {a b : Fin N} → a < b → N F, H a b • H a b === ε

  b4 : ∀ {a b c : Fin N} → a ≢ b → a ≢ c → b < c →
       N F, −1 a • H b c === H b c • −1 a
  b5 : ∀ {a b c d : Fin N} → a < b → c < d → a ≢ c → a ≢ d → b ≢ c → b ≢ d →
       N F, X a b • H c d === H c d • X a b
  b6 : ∀ {a b c d : Fin N} → a < b → c < d → a ≢ c → a ≢ d → b ≢ c → b ≢ d →
       N F, H a b • H c d === H c d • H a b

  c4 : ∀ {a b c : Fin N} → a < b → b < c → N F, H b c • X a b === X a b • H a c
  c5 : ∀ {a b c : Fin N} → a < b → b < c → N F, H a c • X b c === X b c • H a b

  d1 : ∀ {a b : Fin N} → a < b → N F, −1 a • −1 b • H a b === H a b • −1 a • −1 b
  d2 : ∀ {a b : Fin N} → a < b → N F, −1 b • H a b === H a b • X a b
  d3 : ∀ {a b c d : Fin N} → a < b → c < d → a < c → b < d → b ≢ c →
       N F, (H c d • H a c • H b d) ^ 4 === H a b • H c d
  d4 : ∀ {a b c d e f : Fin N} →
       a < b → a < c → b < d → c < e → d < f → e < f →
       b ≢ c → b ≢ e → c ≢ d → d ≢ e →
       N F, (H a c • H b d • H a b • H a c • H b d • X c e • X d f) ^ 3 ===
            H c e • H d f • H e f • H c e • H d f • X c e • X d f

  e1 : ∀ {b c : Fin N} → b < c → N F, X c b === X b c
  e2 : ∀ {b c : Fin N} → b < c → N F, H c b === X b c • H b c • X b c
