------------------------------------------------------------------------
-- Presentations of groups
--
-- The local relations of Figure 6: (a1)–(d2), the ones on at most three
-- indices.  They are the common ground of the paper's relations and
-- Clément's (Clement): each set derives them, and Engine works in any
-- set that does.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Local where

open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Word.Base
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics

private
  variable
    n : ℕ
    a b c d : Fin n

infix 4 _===ˡ_

data _===ˡ_ {n : ℕ} : WRel (Gen n) where
  a1 : Z a ^ 2 ===ˡ ε
  a2 : .(p : a < b) → X a b p ^ 2 ===ˡ ε
  a3 : .(p : a < b) → H a b p ^ 2 ===ˡ ε
  b1 : a ≢ b → Z a • Z b ===ˡ Z b • Z a
  b2 : .(p : b < c) → a ≢ b → a ≢ c → Z a • X b c p ===ˡ X b c p • Z a
  b3 : .(p : a < b) .(q : c < d) → a ≢ c → a ≢ d → b ≢ c → b ≢ d →
       X a b p • X c d q ===ˡ X c d q • X a b p
  b4 : .(p : b < c) → a ≢ b → a ≢ c → Z a • H b c p ===ˡ H b c p • Z a
  b5 : .(p : a < b) .(q : c < d) → a ≢ c → a ≢ d → b ≢ c → b ≢ d →
       X a b p • H c d q ===ˡ H c d q • X a b p
  b6 : .(p : a < b) .(q : c < d) → a ≢ c → a ≢ d → b ≢ c → b ≢ d →
       H a b p • H c d q ===ˡ H c d q • H a b p
  c1 : .(p : a < b) → Z a • X a b p ===ˡ X a b p • Z b
  c2 : (p : a < b) (q : b < c) →
       X b c q • X a b p ===ˡ X a b p • X a c (FinP.<-trans p q)
  c3 : (p : a < b) (q : b < c) →
       X a c (FinP.<-trans p q) • X b c q ===ˡ X b c q • X a b p
  c4 : (p : a < b) (q : b < c) →
       H b c q • X a b p ===ˡ X a b p • H a c (FinP.<-trans p q)
  c5 : (p : a < b) (q : b < c) →
       H a c (FinP.<-trans p q) • X b c q ===ˡ X b c q • H a b p
  d1 : .(p : a < b) → Z a • Z b • H a b p ===ˡ H a b p • Z a • Z b
  d2 : .(p : a < b) → Z b • H a b p ===ˡ H a b p • X a b p

-- They are relations of Figure 6.
local⇒ : ∀ {u v : Word (Gen n)} → u ===ˡ v → u === v
local⇒ a1 = a1
local⇒ (a2 p) = a2 p
local⇒ (a3 p) = a3 p
local⇒ (b1 x) = b1 x
local⇒ (b2 p x y) = b2 p x y
local⇒ (b3 p q x y z w) = b3 p q x y z w
local⇒ (b4 p x y) = b4 p x y
local⇒ (b5 p q x y z w) = b5 p q x y z w
local⇒ (b6 p q x y z w) = b6 p q x y z w
local⇒ (c1 p) = c1 p
local⇒ (c2 p q) = c2 p q
local⇒ (c3 p q) = c3 p q
local⇒ (c4 p q) = c4 p q
local⇒ (c5 p q) = c5 p q
local⇒ (d1 p) = d1 p
local⇒ (d2 p) = d2 p
