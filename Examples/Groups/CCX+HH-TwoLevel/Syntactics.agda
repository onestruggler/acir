------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators and relations of Li, Ross and Selinger, "Generators
-- and Relations for the Group Oₙ(ℤ[1/2])" (QPL 2021,
-- arXiv:2106.01175): the one-, two- and four-level matrices
--
--   (-1)_[a],   X_[a,b] (a < b),   K_[a,b,c,d] (a < b < c < d)
--
-- of the generating set 𝒢ₙ (Definition 2.6), where K = H ⊗ H
-- (Definition 2.4), and the relations of Table 1.
--
-- Table 1 asks that the indices be distinct and the relations
-- well-formed: X_[a,b] needs a < b and K_[a,b,c,d] needs a < b < c < d.
-- The constructors below take exactly these order constraints (and
-- distinctness where the order leaves it open); indices start at 0.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Syntactics where

open import Data.Fin.Base using (Fin ; _<_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Word.Base

private
  variable
    n : ℕ
    a a′ b b′ c c′ d d′ e f g h : Fin n

------------------------------------------------------------------------
-- Generators

data Gen (n : ℕ) : Set where
  M-gen : Fin n → Gen n
  X-gen : (a b : Fin n) → .(a < b) → Gen n
  K-gen : (a b c d : Fin n) → .(a < b) → .(b < c) → .(c < d) → Gen n

-- (-1)_[a].
M : Fin n → Word (Gen n)
M a = [ M-gen a ]ʷ

X : (a b : Fin n) → .(a < b) → Word (Gen n)
X a b p = [ X-gen a b p ]ʷ

K : (a b c d : Fin n) → .(a < b) → .(b < c) → .(c < d) → Word (Gen n)
K a b c d p q r = [ K-gen a b c d p q r ]ʷ

------------------------------------------------------------------------
-- The relations of Table 1

infix 4 _===_

data _===_ {n : ℕ} : WRel (Gen n) where
  -- (1a)–(1c): the generators are involutions.
  r1a : .(p : a < b) → X a b p • X a b p === ε
  r1b : M a • M a === ε
  r1c : .(p : a < b) .(q : b < c) .(r : c < d) → K a b c d p q r • K a b c d p q r === ε

  -- (2a)–(2f): generators with disjoint indices commute.
  r2a : .(p : a < b) .(q : c < d) → a ≢ c → a ≢ d → b ≢ c → b ≢ d →
        X a b p • X c d q === X c d q • X a b p
  r2b : .(p : a < b) → c ≢ a → c ≢ b → X a b p • M c === M c • X a b p
  r2c : .(p : a < b) .(q : c < d) .(r : d < e) .(s : e < f) →
        a ≢ c → a ≢ d → a ≢ e → a ≢ f → b ≢ c → b ≢ d → b ≢ e → b ≢ f →
        X a b p • K c d e f q r s === K c d e f q r s • X a b p
  r2d : a ≢ b → M a • M b === M b • M a
  r2e : .(p : b < c) .(q : c < d) .(r : d < e) → a ≢ b → a ≢ c → a ≢ d → a ≢ e →
        M a • K b c d e p q r === K b c d e p q r • M a
  r2f : .(p : a < b) .(q : b < c) .(r : c < d) .(s : e < f) .(t : f < g) .(u : g < h) →
        a ≢ e → a ≢ f → a ≢ g → a ≢ h → b ≢ e → b ≢ f → b ≢ g → b ≢ h →
        c ≢ e → c ≢ f → c ≢ g → c ≢ h → d ≢ e → d ≢ f → d ≢ g → d ≢ h →
        K a b c d p q r • K e f g h s t u === K e f g h s t u • K a b c d p q r

  -- (3a)–(3g): renaming an index by X.
  r3a : .(p : a < a′) .(q : a′ < b) .(r : a < b) → X a a′ p • X a b r === X a′ b q • X a a′ p
  r3b : .(p : a < b) .(q : b < b′) .(r : a < b′) → X b b′ q • X a b p === X a b′ r • X b b′ q
  r3c : .(p : a < b) → X a b p • M b === M a • X a b p
  r3d : .(p : a < a′) .(q : a′ < b) .(r : b < c) .(s : c < d) .(t : a < b) →
        X a a′ p • K a b c d t r s === K a′ b c d q r s • X a a′ p
  r3e : .(p : a < b) .(q : b < b′) .(r : b′ < c) .(s : c < d) .(t : b < c) .(u : a < b′) →
        X b b′ q • K a b c d p t s === K a b′ c d u r s • X b b′ q
  r3f : .(p : a < b) .(q : b < c) .(r : c < c′) .(s : c′ < d) .(t : c < d) .(u : b < c′) →
        X c c′ r • K a b c d p q t === K a b c′ d p u s • X c c′ r
  r3g : .(p : a < b) .(q : b < c) .(r : c < d) .(s : d < d′) .(t : c < d′) →
        X d d′ s • K a b c d p q r === K a b c d′ p q t • X d d′ s

  -- (4a)–(4c): symmetries of K.
  r4a : .(p : a < b) .(q : b < c) .(r : c < d) .(s : b < d) →
        X a b p • K a b c d p q r === K a b c d p q r • X b d s • M b • M d
  r4b : .(p : a < b) .(q : b < c) .(r : c < d) →
        X b c q • K a b c d p q r === M a • K a b c d p q r • M a • K a b c d p q r • M a
  r4c : .(p : a < b) .(q : b < c) .(r : c < d) .(s : b < d) →
        X c d r • K a b c d p q r === K a b c d p q r • X b d s

  -- (5a): two K's sharing two indices.
  r5a : .(p : a < b) .(q : b < c) .(r : c < d) .(s : d < e) .(t : e < f) .(u : b < d) .(v : c < e) →
        K a b c d p q r • K b d e f u s t === K c d e f r s t • K a b c e p q v

  -- (6a), for a < b < c < d < e < f < g < h.
  r6a : .(p : a < b) .(q : b < c) .(r : c < d) .(s : d < e) .(t : e < f) .(u : f < g) .(v : g < h)
        .(w : a < e) →
        M a • M e • X a e w • K e f g h t u v • K a b c d p q r • X d e s • K a b c d p q r •
          K e f g h t u v • X a e w • M a • M e
        === K e f g h t u v • K a b c d p q r • X d e s • K a b c d p q r • K e f g h t u v
