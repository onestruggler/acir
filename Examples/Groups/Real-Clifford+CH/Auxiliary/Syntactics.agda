------------------------------------------------------------------------
-- Presentations of groups
--
-- The auxiliary language: 1- and 2-level matrices, and the simplified
-- complete equational theory of Clément's Figure 7
--
-- Section 4 of the paper relies on a presentation of the group
-- O_N(ℤ[1/√2]) by the generators
--
--     (−1)_[a]      the one-level matrix negating basis vector a,
--     X_[a,b]       the two-level matrix exchanging a and b,
--     H_[a,b]       the two-level Hadamard on a and b,
--
-- for indices a, b ∈ {0, …, N − 1} (Definition 4.1, [Fang, Heunen and
-- Kaarsgaard, Hadamard-π]).  Figure 7 is the paper's simplification of
-- that theory, equivalent to it (Proposition 4.8): generic equations
-- over distinct indices, and a few instances at named indices 0 … 5.
-- Its completeness for the matrix group is the paper's Theorem 4.4,
-- quoted from the literature; here it is a hypothesis of the
-- completeness theorems that use it.
--
-- The relation is indexed by N, like the circuit relations by their
-- width: an equation naming the indices 0 … j is stated for every N
-- above j.  The paper's word order is kept, a word denoting the
-- product of its letters' matrices in the order written.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

private
  variable
    N m : ℕ

------------------------------------------------------------------------
-- Generators (Definition 4.1)

data Gen (N : ℕ) : Set where
  −1[_]  : Fin N → Gen N
  X[_,_] : Fin N → Fin N → Gen N
  H[_,_] : Fin N → Fin N → Gen N

-- The generators as one-letter words.
−1 : Fin N → Word (Gen N)
−1 a = [ −1[ a ] ]ʷ

X H : Fin N → Fin N → Word (Gen N)
X a b = [ X[ a , b ] ]ʷ
H a b = [ H[ a , b ] ]ʷ

------------------------------------------------------------------------
-- The simplified theory (Figure 7)
--
-- In each equation all indices are distinct; the generic ones carry
-- that as hypotheses, the named ones have it by construction.

infix 4 _G,_===_
data _G,_===_ : (N : ℕ) → WRel (Gen N) where

  a1* : (₁₊ m) G, −1 ₀ • −1 ₀ === ε
  a2  : ∀ {a b : Fin N} → a ≢ b → N G, X a b • X a b === ε
  a3  : ∀ {a b : Fin N} → a ≢ b → N G, H a b • H a b === ε

  b1* : (₂₊ m) G, −1 ₀ • −1 ₁ === −1 ₁ • −1 ₀
  b4* : (₃₊ m) G, −1 ₁ • H ₀ ₂ === H ₀ ₂ • −1 ₁
  b6* : (₄₊ m) G, H ₀ ₁ • H ₂ ₃ === H ₂ ₃ • H ₀ ₁

  c1  : ∀ {a b : Fin N} → a ≢ b → N G, −1 a • X a b === X a b • −1 b
  c5  : ∀ {a b c : Fin N} → a ≢ b → a ≢ c → b ≢ c →
        N G, H a c • X b c === X b c • H a b

  d2  : ∀ {a b : Fin N} → a ≢ b → N G, −1 b • H a b === H a b • X a b
  d3* : (₄₊ m) G,
        H ₀ ₁ • H ₀ ₂ • H ₁ ₃ • H ₀ ₁ • −1 ₀ • −1 ₁ • H ₀ ₂ • H ₁ ₃ ===
        H ₀ ₂ • H ₁ ₃ • H ₀ ₁ • −1 ₀ • −1 ₁ • H ₀ ₂ • H ₁ ₃ • H ₀ ₁
  d4* : (₂₊ (₄₊ m)) G,
        H ₀ ₁ • H ₀ ₂ • H ₁ ₃ • H ₀ ₄ • H ₁ ₅ • H ₀ ₁ • −1 ₀ • −1 ₁ •
        H ₀ ₄ • H ₁ ₅ • H ₀ ₂ • H ₁ ₃ ===
        H ₀ ₂ • H ₁ ₃ • H ₀ ₄ • H ₁ ₅ • H ₀ ₁ • −1 ₀ • −1 ₁ •
        H ₀ ₄ • H ₁ ₅ • H ₀ ₂ • H ₁ ₃ • H ₀ ₁

  e2* : ∀ {b c : Fin N} → b ≢ c → N G, H c b • X b c === X b c • H b c
