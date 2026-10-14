------------------------------------------------------------------------
-- Presentations of groups
--
-- The four cosets of the determinant-one subgroup
--
-- From four wires on the Clifford+CS circuits denote the subgroup of
-- U_N(ℤ[½,i]) of determinant 1, and the letters of P′ generate it
-- (scratchpad/four-wire-notes.md: index 4 by coset enumeration at
-- N = 5, 6, 8 and 16).  The determinant of a two-level generator is a
-- power of i — i for i_[a] and K_[a,b], −1 for X_[a,b] — so the cosets
-- are ℤ/4, the degree of a word, and their representatives the powers
-- of i_[0]:
--
--     ε,   i_[0],   i_[0]²,   i_[0]³.
--
-- This is the analogue of Clément's Definition A.2 with the parity
-- pair replaced by the degree: there the H-parity is a second
-- coordinate, here relation (16) of the two-level presentation
-- (K i³ = i K i K, odd in K) identifies a K with a phase in the
-- quotient, so one coordinate is all there is.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Auxiliary.Cosets where

open import Word.Base using (Word ; ε ; _•_)

------------------------------------------------------------------------
-- The cosets

-- ⟨k⟩ is the coset of degree k, represented by i_[0]^k; ⟨0⟩ is the
-- subgroup itself.
data Coset : Set where
  ⟨0⟩ ⟨1⟩ ⟨2⟩ ⟨3⟩ : Coset

-- One degree up, the coset a phase or a K moves to.
inc : Coset → Coset
inc ⟨0⟩ = ⟨1⟩
inc ⟨1⟩ = ⟨2⟩
inc ⟨2⟩ = ⟨3⟩
inc ⟨3⟩ = ⟨0⟩

-- Two degrees up, the coset an exchange moves to.
inc² : Coset → Coset
inc² c = inc (inc c)

-- A word repeated as often as the degree of a coset.
pows : ∀ {X : Set} → Coset → Word X → Word X
pows ⟨0⟩ w = ε
pows ⟨1⟩ w = w
pows ⟨2⟩ w = w • w
pows ⟨3⟩ w = w • (w • w)
