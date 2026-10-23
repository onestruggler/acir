------------------------------------------------------------------------
-- Presentations of groups
--
-- Words over P′ decoding to words of blocks (four wires)
--
-- A base case of Lemma 8.7 is a word over P′ put together from parts —
-- a consecutive letter, whose decoding is its gadget block
-- (Four.Facts.Bridges), or the word of a gate done before, whose
-- decoding is that gate as a macro letter — and the four-wire
-- derivations (Four.D) state their facts about the blocks flattened.
-- `chainᵈ` joins the parts: the product of their words decodes to the
-- flattened blocks.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Proofs ; Win ; get)
open import Examples.Groups.Clifford+CS.Four.CStmt using (clemmas)

module Examples.Groups.Clifford+CS.Lemma87.Parts (C : Proofs clemmas) where

open import Data.List using (List ; [] ; _∷_ ; map)
open import Word.Base using (Word ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; sym)
open import Examples.Groups.Clifford+CS.Four.Transport C using (Blk ; flatB ; flat ; ++≈)
open import Examples.Groups.Clifford+CS.Lemma87.Decodes 0 public

-- A part: a word over P′ decoding to a block.
record Part : Set where
  constructor part
  field
    pw : Word (GenP 16)
    pb : Blk
    pd : Decodes pw ⟪ flatB pb ⟫ʷ

open Part public

words : List Part → Word (GenP 16)
words []       = ε
words (p ∷ ps) = pw p • words ps

blocks : List Part → List Blk
blocks = map pb

-- The product of the parts decodes to their blocks flattened.
chainᵈ : (ps : List Part) → Decodes (words ps) ⟪ flat (blocks ps) ⟫ʷ
chainᵈ []       = εᵈ
chainᵈ (p ∷ ps) = ≈ᵈ (pd p •ᵈ chainᵈ ps) (sym (++≈ (flatB (pb p)) (flat (blocks ps))))
