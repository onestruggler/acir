------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness from four wires on, given a decoding (the analogue of
-- Clément's Section 8)
--
-- The encoding of a generator into P′ (Encoding.e) has its matrix
-- (`e-sem`): the word over P′ reads as its two-level spelling
-- (BridgeGray), the spelling is the two-level product the action
-- translated (ActionSound, the product having degree 0 by Degree), and
-- the product reads as the gate (EncodingSemantics.Gates).  With the
-- completeness of the P′ rules for that reading (BridgeGray.complete-P,
-- from Theorem410), what BackAndForth still asks for is the decoding:
-- a circuit for each letter of P′ that respects the rules (the
-- analogue of Lemma 8.8) and inverts the encoding (Lemma 8.7).  Given
-- those two, `Complete.complete` is completeness on 4 + m qubits.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Section8 (m : ℕ) where

open import Word.Base using (Word ; [_]ʷ ; _ʷ)

open import Examples.Groups.Clifford+CS.Semantics using (_~_ ; ~-trans)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Encoding m
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; asG)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (_R,_===_)
open import Examples.Groups.Clifford+CS.BridgeGray n
  using (⟦_⟧Y ; ⟦_⟧ᴾ ; ⟦_⟧PY ; PY-asG ; sound-Y ; module BFP ; module Complete)
open import Examples.Groups.Clifford+CS.ActionSound N′ big using (spell)
open import Examples.Groups.Clifford+CS.EncodingSemantics.Degree m using (deg-E)
open import Examples.Groups.Clifford+CS.EncodingSemantics.Gates m using (eTL-sem)

open Complete big using (complete-P)

------------------------------------------------------------------------
-- The encoding into P′ preserves the semantics

e-sem : ∀ (g : Gen n) → ⟦ e g ⟧PY ~ ⟦ [ g ]ʷ ⟧
e-sem g =
  ~-trans {s = ⟦ e g ⟧PY} {⟦ (asG ʷ) (e g) ⟧Y} {⟦ [ g ]ʷ ⟧} (PY-asG (e g))
    (~-trans {s = ⟦ (asG ʷ) (e g) ⟧Y} {⟦ eTL g ⟧Y} {⟦ [ g ]ʷ ⟧}
      (sound-Y (spell (eTL g) (deg-E g)))
      (eTL-sem g))

------------------------------------------------------------------------
-- Completeness, given the decoding

module Complete′
  (d    : GenP N → Circuit n)                                      -- the decoding
  (d-wd : ∀ {u t : Word (GenP N)} → N R, u === t → n ⊢ (d ʷ) u ≈ (d ʷ) t)  -- Lemma 8.8
  (d∘e  : ∀ (g : Gen n) → n ⊢ [ g ]ʷ ≈ (d ʷ) (e g))                -- Lemma 8.7
  where

  open BFP.Complete complete-P e e-sem d d-wd d∘e public using (complete)
