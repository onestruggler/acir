------------------------------------------------------------------------
-- Presentations of groups
--
-- Commuting gates on disjoint wires.
--
-- Selinger works in a strict spatial monoidal groupoid, so the
-- bifunctorial law -- gates on disjoint sets of qubits commute -- is
-- built into the setting and never appears as a step of a proof (§2).
-- Here it is Circuit.Base's structural comm₁, and it does have to be
-- applied; this module packages it in the form the two-wire derivations
-- of Lemmas and the replay of Figures 3-7 keep needing.
--
-- The shape that comes up is always the same: a word written on the
-- bottom (un-shifted) wire alone, crossed by a whole circuit that has
-- been shifted up past it.  Lift-Relation's comm-gate₁-w↑ does one
-- letter of that; comm-bot walks it across the word.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger2.Wires where

open import Data.Nat using (ℕ)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB

open import Examples.Groups.Clifford.Qubit.Selinger2.Figure8

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Bottom-wire words
--
-- A word of 1-ary gates, read on the un-shifted wire.  Being a _ʷ, it
-- distributes over concatenation definitionally, so `bot` never has to
-- be unfolded by hand: bot ([ H-gate ]ʷ • [ S-gate ]ʷ) IS H ↓ • S ↓.

bot : Word (ExactGate 1) → Circuit (₁₊ n)
bot = ((λ g → [ gate₁ g ]ʷ) ʷ)

------------------------------------------------------------------------
-- A shifted circuit commutes with any bottom-wire word

comm-bot : ∀ (w : Circuit n) (t : Word (ExactGate 1)) →
  let open PB ((₁₊ n) CRel,_===_) using (_≈_)
  in w ↑ • bot t ≈ bot t • w ↑
comm-bot w [ g ]ʷ  = comm-gate₁-w↑ g w
comm-bot w ε       = PB.trans PB.right-unit (PB.sym PB.left-unit)
comm-bot w (t • u) =
  PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (comm-bot w t) PB.refl)
      (PB.trans PB.assoc
        (PB.trans (PB.cong PB.refl (comm-bot w u)) (PB.sym PB.assoc))))
