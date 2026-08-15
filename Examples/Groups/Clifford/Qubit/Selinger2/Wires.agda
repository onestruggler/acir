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

------------------------------------------------------------------------
-- Lifting an equation onto higher wires
--
-- Lift-Relation's lemma-cong↑ takes its two words EXPLICITLY, because the
-- congruence's implicit arguments cannot be inferred from the proof
-- alone.  A rule of Figures 3-7 is applied at whatever wire offset the
-- step calls for, so the replay lifts a lemma k times; writing the two
-- words out at each of those k stages is exactly the sort of bulk the
-- generator should not have to produce.  `up` is the same lemma with the
-- words implicit, so a lift reads `up (up lem)` however deep it goes.

up : ∀ {w v : Circuit n} →
  let open PB (n CRel,_===_)        using (_≈_)
      open PB ((₁₊ n) CRel,_===_) renaming (_≈_ to _≈↑_) using ()
  in w ≈ v → w ↑ ≈↑ v ↑
up {w = w} {v = v} = lemma-cong↑ w v

------------------------------------------------------------------------
-- Rewriting inside a right-nested word
--
-- Words are right-nested, so in g • h • post the subterm (g • h) does
-- not occur: the term is g • (h • post).  swap1 re-brackets, applies the
-- commutation, and brackets back, so a transposition at position i of a
-- word is `cright … cright (swap1 e)` with i crights and nothing else.
-- With one of these per swap the replay of Figures 3-7 needs no
-- associativity steps of its own for its commutation legs.

swap1 : ∀ {g h post : Circuit n} →
  let open PB (n CRel,_===_) using (_≈_)
  in g • h ≈ h • g → g • h • post ≈ h • g • post
swap1 e = PB.trans (PB.sym PB.assoc)
            (PB.trans (PB.cong e PB.refl) PB.assoc)

-- Apply an equation inside a context, with the context given EXPLICITLY.
-- `cright cleft e` leaves the two context words as metas that by-assoc's
-- to-list equation cannot solve, so the replay names them: the emitter
-- knows both, and printing them is cheaper than making Agda guess.
at : ∀ (pre : Circuit n) {u v : Circuit n} (post : Circuit n) →
  let open PB (n CRel,_===_) using (_≈_)
  in u ≈ v → pre • u • post ≈ pre • v • post
at pre post e = PB.cong PB.refl (PB.cong e PB.refl)
