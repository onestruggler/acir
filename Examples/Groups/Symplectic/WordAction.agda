------------------------------------------------------------------------
-- Presentations of groups
--
-- The symplectic action of a whole circuit word, for the plain gate set.
--
-- Examples.Groups.Symplectic.Semantics interprets a circuit as a
-- Symplectic record (Interpretation.⟦_⟧); several clients instead want
-- the bare action as a function, defined by recursion on the word:
--
--     act = word-act actg.
--
-- The two agree pointwise (act≡ap), but only propositionally: for a
-- variable word the two recursions are stuck at different heads, so the
-- bridge lemma is needed whenever a result stated for one is used on the
-- other.  act-sound-ax is the ⟦_⟧-free restatement of Transport.sound-ax
-- that this buys.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.WordAction
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Presentation.GroupLike using (word-act)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Pauli.Semantics p-2 p-prime using (Pauli)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (Gen ; Circuit ; _QRel,_===_)

open import Examples.Groups.Symplectic.Semantics p-2 p-prime as Sem using ()
open Sem.Symplectic using (ap)
open Sem.Interpretation using (actg ; ⟦_⟧)

open import Examples.Groups.Symplectic.Transport p-2 p-prime using (sound-ax)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The action of a circuit word

act : Word (Gen n) → Pauli n → Pauli n
act = word-act actg

------------------------------------------------------------------------
-- Agreement with the Symplectic-valued interpretation

-- Both are multiplicative over _•_ and agree on generators, so they
-- agree everywhere.
act≡ap : (w : Circuit n) (x : Pauli n) → act w x ≡ ap ⟦ w ⟧ x
act≡ap [ g ]ʷ  x = Eq.refl
act≡ap ε       x = Eq.refl
act≡ap (w • v) x =
  Eq.trans (Eq.cong (act w) (act≡ap v x)) (act≡ap w (ap ⟦ v ⟧ x))

------------------------------------------------------------------------
-- Soundness, stated for act

-- Transport.sound-ax with both sides pushed along act≡ap.
act-sound-ax : (w v : Circuit n) → n QRel, w === v → ∀ x → act w x ≡ act v x
act-sound-ax w v r x =
  Eq.trans (act≡ap w x) (Eq.trans (sound-ax r x) (Eq.sym (act≡ap v x)))
