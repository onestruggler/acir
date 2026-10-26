------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the four-wire derivations, each decided once
--
-- Each lemma is one window step of Four/D: two words on three wires with
-- the same operator, equal by completeness on three wires
-- (Windows.win, one evaluation, through the tables of Four.Lits),
-- stated over the macro letters as Four/D uses it.  Written by
-- scratchpad/four/winlib4.py, restated by winmac4.py and wintable4.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Wins.W49 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

wn02572 : Base 3 → ⟪ (ℓ "丈丈丌丒丘丷丈九三丒丷丈九三丘丷丈九三丒丷丈九三丌丒") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
wn02572 b = lw3 b (ℓ "丈丈丌丒丘丷丈九三丒丷丈九三丘丷丈九三丒丷丈九三丌丒") (ℓ "丌") tt tt Eq.refl
wn02573 : Base 3 → ⟪ (ℓ "丕丼") ⟫ʷ ≈ ⟪ (ℓ "丼丏") ⟫ʷ
wn02573 b = lw3 b (ℓ "丕丼") (ℓ "丼丏") tt tt Eq.refl
wn02574 : Base 3 → ⟪ (ℓ "丗丼") ⟫ʷ ≈ ⟪ (ℓ "丼丑") ⟫ʷ
wn02574 b = lw3 b (ℓ "丗丼") (ℓ "丼丑") tt tt Eq.refl
wn02575 : Base 3 → ⟪ (ℓ "与与丒丘丨与习丏丘丨与习丏丌丘丨与习丏丘丨与习丏丌丒") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
wn02575 b = lw3 b (ℓ "与与丒丘丨与习丏丘丨与习丏丌丘丨与习丏丘丨与习丏丌丒") (ℓ "丒") tt tt Eq.refl
wn02576 : Base 3 → ⟪ (ℓ "且且丌丘両且乣丕丌両且乣丕丌丒両且乣丕丌両且乣丕丒丘") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
wn02576 b = lw3 b (ℓ "且且丌丘両且乣丕丌両且乣丕丌丒両且乣丕丌両且乣丕丒丘") (ℓ "丘") tt tt Eq.refl
wn02577 : Base 3 → ⟪ (ℓ "且且丌丒丘両且乣丕丌両且乣丕丌丒両且乣丕丌両且乣丕丘") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
wn02577 b = lw3 b (ℓ "且且丌丒丘両且乣丕丌両且乣丕丌丒両且乣丕丌両且乣丕丘") (ℓ "丘") tt tt Eq.refl
wn02578 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "与丏") ⟫ʷ
wn02578 b = lw3 b [] (ℓ "与丏") tt tt Eq.refl
wn02579 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "丐丑") ⟫ʷ
wn02579 b = lw3 b [] (ℓ "丐丑") tt tt Eq.refl
wn02580 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "丏与") ⟫ʷ
wn02580 b = lw3 b [] (ℓ "丏与") tt tt Eq.refl
wn02581 : Base 3 → ⟪ (ℓ "丏与") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02581 b = lw3 b (ℓ "丏与") [] tt tt Eq.refl
wn02582 : Base 3 → ⟪ (ℓ "丐丑") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02582 b = lw3 b (ℓ "丐丑") [] tt tt Eq.refl
wn02583 : Base 3 → ⟪ (ℓ "与丏") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02583 b = lw3 b (ℓ "与丏") [] tt tt Eq.refl
wn02584 : Base 3 → ⟪ (ℓ "丳丢丢丣丳丢") ⟫ʷ ≈ ⟪ (ℓ "丢並") ⟫ʷ
wn02584 b = lw3 b (ℓ "丳丢丢丣丳丢") (ℓ "丢並") tt tt Eq.refl
