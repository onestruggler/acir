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

module Examples.Groups.Clifford+CS.Four.Wins.W03 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)

wn00409 : Base 3 → ⟪ (CS23 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00409 b = lw1 b (CS23 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS23 ∷ []) tt tt Eq.refl
wn00410 : Base 3 → ⟪ (CS13 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CS13 ∷ []) ⟫ʷ
wn00410 b = lw0 b (CS13 ∷ CS23 ∷ []) (CS23 ∷ CS13 ∷ []) tt tt Eq.refl
wn00411 : Base 3 → ⟪ (CX31 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX31 ∷ []) ⟫ʷ
wn00411 b = lw0 b (CX31 ∷ CS23 ∷ []) (CS23 ∷ CX31 ∷ []) tt tt Eq.refl
wn00412 : Base 3 → ⟪ (CS23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS23 ∷ []) ⟫ʷ
wn00412 b = lw0 b (CS23 ∷ CS12 ∷ []) (CS12 ∷ CS23 ∷ []) tt tt Eq.refl
wn00413 : Base 3 → ⟪ (CS23 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ CS23 ∷ []) ⟫ʷ
wn00413 b = lw0 b (CS23 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ CS23 ∷ []) tt tt Eq.refl
wn00414 : Base 3 → ⟪ (CX12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX21 ∷ []) ⟫ʷ
wn00414 b = lw3 b (CX12 ∷ Sw12 ∷ []) (Sw12 ∷ CX21 ∷ []) tt tt Eq.refl
wn00415 : Base 3 → ⟪ (CS02 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CS02 ∷ []) ⟫ʷ
wn00415 b = lw3 b (CS02 ∷ CZ01 ∷ []) (CZ01 ∷ CS02 ∷ []) tt tt Eq.refl
wn00416 : Base 3 → ⟪ (CS12 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00416 b = lw0 b (CS12 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS12 ∷ []) tt tt Eq.refl
wn00417 : Base 3 → ⟪ (CS02⁻ ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00417 b = lw3 b (CS02⁻ ∷ CZ01 ∷ []) (CZ01 ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn00418 : Base 3 → ⟪ (CS12⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00418 b = lw0 b (CS12⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00419 : Base 3 → ⟪ (X3 ∷ CK32 ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn00419 b = lw0 b (X3 ∷ CK32 ∷ X3 ∷ Toff123 ∷ []) (Toff123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) tt tt Eq.refl
wn00420 : Base 3 → ⟪ (CS13 ∷ ι3 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ CS13 ∷ []) ⟫ʷ
wn00420 b = lw0 b (CS13 ∷ ι3 ∷ []) (ι3 ∷ CS13 ∷ []) tt tt Eq.refl
wn00421 : Base 3 → ⟪ (CS13 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS13 ∷ []) ⟫ʷ
wn00421 b = lw0 b (CS13 ∷ S3⁻ ∷ []) (S3⁻ ∷ CS13 ∷ []) tt tt Eq.refl
wn00422 : Base 3 → ⟪ (CS13 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS13 ∷ []) ⟫ʷ
wn00422 b = lw0 b (CS13 ∷ S3 ∷ []) (S3 ∷ CS13 ∷ []) tt tt Eq.refl
wn00423 : Base 3 → ⟪ (CS12 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
wn00423 b = lw3 b (CS12 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS12 ∷ []) tt tt Eq.refl
wn00424 : Base 3 → ⟪ (CX20 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX20 ∷ []) ⟫ʷ
wn00424 b = lw3 b (CX20 ∷ CS12 ∷ []) (CS12 ∷ CX20 ∷ []) tt tt Eq.refl
wn00425 : Base 3 → ⟪ (CS12 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00425 b = lw3 b (CS12 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS12 ∷ []) tt tt Eq.refl
wn00426 : Base 3 → ⟪ (CS23 ∷ ι3 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ CS23 ∷ []) ⟫ʷ
wn00426 b = lw0 b (CS23 ∷ ι3 ∷ []) (ι3 ∷ CS23 ∷ []) tt tt Eq.refl
wn00427 : Base 3 → ⟪ (CS23 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00427 b = lw0 b (CS23 ∷ S3⁻ ∷ []) (S3⁻ ∷ CS23 ∷ []) tt tt Eq.refl
wn00428 : Base 3 → ⟪ (CS23 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS23 ∷ []) ⟫ʷ
wn00428 b = lw0 b (CS23 ∷ S3 ∷ []) (S3 ∷ CS23 ∷ []) tt tt Eq.refl
wn00429 : Base 3 → ⟪ (Toff201 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff201 ∷ []) ⟫ʷ
wn00429 b = lw3 b (Toff201 ∷ ι ∷ []) (ι ∷ Toff201 ∷ []) tt tt Eq.refl
wn00430 : Base 3 → ⟪ (CS23⁻ ∷ ι3 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00430 b = lw0 b (CS23⁻ ∷ ι3 ∷ []) (ι3 ∷ CS23⁻ ∷ []) tt tt Eq.refl
wn00431 : Base 3 → ⟪ (S0⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn00431 b = lw1 b (S0⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn00432 : Base 3 → ⟪ (S3⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S3⁻ ∷ []) ⟫ʷ
wn00432 b = lw0 b (S3⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S3⁻ ∷ []) tt tt Eq.refl
wn00433 : Base 3 → ⟪ (CS13 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS13 ∷ []) ⟫ʷ
wn00433 b = lw0 b (CS13 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS13 ∷ []) tt tt Eq.refl
wn00434 : Base 3 → ⟪ (S0⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S1⁻ ∷ []) ⟫ʷ
wn00434 b = lw3 b (S0⁻ ∷ Sw01 ∷ []) (Sw01 ∷ S1⁻ ∷ []) tt tt Eq.refl
wn00435 : Base 3 → ⟪ (ι ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ ι ∷ []) ⟫ʷ
wn00435 b = lw3 b (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι ∷ []) tt tt Eq.refl
wn00436 : Base 3 → ⟪ (CS23 ∷ ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ CS23 ∷ []) ⟫ʷ
wn00436 b = lw0 b (CS23 ∷ ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ []) (ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ CS23 ∷ []) tt tt Eq.refl
wn00437 : Base 3 → ⟪ (Sw01 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Sw01 ∷ []) ⟫ʷ
wn00437 b = lw3 b (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) tt tt Eq.refl
wn00438 : Base 3 → ⟪ (Toff201 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Toff201 ∷ []) ⟫ʷ
wn00438 b = lw3 b (Toff201 ∷ S0⁻ ∷ []) (S0⁻ ∷ Toff201 ∷ []) tt tt Eq.refl
wn00439 : Base 3 → ⟪ (CS23⁻ ∷ ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00439 b = lw0 b (CS23⁻ ∷ ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ []) (ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ CS23⁻ ∷ []) tt tt Eq.refl
wn00440 : Base 3 → ⟪ (CS23 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS23 ∷ []) ⟫ʷ
wn00440 b = lw0 b (CS23 ∷ S2 ∷ []) (S2 ∷ CS23 ∷ []) tt tt Eq.refl
wn00441 : Base 3 → ⟪ (CS23 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00441 b = lw0 b (CS23 ∷ S2⁻ ∷ []) (S2⁻ ∷ CS23 ∷ []) tt tt Eq.refl
wn00442 : Base 3 → ⟪ (CS23 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS23 ∷ []) ⟫ʷ
wn00442 b = lw0 b (CS23 ∷ S1 ∷ []) (S1 ∷ CS23 ∷ []) tt tt Eq.refl
wn00443 : Base 3 → ⟪ (CS23 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00443 b = lw0 b (CS23 ∷ S1⁻ ∷ []) (S1⁻ ∷ CS23 ∷ []) tt tt Eq.refl
wn00444 : Base 3 → ⟪ (CCZ012 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ012 ∷ []) ⟫ʷ
wn00444 b = lw3 b (CCZ012 ∷ CS01 ∷ []) (CS01 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00445 : Base 3 → ⟪ (S2 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S2 ∷ []) ⟫ʷ
wn00445 b = lw0 b (S2 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S2 ∷ []) tt tt Eq.refl
wn00446 : Base 3 → ⟪ (CCZ012 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00446 b = lw3 b (CCZ012 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00447 : Base 3 → ⟪ (S2⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S2⁻ ∷ []) ⟫ʷ
wn00447 b = lw0 b (S2⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S2⁻ ∷ []) tt tt Eq.refl
wn00448 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn00448 b = lw0 b (X3 ∷ CK31 ∷ X3 ∷ Toff213 ∷ []) (Toff213 ∷ X3 ∷ CK31 ∷ X3 ∷ []) tt tt Eq.refl
wn00449 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn00449 b = lw0 b (X3 ∷ CS13 ∷ X3 ∷ Toff213 ∷ []) (Toff213 ∷ X3 ∷ CS13 ∷ X3 ∷ []) tt tt Eq.refl
wn00450 : Base 3 → ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn00450 b = lw0 b (X3 ∷ CS13⁻ ∷ X3 ∷ Toff213 ∷ []) (Toff213 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn00451 : Base 3 → ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn00451 b = lw0 b (X3 ∷ CK31⁻ ∷ X3 ∷ Toff213 ∷ []) (Toff213 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) tt tt Eq.refl
wn00452 : Base 3 → ⟪ (X1 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ
wn00452 b = lw3 b (X1 ∷ S1 ∷ K1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) tt tt Eq.refl
wn00453 : Base 3 → ⟪ (K1⁻ ∷ S1⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ
wn00453 b = lw3 b (K1⁻ ∷ S1⁻ ∷ X1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) tt tt Eq.refl
wn00454 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn00454 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn00455 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn00455 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn00456 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn00456 b = lw3 b (X1 ∷ CS01⁻ ∷ X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl
wn00457 : Base 3 → ⟪ (CX21 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CX21 ∷ []) ⟫ʷ
wn00457 b = lw0 b (CX21 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX21 ∷ []) tt tt Eq.refl
wn00458 : Base 3 → ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX10 ∷ CX20 ∷ Toff012 ∷ []) ⟫ʷ
wn00458 b = lw3 b (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X0 ∷ CX10 ∷ CX20 ∷ Toff012 ∷ []) tt tt Eq.refl
wn00459 : Base 3 → ⟪ (CS02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S2 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00459 b = lw3 b (CS02 ∷ X0 ∷ []) (X0 ∷ S2 ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn00460 : Base 3 → ⟪ (CS02⁻ ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00460 b = lw3 b (CS02⁻ ∷ CX10 ∷ []) (CX10 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00461 : Base 3 → ⟪ (CCZ012 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CZ12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00461 b = lw3 b (CCZ012 ∷ CX20 ∷ []) (CX20 ∷ CZ12 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00462 : Base 3 → ⟪ (CS12⁻ ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00462 b = lw3 b (CS12⁻ ∷ CX20 ∷ []) (CX20 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00463 : Base 3 → ⟪ (CS02⁻ ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ S2⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00463 b = lw3 b (CS02⁻ ∷ CX20 ∷ []) (CX20 ∷ S2⁻ ∷ CS02 ∷ []) tt tt Eq.refl
wn00464 : Base 3 → ⟪ (S3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ S2 ∷ []) ⟫ʷ
wn00464 b = lw0 b (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) tt tt Eq.refl
wn00465 : Base 3 → ⟪ (S2 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ S2 ∷ []) ⟫ʷ
wn00465 b = lw3 b (S2 ∷ CX20 ∷ []) (CX20 ∷ S2 ∷ []) tt tt Eq.refl
wn00466 : Base 3 → ⟪ (CCZ012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00466 b = lw3 b (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00467 : Base 3 → ⟪ (CZ12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CZ12 ∷ []) ⟫ʷ
wn00467 b = lw3 b (CZ12 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ []) tt tt Eq.refl
wn00468 : Base 3 → ⟪ (CS12⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00468 b = lw3 b (CS12⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00469 : Base 3 → ⟪ (CS02 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00469 b = lw3 b (CS02 ∷ Toff012 ∷ []) (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00470 : Base 3 → ⟪ (S0 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S0 ∷ []) ⟫ʷ
wn00470 b = lw1 b (S0 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn00471 : Base 3 → ⟪ (CS13⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wn00471 b = lw0 b (CS13⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl
wn00472 : Base 3 → ⟪ (Toff102 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff102 ∷ []) ⟫ʷ
wn00472 b = lw3 b (Toff102 ∷ ι ∷ []) (ι ∷ Toff102 ∷ []) tt tt Eq.refl
wn00473 : Base 3 → ⟪ (CS13⁻ ∷ ι3 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ CS13⁻ ∷ []) ⟫ʷ
wn00473 b = lw0 b (CS13⁻ ∷ ι3 ∷ []) (ι3 ∷ CS13⁻ ∷ []) tt tt Eq.refl
wn00474 : Base 3 → ⟪ (CS13⁻ ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wn00474 b = lw0 b (CS13⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl
wn00475 : Base 3 → ⟪ (CS13⁻ ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS13⁻ ∷ []) ⟫ʷ
wn00475 b = lw0 b (CS13⁻ ∷ S3 ∷ []) (S3 ∷ CS13⁻ ∷ []) tt tt Eq.refl
wn00476 : Base 3 → ⟪ (S2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ S3 ∷ []) ⟫ʷ
wn00476 b = lw0 b (S2 ∷ Sw23 ∷ []) (Sw23 ∷ S3 ∷ []) tt tt Eq.refl
wn00477 : Base 3 → ⟪ (S2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S1 ∷ []) ⟫ʷ
wn00477 b = lw3 b (S2 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ []) tt tt Eq.refl
wn00478 : Base 3 → ⟪ (CX21 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX12 ∷ []) ⟫ʷ
wn00478 b = lw3 b (CX21 ∷ Sw12 ∷ []) (Sw12 ∷ CX12 ∷ []) tt tt Eq.refl
wn00479 : Base 3 → ⟪ (S1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S2 ∷ []) ⟫ʷ
wn00479 b = lw3 b (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) tt tt Eq.refl
wn00480 : Base 3 → ⟪ (CK01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK10 ∷ []) ⟫ʷ
wn00480 b = lw3 b (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ []) tt tt Eq.refl
wn00481 : Base 3 → ⟪ (S0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S1 ∷ []) ⟫ʷ
wn00481 b = lw3 b (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) tt tt Eq.refl
wn00482 : Base 3 → ⟪ (CX32 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CX32 ∷ []) ⟫ʷ
wn00482 b = lw0 b (CX32 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CX32 ∷ []) tt tt Eq.refl
wn00483 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00483 b = lw3 b (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
wn00484 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00484 b = lw3 b (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
wn00485 : Base 3 → ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn00485 b = lw3 b (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) tt tt Eq.refl
wn00486 : Base 3 → ⟪ (CX32 ∷ X3 ∷ CX31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CX31 ∷ X3 ∷ CX32 ∷ []) ⟫ʷ
wn00486 b = lw0 b (CX32 ∷ X3 ∷ CX31 ∷ X3 ∷ []) (X3 ∷ CX31 ∷ X3 ∷ CX32 ∷ []) tt tt Eq.refl
wn00487 : Base 3 → ⟪ (S2 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ S2 ∷ []) ⟫ʷ
wn00487 b = lw0 b (S2 ∷ CX31 ∷ []) (CX31 ∷ S2 ∷ []) tt tt Eq.refl
wn00488 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CX21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00488 b = lw3 b (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
wn00489 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00489 b = lw3 b (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
wn00490 : Base 3 → ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn00490 b = lw3 b (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) tt tt Eq.refl
wn00491 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00491 b = lw0 b (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) tt tt Eq.refl
wn00492 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00492 b = lw0 b (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) tt tt Eq.refl
wn00493 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00493 b = lw0 b (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) tt tt Eq.refl
wn00494 : Base 3 → ⟪ (CX32 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ CX32 ∷ []) ⟫ʷ
wn00494 b = lw0 b (CX32 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ CX32 ∷ []) tt tt Eq.refl
wn00495 : Base 3 → ⟪ (S2 ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ S2 ∷ []) ⟫ʷ
wn00495 b = lw0 b (S2 ∷ CK31 ∷ []) (CK31 ∷ S2 ∷ []) tt tt Eq.refl
wn00496 : Base 3 → ⟪ (CK20 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CK20 ∷ []) ⟫ʷ
wn00496 b = lw3 b (CK20 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ CK20 ∷ []) tt tt Eq.refl
wn00497 : Base 3 → ⟪ (CS02 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00497 b = lw3 b (CS02 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ []) tt tt Eq.refl
wn00498 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00498 b = lw0 b (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) tt tt Eq.refl
wn00499 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00499 b = lw0 b (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) tt tt Eq.refl
wn00500 : Base 3 → ⟪ (CX32 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CX32 ∷ []) ⟫ʷ
wn00500 b = lw0 b (CX32 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CX32 ∷ []) tt tt Eq.refl
wn00501 : Base 3 → ⟪ (S2 ∷ CK31⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ S2 ∷ []) ⟫ʷ
wn00501 b = lw0 b (S2 ∷ CK31⁻ ∷ []) (CK31⁻ ∷ S2 ∷ []) tt tt Eq.refl
wn00502 : Base 3 → ⟪ (CK20 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CK20 ∷ []) ⟫ʷ
wn00502 b = lw3 b (CK20 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CK20 ∷ []) tt tt Eq.refl
wn00503 : Base 3 → ⟪ (CS02 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00503 b = lw3 b (CS02 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ []) tt tt Eq.refl
wn00504 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00504 b = lw0 b (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) tt tt Eq.refl
wn00505 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00505 b = lw3 b (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
wn00506 : Base 3 → ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn00506 b = lw3 b (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) tt tt Eq.refl
wn00507 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00507 b = lw3 b (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) tt tt Eq.refl
