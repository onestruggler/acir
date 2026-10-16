{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D154 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at0114203243 ; lem-sym12-at0214203143 ; lem-sym12-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-c124-beta-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at0110243243 ; lem-sym12-at0210243143 ; lem-sym12-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-sym23-at0310213442 ; lem-sym23-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-X1-beta-at0114203243 ; lem-X1-beta-at0214203143 ; lem-X1-beta-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-CS12-beta-at0220 ; lem-auto-CS01-∣-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-auto-SBOXd⟨0·1·2·3⟩-∣-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.D145 using (lem-sym12-at122441 ; lem-sym12-at142142 ; lem-sym12-at1441 ; lem-sym12-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D151 using (lem-auto-CS01-∣-BOX⟨1·2034⟩ ; lem-auto-S0-∣-BOX⟨1·2034⟩)
open import Examples.Groups.Clifford+CS.Five.D.D153 using (lem-auto-CSd01-∣-BOX⟨0·1234⟩-at12213443)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-CCZ023 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOX⟨0·1243⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨0·4132⟩ ; lem-nat-1-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-1-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-3-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-1-BOX⟨0·2143⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨0·2143⟩ ; lem-nat-0-BOX⟨1·2043⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-BOX⟨1·4032⟩ ; lem-nat-2-BOX⟨0·4123⟩ ; lem-nat-2-BOX⟨0·4132⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨3·0412⟩ ; lem-nat-1-CS04 ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-BOX⟨1·0432⟩ ; lem-nat-2-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-2-BOX⟨3·0421⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-3-CS04)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-2-BOX⟨1·0234⟩ ; lem-nat-2-CS04 ; lem-nat-3-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-0-BOX⟨2·0134⟩ ; lem-nat-0-BOX⟨2·1034⟩ ; lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨0·1432⟩ ; lem-nat-0-BOX⟨0·2431⟩ ; lem-nat-0-BOX⟨1·2430⟩ ; lem-nat-1-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨0·2431⟩ ; lem-nat-1-BOX⟨1·0432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-0-BOX⟨1·0432⟩ ; lem-nat-1-BOX⟨2·0431⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-2-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-1-BOX⟨3·0421⟩ ; lem-nat-2-BOX⟨1·0324⟩ ; lem-nat-2-BOX⟨2·0431⟩ ; lem-nat-3-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-3-BOX⟨1·0324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-1-BOX⟨0·4132⟩ ; lem-nat-1-BOX⟨0·4231⟩)
open import Examples.Groups.Clifford+CS.Five.D.R035 using (lem-nat-0-BOX⟨2·0431⟩ ; lem-nat-0-BOX⟨2·1430⟩ ; lem-nat-1-BOX⟨1·2430⟩ ; lem-nat-1-BOX⟨2·1430⟩)
-- auto CSd01 | BOX(0;1234) @0112203443: 7 steps
lem-auto-CSd01-∣-BOX⟨0·1234⟩-at0112203443 : Complete 4 → ⟪ (CS12⁻ ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·1234⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12⁻ ∷ Bx1-2043 ∷ []) (Bx1-2043 ∷ CS12⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2043⟩ c4) ▸
       at 1 2 (Bx0-2143 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·1234⟩-at12213443 c4) ▸
       at 0 2 (Bx1-2043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2143⟩ c4) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;2043): 3 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2043⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2043⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx1-2043 ∷ []) (Bx1-2043 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx1-2043 ∷ CS12⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·1234⟩-at0112203443 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;2;3) | SBOX(1;2;04;3): 15 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨1·2·04·3⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Sb1-2-04-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-04-3 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨1·2·04·3⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Sb1-2-04-3 ∷ []) (Bx1-2043 ∷ Toff304 ∷ Sb1-2-3-4 ∷ Sb⁻0-1-2-3 ∷ Toff304 ∷ Sb⁻1-2-3-4 ∷ [])
  b0 = at 1 1 (Bx1-2043 ∷ Toff304 ∷ Sb1-2-3-4 ∷ Toff304 ∷ Sb⁻1-2-3-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-2043 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2043⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-TOFF304 c4) ▸
       at 2 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CS23 ∷ []) (refl) ▸
       at 2 2 (CS23 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CS23 ∷ []) (CS23 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-2-3-4 ∷ []) (refl) ▸
       at 3 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx1-2043 ∷ Toff304 ∷ Sb1-2-3-4 ∷ Sb⁻0-1-2-3 ∷ Toff304 ∷ Sb⁻1-2-3-4 ∷ []) (Sb1-2-04-3 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 3 2 (Toff304 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-TOFF304 c4) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 1 (CS23⁻ ∷ []) (refl) ▸
       at 4 2 (CS23⁻ ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-2-3-4 ∷ []) (refl) ▸
       at 5 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-2-04-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(0;1234) @3443: 7 steps
lem-auto-CS01-∣-BOX⟨0·1234⟩-at3443 : Complete 4 → ⟪ (CS01 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·1234⟩-at3443 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨0·1234⟩ c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(0;1234) @12213443: 7 steps
lem-auto-CS01-∣-BOX⟨0·1234⟩-at12213443 : Complete 4 → ⟪ (CS02 ∷ Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·1234⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx0-2143 ∷ []) (Bx0-2143 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ c4) ▸
       at 1 2 (Bx0-1243 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨0·1234⟩-at3443 c4) ▸
       at 0 2 (Bx0-2143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(0;1234) @0112203443: 7 steps
lem-auto-CS01-∣-BOX⟨0·1234⟩-at0112203443 : Complete 4 → ⟪ (CS12 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·1234⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12 ∷ Bx1-2043 ∷ []) (Bx1-2043 ∷ CS12 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2043⟩ c4) ▸
       at 1 2 (Bx0-2143 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨0·1234⟩-at12213443 c4) ▸
       at 0 2 (Bx1-2043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2143⟩ c4) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;2043): 3 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·2043⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·2043⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx1-2043 ∷ []) (Bx1-2043 ∷ Sb0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Bx1-2043 ∷ CS12 ∷ []) (lem-auto-CS01-∣-BOX⟨0·1234⟩-at0112203443 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- auto CCZ012 | BOX(3;0412): 3 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4) ▸
       at 0 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4) ▸ done


-- auto CCZ012 | BOX(3;0412) @2332: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 : Complete 4 → ⟪ (CCZ013 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx3-0412 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | BOX(1;2034) @0110: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at0110 : Complete 4 → ⟪ (S1 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ S1 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at0110 c4 = run b0
  where
  b0 : Chain (S1 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ S1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Bx1-2034 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (S1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ S0 ∷ []) (S1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | BOX(1;2034) @021021: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at021021 : Complete 4 → ⟪ (S2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S2 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at021021 c4 = run b0
  where
  b0 : Chain (S2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S2 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ S2 ∷ []) (S1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Bx0-2134 ∷ S1 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0110 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (S2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ S1 ∷ []) (S2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | BOX(1;2034) @03102132: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at03102132 : Complete 4 → ⟪ (S3 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ S3 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at03102132 c4 = run b0
  where
  b0 : Chain (S3 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ S3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ S3 ∷ []) (S2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ S2 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at021021 c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (S3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | BOX(1;2034) @0410213243: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 : Complete 4 → ⟪ (S4 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (S4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ S4 ∷ []) (S3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ S3 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at03102132 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (S4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ S3 ∷ []) (S4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | BOX(1;2034) @04203243: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at04203243 : Complete 4 → ⟪ (S4 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at04203243 c4 = run b0
  where
  b0 : Chain (S4 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | BOX(1;2034) @0412203143: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at0412203143 : Complete 4 → ⟪ (S4 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (S4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at04203243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 iI^0|CS01^1: 24 steps
lem-F4-iIᵖ0∣CS01ᵖ1 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-iIᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 2 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 3 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 1 2 (Bx2-0413 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0412203143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 4 2 (X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ S4 ∷ X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b2 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ S4 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ S4 ∷ X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ S4 ∷ X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- auto CCZ012 | BOX(3;0412) @122331: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 : Complete 4 → ⟪ (CCZ023 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 iI^0|CS02^1: 24 steps
lem-F4-iIᵖ0∣CS02ᵖ1 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-iIᵖ0∣CS02ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (X4 ∷ Bx1-0423 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b0 = at 3 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 2 3 (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4) ▸
       at 3 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 2 2 (Bx1-0423 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4) ▸
       at 1 2 (Bx1-0423 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at04203243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx1-0423 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b1 = at 1 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 0 3 (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 0 2 (Bx1-0423 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4) ▸
       at 4 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ S4 ∷ X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx1-0423 ∷ Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Sb1-0-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b2 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ S4 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ S4 ∷ X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ S4 ∷ X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done


-- sym12 @01102442: 5 steps
lem-sym12-at01102442 : Complete 4 → ⟪ (Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4032 ∷ []) ⟫ʷ
lem-sym12-at01102442 c4 = run b0
  where
  b0 : Chain (Bx1-0432 ∷ []) (Bx1-4032 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 1 (Bx0-4132 ∷ []) (lem-sym12-at2442 c4) ▸
       at 0 2 (Bx1-4032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4132⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @142142: 8 steps
lem-X1-beta-at142142 : Complete 4 → ⟪ (X4 ∷ Bx0-4132 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-4132 ∷ []) ⟫ʷ
lem-X1-beta-at142142 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx0-4132 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4132 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 2 2 (Bx0-4123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4132⟩ c4) ▸
       at 3 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 1 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @01142042: 8 steps
lem-X1-beta-at01142042 : Complete 4 → ⟪ (X4 ∷ Bx1-4032 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx1-4032 ∷ []) ⟫ʷ
lem-X1-beta-at01142042 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx1-4032 ∷ X4 ∷ []) (CCZ023 ∷ Bx1-4032 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 2 2 (Bx0-4132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4032⟩ c4) ▸
       at 3 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 1 3 (CCZ123 ∷ Bx0-4132 ∷ []) (lem-X1-beta-at142142 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-4032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4132⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @01142042: 5 steps
lem-sym12-at01142042 : Complete 4 → ⟪ (Bx1-4032 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ []) ⟫ʷ
lem-sym12-at01142042 c4 = run b0
  where
  b0 : Chain (Bx1-4032 ∷ []) (Bx1-0432 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4032⟩ c4) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym12-at142142 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;0412) @1221: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1221 : Complete 4 → ⟪ (CCZ012 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0421 ∷ []) (Bx3-0421 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (Bx3-0412 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;0412) @132132: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at132132 : Complete 4 → ⟪ (CCZ013 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx2-0431 ∷ []) (Bx2-0431 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Bx3-0421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Bx3-0421 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1221 c4) ▸
       at 0 2 (Bx2-0431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;0412) @1331: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 : Complete 4 → ⟪ (CCZ023 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Bx2-0431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Bx2-0431 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at132132 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | BOX(1;2034) @04102142: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at04102142 : Complete 4 → ⟪ (S4 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at04102142 c4 = run b0
  where
  b0 : Chain (S4 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 2 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | BOX(1;2034) @042042: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at042042 : Complete 4 → ⟪ (S4 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at042042 c4 = run b0
  where
  b0 : Chain (S4 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 2 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at04102142 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 iI^0|CS03^1: 24 steps
lem-F4-iIᵖ0∣CS03ᵖ1 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-iIᵖ0∣CS03ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ023 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b0 = at 3 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 2 3 (CCZ023 ∷ Bx1-4032 ∷ []) (lem-X1-beta-at01142042 c4) ▸
       at 3 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 2 2 (Bx1-0432 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 c4) ▸
       at 1 2 (Bx1-0432 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at042042 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ023 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ X4 ∷ S4 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b1 = at 1 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 0 3 (CCZ023 ∷ Bx1-4032 ∷ []) (lem-X1-beta-at01142042 c4) ▸
       at 1 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 0 2 (Bx1-0432 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 c4) ▸
       at 4 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ S4 ∷ X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff234 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx1-0432 ∷ Toff234 ∷ X4 ∷ S4 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b2 = at 5 1 (CS02 ∷ []) (refl) ▸
       at 2 4 (CS02 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ S4 ∷ X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 3 4 (Toff234 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 4 (CS02⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ S4 ∷ X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- auto CCZ012 | BOX(3;0412) @01122330: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 : Complete 4 → ⟪ (CCZ123 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 iI^0|CS12^1: 24 steps
lem-F4-iIᵖ0∣CS12ᵖ1 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-iIᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 3 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 1 2 (Bx0-1423 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ S4 ∷ X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b2 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CS13 ∷ []) (CS13 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- auto CCZ012 | BOX(3;0412) @011330: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at011330 : Complete 4 → ⟪ (CCZ123 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at011330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Bx1-0432 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 iI^0|CS13^1: 24 steps
lem-F4-iIᵖ0∣CS13ᵖ1 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-iIᵖ0∣CS13ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb0-1-43-2 ∷ []) (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ123 ∷ X4 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 3 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-4132 ∷ []) (lem-sym12-at2442 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4132 ∷ []) (lem-X1-beta-at142142 c4) ▸
       at 3 1 (Bx0-1432 ∷ []) (lem-sym12-at142142 c4) ▸
       at 2 2 (Bx0-1432 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at011330 c4) ▸
       at 1 2 (Bx0-1432 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at04102142 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ123 ∷ X4 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (Bx0-1432 ∷ Toff234 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 1 1 (Bx0-4132 ∷ []) (lem-sym12-at2442 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4132 ∷ []) (lem-X1-beta-at142142 c4) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym12-at142142 c4) ▸
       at 0 2 (Bx0-1432 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at011330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ S4 ∷ X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff234 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-1432 ∷ Toff234 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (Sb0-1-43-2 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b2 = at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 4 (Toff234 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- X1-beta @1441: 8 steps
lem-X1-beta-at1441 : Complete 4 → ⟪ (X4 ∷ Bx0-4231 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-4231 ∷ []) ⟫ʷ
lem-X1-beta-at1441 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx0-4231 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4231 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Bx0-4132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4231⟩ c4) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 1 3 (CCZ123 ∷ Bx0-4132 ∷ []) (lem-X1-beta-at142142 c4) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4132⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;0412) @01132032: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01132032 : Complete 4 → ⟪ (CCZ013 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01132032 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx2-1430 ∷ []) (Bx2-1430 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-0431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1430⟩ c4) ▸
       at 1 2 (Bx2-0431 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at132132 c4) ▸
       at 0 2 (Bx2-1430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;0412) @02132031: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132031 : Complete 4 → ⟪ (CCZ023 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132031 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Bx1-2430 ∷ []) (Bx1-2430 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Bx2-1430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2430⟩ c4) ▸
       at 1 2 (Bx2-1430 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01132032 c4) ▸
       at 0 2 (Bx1-2430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1430⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;0412) @02132130: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 : Complete 4 → ⟪ (CCZ123 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-2430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Bx1-2430 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132031 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | BOX(1;2034) @041041: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at041041 : Complete 4 → ⟪ (S4 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at041041 c4 = run b0
  where
  b0 : Chain (S4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at04102142 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 iI^0|CS23^1: 24 steps
lem-F4-iIᵖ0∣CS23ᵖ1 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-iIᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 1 2 (Bx0-2431 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at041041 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ S4 ∷ X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b2 = at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;1034): 3 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩ : Complete 4 → ⟪ (CS01 ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-1034 ∷ []) (Bx2-1034 ∷ CS01 ∷ [])
  b0 = at 0 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Bx2-1034 ∷ CS01 ∷ []) (lem-CS12-beta-at0220 c4) ▸
       at 1 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(2;1034) @0110: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at0110 : Complete 4 → ⟪ (CS01 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at0110 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-1034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0134⟩ c4) ▸
       at 1 2 (Bx2-1034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩ c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(2;1034) @021021: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at021021 : Complete 4 → ⟪ (CS02 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at021021 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Bx2-0134 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at0110 c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(2;1034) @03102132: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at03102132 : Complete 4 → ⟪ (CS03 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 2 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at021021 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(2;1034) @0410213243: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at0410213243 : Complete 4 → ⟪ (CS04 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 c4) ▸
       at 2 2 (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx1-0324 ∷ CS03 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at03102132 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(2;1034) @04103143: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04103143 : Complete 4 → ⟪ (CS04 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04103143 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at0410213243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 S0^0|CS01^1: 24 steps
lem-F4-S0ᵖ0∣CS01ᵖ1 : Complete 4 → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CS04 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 2 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 3 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 1 2 (Bx2-0413 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at04103143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CS04 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 4 2 (X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ CS04 ∷ X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS04 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b2 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS04 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4 S0^0|CS02^1: 24 steps
lem-F4-S0ᵖ0∣CS02ᵖ1 : Complete 4 → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0ᵖ0∣CS02ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (X4 ∷ Bx1-0423 ∷ X4 ∷ X4 ∷ CS04 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b0 = at 3 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 2 3 (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4) ▸
       at 3 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 2 2 (Bx1-0423 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4) ▸
       at 1 2 (Bx1-0423 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at0410213243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx1-0423 ∷ X4 ∷ X4 ∷ CS04 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b1 = at 1 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 0 3 (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 0 2 (Bx1-0423 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4) ▸
       at 4 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ CS04 ∷ X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx1-0423 ∷ Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Sb1-0-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b2 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;1034) @04102142: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04102142 : Complete 4 → ⟪ (CS04 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04102142 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at0410213243 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 S0^0|CS03^1: 24 steps
lem-F4-S0ᵖ0∣CS03ᵖ1 : Complete 4 → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0ᵖ0∣CS03ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ CS04 ∷ CCZ023 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b0 = at 3 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 2 3 (CCZ023 ∷ Bx1-4032 ∷ []) (lem-X1-beta-at01142042 c4) ▸
       at 3 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 2 2 (Bx1-0432 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 c4) ▸
       at 1 2 (Bx1-0432 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at04102142 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ CS04 ∷ CCZ023 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b1 = at 1 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 0 3 (CCZ023 ∷ Bx1-4032 ∷ []) (lem-X1-beta-at01142042 c4) ▸
       at 1 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 0 2 (Bx1-0432 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 c4) ▸
       at 4 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ CS04 ∷ X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff234 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx1-0432 ∷ Toff234 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b2 = at 5 1 (CS02 ∷ []) (refl) ▸
       at 2 4 (CS02 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS04 ∷ X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 3 4 (Toff234 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 4 (CS02⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS04 ∷ X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(1;2034) @0110: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0110 : Complete 4 → ⟪ (CS01 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0110 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(1;2034) @021021: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at021021 : Complete 4 → ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at021021 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Bx0-2134 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at0110 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

