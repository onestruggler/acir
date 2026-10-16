{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D176 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym12)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at1221 ; lem-sym23-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym12-at0110 ; lem-sym12-at011220 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at122331)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym34-at122331 ; lem-sym34-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ231)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-X1-beta-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442 ; lem-T312-beta-at12233441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-sym34-at01122330 ; lem-sym34-at0112233440)
open import Examples.Groups.Clifford+CS.Five.D.D042 using (lem-auto-CS01-∣-BOX⟨1·2340⟩-at3443 ; lem-auto-CSd01-∣-BOX⟨1·2340⟩-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D079 using (lem-auto-TOFF012-∣-BOX⟨0·3124⟩)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-auto-BOX⟨0·1234⟩-∣-CSd34)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-sym12-at0410213243)
open import Examples.Groups.Clifford+CS.Five.D.D136 using (lem-beta-T-at0412233041)
open import Examples.Groups.Clifford+CS.Five.D.D137 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ401 ; lem-auto-CCZ012-∣-CCZ341 ; lem-auto-CCZ012-∣-CCZ342-at0410213243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ421 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ423)
open import Examples.Groups.Clifford+CS.Five.D.D143 using (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩)
open import Examples.Groups.Clifford+CS.Five.D.D152 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS01-at2332 ; lem-sym23-at042042 ; lem-sym23-at04233042)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D165 using (lem-auto-CS01-∣-BOX⟨0·2341⟩-at3443 ; lem-auto-CSd01-∣-BOX⟨0·2341⟩-at3443 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd01-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D169 using (lem-Cz-beta-at1221 ; lem-T312-beta-at0112233440 ; lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at0213203441)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-CCZ013 ; lem-nat-2-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-2-TOFF201)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-2-BOX⟨3·4012⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨3·4021⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨3·4120⟩ ; lem-nat-1-BOX⟨3·4012⟩ ; lem-nat-1-BOX⟨3·4021⟩ ; lem-nat-2-BOX⟨2·4013⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF413 ; lem-nat-1-TOFF401 ; lem-nat-2-TOFF402 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-CSd02 ; lem-nat-2-BOX⟨1·0432⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-CSd01 ; lem-nat-2-BOX⟨3·0421⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-BOX⟨4·0132⟩ ; lem-nat-1-BOX⟨4·0231⟩ ; lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨1·0234⟩ ; lem-nat-2-BOX⟨4·0132⟩ ; lem-nat-2-BOX⟨4·0321⟩ ; lem-nat-2-SBOX⟨4·0·1·2⟩ ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-0-BOX⟨0·3124⟩ ; lem-nat-0-BOX⟨1·3024⟩ ; lem-nat-1-BOX⟨1·3024⟩ ; lem-nat-1-BOX⟨2·3014⟩ ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨0·2431⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-0-BOX⟨1·0432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-2-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-2-BOX⟨1·0324⟩ ; lem-nat-2-BOX⟨2·0431⟩ ; lem-nat-3-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-3-BOX⟨1·0324⟩ ; lem-nat-3-SBOX⟨0·2·31·4⟩ ; lem-nat-3-SBOX⟨0·2·41·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R030 using (lem-nat-0-BOX⟨4·0132⟩ ; lem-nat-1-BOX⟨4·1023⟩ ; lem-nat-1-BOX⟨4·1032⟩ ; lem-nat-1-BOX⟨4·2013⟩)
open import Examples.Groups.Clifford+CS.Five.D.R031 using (lem-nat-1-BOX⟨4·2301⟩)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-0-BOX⟨3·0421⟩ ; lem-nat-0-BOX⟨3·1420⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-BOX⟨4·1032⟩ ; lem-nat-2-BOX⟨4·0231⟩)
open import Examples.Groups.Clifford+CS.Five.D.R035 using (lem-comm-CCZ023-SBOX⟨0·1·4·3⟩ ; lem-comm-CCZ023-SBOXd⟨0·1·4·3⟩ ; lem-nat-0-BOX⟨2·0431⟩ ; lem-nat-0-BOX⟨2·1430⟩ ; lem-nat-1-BOX⟨1·2430⟩ ; lem-nat-1-BOX⟨2·1430⟩)
open import Examples.Groups.Clifford+CS.Five.D.R038 using (lem-nat-1-BOX⟨4·1302⟩ ; lem-nat-1-BOX⟨4·2031⟩ ; lem-nat-1-SBOX⟨0·1·42·3⟩ ; lem-nat-1-SBOX⟨0·2·41·3⟩ ; lem-nat-2-BOX⟨2·3014⟩ ; lem-nat-2-BOX⟨3·2014⟩ ; lem-nat-2-BOX⟨4·1023⟩ ; lem-nat-2-BOX⟨4·1032⟩ ; lem-nat-2-SBOX⟨4·0·1·3⟩ ; lem-nat-3-BOX⟨3·0421⟩ ; lem-nat-3-BOX⟨3·2014⟩ ; lem-nat-3-BOX⟨4·0321⟩ ; lem-nat-3-BOX⟨4·2013⟩ ; lem-nat-3-SBOX⟨3·0·1·2⟩ ; lem-nat-3-SBOX⟨4·0·1·2⟩)
-- auto CSd01 | BOX(0;2341) @12213443: 7 steps
lem-auto-CSd01-∣-BOX⟨0·2341⟩-at12213443 : Complete 4 → ⟪ (CS02⁻ ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·2341⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 2 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Bx0-2431 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·2341⟩-at3443 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(0;2341) @0112203443: 7 steps
lem-auto-CSd01-∣-BOX⟨0·2341⟩-at0112203443 : Complete 4 → ⟪ (CS12⁻ ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·2341⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12⁻ ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ CS12⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·2341⟩-at12213443 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;0432): 3 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx1-0432 ∷ CS12⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·2341⟩-at0112203443 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(0;2341) @12213443: 7 steps
lem-auto-CS01-∣-BOX⟨0·2341⟩-at12213443 : Complete 4 → ⟪ (CS02 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2341⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Bx0-2431 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2341⟩-at3443 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(0;2341) @0112203443: 7 steps
lem-auto-CS01-∣-BOX⟨0·2341⟩-at0112203443 : Complete 4 → ⟪ (CS12 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2341⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ CS12 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2341⟩-at12213443 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;0432): 3 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ Sb0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Bx1-0432 ∷ CS12 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2341⟩-at0112203443 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;0432) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx1-0432 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩ c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;0432) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-4-2 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at2332 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;0432) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-4-3 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Bx1-0324 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at243243 c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;0432) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at2332 : Complete 4 → ⟪ (Sb0-1-3-2 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx1-0432 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩ c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;0432) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at243243 : Complete 4 → ⟪ (Sb0-1-4-2 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at2332 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;0432) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at2442 : Complete 4 → ⟪ (Sb0-1-4-3 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Bx1-0324 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at243243 c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(1;0234): 27 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨1·0234⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨1·0234⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx1-0234 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx1-2304 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx1-0234 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at2442 c4) ▸
       at 5 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸
       at 4 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 4 1 (Bx1-2340 ∷ []) (lem-sym34-at01122330 c4) ▸
       at 3 3 (Bx1-2340 ∷ CCZ023 ∷ []) (lem-T312-beta-at0112233440 c4) ▸
       at 3 1 (Bx1-2304 ∷ []) (lem-sym34-at0112233440 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx1-2304 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1234 ∷ Bx1-2340 ∷ CCZ023 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b1 = at 3 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 3 1 (Bx1-0234 ∷ []) (lem-sym12-at011220 c4) ▸
       at 2 2 (Bx1-0234 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0432⟩-at2442 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸
       at 2 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 2 1 (Bx1-2340 ∷ []) (lem-sym34-at01122330 c4) ▸
       at 1 3 (Bx1-2340 ∷ CCZ023 ∷ []) (lem-T312-beta-at0112233440 c4) ▸ done

  b2 : Chain (Bx0-1234 ∷ Bx1-2340 ∷ CCZ023 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx1-0234 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ CCZ023 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ [])
  b2 = at 1 1 (Bx1-2304 ∷ []) (lem-sym34-at0112233440 c4) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 1 1 (Bx1-0234 ∷ []) (lem-sym12-at011220 c4) ▸
       at 0 2 (Bx1-0234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩ c4) ▸
       at 5 3 (Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at0213203441 c4) ▸
       at 2 2 (Toff423 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sb0-1-4-3 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-SBOX⟨0·1·4·3⟩ c4) ▸
       at 4 2 (Toff423 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx1-0234 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ CCZ023 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) (Bx1-0234 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 5 2 (Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 6 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd34: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd34 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd34 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS34⁻ ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS34⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd34 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS34⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ423 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ423-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ423-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ423 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF432: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF432 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF432 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (lw0 c4 (Toff423 ∷ []) (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 1 2 (CCZ234 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ423-at2332 c4) ▸
       at 2 2 (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff423 ∷ []) (lw0 c4 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ421 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ421-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ421-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CCZ124 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ421 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF431: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF431 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF431 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff413 ∷ []) (Toff413 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (lw0 c4 (Toff413 ∷ []) (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 1 2 (CCZ134 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ421-at2332 c4) ▸
       at 2 2 (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff413 ∷ []) (lw0 c4 (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (Toff413 ∷ []) tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(1;2340) @12213443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at12213443 : Complete 4 → ⟪ (CS02⁻ ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx2-1430 ∷ []) (Bx2-1430 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 2 2 (Bx1-2430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1430⟩ c4) ▸
       at 1 2 (Bx1-2430 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2340⟩-at3443 c4) ▸
       at 0 2 (Bx2-1430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2430⟩ c4) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(1;2340) @0112203443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0112203443 : Complete 4 → ⟪ (CS12⁻ ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12⁻ ∷ Bx2-0431 ∷ []) (Bx2-0431 ∷ CS12⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-1430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Bx2-1430 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2340⟩-at12213443 c4) ▸
       at 0 2 (Bx2-0431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1430⟩ c4) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0431): 3 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx2-0431 ∷ []) (Bx2-0431 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-0431 ∷ CS12⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0112203443 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(1;2340) @12213443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2340⟩-at12213443 : Complete 4 → ⟪ (CS02 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2340⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx2-1430 ∷ []) (Bx2-1430 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Bx1-2430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1430⟩ c4) ▸
       at 1 2 (Bx1-2430 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2340⟩-at3443 c4) ▸
       at 0 2 (Bx2-1430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2430⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(1;2340) @0112203443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2340⟩-at0112203443 : Complete 4 → ⟪ (CS12 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2340⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12 ∷ Bx2-0431 ∷ []) (Bx2-0431 ∷ CS12 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-1430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Bx2-1430 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2340⟩-at12213443 c4) ▸
       at 0 2 (Bx2-0431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1430⟩ c4) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0431): 3 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx2-0431 ∷ []) (Bx2-0431 ∷ Sb0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Bx2-0431 ∷ CS12 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2340⟩-at0112203443 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- sym12 @04102142: 5 steps
lem-sym12-at04102142 : Complete 4 → ⟪ (Bx4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ []) ⟫ʷ
lem-sym12-at04102142 c4 = run b0
  where
  b0 : Chain (Bx4-0132 ∷ []) (Bx4-1032 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0132⟩ c4) ▸
       at 1 1 (Bx4-1023 ∷ []) (lem-sym12-at0410213243 c4) ▸
       at 0 2 (Bx4-1032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1023⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @041041: 5 steps
lem-sym12-at041041 : Complete 4 → ⟪ (Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-sym12-at041041 c4 = run b0
  where
  b0 : Chain (Bx4-0231 ∷ []) (Bx4-2031 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0231⟩ c4) ▸
       at 1 1 (Bx4-1032 ∷ []) (lem-sym12-at04102142 c4) ▸
       at 0 2 (Bx4-2031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·1032⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @04122041: 5 steps
lem-sym23-at04122041 : Complete 4 → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-sym23-at04122041 c4 = run b0
  where
  b0 : Chain (Bx4-2031 ∷ []) (Bx4-2301 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2031⟩ c4) ▸
       at 1 1 (Bx4-1302 ∷ []) (lem-sym23-at042042 c4) ▸
       at 0 2 (Bx4-2301 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·1302⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0412233041: 5 steps
lem-sym23-at0412233041 : Complete 4 → ⟪ (Bx4-2301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-sym23-at0412233041 c4 = run b0
  where
  b0 : Chain (Bx4-2301 ∷ []) (Bx4-2031 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2301⟩ c4) ▸
       at 1 1 (Bx4-1032 ∷ []) (lem-sym23-at04233042 c4) ▸
       at 0 2 (Bx4-2031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·1032⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @042042: 5 steps
lem-sym12-at042042 : Complete 4 → ⟪ (Bx4-1032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ []) ⟫ʷ
lem-sym12-at042042 c4 = run b0
  where
  b0 : Chain (Bx4-1032 ∷ []) (Bx4-0132 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1032⟩ c4) ▸
       at 1 1 (Bx4-1032 ∷ []) (lem-sym12-at04102142 c4) ▸
       at 0 2 (Bx4-0132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1032⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @04122041: 5 steps
lem-sym12-at04122041 : Complete 4 → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ []) ⟫ʷ
lem-sym12-at04122041 c4 = run b0
  where
  b0 : Chain (Bx4-2031 ∷ []) (Bx4-0231 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2031⟩ c4) ▸
       at 1 1 (Bx4-0132 ∷ []) (lem-sym12-at042042 c4) ▸
       at 0 2 (Bx4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0132⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(4;0231): 31 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0231⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0231⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Bx0-1234 ∷ Bx4-0231 ∷ []) (Toff423 ∷ Bx0-2341 ∷ CCZ123 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ [])
  b0 = at 1 1 (Bx4-2031 ∷ []) (lem-sym12-at041041 c4) ▸
       at 1 1 (Bx4-2301 ∷ []) (lem-sym23-at04122041 c4) ▸
       at 1 1 (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (lem-beta-T-at0412233041 c4) ▸
       at 0 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 2 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 2 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸
       at 1 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸ done

  b1 : Chain (Toff423 ∷ Bx0-2341 ∷ CCZ123 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (Toff423 ∷ CCZ123 ∷ CCZ014 ∷ Toff423 ∷ Toff423 ∷ Bx0-2314 ∷ Toff423 ∷ CCZ014 ∷ [])
  b1 = at 1 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 1 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4) ▸
       at 2 2 (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ401 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 5 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸ done

  b2 : Chain (Toff423 ∷ CCZ123 ∷ CCZ014 ∷ Toff423 ∷ Toff423 ∷ Bx0-2314 ∷ Toff423 ∷ CCZ014 ∷ []) (CCZ123 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ123 ∷ CCZ014 ∷ Bx0-1234 ∷ [])
  b2 = at 5 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸
       at 4 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸
       at 4 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸
       at 4 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 4 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 4 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4) ▸
       at 5 2 (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ401 c4) ▸
       at 0 2 (CCZ123 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CCZ123 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ123 ∷ CCZ014 ∷ Bx0-1234 ∷ []) (Bx4-0231 ∷ Bx0-1234 ∷ [])
  b3 = at 3 2 (CCZ123 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0410213243 c4) ▸
       at 1 2 (CCZ123 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx4-2301 ∷ []) (sym (lem-beta-T-at0412233041 c4)) ▸
       at 0 1 (Bx4-2031 ∷ []) (lem-sym23-at0412233041 c4) ▸
       at 0 1 (Bx4-0231 ∷ []) (lem-sym12-at04122041 c4) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0431) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx3-0421 ∷ []) (Bx3-0421 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx2-0431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (Bx2-0431 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩ c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0431) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-4-2 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx4-0321 ∷ []) (Bx4-0321 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx3-0421 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0321⟩ c4) ▸
       at 1 2 (Bx3-0421 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at2332 c4) ▸
       at 0 2 (Bx4-0321 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0431) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-4-3 ∷ Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx4-0231 ∷ []) (Bx4-0231 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx4-0321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0231⟩ c4) ▸
       at 1 2 (Bx4-0321 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at243243 c4) ▸
       at 0 2 (Bx4-0231 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0321⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3124) @0110: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at0110 : Complete 4 → ⟪ (Toff102 ∷ Bx1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at0110 c4 = run b0
  where
  b0 : Chain (Toff102 ∷ Bx1-3024 ∷ []) (Bx1-3024 ∷ Toff102 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-3124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3024⟩ c4) ▸
       at 1 2 (Bx0-3124 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3124⟩ c4) ▸
       at 0 2 (Bx1-3024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3124⟩ c4) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3124) @021021: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at021021 : Complete 4 → ⟪ (Toff201 ∷ Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at021021 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx2-3014 ∷ []) (Bx2-3014 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-3024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3014⟩ c4) ▸
       at 1 2 (Bx1-3024 ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at0110 c4) ▸
       at 0 2 (Bx2-3014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3024⟩ c4) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3124) @03102132: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at03102132 : Complete 4 → ⟪ (Toff301 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx3-2014 ∷ []) (Bx3-2014 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx2-3014 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·2014⟩ c4) ▸
       at 1 2 (Bx2-3014 ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at021021 c4) ▸
       at 0 2 (Bx3-2014 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·3014⟩ c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3124) @0410213243: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at0410213243 : Complete 4 → ⟪ (Toff401 ∷ Bx4-2013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ Toff401 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ Bx4-2013 ∷ []) (Bx4-2013 ∷ Toff401 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 2 2 (Bx3-2014 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·2013⟩ c4) ▸
       at 1 2 (Bx3-2014 ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at03102132 c4) ▸
       at 0 2 (Bx4-2013 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·2014⟩ c4) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3124) @04103143: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at04103143 : Complete 4 → ⟪ (Toff402 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Toff402 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at04103143 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ Toff402 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx4-2013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·1023⟩ c4) ▸
       at 1 2 (Bx4-2013 ∷ Toff401 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at0410213243 c4) ▸
       at 0 2 (Bx4-1023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2013⟩ c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3124) @0410233142: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at0410233142 : Complete 4 → ⟪ (Toff403 ∷ Bx4-1032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ Toff403 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at0410233142 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Bx4-1032 ∷ []) (Bx4-1032 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx4-1023 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1032⟩ c4) ▸
       at 1 2 (Bx4-1023 ∷ Toff402 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at04103143 c4) ▸
       at 0 2 (Bx4-1032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1023⟩ c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3124) @04233042: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at04233042 : Complete 4 → ⟪ (Toff413 ∷ Bx4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ Toff413 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at04233042 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Bx4-0132 ∷ []) (Bx4-0132 ∷ Toff413 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx4-1032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0132⟩ c4) ▸
       at 1 2 (Bx4-1032 ∷ Toff403 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at0410233142 c4) ▸
       at 0 2 (Bx4-0132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1032⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3124) @0412233041: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at0412233041 : Complete 4 → ⟪ (Toff423 ∷ Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at0412233041 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx4-0231 ∷ []) (Bx4-0231 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0231⟩ c4) ▸
       at 1 2 (Bx4-0132 ∷ Toff413 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at04233042 c4) ▸
       at 0 2 (Bx4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0132⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0431) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at2332 : Complete 4 → ⟪ (Sb0-1-3-2 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx3-0421 ∷ []) (Bx3-0421 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx2-0431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (Bx2-0431 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩ c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0431) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at243243 : Complete 4 → ⟪ (Sb0-1-4-2 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx4-0321 ∷ []) (Bx4-0321 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx3-0421 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0321⟩ c4) ▸
       at 1 2 (Bx3-0421 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at2332 c4) ▸
       at 0 2 (Bx4-0321 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0431) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at2442 : Complete 4 → ⟪ (Sb0-1-4-3 ∷ Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx4-0231 ∷ []) (Bx4-0231 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx4-0321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0231⟩ c4) ▸
       at 1 2 (Bx4-0321 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at243243 c4) ▸
       at 0 2 (Bx4-0231 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0321⟩ c4) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;0231): 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx4-0231 ∷ []) (Bx4-0231 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx4-0231 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at2442 c4) ▸
       at 3 2 (Bx4-0231 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at0412233041 c4) ▸
       at 2 2 (Bx4-0231 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0431⟩-at2442 c4) ▸
       at 1 2 (Bx4-0231 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at0412233041 c4) ▸
       at 0 2 (Bx4-0231 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0231⟩ c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto CCZ012 | BOX(0;2314): 5 steps
lem-auto-CCZ012-∣-BOX⟨0·2314⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨0·2314⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 2 (Bx0-2134 ∷ CCZ012 ∷ []) (lem-Cz-beta-at1221 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF341: 5 steps
lem-auto-CCZ012-∣-TOFF341 : Complete 4 → ⟪ (CCZ012 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF341 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 2 (K3 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ K3 ∷ []) (K3 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ341 c4) ▸
       at 2 2 (K3⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF341 @3443: 7 steps
lem-auto-CCZ012-∣-TOFF341-at3443 : Complete 4 → ⟪ (CCZ012 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF341-at3443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff314 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff413 ∷ []) (Toff314 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff314 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF341 c4) ▸
       at 0 2 (Toff413 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(0;2;31;4): 11 steps
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩ : Complete 4 → ⟪ (CCZ012 ∷ Sb0-2-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-31-4 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Sb0-2-31-4 ∷ []) (Bx0-2314 ∷ Toff413 ∷ Sb0-2-4-1 ∷ Toff413 ∷ CCZ012 ∷ CS24⁻ ∷ [])
  b0 = at 1 1 (Bx0-2314 ∷ Toff413 ∷ Sb0-2-4-1 ∷ Toff413 ∷ Sb⁻0-2-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-2314 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨0·2314⟩ c4) ▸
       at 1 2 (Toff413 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF341-at3443 c4) ▸
       at 3 1 (CS24 ∷ []) (refl) ▸
       at 2 2 (CS24 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CS24 ∷ []) (CS24 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-4-1 ∷ []) (refl) ▸
       at 3 2 (Toff413 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF341-at3443 c4) ▸
       at 5 1 (CS24⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-2314 ∷ Toff413 ∷ Sb0-2-4-1 ∷ Toff413 ∷ CCZ012 ∷ CS24⁻ ∷ []) (Sb0-2-31-4 ∷ CCZ012 ∷ [])
  b1 = at 4 2 (CS24⁻ ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-2-4-1 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-31-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;0;1;3): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb4-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-1-3 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb4-0-1-3 ∷ []) (Sb4-0-1-3 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS01-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb4-0-1-3 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;0;1;3): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb⁻4-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-1-3 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻4-0-1-3 ∷ []) (Sb⁻4-0-1-3 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS01⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd01-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻4-0-1-3 ∷ []) (refl) ▸ done


-- X1-beta @0314203142: 8 steps
lem-X1-beta-at0314203142 : Complete 4 → ⟪ (X4 ∷ Bx3-4012 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx3-4012 ∷ []) ⟫ʷ
lem-X1-beta-at0314203142 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx3-4012 ∷ X4 ∷ []) (CCZ012 ∷ Bx3-4012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 2 2 (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ c4) ▸
       at 3 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 1 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Bx3-4012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4013⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @0314203241: 8 steps
lem-X1-beta-at0314203241 : Complete 4 → ⟪ (X4 ∷ Bx3-4021 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx3-4021 ∷ []) ⟫ʷ
lem-X1-beta-at0314203241 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx3-4021 ∷ X4 ∷ []) (CCZ012 ∷ Bx3-4021 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Bx3-4012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4021⟩ c4) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 1 3 (CCZ012 ∷ Bx3-4012 ∷ []) (lem-X1-beta-at0314203142 c4) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4012⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @0314213240: 8 steps
lem-X1-beta-at0314213240 : Complete 4 → ⟪ (X4 ∷ Bx3-4120 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx3-4120 ∷ []) ⟫ʷ
lem-X1-beta-at0314213240 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx3-4120 ∷ X4 ∷ []) (CCZ012 ∷ Bx3-4120 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 2 2 (Bx3-4021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4120⟩ c4) ▸
       at 3 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 1 3 (CCZ012 ∷ Bx3-4021 ∷ []) (lem-X1-beta-at0314203241 c4) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4021⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;0412) @011220: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at011220 : Complete 4 → ⟪ (CCZ012 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at011220 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-1420 ∷ []) (Bx3-1420 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 1 2 (Bx3-0421 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1221 c4) ▸
       at 0 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;0231) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Bx4-0321 ∷ []) (Bx4-0321 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Bx4-0231 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0321⟩ c4) ▸
       at 1 2 (Bx4-0231 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩ c4) ▸
       at 0 2 (Bx4-0321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0231⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;0231) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Bx3-0421 ∷ []) (Bx3-0421 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Bx4-0321 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (Bx4-0321 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at2332 c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0321⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;0231) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Bx3-1420 ∷ []) (Bx3-1420 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 1 2 (Bx3-0421 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at243243 c4) ▸
       at 0 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(0;2;31;4) @3443: 7 steps
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at3443 : Complete 4 → ⟪ (CCZ012 ∷ Sb0-2-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-41-3 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at3443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb0-2-41-3 ∷ []) (Sb0-2-41-3 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Sb0-2-31-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·41·3⟩ c4) ▸
       at 1 2 (Sb0-2-31-4 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩ c4) ▸
       at 0 2 (Sb0-2-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·31·4⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(0;2;31;4) @12213443: 7 steps
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at12213443 : Complete 4 → ⟪ (CCZ012 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb0-2-41-3 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at3443 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·41·3⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(0;2;31;4) @0112203443: 7 steps
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at0112203443 : Complete 4 → ⟪ (CCZ012 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at12213443 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;0;1;3) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-1-2 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb4-0-1-2 ∷ []) (Sb4-0-1-2 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb4-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·1·2⟩ c4) ▸
       at 1 2 (Sb4-0-1-3 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩ c4) ▸
       at 0 2 (Sb4-0-1-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·1·3⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;0;1;3) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-2 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb3-0-1-2 ∷ []) (Sb3-0-1-2 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb4-0-1-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·0·1·2⟩ c4) ▸
       at 1 2 (Sb4-0-1-2 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at2332 c4) ▸
       at 0 2 (Sb3-0-1-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨4·0·1·2⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

