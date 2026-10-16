{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D163 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-CS20-beta-ci-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D145 using (lem-sym23-at142142 ; lem-sym23-at14233142)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310 ; lem-beta-T-at143143)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-2-TOFF201)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨0·4132⟩ ; lem-nat-1-BOX⟨1·4032⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF413 ; lem-nat-1-TOFF401 ; lem-nat-2-TOFF402 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-BOX⟨1·4032⟩ ; lem-nat-1-BOX⟨2·4031⟩ ; lem-nat-2-CSd12 ; lem-nat-2-CSd13 ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-CSd01)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-1-SBOX⟨1·0·2·3⟩ ; lem-nat-1-SBOX⟨2·0·1·3⟩ ; lem-nat-1-SBOXd⟨1·0·2·3⟩ ; lem-nat-1-SBOXd⟨2·0·1·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-1-BOX⟨2·4301⟩ ; lem-nat-3-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R027 using (lem-nat-3-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-2-BOX⟨0·4312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R036 using (lem-nat-0-BOX⟨0·4312⟩ ; lem-nat-0-BOX⟨1·4302⟩ ; lem-nat-0-SBOX⟨2·0·1·3⟩ ; lem-nat-0-SBOX⟨2·1·0·3⟩ ; lem-nat-1-BOX⟨1·4302⟩ ; lem-nat-2-SBOX⟨2·1·0·4⟩ ; lem-nat-2-SBOX⟨3·1·0·4⟩ ; lem-nat-2-SBOXd⟨2·1·0·4⟩ ; lem-nat-3-SBOX⟨2·1·0·3⟩ ; lem-nat-3-SBOX⟨2·1·0·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R037 using (lem-nat-0-SBOXd⟨2·0·1·3⟩ ; lem-nat-0-SBOXd⟨2·1·0·3⟩ ; lem-nat-2-SBOXd⟨3·1·0·4⟩ ; lem-nat-3-SBOXd⟨2·1·0·3⟩ ; lem-nat-3-SBOXd⟨2·1·0·4⟩)
-- auto SBOX(0;1;23;4) | SBOX(3;1;0;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb3-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-0-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb3-1-0-4 ∷ []) (Sb3-1-0-4 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb3-1-0-4 ∷ []) (refl) ▸ done


-- auto TOFF012 | CSd34: 1 steps
lem-auto-TOFF012-∣-CSd34 : Complete 4 → ⟪ (Toff012 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CSd34 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff012 ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸ done


-- auto BOX(0;1234) | CSd10: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd10 : Complete 4 → ⟪ (Bx0-1234 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd10 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (CS01⁻ ∷ Bx0-2134 ∷ []) (sym (lem-CS20-beta-ci-at1221 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl) ▸ done


-- auto TOFF012 | CSd34 @0110: 7 steps
lem-auto-TOFF012-∣-CSd34-at0110 : Complete 4 → ⟪ (Toff102 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CSd34-at0110 c4 = run b0
  where
  b0 : Chain (Toff102 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff102 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 1 2 (CS34⁻ ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CSd34 c4) ▸
       at 0 2 (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CSd34 @021021: 7 steps
lem-auto-TOFF012-∣-CSd34-at021021 : Complete 4 → ⟪ (Toff201 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CSd34-at021021 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff201 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-CSd34-at0110 c4) ▸
       at 0 2 (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CSd34 @03102132: 7 steps
lem-auto-TOFF012-∣-CSd34-at03102132 : Complete 4 → ⟪ (Toff301 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CSd34-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff301 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34⁻ ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-CSd34-at021021 c4) ▸
       at 0 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CSd34 @0410213243: 7 steps
lem-auto-TOFF012-∣-CSd34-at0410213243 : Complete 4 → ⟪ (Toff401 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Toff401 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CSd34-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Toff401 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 2 2 (CS24⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd23 c4) ▸
       at 1 2 (CS24⁻ ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-CSd34-at03102132 c4) ▸
       at 0 2 (CS23⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd24 c4) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CSd34 @04103143: 7 steps
lem-auto-TOFF012-∣-CSd34-at04103143 : Complete 4 → ⟪ (Toff402 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Toff402 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CSd34-at04103143 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff402 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ Toff401 ∷ []) (lem-auto-TOFF012-∣-CSd34-at0410213243 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CSd34 @0410233142: 7 steps
lem-auto-TOFF012-∣-CSd34-at0410233142 : Complete 4 → ⟪ (Toff403 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Toff403 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CSd34-at0410233142 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff403 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 1 2 (CS13⁻ ∷ Toff402 ∷ []) (lem-auto-TOFF012-∣-CSd34-at04103143 c4) ▸
       at 0 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CSd34 @04233042: 7 steps
lem-auto-TOFF012-∣-CSd34-at04233042 : Complete 4 → ⟪ (Toff413 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff413 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CSd34-at04233042 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff413 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12⁻ ∷ Toff403 ∷ []) (lem-auto-TOFF012-∣-CSd34-at0410233142 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CSd34 @0412233041: 7 steps
lem-auto-TOFF012-∣-CSd34-at0412233041 : Complete 4 → ⟪ (Toff423 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CSd34-at0412233041 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Toff423 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 1 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-auto-TOFF012-∣-CSd34-at04233042 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CSd34 @0412233140: 7 steps
lem-auto-TOFF012-∣-CSd34-at0412233140 : Complete 4 → ⟪ (Toff423 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CSd34-at0412233140 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Toff423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CSd34-at0412233041 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd10: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd10 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd10 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS01⁻ ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS01⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS01⁻ ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS01⁻ ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CSd34-at0412233140 c4) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS01⁻ ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS01⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS01⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS01⁻ ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CSd34-at0412233140 c4) ▸
       at 0 2 (CS01⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd10 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd10 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd10-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd10-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 1 2 (CS01⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd10 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(3;1;0;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb⁻3-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-0-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻3-1-0-4 ∷ []) (Sb⁻3-1-0-4 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS01⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd10-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻3-1-0-4 ∷ []) (refl) ▸ done


-- sym23 @01142042: 5 steps
lem-sym23-at01142042 : Complete 4 → ⟪ (Bx1-4032 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4302 ∷ []) ⟫ʷ
lem-sym23-at01142042 c4 = run b0
  where
  b0 : Chain (Bx1-4032 ∷ []) (Bx1-4302 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4032⟩ c4) ▸
       at 1 1 (Bx0-4312 ∷ []) (lem-sym23-at142142 c4) ▸
       at 0 2 (Bx1-4302 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4312⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @14233142: 8 steps
lem-beta-T-at14233142 : Complete 4 → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-beta-T-at14233142 c4 = run b0
  where
  b0 : Chain (Bx0-4312 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4312⟩ c4) ▸
       at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at143143 c4) ▸
       at 0 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 3 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0114233042: 8 steps
lem-beta-T-at0114233042 : Complete 4 → ⟪ (Bx1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-beta-T-at0114233042 c4 = run b0
  where
  b0 : Chain (Bx1-4302 ∷ []) (Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4312 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4302⟩ c4) ▸
       at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-beta-T-at14233142 c4) ▸
       at 0 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 3 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ310 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (CCZ013 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310 c4) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ310 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (CCZ012 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at2332 c4) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ310 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at243243 c4) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ310 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at0110243243 c4) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0114233042: 5 steps
lem-sym23-at0114233042 : Complete 4 → ⟪ (Bx1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4032 ∷ []) ⟫ʷ
lem-sym23-at0114233042 c4 = run b0
  where
  b0 : Chain (Bx1-4302 ∷ []) (Bx1-4032 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4312 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4302⟩ c4) ▸
       at 1 1 (Bx0-4132 ∷ []) (lem-sym23-at14233142 c4) ▸
       at 0 2 (Bx1-4032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4132⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @02142041: 5 steps
lem-sym23-at02142041 : Complete 4 → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-sym23-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-4301 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-4032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4031⟩ c4) ▸
       at 1 1 (Bx1-4302 ∷ []) (lem-sym23-at01142042 c4) ▸
       at 0 2 (Bx2-4301 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4302⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0214233041: 8 steps
lem-beta-T-at0214233041 : Complete 4 → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-beta-T-at0214233041 c4 = run b0
  where
  b0 : Chain (Bx2-4301 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-4302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4301⟩ c4) ▸
       at 1 1 (Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ []) (lem-beta-T-at0114233042 c4) ▸
       at 0 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0214233041: 5 steps
lem-sym23-at0214233041 : Complete 4 → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-sym23-at0214233041 c4 = run b0
  where
  b0 : Chain (Bx2-4301 ∷ []) (Bx2-4031 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-4302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4301⟩ c4) ▸
       at 1 1 (Bx1-4032 ∷ []) (lem-sym23-at0114233042 c4) ▸
       at 0 2 (Bx2-4031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4032⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | Kd0 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ K0⁻ ∷ []) (K0⁻ ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 1 2 (K0⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4) ▸
       at 0 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | Kd0 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ K1⁻ ∷ []) (K1⁻ ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (K0⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1⁻ ∷ []) (K0⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0⁻ ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at243243 c4) ▸
       at 0 2 (K1⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K0⁻ ∷ []) (K1⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | Kd0 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ K2⁻ ∷ []) (K2⁻ ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (K1⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2⁻ ∷ []) (K1⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K1⁻ ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at0110243243 c4) ▸
       at 0 2 (K2⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1⁻ ∷ []) (K2⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(3;1;0;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb2-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb2-1-0-4 ∷ []) (Sb2-1-0-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb3-1-0-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·0·4⟩ c4) ▸
       at 1 2 (Sb3-1-0-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩ c4) ▸
       at 0 2 (Sb2-1-0-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·0·4⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(3;1;0;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb2-1-0-3 ∷ []) (Sb2-1-0-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb2-1-0-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·1·0·3⟩ c4) ▸
       at 1 2 (Sb2-1-0-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩-at2332 c4) ▸
       at 0 2 (Sb2-1-0-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·1·0·4⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(3;1;0;4) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ Sb2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sb2-0-1-3 ∷ []) (Sb2-0-1-3 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Sb2-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·1·3⟩ c4) ▸
       at 1 2 (Sb2-1-0-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩-at243243 c4) ▸
       at 0 2 (Sb2-0-1-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·0·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(3;1;0;4) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-3 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (Sb2-0-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb2-0-1-3 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb1-0-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·1·3⟩ c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(3;1;0;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb⁻2-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb⁻2-1-0-4 ∷ []) (Sb⁻2-1-0-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb⁻3-1-0-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·1·0·4⟩ c4) ▸
       at 1 2 (Sb⁻3-1-0-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩ c4) ▸
       at 0 2 (Sb⁻2-1-0-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·1·0·4⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(3;1;0;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb⁻2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb⁻2-1-0-3 ∷ []) (Sb⁻2-1-0-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb⁻2-1-0-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·1·0·3⟩ c4) ▸
       at 1 2 (Sb⁻2-1-0-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩-at2332 c4) ▸
       at 0 2 (Sb⁻2-1-0-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·1·0·4⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(3;1;0;4) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ Sb⁻2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻2-0-1-3 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Sb⁻2-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·1·3⟩ c4) ▸
       at 1 2 (Sb⁻2-1-0-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩-at243243 c4) ▸
       at 0 2 (Sb⁻2-0-1-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·0·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(3;1;0;4) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (Sb⁻2-0-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb⁻2-0-1-3 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb⁻1-0-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·1·3⟩ c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

