{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D202 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at13243142 ; lem-sym12 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at1221 ; lem-sym23-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-Cz-beta-at243243 ; lem-sym23-at122331 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ032)
open import Examples.Groups.Clifford+CS.Five.D.D142 using (lem-T-beta-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D143 using (lem-sym23-at0312203441 ; lem-sym23-at0312243041)
open import Examples.Groups.Clifford+CS.Five.D.D152 using (lem-auto-BOX⟨0·1234⟩-∣-CSd21)
open import Examples.Groups.Clifford+CS.Five.D.D153 using (lem-T312-beta-at133441)
open import Examples.Groups.Clifford+CS.Five.D.D167 using (lem-beta-T-at133441)
open import Examples.Groups.Clifford+CS.Five.D.D191 using (lem-c124-beta-at0312203441)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨0·2314⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CSd12 ; lem-nat-2-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-0-SBOX⟨2·1·40·3⟩ ; lem-nat-1-SBOX⟨3·1·40·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R027 using (lem-nat-0-SBOX⟨2·0·41·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-1-BOX⟨0·3421⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-2-BOX⟨0·2431⟩ ; lem-nat-2-BOX⟨0·3241⟩ ; lem-nat-2-SBOX⟨0·3·1·4⟩ ; lem-nat-2-SBOXd⟨0·3·1·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R037 using (lem-nat-2-BOX⟨0·3421⟩ ; lem-nat-3-BOX⟨0·2341⟩ ; lem-nat-3-BOX⟨0·2431⟩)
open import Examples.Groups.Clifford+CS.Five.D.R041 using (lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 ; lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 ; lem-nat-1-SBOX⟨3·2·40·1⟩ ; lem-nat-2-BOX⟨0·2341⟩ ; lem-nat-2-SBOX⟨0·2·1·4⟩ ; lem-nat-2-SBOX⟨2·1·40·3⟩ ; lem-nat-2-SBOX⟨3·1·40·2⟩ ; lem-nat-2-SBOXd⟨0·2·1·4⟩ ; lem-nat-3-SBOX⟨0·2·1·3⟩ ; lem-nat-3-SBOX⟨0·2·1·4⟩ ; lem-nat-3-SBOXd⟨0·2·1·3⟩ ; lem-nat-3-SBOXd⟨0·2·1·4⟩)
-- auto SBOX(0;1;23;4) | CCZ032 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ032-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ032-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ032 c4) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF023: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF023 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF023 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff023 ∷ []) (Toff023 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (lw4 c4 (Toff023 ∷ []) (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4) ▸
       at 1 2 (CCZ023 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ032-at2332 c4) ▸
       at 2 2 (K0⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff023 ∷ []) (lw4 c4 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸ done


-- beta-T @13243241: 8 steps
lem-beta-T-at13243241 : Complete 4 → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-beta-T-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ c4) ▸
       at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-beta-T-at13243142 c4) ▸
       at 0 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 3 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;3421): 10 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx0-3421 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-beta-T-at13243241 c4) ▸
       at 0 2 (Toff034 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 c4) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ012 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 2 (Toff034 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 c4) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ012 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CS12⁻ ∷ []) (Bx0-3421 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-3421 ∷ []) (sym (lem-beta-T-at13243241 c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;3421): 10 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx0-3421 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CS12 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-beta-T-at13243241 c4) ▸
       at 0 2 (Toff034 ∷ Sb0-1-2-3 ∷ []) (lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 c4) ▸
       at 1 1 (CS12 ∷ []) (refl) ▸
       at 1 2 (CCZ012 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 2 2 (Toff034 ∷ Sb0-1-2-3 ∷ []) (lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 c4) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 3 2 (CCZ012 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CS12 ∷ []) (Bx0-3421 ∷ Sb0-1-2-3 ∷ [])
  b1 = at 4 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-3421 ∷ []) (sym (lem-beta-T-at13243241 c4)) ▸ done


-- T-beta @122331: 7 steps
lem-T-beta-at122331 : Complete 4 → ⟪ (Toff023 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ Toff023 ∷ []) ⟫ʷ
lem-T-beta-at122331 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ Toff023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ Toff013 ∷ []) (lem-T-beta-at2332 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF032: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF032 : Complete 4 → ⟪ (Bx0-1234 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF032 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Toff023 ∷ []) (Toff023 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff023 ∷ []) (lw4 c4 (Toff023 ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (Toff023 ∷ Bx0-2314 ∷ []) (sym (lem-T-beta-at122331 c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (Toff023 ∷ []) (lw4 c4 (Toff023 ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ041 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ041 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CCZ014 ∷ Bx0-1423 ∷ []) (sym (lem-Cz-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(0;3241): 6 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·3241⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·3241⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at133441 c4) ▸
       at 0 2 (Toff023 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF032 c4) ▸
       at 1 2 (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ041 c4) ▸
       at 2 2 (Toff023 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF032 c4) ▸
       at 3 2 (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ041 c4) ▸
       at 0 4 (Bx0-3241 ∷ []) (sym (lem-beta-T-at133441 c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;3421) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx0-3421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Bx0-3421 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3421⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;3421) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-4-2 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx0-2431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2341⟩ c4) ▸
       at 1 2 (Bx0-2431 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;3421) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-4-3 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx0-2341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3241⟩ c4) ▸
       at 1 2 (Bx0-2341 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 c4) ▸
       at 0 2 (Bx0-3241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2341⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;3421) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 : Complete 4 → ⟪ (Sb0-1-3-2 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx0-3421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Bx0-3421 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3421⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;3421) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 : Complete 4 → ⟪ (Sb0-1-4-2 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx0-2431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2341⟩ c4) ▸
       at 1 2 (Bx0-2431 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;3421) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 : Complete 4 → ⟪ (Sb0-1-4-3 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx0-2341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3241⟩ c4) ▸
       at 1 2 (Bx0-2341 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 c4) ▸
       at 0 2 (Bx0-3241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2341⟩ c4) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;3241): 22 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩ c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx0-3241 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Bx0-3241 ∷ Toff423 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx0-3241 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 c4) ▸
       at 5 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff423 ∷ []) (lw0 c4 (Toff423 ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Toff423 ∷ []) (lw0 c4 (Toff423 ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Bx0-3241 ∷ CCZ123 ∷ []) (lem-T312-beta-at133441 c4) ▸
       at 2 2 (Bx0-3241 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Bx0-3241 ∷ Toff423 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-3241 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ [])
  b1 = at 1 1 (Toff423 ∷ []) (lw0 c4 (Toff423 ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff423 ∷ []) (lw0 c4 (Toff423 ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-3241 ∷ CCZ123 ∷ []) (lem-T312-beta-at133441 c4) ▸
       at 0 2 (Bx0-3241 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·3241⟩ c4) ▸
       at 7 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 3 (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-3241 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ []) (Bx0-3241 ∷ Sb0-1-23-4 ∷ [])
  b2 = at 6 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 5 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 6 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto CCZ012 | BOX(3;2401): 5 steps
lem-auto-CCZ012-∣-BOX⟨3·2401⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·2401⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx3-2041 ∷ []) (lem-sym23-at0312243041 c4) ▸
       at 0 2 (Bx3-2041 ∷ CCZ012 ∷ []) (lem-c124-beta-at0312203441 c4) ▸
       at 0 1 (Bx3-2401 ∷ []) (lem-sym23-at0312203441 c4) ▸
       at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;2;40;1): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩ : Complete 4 → ⟪ (CCZ012 ∷ Sb3-2-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-2-40-1 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Sb3-2-40-1 ∷ []) (Bx3-2401 ∷ Toff104 ∷ Sb3-2-1-0 ∷ Toff104 ∷ Sb⁻3-2-1-0 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-2401 ∷ Toff104 ∷ Sb3-2-1-0 ∷ Toff104 ∷ Sb⁻3-2-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-2401 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·2401⟩ c4) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 1 4 (Toff104 ∷ CS12 ∷ Toff104 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ Toff104 ∷ CS12 ∷ Toff104 ∷ []) (Toff104 ∷ CS12 ∷ Toff104 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb3-2-1-0 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻3-2-1-0 ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-2401 ∷ Toff104 ∷ Sb3-2-1-0 ∷ Toff104 ∷ Sb⁻3-2-1-0 ∷ CCZ012 ∷ []) (Sb3-2-40-1 ∷ CCZ012 ∷ [])
  b1 = at 0 5 (Sb3-2-40-1 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;3;1;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb0-3-1-4 ∷ []) (Sb0-3-1-4 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb0-3-1-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd21: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS12⁻ ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS12⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS12⁻ ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS12⁻ ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS12⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS12⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS12⁻ ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS12⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd21 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 1 2 (CS12⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;3;1;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb⁻0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻0-3-1-4 ∷ []) (Sb⁻0-3-1-4 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻0-3-1-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;3241) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Bx0-3241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2341⟩ c4) ▸
       at 1 2 (Bx0-3241 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩ c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3241⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;3241) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Bx0-2341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Bx0-2341 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at2332 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2341⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;2;40;1) @1221: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at1221 : Complete 4 → ⟪ (CCZ012 ∷ Sb3-1-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-40-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb3-1-40-2 ∷ []) (Sb3-1-40-2 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-2-40-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·1·40·2⟩ c4) ▸
       at 1 2 (Sb3-2-40-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩ c4) ▸
       at 0 2 (Sb3-1-40-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·2·40·1⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;2;40;1) @132132: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at132132 : Complete 4 → ⟪ (CCZ013 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb2-1-40-3 ∷ []) (Sb2-1-40-3 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Sb3-1-40-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·40·3⟩ c4) ▸
       at 1 2 (Sb3-1-40-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at1221 c4) ▸
       at 0 2 (Sb2-1-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·40·2⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;2;40;1) @01132032: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at01132032 : Complete 4 → ⟪ (CCZ013 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at01132032 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb2-1-40-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb2-1-40-3 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at132132 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;2;40;1) @02132031: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132031 : Complete 4 → ⟪ (CCZ023 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132031 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at01132032 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;2;40;1) @02132130: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132130 : Complete 4 → ⟪ (CCZ123 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132130 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132031 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;3;1;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb0-2-1-4 ∷ []) (Sb0-2-1-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb0-3-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·2·1·4⟩ c4) ▸
       at 1 2 (Sb0-3-1-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩ c4) ▸
       at 0 2 (Sb0-2-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·1·4⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;3;1;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb0-2-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·1·3⟩ c4) ▸
       at 1 2 (Sb0-2-1-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at2332 c4) ▸
       at 0 2 (Sb0-2-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·1·4⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;3;1;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb⁻0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-2-1-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb⁻0-3-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·2·1·4⟩ c4) ▸
       at 1 2 (Sb⁻0-3-1-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩ c4) ▸
       at 0 2 (Sb⁻0-2-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·3·1·4⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;3;1;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb⁻0-2-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·1·3⟩ c4) ▸
       at 1 2 (Sb⁻0-2-1-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at2332 c4) ▸
       at 0 2 (Sb⁻0-2-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·1·4⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

