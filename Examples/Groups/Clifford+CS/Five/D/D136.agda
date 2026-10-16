{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D136 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23-at132132 ; lem-sym34-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ234 ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym34-at12213443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-beta-T-at03102132 ; lem-sym12-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CX23-beta-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-CX23-beta-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42)
open import Examples.Groups.Clifford+CS.Five.D.D079 using (lem-CSd12-beta-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-sym23-at1331)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-CX23-beta-at04203243 ; lem-F0-at0112203443 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243 ; lem-auto-BOX⟨0·1234⟩-∣-CSd12 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS12-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS32-at2332 ; lem-sym12-at0410213243 ; lem-sym12-at04233240 ; lem-sym23-at04203243 ; lem-sym34-at0413203142 ; lem-sym34-at0413203241)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ024 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ124 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-TOFF401 ; lem-nat-2-TOFF402 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨0·2314⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CSd12 ; lem-nat-2-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-CSd02 ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-CSd01)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-BOX⟨4·0312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-3-BOX⟨3·0124⟩ ; lem-nat-3-BOX⟨4·0123⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-1-BOX⟨0·3214⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF304 ; lem-nat-0-BOX⟨4·0321⟩ ; lem-nat-0-BOX⟨4·1320⟩ ; lem-nat-1-BOX⟨0·3124⟩ ; lem-nat-1-BOX⟨4·0213⟩ ; lem-nat-1-BOX⟨4·0321⟩ ; lem-nat-2-BOX⟨4·0312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R030 using (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF403 ; lem-nat-0-BOX⟨4·1023⟩ ; lem-nat-0-BOX⟨4·1302⟩ ; lem-nat-0-BOX⟨4·3012⟩ ; lem-nat-0-BOX⟨4·3021⟩ ; lem-nat-0-BOX⟨4·3102⟩ ; lem-nat-0-BOX⟨4·3120⟩ ; lem-nat-1-BOX⟨4·0123⟩ ; lem-nat-1-BOX⟨4·1023⟩ ; lem-nat-1-BOX⟨4·1203⟩ ; lem-nat-1-BOX⟨4·2013⟩ ; lem-nat-1-BOX⟨4·3021⟩ ; lem-nat-1-CX01 ; lem-nat-2-BOX⟨4·0213⟩ ; lem-nat-2-BOX⟨4·2013⟩ ; lem-nat-2-BOX⟨4·2103⟩ ; lem-nat-2-BOX⟨4·3012⟩)
open import Examples.Groups.Clifford+CS.Five.D.R031 using (lem-nat-0-BOX⟨4·2310⟩ ; lem-nat-1-BOX⟨4·2301⟩)
-- sym34 @0413213240: 5 steps
lem-sym34-at0413213240 : Complete 4 → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-sym34-at0413213240 c4 = run b0
  where
  b0 : Chain (Bx4-3120 ∷ []) (Bx4-3102 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-3021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·3120⟩ c4) ▸
       at 1 1 (Bx4-3012 ∷ []) (lem-sym34-at0413203241 c4) ▸
       at 0 2 (Bx4-3102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·3012⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0412203143: 5 steps
lem-sym23-at0412203143 : Complete 4 → ⟪ (Bx4-2013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2103 ∷ []) ⟫ʷ
lem-sym23-at0412203143 c4 = run b0
  where
  b0 : Chain (Bx4-2013 ∷ []) (Bx4-2103 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2013⟩ c4) ▸
       at 1 1 (Bx4-1203 ∷ []) (lem-sym23-at04203243 c4) ▸
       at 0 2 (Bx4-2103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·1203⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0413203142: 5 steps
lem-sym23-at0413203142 : Complete 4 → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-sym23-at0413203142 c4 = run b0
  where
  b0 : Chain (Bx4-3012 ∷ []) (Bx4-3102 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-2013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·3012⟩ c4) ▸
       at 1 1 (Bx4-2103 ∷ []) (lem-sym23-at0412203143 c4) ▸
       at 0 2 (Bx4-3102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·2103⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0413213042: 5 steps
lem-sym23-at0413213042 : Complete 4 → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-sym23-at0413213042 c4 = run b0
  where
  b0 : Chain (Bx4-3102 ∷ []) (Bx4-3012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-3012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·3102⟩ c4) ▸
       at 1 1 (Bx4-3102 ∷ []) (lem-sym23-at0413203142 c4) ▸
       at 0 2 (Bx4-3012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·3102⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta @0412203143: 8 steps
lem-CX23-beta-at0412203143 : Complete 4 → ⟪ (CX01 ∷ Bx4-2013 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CX23-beta-at0412203143 c4 = run b0
  where
  b0 : Chain (CX01 ∷ Bx4-2013 ∷ CX01 ∷ []) (Bx4-2013 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX02 ∷ Sw12 ∷ []) (lem-nat-1-CX01 c4) ▸
       at 2 2 (Bx4-1023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2013⟩ c4) ▸
       at 3 2 (CX02 ∷ Sw12 ∷ []) (lem-nat-1-CX01 c4) ▸
       at 1 3 (Bx4-1023 ∷ CCZ013 ∷ []) (lem-CX23-beta-at04203243 c4) ▸
       at 0 2 (Bx4-2013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·1023⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta @0413203142: 8 steps
lem-CX23-beta-at0413203142 : Complete 4 → ⟪ (CX01 ∷ Bx4-3012 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CX23-beta-at0413203142 c4 = run b0
  where
  b0 : Chain (CX01 ∷ Bx4-3012 ∷ CX01 ∷ []) (Bx4-3012 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 2 2 (Bx4-2013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·3012⟩ c4) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 1 3 (Bx4-2013 ∷ CCZ023 ∷ []) (lem-CX23-beta-at0412203143 c4) ▸
       at 0 2 (Bx4-3012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·2013⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0413213042: 5 steps
lem-sym34-at0413213042 : Complete 4 → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-sym34-at0413213042 c4 = run b0
  where
  b0 : Chain (Bx4-3102 ∷ []) (Bx4-3120 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-3012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·3102⟩ c4) ▸
       at 1 1 (Bx4-3021 ∷ []) (lem-sym34-at0413203142 c4) ▸
       at 0 2 (Bx4-3120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·3021⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @04203243: 5 steps
lem-sym12-at04203243 : Complete 4 → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-sym12-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1023⟩ c4) ▸
       at 1 1 (Bx4-1023 ∷ []) (lem-sym12-at0410213243 c4) ▸
       at 0 2 (Bx4-0123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1023⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0412203143: 5 steps
lem-sym12-at0412203143 : Complete 4 → ⟪ (Bx4-2013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ []) ⟫ʷ
lem-sym12-at0412203143 c4 = run b0
  where
  b0 : Chain (Bx4-2013 ∷ []) (Bx4-0213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2013⟩ c4) ▸
       at 1 1 (Bx4-0123 ∷ []) (lem-sym12-at04203243 c4) ▸
       at 0 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0413203142: 5 steps
lem-sym12-at0413203142 : Complete 4 → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ []) ⟫ʷ
lem-sym12-at0413203142 c4 = run b0
  where
  b0 : Chain (Bx4-3012 ∷ []) (Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-2013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·3012⟩ c4) ▸
       at 1 1 (Bx4-0213 ∷ []) (lem-sym12-at0412203143 c4) ▸
       at 0 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0413203241: 5 steps
lem-sym12-at0413203241 : Complete 4 → ⟪ (Bx4-3021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ []) ⟫ʷ
lem-sym12-at0413203241 c4 = run b0
  where
  b0 : Chain (Bx4-3021 ∷ []) (Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-3012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·3021⟩ c4) ▸
       at 1 1 (Bx4-0312 ∷ []) (lem-sym12-at0413203142 c4) ▸
       at 0 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0413213240: 5 steps
lem-sym12-at0413213240 : Complete 4 → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-sym12-at0413213240 c4 = run b0
  where
  b0 : Chain (Bx4-3120 ∷ []) (Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-3021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·3120⟩ c4) ▸
       at 1 1 (Bx4-0321 ∷ []) (lem-sym12-at0413203241 c4) ▸
       at 0 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0110 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at021021 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (CCZ124 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03102132 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @04103143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at04103143 : Complete 4 → ⟪ (Bx4-0213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx4-0213 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at04103143 c4 = run b0
  where
  b0 : Chain (Bx4-0213 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx4-0213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0410213243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @0410233142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0410233142 : Complete 4 → ⟪ (Bx4-0312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx4-0312 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Bx4-0213 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at04103143 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @0410233241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0410233241 : Complete 4 → ⟪ (Bx4-0321 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx4-0321 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Bx4-0312 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0410233142 c4) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @04233240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at04233240 : Complete 4 → ⟪ (Bx4-1320 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx4-1320 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Bx4-0321 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0410233241 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd12 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd12 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd12 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 1 2 (CS02⁻ ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd12-at0110 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd12 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 1 2 (CS01⁻ ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd12-at021021 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd12 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ c4) ▸
       at 2 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 1 2 (CS01⁻ ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd12-at03102132 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd12 @04103143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at04103143 : Complete 4 → ⟪ (Bx4-0213 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx4-0213 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at04103143 c4 = run b0
  where
  b0 : Chain (Bx4-0213 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx4-0213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ c4) ▸
       at 2 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 1 2 (CS01⁻ ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd12-at0410213243 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 1 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd12 @0410233142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at0410233142 : Complete 4 → ⟪ (Bx4-0312 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx4-0312 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 1 2 (CS02⁻ ∷ Bx4-0213 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd12-at04103143 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 1 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd12 @0410233241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at0410233241 : Complete 4 → ⟪ (Bx4-0321 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx4-0321 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Bx4-0312 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd12-at0410233142 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd12 @04233240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at04233240 : Complete 4 → ⟪ (Bx4-1320 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx4-1320 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13⁻ ∷ []) (CS03⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Bx4-0321 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd12-at0410233241 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03⁻ ∷ []) (CS13⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ301: 38 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ301 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ301 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ013 ∷ []) (CS13 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sb⁻4-1-0-2 ∷ CS03 ∷ [])
  b0 = at 1 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS12-at2332 c4) ▸
       at 1 1 (Sb4-1-32-0 ∷ []) (lem-F0-at0112203443 c4) ▸
       at 1 1 (Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 5 4 (CX01 ∷ CS13⁻ ∷ CX01 ∷ CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ []) (CX01 ∷ CS13⁻ ∷ CX01 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻4-1-0-2 ∷ []) (refl) ▸ done

  b1 : Chain (CS13 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sb⁻4-1-0-2 ∷ CS03 ∷ []) (CS13 ∷ CX01 ∷ Bx4-3012 ∷ CCZ023 ∷ CS13⁻ ∷ CX01 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS03 ∷ [])
  b1 = at 3 1 (CS01 ∷ []) (refl) ▸
       at 2 6 (CX01 ∷ CS13⁻ ∷ CX01 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS01 ∷ Toff023 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ []) (CX01 ∷ CS13⁻ ∷ CX01 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb4-1-0-2 ∷ []) (refl) ▸
       at 1 0 (CX01 ∷ CX01 ∷ []) (lw4 c4 [] (CX01 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx4-3120 ∷ []) (lem-sym12-at04233240 c4) ▸
       at 3 1 (Bx4-3102 ∷ []) (lem-sym34-at0413213240 c4) ▸
       at 3 1 (Bx4-3012 ∷ []) (lem-sym23-at0413213042 c4) ▸
       at 2 3 (Bx4-3012 ∷ CCZ023 ∷ []) (lem-CX23-beta-at0413203142 c4) ▸ done

  b2 : Chain (CS13 ∷ CX01 ∷ Bx4-3012 ∷ CCZ023 ∷ CS13⁻ ∷ CX01 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS03 ∷ []) (CS13 ∷ CX01 ∷ CCZ023 ∷ CS13⁻ ∷ CX01 ∷ CX01 ∷ Bx4-3102 ∷ CX01 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS03 ∷ [])
  b2 = at 2 1 (Bx4-3102 ∷ []) (lem-sym23-at0413203142 c4) ▸
       at 2 1 (Bx4-3120 ∷ []) (lem-sym34-at0413213042 c4) ▸
       at 2 1 (Bx4-1320 ∷ []) (lem-sym12-at0413213240 c4) ▸
       at 2 2 (CCZ023 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at04233240 c4) ▸
       at 3 2 (CS13⁻ ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd12-at04233240 c4) ▸
       at 4 0 (CX01 ∷ CX01 ∷ []) (lw4 c4 [] (CX01 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx4-3120 ∷ []) (lem-sym12-at04233240 c4) ▸
       at 6 1 (Bx4-3102 ∷ []) (lem-sym34-at0413213240 c4) ▸ done

  b3 : Chain (CS13 ∷ CX01 ∷ CCZ023 ∷ CS13⁻ ∷ CX01 ∷ CX01 ∷ Bx4-3102 ∷ CX01 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS03 ∷ []) (CS13 ∷ CCZ023 ∷ CCZ023 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS03 ∷ [])
  b3 = at 6 1 (Bx4-3012 ∷ []) (lem-sym23-at0413213042 c4) ▸
       at 5 3 (Bx4-3012 ∷ CCZ023 ∷ []) (lem-CX23-beta-at0413203142 c4) ▸
       at 5 1 (Bx4-3102 ∷ []) (lem-sym23-at0413203142 c4) ▸
       at 5 1 (Bx4-3120 ∷ []) (lem-sym34-at0413213042 c4) ▸
       at 5 1 (Bx4-1320 ∷ []) (lem-sym12-at0413213240 c4) ▸
       at 5 2 (CCZ023 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at04233240 c4) ▸
       at 1 2 (CCZ023 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ023 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CS13⁻ ∷ CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (CS13 ∷ CCZ023 ∷ CCZ023 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS03 ∷ []) (CCZ013 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 1 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb4-1-32-0 ∷ []) (refl) ▸
       at 4 1 (Sb0-1-32-4 ∷ []) (sym (lem-F0-at0112203443 c4)) ▸
       at 4 2 (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- CX23-beta @1331: 8 steps
lem-CX23-beta-at1331 : Complete 4 → ⟪ (CX21 ∷ Bx0-3214 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CX23-beta-at1331 c4 = run b0
  where
  b0 : Chain (CX21 ∷ Bx0-3214 ∷ CX21 ∷ []) (Bx0-3214 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX12 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX21 ∷ []) (CX12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-3124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3214⟩ c4) ▸
       at 3 2 (CX12 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX21 ∷ []) (CX12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-3124 ∷ CCZ134 ∷ []) (lem-CX23-beta-at132132 c4) ▸
       at 0 2 (Bx0-3214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3124⟩ c4) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ234 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd12 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd12-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 1 2 (CS12⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd12 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ321: 34 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ321 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ321 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ123 ∷ []) (CS13 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ [])
  b0 = at 1 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS12-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX21 ∷ CS13⁻ ∷ CX21 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ []) (CX21 ∷ CS13⁻ ∷ CX21 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 4 (CX21 ∷ CS13⁻ ∷ CX21 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ []) (CX21 ∷ CS13⁻ ∷ CX21 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ []) (CS13 ∷ CX21 ∷ Bx0-3214 ∷ CCZ234 ∷ CS13⁻ ∷ CX21 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ [])
  b1 = at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 4 (CX21 ∷ CS13⁻ ∷ CX21 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ []) (CX21 ∷ CS13⁻ ∷ CX21 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 4 (CX21 ∷ CS13⁻ ∷ CX21 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ []) (CX21 ∷ CS13⁻ ∷ CX21 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (CX21 ∷ CX21 ∷ []) (lw4 c4 [] (CX21 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 3 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 2 3 (Bx0-3214 ∷ CCZ234 ∷ []) (lem-CX23-beta-at1331 c4) ▸ done

  b2 : Chain (CS13 ∷ CX21 ∷ Bx0-3214 ∷ CCZ234 ∷ CS13⁻ ∷ CX21 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ []) (CS13 ∷ CX21 ∷ CCZ234 ∷ CS13⁻ ∷ CX21 ∷ Bx0-3214 ∷ CCZ234 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ [])
  b2 = at 2 1 (Bx0-3124 ∷ []) (lem-sym23-at1331 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 2 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2332 c4) ▸
       at 3 2 (CS13⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd12-at2332 c4) ▸
       at 4 0 (CX21 ∷ CX21 ∷ []) (lw4 c4 [] (CX21 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 6 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 5 3 (Bx0-3214 ∷ CCZ234 ∷ []) (lem-CX23-beta-at1331 c4) ▸ done

  b3 : Chain (CS13 ∷ CX21 ∷ CCZ234 ∷ CS13⁻ ∷ CX21 ∷ Bx0-3214 ∷ CCZ234 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Sb0-1-32-4 ∷ [])
  b3 = at 5 1 (Bx0-3124 ∷ []) (lem-sym23-at1331 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 5 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2332 c4) ▸
       at 1 2 (CCZ234 ∷ CX21 ∷ []) (lw0 c4 (CX21 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ234 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ []) (lw0 c4 (CX21 ∷ CS13⁻ ∷ CX21 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS23 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS32-at2332 c4) ▸ done

  b4 : Chain (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Sb0-1-32-4 ∷ []) (CCZ123 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ123 ∷ []) (lw4 c4 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | TOFF340: 1 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-TOFF340 : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-TOFF340 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Toff304 ∷ []) (Toff304 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 2 (Toff304 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF304 c4) ▸ done


-- auto BOX(0;1234) | CSd42: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd42 : Complete 4 → ⟪ (Bx0-1234 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ []) (CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CS24⁻ ∷ Bx0-2413 ∷ []) (sym (lem-CSd12-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ Bx0-1234 ∷ []) (CS24⁻ ∷ Bx0-1234 ∷ [])
  b1 = at 0 1 (CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ []) (CS24⁻ ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd42: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS24⁻ ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS24⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd42 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS24⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS42 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42 c4) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd42 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42 c4) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ324: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ324 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ324 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 c4) ▸
       at 1 2 (CX24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332 c4) ▸
       at 2 2 (CS34⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332 c4) ▸
       at 3 2 (CX24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332 c4) ▸
       at 4 2 (CS23 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS32-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done

  b1 : Chain (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Sb0-1-23-4 ∷ []) (CCZ234 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 0 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS14 CS14: 6 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-CS14 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS14 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-CS14 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS14 ∷ CS14 ∷ []) (CS14 ∷ CS14 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 1 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 1 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 c4) ▸
       at 2 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS14 CS14 @2332: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-CS14-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS14 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-CS14-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS14 ∷ CS14 ∷ []) (CS14 ∷ CS14 ∷ Sb0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS14 ∷ CS14 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-CS14 c4) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸ done

  b1 : Chain (CS14 ∷ CS14 ∷ Sb0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ []) (CS14 ∷ CS14 ∷ Sb0-1-32-4 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CZ14: 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ14 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (CZ14 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ14 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CZ14 ∷ []) (CZ14 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14 ∷ CS14 ∷ []) (lw0 c4 (CZ14 ∷ []) (CS14 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 3 (CS14 ∷ CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-CS14-at2332 c4) ▸
       at 2 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 2 (CZ14 ∷ []) (lw0 c4 (CS14 ∷ CS14 ∷ []) (CZ14 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CZ14 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ14-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (CZ14 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ14-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CZ14 ∷ []) (CZ14 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CZ14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ14 ∷ []) (CZ14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ14 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ14 c4) ▸
       at 0 2 (CZ14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ14 ∷ []) (CZ14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CX14: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX14 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX14 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CX14 ∷ []) (CX14 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K4 ∷ CZ14 ∷ K4⁻ ∷ []) (lw0 c4 (CX14 ∷ []) (K4 ∷ CZ14 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 1 2 (CZ14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ14-at2332 c4) ▸
       at 2 2 (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (CX14 ∷ []) (lw0 c4 (K4 ∷ CZ14 ∷ K4⁻ ∷ []) (CX14 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CX14 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX14-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX14-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CX14 ∷ []) (CX14 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CX14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX14 ∷ []) (CX14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX14 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX14 c4) ▸
       at 0 2 (CX14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX14 ∷ []) (CX14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ314: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 c4) ▸
       at 1 2 (CX14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX14-at2332 c4) ▸
       at 2 2 (CS34⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332 c4) ▸
       at 3 2 (CX14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX14-at2332 c4) ▸
       at 4 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS12-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done

  b1 : Chain (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Sb0-1-23-4 ∷ []) (CCZ134 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 0 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- beta-T @0410213243: 8 steps
lem-beta-T-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ c4) ▸
       at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-beta-T-at03102132 c4) ▸
       at 0 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 1 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 3 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @04103143: 8 steps
lem-beta-T-at04103143 : Complete 4 → ⟪ (Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at04103143 c4 = run b0
  where
  b0 : Chain (Bx4-0213 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ c4) ▸
       at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-beta-T-at0410213243 c4) ▸
       at 0 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 3 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0410233142: 8 steps
lem-beta-T-at0410233142 : Complete 4 → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-beta-T-at04103143 c4) ▸
       at 0 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 2 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 3 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(4;0312): 10 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨4·0312⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨4·0312⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx4-0312 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-beta-T-at0410233142 c4) ▸
       at 0 2 (Toff403 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF403 c4) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ124 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 2 (Toff403 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF403 c4) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ124 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CS12⁻ ∷ []) (Bx4-0312 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx4-0312 ∷ []) (sym (lem-beta-T-at0410233142 c4)) ▸ done


-- auto TOFF012 | CCZ134: 7 steps
lem-auto-TOFF012-∣-CCZ134 : Complete 4 → ⟪ (Toff012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ134 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ CCZ134 ∷ []) (CCZ134 ∷ Toff012 ∷ [])
  b0 = at 1 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS14 ∷ Toff012 ∷ []) (pw3 c4 (Toff012 ∷ CS14 ∷ []) (CS14 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁)) ▸
       at 2 2 (CS14⁻ ∷ Toff012 ∷ []) (pw3 c4 (Toff012 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁)) ▸
       at 4 2 (CS13 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS13 ∷ []) (CS13 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- beta-T @04233042: 8 steps
lem-beta-T-at04233042 : Complete 4 → ⟪ (Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at04233042 c4 = run b0
  where
  b0 : Chain (Bx4-1302 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1302⟩ c4) ▸
       at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-beta-T-at0410233142 c4) ▸
       at 0 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 3 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0412233041: 8 steps
lem-beta-T-at0412233041 : Complete 4 → ⟪ (Bx4-2301 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at0412233041 c4 = run b0
  where
  b0 : Chain (Bx4-2301 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2301⟩ c4) ▸
       at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-beta-T-at04233042 c4) ▸
       at 0 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0412233140: 8 steps
lem-beta-T-at0412233140 : Complete 4 → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at0412233140 c4 = run b0
  where
  b0 : Chain (Bx4-2310 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-2301 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·2310⟩ c4) ▸
       at 1 1 (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (lem-beta-T-at0412233041 c4) ▸
       at 0 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 3 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(4;2310): 14 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨4·2310⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨4·2310⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx4-2310 ∷ []) (Toff423 ∷ CCZ014 ∷ CS12⁻ ∷ Toff423 ∷ CCZ014 ∷ [])
  b0 = at 1 1 (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (lem-beta-T-at0412233140 c4) ▸
       at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Toff423 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ014 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Toff423 ∷ CCZ014 ∷ CS12⁻ ∷ Toff423 ∷ CCZ014 ∷ []) (Bx4-2310 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff423 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ014 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx4-2310 ∷ []) (sym (lem-beta-T-at0412233140 c4)) ▸ done


-- sym12 @1331: 5 steps
lem-sym12-at1331 : Complete 4 → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym12-at1331 c4 = run b0
  where
  b0 : Chain (Bx0-3214 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3214⟩ c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta @122331: 8 steps
lem-CX23-beta-at122331 : Complete 4 → ⟪ (CX31 ∷ Bx0-2314 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CX23-beta-at122331 c4 = run b0
  where
  b0 : Chain (CX31 ∷ Bx0-2314 ∷ CX31 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX32 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ c4) ▸
       at 3 2 (CX32 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CX23-beta-at2332 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @122331: 5 steps
lem-sym12-at122331 : Complete 4 → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym12-at122331 c4 = run b0
  where
  b0 : Chain (Bx0-2314 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 0 2 (Bx0-3214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3124⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ431: 36 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ431 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ431 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ134 ∷ []) (CS14 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ [])
  b0 = at 1 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX31 ∷ CS14⁻ ∷ CX31 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ []) (CX31 ∷ CS14⁻ ∷ CX31 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ []) (CS14 ∷ CX31 ∷ Bx0-3214 ∷ CCZ234 ∷ CS14⁻ ∷ CX31 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ [])
  b1 = at 2 6 (CX31 ∷ CS14⁻ ∷ CX31 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ []) (CX31 ∷ CS14⁻ ∷ CX31 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 1 0 (CX31 ∷ CX31 ∷ []) (lw4 c4 [] (CX31 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 3 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 3 1 (Bx0-2314 ∷ []) (lem-sym12-at1331 c4) ▸
       at 2 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-CX23-beta-at122331 c4) ▸
       at 2 1 (Bx0-3214 ∷ []) (lem-sym12-at122331 c4) ▸ done

  b2 : Chain (CS14 ∷ CX31 ∷ Bx0-3214 ∷ CCZ234 ∷ CS14⁻ ∷ CX31 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ []) (CS14 ∷ CX31 ∷ CCZ234 ∷ CS14⁻ ∷ CX31 ∷ CX31 ∷ Bx0-2314 ∷ CX31 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ [])
  b2 = at 2 1 (Bx0-3124 ∷ []) (lem-sym23-at1331 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 2 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 c4) ▸
       at 3 2 (CS14⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2332 c4) ▸
       at 4 0 (CX31 ∷ CX31 ∷ []) (lw4 c4 [] (CX31 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 6 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 6 1 (Bx0-2314 ∷ []) (lem-sym12-at1331 c4) ▸ done

  b3 : Chain (CS14 ∷ CX31 ∷ CCZ234 ∷ CS14⁻ ∷ CX31 ∷ CX31 ∷ Bx0-2314 ∷ CX31 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ []) (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ [])
  b3 = at 5 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-CX23-beta-at122331 c4) ▸
       at 5 1 (Bx0-3214 ∷ []) (lem-sym12-at122331 c4) ▸
       at 5 1 (Bx0-3124 ∷ []) (lem-sym23-at1331 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 5 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 c4) ▸
       at 1 2 (CCZ234 ∷ CX31 ∷ []) (lw0 c4 (CX31 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ234 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ []) (lw0 c4 (CX31 ∷ CS14⁻ ∷ CX31 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done

  b4 : Chain (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ []) (CCZ134 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done

