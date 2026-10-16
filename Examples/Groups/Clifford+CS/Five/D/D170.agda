{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D170 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0034 ; wl0044 ; wl0047 ; wl0078 ; wl0084 ; wl0086 ; wl0095 ; wl0097 ; wl0099 ; wl0110 ; wl0115 ; wl0116 ; wl0228 ; wl0229 ; wl0230 ; wl0244 ; wl0351 ; wl0364 ; wl0599 ; wl0609 ; wl0612 ; wl0613 ; wl0614 ; wl0615 ; wl0624 ; wl0625 ; wl0626 ; wp0034 ; wp0055 ; wp0064 ; wp0261 ; wp0263 ; wp0265 ; wp0267 ; wp0268 ; wp0276 ; wp0277 ; wp0278 ; wp0279 ; wp0281 ; wp0282 ; wp0283)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-T-beta ; lem-T312-beta ; lem-T312-beta-at0314203142 ; lem-T312-beta-at0314213240 ; lem-sym12 ; lem-sym12-at0314203142 ; lem-sym12-at1221 ; lem-sym23-at0314203142 ; lem-sym23-at0314213042 ; lem-sym34-at03102132 ; lem-sym34-at0310213442 ; lem-sym34-at0314213042 ; lem-sym34-at0314213240 ; lem-sym34-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-Cz-beta-at12243143 ; lem-SB2 ; lem-TW ; lem-auto-BOX⟨0·1234⟩-∣-CCZ342 ; lem-beta-T-at03102132 ; lem-sym12-at021021 ; lem-sym12-at03102132 ; lem-sym23-at0310243142 ; lem-sym23-at032032 ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym23-at13243142 ; lem-sym34-at12213443 ; lem-sym34-at13213442)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ124 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-F0-at011220 ; lem-SB2-at011220 ; lem-T312-beta-at03143041 ; lem-T312-beta-at03143140 ; lem-T312-beta-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 ; lem-auto-CCZ012-∣-CCZ342 ; lem-sym12-at0314213240 ; lem-sym12-at03243240 ; lem-sym23-at0314213240 ; lem-sym23-at03143140 ; lem-sym34-at03143041 ; lem-sym34-at03143140)
open import Examples.Groups.Clifford+CS.Five.D.D162 using (lem-T312-beta-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CS43-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CSd43-at03243240 ; lem-beta-inv-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D164 using (lem-TW-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ304 ; lem-auto-CCZ012-∣-CCZ342-at0310243142 ; lem-sym12-at0310213442 ; lem-sym12-at03122031)
open import Examples.Groups.Clifford+CS.Five.D.D165 using (lem-SB2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D166 using (lem-boxify-6 ; lem-boxify-7 ; lem-boxify-8)
open import Examples.Groups.Clifford+CS.Five.D.D167 using (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·2034⟩ ; lem-boxify-9)
open import Examples.Groups.Clifford+CS.Five.D.D169 using (lem-boxify-14-nf-of-rhs)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-BOX⟨0·2413⟩ ; lem-nat-2-BOX⟨0·3124⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·2134⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨3·0124⟩ ; lem-nat-1-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨3·0124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-0-BOX⟨3·0214⟩ ; lem-nat-0-BOX⟨3·1024⟩ ; lem-nat-0-BOX⟨3·1204⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF034 ; lem-nat-1-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·3124⟩ ; lem-nat-0-BOX⟨1·3024⟩ ; lem-nat-0-BOX⟨2·1034⟩ ; lem-nat-0-BOX⟨2·3104⟩ ; lem-nat-1-BOX⟨2·3014⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨2·3014⟩ ; lem-nat-1-BOX⟨1·3024⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨3·0142⟩ ; lem-nat-1-BOX⟨3·0241⟩ ; lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨0·3412⟩ ; lem-nat-0-BOX⟨1·3402⟩ ; lem-nat-0-BOX⟨2·3401⟩ ; lem-nat-0-BOX⟨2·3410⟩ ; lem-nat-1-BOX⟨1·3402⟩ ; lem-nat-1-BOX⟨2·3401⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨0·3124⟩ ; lem-nat-1-BOX⟨0·3241⟩ ; lem-nat-1-BOX⟨3·0421⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨3·0124⟩ ; lem-nat-0-BOX⟨3·0142⟩ ; lem-nat-0-BOX⟨3·1042⟩ ; lem-nat-1-BOX⟨0·3142⟩ ; lem-nat-1-BOX⟨3·1024⟩ ; lem-nat-1-BOX⟨3·1042⟩ ; lem-nat-1-BOX⟨3·2014⟩ ; lem-nat-1-BOX⟨3·2041⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨0·3421⟩ ; lem-nat-0-BOX⟨1·3420⟩ ; lem-nat-0-BOX⟨3·2014⟩ ; lem-nat-0-BOX⟨3·2104⟩ ; lem-nat-1-BOX⟨0·3412⟩ ; lem-nat-1-BOX⟨0·3421⟩ ; lem-nat-1-BOX⟨1·3420⟩ ; lem-nat-1-BOX⟨2·3410⟩ ; lem-nat-1-BOX⟨3·1204⟩ ; lem-nat-1-BOX⟨3·2104⟩)
-- boxify-14: 334 steps
lem-boxify-14 : Ws → ⟪ (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-14 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (run b41)))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b0 = at 0 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 2 1 (CS01 ∷ []) (refl) ▸
       at 4 1 (CS01⁻ ∷ []) (refl) ▸
       at 7 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 7 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 9 1 (CS01 ∷ []) (refl) ▸
       at 11 1 (CS01⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b1 = at 16 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 16 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 18 1 (CS02 ∷ []) (refl) ▸
       at 20 1 (CS02⁻ ∷ []) (refl) ▸
       at 16 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 18 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 18 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 18 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸ done

  b2 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-4012 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b2 = at 17 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 17 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 17 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 17 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 17 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 18 2 (CS02 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4) ▸
       at 19 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 21 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸ done

  b3 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-4012 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b3 = at 21 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 21 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 20 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 20 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 20 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 20 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 20 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 21 2 (CS02⁻ ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4) ▸ done

  b4 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Bx3-0412 ∷ CCZ014 ∷ Toff124 ∷ Toff214 ∷ [])
  b4 = at 22 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 24 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 24 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 24 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 23 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 23 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 23 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 23 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸ done

  b5 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Bx3-0412 ∷ CCZ014 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ Bx3-4120 ∷ CCZ024 ∷ Toff214 ∷ [])
  b5 = at 23 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 24 0 (Toff124 ∷ Toff124 ∷ []) (sym (wl0614 (lit c4))) ▸
       at 26 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 26 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 26 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 26 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 25 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-T312-beta-at03143140 c4) ▸
       at 25 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸ done

  b6 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ Bx3-4120 ∷ CCZ024 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ [])
  b6 = at 25 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 25 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 25 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 25 2 (CCZ024 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 c4) ▸
       at 26 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 28 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 28 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 28 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸ done

  b7 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ Toff024 ∷ Bx3-4210 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b7 = at 27 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 27 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 27 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 27 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 27 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 7 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0268 c4)) ▸
       at 9 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 9 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸ done

  b8 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ Toff024 ∷ Bx3-4210 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ Toff024 ∷ Bx3-1420 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b8 = at 9 1 (Bx3-4201 ∷ []) (lem-sym34-at03143140 c4) ▸
       at 8 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-T312-beta-at03143041 c4) ▸
       at 8 1 (Bx3-4210 ∷ []) (lem-sym34-at03143041 c4) ▸
       at 8 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 8 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 8 2 (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4) ▸
       at 9 2 (CS01 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 c4) ▸
       at 10 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0268 c4)) ▸ done

  b9 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ Toff024 ∷ Bx3-1420 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ Bx3-1420 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b9 = at 12 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 12 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 12 1 (Bx3-4201 ∷ []) (lem-sym34-at03143140 c4) ▸
       at 11 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-T312-beta-at03143041 c4) ▸
       at 11 1 (Bx3-4210 ∷ []) (lem-sym34-at03143041 c4) ▸
       at 11 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 11 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 11 2 (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4) ▸ done

  b10 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ Bx3-1420 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Bx3-4120 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b10 = at 12 2 (CS01⁻ ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 c4) ▸
       at 13 0 (Toff104 ∷ Toff104 ∷ []) (sym (wp0064 c4)) ▸
       at 15 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 15 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 15 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 14 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-T312-beta-at0314203142 c4) ▸
       at 14 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 14 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸ done

  b11 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Bx3-4120 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ Toff124 ∷ Bx3-1420 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b11 = at 14 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 14 2 (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 c4) ▸
       at 15 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 16 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 18 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 16 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-T312-beta-at03243240 c4) ▸
       at 16 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 17 0 (Toff124 ∷ Toff124 ∷ []) (sym (wl0614 (lit c4))) ▸ done

  b12 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ Toff124 ∷ Bx3-1420 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b12 = at 19 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 19 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 18 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-T312-beta-at03143140 c4) ▸
       at 18 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 18 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 18 2 (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 c4) ▸
       at 19 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 20 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸ done

  b13 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Bx3-1420 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b13 = at 22 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 20 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-T312-beta-at03243240 c4) ▸
       at 20 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 21 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 22 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 24 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 22 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-T312-beta-at03243240 c4) ▸
       at 22 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸ done

  b14 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Bx3-1420 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b14 = at 23 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 c4) ▸
       at 24 2 (CS02 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at03243240 c4) ▸
       at 25 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 26 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 28 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 26 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-T312-beta-at03243240 c4) ▸
       at 26 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 27 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 c4) ▸ done

  b15 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ Toff124 ∷ Bx3-1420 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b15 = at 28 2 (CS02⁻ ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at03243240 c4) ▸
       at 29 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 30 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 32 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 30 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-T312-beta-at03243240 c4) ▸
       at 30 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 31 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 c4) ▸
       at 32 0 (Toff124 ∷ Toff124 ∷ []) (sym (wl0614 (lit c4))) ▸ done

  b16 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ Toff124 ∷ Bx3-1420 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b16 = at 34 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 34 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 33 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-T312-beta-at03143140 c4) ▸
       at 33 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 33 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 33 2 (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 c4) ▸
       at 34 2 (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 c4) ▸
       at 35 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b17 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Toff024 ∷ Toff024 ∷ Bx3-4210 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b17 = at 36 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 38 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 36 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-T312-beta-at03243240 c4) ▸
       at 36 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 37 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 c4) ▸
       at 0 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0268 c4)) ▸
       at 2 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 2 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸ done

  b18 : Chain (Toff024 ∷ Toff024 ∷ Bx3-4210 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ Toff024 ∷ Bx3-1420 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b18 = at 2 1 (Bx3-4201 ∷ []) (lem-sym34-at03143140 c4) ▸
       at 1 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-T312-beta-at03143041 c4) ▸
       at 1 1 (Bx3-4210 ∷ []) (lem-sym34-at03143041 c4) ▸
       at 1 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 1 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 1 2 (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4) ▸
       at 2 2 (CS01 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 c4) ▸
       at 3 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0268 c4)) ▸ done

  b19 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ Toff024 ∷ Bx3-1420 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ Bx3-1420 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b19 = at 5 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 5 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 5 1 (Bx3-4201 ∷ []) (lem-sym34-at03143140 c4) ▸
       at 4 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-T312-beta-at03143041 c4) ▸
       at 4 1 (Bx3-4210 ∷ []) (lem-sym34-at03143041 c4) ▸
       at 4 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 4 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 4 2 (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4) ▸ done

  b20 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ Bx3-1420 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Bx3-4120 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b20 = at 5 2 (CS01⁻ ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 c4) ▸
       at 6 0 (Toff104 ∷ Toff104 ∷ []) (sym (wp0064 c4)) ▸
       at 8 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 8 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 8 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 7 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-T312-beta-at0314203142 c4) ▸
       at 7 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 7 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸ done

  b21 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Bx3-4120 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ Bx3-4201 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b21 = at 7 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 7 2 (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 c4) ▸
       at 8 2 (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 c4) ▸
       at 9 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0268 c4)) ▸
       at 11 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 11 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 11 1 (Bx3-4201 ∷ []) (lem-sym34-at03143140 c4) ▸
       at 10 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-T312-beta-at03143041 c4) ▸ done

  b22 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ Bx3-4201 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ Toff024 ∷ Bx3-4120 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b22 = at 10 1 (Bx3-4210 ∷ []) (lem-sym34-at03143041 c4) ▸
       at 10 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 10 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 10 2 (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4) ▸
       at 11 2 (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4) ▸
       at 12 2 (CS01 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 c4) ▸
       at 13 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0268 c4)) ▸
       at 15 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸ done

  b23 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ Toff024 ∷ Bx3-4120 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ Bx3-1420 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b23 = at 15 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 15 1 (Bx3-4201 ∷ []) (lem-sym34-at03143140 c4) ▸
       at 14 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-T312-beta-at03143041 c4) ▸
       at 14 1 (Bx3-4210 ∷ []) (lem-sym34-at03143041 c4) ▸
       at 14 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 14 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 14 2 (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4) ▸
       at 15 2 (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4) ▸ done

  b24 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ Bx3-1420 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Bx3-4120 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b24 = at 16 2 (CS01⁻ ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 c4) ▸
       at 17 0 (Toff104 ∷ Toff104 ∷ []) (sym (wp0064 c4)) ▸
       at 19 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 19 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 19 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 18 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-T312-beta-at0314203142 c4) ▸
       at 18 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 18 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸ done

  b25 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Bx3-4120 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-1420 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b25 = at 18 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 18 2 (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 c4) ▸
       at 19 2 (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 c4) ▸
       at 20 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 21 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 23 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 21 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-T312-beta-at03243240 c4) ▸
       at 21 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸ done

  b26 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-1420 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Bx3-1420 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b26 = at 22 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 23 0 (Toff124 ∷ Toff124 ∷ []) (sym (wl0614 (lit c4))) ▸
       at 25 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 25 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 24 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-T312-beta-at03143140 c4) ▸
       at 24 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 24 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 24 2 (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 c4) ▸ done

  b27 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Bx3-1420 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b27 = at 25 2 (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 c4) ▸
       at 26 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 27 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 29 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 27 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-T312-beta-at03243240 c4) ▸
       at 27 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 28 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 29 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b28 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b28 = at 30 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 32 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 30 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-T312-beta-at03243240 c4) ▸
       at 30 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 31 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 32 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 c4) ▸
       at 33 2 (CS02 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at03243240 c4) ▸
       at 34 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b29 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b29 = at 35 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 37 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 35 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-T312-beta-at03243240 c4) ▸
       at 35 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 36 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 37 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 c4) ▸
       at 38 2 (CS02⁻ ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at03243240 c4) ▸
       at 39 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b30 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ Toff124 ∷ Bx3-4120 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b30 = at 40 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 42 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 40 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-T312-beta-at03243240 c4) ▸
       at 40 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 41 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 42 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 c4) ▸
       at 43 0 (Toff124 ∷ Toff124 ∷ []) (sym (wl0614 (lit c4))) ▸
       at 45 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸ done

  b31 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ Toff124 ∷ Bx3-4120 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b31 = at 45 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 44 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-T312-beta-at03143140 c4) ▸
       at 44 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 44 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 44 2 (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 c4) ▸
       at 45 2 (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 c4) ▸
       at 46 2 (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 c4) ▸
       at 47 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b32 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0142 ∷ [])
  b32 = at 48 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 50 1 (Toff214 ∷ []) (wl0615 (lit c4)) ▸
       at 48 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-T312-beta-at03243240 c4) ▸
       at 48 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 49 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4) ▸
       at 50 2 (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 c4) ▸
       at 51 2 [] (lem-beta-inv-at03243240 c4) ▸
       at 51 1 (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4) ▸ done

  b33 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0142 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ [])
  b33 = at 51 1 (Bx3-0124 ∷ []) (lem-sym34-at0310213442 c4) ▸
       at 46 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 45 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 44 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 42 2 (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0265 c4) ▸
       at 44 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 43 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 41 2 (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0265 c4) ▸ done

  b34 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ [])
  b34 = at 43 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 42 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 40 2 (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0265 c4) ▸
       at 42 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 41 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 28 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 27 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 25 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸ done

  b35 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ [])
  b35 = at 27 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 26 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 24 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 26 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 25 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 22 2 (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0265 c4) ▸
       at 24 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 26 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸ done

  b36 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ [])
  b36 = at 25 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 23 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 24 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 21 2 (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0265 c4) ▸
       at 23 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 25 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 24 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 22 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸ done

  b37 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ [])
  b37 = at 23 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 19 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 21 2 (Toff124 ∷ CCZ024 ∷ []) (wp0281 c4) ▸
       at 22 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 24 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 23 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 20 2 (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0265 c4) ▸
       at 22 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸ done

  b38 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ [])
  b38 = at 24 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 23 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 21 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 22 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 18 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 20 2 (Toff124 ∷ CCZ024 ∷ []) (wp0281 c4) ▸
       at 21 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 23 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸ done

  b39 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ [])
  b39 = at 22 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 19 2 (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0265 c4) ▸
       at 21 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 23 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 22 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 20 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 21 2 (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 8 2 (Toff024 ∷ CCZ124 ∷ []) (wp0278 c4) ▸ done

  b40 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CZ24 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ [])
  b40 = at 7 2 (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) (wp0279 c4) ▸
       at 65 2 [] (wp0055 c4) ▸
       at 66 3 (CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ []) (wp0282 c4) ▸
       at 65 2 [] (wp0034 c4) ▸
       at 65 2 [] (wp0055 c4) ▸
       at 65 2 [] (wp0055 c4) ▸
       at 66 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0277 c4) ▸
       at 65 2 [] (wp0034 c4) ▸ done

  b41 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CZ24 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-0124 ∷ []) (Bx3-0124 ∷ [])
  b41 = at 65 2 [] (wp0055 c4) ▸
       at 66 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0277 c4) ▸
       at 65 2 [] (wp0034 c4) ▸
       at 66 2 [] (wp0055 c4) ▸
       at 0 67 [] (wp0283 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (sym (lem-boxify-14-nf-of-rhs c4)) ▸ done


-- sym12 @031031: 5 steps
lem-sym12-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-sym12-at031031 c4 = run b0
  where
  b0 : Chain (Bx3-0214 ∷ []) (Bx3-2014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ (lit c4)) ▸
       at 1 1 (Bx3-1024 ∷ []) (lem-sym12-at03102132 c4) ▸
       at 0 2 (Bx3-2014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1024⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @03122031: 5 steps
lem-sym23-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-sym23-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Bx3-2104 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ (lit c4)) ▸
       at 1 1 (Bx3-1204 ∷ []) (lem-sym23-at032032 c4) ▸
       at 0 2 (Bx3-2104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1204⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @032032: 8 steps
lem-beta-T-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ (lit c4)) ▸
       at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-beta-T-at03102132 c4) ▸
       at 0 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 2 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- beta-T @03122031: 8 steps
lem-beta-T-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ (lit c4)) ▸
       at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-beta-T-at032032 c4) ▸
       at 0 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 2 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @03122130: 8 steps
lem-beta-T-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ (lit c4)) ▸
       at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03122031 c4) ▸
       at 0 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 2 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @03122130: 5 steps
lem-sym23-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-sym23-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ []) (Bx3-2014 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ (lit c4)) ▸
       at 1 1 (Bx3-2104 ∷ []) (lem-sym23-at03122031 c4) ▸
       at 0 2 (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(3;0214): 23 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩ c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1234 ∷ Bx3-0214 ∷ []) (Toff312 ∷ CCZ124 ∷ Bx0-1234 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Bx3-2014 ∷ []) (lem-sym12-at031031 c4) ▸
       at 1 1 (Bx3-2104 ∷ []) (lem-sym23-at03122031 c4) ▸
       at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-beta-T-at03122130 c4) ▸
       at 0 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 1 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸
       at 3 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 1 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124 c4) ▸ done

  b1 : Chain (Toff312 ∷ CCZ124 ∷ Bx0-1234 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (CCZ124 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ Bx0-1234 ∷ [])
  b1 = at 2 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ304 c4) ▸
       at 3 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 4 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸
       at 6 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸
       at 4 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 4 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124 c4) ▸
       at 5 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ304 c4) ▸
       at 0 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0624 (lit c4))) ▸ done

  b2 : Chain (CCZ124 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ Bx0-1234 ∷ []) (Bx3-0214 ∷ Bx0-1234 ∷ [])
  b2 = at 3 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0624 (lit c4))) ▸
       at 2 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0310243142 c4) ▸
       at 1 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0624 (lit c4))) ▸
       at 0 2 [] (wl0351 (lit c4)) ▸
       at 0 4 (Bx3-2104 ∷ []) (sym (lem-beta-T-at03122130 c4)) ▸
       at 0 1 (Bx3-2014 ∷ []) (lem-sym23-at03122130 c4) ▸
       at 0 1 (Bx3-0214 ∷ []) (lem-sym12-at03122031 c4) ▸ done


-- auto BOX(0;1234) | CCZ042: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ042 : Ws → ⟪ (Bx0-1234 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ []) (wp0261 c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CCZ024 ∷ Bx0-2413 ∷ []) (sym (lem-Cz-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Bx0-1234 ∷ []) (CCZ024 ∷ Bx0-1234 ∷ [])
  b1 = at 0 1 (CCZ024 ∷ []) (wp0261 c4) ▸ done


-- auto BOX(0;1234) | TOFF021: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF021 : Ws → ⟪ (Bx0-1234 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF021 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Toff012 ∷ []) (Toff012 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff012 ∷ []) (wl0599 (lit c4)) ▸
       at 0 2 (Toff012 ∷ Bx0-1234 ∷ []) (sym (lem-T-beta c4)) ▸
       at 0 1 (Toff012 ∷ []) (wl0599 (lit c4)) ▸ done


-- auto CCZ012 | TOFF342: 5 steps
lem-auto-CCZ012-∣-TOFF342 : Ws → ⟪ (CCZ012 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0364 (lit c4))) ▸
       at 0 2 (K3 ∷ CCZ012 ∷ []) (wl0228 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342 c4) ▸
       at 2 2 (K3⁻ ∷ CCZ012 ∷ []) (wl0229 (lit c4)) ▸
       at 0 3 (Toff324 ∷ []) (wl0364 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;2034) @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·2034⟩-at0110 : Ws → ⟪ (Bx1-0234 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·2034⟩-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (Bx1-2034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;2034) @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·2034⟩-at021021 : Ws → ⟪ (Bx2-0134 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·2034⟩-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (Bx0-2134 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·2034⟩-at0110 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F1 toff-ccz [nf of rhs]: 51 steps
lem-F1-toff-ccz-nf-of-rhs : Ws → ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-F1-toff-ccz-nf-of-rhs c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b0 = at 1 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 5 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 9 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 14 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 17 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 20 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 24 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 28 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸ done

  b1 : Chain (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b1 = at 32 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 37 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 41 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 45 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 49 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 53 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 57 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 62 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸ done

  b2 : Chain (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b2 = at 65 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 68 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 72 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 76 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 80 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 85 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 89 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 93 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸ done

  b3 : Chain (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b3 = at 0 4 (Toff324 ∷ []) (wl0625 (lit c4)) ▸
       at 1 4 (Toff234 ∷ []) (wl0626 (lit c4)) ▸
       at 2 4 (Toff324 ∷ []) (wl0625 (lit c4)) ▸
       at 4 4 (Toff104 ∷ []) (wp0267 c4) ▸
       at 7 4 (Toff104 ∷ []) (wp0267 c4) ▸
       at 8 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 9 4 (Toff124 ∷ []) (wl0613 (lit c4)) ▸
       at 10 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸ done

  b4 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-2-43-1 ∷ Toff214 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ Toff214 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b4 = at 12 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 13 4 (Toff124 ∷ []) (wl0613 (lit c4)) ▸
       at 14 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 15 4 (Toff324 ∷ []) (wl0625 (lit c4)) ▸
       at 16 4 (Toff234 ∷ []) (wl0626 (lit c4)) ▸
       at 17 4 (Toff324 ∷ []) (wl0625 (lit c4)) ▸
       at 19 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 22 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸ done

  b5 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-2-43-1 ∷ Toff214 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ Toff214 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ Sb0-2-43-1 ∷ Toff214 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b5 = at 23 4 (Toff324 ∷ []) (wl0625 (lit c4)) ▸
       at 24 4 (Toff234 ∷ []) (wl0626 (lit c4)) ▸
       at 25 4 (Toff324 ∷ []) (wl0625 (lit c4)) ▸
       at 27 4 (Toff324 ∷ []) (wl0625 (lit c4)) ▸
       at 28 4 (Toff234 ∷ []) (wl0626 (lit c4)) ▸
       at 29 4 (Toff324 ∷ []) (wl0625 (lit c4)) ▸
       at 3 12 (Bx3-0124 ∷ []) (lem-boxify-6 c4) ▸
       at 2 3 (Bx3-0124 ∷ []) (lem-boxify-7 c4) ▸ done

  b6 : Chain (Toff324 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ Sb0-2-43-1 ∷ Toff214 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-1234 ∷ Bx2-0134 ∷ [])
  b6 = at 0 5 (Bx2-0134 ∷ []) (lem-boxify-8 c4) ▸
       at 1 12 (Bx0-1234 ∷ []) (lem-boxify-9 c4) ▸
       at 0 2 (Bx0-1234 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·2034⟩-at021021 c4) ▸ done


-- TW @1221: 8 steps
lem-TW-at1221 : Ws → ⟪ (Toff201 ∷ Bx0-2134 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-TW-at1221 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx0-2134 ∷ Toff201 ∷ []) (Bx0-2134 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 (lit c4)) ▸
       at 1 3 (Bx0-1234 ∷ Bx1-0234 ∷ []) (lem-TW c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- TW @132132: 8 steps
lem-TW-at132132 : Ws → ⟪ (Toff301 ∷ Bx0-3124 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-TW-at132132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx0-3124 ∷ Toff301 ∷ []) (Bx0-3124 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 (lit c4)) ▸
       at 2 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ (lit c4)) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 (lit c4)) ▸
       at 1 3 (Bx0-2134 ∷ Bx2-0134 ∷ []) (lem-TW-at1221 c4) ▸
       at 0 2 (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- TW @01132032: 8 steps
lem-TW-at01132032 : Ws → ⟪ (Toff301 ∷ Bx1-3024 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ Bx3-1024 ∷ []) ⟫ʷ
lem-TW-at01132032 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx1-3024 ∷ Toff301 ∷ []) (Bx1-3024 ∷ Bx3-1024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 (lit c4)) ▸
       at 2 2 (Bx0-3124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3024⟩ (lit c4)) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 (lit c4)) ▸
       at 1 3 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-TW-at132132 c4) ▸
       at 0 2 (Bx1-3024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3124⟩ (lit c4)) ▸
       at 1 2 (Bx3-1024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- TW @02132031: 8 steps
lem-TW-at02132031 : Ws → ⟪ (Toff302 ∷ Bx2-3014 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ Bx3-2014 ∷ []) ⟫ʷ
lem-TW-at02132031 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Bx2-3014 ∷ Toff302 ∷ []) (Bx2-3014 ∷ Bx3-2014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 (lit c4)) ▸
       at 2 2 (Bx1-3024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3014⟩ (lit c4)) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 (lit c4)) ▸
       at 1 3 (Bx1-3024 ∷ Bx3-1024 ∷ []) (lem-TW-at01132032 c4) ▸
       at 0 2 (Bx2-3014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3024⟩ (lit c4)) ▸
       at 1 2 (Bx3-2014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1024⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- TW @02132130: 8 steps
lem-TW-at02132130 : Ws → ⟪ (Toff312 ∷ Bx2-3104 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ Bx3-2104 ∷ []) ⟫ʷ
lem-TW-at02132130 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Bx2-3104 ∷ Toff312 ∷ []) (Bx2-3104 ∷ Bx3-2104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 (lit c4)) ▸
       at 2 2 (Bx2-3014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3104⟩ (lit c4)) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 (lit c4)) ▸
       at 1 3 (Bx2-3014 ∷ Bx3-2014 ∷ []) (lem-TW-at02132031 c4) ▸
       at 0 2 (Bx2-3104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3014⟩ (lit c4)) ▸
       at 1 2 (Bx3-2104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2014⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @0220: 5 steps
lem-sym12-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym12-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ (lit c4)) ▸
       at 1 1 (Bx2-1034 ∷ []) (lem-sym12-at021021 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(3;0214) @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at0110 : Ws → ⟪ (Bx1-0234 ∷ Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ Bx3-1204 ∷ []) (Bx3-1204 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (Bx3-0214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1204⟩ (lit c4)) ▸
       at 1 2 (Bx3-0214 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩ c4) ▸
       at 0 2 (Bx3-1204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0214⟩ (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(3;0214) @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at021021 : Ws → ⟪ (Bx2-0134 ∷ Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ Bx3-2104 ∷ []) (Bx3-2104 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (Bx3-1204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2104⟩ (lit c4)) ▸
       at 1 2 (Bx3-1204 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at0110 c4) ▸
       at 0 2 (Bx3-2104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1204⟩ (lit c4)) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- T312-beta @12243143: 8 steps
lem-T312-beta-at12243143 : Ws → ⟪ (Toff124 ∷ Bx0-2413 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ234 ∷ []) ⟫ʷ
lem-T312-beta-at12243143 c4 = run b0
  where
  b0 : Chain (Toff124 ∷ Bx0-2413 ∷ Toff124 ∷ []) (Bx0-2413 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 (lit c4)) ▸
       at 1 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-T312-beta-at243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- T312-beta @13243142: 8 steps
lem-T312-beta-at13243142 : Ws → ⟪ (Toff134 ∷ Bx0-3412 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ234 ∷ []) ⟫ʷ
lem-T312-beta-at13243142 c4 = run b0
  where
  b0 : Chain (Toff134 ∷ Bx0-3412 ∷ Toff134 ∷ []) (Bx0-3412 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 (lit c4)) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 (lit c4)) ▸
       at 1 3 (Bx0-2413 ∷ CCZ234 ∷ []) (lem-T312-beta-at12243143 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- T312-beta @0113243042: 8 steps
lem-T312-beta-at0113243042 : Ws → ⟪ (Toff034 ∷ Bx1-3402 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ CCZ234 ∷ []) ⟫ʷ
lem-T312-beta-at0113243042 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx1-3402 ∷ Toff034 ∷ []) (Bx1-3402 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 (lit c4)) ▸
       at 2 2 (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ (lit c4)) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 (lit c4)) ▸
       at 1 3 (Bx0-3412 ∷ CCZ234 ∷ []) (lem-T312-beta-at13243142 c4) ▸
       at 0 2 (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- T312-beta @0213243041: 8 steps
lem-T312-beta-at0213243041 : Ws → ⟪ (Toff034 ∷ Bx2-3401 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at0213243041 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx2-3401 ∷ Toff034 ∷ []) (Bx2-3401 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 (lit c4)) ▸
       at 2 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ (lit c4)) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 (lit c4)) ▸
       at 1 3 (Bx1-3402 ∷ CCZ234 ∷ []) (lem-T312-beta-at0113243042 c4) ▸
       at 0 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ342 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110 : Ws → ⟪ (Bx1-0234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ342 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at021021 : Ws → ⟪ (Bx2-0134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @032032: 5 steps
lem-sym34-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-sym34-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-1042 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ (lit c4)) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym34-at03102132 c4) ▸
       at 0 2 (Bx3-1042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0142⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @03122031: 5 steps
lem-sym34-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-sym34-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ (lit c4)) ▸
       at 1 1 (Bx3-1042 ∷ []) (lem-sym34-at032032 c4) ▸
       at 0 2 (Bx3-2041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1042⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @03203442: 5 steps
lem-sym12-at03203442 : Ws → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym12-at03203442 c4 = run b0
  where
  b0 : Chain (Bx3-1042 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1042⟩ (lit c4)) ▸
       at 1 1 (Bx3-1042 ∷ []) (lem-sym12-at0310213442 c4) ▸
       at 0 2 (Bx3-0142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1042⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @0312203441: 5 steps
lem-sym12-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-sym12-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2041⟩ (lit c4)) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym12-at03203442 c4) ▸
       at 0 2 (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- TW @0310243241: 8 steps
lem-TW-at0310243241 : Ws → ⟪ (Toff034 ∷ Bx3-0421 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ Bx0-3421 ∷ []) ⟫ʷ
lem-TW-at0310243241 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx3-0421 ∷ Toff034 ∷ []) (Bx3-0421 ∷ Bx0-3421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 (lit c4)) ▸
       at 2 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4)) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 (lit c4)) ▸
       at 1 3 (Bx3-0412 ∷ Bx0-3412 ∷ []) (lem-TW-at0310243142 c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (Bx0-3421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3412⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @03103441: 5 steps
lem-sym34-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym34-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ (lit c4)) ▸
       at 1 1 (Bx3-0124 ∷ []) (lem-sym34-at0310213442 c4) ▸
       at 0 2 (Bx3-0214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0124⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(3;0412) @032032: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at032032 : Ws → ⟪ (Bx3-1024 ∷ Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ Bx3-1024 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ Bx2-3410 ∷ []) (Bx2-3410 ∷ Bx3-1024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ (lit c4)) ▸
       at 2 2 (Bx2-3401 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3410⟩ (lit c4)) ▸
       at 1 2 (Bx2-3401 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 c4) ▸
       at 0 2 (Bx2-3410 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3401⟩ (lit c4)) ▸
       at 1 2 (Bx3-1024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(3;0412) @03122031: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122031 : Ws → ⟪ (Bx3-2014 ∷ Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ Bx3-2014 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ Bx1-3420 ∷ []) (Bx1-3420 ∷ Bx3-2014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ (lit c4)) ▸
       at 2 2 (Bx2-3410 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3420⟩ (lit c4)) ▸
       at 1 2 (Bx2-3410 ∷ Bx3-1024 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at032032 c4) ▸
       at 0 2 (Bx1-3420 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3410⟩ (lit c4)) ▸
       at 1 2 (Bx3-2014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1024⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(3;0412) @03122130: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122130 : Ws → ⟪ (Bx3-2104 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Bx3-2104 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ Bx0-3421 ∷ []) (Bx0-3421 ∷ Bx3-2104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ (lit c4)) ▸
       at 2 2 (Bx1-3420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3421⟩ (lit c4)) ▸
       at 1 2 (Bx1-3420 ∷ Bx3-2014 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122031 c4) ▸
       at 0 2 (Bx0-3421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3420⟩ (lit c4)) ▸
       at 1 2 (Bx3-2104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2014⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ042 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at0110 : Ws → ⟪ (Bx1-0234 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042 c4) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ042 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at021021 : Ws → ⟪ (Bx2-0134 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at0110 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ042 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03102132 : Ws → ⟪ (Bx3-0124 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at021021 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ042 @032032: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at032032 : Ws → ⟪ (Bx3-1024 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx3-1024 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx3-1024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03102132 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 1 2 (Bx3-1024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ042 @03122031: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122031 : Ws → ⟪ (Bx3-2014 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx3-2014 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx3-2014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Bx3-1024 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at032032 c4) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 1 2 (Bx3-2014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1024⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ042 @03122130: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122130 : Ws → ⟪ (Bx3-2104 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx3-2104 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx3-2104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Bx3-2014 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122031 c4) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 1 2 (Bx3-2104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2014⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ124 @12243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at12243143 : Ws → ⟪ (Bx0-2413 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 1 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ124 @13243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243142 : Ws → ⟪ (Bx0-3412 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-3412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Bx0-2413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at12243143 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ124 @13243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243241 : Ws → ⟪ (Bx0-3421 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-3421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-3421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Bx0-3412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243142 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 1 2 (Bx0-3421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3412⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF021 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at0110 : Ws → ⟪ (Bx1-0234 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ Toff102 ∷ []) (Toff102 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 (lit c4)) ▸
       at 1 2 (Toff012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021 c4) ▸
       at 0 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF021 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at021021 : Ws → ⟪ (Bx2-0134 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ Toff201 ∷ []) (Toff201 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 (lit c4)) ▸
       at 1 2 (Toff102 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at0110 c4) ▸
       at 0 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4)) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF021 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ Toff301 ∷ []) (Toff301 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 (lit c4)) ▸
       at 1 2 (Toff201 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at021021 c4) ▸
       at 0 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4)) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF021 @032032: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at032032 : Ws → ⟪ (Bx3-1024 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Bx3-1024 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ Toff301 ∷ []) (Toff301 ∷ Bx3-1024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ (lit c4)) ▸
       at 2 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 (lit c4)) ▸
       at 1 2 (Toff301 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03102132 c4) ▸
       at 0 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 (lit c4)) ▸
       at 1 2 (Bx3-1024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF021 @03122031: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122031 : Ws → ⟪ (Bx3-2014 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Bx3-2014 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ Toff302 ∷ []) (Toff302 ∷ Bx3-2014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ (lit c4)) ▸
       at 2 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 (lit c4)) ▸
       at 1 2 (Toff301 ∷ Bx3-1024 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at032032 c4) ▸
       at 0 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4)) ▸
       at 1 2 (Bx3-2014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1024⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF021 @03122130: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122130 : Ws → ⟪ (Bx3-2104 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Bx3-2104 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ Toff312 ∷ []) (Toff312 ∷ Bx3-2104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ (lit c4)) ▸
       at 2 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 (lit c4)) ▸
       at 1 2 (Toff302 ∷ Bx3-2014 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122031 c4) ▸
       at 0 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 (lit c4)) ▸
       at 1 2 (Bx3-2104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2014⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @13243241: 5 steps
lem-sym23-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-sym23-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ []) (Bx0-3241 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ (lit c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 0 2 (Bx0-3241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3142⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @133441: 5 steps
lem-sym34-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym34-at133441 c4 = run b0
  where
  b0 : Chain (Bx0-3241 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ (lit c4)) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 0 2 (Bx0-3214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3124⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done

