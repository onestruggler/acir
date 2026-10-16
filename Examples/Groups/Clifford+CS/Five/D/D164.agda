{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D164 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0034 ; wl0063 ; wl0078 ; wl0084 ; wl0086 ; wl0127 ; wl0136 ; wl0140 ; wl0144 ; wl0155 ; wl0230 ; wl0242 ; wl0244 ; wl0248 ; wl0265 ; wl0267 ; wl0351 ; wl0614 ; wl0615 ; wl0616 ; wl0617 ; wl0618 ; wl0619 ; wl0620 ; wl0621 ; wl0622 ; wl0623 ; wl0624 ; wp0025 ; wp0034 ; wp0055 ; wp0064 ; wp0263 ; wp0265 ; wp0268 ; wp0276 ; wp0277 ; wp0278 ; wp0279 ; wp0281 ; wp0282 ; wp0283 ; wp0284 ; wp0285)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-T-beta ; lem-T312-beta ; lem-T312-beta-at0314203142 ; lem-T312-beta-at0314213240 ; lem-beta-T-at0314213042 ; lem-beta-inv-at0310243142 ; lem-sym12 ; lem-sym12-at0110 ; lem-sym12-at011220 ; lem-sym12-at0314203142 ; lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23 ; lem-sym23-at0314203142 ; lem-sym23-at0314213042 ; lem-sym23-at1221 ; lem-sym34 ; lem-sym34-at03102132 ; lem-sym34-at0310213442 ; lem-sym34-at0314213042 ; lem-sym34-at0314213240 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-Cz-beta-at13243142 ; lem-Cz-beta-at2332 ; lem-Cz-beta-at243243 ; lem-T312-beta-at122331 ; lem-TW ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234 ; lem-beta-T-at0330 ; lem-sym12-at03102132 ; lem-sym12-at233442 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at03102132 ; lem-sym23-at0310213442 ; lem-sym23-at0310243142 ; lem-sym23-at122331 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at13213442 ; lem-sym34-at2332 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ124 ; lem-sym23-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-beta-T-at01122330 ; lem-sym12-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-sym12-at0210213443 ; lem-sym23-at233442 ; lem-sym23-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-sym23-at0213243041 ; lem-sym34-at0213203441)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ142)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-F0-at011220 ; lem-T312-beta-at03143041 ; lem-T312-beta-at03143140 ; lem-T312-beta-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 ; lem-auto-CCZ012-∣-CCZ342 ; lem-auto-CCZ012-∣-CCZ342-at03102132 ; lem-sym12-at0314213240 ; lem-sym12-at03243240 ; lem-sym23-at0314213240 ; lem-sym23-at03143140 ; lem-sym34-at03143041 ; lem-sym34-at03143140)
open import Examples.Groups.Clifford+CS.Five.D.D162 using (lem-T312-beta-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CS43-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CSd43-at03243240 ; lem-beta-inv-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D163 using (lem-boxify-2-nf-of-rhs)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF103 ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-2-BOX⟨0·2413⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF304 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF314 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-1-BOX⟨3·0124⟩ ; lem-nat-1-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨3·0142⟩ ; lem-nat-2-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨3·1024⟩ ; lem-nat-1-BOX⟨0·2314⟩ ; lem-nat-2-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-TOFF134 ; lem-nat-2-BOX⟨0·1432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF034 ; lem-nat-2-BOX⟨1·0234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨3·0142⟩ ; lem-nat-1-BOX⟨3·0241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨0·3412⟩ ; lem-nat-0-BOX⟨1·3402⟩ ; lem-nat-0-BOX⟨3·0412⟩ ; lem-nat-1-BOX⟨1·3402⟩ ; lem-nat-1-BOX⟨2·3401⟩ ; lem-nat-1-BOX⟨3·1402⟩ ; lem-nat-2-BOX⟨3·2401⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-BOX⟨1·0324⟩ ; lem-nat-3-BOX⟨1·0324⟩ ; lem-nat-3-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨3·0124⟩ ; lem-nat-0-BOX⟨3·0142⟩ ; lem-nat-0-BOX⟨3·1042⟩ ; lem-nat-0-BOX⟨3·1402⟩ ; lem-nat-1-BOX⟨3·1024⟩ ; lem-nat-1-BOX⟨3·1042⟩ ; lem-nat-1-BOX⟨3·2014⟩ ; lem-nat-1-BOX⟨3·2041⟩ ; lem-nat-1-BOX⟨3·2401⟩ ; lem-nat-2-BOX⟨2·1043⟩ ; lem-nat-2-BOX⟨2·3401⟩)
-- boxify-2: 334 steps
lem-boxify-2 : Ws → ⟪ (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (run b41)))))))))))))))))))))))))))))))))))))))))
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
       at 0 1 (Bx3-0124 ∷ []) (sym (lem-boxify-2-nf-of-rhs c4)) ▸ done


-- T-beta @2332: 7 steps
lem-T-beta-at2332 : Ws → ⟪ (Toff013 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Toff013 ∷ []) ⟫ʷ
lem-T-beta-at2332 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ Toff012 ∷ []) (lem-T-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- T-beta @243243: 7 steps
lem-T-beta-at243243 : Ws → ⟪ (Toff014 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Toff014 ∷ []) ⟫ʷ
lem-T-beta-at243243 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Toff014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Toff013 ∷ []) (lem-T-beta-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- T-beta @12243143: 7 steps
lem-T-beta-at12243143 : Ws → ⟪ (Toff024 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Toff024 ∷ []) ⟫ʷ
lem-T-beta-at12243143 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Toff024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Toff014 ∷ []) (lem-T-beta-at243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- T-beta @13243142: 7 steps
lem-T-beta-at13243142 : Ws → ⟪ (Toff034 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Toff034 ∷ []) ⟫ʷ
lem-T-beta-at13243142 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Toff034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 (lit c4)) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 (Bx0-2413 ∷ Toff024 ∷ []) (lem-T-beta-at12243143 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF043: 11 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF043 : Ws → ⟪ (Bx0-1234 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ Toff034 ∷ []) (Toff034 ∷ Bx0-3124 ∷ [])
  b0 = at 1 1 (Toff034 ∷ []) (wp0284 c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (Toff034 ∷ Bx0-3412 ∷ []) (sym (lem-T-beta-at13243142 c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸ done

  b1 : Chain (Toff034 ∷ Bx0-3124 ∷ []) (Toff034 ∷ Bx0-1234 ∷ [])
  b1 = at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (Toff034 ∷ []) (wp0284 c4) ▸ done


-- boxify-3 [nf of rhs]: 0 steps
lem-boxify-3-nf-of-rhs : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-3-nf-of-rhs c4 = refl

-- auto BOX(0;1234) | TOFF043 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at0110 : Ws → ⟪ (Bx1-0234 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ Toff134 ∷ []) (Toff134 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 (lit c4)) ▸
       at 1 2 (Toff034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF043 c4) ▸
       at 0 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF043 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at021021 : Ws → ⟪ (Bx2-0134 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ Toff234 ∷ []) (Toff234 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 (lit c4)) ▸
       at 1 2 (Toff134 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at0110 c4) ▸
       at 0 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 (lit c4)) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF043 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ Toff324 ∷ []) (Toff324 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 (lit c4)) ▸
       at 1 2 (Toff234 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at021021 c4) ▸
       at 0 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 (lit c4)) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- boxify-3: 3 steps
lem-boxify-3 : Ws → ⟪ (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-3 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 1 2 (Toff324 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at03102132 c4) ▸
       at 0 2 [] (wl0616 (lit c4)) ▸
       at 0 1 (Bx3-0124 ∷ []) (sym (lem-boxify-3-nf-of-rhs c4)) ▸ done


-- auto BOX(0;1234) | CCZ304: 11 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ304 : Ws → ⟪ (Bx0-1234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ304 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx0-3124 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ []) (wp0025 c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (CCZ034 ∷ Bx0-3412 ∷ []) (sym (lem-Cz-beta-at13243142 c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Bx0-3124 ∷ []) (CCZ034 ∷ Bx0-1234 ∷ [])
  b1 = at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ034 ∷ []) (wp0025 c4) ▸ done


-- Cz-beta @122331: 7 steps
lem-Cz-beta-at122331 : Ws → ⟪ (CCZ023 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-Cz-beta-at122331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ CCZ013 ∷ []) (lem-Cz-beta-at2332 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ302: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ302 : Ws → ⟪ (Bx0-1234 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ302 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ []) (wl0242 (lit c4)) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (CCZ023 ∷ Bx0-2314 ∷ []) (sym (lem-Cz-beta-at122331 c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (CCZ023 ∷ []) (wl0242 (lit c4)) ▸ done


-- T312-beta @2442: 8 steps
lem-T312-beta-at2442 : Ws → ⟪ (Toff314 ∷ Bx0-1432 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at2442 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Bx0-1432 ∷ Toff314 ∷ []) (Bx0-1432 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 (lit c4)) ▸
       at 1 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-T312-beta-at243243 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | CCZ342 @031031: 7 steps
lem-auto-CCZ012-∣-CCZ342-at031031 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at031031 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at03102132 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(3;0412): 35 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Bx0-1234 ∷ Bx3-0412 ∷ []) (Toff314 ∷ Toff314 ∷ Bx0-1342 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 1 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-beta-T-at0314213042 c4) ▸
       at 0 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
       at 1 1 (Toff314 ∷ []) (wl0267 (lit c4)) ▸
       at 3 1 (Toff314 ∷ []) (wl0267 (lit c4)) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 2 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸ done

  b1 : Chain (Toff314 ∷ Toff314 ∷ Bx0-1342 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (Toff314 ∷ CCZ124 ∷ CCZ023 ∷ Toff314 ∷ Toff314 ∷ Bx0-1234 ∷ Toff314 ∷ CCZ023 ∷ [])
  b1 = at 2 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 1 3 (Bx0-1432 ∷ CCZ124 ∷ []) (lem-T312-beta-at2442 c4) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 1 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ142 c4) ▸
       at 2 2 (CCZ023 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ302 c4) ▸
       at 3 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸ done

  b2 : Chain (Toff314 ∷ CCZ124 ∷ CCZ023 ∷ Toff314 ∷ Toff314 ∷ Bx0-1234 ∷ Toff314 ∷ CCZ023 ∷ []) (Toff314 ∷ CCZ124 ∷ CCZ023 ∷ Toff314 ∷ Bx0-1324 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b2 = at 4 1 (Toff314 ∷ []) (wl0267 (lit c4)) ▸
       at 6 1 (Toff314 ∷ []) (wl0267 (lit c4)) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 5 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 5 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 4 3 (Bx0-1432 ∷ CCZ124 ∷ []) (lem-T312-beta-at2442 c4) ▸
       at 4 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 4 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸ done

  b3 : Chain (Toff314 ∷ CCZ124 ∷ CCZ023 ∷ Toff314 ∷ Bx0-1324 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Bx0-1234 ∷ [])
  b3 = at 4 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 4 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ142 c4) ▸
       at 5 2 (CCZ023 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ302 c4) ▸
       at 0 2 (CCZ124 ∷ Toff314 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ Toff314 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 2 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at031031 c4) ▸
       at 1 2 (CCZ124 ∷ Toff314 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 0 2 [] (wl0351 (lit c4)) ▸ done

  b4 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Bx0-1234 ∷ []) (Bx3-0412 ∷ Bx0-1234 ∷ [])
  b4 = at 0 4 (Bx3-4102 ∷ []) (sym (lem-beta-T-at0314213042 c4)) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸ done


-- auto BOX(0;1234) | CCZ104: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ104 : Ws → ⟪ (Bx0-1234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ104 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ []) (wp0285 c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CCZ014 ∷ Bx0-1423 ∷ []) (sym (lem-Cz-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CCZ014 ∷ []) (wp0285 c4) ▸ done


-- auto CCZ012 | CCZ342 @2332: 7 steps
lem-auto-CCZ012-∣-CCZ342-at2332 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | CCZ342 @243243: 7 steps
lem-auto-CCZ012-∣-CCZ342-at243243 : Ws → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at2332 c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CCZ012 | CCZ342 @0110243243: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0110243243 : Ws → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0110243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;0234): 27 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Bx0-1234 ∷ Bx1-0234 ∷ []) (Toff123 ∷ Bx0-2134 ∷ CCZ234 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ [])
  b0 = at 1 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸
       at 1 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 1 1 (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) (lem-beta-T-at01122330 c4) ▸
       at 0 0 (Toff123 ∷ Toff123 ∷ []) (sym (wl0618 (lit c4))) ▸
       at 2 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 2 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 1 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-T312-beta-at122331 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸ done

  b1 : Chain (Toff123 ∷ Bx0-2134 ∷ CCZ234 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) (Toff123 ∷ CCZ234 ∷ CCZ014 ∷ Toff123 ∷ Bx0-2134 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b1 = at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4) ▸
       at 2 2 (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ104 c4) ▸
       at 3 0 (Toff123 ∷ Toff123 ∷ []) (sym (wl0618 (lit c4))) ▸
       at 5 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 5 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 4 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-T312-beta-at122331 c4) ▸
       at 4 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸ done

  b2 : Chain (Toff123 ∷ CCZ234 ∷ CCZ014 ∷ Toff123 ∷ Bx0-2134 ∷ CCZ234 ∷ CCZ014 ∷ []) (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ Bx0-1234 ∷ [])
  b2 = at 4 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 4 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4) ▸
       at 5 2 (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ104 c4) ▸
       at 0 2 (CCZ234 ∷ Toff123 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ Toff123 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 2 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0110243243 c4) ▸
       at 1 2 (CCZ234 ∷ Toff123 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 0 2 [] (wl0265 (lit c4)) ▸ done

  b3 : Chain (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ Bx0-1234 ∷ []) (Bx1-0234 ∷ Bx0-1234 ∷ [])
  b3 = at 0 4 (Bx1-2304 ∷ []) (sym (lem-beta-T-at01122330 c4)) ▸
       at 0 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 0 1 (Bx1-0234 ∷ []) (lem-sym12-at011220 c4) ▸ done


-- boxify-4 [nf of rhs]: 0 steps
lem-boxify-4-nf-of-rhs : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-boxify-4-nf-of-rhs c4 = refl

-- sym34 @031031: 5 steps
lem-sym34-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-sym34-at031031 c4 = run b0
  where
  b0 : Chain (Bx3-0214 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ (lit c4)) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym34-at03102132 c4) ▸
       at 0 2 (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @0310213442: 5 steps
lem-sym12-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-sym12-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-1042 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ (lit c4)) ▸
       at 1 1 (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4) ▸
       at 0 2 (Bx3-1042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1043⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym12 @03103441: 5 steps
lem-sym12-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-sym12-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ (lit c4)) ▸
       at 1 1 (Bx3-1042 ∷ []) (lem-sym12-at0310213442 c4) ▸
       at 0 2 (Bx3-2041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1042⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @03203442: 5 steps
lem-sym23-at03203442 : Ws → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-sym23-at03203442 c4 = run b0
  where
  b0 : Chain (Bx3-1042 ∷ []) (Bx3-1402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1042⟩ (lit c4)) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @0312203441: 5 steps
lem-sym23-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-sym23-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2041⟩ (lit c4)) ▸
       at 1 1 (Bx3-1402 ∷ []) (lem-sym23-at03203442 c4) ▸
       at 0 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- TW @2332: 8 steps
lem-TW-at2332 : Ws → ⟪ (Toff103 ∷ Bx0-1324 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Bx1-0324 ∷ []) ⟫ʷ
lem-TW-at2332 c4 = run b0
  where
  b0 : Chain (Toff103 ∷ Bx0-1324 ∷ Toff103 ∷ []) (Bx0-1324 ∷ Bx1-0324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 (lit c4)) ▸
       at 1 3 (Bx0-1234 ∷ Bx1-0234 ∷ []) (lem-TW c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- TW @243243: 8 steps
lem-TW-at243243 : Ws → ⟪ (Toff104 ∷ Bx0-1423 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-TW-at243243 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ Bx0-1423 ∷ Toff104 ∷ []) (Bx0-1423 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 3 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 (lit c4)) ▸
       at 1 3 (Bx0-1324 ∷ Bx1-0324 ∷ []) (lem-TW-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- TW @0110243243: 8 steps
lem-TW-at0110243243 : Ws → ⟪ (Toff014 ∷ Bx1-0423 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-TW-at0110243243 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Bx1-0423 ∷ Toff014 ∷ []) (Bx1-0423 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 1 3 (Bx0-1423 ∷ Bx1-0423 ∷ []) (lem-TW-at243243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- TW @0210243143: 8 steps
lem-TW-at0210243143 : Ws → ⟪ (Toff024 ∷ Bx2-0413 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-TW-at0210243143 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Bx2-0413 ∷ Toff024 ∷ []) (Bx2-0413 ∷ Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 (lit c4)) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 (lit c4)) ▸
       at 1 3 (Bx1-0423 ∷ Bx0-1423 ∷ []) (lem-TW-at0110243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- TW @0310243142: 8 steps
lem-TW-at0310243142 : Ws → ⟪ (Toff034 ∷ Bx3-0412 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-TW-at0310243142 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx3-0412 ∷ Toff034 ∷ []) (Bx3-0412 ∷ Bx0-3412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 (lit c4)) ▸
       at 2 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 (lit c4)) ▸
       at 1 3 (Bx2-0413 ∷ Bx0-2413 ∷ []) (lem-TW-at0210243143 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- TW @03243042: 8 steps
lem-TW-at03243042 : Ws → ⟪ (Toff134 ∷ Bx3-1402 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Bx1-3402 ∷ []) ⟫ʷ
lem-TW-at03243042 c4 = run b0
  where
  b0 : Chain (Toff134 ∷ Bx3-1402 ∷ Toff134 ∷ []) (Bx3-1402 ∷ Bx1-3402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 (lit c4)) ▸
       at 2 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ (lit c4)) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 (lit c4)) ▸
       at 1 3 (Bx3-0412 ∷ Bx0-3412 ∷ []) (lem-TW-at0310243142 c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- TW @0312243041: 8 steps
lem-TW-at0312243041 : Ws → ⟪ (Toff234 ∷ Bx3-2401 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ
lem-TW-at0312243041 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Bx3-2401 ∷ Toff234 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 (lit c4)) ▸
       at 2 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ (lit c4)) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 (lit c4)) ▸
       at 1 3 (Bx3-1402 ∷ Bx1-3402 ∷ []) (lem-TW-at03243042 c4) ▸
       at 0 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ (lit c4)) ▸
       at 1 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @03243042: 5 steps
lem-sym23-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-sym23-at03243042 c4 = run b0
  where
  b0 : Chain (Bx3-1402 ∷ []) (Bx3-1042 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ (lit c4)) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4) ▸
       at 0 2 (Bx3-1042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0142⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @0312243041: 5 steps
lem-sym23-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-sym23-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ (lit c4)) ▸
       at 1 1 (Bx3-1042 ∷ []) (lem-sym23-at03243042 c4) ▸
       at 0 2 (Bx3-2041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1042⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @03203442: 5 steps
lem-sym34-at03203442 : Ws → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym34-at03203442 c4 = run b0
  where
  b0 : Chain (Bx3-1042 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1042⟩ (lit c4)) ▸
       at 1 1 (Bx3-0124 ∷ []) (lem-sym34-at0310213442 c4) ▸
       at 0 2 (Bx3-1024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0124⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @0312203441: 5 steps
lem-sym34-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-sym34-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-2014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2041⟩ (lit c4)) ▸
       at 1 1 (Bx3-1024 ∷ []) (lem-sym34-at03203442 c4) ▸
       at 0 2 (Bx3-2014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1024⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @032032: 5 steps
lem-sym12-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym12-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ (lit c4)) ▸
       at 1 1 (Bx3-1024 ∷ []) (lem-sym12-at03102132 c4) ▸
       at 0 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @03122031: 5 steps
lem-sym12-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym12-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ (lit c4)) ▸
       at 1 1 (Bx3-0124 ∷ []) (lem-sym12-at032032 c4) ▸
       at 0 2 (Bx3-0214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0124⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @031031: 5 steps
lem-sym23-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym23-at031031 c4 = run b0
  where
  b0 : Chain (Bx3-0214 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ (lit c4)) ▸
       at 1 1 (Bx3-0214 ∷ []) (lem-sym23-at03102132 c4) ▸
       at 0 2 (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(3;0412) @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at0110 : Ws → ⟪ (Bx1-0234 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ Bx3-1402 ∷ []) (Bx3-1402 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩ c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(3;0412) @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at021021 : Ws → ⟪ (Bx2-0134 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ (lit c4)) ▸
       at 1 2 (Bx3-1402 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at0110 c4) ▸
       at 0 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ (lit c4)) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(3;0412) @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 (Bx3-2401 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·3401⟩ (lit c4)) ▸
       at 1 2 (Bx3-2401 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at021021 c4) ▸
       at 0 2 (Bx2-3401 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·2401⟩ (lit c4)) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- TW @12243143: 8 steps
lem-TW-at12243143 : Ws → ⟪ (Toff204 ∷ Bx0-2413 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-TW-at12243143 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx0-2413 ∷ Toff204 ∷ []) (Bx0-2413 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 (lit c4)) ▸
       at 1 3 (Bx0-1423 ∷ Bx1-0423 ∷ []) (lem-TW-at243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- TW @13243142: 8 steps
lem-TW-at13243142 : Ws → ⟪ (Toff304 ∷ Bx0-3412 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-TW-at13243142 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Bx0-3412 ∷ Toff304 ∷ []) (Bx0-3412 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 (lit c4)) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 (lit c4)) ▸
       at 1 3 (Bx0-2413 ∷ Bx2-0413 ∷ []) (lem-TW-at12243143 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- TW @0113243042: 8 steps
lem-TW-at0113243042 : Ws → ⟪ (Toff314 ∷ Bx1-3402 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Bx3-1402 ∷ []) ⟫ʷ
lem-TW-at0113243042 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Bx1-3402 ∷ Toff314 ∷ []) (Bx1-3402 ∷ Bx3-1402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 (lit c4)) ▸
       at 2 2 (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ (lit c4)) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 (lit c4)) ▸
       at 1 3 (Bx0-3412 ∷ Bx3-0412 ∷ []) (lem-TW-at13243142 c4) ▸
       at 0 2 (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- TW @0213243041: 8 steps
lem-TW-at0213243041 : Ws → ⟪ (Toff324 ∷ Bx2-3401 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ
lem-TW-at0213243041 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Bx2-3401 ∷ Toff324 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 (lit c4)) ▸
       at 2 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ (lit c4)) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 (lit c4)) ▸
       at 1 3 (Bx1-3402 ∷ Bx3-1402 ∷ []) (lem-TW-at0113243042 c4) ▸
       at 0 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ (lit c4)) ▸
       at 1 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at2332 : Ws → ⟪ (Bx0-1324 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩ c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at243243 : Ws → ⟪ (Bx0-1423 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx1-0324 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at2332 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @12243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at12243143 : Ws → ⟪ (Bx0-2413 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @13243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at13243142 : Ws → ⟪ (Bx0-3412 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Bx0-3412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 2 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ Bx0-2413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at12243143 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @0113243042: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0113243042 : Ws → ⟪ (Bx1-3402 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Bx1-3402 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0113243042 c4 = run b0
  where
  b0 : Chain (Bx1-3402 ∷ Bx3-1402 ∷ []) (Bx3-1402 ∷ Bx1-3402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ (lit c4)) ▸
       at 2 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ Bx0-3412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at13243142 c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @0213243041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0213243041 c4 = run b0
  where
  b0 : Chain (Bx2-3401 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ (lit c4)) ▸
       at 2 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ (lit c4)) ▸
       at 1 2 (Bx3-1402 ∷ Bx1-3402 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0113243042 c4) ▸
       at 0 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ (lit c4)) ▸
       at 1 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0110243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 (Bx0-2413 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0210243143 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @03243042: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at03243042 : Ws → ⟪ (Bx3-1402 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Bx3-1402 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at03243042 c4 = run b0
  where
  b0 : Chain (Bx3-1402 ∷ Bx1-3402 ∷ []) (Bx1-3402 ∷ Bx3-1402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ (lit c4)) ▸
       at 2 2 (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ (lit c4)) ▸
       at 1 2 (Bx0-3412 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0310243142 c4) ▸
       at 0 2 (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @0312243041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ (lit c4)) ▸
       at 2 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ (lit c4)) ▸
       at 1 2 (Bx1-3402 ∷ Bx3-1402 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at03243042 c4) ▸
       at 0 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ (lit c4)) ▸
       at 1 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- beta-inv @03243042: 5 steps
lem-beta-inv-at03243042 : Ws → ⟪ (Bx3-1402 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03243042 c4 = run b0
  where
  b0 : Chain (Bx3-1402 ∷ Bx3-1402 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ (lit c4)) ▸
       at 2 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at0310243142 c4) ▸
       at 0 2 [] (wl0002 (lit c4)) ▸ done


-- beta-inv @0312243041: 5 steps
lem-beta-inv-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ Bx3-2401 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ (lit c4)) ▸
       at 2 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at03243042 c4) ▸
       at 0 2 [] (wl0001 (lit c4)) ▸ done


-- boxify-4: 31 steps
lem-boxify-4 : Ws → ⟪ (Toff324 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-boxify-4 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Toff324 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-2401 ∷ Bx2-3401 ∷ Toff324 ∷ [])
  b0 = at 2 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0620 (lit c4))) ▸
       at 3 1 (Toff234 ∷ []) (wl0621 (lit c4)) ▸
       at 5 1 (Toff234 ∷ []) (wl0621 (lit c4)) ▸
       at 4 1 (Bx3-0214 ∷ []) (lem-sym23-at03102132 c4) ▸
       at 4 1 (Bx3-0241 ∷ []) (lem-sym34-at031031 c4) ▸
       at 4 1 (Bx3-2041 ∷ []) (lem-sym12-at03103441 c4) ▸
       at 4 1 (Bx3-2401 ∷ []) (lem-sym23-at0312203441 c4) ▸
       at 3 3 (Bx3-2401 ∷ Bx2-3401 ∷ []) (lem-TW-at0312243041 c4) ▸ done

  b1 : Chain (Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-2401 ∷ Bx2-3401 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Bx2-3401 ∷ Toff324 ∷ Bx3-0124 ∷ [])
  b1 = at 3 1 (Bx3-2041 ∷ []) (lem-sym23-at0312243041 c4) ▸
       at 3 1 (Bx3-2014 ∷ []) (lem-sym34-at0312203441 c4) ▸
       at 3 1 (Bx3-0214 ∷ []) (lem-sym12-at03122031 c4) ▸
       at 3 1 (Bx3-0124 ∷ []) (lem-sym23-at031031 c4) ▸
       at 3 2 (Bx2-3401 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 c4) ▸
       at 4 2 (Toff324 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at03102132 c4) ▸
       at 3 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 4 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸ done

  b2 : Chain (Toff324 ∷ Toff234 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Bx2-3401 ∷ Toff324 ∷ Bx3-0124 ∷ []) (Toff324 ∷ Toff234 ∷ Toff234 ∷ Toff324 ∷ Bx2-3401 ∷ Bx3-2401 ∷ Bx3-2401 ∷ [])
  b2 = at 6 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 4 3 (Bx2-3401 ∷ Bx3-2401 ∷ []) (lem-TW-at0213243041 c4) ▸
       at 4 2 (Bx3-2401 ∷ Bx2-3401 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0213243041 c4) ▸
       at 4 2 (Bx2-3401 ∷ Bx3-2401 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0312243041 c4) ▸
       at 6 1 (Bx3-0214 ∷ []) (lem-sym23-at03102132 c4) ▸
       at 6 1 (Bx3-0241 ∷ []) (lem-sym34-at031031 c4) ▸
       at 6 1 (Bx3-2041 ∷ []) (lem-sym12-at03103441 c4) ▸
       at 6 1 (Bx3-2401 ∷ []) (lem-sym23-at0312203441 c4) ▸ done

  b3 : Chain (Toff324 ∷ Toff234 ∷ Toff234 ∷ Toff324 ∷ Bx2-3401 ∷ Bx3-2401 ∷ Bx3-2401 ∷ []) (Bx2-0134 ∷ [])
  b3 = at 5 2 [] (lem-beta-inv-at0312243041 c4) ▸
       at 4 1 (Bx2-3041 ∷ []) (lem-sym23-at0213243041 c4) ▸
       at 4 1 (Bx2-3014 ∷ []) (lem-sym34-at0213203441 c4) ▸
       at 4 1 (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4) ▸
       at 4 1 (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4) ▸
       at 0 4 [] (wl0623 (lit c4)) ▸
       at 0 1 (Bx2-0134 ∷ []) (sym (lem-boxify-4-nf-of-rhs c4)) ▸ done


-- auto CCZ012 | CCZ342 @0210243143: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0210243143 : Ws → ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0210243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0110243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | CCZ342 @0310243142: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0310243142 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0310243142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0210243143 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(3;1204): 15 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ Bx3-1204 ∷ []) (Toff312 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ Bx0-1234 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-beta-T-at0330 c4) ▸
       at 0 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 1 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124 c4) ▸
       at 2 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ304 c4) ▸
       at 3 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 4 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 4 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124 c4) ▸ done

  b1 : Chain (Toff312 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ Bx0-1234 ∷ CCZ034 ∷ []) (Bx3-1204 ∷ Bx0-1234 ∷ [])
  b1 = at 5 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ304 c4) ▸
       at 0 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0624 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0624 (lit c4))) ▸
       at 2 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0310243142 c4) ▸
       at 1 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0624 (lit c4))) ▸
       at 0 2 [] (wl0351 (lit c4)) ▸
       at 0 4 (Bx3-1204 ∷ []) (sym (lem-beta-T-at0330 c4)) ▸ done


-- boxify-5 [nf of rhs]: 0 steps
lem-boxify-5-nf-of-rhs : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-5-nf-of-rhs c4 = refl
