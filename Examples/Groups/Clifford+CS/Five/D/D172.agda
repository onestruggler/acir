{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D172 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0008 ; wl0011 ; wl0015 ; wl0017 ; wl0037 ; wl0038 ; wl0100 ; wl0103 ; wl0111 ; wl0113 ; wl0132 ; wl0160 ; wl0164 ; wl0212 ; wl0283 ; wl0332 ; wl0648 ; wl0649 ; wl0659 ; wl0661 ; wl0662 ; wl0663 ; wl0664 ; wl0665 ; wl0666 ; wl0667 ; wl0668 ; wl0669 ; wl0670 ; wl0671 ; wl0672 ; wl0673 ; wl0674 ; wl0675 ; wl0676 ; wl0677 ; wl0678 ; wl0679 ; wl0680 ; wl0681 ; wl0682 ; wl0683 ; wl0684 ; wl0685 ; wl0686 ; wl0687 ; wl0688 ; wl0689 ; wl0690 ; wl0691 ; wl0692 ; wl0693 ; wl0694 ; wl0695 ; wl0696 ; wl0697 ; wl0698 ; wl0699 ; wl0700 ; wl0701 ; wl0702 ; wl0703 ; wl0704 ; wl0705 ; wl0706 ; wl0707 ; wl0708 ; wl0709 ; wl0710 ; wl0711 ; wl0712 ; wl0713 ; wp0296 ; wp0300 ; wp0301 ; wp0302 ; wp0303 ; wp0304 ; wp0305 ; wp0306 ; wp0307 ; wp0308 ; wp0309 ; wp0310 ; wp0311 ; wp0312 ; wp0313 ; wp0314 ; wp0315 ; wp0316 ; wp0317 ; wp0318 ; wp0319 ; wp0320 ; wp0321 ; wp0322 ; wp0323 ; wp0324 ; wp0325 ; wp0326 ; wp0327 ; wp0328 ; wp0329 ; wp0330 ; wp0331 ; wp0332 ; wp0333 ; wp0334 ; wp0335 ; wp0336 ; wp0337 ; wp0338 ; wp0339)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at243243 ; lem-sym12-at0214203143 ; lem-sym12-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym12-at0210243143 ; lem-sym12-at243243 ; lem-sym23-at021021 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143 ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym23-at243243 ; lem-sym23-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-CS12-beta-at021021 ; lem-X1-beta-at0214203143 ; lem-X1-beta-at14213243 ; lem-auto-CS01-∣-BOX⟨2·3041⟩ ; lem-beta-T-at2442 ; lem-sym23-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at02102331 ; lem-sym12-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-beta-T-at233442 ; lem-beta-T-at3443 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym23-at233442 ; lem-sym23-at2442 ; lem-sym34-at0210243143 ; lem-sym34-at02102441 ; lem-sym34-at243243 ; lem-sym34-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-CS12-beta-at0220)
open import Examples.Groups.Clifford+CS.Five.D.D166 using (lem-sym12-at122441 ; lem-sym12-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-auto-CCZ012-∣-BOX⟨3·0412⟩ ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 ; lem-auto-CK01-∣-BOX⟨1·2034⟩ ; lem-auto-CS01-∣-BOX⟨1·2034⟩ ; lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 ; lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ013 ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-1-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-1-BOX⟨0·1342⟩ ; lem-nat-1-BOX⟨0·2143⟩ ; lem-nat-1-BOX⟨0·2341⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-1-BOX⟨3·0412⟩ ; lem-nat-1-CS04 ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-BOX⟨0·4123⟩ ; lem-nat-2-BOX⟨0·4132⟩ ; lem-nat-2-BOX⟨1·0432⟩ ; lem-nat-2-BOX⟨3·0421⟩ ; lem-nat-2-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-2-BOX⟨1·0234⟩ ; lem-nat-2-CS04 ; lem-nat-3-CS04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨2·0134⟩ ; lem-nat-0-BOX⟨2·1034⟩ ; lem-nat-0-BOX⟨2·3104⟩ ; lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-CS03 ; lem-nat-3-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·2431⟩ ; lem-nat-0-BOX⟨1·2430⟩ ; lem-nat-0-BOX⟨2·3014⟩ ; lem-nat-0-BOX⟨2·3041⟩ ; lem-nat-0-BOX⟨2·3140⟩ ; lem-nat-1-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨0·2431⟩ ; lem-nat-1-BOX⟨1·3240⟩ ; lem-nat-1-BOX⟨2·3140⟩ ; lem-nat-3-BOX⟨1·2340⟩ ; lem-nat-3-BOX⟨1·2430⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·1432⟩ ; lem-nat-0-BOX⟨1·0432⟩ ; lem-nat-1-BOX⟨1·3204⟩ ; lem-nat-1-BOX⟨2·3104⟩ ; lem-nat-2-BOX⟨1·0423⟩ ; lem-nat-2-BOX⟨1·2340⟩ ; lem-nat-2-BOX⟨1·3240⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨1·2403⟩ ; lem-nat-1-BOX⟨2·1403⟩ ; lem-nat-2-BOX⟨1·2304⟩ ; lem-nat-2-BOX⟨1·3204⟩ ; lem-nat-3-BOX⟨1·2304⟩ ; lem-nat-3-BOX⟨1·2403⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨0·2413⟩ ; lem-nat-0-BOX⟨1·2403⟩ ; lem-nat-1-BOX⟨3·0421⟩ ; lem-nat-2-BOX⟨1·0324⟩ ; lem-nat-2-BOX⟨2·0431⟩ ; lem-nat-3-BOX⟨1·0324⟩ ; lem-nat-3-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-BOX⟨0·4132⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-comm-CCZ013-CK42 ; lem-comm-CCZ013-CS24 ; lem-comm-CCZ123-CK40 ; lem-comm-CCZ123-CS04 ; lem-comm-CK40-CCZ123 ; lem-comm-CK41-CCZ023 ; lem-comm-CK41-TOFF023 ; lem-comm-CK41-TOFF203 ; lem-comm-CK42-CCZ013 ; lem-comm-CK42-TOFF013 ; lem-nat-0-BOX⟨2·0431⟩ ; lem-nat-0-BOX⟨2·1430⟩ ; lem-nat-0-CK40 ; lem-nat-0-CK41 ; lem-nat-1-BOX⟨0·4231⟩ ; lem-nat-1-BOX⟨1·2430⟩ ; lem-nat-1-BOX⟨2·1430⟩ ; lem-nat-1-CK10 ; lem-nat-1-CK20 ; lem-nat-1-CK40 ; lem-nat-2-CK20 ; lem-nat-2-CK30 ; lem-nat-2-CK40 ; lem-nat-3-CK30 ; lem-nat-3-CK40)
-- auto CCZ012 | BOX(3;0412) @122331: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 : Ws → ⟪ (CCZ023 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 2 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- X1-beta @142142: 8 steps
lem-X1-beta-at142142 : Ws → ⟪ (X4 ∷ Bx0-4132 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-4132 ∷ []) ⟫ʷ
lem-X1-beta-at142142 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx0-4132 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4132 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 2 2 (Bx0-4123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4132⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 1 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 1 2 (Bx0-4132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4123⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0412) @1221: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1221 : Ws → ⟪ (CCZ012 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0421 ∷ []) (Bx3-0421 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0412) @132132: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at132132 : Ws → ⟪ (CCZ013 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx2-0431 ∷ []) (Bx2-0431 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (Bx3-0421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0431⟩ (lit c4)) ▸
       at 1 2 (Bx3-0421 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1221 c4) ▸
       at 0 2 (Bx2-0431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0421⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto S0 | BOX(1;2034) @04102142: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at04102142 : Ws → ⟪ (S4 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at04102142 c4 = run b0
  where
  b0 : Chain (S4 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 2 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0412) @01122330: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 : Ws → ⟪ (CCZ123 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 2 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F4 iI^0|CS12^1: 24 steps
lem-F4-iIᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-iIᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 3 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 1 2 (Bx0-1423 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 4 (X4 ∷ S4 ∷ X4 ∷ CCZ123 ∷ []) (wl0662 (lit c4)) ▸
       at 4 2 [] (wl0212 (lit c4)) ▸
       at 1 4 (Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0663 (lit c4))) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b2 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0664 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0663 (lit c4))) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0665 (lit c4))) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- X1-beta @1441: 8 steps
lem-X1-beta-at1441 : Ws → ⟪ (X4 ∷ Bx0-4231 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-4231 ∷ []) ⟫ʷ
lem-X1-beta-at1441 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx0-4231 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4231 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Bx0-4132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4231⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 1 3 (CCZ123 ∷ Bx0-4132 ∷ []) (lem-X1-beta-at142142 c4) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 1 2 (Bx0-4231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4132⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0412) @01132032: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01132032 : Ws → ⟪ (CCZ013 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01132032 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx2-1430 ∷ []) (Bx2-1430 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 (lit c4))) ▸
       at 2 2 (Bx2-0431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1430⟩ (lit c4)) ▸
       at 1 2 (Bx2-0431 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at132132 c4) ▸
       at 0 2 (Bx2-1430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0431⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0412) @02132031: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132031 : Ws → ⟪ (CCZ023 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132031 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Bx1-2430 ∷ []) (Bx1-2430 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 2 2 (Bx2-1430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2430⟩ (lit c4)) ▸
       at 1 2 (Bx2-1430 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01132032 c4) ▸
       at 0 2 (Bx1-2430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1430⟩ (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0412) @02132130: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 : Ws → ⟪ (CCZ123 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 2 2 (Bx1-2430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Bx1-2430 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132031 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto S0 | BOX(1;2034) @041041: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at041041 : Ws → ⟪ (S4 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at041041 c4 = run b0
  where
  b0 : Chain (S4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Bx0-1432 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at04102142 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 iI^0|CS23^1: 24 steps
lem-F4-iIᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-iIᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 1 2 (Bx0-2431 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at041041 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 4 (X4 ∷ S4 ∷ X4 ∷ CCZ123 ∷ []) (wl0662 (lit c4)) ▸
       at 4 2 [] (wl0212 (lit c4)) ▸
       at 1 4 (Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0666 (lit c4))) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b2 = at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0667 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0666 (lit c4))) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0668 (lit c4))) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;1034): 3 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩ : Ws → ⟪ (CS01 ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-1034 ∷ []) (Bx2-1034 ∷ CS01 ∷ [])
  b0 = at 0 1 (CS01 ∷ []) (wl0332 (lit c4)) ▸
       at 0 2 (Bx2-1034 ∷ CS01 ∷ []) (lem-CS12-beta-at0220 c4) ▸
       at 1 1 (CS01 ∷ []) (wl0332 (lit c4)) ▸ done


-- auto CS01 | BOX(2;1034) @0110: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at0110 : Ws → ⟪ (CS01 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at0110 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 (Bx2-1034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 2 (Bx2-1034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩ c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | BOX(2;1034) @021021: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at021021 : Ws → ⟪ (CS02 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at021021 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 2 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 (Bx2-0134 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at0110 c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | BOX(2;1034) @03102132: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at03102132 : Ws → ⟪ (CS03 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 2 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at021021 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CS01 | BOX(2;1034) @0410213243: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at0410213243 : Ws → ⟪ (CS04 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4)) ▸
       at 2 2 (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx1-0324 ∷ CS03 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at03102132 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CS01 | BOX(2;1034) @04103143: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04103143 : Ws → ⟪ (CS04 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04103143 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at0410213243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 S0^0|CS01^1: 24 steps
lem-F4-S0ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CS04 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 2 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 3 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 1 2 (Bx2-0413 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at04103143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CS04 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 4 2 (X4 ∷ CCZ013 ∷ []) (wp0296 c4) ▸
       at 1 4 (X4 ∷ CS04 ∷ X4 ∷ CCZ013 ∷ []) (wp0300 c4) ▸
       at 4 2 [] (wl0659 (lit c4)) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0301 c4)) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b2 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0302 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0301 c4)) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0303 c4)) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;1034) @04102142: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04102142 : Ws → ⟪ (CS04 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04102142 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 2 2 (Bx1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0432⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at0410213243 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2034) @0110: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0110 : Ws → ⟪ (CS01 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0110 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2034) @021021: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at021021 : Ws → ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at021021 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 2 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (Bx0-2134 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at0110 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2034) @03102132: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at03102132 : Ws → ⟪ (CS03 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at021021 c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2034) @0410213243: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0410213243 : Ws → ⟪ (CS04 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ CS03 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at03102132 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- F4 S0^0|CS12^1: 26 steps
lem-F4-S0ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CS04 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 3 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 1 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CS04 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸
       at 2 2 (CS04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CS04 (lit c4)) ▸
       at 3 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸ done

  b2 : Chain (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b2 = at 4 2 [] (wl0212 (lit c4)) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0304 c4)) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0305 c4)) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0304 c4)) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0306 c4)) ▸ done

  b3 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b3 = at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(1;2034) @04102142: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at04102142 : Ws → ⟪ (CS04 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at04102142 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2034) @041041: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at041041 : Ws → ⟪ (CS04 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at041041 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 2 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Bx0-1432 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at04102142 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 S0^0|CS23^1: 26 steps
lem-F4-S0ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CS04 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 1 2 (Bx0-2431 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at041041 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CS04 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸
       at 2 2 (CS04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CS04 (lit c4)) ▸
       at 3 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸ done

  b2 : Chain (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b2 = at 4 2 [] (wl0212 (lit c4)) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0307 c4)) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0308 c4)) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0307 c4)) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0309 c4)) ▸ done

  b3 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b3 = at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;3014): 5 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩ : Ws → ⟪ (CS01 ∷ Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-3014 ∷ []) (Bx2-3014 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4) ▸
       at 1 1 (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4) ▸
       at 0 2 (Bx2-0134 ∷ CS01 ∷ []) (lem-CS12-beta-at021021 c4) ▸
       at 0 1 (Bx2-0314 ∷ []) (lem-sym23-at021021 c4) ▸
       at 0 1 (Bx2-3014 ∷ []) (lem-sym12-at02102331 c4) ▸ done


-- auto CS01 | BOX(2;3014) @0110: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0110 : Ws → ⟪ (CS01 ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0110 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-3104 ∷ []) (Bx2-3104 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 (Bx2-3014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3104⟩ (lit c4)) ▸
       at 1 2 (Bx2-3014 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩ c4) ▸
       at 0 2 (Bx2-3104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3014⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3014) @021021: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at021021 : Ws → ⟪ (CS02 ∷ Bx1-3204 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3204 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at021021 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx1-3204 ∷ []) (Bx1-3204 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 2 2 (Bx2-3104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3204⟩ (lit c4)) ▸
       at 1 2 (Bx2-3104 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0110 c4) ▸
       at 0 2 (Bx1-3204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3104⟩ (lit c4)) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3014) @03102132: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at03102132 : Ws → ⟪ (CS03 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 2 2 (Bx1-3204 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2304⟩ (lit c4)) ▸
       at 1 2 (Bx1-3204 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at021021 c4) ▸
       at 0 2 (Bx1-2304 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3204⟩ (lit c4)) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3014) @0410213243: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0410213243 : Ws → ⟪ (CS04 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4)) ▸
       at 2 2 (Bx1-2304 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2403⟩ (lit c4)) ▸
       at 1 2 (Bx1-2304 ∷ CS03 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at03102132 c4) ▸
       at 0 2 (Bx1-2403 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2304⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3014) @04103143: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at04103143 : Ws → ⟪ (CS04 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at04103143 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 2 2 (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ (lit c4)) ▸
       at 1 2 (Bx1-2403 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0410213243 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3014) @043043: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at043043 : Ws → ⟪ (CS14 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at043043 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS14 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 2 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx2-1403 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at04103143 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ (lit c4)) ▸
       at 1 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F4 S1^0|CS01^1: 24 steps
lem-F4-S1ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CS14 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 2 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 3 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 1 2 (Bx2-0413 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at043043 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CS14 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 4 2 (X4 ∷ CCZ013 ∷ []) (wp0296 c4) ▸
       at 1 4 (X4 ∷ CS14 ∷ X4 ∷ CCZ013 ∷ []) (wp0310 c4) ▸
       at 4 2 [] (wl0659 (lit c4)) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0669 (lit c4))) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b2 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0311 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0669 (lit c4))) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0312 c4)) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(1;2034) @04203243: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at04203243 : Ws → ⟪ (CS14 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS14 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | BOX(2;1034) @04203243: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04203243 : Ws → ⟪ (CS14 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 2 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at0410213243 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F4 S1^0|CS12^1: 24 steps
lem-F4-S1ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CS14 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 3 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 1 2 (Bx0-1423 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at04203243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CS14 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 4 (X4 ∷ CS14 ∷ X4 ∷ CCZ123 ∷ []) (wl0670 (lit c4)) ▸
       at 4 2 [] (wl0212 (lit c4)) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0671 (lit c4))) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b2 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0672 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0671 (lit c4))) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0673 (lit c4))) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;1034) @042042: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at042042 : Ws → ⟪ (CS14 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at042042 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS14 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 2 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (Bx1-0432 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at04102142 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ (lit c4)) ▸
       at 1 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3041) @0110: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0110 : Ws → ⟪ (CS01 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0110 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-3140 ∷ []) (Bx2-3140 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 (Bx2-3041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3140⟩ (lit c4)) ▸
       at 1 2 (Bx2-3041 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩ c4) ▸
       at 0 2 (Bx2-3140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3041⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3041) @021021: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at021021 : Ws → ⟪ (CS02 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at021021 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx1-3240 ∷ []) (Bx1-3240 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 2 2 (Bx2-3140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3240⟩ (lit c4)) ▸
       at 1 2 (Bx2-3140 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0110 c4) ▸
       at 0 2 (Bx1-3240 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3140⟩ (lit c4)) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3041) @03102132: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at03102132 : Ws → ⟪ (CS03 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Bx1-2340 ∷ []) (Bx1-2340 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 2 2 (Bx1-3240 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2340⟩ (lit c4)) ▸
       at 1 2 (Bx1-3240 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at021021 c4) ▸
       at 0 2 (Bx1-2340 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3240⟩ (lit c4)) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3041) @0410213243: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0410213243 : Ws → ⟪ (CS04 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx1-2430 ∷ []) (Bx1-2430 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4)) ▸
       at 2 2 (Bx1-2340 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2430⟩ (lit c4)) ▸
       at 1 2 (Bx1-2340 ∷ CS03 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at03102132 c4) ▸
       at 0 2 (Bx1-2430 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2340⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3041) @04203243: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at04203243 : Ws → ⟪ (CS14 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS14 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 2 2 (Bx1-2430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Bx1-2430 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0410213243 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ (lit c4)) ▸
       at 1 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F4 S1^0|CS23^1: 24 steps
lem-F4-S1ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CS14 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 1 2 (Bx0-2431 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at04203243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CS14 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 4 (X4 ∷ CS14 ∷ X4 ∷ CCZ123 ∷ []) (wl0670 (lit c4)) ▸
       at 4 2 [] (wl0212 (lit c4)) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0674 (lit c4))) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b2 = at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0675 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0674 (lit c4))) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0676 (lit c4))) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(1;2034) @0412203143: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0412203143 : Ws → ⟪ (CS24 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS24 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at04203243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 S2^0|CS01^1: 26 steps
lem-F4-S2ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CS24 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 2 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 3 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 1 2 (Bx2-0413 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at0412203143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CS24 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 4 2 (X4 ∷ CCZ013 ∷ []) (wp0296 c4) ▸
       at 1 2 (X4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X)) ▸
       at 2 2 (CS24 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS24 (lit c4)) ▸
       at 3 2 (X4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X)) ▸ done

  b2 : Chain (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b2 = at 4 2 [] (wl0659 (lit c4)) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0313 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0314 c4)) ▸ done

  b3 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b3 = at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;3014) @04203243: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at04203243 : Ws → ⟪ (CS14 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CS14 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 2 2 (Bx1-2403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (Bx1-2403 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0410213243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2403⟩ (lit c4)) ▸
       at 1 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3014) @0412203143: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0412203143 : Ws → ⟪ (CS24 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS24 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 2 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-2413 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at04203243 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3041) @0412203143: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0412203143 : Ws → ⟪ (CS24 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS24 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 2 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (Bx0-2431 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at04203243 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 S2^0|CS12^1: 24 steps
lem-F4-S2ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CS24 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 3 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 1 2 (Bx0-1423 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0412203143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CS24 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 4 (X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ []) (wl0678 (lit c4)) ▸
       at 4 2 [] (wl0212 (lit c4)) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0679 (lit c4))) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b2 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0680 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0681 (lit c4))) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;1034) @04122041: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04122041 : Ws → ⟪ (CS24 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04122041 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS24 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 2 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Bx0-1432 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at042042 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 S2^0|CS23^1: 24 steps
lem-F4-S2ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CS24 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 1 2 (Bx0-2431 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at04122041 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CS24 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 4 (X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ []) (wl0678 (lit c4)) ▸
       at 4 2 [] (wl0212 (lit c4)) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0682 (lit c4))) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b2 = at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0683 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0682 (lit c4))) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0684 (lit c4))) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;3041) @0413203142: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413203142 : Ws → ⟪ (CS34 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413203142 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 2 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1432 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0412203143 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3041) @0413213042: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413213042 : Ws → ⟪ (CS34 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413213042 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413203142 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3041) @04133041: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at04133041 : Ws → ⟪ (CS34 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at04133041 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413213042 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 S3^0|CS01^1: 24 steps
lem-F4-S3ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 2 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 3 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 1 2 (Bx2-0413 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at04133041 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 4 2 (X4 ∷ CCZ013 ∷ []) (wp0296 c4) ▸
       at 1 4 (X4 ∷ CS34 ∷ X4 ∷ CCZ013 ∷ []) (wp0315 c4) ▸
       at 4 2 [] (wl0659 (lit c4)) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0685 (lit c4))) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b2 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0316 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0685 (lit c4))) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0317 c4)) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;3014) @0413203142: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203142 : Ws → ⟪ (CS34 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203142 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 2 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0412203143 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- F4 S3^0|CS12^1: 24 steps
lem-F4-S3ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 3 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 1 2 (Bx0-1423 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413203142 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 4 (X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ []) (wl0686 (lit c4)) ▸
       at 4 2 [] (wl0212 (lit c4)) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0687 (lit c4))) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b2 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0688 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0687 (lit c4))) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0689 (lit c4))) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;3014) @0413203241: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203241 : Ws → ⟪ (CS34 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203241 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Bx0-1432 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203142 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 S3^0|CS23^1: 24 steps
lem-F4-S3ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 1 2 (Bx0-2431 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203241 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 4 (X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ []) (wl0686 (lit c4)) ▸
       at 4 2 [] (wl0212 (lit c4)) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0690 (lit c4))) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b2 = at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0691 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0690 (lit c4))) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0692 (lit c4))) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4 K0^0|CS01^1: 18 steps
lem-F4-K0ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 0 4 (Toff204 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0318 c4)) ▸
       at 3 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 2 2 (CCZ123 ∷ CK40 ∷ []) (lem-comm-CK40-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 2 4 (Toff204 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0318 c4)) ▸
       at 5 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b1 = at 4 2 (CCZ123 ∷ CK40 ∷ []) (lem-comm-CK40-CCZ123 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0319 c4)) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0320 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b2 = at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- auto CK01 | BOX(1;2034) @0110: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0110 : Ws → ⟪ (CK10 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CK10 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0110 c4 = run b0
  where
  b0 : Chain (CK10 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CK10 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CK01 ∷ Sw01 ∷ []) (sym (wl0648 (lit c4))) ▸
       at 2 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (Bx1-2034 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 2 (CK10 ∷ Sw01 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CK01 | BOX(1;2034) @021021: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at021021 : Ws → ⟪ (CK20 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK20 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at021021 c4 = run b0
  where
  b0 : Chain (CK20 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK20 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK10 ∷ Sw12 ∷ []) (lem-nat-1-CK20 (lit c4)) ▸
       at 2 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (Bx0-2134 ∷ CK10 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at0110 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (CK20 ∷ Sw12 ∷ []) (lem-nat-1-CK10 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CK01 | BOX(1;2034) @03102132: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at03102132 : Ws → ⟪ (CK30 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CK30 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CK30 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CK30 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CK20 ∷ Sw23 ∷ []) (lem-nat-2-CK30 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CK20 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at021021 c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CK30 ∷ Sw23 ∷ []) (lem-nat-2-CK20 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CK01 | BOX(1;2034) @0410213243: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0410213243 : Ws → ⟪ (CK40 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CK30 ∷ Sw34 ∷ []) (lem-nat-3-CK40 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ CK30 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at03102132 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (CK40 ∷ Sw34 ∷ []) (lem-nat-3-CK30 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- F4 K0^0|CS12^1: 26 steps
lem-F4-K0ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 3 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 1 2 (Bx0-1423 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸
       at 2 2 (CK40 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CK40 (lit c4)) ▸
       at 3 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸ done

  b2 : Chain (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b2 = at 4 2 [] (wl0212 (lit c4)) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0321 c4)) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0322 c4)) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0321 c4)) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0323 c4)) ▸ done

  b3 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b3 = at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- auto CK01 | BOX(1;2034) @04102142: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at04102142 : Ws → ⟪ (CK40 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at04102142 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CK01 | BOX(1;2034) @041041: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at041041 : Ws → ⟪ (CK40 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at041041 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 2 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Bx0-1432 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at04102142 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 K0^0|CS23^1: 26 steps
lem-F4-K0ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 1 2 (Bx0-2431 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at041041 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸
       at 2 2 (CK40 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CK40 (lit c4)) ▸
       at 3 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸ done

  b2 : Chain (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b2 = at 4 2 [] (wl0212 (lit c4)) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0324 c4)) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0325 c4)) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0324 c4)) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0326 c4)) ▸ done

  b3 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b3 = at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4 K1^0|CS01^1: 24 steps
lem-F4-K1ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Toff203 ∷ CCZ124 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 3 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 3 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 2 2 (Toff203 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 2 (Toff203 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF203 (lit c4)) ▸
       at 0 2 (Toff203 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 4 (CCZ124 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0693 (lit c4))) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 4 2 (Toff203 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 2 (Toff203 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF203 (lit c4)) ▸
       at 2 2 (Toff203 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 4 (CCZ124 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0693 (lit c4))) ▸
       at 0 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 0 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0694 (lit c4))) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0327 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0694 (lit c4))) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0328 c4)) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- auto CK01 | BOX(1;2034) @04203243: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at04203243 : Ws → ⟪ (CK41 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CK41 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CK41 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F4 K1^0|CS12^1: 18 steps
lem-F4-K1ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ X4 ∷ CK41 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 0 4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0329 c4)) ▸
       at 3 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0329 c4)) ▸
       at 5 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ X4 ∷ CK41 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b1 = at 4 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0695 (lit c4))) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0696 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- sym23 @122441: 5 steps
lem-sym23-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym23-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @12233441: 8 steps
lem-beta-T-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ (lit c4)) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 0 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @12233441: 5 steps
lem-sym23-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-sym23-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ (lit c4)) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- F4 K1^0|CS23^1: 20 steps
lem-F4-K1ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Toff023 ∷ CCZ014 ∷ X4 ∷ CK41 ∷ Toff023 ∷ X4 ∷ CCZ014 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (Bx0-2341 ∷ []) (lem-sym23-at122441 c4) ▸
       at 3 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at12233441 c4) ▸
       at 2 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4)) ▸
       at 0 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 4 (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0330 c4)) ▸
       at 4 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ X4 ∷ CK41 ∷ Toff023 ∷ X4 ∷ CCZ014 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CK41 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 3 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4)) ▸
       at 2 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 4 (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0330 c4)) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-beta-T-at12233441 c4)) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-sym23-at12233441 c4) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0697 (lit c4))) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CK41 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 2 6 (CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- auto CK01 | BOX(1;2034) @0412203143: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0412203143 : Ws → ⟪ (CK42 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CK42 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CK42 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ CK41 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at04203243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 K2^0|CS01^1: 26 steps
lem-F4-K2ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CK42 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 2 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 3 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 1 2 (Bx2-0413 ∷ CK42 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at0412203143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CK42 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 4 2 (X4 ∷ CCZ013 ∷ []) (wp0296 c4) ▸
       at 1 2 (X4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X)) ▸
       at 2 2 (CK42 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CK42 (lit c4)) ▸
       at 3 2 (X4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X)) ▸ done

  b2 : Chain (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 4 2 [] (wl0659 (lit c4)) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0699 (lit c4))) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0331 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0699 (lit c4))) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0332 c4)) ▸ done

  b3 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b3 = at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4 K2^0|CS12^1: 24 steps
lem-F4-K2ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Toff013 ∷ CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 3 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 3 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 2 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 1 2 (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 (lit c4)) ▸
       at 0 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 1 4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0333 c4)) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 4 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 3 2 (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 (lit c4)) ▸
       at 2 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 3 4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0333 c4)) ▸
       at 0 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸
       at 0 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0700 (lit c4))) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0701 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0700 (lit c4))) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0702 (lit c4))) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- beta-T @122441: 8 steps
lem-beta-T-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 0 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 2 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 (lit c4)) ▸
       at 3 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- F4 K2^0|CS23^1: 18 steps
lem-F4-K2ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ X4 ∷ CK42 ∷ CCZ013 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 0 4 (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0334 c4)) ▸
       at 3 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 2 2 (CCZ013 ∷ CK42 ∷ []) (lem-comm-CK42-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 2 4 (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0334 c4)) ▸
       at 5 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ X4 ∷ CK42 ∷ CCZ013 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b1 = at 4 2 (CCZ013 ∷ CK42 ∷ []) (lem-comm-CK42-CCZ013 (lit c4)) ▸
       at 3 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0703 (lit c4))) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0704 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4 K3^0|CS01^1: 20 steps
lem-F4-K3ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Toff201 ∷ CCZ234 ∷ X4 ∷ CK43 ∷ Toff201 ∷ X4 ∷ CCZ234 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 3 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 2 2 (Toff201 ∷ X4 ∷ []) (sym (c₃ (Toffᵗ) (X ↑))) ▸
       at 1 2 (Toff201 ∷ CK43 ∷ []) (sym (c₃ (Toffᵗ) (CK₁₀))) ▸
       at 0 2 (Toff201 ∷ X4 ∷ []) (sym (c₃ (Toffᵗ) (X ↑))) ▸
       at 1 4 (CCZ234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0705 (lit c4))) ▸
       at 4 2 (Toff201 ∷ X4 ∷ []) (sym (c₃ (Toffᵗ) (X ↑))) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ X4 ∷ CK43 ∷ Toff201 ∷ X4 ∷ CCZ234 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CK43 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 3 2 (Toff201 ∷ CK43 ∷ []) (sym (c₃ (Toffᵗ) (CK₁₀))) ▸
       at 2 2 (Toff201 ∷ X4 ∷ []) (sym (c₃ (Toffᵗ) (X ↑))) ▸
       at 3 4 (CCZ234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0705 (lit c4))) ▸
       at 0 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0706 (lit c4))) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CK43 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 6 (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0335 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4 K3^0|CS12^1: 20 steps
lem-F4-K3ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Toff012 ∷ CCZ034 ∷ X4 ∷ CK43 ∷ Toff012 ∷ X4 ∷ CCZ034 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 3 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at3443 c4) ▸
       at 2 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 1 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 0 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 1 4 (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0336 c4)) ▸
       at 4 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ X4 ∷ CK43 ∷ Toff012 ∷ X4 ∷ CCZ034 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 3 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 2 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 3 4 (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0336 c4)) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-beta-T-at3443 c4)) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0707 (lit c4))) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 6 (CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0708 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- sym34 @122441: 5 steps
lem-sym34-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-sym34-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @12213443: 8 steps
lem-beta-T-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ (lit c4)) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at3443 c4) ▸
       at 0 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 2 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- F4 K3^0|CS23^1: 24 steps
lem-F4-K3ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Toff012 ∷ CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 3 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 3 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 2 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 1 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 0 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 1 4 (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0336 c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 4 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 3 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 2 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 3 4 (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0336 c4)) ▸
       at 0 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0709 (lit c4))) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0710 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0709 (lit c4))) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0711 (lit c4))) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4 CS01^0|iI^1: 30 steps
lem-F4-CS01ᵖ0∣iIᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣iIᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS03⁻ ∷ []) (refl) ▸
       at 12 4 (S4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0337 c4)) ▸
       at 14 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b1 = at 9 4 (S4 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0712 (lit c4))) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 6 4 (S4 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0338 c4)) ▸
       at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (S4 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0712 (lit c4))) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 4 (S4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0713 (lit c4))) ▸
       at 6 4 (S4 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0339 c4)) ▸
       at 3 4 (S4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0713 (lit c4))) ▸
       at 0 4 (S4 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0339 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b3 : Chain (S4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

