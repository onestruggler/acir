{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D172 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0008 ; wl0011 ; wl0015 ; wl0017 ; wl0037 ; wl0038 ; wl0100 ; wl0103 ; wl0111 ; wl0113 ; wl0132 ; wl0160 ; wl0164 ; wl0212 ; wl0283 ; wl0332 ; wl0648 ; wl0649 ; wl0659 ; wl0661 ; wl0662 ; wl0663 ; wl0664 ; wl0665 ; wl0666 ; wl0667 ; wl0668 ; wl0669 ; wl0670 ; wl0671 ; wl0672 ; wl0673 ; wl0674 ; wl0675 ; wl0676 ; wl0677 ; wl0678 ; wl0679 ; wl0680 ; wl0681 ; wl0682 ; wl0683 ; wl0684 ; wl0685 ; wl0686 ; wl0687 ; wl0688 ; wl0689 ; wl0690 ; wl0691 ; wl0692 ; wl0693 ; wl0694 ; wl0695 ; wl0696 ; wl0697 ; wl0698 ; wl0699 ; wl0700 ; wl0701 ; wl0702 ; wl0703 ; wl0704 ; wl0705 ; wl0706 ; wl0707 ; wl0708 ; wl0709 ; wl0710 ; wl0711 ; wl0712 ; wl0713 ; wp0296 ; wp0300 ; wp0301 ; wp0302 ; wp0303 ; wp0304 ; wp0305 ; wp0306 ; wp0307 ; wp0308 ; wp0309 ; wp0310 ; wp0311 ; wp0312 ; wp0313 ; wp0314 ; wp0315 ; wp0316 ; wp0317 ; wp0318 ; wp0319 ; wp0320 ; wp0321 ; wp0322 ; wp0323 ; wp0324 ; wp0325 ; wp0326 ; wp0327 ; wp0328 ; wp0329 ; wp0330 ; wp0331 ; wp0332 ; wp0333 ; wp0334 ; wp0335 ; wp0336 ; wp0337 ; wp0338 ; wp0339)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
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

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ013 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4))

-- auto CCZ012 | BOX(3;0412) @122331: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 : Ws → ⟪ (CCZ023 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4 = derive (CCZ023 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw23 ∷ Bx0-4132 ∷ []) (Bx0-4123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4132⟩ (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (X4 ∷ Bx0-4123 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) (wl0113 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw23 ∷ Bx0-4123 ∷ []) (Bx0-4132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4123⟩ (lit c4))

-- X1-beta @142142: 8 steps
lem-X1-beta-at142142 : Ws → ⟪ (X4 ∷ Bx0-4132 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-4132 ∷ []) ⟫ʷ
lem-X1-beta-at142142 c4 = derive (X4 ∷ Bx0-4132 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4132 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 3 (q8 c4) ∷
   rw 1 (q10 c4) ∷
   rw⁻ 0 (q11 c4) ∷
   rw 1 (q12 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw12 ∷ Bx3-0421 ∷ []) (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ012 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw12 ∷ Bx3-0412 ∷ []) (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ (lit c4))

-- auto CCZ012 | BOX(3;0412) @1221: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1221 : Ws → ⟪ (CCZ012 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1221 c4 = derive (CCZ012 ∷ Bx3-0421 ∷ []) (Bx3-0421 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   rw 2 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw23 ∷ Bx2-0431 ∷ []) (Bx3-0421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0431⟩ (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ012 ∷ Bx3-0421 ∷ []) (Bx3-0421 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1221 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw23 ∷ Bx3-0421 ∷ []) (Bx2-0431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0421⟩ (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4))

-- auto CCZ012 | BOX(3;0412) @132132: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at132132 : Ws → ⟪ (CCZ013 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at132132 c4 = derive (CCZ013 ∷ Bx2-0431 ∷ []) (Bx2-0431 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 0 (q20 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw23 ∷ Bx0-1432 ∷ []) (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (S4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw23 ∷ Bx0-1423 ∷ []) (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4))

-- auto S0 | BOX(1;2034) @04102142: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at04102142 : Ws → ⟪ (S4 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at04102142 c4 = derive (S4 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ S4 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw 1 (q24 c4) ∷
   rw 0 (q25 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ023 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 (lit c4))

-- auto CCZ012 | BOX(3;0412) @01122330: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 : Ws → ⟪ (CCZ123 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4 = derive (CCZ123 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 2 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 0 (q30 c4) ∷
   rw⁻ 1 (q31 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx0-1423 ∷ []) (Bx0-4123 ∷ []) (lem-sym12-at243243 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx0-4123 ∷ []) (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ123 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ123 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ123 ∷ []) (wl0662 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0212 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ []) (wl0663 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CS13 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS13 ∷ []) (wl0664 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CS13⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS13⁻ ∷ []) (wl0665 (lit c4))

-- F4 iI^0|CS12^1: 24 steps
lem-F4-iIᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-iIᵖ0∣CS12ᵖ1 c4 = derive (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q24 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 0 (q10 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 4 (q36 c4) ∷
   rw 1 (q37 c4) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   re 5 1 (CS13 ∷ []) ∷
   rw⁻ 2 (q40 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q39 c4) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q41 c4) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q43 : Ws → Eqn
  q43 c4 = eqn (Sw12 ∷ Bx0-4231 ∷ []) (Bx0-4132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4231⟩ (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (X4 ∷ Bx0-4132 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4132 ∷ []) (lem-X1-beta-at142142 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (Sw12 ∷ Bx0-4132 ∷ []) (Bx0-4231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4132⟩ (lit c4))

-- X1-beta @1441: 8 steps
lem-X1-beta-at1441 : Ws → ⟪ (X4 ∷ Bx0-4231 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-4231 ∷ []) ⟫ʷ
lem-X1-beta-at1441 c4 = derive (X4 ∷ Bx0-4231 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4231 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q43 c4) ∷
   rw 3 (q42 c4) ∷
   rw 1 (q44 c4) ∷
   rw⁻ 0 (q45 c4) ∷
   rw 1 (q46 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ013 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ013 ∷ []) (wl0100 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Sw01 ∷ Bx2-1430 ∷ []) (Bx2-0431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1430⟩ (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ013 ∷ Bx2-0431 ∷ []) (Bx2-0431 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at132132 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (Sw01 ∷ Bx2-0431 ∷ []) (Bx2-1430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0431⟩ (lit c4))

-- auto CCZ012 | BOX(3;0412) @01132032: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01132032 : Ws → ⟪ (CCZ013 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01132032 c4 = derive (CCZ013 ∷ Bx2-1430 ∷ []) (Bx2-1430 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw⁻ 1 (q47 c4) ∷
   rw 2 (q48 c4) ∷
   rw 1 (q49 c4) ∷
   rw 0 (q50 c4) ∷
   rw⁻ 1 (q47 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = eqn (Sw12 ∷ Bx1-2430 ∷ []) (Bx2-1430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2430⟩ (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ013 ∷ Bx2-1430 ∷ []) (Bx2-1430 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01132032 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Sw12 ∷ Bx2-1430 ∷ []) (Bx1-2430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1430⟩ (lit c4))

-- auto CCZ012 | BOX(3;0412) @02132031: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132031 : Ws → ⟪ (CCZ023 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132031 c4 = derive (CCZ023 ∷ Bx1-2430 ∷ []) (Bx1-2430 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw 0 (q53 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = eqn (Sw01 ∷ Bx0-2431 ∷ []) (Bx1-2430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2431⟩ (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ023 ∷ Bx1-2430 ∷ []) (Bx1-2430 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132031 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (Sw01 ∷ Bx1-2430 ∷ []) (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ (lit c4))

-- auto CCZ012 | BOX(3;0412) @02132130: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 : Ws → ⟪ (CCZ123 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4 = derive (CCZ123 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 2 (q54 c4) ∷
   rw 1 (q55 c4) ∷
   rw 0 (q56 c4) ∷
   rw⁻ 1 (q31 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q58 : Ws → Eqn
  q58 c4 = eqn (Sw12 ∷ Bx0-2431 ∷ []) (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (S4 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at04102142 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Sw12 ∷ Bx0-1432 ∷ []) (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4))

-- auto S0 | BOX(1;2034) @041041: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at041041 : Ws → ⟪ (S4 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at041041 c4 = derive (S4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ S4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q57 c4) ∷
   rw 2 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 1 (q57 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx0-2431 ∷ []) (Bx0-4231 ∷ []) (lem-sym12-at122441 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (X4 ∷ Bx0-4231 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx0-4231 ∷ []) (Bx0-2431 ∷ []) (lem-sym12-at1441 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ123 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (S4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at041041 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff134 ∷ []) (wl0666 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CS12 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS12 ∷ []) (wl0667 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CS12⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS12⁻ ∷ []) (wl0668 (lit c4))

-- F4 iI^0|CS23^1: 24 steps
lem-F4-iIᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-iIᵖ0∣CS23ᵖ1 c4 = derive (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   rw 3 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q61 c4) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 0 (q64 c4) ∷
   rw 4 (q36 c4) ∷
   rw 1 (q37 c4) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 1 (q66 c4) ∷
   re 5 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q67 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q66 c4) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q68 c4) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (CS01 ∷ []) (CS01 ∷ []) (wl0332 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (CS01 ∷ Bx2-1034 ∷ []) (Bx2-1034 ∷ CS01 ∷ []) (lem-CS12-beta-at0220 c4)

-- auto CS01 | BOX(2;1034): 3 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩ : Ws → ⟪ (CS01 ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩ c4 = derive (CS01 ∷ Bx2-1034 ∷ []) (Bx2-1034 ∷ CS01 ∷ [])
  (rw 0 (q69 c4) ∷
   rw 0 (q70 c4) ∷
   rw 1 (q69 c4) ∷ []) Eq.refl

private
  q71 : Ws → Eqn
  q71 c4 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wl0132 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (Sw01 ∷ Bx2-0134 ∷ []) (Bx2-1034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0134⟩ (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (CS01 ∷ Bx2-1034 ∷ []) (Bx2-1034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩ c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (Sw01 ∷ Bx2-1034 ∷ []) (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ (lit c4))

-- auto CS01 | BOX(2;1034) @0110: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at0110 : Ws → ⟪ (CS01 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at0110 c4 = derive (CS01 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 2 (q72 c4) ∷
   rw 1 (q73 c4) ∷
   rw 0 (q74 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = eqn (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (Sw12 ∷ Bx1-0234 ∷ []) (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (CS01 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at0110 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4))

-- auto CS01 | BOX(2;1034) @021021: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at021021 : Ws → ⟪ (CS02 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at021021 c4 = derive (CS02 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   rw 0 (q78 c4) ∷
   rw 1 (q79 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4))
  q81 : Ws → Eqn
  q81 c4 = eqn (Sw23 ∷ Bx1-0324 ∷ []) (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (CS02 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at021021 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (Sw23 ∷ Bx1-0234 ∷ []) (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4))

-- auto CS01 | BOX(2;1034) @03102132: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at03102132 : Ws → ⟪ (CS03 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at03102132 c4 = derive (CS03 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ CS03 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (Sw34 ∷ CS04 ∷ []) (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (Sw34 ∷ Bx1-0423 ∷ []) (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (CS03 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ CS03 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at03102132 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (Sw34 ∷ Bx1-0324 ∷ []) (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (Sw34 ∷ CS03 ∷ []) (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4))

-- auto CS01 | BOX(2;1034) @0410213243: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at0410213243 : Ws → ⟪ (CS04 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at0410213243 c4 = derive (CS04 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS04 ∷ [])
  (rw⁻ 0 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q87 c4) ∷
   rw 1 (q88 c4) ∷
   rw 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q85 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (CS04 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at0410213243 c4)

-- auto CS01 | BOX(2;1034) @04103143: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04103143 : Ws → ⟪ (CS04 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04103143 c4 = derive (CS04 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS04 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q5 c4) ∷
   rw 1 (q92 c4) ∷
   rw 0 (q3 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = eqn (Bx2-0413 ∷ []) (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (X4 ∷ Bx2-4013 ∷ X4 ∷ []) (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (Bx2-4013 ∷ []) (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (CS04 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at04103143 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) (wp0296 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (CCZ013 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CCZ013 ∷ []) (wp0300 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl0659 (lit c4))
  q100 : Ws → Eqn
  q100 c4 = eqn (Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ Toff314 ∷ []) (wp0301 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (CS03 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS03 ∷ []) (wp0302 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (CS03⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS03⁻ ∷ []) (wp0303 c4)

-- F4 S0^0|CS01^1: 24 steps
lem-F4-S0ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0ᵖ0∣CS01ᵖ1 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q93 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q95 c4) ∷
   rw 2 (q4 c4) ∷
   rw 1 (q96 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q93 c4) ∷
   rw 0 (q94 c4) ∷
   rw 1 (q95 c4) ∷
   rw 0 (q4 c4) ∷
   rw 4 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 4 (q99 c4) ∷
   rw⁻ 1 (q100 c4) ∷
   re 5 1 (CS03 ∷ []) ∷
   rw⁻ 2 (q101 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q100 c4) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 4 (q102 c4) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (Sw23 ∷ Bx1-0432 ∷ []) (Bx1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0432⟩ (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (Sw23 ∷ Bx1-0423 ∷ []) (Bx1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0423⟩ (lit c4))

-- auto CS01 | BOX(2;1034) @04102142: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04102142 : Ws → ⟪ (CS04 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04102142 c4 = derive (CS04 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ CS04 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q104 c4) ∷
   rw 1 (q92 c4) ∷
   rw 0 (q105 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (Sw01 ∷ Bx0-2134 ∷ []) (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (CS01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩ c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (Sw01 ∷ Bx1-2034 ∷ []) (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4))

-- auto CS01 | BOX(1;2034) @0110: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0110 : Ws → ⟪ (CS01 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0110 c4 = derive (CS01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q107 c4) ∷
   rw 0 (q108 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = eqn (Sw12 ∷ Bx0-1234 ∷ []) (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CS01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at0110 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (Sw12 ∷ Bx0-2134 ∷ []) (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4))

-- auto CS01 | BOX(1;2034) @021021: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at021021 : Ws → ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at021021 c4 = derive (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw 0 (q111 c4) ∷
   rw 1 (q79 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at021021 c4)
  q114 : Ws → Eqn
  q114 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4))

-- auto CS01 | BOX(1;2034) @03102132: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at03102132 : Ws → ⟪ (CS03 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at03102132 c4 = derive (CS03 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS03 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q112 c4) ∷
   rw 1 (q113 c4) ∷
   rw 0 (q114 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (CS03 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS03 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at03102132 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4))

-- auto CS01 | BOX(1;2034) @0410213243: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0410213243 : Ws → ⟪ (CS04 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0410213243 c4 = derive (CS04 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04 ∷ [])
  (rw⁻ 0 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   rw 0 (q117 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q85 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = eqn (CS04 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at0410213243 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X))
  q120 : Ws → Eqn
  q120 c4 = eqn (CCZ123 ∷ CS04 ∷ []) (CS04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CS04 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ []) (wp0304 c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (CS13 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS13 ∷ []) (wp0305 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS13⁻ ∷ []) (wp0306 c4)

-- F4 S0^0|CS12^1: 26 steps
lem-F4-S0ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0ᵖ0∣CS12ᵖ1 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q118 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 0 (q10 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 4 (q36 c4) ∷
   rw 1 (q119 c4) ∷
   rw 2 (q120 c4) ∷
   rw 3 (q119 c4) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   re 5 1 (CS13 ∷ []) ∷
   rw⁻ 2 (q122 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q121 c4) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q123 c4) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

-- auto CS01 | BOX(1;2034) @04102142: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at04102142 : Ws → ⟪ (CS04 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at04102142 c4 = derive (CS04 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS04 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q23 c4) ∷
   rw 1 (q118 c4) ∷
   rw 0 (q25 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q124 : Ws → Eqn
  q124 c4 = eqn (CS04 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at04102142 c4)

-- auto CS01 | BOX(1;2034) @041041: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at041041 : Ws → ⟪ (CS04 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at041041 c4 = derive (CS04 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS04 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q58 c4) ∷
   rw 1 (q124 c4) ∷
   rw 0 (q60 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = eqn (CS04 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at041041 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ []) (wp0307 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ []) (wp0308 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS12⁻ ∷ []) (wp0309 c4)

-- F4 S0^0|CS23^1: 26 steps
lem-F4-S0ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0ᵖ0∣CS23ᵖ1 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   rw 3 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 1 (q125 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q61 c4) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 0 (q64 c4) ∷
   rw 4 (q36 c4) ∷
   rw 1 (q119 c4) ∷
   rw 2 (q120 c4) ∷
   rw 3 (q119 c4) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 1 (q126 c4) ∷
   re 5 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q127 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q126 c4) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q128 c4) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q129 : Ws → Eqn
  q129 c4 = eqn (Bx2-3014 ∷ []) (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (Bx2-0314 ∷ []) (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (CS01 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01 ∷ []) (lem-CS12-beta-at021021 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (Bx2-0134 ∷ []) (Bx2-0314 ∷ []) (lem-sym23-at021021 c4)
  q133 : Ws → Eqn
  q133 c4 = eqn (Bx2-0314 ∷ []) (Bx2-3014 ∷ []) (lem-sym12-at02102331 c4)

-- auto CS01 | BOX(2;3014): 5 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩ : Ws → ⟪ (CS01 ∷ Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩ c4 = derive (CS01 ∷ Bx2-3014 ∷ []) (Bx2-3014 ∷ CS01 ∷ [])
  (rw 1 (q129 c4) ∷
   rw 1 (q130 c4) ∷
   rw 0 (q131 c4) ∷
   rw 0 (q132 c4) ∷
   rw 0 (q133 c4) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = eqn (Sw01 ∷ Bx2-3104 ∷ []) (Bx2-3014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3104⟩ (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (CS01 ∷ Bx2-3014 ∷ []) (Bx2-3014 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩ c4)
  q136 : Ws → Eqn
  q136 c4 = eqn (Sw01 ∷ Bx2-3014 ∷ []) (Bx2-3104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3014⟩ (lit c4))

-- auto CS01 | BOX(2;3014) @0110: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0110 : Ws → ⟪ (CS01 ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0110 c4 = derive (CS01 ∷ Bx2-3104 ∷ []) (Bx2-3104 ∷ CS01 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 2 (q134 c4) ∷
   rw 1 (q135 c4) ∷
   rw 0 (q136 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = eqn (Sw12 ∷ Bx1-3204 ∷ []) (Bx2-3104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3204⟩ (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (CS01 ∷ Bx2-3104 ∷ []) (Bx2-3104 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0110 c4)
  q139 : Ws → Eqn
  q139 c4 = eqn (Sw12 ∷ Bx2-3104 ∷ []) (Bx1-3204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3104⟩ (lit c4))

-- auto CS01 | BOX(2;3014) @021021: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at021021 : Ws → ⟪ (CS02 ∷ Bx1-3204 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3204 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at021021 c4 = derive (CS02 ∷ Bx1-3204 ∷ []) (Bx1-3204 ∷ CS02 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q137 c4) ∷
   rw 1 (q138 c4) ∷
   rw 0 (q139 c4) ∷
   rw 1 (q79 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = eqn (Sw23 ∷ Bx1-2304 ∷ []) (Bx1-3204 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2304⟩ (lit c4))
  q141 : Ws → Eqn
  q141 c4 = eqn (CS02 ∷ Bx1-3204 ∷ []) (Bx1-3204 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at021021 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (Sw23 ∷ Bx1-3204 ∷ []) (Bx1-2304 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3204⟩ (lit c4))

-- auto CS01 | BOX(2;3014) @03102132: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at03102132 : Ws → ⟪ (CS03 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at03102132 c4 = derive (CS03 ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS03 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q140 c4) ∷
   rw 1 (q141 c4) ∷
   rw 0 (q142 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = eqn (Sw34 ∷ Bx1-2403 ∷ []) (Bx1-2304 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2403⟩ (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (CS03 ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS03 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at03102132 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (Sw34 ∷ Bx1-2304 ∷ []) (Bx1-2403 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2304⟩ (lit c4))

-- auto CS01 | BOX(2;3014) @0410213243: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0410213243 : Ws → ⟪ (CS04 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0410213243 c4 = derive (CS04 ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CS04 ∷ [])
  (rw⁻ 0 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q145 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q85 c4) ∷ []) Eq.refl

private
  q146 : Ws → Eqn
  q146 c4 = eqn (Sw12 ∷ Bx2-1403 ∷ []) (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (CS04 ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0410213243 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (Sw12 ∷ Bx1-2403 ∷ []) (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ (lit c4))

-- auto CS01 | BOX(2;3014) @04103143: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at04103143 : Ws → ⟪ (CS04 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at04103143 c4 = derive (CS04 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS04 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q146 c4) ∷
   rw 1 (q147 c4) ∷
   rw 0 (q148 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4))
  q150 : Ws → Eqn
  q150 c4 = eqn (Sw01 ∷ Bx2-0413 ∷ []) (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (CS04 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at04103143 c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (Sw01 ∷ Bx2-1403 ∷ []) (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ (lit c4))
  q153 : Ws → Eqn
  q153 c4 = eqn (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4))

-- auto CS01 | BOX(2;3014) @043043: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at043043 : Ws → ⟪ (CS14 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at043043 c4 = derive (CS14 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS14 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q149 c4) ∷
   rw 2 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 0 (q152 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = eqn (CS14 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at043043 c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (CCZ013 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CCZ013 ∷ []) (wp0310 c4)
  q156 : Ws → Eqn
  q156 c4 = eqn (Toff314 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ []) (wl0669 (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ []) (wp0311 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS03⁻ ∷ []) (wp0312 c4)

-- F4 S1^0|CS01^1: 24 steps
lem-F4-S1ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1ᵖ0∣CS01ᵖ1 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q93 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q95 c4) ∷
   rw 2 (q4 c4) ∷
   rw 1 (q154 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q93 c4) ∷
   rw 0 (q94 c4) ∷
   rw 1 (q95 c4) ∷
   rw 0 (q4 c4) ∷
   rw 4 (q97 c4) ∷
   rw 1 (q155 c4) ∷
   rw 4 (q99 c4) ∷
   rw⁻ 1 (q156 c4) ∷
   re 5 1 (CS03 ∷ []) ∷
   rw⁻ 2 (q157 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q156 c4) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 4 (q158 c4) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

-- auto CS01 | BOX(1;2034) @04203243: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at04203243 : Ws → ⟪ (CS14 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at04203243 c4 = derive (CS14 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS14 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q149 c4) ∷
   rw 2 (q30 c4) ∷
   rw 1 (q118 c4) ∷
   rw 0 (q28 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

-- auto CS01 | BOX(2;1034) @04203243: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04203243 : Ws → ⟪ (CS14 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04203243 c4 = derive (CS14 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q149 c4) ∷
   rw 2 (q28 c4) ∷
   rw 1 (q92 c4) ∷
   rw 0 (q30 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q159 : Ws → Eqn
  q159 c4 = eqn (CS14 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at04203243 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (CCZ123 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CCZ123 ∷ []) (wl0670 (lit c4))
  q161 : Ws → Eqn
  q161 c4 = eqn (Toff324 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff324 ∷ []) (wl0671 (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (CS13 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS13 ∷ []) (wl0672 (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (CS13⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS13⁻ ∷ []) (wl0673 (lit c4))

-- F4 S1^0|CS12^1: 24 steps
lem-F4-S1ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1ᵖ0∣CS12ᵖ1 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q159 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 0 (q10 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 4 (q36 c4) ∷
   rw 1 (q160 c4) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 1 (q161 c4) ∷
   re 5 1 (CS13 ∷ []) ∷
   rw⁻ 2 (q162 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q161 c4) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q163 c4) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q164 : Ws → Eqn
  q164 c4 = eqn (Sw01 ∷ Bx0-1432 ∷ []) (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ (lit c4))
  q165 : Ws → Eqn
  q165 c4 = eqn (CS04 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at04102142 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (Sw01 ∷ Bx1-0432 ∷ []) (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ (lit c4))

-- auto CS01 | BOX(2;1034) @042042: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at042042 : Ws → ⟪ (CS14 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at042042 c4 = derive (CS14 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS14 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q149 c4) ∷
   rw 2 (q164 c4) ∷
   rw 1 (q165 c4) ∷
   rw 0 (q166 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = eqn (Sw01 ∷ Bx2-3140 ∷ []) (Bx2-3041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3140⟩ (lit c4))
  q168 : Ws → Eqn
  q168 c4 = eqn (CS01 ∷ Bx2-3041 ∷ []) (Bx2-3041 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩ c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (Sw01 ∷ Bx2-3041 ∷ []) (Bx2-3140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3041⟩ (lit c4))

-- auto CS01 | BOX(2;3041) @0110: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0110 : Ws → ⟪ (CS01 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0110 c4 = derive (CS01 ∷ Bx2-3140 ∷ []) (Bx2-3140 ∷ CS01 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 2 (q167 c4) ∷
   rw 1 (q168 c4) ∷
   rw 0 (q169 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q170 : Ws → Eqn
  q170 c4 = eqn (Sw12 ∷ Bx1-3240 ∷ []) (Bx2-3140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3240⟩ (lit c4))
  q171 : Ws → Eqn
  q171 c4 = eqn (CS01 ∷ Bx2-3140 ∷ []) (Bx2-3140 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0110 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (Sw12 ∷ Bx2-3140 ∷ []) (Bx1-3240 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3140⟩ (lit c4))

-- auto CS01 | BOX(2;3041) @021021: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at021021 : Ws → ⟪ (CS02 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at021021 c4 = derive (CS02 ∷ Bx1-3240 ∷ []) (Bx1-3240 ∷ CS02 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q170 c4) ∷
   rw 1 (q171 c4) ∷
   rw 0 (q172 c4) ∷
   rw 1 (q79 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q173 : Ws → Eqn
  q173 c4 = eqn (Sw23 ∷ Bx1-2340 ∷ []) (Bx1-3240 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2340⟩ (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (CS02 ∷ Bx1-3240 ∷ []) (Bx1-3240 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at021021 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (Sw23 ∷ Bx1-3240 ∷ []) (Bx1-2340 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3240⟩ (lit c4))

-- auto CS01 | BOX(2;3041) @03102132: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at03102132 : Ws → ⟪ (CS03 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at03102132 c4 = derive (CS03 ∷ Bx1-2340 ∷ []) (Bx1-2340 ∷ CS03 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q173 c4) ∷
   rw 1 (q174 c4) ∷
   rw 0 (q175 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q176 : Ws → Eqn
  q176 c4 = eqn (Sw34 ∷ Bx1-2430 ∷ []) (Bx1-2340 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2430⟩ (lit c4))
  q177 : Ws → Eqn
  q177 c4 = eqn (CS03 ∷ Bx1-2340 ∷ []) (Bx1-2340 ∷ CS03 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at03102132 c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (Sw34 ∷ Bx1-2340 ∷ []) (Bx1-2430 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2340⟩ (lit c4))

-- auto CS01 | BOX(2;3041) @0410213243: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0410213243 : Ws → ⟪ (CS04 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0410213243 c4 = derive (CS04 ∷ Bx1-2430 ∷ []) (Bx1-2430 ∷ CS04 ∷ [])
  (rw⁻ 0 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q176 c4) ∷
   rw 1 (q177 c4) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q85 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = eqn (CS04 ∷ Bx1-2430 ∷ []) (Bx1-2430 ∷ CS04 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0410213243 c4)

-- auto CS01 | BOX(2;3041) @04203243: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at04203243 : Ws → ⟪ (CS14 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at04203243 c4 = derive (CS14 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS14 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q149 c4) ∷
   rw 2 (q54 c4) ∷
   rw 1 (q179 c4) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = eqn (CS14 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at04203243 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (Toff134 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ []) (wl0674 (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn (CS12 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS12 ∷ []) (wl0675 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (CS12⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS12⁻ ∷ []) (wl0676 (lit c4))

-- F4 S1^0|CS23^1: 24 steps
lem-F4-S1ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1ᵖ0∣CS23ᵖ1 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   rw 3 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 1 (q180 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q61 c4) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 0 (q64 c4) ∷
   rw 4 (q36 c4) ∷
   rw 1 (q160 c4) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 1 (q181 c4) ∷
   re 5 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q182 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q181 c4) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q183 c4) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q184 : Ws → Eqn
  q184 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 (lit c4))
  q185 : Ws → Eqn
  q185 c4 = eqn (CS14 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at04203243 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 (lit c4))

-- auto CS01 | BOX(1;2034) @0412203143: 7 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0412203143 : Ws → ⟪ (CS24 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩-at0412203143 c4 = derive (CS24 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS24 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q184 c4) ∷
   rw 2 (q5 c4) ∷
   rw 1 (q185 c4) ∷
   rw 0 (q3 c4) ∷
   rw⁻ 1 (q186 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q187 : Ws → Eqn
  q187 c4 = eqn (CS24 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩-at0412203143 c4)
  q188 : Ws → Eqn
  q188 c4 = eqn (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))
  q189 : Ws → Eqn
  q189 c4 = eqn (CCZ013 ∷ CS24 ∷ []) (CS24 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS24 (lit c4))
  q190 : Ws → Eqn
  q190 c4 = eqn (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ []) (wl0677 (lit c4))
  q191 : Ws → Eqn
  q191 c4 = eqn (CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ []) (wp0313 c4)
  q192 : Ws → Eqn
  q192 c4 = eqn (CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ []) (wp0314 c4)

-- F4 S2^0|CS01^1: 26 steps
lem-F4-S2ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2ᵖ0∣CS01ᵖ1 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q93 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q95 c4) ∷
   rw 2 (q4 c4) ∷
   rw 1 (q187 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q93 c4) ∷
   rw 0 (q94 c4) ∷
   rw 1 (q95 c4) ∷
   rw 0 (q4 c4) ∷
   rw 4 (q97 c4) ∷
   rw 1 (q188 c4) ∷
   rw 2 (q189 c4) ∷
   rw 3 (q188 c4) ∷
   rw 4 (q99 c4) ∷
   rw⁻ 1 (q190 c4) ∷
   re 5 1 (CS03 ∷ []) ∷
   rw⁻ 2 (q191 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q190 c4) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 4 (q192 c4) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q193 : Ws → Eqn
  q193 c4 = eqn (Sw01 ∷ Bx0-2413 ∷ []) (Bx1-2403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2413⟩ (lit c4))
  q194 : Ws → Eqn
  q194 c4 = eqn (Sw01 ∷ Bx1-2403 ∷ []) (Bx0-2413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2403⟩ (lit c4))

-- auto CS01 | BOX(2;3014) @04203243: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at04203243 : Ws → ⟪ (CS14 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at04203243 c4 = derive (CS14 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CS14 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q149 c4) ∷
   rw 2 (q193 c4) ∷
   rw 1 (q147 c4) ∷
   rw 0 (q194 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q195 : Ws → Eqn
  q195 c4 = eqn (Sw12 ∷ Bx0-1423 ∷ []) (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4))
  q196 : Ws → Eqn
  q196 c4 = eqn (CS14 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at04203243 c4)
  q197 : Ws → Eqn
  q197 c4 = eqn (Sw12 ∷ Bx0-2413 ∷ []) (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4))

-- auto CS01 | BOX(2;3014) @0412203143: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0412203143 : Ws → ⟪ (CS24 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0412203143 c4 = derive (CS24 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS24 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q184 c4) ∷
   rw 2 (q195 c4) ∷
   rw 1 (q196 c4) ∷
   rw 0 (q197 c4) ∷
   rw⁻ 1 (q186 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

-- auto CS01 | BOX(2;3041) @0412203143: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0412203143 : Ws → ⟪ (CS24 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0412203143 c4 = derive (CS24 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS24 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q184 c4) ∷
   rw 2 (q60 c4) ∷
   rw 1 (q180 c4) ∷
   rw 0 (q58 c4) ∷
   rw⁻ 1 (q186 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q198 : Ws → Eqn
  q198 c4 = eqn (CS24 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0412203143 c4)
  q199 : Ws → Eqn
  q199 c4 = eqn (CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ []) (wl0678 (lit c4))
  q200 : Ws → Eqn
  q200 c4 = eqn (Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ []) (wl0679 (lit c4))
  q201 : Ws → Eqn
  q201 c4 = eqn (CS13 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS13 ∷ []) (wl0680 (lit c4))
  q202 : Ws → Eqn
  q202 c4 = eqn (CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS13⁻ ∷ []) (wl0681 (lit c4))

-- F4 S2^0|CS12^1: 24 steps
lem-F4-S2ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2ᵖ0∣CS12ᵖ1 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q198 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 0 (q10 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 4 (q36 c4) ∷
   rw 1 (q199 c4) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 1 (q200 c4) ∷
   re 5 1 (CS13 ∷ []) ∷
   rw⁻ 2 (q201 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q200 c4) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q202 c4) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q203 : Ws → Eqn
  q203 c4 = eqn (CS14 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at042042 c4)

-- auto CS01 | BOX(2;1034) @04122041: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04122041 : Ws → ⟪ (CS24 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04122041 c4 = derive (CS24 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS24 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q184 c4) ∷
   rw 2 (q58 c4) ∷
   rw 1 (q203 c4) ∷
   rw 0 (q60 c4) ∷
   rw⁻ 1 (q186 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q204 : Ws → Eqn
  q204 c4 = eqn (CS24 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at04122041 c4)
  q205 : Ws → Eqn
  q205 c4 = eqn (Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff134 ∷ []) (wl0682 (lit c4))
  q206 : Ws → Eqn
  q206 c4 = eqn (CS12 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS12 ∷ []) (wl0683 (lit c4))
  q207 : Ws → Eqn
  q207 c4 = eqn (CS12⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS12⁻ ∷ []) (wl0684 (lit c4))

-- F4 S2^0|CS23^1: 24 steps
lem-F4-S2ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2ᵖ0∣CS23ᵖ1 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   rw 3 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 1 (q204 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q61 c4) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 0 (q64 c4) ∷
   rw 4 (q36 c4) ∷
   rw 1 (q199 c4) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 1 (q205 c4) ∷
   re 5 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q206 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q205 c4) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q207 c4) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q208 : Ws → Eqn
  q208 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 (lit c4))
  q209 : Ws → Eqn
  q209 c4 = eqn (CS24 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0412203143 c4)
  q210 : Ws → Eqn
  q210 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 (lit c4))

-- auto CS01 | BOX(2;3041) @0413203142: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413203142 : Ws → ⟪ (CS34 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413203142 c4 = derive (CS34 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS34 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q208 c4) ∷
   rw 2 (q25 c4) ∷
   rw 1 (q209 c4) ∷
   rw 0 (q23 c4) ∷
   rw⁻ 1 (q210 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q211 : Ws → Eqn
  q211 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q212 : Ws → Eqn
  q212 c4 = eqn (CS34 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413203142 c4)

-- auto CS01 | BOX(2;3041) @0413213042: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413213042 : Ws → ⟪ (CS34 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413213042 c4 = derive (CS34 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS34 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q211 c4) ∷
   rw 2 (q30 c4) ∷
   rw 1 (q212 c4) ∷
   rw 0 (q28 c4) ∷
   rw 1 (q211 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q214 : Ws → Eqn
  q214 c4 = eqn (CS34 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413213042 c4)

-- auto CS01 | BOX(2;3041) @04133041: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at04133041 : Ws → ⟪ (CS34 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at04133041 c4 = derive (CS34 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS34 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q213 c4) ∷
   rw 2 (q5 c4) ∷
   rw 1 (q214 c4) ∷
   rw 0 (q3 c4) ∷
   rw 1 (q213 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q215 : Ws → Eqn
  q215 c4 = eqn (CS34 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at04133041 c4)
  q216 : Ws → Eqn
  q216 c4 = eqn (CCZ013 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ013 ∷ []) (wp0315 c4)
  q217 : Ws → Eqn
  q217 c4 = eqn (Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ []) (wl0685 (lit c4))
  q218 : Ws → Eqn
  q218 c4 = eqn (CS03 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS03 ∷ []) (wp0316 c4)
  q219 : Ws → Eqn
  q219 c4 = eqn (CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS03⁻ ∷ []) (wp0317 c4)

-- F4 S3^0|CS01^1: 24 steps
lem-F4-S3ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3ᵖ0∣CS01ᵖ1 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q93 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q95 c4) ∷
   rw 2 (q4 c4) ∷
   rw 1 (q215 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q93 c4) ∷
   rw 0 (q94 c4) ∷
   rw 1 (q95 c4) ∷
   rw 0 (q4 c4) ∷
   rw 4 (q97 c4) ∷
   rw 1 (q216 c4) ∷
   rw 4 (q99 c4) ∷
   rw⁻ 1 (q217 c4) ∷
   re 5 1 (CS03 ∷ []) ∷
   rw⁻ 2 (q218 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q217 c4) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 4 (q219 c4) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

-- auto CS01 | BOX(2;3014) @0413203142: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203142 : Ws → ⟪ (CS34 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203142 c4 = derive (CS34 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS34 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q208 c4) ∷
   rw 2 (q23 c4) ∷
   rw 1 (q198 c4) ∷
   rw 0 (q25 c4) ∷
   rw⁻ 1 (q210 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = eqn (CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ []) (wl0686 (lit c4))
  q221 : Ws → Eqn
  q221 c4 = eqn (Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ []) (wl0687 (lit c4))
  q222 : Ws → Eqn
  q222 c4 = eqn (CS13 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS13 ∷ []) (wl0688 (lit c4))
  q223 : Ws → Eqn
  q223 c4 = eqn (CS13⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS13⁻ ∷ []) (wl0689 (lit c4))

-- F4 S3^0|CS12^1: 24 steps
lem-F4-S3ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3ᵖ0∣CS12ᵖ1 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q212 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 0 (q10 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 4 (q36 c4) ∷
   rw 1 (q220 c4) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 1 (q221 c4) ∷
   re 5 1 (CS13 ∷ []) ∷
   rw⁻ 2 (q222 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q221 c4) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q223 c4) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = eqn (CS34 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203142 c4)

-- auto CS01 | BOX(2;3014) @0413203241: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203241 : Ws → ⟪ (CS34 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203241 c4 = derive (CS34 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS34 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q213 c4) ∷
   rw 2 (q58 c4) ∷
   rw 1 (q224 c4) ∷
   rw 0 (q60 c4) ∷
   rw 1 (q213 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q225 : Ws → Eqn
  q225 c4 = eqn (CS34 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203241 c4)
  q226 : Ws → Eqn
  q226 c4 = eqn (Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ []) (wl0690 (lit c4))
  q227 : Ws → Eqn
  q227 c4 = eqn (CS12 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS12 ∷ []) (wl0691 (lit c4))
  q228 : Ws → Eqn
  q228 c4 = eqn (CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS12⁻ ∷ []) (wl0692 (lit c4))

-- F4 S3^0|CS23^1: 24 steps
lem-F4-S3ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3ᵖ0∣CS23ᵖ1 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   rw 3 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 1 (q225 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q61 c4) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 0 (q64 c4) ∷
   rw 4 (q36 c4) ∷
   rw 1 (q220 c4) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 1 (q226 c4) ∷
   re 5 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q227 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q226 c4) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q228 c4) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q229 : Ws → Eqn
  q229 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q230 : Ws → Eqn
  q230 c4 = eqn (Toff204 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff204 ∷ []) (wp0318 c4)
  q231 : Ws → Eqn
  q231 c4 = eqn (CK40 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK40 ∷ []) (lem-comm-CK40-CCZ123 (lit c4))
  q232 : Ws → Eqn
  q232 c4 = eqn (Toff314 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff314 ∷ []) (wp0319 c4)
  q233 : Ws → Eqn
  q233 c4 = eqn (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0320 c4)

-- F4 K0^0|CS01^1: 18 steps
lem-F4-K0ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0ᵖ0∣CS01ᵖ1 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 3 (q229 c4) ∷
   rw⁻ 0 (q230 c4) ∷
   rw⁻ 3 (q119 c4) ∷
   rw 2 (q231 c4) ∷
   rw⁻ 1 (q119 c4) ∷
   rw⁻ 2 (q230 c4) ∷
   rw⁻ 5 (q119 c4) ∷
   rw 4 (q231 c4) ∷
   rw⁻ 3 (q119 c4) ∷
   rw⁻ 0 (q229 c4) ∷
   rw⁻ 1 (q232 c4) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q233 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q234 : Ws → Eqn
  q234 c4 = eqn (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ []) (wl0648 (lit c4))
  q235 : Ws → Eqn
  q235 c4 = eqn (CK01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩ c4)
  q236 : Ws → Eqn
  q236 c4 = eqn (CK10 ∷ Sw01 ∷ []) (Sw01 ∷ CK01 ∷ []) (wl0649 (lit c4))

-- auto CK01 | BOX(1;2034) @0110: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0110 : Ws → ⟪ (CK10 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CK10 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0110 c4 = derive (CK10 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CK10 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw⁻ 1 (q234 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q235 c4) ∷
   rw 0 (q108 c4) ∷
   rw⁻ 1 (q236 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q237 : Ws → Eqn
  q237 c4 = eqn (Sw12 ∷ CK20 ∷ []) (CK10 ∷ Sw12 ∷ []) (lem-nat-1-CK20 (lit c4))
  q238 : Ws → Eqn
  q238 c4 = eqn (CK10 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CK10 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at0110 c4)
  q239 : Ws → Eqn
  q239 c4 = eqn (Sw12 ∷ CK10 ∷ []) (CK20 ∷ Sw12 ∷ []) (lem-nat-1-CK10 (lit c4))

-- auto CK01 | BOX(1;2034) @021021: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at021021 : Ws → ⟪ (CK20 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK20 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at021021 c4 = derive (CK20 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK20 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q237 c4) ∷
   rw 2 (q109 c4) ∷
   rw 1 (q238 c4) ∷
   rw 0 (q111 c4) ∷
   rw 1 (q239 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q240 : Ws → Eqn
  q240 c4 = eqn (Sw23 ∷ CK30 ∷ []) (CK20 ∷ Sw23 ∷ []) (lem-nat-2-CK30 (lit c4))
  q241 : Ws → Eqn
  q241 c4 = eqn (CK20 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK20 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at021021 c4)
  q242 : Ws → Eqn
  q242 c4 = eqn (Sw23 ∷ CK20 ∷ []) (CK30 ∷ Sw23 ∷ []) (lem-nat-2-CK20 (lit c4))

-- auto CK01 | BOX(1;2034) @03102132: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at03102132 : Ws → ⟪ (CK30 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CK30 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at03102132 c4 = derive (CK30 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CK30 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q240 c4) ∷
   rw 2 (q112 c4) ∷
   rw 1 (q241 c4) ∷
   rw 0 (q114 c4) ∷
   rw 1 (q242 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q243 : Ws → Eqn
  q243 c4 = eqn (Sw34 ∷ CK40 ∷ []) (CK30 ∷ Sw34 ∷ []) (lem-nat-3-CK40 (lit c4))
  q244 : Ws → Eqn
  q244 c4 = eqn (CK30 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CK30 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at03102132 c4)
  q245 : Ws → Eqn
  q245 c4 = eqn (Sw34 ∷ CK30 ∷ []) (CK40 ∷ Sw34 ∷ []) (lem-nat-3-CK30 (lit c4))

-- auto CK01 | BOX(1;2034) @0410213243: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0410213243 : Ws → ⟪ (CK40 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0410213243 c4 = derive (CK40 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CK40 ∷ [])
  (rw⁻ 0 (q85 c4) ∷
   rw 1 (q243 c4) ∷
   rw 2 (q115 c4) ∷
   rw 1 (q244 c4) ∷
   rw 0 (q117 c4) ∷
   rw 1 (q245 c4) ∷
   rw 2 (q85 c4) ∷ []) Eq.refl

private
  q246 : Ws → Eqn
  q246 c4 = eqn (CK40 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at0410213243 c4)
  q247 : Ws → Eqn
  q247 c4 = eqn (CCZ123 ∷ CK40 ∷ []) (CK40 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CK40 (lit c4))
  q248 : Ws → Eqn
  q248 c4 = eqn (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ []) (wp0321 c4)
  q249 : Ws → Eqn
  q249 c4 = eqn (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS13 ∷ []) (wp0322 c4)
  q250 : Ws → Eqn
  q250 c4 = eqn (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS13⁻ ∷ []) (wp0323 c4)

-- F4 K0^0|CS12^1: 26 steps
lem-F4-K0ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0ᵖ0∣CS12ᵖ1 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q246 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 0 (q10 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 4 (q36 c4) ∷
   rw 1 (q119 c4) ∷
   rw 2 (q247 c4) ∷
   rw 3 (q119 c4) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 1 (q248 c4) ∷
   re 5 1 (CS13 ∷ []) ∷
   rw⁻ 2 (q249 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q248 c4) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q250 c4) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q251 : Ws → Eqn
  q251 c4 = eqn (Sw23 ∷ CK40 ∷ []) (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4))

-- auto CK01 | BOX(1;2034) @04102142: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at04102142 : Ws → ⟪ (CK40 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at04102142 c4 = derive (CK40 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CK40 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q251 c4) ∷
   rw 2 (q23 c4) ∷
   rw 1 (q246 c4) ∷
   rw 0 (q25 c4) ∷
   rw 1 (q251 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q252 : Ws → Eqn
  q252 c4 = eqn (Sw12 ∷ CK40 ∷ []) (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4))
  q253 : Ws → Eqn
  q253 c4 = eqn (CK40 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at04102142 c4)

-- auto CK01 | BOX(1;2034) @041041: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at041041 : Ws → ⟪ (CK40 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at041041 c4 = derive (CK40 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CK40 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q252 c4) ∷
   rw 2 (q58 c4) ∷
   rw 1 (q253 c4) ∷
   rw 0 (q60 c4) ∷
   rw 1 (q252 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q254 : Ws → Eqn
  q254 c4 = eqn (CK40 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at041041 c4)
  q255 : Ws → Eqn
  q255 c4 = eqn (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff134 ∷ []) (wp0324 c4)
  q256 : Ws → Eqn
  q256 c4 = eqn (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS12 ∷ []) (wp0325 c4)
  q257 : Ws → Eqn
  q257 c4 = eqn (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS12⁻ ∷ []) (wp0326 c4)

-- F4 K0^0|CS23^1: 26 steps
lem-F4-K0ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0ᵖ0∣CS23ᵖ1 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   rw 3 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 1 (q254 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q61 c4) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 0 (q64 c4) ∷
   rw 4 (q36 c4) ∷
   rw 1 (q119 c4) ∷
   rw 2 (q247 c4) ∷
   rw 3 (q119 c4) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 1 (q255 c4) ∷
   re 5 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q256 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q255 c4) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q257 c4) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q258 : Ws → Eqn
  q258 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q259 : Ws → Eqn
  q259 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q260 : Ws → Eqn
  q260 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q261 : Ws → Eqn
  q261 c4 = eqn (Toff203 ∷ X4 ∷ []) (X4 ∷ Toff203 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))
  q262 : Ws → Eqn
  q262 c4 = eqn (CK41 ∷ Toff203 ∷ []) (Toff203 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF203 (lit c4))
  q263 : Ws → Eqn
  q263 c4 = eqn (CCZ124 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CCZ124 ∷ []) (wl0693 (lit c4))
  q264 : Ws → Eqn
  q264 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q265 : Ws → Eqn
  q265 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q266 : Ws → Eqn
  q266 c4 = eqn (Toff314 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff314 ∷ []) (wl0694 (lit c4))
  q267 : Ws → Eqn
  q267 c4 = eqn (CS03 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS03 ∷ []) (wp0327 c4)
  q268 : Ws → Eqn
  q268 c4 = eqn (CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS03⁻ ∷ []) (wp0328 c4)

-- F4 K1^0|CS01^1: 24 steps
lem-F4-K1ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1ᵖ0∣CS01ᵖ1 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 3 (q258 c4) ∷
   rw 3 (q259 c4) ∷
   rw 3 (q260 c4) ∷
   rw⁻ 2 (q261 c4) ∷
   rw 1 (q262 c4) ∷
   rw⁻ 0 (q261 c4) ∷
   rw⁻ 1 (q263 c4) ∷
   rw⁻ 4 (q261 c4) ∷
   rw 3 (q262 c4) ∷
   rw⁻ 2 (q261 c4) ∷
   rw⁻ 3 (q263 c4) ∷
   rw⁻ 0 (q260 c4) ∷
   rw 0 (q264 c4) ∷
   rw 0 (q265 c4) ∷
   rw⁻ 1 (q266 c4) ∷
   re 5 1 (CS03 ∷ []) ∷
   rw⁻ 2 (q267 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q266 c4) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 4 (q268 c4) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q269 : Ws → Eqn
  q269 c4 = eqn (Sw01 ∷ CK41 ∷ []) (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4))
  q270 : Ws → Eqn
  q270 c4 = eqn (Sw01 ∷ CK40 ∷ []) (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4))

-- auto CK01 | BOX(1;2034) @04203243: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at04203243 : Ws → ⟪ (CK41 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CK41 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at04203243 c4 = derive (CK41 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CK41 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q269 c4) ∷
   rw 2 (q30 c4) ∷
   rw 1 (q246 c4) ∷
   rw 0 (q28 c4) ∷
   rw 1 (q270 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q271 : Ws → Eqn
  q271 c4 = eqn (Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4)
  q272 : Ws → Eqn
  q272 c4 = eqn (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) (wp0329 c4)
  q273 : Ws → Eqn
  q273 c4 = eqn (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))
  q274 : Ws → Eqn
  q274 c4 = eqn (CK41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 (lit c4))
  q275 : Ws → Eqn
  q275 c4 = eqn (Toff324 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff324 ∷ []) (wl0695 (lit c4))
  q276 : Ws → Eqn
  q276 c4 = eqn (CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (wl0696 (lit c4))

-- F4 K1^0|CS12^1: 18 steps
lem-F4-K1ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1ᵖ0∣CS12ᵖ1 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw 3 (q271 c4) ∷
   rw⁻ 0 (q272 c4) ∷
   rw⁻ 3 (q273 c4) ∷
   rw 2 (q274 c4) ∷
   rw⁻ 1 (q273 c4) ∷
   rw⁻ 2 (q272 c4) ∷
   rw⁻ 5 (q273 c4) ∷
   rw 4 (q274 c4) ∷
   rw⁻ 3 (q273 c4) ∷
   rw⁻ 0 (q271 c4) ∷
   rw⁻ 1 (q275 c4) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q276 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q277 : Ws → Eqn
  q277 c4 = eqn (Bx0-1432 ∷ []) (Bx0-1342 ∷ []) (lem-sym23-at2442 c4)
  q278 : Ws → Eqn
  q278 c4 = eqn (Sw12 ∷ Bx0-1342 ∷ []) (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ (lit c4))

-- sym23 @122441: 5 steps
lem-sym23-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym23-at122441 c4 = derive (Bx0-2431 ∷ []) (Bx0-2341 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q58 c4) ∷
   rw 1 (q277 c4) ∷
   rw 0 (q278 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q279 : Ws → Eqn
  q279 c4 = eqn (Sw12 ∷ Bx0-2341 ∷ []) (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ (lit c4))
  q280 : Ws → Eqn
  q280 c4 = eqn (Bx0-1342 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4)
  q281 : Ws → Eqn
  q281 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 (lit c4))
  q282 : Ws → Eqn
  q282 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4))

-- beta-T @12233441: 8 steps
lem-beta-T-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at12233441 c4 = derive (Bx0-2341 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q279 c4) ∷
   rw 1 (q280 c4) ∷
   rw 0 (q281 c4) ∷
   rw 1 (q282 c4) ∷
   rw 2 (q281 c4) ∷
   rw 3 (q282 c4) ∷
   rw 4 (q1 c4) ∷ []) Eq.refl

private
  q283 : Ws → Eqn
  q283 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1432 ∷ []) (lem-sym23-at233442 c4)

-- sym23 @12233441: 5 steps
lem-sym23-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-sym23-at12233441 c4 = derive (Bx0-2341 ∷ []) (Bx0-2431 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q279 c4) ∷
   rw 1 (q283 c4) ∷
   rw 0 (q60 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q284 : Ws → Eqn
  q284 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2341 ∷ []) (lem-sym23-at122441 c4)
  q285 : Ws → Eqn
  q285 c4 = eqn (Bx0-2341 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at12233441 c4)
  q286 : Ws → Eqn
  q286 c4 = eqn (Toff023 ∷ X4 ∷ []) (X4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))
  q287 : Ws → Eqn
  q287 c4 = eqn (CK41 ∷ Toff023 ∷ []) (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4))
  q288 : Ws → Eqn
  q288 c4 = eqn (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ []) (wp0330 c4)
  q289 : Ws → Eqn
  q289 c4 = eqn (Bx0-2341 ∷ []) (Bx0-2431 ∷ []) (lem-sym23-at12233441 c4)
  q290 : Ws → Eqn
  q290 c4 = eqn (Toff134 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff134 ∷ []) (wl0697 (lit c4))
  q291 : Ws → Eqn
  q291 c4 = eqn (CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (wl0698 (lit c4))

-- F4 K1^0|CS23^1: 20 steps
lem-F4-K1ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1ᵖ0∣CS23ᵖ1 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw 3 (q284 c4) ∷
   rw 3 (q285 c4) ∷
   rw⁻ 2 (q286 c4) ∷
   rw 1 (q287 c4) ∷
   rw⁻ 0 (q286 c4) ∷
   rw⁻ 1 (q288 c4) ∷
   rw⁻ 4 (q286 c4) ∷
   rw 3 (q287 c4) ∷
   rw⁻ 2 (q286 c4) ∷
   rw⁻ 3 (q288 c4) ∷
   rw⁻ 0 (q285 c4) ∷
   rw 0 (q289 c4) ∷
   rw⁻ 1 (q290 c4) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q291 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q292 : Ws → Eqn
  q292 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl0160 (lit c4))
  q293 : Ws → Eqn
  q293 c4 = eqn (CK41 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CK41 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at04203243 c4)
  q294 : Ws → Eqn
  q294 c4 = eqn (CK42 ∷ Sw12 ∷ []) (Sw12 ∷ CK41 ∷ []) (wl0164 (lit c4))

-- auto CK01 | BOX(1;2034) @0412203143: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0412203143 : Ws → ⟪ (CK42 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CK42 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0412203143 c4 = derive (CK42 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CK42 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q292 c4) ∷
   rw 2 (q5 c4) ∷
   rw 1 (q293 c4) ∷
   rw 0 (q3 c4) ∷
   rw⁻ 1 (q294 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q295 : Ws → Eqn
  q295 c4 = eqn (CK42 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CK42 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at0412203143 c4)
  q296 : Ws → Eqn
  q296 c4 = eqn (CCZ013 ∷ CK42 ∷ []) (CK42 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CK42 (lit c4))
  q297 : Ws → Eqn
  q297 c4 = eqn (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff314 ∷ []) (wl0699 (lit c4))
  q298 : Ws → Eqn
  q298 c4 = eqn (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS03 ∷ []) (wp0331 c4)
  q299 : Ws → Eqn
  q299 c4 = eqn (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS03⁻ ∷ []) (wp0332 c4)

-- F4 K2^0|CS01^1: 26 steps
lem-F4-K2ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2ᵖ0∣CS01ᵖ1 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 3 (q93 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q95 c4) ∷
   rw 2 (q4 c4) ∷
   rw 1 (q295 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q93 c4) ∷
   rw 0 (q94 c4) ∷
   rw 1 (q95 c4) ∷
   rw 0 (q4 c4) ∷
   rw 4 (q97 c4) ∷
   rw 1 (q188 c4) ∷
   rw 2 (q296 c4) ∷
   rw 3 (q188 c4) ∷
   rw 4 (q99 c4) ∷
   rw⁻ 1 (q297 c4) ∷
   re 5 1 (CS03 ∷ []) ∷
   rw⁻ 2 (q298 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q297 c4) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 4 (q299 c4) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q300 : Ws → Eqn
  q300 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1432 ∷ []) (lem-sym34-at243243 c4)
  q301 : Ws → Eqn
  q301 c4 = eqn (Toff013 ∷ X4 ∷ []) (X4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))
  q302 : Ws → Eqn
  q302 c4 = eqn (CK42 ∷ Toff013 ∷ []) (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 (lit c4))
  q303 : Ws → Eqn
  q303 c4 = eqn (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ []) (wp0333 c4)
  q304 : Ws → Eqn
  q304 c4 = eqn (Bx0-1432 ∷ []) (Bx0-1423 ∷ []) (lem-sym34-at2442 c4)
  q305 : Ws → Eqn
  q305 c4 = eqn (Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff324 ∷ []) (wl0700 (lit c4))
  q306 : Ws → Eqn
  q306 c4 = eqn (CS13 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS13 ∷ []) (wl0701 (lit c4))
  q307 : Ws → Eqn
  q307 c4 = eqn (CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS13⁻ ∷ []) (wl0702 (lit c4))

-- F4 K2^0|CS12^1: 24 steps
lem-F4-K2ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2ᵖ0∣CS12ᵖ1 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw 3 (q300 c4) ∷
   rw 3 (q277 c4) ∷
   rw 3 (q280 c4) ∷
   rw⁻ 2 (q301 c4) ∷
   rw 1 (q302 c4) ∷
   rw⁻ 0 (q301 c4) ∷
   rw⁻ 1 (q303 c4) ∷
   rw⁻ 4 (q301 c4) ∷
   rw 3 (q302 c4) ∷
   rw⁻ 2 (q301 c4) ∷
   rw⁻ 3 (q303 c4) ∷
   rw⁻ 0 (q280 c4) ∷
   rw 0 (q283 c4) ∷
   rw 0 (q304 c4) ∷
   rw⁻ 1 (q305 c4) ∷
   re 5 1 (CS13 ∷ []) ∷
   rw⁻ 2 (q306 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q305 c4) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q307 c4) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q308 : Ws → Eqn
  q308 c4 = eqn (Bx0-1432 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4)
  q309 : Ws → Eqn
  q309 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 (lit c4))

-- beta-T @122441: 8 steps
lem-beta-T-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at122441 c4 = derive (Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q58 c4) ∷
   rw 1 (q308 c4) ∷
   rw 0 (q309 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q309 c4) ∷
   rw 3 (q2 c4) ∷
   rw 4 (q1 c4) ∷ []) Eq.refl

private
  q310 : Ws → Eqn
  q310 c4 = eqn (Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4)
  q311 : Ws → Eqn
  q311 c4 = eqn (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ []) (wp0334 c4)
  q312 : Ws → Eqn
  q312 c4 = eqn (CK42 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK42 ∷ []) (lem-comm-CK42-CCZ013 (lit c4))
  q313 : Ws → Eqn
  q313 c4 = eqn (Toff134 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff134 ∷ []) (wl0703 (lit c4))
  q314 : Ws → Eqn
  q314 c4 = eqn (CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (wl0704 (lit c4))

-- F4 K2^0|CS23^1: 18 steps
lem-F4-K2ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2ᵖ0∣CS23ᵖ1 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw 3 (q310 c4) ∷
   rw⁻ 0 (q311 c4) ∷
   rw⁻ 3 (q188 c4) ∷
   rw 2 (q312 c4) ∷
   rw⁻ 1 (q188 c4) ∷
   rw⁻ 2 (q311 c4) ∷
   rw⁻ 5 (q188 c4) ∷
   rw 4 (q312 c4) ∷
   rw⁻ 3 (q188 c4) ∷
   rw⁻ 0 (q310 c4) ∷
   rw⁻ 1 (q313 c4) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q314 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q315 : Ws → Eqn
  q315 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q316 : Ws → Eqn
  q316 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q317 : Ws → Eqn
  q317 c4 = eqn (Toff201 ∷ X4 ∷ []) (X4 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (X ↑))
  q318 : Ws → Eqn
  q318 c4 = eqn (Toff201 ∷ CK43 ∷ []) (CK43 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CK₁₀))
  q319 : Ws → Eqn
  q319 c4 = eqn (CCZ234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CCZ234 ∷ []) (wl0705 (lit c4))
  q320 : Ws → Eqn
  q320 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q321 : Ws → Eqn
  q321 c4 = eqn (Toff314 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff314 ∷ []) (wl0706 (lit c4))
  q322 : Ws → Eqn
  q322 c4 = eqn (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0335 c4)

-- F4 K3^0|CS01^1: 20 steps
lem-F4-K3ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3ᵖ0∣CS01ᵖ1 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 3 (q315 c4) ∷
   rw 3 (q316 c4) ∷
   rw⁻ 2 (q317 c4) ∷
   rw⁻ 1 (q318 c4) ∷
   rw⁻ 0 (q317 c4) ∷
   rw⁻ 1 (q319 c4) ∷
   rw⁻ 4 (q317 c4) ∷
   rw⁻ 3 (q318 c4) ∷
   rw⁻ 2 (q317 c4) ∷
   rw⁻ 3 (q319 c4) ∷
   rw⁻ 0 (q316 c4) ∷
   rw 0 (q320 c4) ∷
   rw⁻ 1 (q321 c4) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q322 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q323 : Ws → Eqn
  q323 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1243 ∷ []) (lem-sym23-at243243 c4)
  q324 : Ws → Eqn
  q324 c4 = eqn (Bx0-1243 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at3443 c4)
  q325 : Ws → Eqn
  q325 c4 = eqn (Toff012 ∷ X4 ∷ []) (X4 ∷ Toff012 ∷ []) (c₃ (Toff) (X ↑))
  q326 : Ws → Eqn
  q326 c4 = eqn (Toff012 ∷ CK43 ∷ []) (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀))
  q327 : Ws → Eqn
  q327 c4 = eqn (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CCZ034 ∷ []) (wp0336 c4)
  q328 : Ws → Eqn
  q328 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1423 ∷ []) (lem-sym23-at3443 c4)
  q329 : Ws → Eqn
  q329 c4 = eqn (Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff324 ∷ []) (wl0707 (lit c4))
  q330 : Ws → Eqn
  q330 c4 = eqn (CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (wl0708 (lit c4))

-- F4 K3^0|CS12^1: 20 steps
lem-F4-K3ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3ᵖ0∣CS12ᵖ1 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw 3 (q323 c4) ∷
   rw 3 (q324 c4) ∷
   rw⁻ 2 (q325 c4) ∷
   rw⁻ 1 (q326 c4) ∷
   rw⁻ 0 (q325 c4) ∷
   rw⁻ 1 (q327 c4) ∷
   rw⁻ 4 (q325 c4) ∷
   rw⁻ 3 (q326 c4) ∷
   rw⁻ 2 (q325 c4) ∷
   rw⁻ 3 (q327 c4) ∷
   rw⁻ 0 (q324 c4) ∷
   rw 0 (q328 c4) ∷
   rw⁻ 1 (q329 c4) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q330 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

-- sym34 @122441: 5 steps
lem-sym34-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-sym34-at122441 c4 = derive (Bx0-2431 ∷ []) (Bx0-2413 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q58 c4) ∷
   rw 1 (q304 c4) ∷
   rw 0 (q195 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q331 : Ws → Eqn
  q331 c4 = eqn (Sw12 ∷ Bx0-2143 ∷ []) (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ (lit c4))
  q332 : Ws → Eqn
  q332 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4))
  q333 : Ws → Eqn
  q333 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4))

-- beta-T @12213443: 8 steps
lem-beta-T-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at12213443 c4 = derive (Bx0-2143 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q331 c4) ∷
   rw 1 (q324 c4) ∷
   rw 0 (q332 c4) ∷
   rw 1 (q333 c4) ∷
   rw 2 (q332 c4) ∷
   rw 3 (q333 c4) ∷
   rw 4 (q1 c4) ∷ []) Eq.refl

private
  q334 : Ws → Eqn
  q334 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2413 ∷ []) (lem-sym34-at122441 c4)
  q335 : Ws → Eqn
  q335 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4)
  q336 : Ws → Eqn
  q336 c4 = eqn (Bx0-2143 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4)
  q337 : Ws → Eqn
  q337 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4)
  q338 : Ws → Eqn
  q338 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4)
  q339 : Ws → Eqn
  q339 c4 = eqn (Toff134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff134 ∷ []) (wl0709 (lit c4))
  q340 : Ws → Eqn
  q340 c4 = eqn (CS12 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS12 ∷ []) (wl0710 (lit c4))
  q341 : Ws → Eqn
  q341 c4 = eqn (CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS12⁻ ∷ []) (wl0711 (lit c4))

-- F4 K3^0|CS23^1: 24 steps
lem-F4-K3ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3ᵖ0∣CS23ᵖ1 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw 3 (q334 c4) ∷
   rw 3 (q335 c4) ∷
   rw 3 (q336 c4) ∷
   rw⁻ 2 (q325 c4) ∷
   rw⁻ 1 (q326 c4) ∷
   rw⁻ 0 (q325 c4) ∷
   rw⁻ 1 (q327 c4) ∷
   rw⁻ 4 (q325 c4) ∷
   rw⁻ 3 (q326 c4) ∷
   rw⁻ 2 (q325 c4) ∷
   rw⁻ 3 (q327 c4) ∷
   rw⁻ 0 (q336 c4) ∷
   rw 0 (q337 c4) ∷
   rw 0 (q338 c4) ∷
   rw⁻ 1 (q339 c4) ∷
   re 5 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q340 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q339 c4) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q341 c4) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q342 : Ws → Eqn
  q342 c4 = eqn (S4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ S4 ∷ []) (wp0337 c4)
  q343 : Ws → Eqn
  q343 c4 = eqn (S4 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ S4 ∷ []) (wl0712 (lit c4))
  q344 : Ws → Eqn
  q344 c4 = eqn (S4 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ S4 ∷ []) (wp0338 c4)
  q345 : Ws → Eqn
  q345 c4 = eqn (S4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ S4 ∷ []) (wl0713 (lit c4))
  q346 : Ws → Eqn
  q346 c4 = eqn (S4 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ S4 ∷ []) (wp0339 c4)

-- F4 CS01^0|iI^1: 30 steps
lem-F4-CS01ᵖ0∣iIᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣iIᵖ1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 2 (q32 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   rw⁻ 8 (q32 c4) ∷
   rw⁻ 11 (q32 c4) ∷
   re 13 1 (CS03⁻ ∷ []) ∷
   rw⁻ 12 (q342 c4) ∷
   re 14 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 9 (q343 c4) ∷
   re 7 1 (CS03 ∷ []) ∷
   rw⁻ 6 (q344 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q343 c4) ∷
   rw 1 (q229 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   rw⁻ 8 (q32 c4) ∷
   rw⁻ 9 (q345 c4) ∷
   rw⁻ 6 (q346 c4) ∷
   rw⁻ 3 (q345 c4) ∷
   rw⁻ 0 (q346 c4) ∷
   rw 3 (q32 c4) ∷
   rw 4 (q32 c4) ∷
   rw 5 (q32 c4) ∷
   rw⁻ 2 (q229 c4) ∷
   rw 3 (q32 c4) ∷
   rw 4 (q32 c4) ∷
   rw 5 (q32 c4) ∷
   rw 6 (q32 c4) ∷
   re 2 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl
