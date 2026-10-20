{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D014 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0180 ; wl0181 ; wl0203 ; wl0204 ; wl0229 ; wl0230 ; wl0258 ; wl0259 ; wl0260 ; wl0261 ; wl0262 ; wl0263 ; wl0269 ; wl0278 ; wl0279 ; wl0280 ; wl0281 ; wl0282 ; wp0006 ; wp0007 ; wp0019 ; wp0022 ; wp0051 ; wp0054 ; wp0080 ; wl0288 ; wl0300 ; wl0301 ; wl0302 ; wl0303 ; wl0304 ; wl0305 ; wl0316 ; wl0317 ; wl0318 ; wl0319 ; wl0320 ; wl0321 ; wl0335 ; wl0336 ; wl0337 ; wl0341 ; wp0135 ; wp0136 ; wp0145 ; wp0161 ; wp0162 ; wp0170 ; wp0189 ; wl0364 ; wl0365 ; wl0377 ; wl0378 ; wl0402 ; wl0405 ; wl0406 ; wl0407 ; wl0420 ; wl0421 ; wp0221 ; wp0257 ; wp0269 ; wp0280 ; wl0423 ; wl0424 ; wl0425 ; wl0443 ; wl0480 ; wl0481 ; wl0482 ; wl0483 ; wl0484 ; wl0486 ; wl0489 ; wp0285 ; wp0305 ; wp0306 ; wp0317 ; wp0321 ; wp0351 ; wl0518 ; wl0547 ; wp0357 ; wp0381 ; wp0382 ; wp0389 ; wp0390 ; wp0393 ; wl0583 ; wl0619 ; wl0635 ; wl0636 ; wl0649 ; wl0650 ; wl0651 ; wl0652 ; wl0653 ; wl0677 ; wl0678 ; wl0679 ; wl0680 ; wl0681 ; wp0506 ; wp0507 ; wp0508 ; wp0523 ; wl0714 ; wl0715 ; wl0716 ; wp0566 ; wp0567 ; wp0568 ; wp0602 ; wp0603 ; wp0606 ; wp0607 ; wp0622 ; wp0623 ; wp0624 ; wl0754 ; wl0755 ; wl0787 ; wp0639 ; wp0640 ; wp0641 ; wp0653 ; wp0671 ; wp0672 ; wp0673 ; wp0674 ; wp0694 ; wl0788 ; wl0835 ; wl0836 ; wl0837 ; wp0705 ; wp0712 ; wp0713 ; wp0729 ; wp0730 ; wp0731 ; wp0738 ; wp0749 ; wl0923 ; wl0935 ; wp0762 ; wp0763 ; wp0764 ; wp0769 ; wl0961 ; wp0778 ; wp0779 ; wl1008 ; wl1009 ; wl1020 ; wl1021 ; wl1022 ; wp0810 ; wp0856 ; wp0857 ; wp0858 ; wp0859 ; wp0860 ; wp0863 ; wp0864 ; wp0899 ; wp0900 ; wp0916 ; wp0917 ; wp0918 ; wp0924 ; wp0991 ; wp1022 ; wp1023 ; wp1024 ; wp1032 ; wp1084 ; wp1085 ; wp1086 ; wp1087 ; wp1088 ; wp1101 ; wp1102)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-nat-SWbc-at0213243140 ; lem-nat-SWbc-at03102132 ; lem-nat-SWbc-at032032 ; lem-nat-SWbc-at04203243 ; lem-nat-SWbc-at13243142 ; lem-nat-SWbc-at13243241 ; lem-nat-SWbc-at14233142 ; lem-tP-at021021 ; lem-tP-at0210213443 ; lem-tP-at0213243140 ; lem-tP-at0220 ; lem-tP-at03102132 ; lem-tP-at032032 ; lem-tP-at0410213243 ; lem-tP-at04203243 ; lem-tP-at13243142 ; lem-tP-at13243241 ; lem-tP-at14233142 ; lem-tP-at14233241)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-nat-SWbc-at0310213442 ; lem-nat-SWbc-at14233241)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-nat-SWbc-at0220)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-CSdu-box-1 ; lem-CSdu-box-2 ; lem-CSdu-box-2-at0210243143 ; lem-CSdu-box-2-at122441 ; lem-CSdu-box-2-at243243 ; lem-CSu-box-1 ; lem-CSu-box-2 ; lem-CSu-box-2-at122441 ; lem-CSu-box-2-at243243 ; lem-CXbc-box ; lem-CXbc-box-at0214203143 ; lem-CXbc-box-at0330 ; lem-CXbc-box-at043043 ; lem-CXbc-box-at1221 ; lem-CXbc-box-at12243143 ; lem-CXbc-box-at13213442 ; lem-CXbc-box-at133441 ; lem-CXcb-box ; lem-CXcb-box-at0214203143 ; lem-CXcb-box-at0330 ; lem-CXcb-box-at043043 ; lem-CXcb-box-at1221 ; lem-CXcb-box-at12243143 ; lem-CXcb-box-at13213442 ; lem-CXcb-box-at133441 ; lem-QVQ-at021021 ; lem-QVQ-at03102132 ; lem-QVQ-at0410213243 ; lem-QVQ-at04203243 ; lem-QVQ-at13243142 ; lem-QVQ-at13243241 ; lem-QVQ-at14233142 ; lem-SWbc-box-at032032 ; lem-SWbc-box-at04203243 ; lem-SWbc-box-at13243142 ; lem-SWbc-box-at13243241 ; lem-SWbc-box-at14233142 ; lem-Sdu-box ; lem-Su-box ; lem-Su-box-at0210243143 ; lem-Su-box-at122441 ; lem-Su-box-at243243 ; lem-VPQ ; lem-VPQ-at0110 ; lem-VPQ-at0210243143 ; lem-VPQ-at0310243142 ; lem-VPQ-at0314203142 ; lem-VPQ-at0330 ; lem-VPQ-at043043 ; lem-VPQ-at1221 ; lem-VPQ-at122331 ; lem-VPQ-at122441 ; lem-VPQ-at132132 ; lem-VPQ-at13213442 ; lem-VPQ-at1331 ; lem-VPQ-at2332 ; lem-VPQ-at243243 ; lem-VPQ-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-CSu-box-2-at0210243143 ; lem-CXbc-box-at0210243143 ; lem-CXbc-box-at0213213440 ; lem-CXbc-box-at0214213043 ; lem-CXbc-box-at022330 ; lem-CXbc-box-at02233440 ; lem-CXbc-box-at022440 ; lem-CXbc-box-at0312213440 ; lem-CXbc-box-at0312243140 ; lem-CXbc-box-at0314203142 ; lem-CXbc-box-at0314213042 ; lem-CXbc-box-at122331 ; lem-CXbc-box-at12233441 ; lem-CXbc-box-at122441 ; lem-CXbc-box-at132132 ; lem-CXbc-box-at1331 ; lem-CXbc-box-at14213243 ; lem-CXbc-box-at1441 ; lem-CXbc-box-at2332 ; lem-CXbc-box-at243243 ; lem-CXcb-box-at0210243143 ; lem-CXcb-box-at0213213440 ; lem-CXcb-box-at0214213043 ; lem-CXcb-box-at022330 ; lem-CXcb-box-at02233440 ; lem-CXcb-box-at0312213440 ; lem-CXcb-box-at0312243140 ; lem-CXcb-box-at0314203142 ; lem-CXcb-box-at0314213042 ; lem-CXcb-box-at122331 ; lem-CXcb-box-at12233441 ; lem-CXcb-box-at122441 ; lem-CXcb-box-at132132 ; lem-CXcb-box-at1331 ; lem-CXcb-box-at14213243 ; lem-CXcb-box-at1441 ; lem-CXcb-box-at2332 ; lem-CXcb-box-at243243 ; lem-QVQ-at0210213443 ; lem-QVQ-at0213243140 ; lem-QVQ-at0220 ; lem-QVQ-at032032 ; lem-QVQ-at14233241 ; lem-SWbc-box-at0213243140 ; lem-SWbc-box-at0220 ; lem-SWbc-box-at03102132 ; lem-VPQ-at0210233441 ; lem-VPQ-at0213203441 ; lem-VPQ-at0214203143 ; lem-VPQ-at0214213043 ; lem-VPQ-at022330 ; lem-VPQ-at022440 ; lem-VPQ-at0312243140 ; lem-VPQ-at0314213042 ; lem-VPQ-at12213443 ; lem-VPQ-at12233441 ; lem-VPQ-at14213243 ; lem-VPQ-at143143 ; lem-VPQ-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-CXbc-box-at0210233441 ; lem-CXbc-box-at02102441 ; lem-CXbc-box-at02142041 ; lem-CXbc-box-at0310243142 ; lem-CXbc-box-at0310243241 ; lem-CXbc-box-at031031 ; lem-CXbc-box-at03103441 ; lem-CXbc-box-at0312203441 ; lem-CXbc-box-at0312243041 ; lem-CXbc-box-at0314213240 ; lem-CXbc-box-at03143041 ; lem-CXbc-box-at03143140 ; lem-CXbc-box-at03243240 ; lem-CXbc-box-at033440 ; lem-CXbc-box-at12213443 ; lem-CXbc-box-at143143 ; lem-CXbc-box-at233442 ; lem-CXbc-box-at2442 ; lem-CXbc-box-at3443 ; lem-CXcb-box-at0210233441 ; lem-CXcb-box-at02102441 ; lem-CXcb-box-at022440 ; lem-CXcb-box-at0310243142 ; lem-CXcb-box-at0310243241 ; lem-CXcb-box-at031031 ; lem-CXcb-box-at03103441 ; lem-CXcb-box-at0312203441 ; lem-CXcb-box-at0312243041 ; lem-CXcb-box-at0314213240 ; lem-CXcb-box-at03143041 ; lem-CXcb-box-at03143140 ; lem-CXcb-box-at03243240 ; lem-CXcb-box-at033440 ; lem-CXcb-box-at12213443 ; lem-CXcb-box-at143143 ; lem-CXcb-box-at233442 ; lem-CXcb-box-at2442 ; lem-CXcb-box-at3443 ; lem-SWbc-box-at0310213442 ; lem-SWbc-box-at14233241 ; lem-VPQ-at02102441 ; lem-VPQ-at02233440 ; lem-VPQ-at0310243241 ; lem-VPQ-at031031 ; lem-VPQ-at03103441 ; lem-VPQ-at0312203441 ; lem-VPQ-at0312243041 ; lem-VPQ-at0314213240 ; lem-VPQ-at03143140 ; lem-VPQ-at03243240 ; lem-VPQ-at033440 ; lem-VPQ-at12243143 ; lem-VPQ-at1441 ; lem-VPQ-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-CXcb-box-at02142041)

-- QVQ: 3 steps
lem-QVQ : Ws → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 0 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 1 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-VPQ c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done

-- QVQ @0210243143: 3 steps
lem-QVQ-at0210243143 : Ws → ⟪ (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-QVQ-at0210243143 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ [])
  b0 = at 0 0 (Toff213 ∷ Toff213 ∷ []) (sym (wl0180 (lit c4))) ▸
       at 1 4 (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0210243143 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done

-- QVQ @243243: 3 steps
lem-QVQ-at243243 : Ws → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at243243 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  b0 = at 0 0 (Toff023 ∷ Toff023 ∷ []) (sym (wl0203 (lit c4))) ▸
       at 1 4 (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at243243 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done

-- QVQ @122441: 3 steps
lem-QVQ-at122441 : Ws → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at122441 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Toff013 ∷ Toff013 ∷ []) (sym (wl0229 (lit c4))) ▸
       at 1 4 (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at122441 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done

-- SWbc-box: 11 steps
lem-SWbc-box : Ws → ⟪ (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-SWbc-box c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (CX23 ∷ Bx0-1234 ∷ CX23 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 4 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 2 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CXbc-box c4) ▸
       at 3 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl0259 (lit c4)) ▸
       at 1 3 (Bx0-1234 ∷ CCZ134 ∷ []) (lem-CXcb-box c4) ▸
       at 4 2 (CX23 ∷ CCZ124 ∷ []) (wl0260 (lit c4)) ▸
       at 3 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0261 (lit c4)) ▸
       at 2 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0261 (lit c4)) ▸ done

  b1 : Chain (CX23 ∷ Bx0-1234 ∷ CX23 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) (Bx0-1234 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wl0262 (lit c4)) ▸
       at 0 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CXbc-box c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done

-- SWbc-box @1221: 11 steps
lem-SWbc-box-at1221 : Ws → ⟪ (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-SWbc-box-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) (CX13 ∷ Bx0-2134 ∷ CX13 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 4 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 2 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1221 c4) ▸
       at 3 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl0279 (lit c4)) ▸
       at 1 3 (Bx0-2134 ∷ CCZ234 ∷ []) (lem-CXcb-box-at1221 c4) ▸
       at 4 2 (CX13 ∷ CCZ124 ∷ []) (wl0280 (lit c4)) ▸
       at 3 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0281 (lit c4)) ▸
       at 2 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0281 (lit c4)) ▸ done

  b1 : Chain (CX13 ∷ Bx0-2134 ∷ CX13 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) (Bx0-2134 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wl0282 (lit c4)) ▸
       at 0 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1221 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done

-- QVQ @1221: 3 steps
lem-QVQ-at1221 : Ws → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ-at1221 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 0 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 1 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at1221 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done

-- QVQ @2332: 3 steps
lem-QVQ-at2332 : Ws → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at2332 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0080 c4)) ▸
       at 1 4 (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at2332 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done

-- sym-bc @13243142: 2 steps
lem-sym-bc-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym-bc-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at13243142 c4)) ▸
       at 0 3 (Bx0-3142 ∷ []) (lem-nat-SWbc-at13243142 c4) ▸ done

-- QVQ @122331: 3 steps
lem-QVQ-at122331 : Ws → ⟪ (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-QVQ-at122331 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 0 (Toff014 ∷ Toff014 ∷ []) (sym (wp0051 c4)) ▸
       at 1 4 (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (sym (lem-VPQ-at122331 c4)) ▸
       at 4 2 [] (wp0161 c4) ▸ done

-- sym-bc @13243241: 2 steps
lem-sym-bc-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-sym-bc-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ []) (Bx0-3241 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at13243241 c4)) ▸
       at 0 3 (Bx0-3241 ∷ []) (lem-nat-SWbc-at13243241 c4) ▸ done

-- QVQ @132132: 3 steps
lem-QVQ-at132132 : Ws → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at132132 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0080 c4)) ▸
       at 1 4 (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at132132 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done

-- SWbc-box @12243143: 11 steps
lem-SWbc-box-at12243143 : Ws → ⟪ (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-SWbc-box-at12243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) (CX41 ∷ Bx0-2413 ∷ CX41 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 2 3 (Bx0-2413 ∷ CCZ234 ∷ []) (lem-CXbc-box-at12243143 c4) ▸
       at 3 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl0301 (lit c4)) ▸
       at 1 3 (Bx0-2413 ∷ CCZ123 ∷ []) (lem-CXcb-box-at12243143 c4) ▸
       at 4 2 (CX41 ∷ CCZ234 ∷ []) (wl0302 (lit c4)) ▸
       at 3 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl0303 (lit c4)) ▸
       at 2 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl0303 (lit c4)) ▸ done

  b1 : Chain (CX41 ∷ Bx0-2413 ∷ CX41 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ []) (Bx0-2413 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (wl0304 (lit c4)) ▸
       at 0 3 (Bx0-2413 ∷ CCZ234 ∷ []) (lem-CXbc-box-at12243143 c4) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸ done

-- sym-bc @14233142: 2 steps
lem-sym-bc-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-sym-bc-at14233142 c4 = run b0
  where
  b0 : Chain (Bx0-4312 ∷ []) (Bx0-4132 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at14233142 c4)) ▸
       at 0 3 (Bx0-4132 ∷ []) (lem-nat-SWbc-at14233142 c4) ▸ done

-- box-cP @14233142: 12 steps
lem-box-cP-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at14233142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4312 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0136 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wp0136 c4)) ▸
       at 2 4 (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at14233142 c4) ▸
       at 1 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at14233142 c4) ▸
       at 2 2 [] (wp0006 c4) ▸ done

-- QVQ @13213442: 3 steps
lem-QVQ-at13213442 : Ws → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at13213442 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0080 c4)) ▸
       at 1 4 (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at13213442 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done

-- QVQ @1331: 3 steps
lem-QVQ-at1331 : Ws → ⟪ (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-QVQ-at1331 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 0 (Toff014 ∷ Toff014 ∷ []) (sym (wp0051 c4)) ▸
       at 1 4 (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (sym (lem-VPQ-at1331 c4)) ▸
       at 4 2 [] (wp0161 c4) ▸ done

-- XCSX-box-1: 4 steps
lem-XCSX-box-1 : Ws → ⟪ (X1 ∷ CS01 ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-XCSX-box-1 c4 = run b0
  where
  b0 : Chain (X1 ∷ CS01 ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b0 = at 0 3 (S0 ∷ CS01⁻ ∷ []) (sym (wl0364 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4) ▸
       at 1 2 (X1 ∷ CS01 ∷ X1 ∷ []) (wl0364 (lit c4)) ▸ done

-- XCSdX-box-1: 4 steps
lem-XCSdX-box-1 : Ws → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-XCSdX-box-1 c4 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 3 (S0⁻ ∷ CS01 ∷ []) (sym (wl0365 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4) ▸
       at 1 2 (X1 ∷ CS01⁻ ∷ X1 ∷ []) (wl0365 (lit c4)) ▸ done

-- XCSX-box-2: 4 steps
lem-XCSX-box-2 : Ws → ⟪ (X2 ∷ CS02 ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-XCSX-box-2 c4 = run b0
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b0 = at 0 3 (S0 ∷ CS02⁻ ∷ []) (sym (wl0377 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4) ▸
       at 1 2 (X2 ∷ CS02 ∷ X2 ∷ []) (wl0377 (lit c4)) ▸ done

-- XCSdX-box-2: 4 steps
lem-XCSdX-box-2 : Ws → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-XCSdX-box-2 c4 = run b0
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b0 = at 0 3 (S0⁻ ∷ CS02 ∷ []) (sym (wl0378 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4) ▸
       at 1 2 (X2 ∷ CS02⁻ ∷ X2 ∷ []) (wl0378 (lit c4)) ▸ done

-- QVQ @0110: 3 steps
lem-QVQ-at0110 : Ws → ⟪ (CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Toff102 ∷ CCZ012 ∷ Toff134 ∷ []) ⟫ʷ
lem-QVQ-at0110 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ134 ∷ []) (Toff134 ∷ Toff102 ∷ CCZ012 ∷ Toff134 ∷ [])
  b0 = at 0 0 (Toff134 ∷ Toff134 ∷ []) (sym (wl0402 (lit c4))) ▸
       at 1 4 (Toff102 ∷ CCZ012 ∷ Toff134 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at0110 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done

-- SWbc-box @133441: 11 steps
lem-SWbc-box-at133441 : Ws → ⟪ (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-SWbc-box-at133441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) (CX24 ∷ Bx0-3241 ∷ CX24 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 4 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 2 3 (Bx0-3241 ∷ CCZ123 ∷ []) (lem-CXbc-box-at133441 c4) ▸
       at 3 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0319 (lit c4)) ▸
       at 1 3 (Bx0-3241 ∷ CCZ134 ∷ []) (lem-CXcb-box-at133441 c4) ▸
       at 4 2 (CX24 ∷ CCZ123 ∷ []) (wl0406 (lit c4)) ▸
       at 3 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0317 (lit c4)) ▸
       at 2 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0317 (lit c4)) ▸ done

  b1 : Chain (CX24 ∷ Bx0-3241 ∷ CX24 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ []) (Bx0-3241 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl0407 (lit c4)) ▸
       at 0 3 (Bx0-3241 ∷ CCZ123 ∷ []) (lem-CXbc-box-at133441 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done

-- box-cP @13243241: 12 steps
lem-box-cP-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at13243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3421 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 2 4 (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at13243241 c4) ▸
       at 1 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at13243241 c4) ▸
       at 2 2 [] (wp0006 c4) ▸ done

-- box-cP @021021: 12 steps
lem-box-cP-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-box-cP-at021021 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0134 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 2 4 (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-QVQ-at021021 c4) ▸
       at 1 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at021021 c4) ▸
       at 2 2 [] (wl0421 (lit c4)) ▸ done

-- SWbc-box @13213442: 11 steps
lem-SWbc-box-at13213442 : Ws → ⟪ (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-SWbc-box-at13213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) (CX14 ∷ Bx0-3142 ∷ CX14 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 2 3 (Bx0-3142 ∷ CCZ123 ∷ []) (lem-CXbc-box-at13213442 c4) ▸
       at 3 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl0303 (lit c4)) ▸
       at 1 3 (Bx0-3142 ∷ CCZ234 ∷ []) (lem-CXcb-box-at13213442 c4) ▸
       at 4 2 (CX14 ∷ CCZ123 ∷ []) (wl0424 (lit c4)) ▸
       at 3 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl0301 (lit c4)) ▸
       at 2 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl0301 (lit c4)) ▸ done

  b1 : Chain (CX14 ∷ Bx0-3142 ∷ CX14 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ []) (Bx0-3142 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl0425 (lit c4)) ▸
       at 0 3 (Bx0-3142 ∷ CCZ123 ∷ []) (lem-CXbc-box-at13213442 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done

-- box-cP @13243142: 12 steps
lem-box-cP-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at13243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3412 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0269 (lit c4))) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0269 (lit c4))) ▸
       at 2 4 (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at13243142 c4) ▸
       at 1 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at13243142 c4) ▸
       at 2 2 [] (wp0006 c4) ▸ done

-- box-cP @03102132: 12 steps
lem-box-cP-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-box-cP-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0124 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 2 4 (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-QVQ-at03102132 c4) ▸
       at 1 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at03102132 c4) ▸
       at 2 2 [] (wl0443 (lit c4)) ▸ done

-- QVQ @3443: 3 steps
lem-QVQ-at3443 : Ws → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ-at3443 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 0 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 1 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at3443 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done

-- box-cP @0410213243: 12 steps
lem-box-cP-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-box-cP-at0410213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0123 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 2 4 (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-QVQ-at0410213243 c4) ▸
       at 1 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at0410213243 c4) ▸
       at 2 2 [] (wp0306 c4) ▸ done

-- QVQ @043043: 3 steps
lem-QVQ-at043043 : Ws → ⟪ (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-QVQ-at043043 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Toff403 ∷ Toff403 ∷ []) (sym (wp0317 c4)) ▸
       at 1 4 (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at043043 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done

-- SWbc-box @043043: 11 steps
lem-SWbc-box-at043043 : Ws → ⟪ (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-SWbc-box-at043043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) (CX20 ∷ Bx4-1203 ∷ CX20 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (sym (wl0480 (lit c4))) ▸
       at 4 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (sym (wl0480 (lit c4))) ▸
       at 2 3 (Bx4-1203 ∷ CCZ123 ∷ []) (lem-CXbc-box-at043043 c4) ▸
       at 3 2 (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl0481 (lit c4)) ▸
       at 1 3 (Bx4-1203 ∷ CCZ013 ∷ []) (lem-CXcb-box-at043043 c4) ▸
       at 4 2 (CX20 ∷ CCZ123 ∷ []) (wl0482 (lit c4)) ▸
       at 3 2 (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl0483 (lit c4)) ▸
       at 2 2 (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl0483 (lit c4)) ▸ done

  b1 : Chain (CX20 ∷ Bx4-1203 ∷ CX20 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ []) (Bx4-1203 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl0484 (lit c4)) ▸
       at 0 3 (Bx4-1203 ∷ CCZ123 ∷ []) (lem-CXbc-box-at043043 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done

-- box-cP @04203243: 12 steps
lem-box-cP-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-box-cP-at04203243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1023 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0486 (lit c4)) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wl0486 (lit c4)) ▸
       at 2 4 (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-QVQ-at04203243 c4) ▸
       at 1 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at04203243 c4) ▸
       at 2 2 [] (wp0306 c4) ▸ done

-- QVQ @0330: 3 steps
lem-QVQ-at0330 : Ws → ⟪ (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-QVQ-at0330 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ [])
  b0 = at 0 0 (Toff304 ∷ Toff304 ∷ []) (sym (wp0351 c4)) ▸
       at 1 4 (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at0330 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done

-- QVQ @0314203142: 3 steps
lem-QVQ-at0314203142 : Ws → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0314203142 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 0 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 1 4 (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0314203142 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done

-- QVQ @0310243142: 3 steps
lem-QVQ-at0310243142 : Ws → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0310243142 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 0 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 1 4 (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0310243142 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done

-- sym-bc @04203243: 2 steps
lem-sym-bc-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-sym-bc-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-1203 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at04203243 c4)) ▸
       at 0 3 (Bx4-1203 ∷ []) (lem-nat-SWbc-at04203243 c4) ▸ done

-- sym-bc @032032: 2 steps
lem-sym-bc-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-sym-bc-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at032032 c4)) ▸
       at 0 3 (Bx3-1204 ∷ []) (lem-nat-SWbc-at032032 c4) ▸ done

-- SWbc-box @0330: 11 steps
lem-SWbc-box-at0330 : Ws → ⟪ (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-SWbc-box-at0330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) (CX20 ∷ Bx3-1204 ∷ CX20 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (sym (wl0480 (lit c4))) ▸
       at 4 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (sym (wl0480 (lit c4))) ▸
       at 2 3 (Bx3-1204 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0330 c4) ▸
       at 3 2 (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0382 c4) ▸
       at 1 3 (Bx3-1204 ∷ CCZ014 ∷ []) (lem-CXcb-box-at0330 c4) ▸
       at 4 2 (CX20 ∷ CCZ124 ∷ []) (wp0389 c4) ▸
       at 3 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸
       at 2 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸ done

  b1 : Chain (CX20 ∷ Bx3-1204 ∷ CX20 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ []) (Bx3-1204 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wp0390 c4) ▸
       at 0 3 (Bx3-1204 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0330 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done

-- XCSX-box-2 @243243: 4 steps
lem-XCSX-box-2-at243243 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-2-at243243 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 3 (S0 ∷ CS04⁻ ∷ []) (sym (wp0257 c4)) ▸
       at 1 2 (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ S0 ∷ []) (lem-Su-box-at243243 c4) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (wp0257 c4) ▸ done

-- XCSX-box-2 @122441: 4 steps
lem-XCSX-box-2-at122441 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-2-at122441 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 3 (S0 ∷ CS04⁻ ∷ []) (sym (wp0257 c4)) ▸
       at 1 2 (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4) ▸
       at 0 2 (Bx0-2431 ∷ S0 ∷ []) (lem-Su-box-at122441 c4) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (wp0257 c4) ▸ done

-- XCSX-box-2 @0210243143: 4 steps
lem-XCSX-box-2-at0210243143 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-2-at0210243143 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 3 (S2 ∷ CS24⁻ ∷ []) (sym (wl0583 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4) ▸
       at 0 2 (Bx2-0413 ∷ S2 ∷ []) (lem-Su-box-at0210243143 c4) ▸
       at 1 2 (X4 ∷ CS24 ∷ X4 ∷ []) (wl0583 (lit c4)) ▸ done

-- SWbc-box @0214203143: 11 steps
lem-SWbc-box-at0214203143 : Ws → ⟪ (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-SWbc-box-at0214203143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) (CX01 ∷ Bx2-4013 ∷ CX01 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 4 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 2 3 (Bx2-4013 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0214203143 c4) ▸
       at 3 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp0506 c4) ▸
       at 1 3 (Bx2-4013 ∷ CCZ134 ∷ []) (lem-CXcb-box-at0214203143 c4) ▸
       at 4 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 3 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0507 c4) ▸
       at 2 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0507 c4) ▸ done

  b1 : Chain (CX01 ∷ Bx2-4013 ∷ CX01 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (Bx2-4013 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (wp0508 c4) ▸
       at 0 3 (Bx2-4013 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0214203143 c4) ▸
       at 1 2 [] (wp0007 c4) ▸ done

-- QVQ @0214213043: 3 steps
lem-QVQ-at0214213043 : Ws → ⟪ (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-QVQ-at0214213043 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ [])
  b0 = at 0 0 (Toff203 ∷ Toff203 ∷ []) (sym (wl0635 (lit c4))) ▸
       at 1 4 (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at0214213043 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done

-- QVQ @0210233441: 3 steps
lem-QVQ-at0210233441 : Ws → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at0210233441 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  b0 = at 0 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0636 (lit c4))) ▸
       at 1 4 (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0210233441 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done

-- SWbc-box @122441: 11 steps
lem-SWbc-box-at122441 : Ws → ⟪ (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-SWbc-box-at122441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) (CX43 ∷ Bx0-2431 ∷ CX43 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 4 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 2 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-CXbc-box-at122441 c4) ▸
       at 3 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0650 (lit c4)) ▸
       at 1 3 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-CXcb-box-at122441 c4) ▸
       at 4 2 (CX43 ∷ CCZ124 ∷ []) (wl0651 (lit c4)) ▸
       at 3 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl0652 (lit c4)) ▸
       at 2 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl0652 (lit c4)) ▸ done

  b1 : Chain (CX43 ∷ Bx0-2431 ∷ CX43 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) (Bx0-2431 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wl0653 (lit c4)) ▸
       at 0 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-CXbc-box-at122441 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done

-- QVQ @12233441: 3 steps
lem-QVQ-at12233441 : Ws → ⟪ (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-QVQ-at12233441 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 0 (Toff014 ∷ Toff014 ∷ []) (sym (wp0051 c4)) ▸
       at 1 4 (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (sym (lem-VPQ-at12233441 c4)) ▸
       at 4 2 [] (wp0161 c4) ▸ done

-- SWbc-box @14213243: 11 steps
lem-SWbc-box-at14213243 : Ws → ⟪ (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-SWbc-box-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) (CX12 ∷ Bx0-4123 ∷ CX12 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 4 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 2 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-CXbc-box-at14213243 c4) ▸
       at 3 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0678 (lit c4)) ▸
       at 1 3 (Bx0-4123 ∷ CCZ234 ∷ []) (lem-CXcb-box-at14213243 c4) ▸
       at 4 2 (CX12 ∷ CCZ134 ∷ []) (wl0679 (lit c4)) ▸
       at 3 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl0680 (lit c4)) ▸
       at 2 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl0680 (lit c4)) ▸ done

  b1 : Chain (CX12 ∷ Bx0-4123 ∷ CX12 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ []) (Bx0-4123 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wl0681 (lit c4)) ▸
       at 0 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-CXbc-box-at14213243 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done

-- QVQ @143143: 3 steps
lem-QVQ-at143143 : Ws → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at143143 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Toff013 ∷ Toff013 ∷ []) (sym (wl0229 (lit c4))) ▸
       at 1 4 (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at143143 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done

-- QVQ @233442: 3 steps
lem-QVQ-at233442 : Ws → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at233442 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0080 c4)) ▸
       at 1 4 (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at233442 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done

-- SWbc-box @0210243143: 11 steps
lem-SWbc-box-at0210243143 : Ws → ⟪ (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-SWbc-box-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) (CX41 ∷ Bx2-0413 ∷ CX41 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 2 3 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0210243143 c4) ▸
       at 3 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0566 c4) ▸
       at 1 3 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-CXcb-box-at0210243143 c4) ▸
       at 4 2 (CX41 ∷ CCZ034 ∷ []) (wp0357 c4) ▸
       at 3 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0567 c4) ▸
       at 2 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0567 c4) ▸ done

  b1 : Chain (CX41 ∷ Bx2-0413 ∷ CX41 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (Bx2-0413 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (wp0568 c4) ▸
       at 0 3 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0210243143 c4) ▸
       at 1 2 [] (wp0007 c4) ▸ done

-- box-cP @0210213443: 12 steps
lem-box-cP-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-box-cP-at0210213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0143 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 2 4 (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-QVQ-at0210213443 c4) ▸
       at 1 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0210213443 c4) ▸
       at 2 2 [] (wl0421 (lit c4)) ▸ done

-- SWbc-box @243243: 11 steps
lem-SWbc-box-at243243 : Ws → ⟪ (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-SWbc-box-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) (CX42 ∷ Bx0-1423 ∷ CX42 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 4 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 2 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CXbc-box-at243243 c4) ▸
       at 3 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0317 (lit c4)) ▸
       at 1 3 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-CXcb-box-at243243 c4) ▸
       at 4 2 (CX42 ∷ CCZ134 ∷ []) (wl0318 (lit c4)) ▸
       at 3 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0319 (lit c4)) ▸
       at 2 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0319 (lit c4)) ▸ done

  b1 : Chain (CX42 ∷ Bx0-1423 ∷ CX42 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (Bx0-1423 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wl0320 (lit c4)) ▸
       at 0 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CXbc-box-at243243 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done

-- SWbc-box @1441: 11 steps
lem-SWbc-box-at1441 : Ws → ⟪ (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-SWbc-box-at1441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) (CX23 ∷ Bx0-4231 ∷ CX23 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 4 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 2 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1441 c4) ▸
       at 3 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl0259 (lit c4)) ▸
       at 1 3 (Bx0-4231 ∷ CCZ134 ∷ []) (lem-CXcb-box-at1441 c4) ▸
       at 4 2 (CX23 ∷ CCZ124 ∷ []) (wl0260 (lit c4)) ▸
       at 3 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0261 (lit c4)) ▸
       at 2 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0261 (lit c4)) ▸ done

  b1 : Chain (CX23 ∷ Bx0-4231 ∷ CX23 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) (Bx0-4231 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wl0262 (lit c4)) ▸
       at 0 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1441 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done

-- box-cP @14233241: 12 steps
lem-box-cP-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at14233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4321 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 2 4 (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at14233241 c4) ▸
       at 1 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at14233241 c4) ▸
       at 2 2 [] (wp0006 c4) ▸ done

-- QVQ @12213443: 3 steps
lem-QVQ-at12213443 : Ws → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ-at12213443 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 0 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 1 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at12213443 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done

-- F4-CS0-S2: 14 steps
lem-F4-CS0-S2 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ Bx2-0413 ∷ S2 ∷ CS24⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S2 ∷ CS24⁻ ∷ X4 ∷ []) (sym (wl0714 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 3 (S2 ∷ CS24⁻ ∷ CS03⁻ ∷ []) (wp0606 c4) ▸
       at 4 3 (S2 ∷ CS24⁻ ∷ Toff314 ∷ []) (sym (wl0715 (lit c4))) ▸
       at 3 3 (S2 ∷ CS24⁻ ∷ CS03 ∷ []) (wp0607 c4) ▸
       at 2 3 (S2 ∷ CS24⁻ ∷ Toff314 ∷ []) (sym (wl0715 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ S2 ∷ CS24⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b1 = at 1 2 (S2 ∷ Bx2-0413 ∷ []) (sym (lem-Su-box-at0210243143 c4)) ▸
       at 2 2 (CS24⁻ ∷ Bx2-0413 ∷ []) (sym (lem-CSdu-box-2-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 3 (CS24 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸ done

-- F4-CS1-S0: 14 steps
lem-F4-CS1-S0 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) (X4 ∷ Bx0-1423 ∷ S0 ∷ CS04⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S0 ∷ CS04⁻ ∷ X4 ∷ []) (sym (wp0602 c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 3 (S0 ∷ CS04⁻ ∷ CS13⁻ ∷ []) (wp0622 c4) ▸
       at 4 3 (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) (sym (wp0623 c4)) ▸
       at 3 3 (S0 ∷ CS04⁻ ∷ CS13 ∷ []) (wp0624 c4) ▸
       at 2 3 (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) (sym (wp0623 c4)) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ S0 ∷ CS04⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 1 2 (S0 ∷ Bx0-1423 ∷ []) (sym (lem-Su-box-at243243 c4)) ▸
       at 2 2 (CS04⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CSdu-box-2-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 3 (CS04 ∷ X4 ∷ []) (sym (wp0603 c4)) ▸ done

-- F4-CS2-S0: 14 steps
lem-F4-CS2-S0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) (X4 ∷ Bx0-2431 ∷ S0 ∷ CS04⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S0 ∷ CS04⁻ ∷ X4 ∷ []) (sym (wp0602 c4)) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 3 (S0 ∷ CS04⁻ ∷ CS12⁻ ∷ []) (wp0639 c4) ▸
       at 4 3 (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) (sym (wp0640 c4)) ▸
       at 3 3 (S0 ∷ CS04⁻ ∷ CS12 ∷ []) (wp0641 c4) ▸
       at 2 3 (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) (sym (wp0640 c4)) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ S0 ∷ CS04⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 1 2 (S0 ∷ Bx0-2431 ∷ []) (sym (lem-Su-box-at122441 c4)) ▸
       at 2 2 (CS04⁻ ∷ Bx0-2431 ∷ []) (sym (lem-CSdu-box-2-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 3 (CS04 ∷ X4 ∷ []) (sym (wp0603 c4)) ▸ done

-- SWbc-box @0314213042: 11 steps
lem-SWbc-box-at0314213042 : Ws → ⟪ (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-SWbc-box-at0314213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) (CX10 ∷ Bx3-4102 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 4 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 2 3 (Bx3-4102 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0314213042 c4) ▸
       at 3 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0671 c4) ▸
       at 1 3 (Bx3-4102 ∷ CCZ024 ∷ []) (lem-CXcb-box-at0314213042 c4) ▸
       at 4 2 (CX10 ∷ CCZ124 ∷ []) (wp0672 c4) ▸
       at 3 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸
       at 2 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸ done

  b1 : Chain (CX10 ∷ Bx3-4102 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (Bx3-4102 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wp0674 c4) ▸
       at 0 3 (Bx3-4102 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0314213042 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done

-- QVQ @0213203441: 3 steps
lem-QVQ-at0213203441 : Ws → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at0213203441 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  b0 = at 0 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0636 (lit c4))) ▸
       at 1 4 (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0213203441 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done

-- SWbc-box @0314203142: 11 steps
lem-SWbc-box-at0314203142 : Ws → ⟪ (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-SWbc-box-at0314203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) (CX01 ∷ Bx3-4012 ∷ CX01 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 4 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 2 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0314203142 c4) ▸
       at 3 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸
       at 1 3 (Bx3-4012 ∷ CCZ124 ∷ []) (lem-CXcb-box-at0314203142 c4) ▸
       at 4 2 (CX01 ∷ CCZ024 ∷ []) (wp0022 c4) ▸
       at 3 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0671 c4) ▸
       at 2 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0671 c4) ▸ done

  b1 : Chain (CX01 ∷ Bx3-4012 ∷ CX01 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ []) (Bx3-4012 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (wp0694 c4) ▸
       at 0 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0314203142 c4) ▸
       at 1 2 [] (wp0135 c4) ▸ done

-- QVQ @0314213042: 3 steps
lem-QVQ-at0314213042 : Ws → ⟪ (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-QVQ-at0314213042 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ [])
  b0 = at 0 0 (Toff302 ∷ Toff302 ∷ []) (sym (wl0787 (lit c4))) ▸
       at 1 4 (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at0314213042 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done

-- SWbc-box @0214213043: 11 steps
lem-SWbc-box-at0214213043 : Ws → ⟪ (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-SWbc-box-at0214213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) (CX10 ∷ Bx2-4103 ∷ CX10 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 4 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 2 3 (Bx2-4103 ∷ CCZ134 ∷ []) (lem-CXbc-box-at0214213043 c4) ▸
       at 3 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0507 c4) ▸
       at 1 3 (Bx2-4103 ∷ CCZ034 ∷ []) (lem-CXcb-box-at0214213043 c4) ▸
       at 4 2 (CX10 ∷ CCZ134 ∷ []) (wp0712 c4) ▸
       at 3 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp0506 c4) ▸
       at 2 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp0506 c4) ▸ done

  b1 : Chain (CX10 ∷ Bx2-4103 ∷ CX10 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) (Bx2-4103 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wp0713 c4) ▸
       at 0 3 (Bx2-4103 ∷ CCZ134 ∷ []) (lem-CXbc-box-at0214213043 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done

-- SWbc-box @1331: 11 steps
lem-SWbc-box-at1331 : Ws → ⟪ (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-SWbc-box-at1331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) (CX21 ∷ Bx0-3214 ∷ CX21 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 4 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 2 3 (Bx0-3214 ∷ CCZ234 ∷ []) (lem-CXbc-box-at1331 c4) ▸
       at 3 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl0680 (lit c4)) ▸
       at 1 3 (Bx0-3214 ∷ CCZ134 ∷ []) (lem-CXcb-box-at1331 c4) ▸
       at 4 2 (CX21 ∷ CCZ234 ∷ []) (wl0836 (lit c4)) ▸
       at 3 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0678 (lit c4)) ▸
       at 2 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0678 (lit c4)) ▸ done

  b1 : Chain (CX21 ∷ Bx0-3214 ∷ CX21 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ []) (Bx0-3214 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (wl0837 (lit c4)) ▸
       at 0 3 (Bx0-3214 ∷ CCZ234 ∷ []) (lem-CXbc-box-at1331 c4) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸ done

-- box-cP @032032: 12 steps
lem-box-cP-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-box-cP-at032032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1024 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 2 4 (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-QVQ-at032032 c4) ▸
       at 1 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at032032 c4) ▸
       at 2 2 [] (wl0443 (lit c4)) ▸ done

-- SWbc-box @0312243140: 11 steps
lem-SWbc-box-at0312243140 : Ws → ⟪ (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-SWbc-box-at0312243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) (CX41 ∷ Bx3-2410 ∷ CX41 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 2 3 (Bx3-2410 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0312243140 c4) ▸
       at 3 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸
       at 1 3 (Bx3-2410 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0312243140 c4) ▸
       at 4 2 (CX41 ∷ CCZ024 ∷ []) (wp0285 c4) ▸
       at 3 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp0730 c4) ▸
       at 2 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp0730 c4) ▸ done

  b1 : Chain (CX41 ∷ Bx3-2410 ∷ CX41 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ []) (Bx3-2410 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (wp0731 c4) ▸
       at 0 3 (Bx3-2410 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0312243140 c4) ▸
       at 1 2 [] (wp0135 c4) ▸ done

-- SWbc-box @0312213440: 11 steps
lem-SWbc-box-at0312213440 : Ws → ⟪ (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-SWbc-box-at0312213440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) (CX14 ∷ Bx3-2140 ∷ CX14 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 2 3 (Bx3-2140 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0312213440 c4) ▸
       at 3 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp0730 c4) ▸
       at 1 3 (Bx3-2140 ∷ CCZ024 ∷ []) (lem-CXcb-box-at0312213440 c4) ▸
       at 4 2 (CX14 ∷ CCZ012 ∷ []) (wp0145 c4) ▸
       at 3 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸
       at 2 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸ done

  b1 : Chain (CX14 ∷ Bx3-2140 ∷ CX14 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (Bx3-2140 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wp0738 c4) ▸
       at 0 3 (Bx3-2140 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0312213440 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done

-- QVQ @0312243140: 3 steps
lem-QVQ-at0312243140 : Ws → ⟪ (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-QVQ-at0312243140 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 1 4 (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at0312243140 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done

-- SWbc-box @132132: 11 steps
lem-SWbc-box-at132132 : Ws → ⟪ (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-SWbc-box-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) (CX12 ∷ Bx0-3124 ∷ CX12 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 4 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 2 3 (Bx0-3124 ∷ CCZ134 ∷ []) (lem-CXbc-box-at132132 c4) ▸
       at 3 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0678 (lit c4)) ▸
       at 1 3 (Bx0-3124 ∷ CCZ234 ∷ []) (lem-CXcb-box-at132132 c4) ▸
       at 4 2 (CX12 ∷ CCZ134 ∷ []) (wl0679 (lit c4)) ▸
       at 3 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl0680 (lit c4)) ▸
       at 2 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl0680 (lit c4)) ▸ done

  b1 : Chain (CX12 ∷ Bx0-3124 ∷ CX12 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ []) (Bx0-3124 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wl0681 (lit c4)) ▸
       at 0 3 (Bx0-3124 ∷ CCZ134 ∷ []) (lem-CXbc-box-at132132 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done

-- SWbc-box @022330: 11 steps
lem-SWbc-box-at022330 : Ws → ⟪ (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-SWbc-box-at022330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) (CX30 ∷ Bx2-1304 ∷ CX30 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX30 ∷ CX03 ∷ CX30 ∷ []) (sym (wl0923 (lit c4))) ▸
       at 4 1 (CX30 ∷ CX03 ∷ CX30 ∷ []) (sym (wl0923 (lit c4))) ▸
       at 2 3 (Bx2-1304 ∷ CCZ134 ∷ []) (lem-CXbc-box-at022330 c4) ▸
       at 3 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0762 c4) ▸
       at 1 3 (Bx2-1304 ∷ CCZ014 ∷ []) (lem-CXcb-box-at022330 c4) ▸
       at 4 2 (CX30 ∷ CCZ134 ∷ []) (wp0705 c4) ▸
       at 3 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0763 c4) ▸
       at 2 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0763 c4) ▸ done

  b1 : Chain (CX30 ∷ Bx2-1304 ∷ CX30 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (Bx2-1304 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wp0764 c4) ▸
       at 0 3 (Bx2-1304 ∷ CCZ134 ∷ []) (lem-CXbc-box-at022330 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done

-- box-cP @0220: 12 steps
lem-box-cP-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-box-cP-at0220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1034 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 2 4 (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-QVQ-at0220 c4) ▸
       at 1 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0220 c4) ▸
       at 2 2 [] (wl0421 (lit c4)) ▸ done

-- sym-bc @0213243140: 2 steps
lem-sym-bc-at0213243140 : Ws → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-sym-bc-at0213243140 c4 = run b0
  where
  b0 : Chain (Bx2-3410 ∷ []) (Bx2-3140 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0213243140 c4)) ▸
       at 0 3 (Bx2-3140 ∷ []) (lem-nat-SWbc-at0213243140 c4) ▸ done

-- SWbc-box @0213213440: 11 steps
lem-SWbc-box-at0213213440 : Ws → ⟪ (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-SWbc-box-at0213213440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) (CX14 ∷ Bx2-3140 ∷ CX14 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 2 3 (Bx2-3140 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0213213440 c4) ▸
       at 3 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0567 c4) ▸
       at 1 3 (Bx2-3140 ∷ CCZ034 ∷ []) (lem-CXcb-box-at0213213440 c4) ▸
       at 4 2 (CX14 ∷ CCZ013 ∷ []) (wp0189 c4) ▸
       at 3 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0566 c4) ▸
       at 2 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0566 c4) ▸ done

  b1 : Chain (CX14 ∷ Bx2-3140 ∷ CX14 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ []) (Bx2-3140 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wp0769 c4) ▸
       at 0 3 (Bx2-3140 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0213213440 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done

-- box-cP @0213243140: 12 steps
lem-box-cP-at0213243140 : Ws → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-box-cP-at0213243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3410 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0935 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0935 (lit c4))) ▸
       at 2 4 (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-QVQ-at0213243140 c4) ▸
       at 1 2 (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0213243140 c4) ▸
       at 2 2 [] (wl0420 (lit c4)) ▸ done

-- sym-bc @0220: 2 steps
lem-sym-bc-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym-bc-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at0220 c4)) ▸
       at 0 3 (Bx2-1304 ∷ []) (lem-nat-SWbc-at0220 c4) ▸ done

-- QVQ @022330: 3 steps
lem-QVQ-at022330 : Ws → ⟪ (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-QVQ-at022330 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ [])
  b0 = at 0 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0019 c4)) ▸
       at 1 4 (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at022330 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done

-- SWbc-box @122331: 11 steps
lem-SWbc-box-at122331 : Ws → ⟪ (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-SWbc-box-at122331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) (CX31 ∷ Bx0-2314 ∷ CX31 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 4 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 2 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-CXbc-box-at122331 c4) ▸
       at 3 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0281 (lit c4)) ▸
       at 1 3 (Bx0-2314 ∷ CCZ124 ∷ []) (lem-CXcb-box-at122331 c4) ▸
       at 4 2 (CX31 ∷ CCZ234 ∷ []) (wl0336 (lit c4)) ▸
       at 3 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl0279 (lit c4)) ▸
       at 2 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl0279 (lit c4)) ▸ done

  b1 : Chain (CX31 ∷ Bx0-2314 ∷ CX31 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) (Bx0-2314 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (wl0337 (lit c4)) ▸
       at 0 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-CXbc-box-at122331 c4) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸ done

-- QVQ @14213243: 3 steps
lem-QVQ-at14213243 : Ws → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at14213243 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  b0 = at 0 0 (Toff023 ∷ Toff023 ∷ []) (sym (wl0203 (lit c4))) ▸
       at 1 4 (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at14213243 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done

-- SWbc-box @12233441: 11 steps
lem-SWbc-box-at12233441 : Ws → ⟪ (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-SWbc-box-at12233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) (CX34 ∷ Bx0-2341 ∷ CX34 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 4 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 2 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-CXbc-box-at12233441 c4) ▸
       at 3 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl0652 (lit c4)) ▸
       at 1 3 (Bx0-2341 ∷ CCZ124 ∷ []) (lem-CXcb-box-at12233441 c4) ▸
       at 4 2 (CX34 ∷ CCZ123 ∷ []) (wl1008 (lit c4)) ▸
       at 3 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0650 (lit c4)) ▸
       at 2 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0650 (lit c4)) ▸ done

  b1 : Chain (CX34 ∷ Bx0-2341 ∷ CX34 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ []) (Bx0-2341 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl1009 (lit c4)) ▸
       at 0 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-CXbc-box-at12233441 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done

-- SWbc-box @2332: 11 steps
lem-SWbc-box-at2332 : Ws → ⟪ (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-SWbc-box-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) (CX32 ∷ Bx0-1324 ∷ CX32 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (sym (wl1020 (lit c4))) ▸
       at 4 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (sym (wl1020 (lit c4))) ▸
       at 2 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CXbc-box-at2332 c4) ▸
       at 3 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0261 (lit c4)) ▸
       at 1 3 (Bx0-1324 ∷ CCZ124 ∷ []) (lem-CXcb-box-at2332 c4) ▸
       at 4 2 (CX32 ∷ CCZ134 ∷ []) (wl1021 (lit c4)) ▸
       at 3 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl0259 (lit c4)) ▸
       at 2 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl0259 (lit c4)) ▸ done

  b1 : Chain (CX32 ∷ Bx0-1324 ∷ CX32 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) (Bx0-1324 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wl1022 (lit c4)) ▸
       at 0 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CXbc-box-at2332 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done

-- F2-S0-CS1: 11 steps
lem-F2-S0-CS1 : Ws → ⟪ (CS04 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS04 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4) ▸
       at 1 2 (Toff324 ∷ CS04 ∷ []) (wp0393 c4) ▸
       at 2 2 (CS13 ∷ CS04 ∷ []) (wp0856 c4) ▸
       at 3 2 (Toff324 ∷ CS04 ∷ []) (wp0393 c4) ▸
       at 4 2 (CS13⁻ ∷ CS04 ∷ []) (wp0857 c4) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS04 ∷ []) (Sb0-1-42-3 ∷ CS04 ∷ [])
  b1 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

-- F2-S0-CS2: 11 steps
lem-F2-S0-CS2 : Ws → ⟪ (CS04 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS04 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4) ▸
       at 1 2 (Toff134 ∷ CS04 ∷ []) (wp0858 c4) ▸
       at 2 2 (CS12 ∷ CS04 ∷ []) (wp0859 c4) ▸
       at 3 2 (Toff134 ∷ CS04 ∷ []) (wp0858 c4) ▸
       at 4 2 (CS12⁻ ∷ CS04 ∷ []) (wp0860 c4) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS04 ∷ []) (Sb0-2-43-1 ∷ CS04 ∷ [])
  b1 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

-- F2-S2-CS0: 11 steps
lem-F2-S2-CS0 : Ws → ⟪ (CS24 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS24 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS24 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4) ▸
       at 1 2 (Toff314 ∷ CS24 ∷ []) (wl0754 (lit c4)) ▸
       at 2 2 (CS03 ∷ CS24 ∷ []) (sym (wp0863 c4)) ▸
       at 3 2 (Toff314 ∷ CS24 ∷ []) (wl0754 (lit c4)) ▸
       at 4 2 (CS03⁻ ∷ CS24 ∷ []) (sym (wp0864 c4)) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS24 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ [])
  b1 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

-- sym-bc @03102132: 2 steps
lem-sym-bc-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym-bc-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at03102132 c4)) ▸
       at 0 3 (Bx3-0214 ∷ []) (lem-nat-SWbc-at03102132 c4) ▸ done

-- QVQ @0214203143: 3 steps
lem-QVQ-at0214203143 : Ws → ⟪ (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-QVQ-at0214203143 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ [])
  b0 = at 0 0 (Toff213 ∷ Toff213 ∷ []) (sym (wl0180 (lit c4))) ▸
       at 1 4 (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0214203143 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done

-- SWbc-box @02233440: 11 steps
lem-SWbc-box-at02233440 : Ws → ⟪ (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-SWbc-box-at02233440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) (CX34 ∷ Bx2-1340 ∷ CX34 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 4 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 2 3 (Bx2-1340 ∷ CCZ013 ∷ []) (lem-CXbc-box-at02233440 c4) ▸
       at 3 2 (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp0916 c4) ▸
       at 1 3 (Bx2-1340 ∷ CCZ014 ∷ []) (lem-CXcb-box-at02233440 c4) ▸
       at 4 2 (CX34 ∷ CCZ013 ∷ []) (wp0523 c4) ▸
       at 3 2 (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0917 c4) ▸
       at 2 2 (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0917 c4) ▸ done

  b1 : Chain (CX34 ∷ Bx2-1340 ∷ CX34 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) (Bx2-1340 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wp0918 c4) ▸
       at 0 3 (Bx2-1340 ∷ CCZ013 ∷ []) (lem-CXbc-box-at02233440 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done

-- QVQ @022440: 3 steps
lem-QVQ-at022440 : Ws → ⟪ (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-QVQ-at022440 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ [])
  b0 = at 0 0 (Toff203 ∷ Toff203 ∷ []) (sym (wl0635 (lit c4))) ▸
       at 1 4 (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at022440 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done

-- SWbc-box @022440: 11 steps
lem-SWbc-box-at022440 : Ws → ⟪ (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-SWbc-box-at022440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) (CX43 ∷ Bx2-1430 ∷ CX43 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 4 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 2 3 (Bx2-1430 ∷ CCZ014 ∷ []) (lem-CXbc-box-at022440 c4) ▸
       at 3 2 (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0917 c4) ▸
       at 1 3 (Bx2-1430 ∷ CCZ013 ∷ []) (lem-CXcb-box-at022440 c4) ▸
       at 4 2 (CX43 ∷ CCZ014 ∷ []) (wp0810 c4) ▸
       at 3 2 (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp0916 c4) ▸
       at 2 2 (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp0916 c4) ▸ done

  b1 : Chain (CX43 ∷ Bx2-1430 ∷ CX43 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ []) (Bx2-1430 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0924 c4) ▸
       at 0 3 (Bx2-1430 ∷ CCZ014 ∷ []) (lem-CXbc-box-at022440 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done

-- QVQ @02233440: 3 steps
lem-QVQ-at02233440 : Ws → ⟪ (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-QVQ-at02233440 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ [])
  b0 = at 0 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0019 c4)) ▸
       at 1 4 (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at02233440 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done

-- QVQ @1441: 3 steps
lem-QVQ-at1441 : Ws → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at1441 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Toff013 ∷ Toff013 ∷ []) (sym (wl0229 (lit c4))) ▸
       at 1 4 (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at1441 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done

-- SWbc-box @0210233441: 11 steps
lem-SWbc-box-at0210233441 : Ws → ⟪ (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-SWbc-box-at0210233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) (CX34 ∷ Bx2-0341 ∷ CX34 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 4 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 2 3 (Bx2-0341 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0210233441 c4) ▸
       at 3 2 (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp0916 c4) ▸
       at 1 3 (Bx2-0341 ∷ CCZ014 ∷ []) (lem-CXcb-box-at0210233441 c4) ▸
       at 4 2 (CX34 ∷ CCZ013 ∷ []) (wp0523 c4) ▸
       at 3 2 (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0917 c4) ▸
       at 2 2 (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0917 c4) ▸ done

  b1 : Chain (CX34 ∷ Bx2-0341 ∷ CX34 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) (Bx2-0341 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wp0918 c4) ▸
       at 0 3 (Bx2-0341 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0210233441 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done

-- QVQ @02102441: 3 steps
lem-QVQ-at02102441 : Ws → ⟪ (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-QVQ-at02102441 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ [])
  b0 = at 0 0 (Toff213 ∷ Toff213 ∷ []) (sym (wl0180 (lit c4))) ▸
       at 1 4 (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at02102441 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done

-- SWbc-box @02102441: 11 steps
lem-SWbc-box-at02102441 : Ws → ⟪ (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-SWbc-box-at02102441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) (CX43 ∷ Bx2-0431 ∷ CX43 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 4 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 2 3 (Bx2-0431 ∷ CCZ014 ∷ []) (lem-CXbc-box-at02102441 c4) ▸
       at 3 2 (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0917 c4) ▸
       at 1 3 (Bx2-0431 ∷ CCZ013 ∷ []) (lem-CXcb-box-at02102441 c4) ▸
       at 4 2 (CX43 ∷ CCZ014 ∷ []) (wp0810 c4) ▸
       at 3 2 (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp0916 c4) ▸
       at 2 2 (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp0916 c4) ▸ done

  b1 : Chain (CX43 ∷ Bx2-0431 ∷ CX43 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ []) (Bx2-0431 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0924 c4) ▸
       at 0 3 (Bx2-0431 ∷ CCZ014 ∷ []) (lem-CXbc-box-at02102441 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done

-- SWbc-box @233442: 11 steps
lem-SWbc-box-at233442 : Ws → ⟪ (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-SWbc-box-at233442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) (CX34 ∷ Bx0-1342 ∷ CX34 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 4 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 2 3 (Bx0-1342 ∷ CCZ123 ∷ []) (lem-CXbc-box-at233442 c4) ▸
       at 3 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl0652 (lit c4)) ▸
       at 1 3 (Bx0-1342 ∷ CCZ124 ∷ []) (lem-CXcb-box-at233442 c4) ▸
       at 4 2 (CX34 ∷ CCZ123 ∷ []) (wl1008 (lit c4)) ▸
       at 3 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0650 (lit c4)) ▸
       at 2 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0650 (lit c4)) ▸ done

  b1 : Chain (CX34 ∷ Bx0-1342 ∷ CX34 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ []) (Bx0-1342 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl1009 (lit c4)) ▸
       at 0 3 (Bx0-1342 ∷ CCZ123 ∷ []) (lem-CXbc-box-at233442 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done

-- QVQ @2442: 3 steps
lem-QVQ-at2442 : Ws → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at2442 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  b0 = at 0 0 (Toff023 ∷ Toff023 ∷ []) (sym (wl0203 (lit c4))) ▸
       at 1 4 (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at2442 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done

-- SWbc-box @2442: 11 steps
lem-SWbc-box-at2442 : Ws → ⟪ (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-SWbc-box-at2442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) (CX43 ∷ Bx0-1432 ∷ CX43 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 4 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 2 3 (Bx0-1432 ∷ CCZ124 ∷ []) (lem-CXbc-box-at2442 c4) ▸
       at 3 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0650 (lit c4)) ▸
       at 1 3 (Bx0-1432 ∷ CCZ123 ∷ []) (lem-CXcb-box-at2442 c4) ▸
       at 4 2 (CX43 ∷ CCZ124 ∷ []) (wl0651 (lit c4)) ▸
       at 3 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl0652 (lit c4)) ▸
       at 2 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl0652 (lit c4)) ▸ done

  b1 : Chain (CX43 ∷ Bx0-1432 ∷ CX43 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) (Bx0-1432 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wl0653 (lit c4)) ▸
       at 0 3 (Bx0-1432 ∷ CCZ124 ∷ []) (lem-CXbc-box-at2442 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done

-- SWbc-box @143143: 11 steps
lem-SWbc-box-at143143 : Ws → ⟪ (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-SWbc-box-at143143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) (CX21 ∷ Bx0-4213 ∷ CX21 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 4 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 2 3 (Bx0-4213 ∷ CCZ234 ∷ []) (lem-CXbc-box-at143143 c4) ▸
       at 3 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl0680 (lit c4)) ▸
       at 1 3 (Bx0-4213 ∷ CCZ134 ∷ []) (lem-CXcb-box-at143143 c4) ▸
       at 4 2 (CX21 ∷ CCZ234 ∷ []) (wl0836 (lit c4)) ▸
       at 3 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0678 (lit c4)) ▸
       at 2 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0678 (lit c4)) ▸ done

  b1 : Chain (CX21 ∷ Bx0-4213 ∷ CX21 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ []) (Bx0-4213 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (wl0837 (lit c4)) ▸
       at 0 3 (Bx0-4213 ∷ CCZ234 ∷ []) (lem-CXbc-box-at143143 c4) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸ done

-- SWbc-box @12213443: 11 steps
lem-SWbc-box-at12213443 : Ws → ⟪ (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-SWbc-box-at12213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) (CX14 ∷ Bx0-2143 ∷ CX14 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 2 3 (Bx0-2143 ∷ CCZ123 ∷ []) (lem-CXbc-box-at12213443 c4) ▸
       at 3 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl0303 (lit c4)) ▸
       at 1 3 (Bx0-2143 ∷ CCZ234 ∷ []) (lem-CXcb-box-at12213443 c4) ▸
       at 4 2 (CX14 ∷ CCZ123 ∷ []) (wl0424 (lit c4)) ▸
       at 3 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl0301 (lit c4)) ▸
       at 2 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl0301 (lit c4)) ▸ done

  b1 : Chain (CX14 ∷ Bx0-2143 ∷ CX14 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ []) (Bx0-2143 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl0425 (lit c4)) ▸
       at 0 3 (Bx0-2143 ∷ CCZ123 ∷ []) (lem-CXbc-box-at12213443 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done

-- QVQ @12243143: 3 steps
lem-QVQ-at12243143 : Ws → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Toff013 ∷ Toff013 ∷ []) (sym (wl0229 (lit c4))) ▸
       at 1 4 (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at12243143 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done

-- sym-bc @14233241: 2 steps
lem-sym-bc-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-sym-bc-at14233241 c4 = run b0
  where
  b0 : Chain (Bx0-4321 ∷ []) (Bx0-4231 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at14233241 c4)) ▸
       at 0 3 (Bx0-4231 ∷ []) (lem-nat-SWbc-at14233241 c4) ▸ done

-- SWbc-box @03143140: 11 steps
lem-SWbc-box-at03143140 : Ws → ⟪ (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-SWbc-box-at03143140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) (CX21 ∷ Bx3-4210 ∷ CX21 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 4 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 2 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-CXbc-box-at03143140 c4) ▸
       at 3 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 1 3 (Bx3-4210 ∷ CCZ014 ∷ []) (lem-CXcb-box-at03143140 c4) ▸
       at 4 2 (CX21 ∷ CCZ024 ∷ []) (wp0749 c4) ▸
       at 3 2 (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0899 c4) ▸
       at 2 2 (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0899 c4) ▸ done

  b1 : Chain (CX21 ∷ Bx3-4210 ∷ CX21 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) (Bx3-4210 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (wp0991 c4) ▸
       at 0 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-CXbc-box-at03143140 c4) ▸
       at 1 2 [] (wp0135 c4) ▸ done

-- QVQ @0314213240: 3 steps
lem-QVQ-at0314213240 : Ws → ⟪ (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-QVQ-at0314213240 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ [])
  b0 = at 0 0 (Toff302 ∷ Toff302 ∷ []) (sym (wl0787 (lit c4))) ▸
       at 1 4 (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at0314213240 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done

-- SWbc-box @0314213240: 11 steps
lem-SWbc-box-at0314213240 : Ws → ⟪ (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-SWbc-box-at0314213240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) (CX12 ∷ Bx3-4120 ∷ CX12 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 4 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 2 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0314213240 c4) ▸
       at 3 2 (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0899 c4) ▸
       at 1 3 (Bx3-4120 ∷ CCZ024 ∷ []) (lem-CXcb-box-at0314213240 c4) ▸
       at 4 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 3 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 2 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸ done

  b1 : Chain (CX12 ∷ Bx3-4120 ∷ CX12 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) (Bx3-4120 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0900 c4) ▸
       at 0 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0314213240 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done

-- QVQ @03143140: 3 steps
lem-QVQ-at03143140 : Ws → ⟪ (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-QVQ-at03143140 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 1 4 (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at03143140 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done

-- QVQ @03243240: 3 steps
lem-QVQ-at03243240 : Ws → ⟪ (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-QVQ-at03243240 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ [])
  b0 = at 0 0 (Toff302 ∷ Toff302 ∷ []) (sym (wl0787 (lit c4))) ▸
       at 1 4 (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at03243240 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done

-- SWbc-box @033440: 11 steps
lem-SWbc-box-at033440 : Ws → ⟪ (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-SWbc-box-at033440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) (CX24 ∷ Bx3-1240 ∷ CX24 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 4 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 2 3 (Bx3-1240 ∷ CCZ012 ∷ []) (lem-CXbc-box-at033440 c4) ▸
       at 3 2 (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1022 c4) ▸
       at 1 3 (Bx3-1240 ∷ CCZ014 ∷ []) (lem-CXcb-box-at033440 c4) ▸
       at 4 2 (CX24 ∷ CCZ012 ∷ []) (wp0170 c4) ▸
       at 3 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸
       at 2 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸ done

  b1 : Chain (CX24 ∷ Bx3-1240 ∷ CX24 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ []) (Bx3-1240 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wp1024 c4) ▸
       at 0 3 (Bx3-1240 ∷ CCZ012 ∷ []) (lem-CXbc-box-at033440 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done

-- SWbc-box @03243240: 11 steps
lem-SWbc-box-at03243240 : Ws → ⟪ (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-SWbc-box-at03243240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) (CX42 ∷ Bx3-1420 ∷ CX42 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 4 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 2 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-CXbc-box-at03243240 c4) ▸
       at 3 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸
       at 1 3 (Bx3-1420 ∷ CCZ012 ∷ []) (lem-CXcb-box-at03243240 c4) ▸
       at 4 2 (CX42 ∷ CCZ014 ∷ []) (wp0269 c4) ▸
       at 3 2 (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1022 c4) ▸
       at 2 2 (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1022 c4) ▸ done

  b1 : Chain (CX42 ∷ Bx3-1420 ∷ CX42 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ []) (Bx3-1420 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp1032 c4) ▸
       at 0 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-CXbc-box-at03243240 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done

-- QVQ @033440: 3 steps
lem-QVQ-at033440 : Ws → ⟪ (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-QVQ-at033440 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ [])
  b0 = at 0 0 (Toff304 ∷ Toff304 ∷ []) (sym (wp0351 c4)) ▸
       at 1 4 (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at033440 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done

-- SWbc-box @03103441: 11 steps
lem-SWbc-box-at03103441 : Ws → ⟪ (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-SWbc-box-at03103441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) (CX24 ∷ Bx3-0241 ∷ CX24 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 4 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 2 3 (Bx3-0241 ∷ CCZ012 ∷ []) (lem-CXbc-box-at03103441 c4) ▸
       at 3 2 (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1022 c4) ▸
       at 1 3 (Bx3-0241 ∷ CCZ014 ∷ []) (lem-CXcb-box-at03103441 c4) ▸
       at 4 2 (CX24 ∷ CCZ012 ∷ []) (wp0170 c4) ▸
       at 3 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸
       at 2 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸ done

  b1 : Chain (CX24 ∷ Bx3-0241 ∷ CX24 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ []) (Bx3-0241 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wp1024 c4) ▸
       at 0 3 (Bx3-0241 ∷ CCZ012 ∷ []) (lem-CXbc-box-at03103441 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done

-- QVQ @0310243241: 3 steps
lem-QVQ-at0310243241 : Ws → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0310243241 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 0 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 1 4 (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0310243241 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done

-- SWbc-box @0310243241: 11 steps
lem-SWbc-box-at0310243241 : Ws → ⟪ (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-SWbc-box-at0310243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) (CX42 ∷ Bx3-0421 ∷ CX42 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 4 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 2 3 (Bx3-0421 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0310243241 c4) ▸
       at 3 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸
       at 1 3 (Bx3-0421 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0310243241 c4) ▸
       at 4 2 (CX42 ∷ CCZ014 ∷ []) (wp0269 c4) ▸
       at 3 2 (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1022 c4) ▸
       at 2 2 (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1022 c4) ▸ done

  b1 : Chain (CX42 ∷ Bx3-0421 ∷ CX42 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ []) (Bx3-0421 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp1032 c4) ▸
       at 0 3 (Bx3-0421 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0310243241 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done

-- QVQ @03103441: 3 steps
lem-QVQ-at03103441 : Ws → ⟪ (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-QVQ-at03103441 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ [])
  b0 = at 0 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0788 (lit c4))) ▸
       at 1 4 (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at03103441 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done

-- SWbc-box @0310243142: 11 steps
lem-SWbc-box-at0310243142 : Ws → ⟪ (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-SWbc-box-at0310243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) (CX41 ∷ Bx3-0412 ∷ CX41 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 2 3 (Bx3-0412 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0310243142 c4) ▸
       at 3 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸
       at 1 3 (Bx3-0412 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0310243142 c4) ▸
       at 4 2 (CX41 ∷ CCZ024 ∷ []) (wp0285 c4) ▸
       at 3 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp0730 c4) ▸
       at 2 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp0730 c4) ▸ done

  b1 : Chain (CX41 ∷ Bx3-0412 ∷ CX41 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ []) (Bx3-0412 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (wp0731 c4) ▸
       at 0 3 (Bx3-0412 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0310243142 c4) ▸
       at 1 2 [] (wp0135 c4) ▸ done

-- sym-bc @0310213442: 2 steps
lem-sym-bc-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym-bc-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0310213442 c4)) ▸
       at 0 3 (Bx3-0412 ∷ []) (lem-nat-SWbc-at0310213442 c4) ▸ done

-- SWbc-box @0312203441: 11 steps
lem-SWbc-box-at0312203441 : Ws → ⟪ (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-SWbc-box-at0312203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) (CX04 ∷ Bx3-2041 ∷ CX04 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX04 ∷ CX40 ∷ CX04 ∷ []) (sym (wp1084 c4)) ▸
       at 4 1 (CX04 ∷ CX40 ∷ CX04 ∷ []) (sym (wp1084 c4)) ▸
       at 2 3 (Bx3-2041 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0312203441 c4) ▸
       at 3 2 (CX40 ∷ CCZ124 ∷ CCZ012 ∷ []) (wp1085 c4) ▸
       at 1 3 (Bx3-2041 ∷ CCZ124 ∷ []) (lem-CXcb-box-at0312203441 c4) ▸
       at 4 2 (CX04 ∷ CCZ012 ∷ []) (wp1086 c4) ▸
       at 3 2 (CX04 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp1087 c4) ▸
       at 2 2 (CX04 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp1087 c4) ▸ done

  b1 : Chain (CX04 ∷ Bx3-2041 ∷ CX04 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ []) (Bx3-2041 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wp1088 c4) ▸
       at 0 3 (Bx3-2041 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0312203441 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done

-- QVQ @0312243041: 3 steps
lem-QVQ-at0312243041 : Ws → ⟪ (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-QVQ-at0312243041 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 1 4 (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at0312243041 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done

-- SWbc-box @0312243041: 11 steps
lem-SWbc-box-at0312243041 : Ws → ⟪ (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-SWbc-box-at0312243041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) (CX40 ∷ Bx3-2401 ∷ CX40 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX40 ∷ CX04 ∷ CX40 ∷ []) (sym (wp1101 c4)) ▸
       at 4 1 (CX40 ∷ CX04 ∷ CX40 ∷ []) (sym (wp1101 c4)) ▸
       at 2 3 (Bx3-2401 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0312243041 c4) ▸
       at 3 2 (CX04 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp1087 c4) ▸
       at 1 3 (Bx3-2401 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0312243041 c4) ▸
       at 4 2 (CX40 ∷ CCZ124 ∷ []) (wp0321 c4) ▸
       at 3 2 (CX40 ∷ CCZ124 ∷ CCZ012 ∷ []) (wp1085 c4) ▸
       at 2 2 (CX40 ∷ CCZ124 ∷ CCZ012 ∷ []) (wp1085 c4) ▸ done

  b1 : Chain (CX40 ∷ Bx3-2401 ∷ CX40 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ []) (Bx3-2401 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wp1102 c4) ▸
       at 0 3 (Bx3-2401 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0312243041 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done

-- QVQ @0312203441: 3 steps
lem-QVQ-at0312203441 : Ws → ⟪ (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-QVQ-at0312203441 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ [])
  b0 = at 0 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0788 (lit c4))) ▸
       at 1 4 (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at0312203441 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done

-- SWbc-box @3443: 11 steps
lem-SWbc-box-at3443 : Ws → ⟪ (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-SWbc-box-at3443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) (CX24 ∷ Bx0-1243 ∷ CX24 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 4 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 2 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-CXbc-box-at3443 c4) ▸
       at 3 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0319 (lit c4)) ▸
       at 1 3 (Bx0-1243 ∷ CCZ134 ∷ []) (lem-CXcb-box-at3443 c4) ▸
       at 4 2 (CX24 ∷ CCZ123 ∷ []) (wl0406 (lit c4)) ▸
       at 3 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0317 (lit c4)) ▸
       at 2 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0317 (lit c4)) ▸ done

  b1 : Chain (CX24 ∷ Bx0-1243 ∷ CX24 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ []) (Bx0-1243 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl0407 (lit c4)) ▸
       at 0 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-CXbc-box-at3443 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done

-- SWbc-box @031031: 11 steps
lem-SWbc-box-at031031 : Ws → ⟪ (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-SWbc-box-at031031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) (CX21 ∷ Bx3-0214 ∷ CX21 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 4 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 2 3 (Bx3-0214 ∷ CCZ024 ∷ []) (lem-CXbc-box-at031031 c4) ▸
       at 3 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 1 3 (Bx3-0214 ∷ CCZ014 ∷ []) (lem-CXcb-box-at031031 c4) ▸
       at 4 2 (CX21 ∷ CCZ024 ∷ []) (wp0749 c4) ▸
       at 3 2 (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0899 c4) ▸
       at 2 2 (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0899 c4) ▸ done

  b1 : Chain (CX21 ∷ Bx3-0214 ∷ CX21 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) (Bx3-0214 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (wp0991 c4) ▸
       at 0 3 (Bx3-0214 ∷ CCZ024 ∷ []) (lem-CXbc-box-at031031 c4) ▸
       at 1 2 [] (wp0135 c4) ▸ done

-- QVQ @031031: 3 steps
lem-QVQ-at031031 : Ws → ⟪ (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-QVQ-at031031 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ [])
  b0 = at 0 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0788 (lit c4))) ▸
       at 1 4 (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at031031 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done

-- SWbc-box @03143041: 11 steps
lem-SWbc-box-at03143041 : Ws → ⟪ (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-SWbc-box-at03143041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) (CX20 ∷ Bx3-4201 ∷ CX20 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (sym (wl0480 (lit c4))) ▸
       at 4 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (sym (wl0480 (lit c4))) ▸
       at 2 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-CXbc-box-at03143041 c4) ▸
       at 3 2 (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0382 c4) ▸
       at 1 3 (Bx3-4201 ∷ CCZ014 ∷ []) (lem-CXcb-box-at03143041 c4) ▸
       at 4 2 (CX20 ∷ CCZ124 ∷ []) (wp0389 c4) ▸
       at 3 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸
       at 2 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸ done

  b1 : Chain (CX20 ∷ Bx3-4201 ∷ CX20 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ []) (Bx3-4201 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wp0390 c4) ▸
       at 0 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-CXbc-box-at03143041 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done

-- SWbc-box @02142041: 11 steps
lem-SWbc-box-at02142041 : Ws → ⟪ (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-SWbc-box-at02142041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) (CX03 ∷ Bx2-4031 ∷ CX03 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX03 ∷ CX30 ∷ CX03 ∷ []) (sym (wl0961 (lit c4))) ▸
       at 4 1 (CX03 ∷ CX30 ∷ CX03 ∷ []) (sym (wl0961 (lit c4))) ▸
       at 2 3 (Bx2-4031 ∷ CCZ014 ∷ []) (lem-CXbc-box-at02142041 c4) ▸
       at 3 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0763 c4) ▸
       at 1 3 (Bx2-4031 ∷ CCZ134 ∷ []) (lem-CXcb-box-at02142041 c4) ▸
       at 4 2 (CX03 ∷ CCZ014 ∷ []) (wp0778 c4) ▸
       at 3 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0762 c4) ▸
       at 2 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0762 c4) ▸ done

  b1 : Chain (CX03 ∷ Bx2-4031 ∷ CX03 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ []) (Bx2-4031 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0779 c4) ▸
       at 0 3 (Bx2-4031 ∷ CCZ014 ∷ []) (lem-CXbc-box-at02142041 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done
