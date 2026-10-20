{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D016 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0162 ; wl0180 ; wl0181 ; wl0182 ; wl0203 ; wl0205 ; wl0207 ; wl0210 ; wl0229 ; wl0231 ; wp0008 ; wp0019 ; wp0051 ; wp0053 ; wp0054 ; wp0066 ; wp0080 ; wp0111 ; wp0124 ; wp0127 ; wl0292 ; wl0297 ; wp0130 ; wp0131 ; wp0153 ; wp0154 ; wp0157 ; wp0180 ; wp0210 ; wp0211 ; wp0212 ; wp0214 ; wl0344 ; wl0403 ; wl0420 ; wl0421 ; wp0216 ; wp0218 ; wp0257 ; wp0262 ; wl0442 ; wl0446 ; wl0458 ; wl0459 ; wl0460 ; wl0461 ; wl0462 ; wl0463 ; wl0464 ; wl0470 ; wl0489 ; wl0493 ; wl0494 ; wp0301 ; wp0307 ; wp0308 ; wp0309 ; wp0310 ; wp0311 ; wp0312 ; wp0313 ; wp0314 ; wp0351 ; wl0542 ; wl0543 ; wl0544 ; wp0392 ; wp0393 ; wp0394 ; wp0395 ; wp0428 ; wp0429 ; wp0430 ; wp0437 ; wp0438 ; wp0439 ; wl0583 ; wl0584 ; wl0610 ; wl0635 ; wl0636 ; wp0456 ; wp0457 ; wp0516 ; wp0598 ; wl0756 ; wl0787 ; wp0661 ; wl0788 ; wl0845 ; wp0733 ; wp0767 ; wp0796 ; wp0797 ; wp0798 ; wl1074 ; wl1126 ; wl1155 ; wp0988 ; wp0992 ; wp1048 ; wl1271 ; wl1303 ; wl1341)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-nat-SWbc-at0214203143 ; lem-nat-SWbc-at0214213043 ; lem-nat-SWbc-at0314203142 ; lem-nat-SWbc-at0314213042 ; lem-nat-SWbc-at122441 ; lem-nat-SWbc-at132132 ; lem-nat-SWbc-at1331 ; lem-nat-SWbc-at14213243 ; lem-sym-ab-at03102132 ; lem-sym-ab-at0410213243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-nat-SWbc-at0210233441 ; lem-nat-SWbc-at02102441 ; lem-nat-SWbc-at02132031 ; lem-nat-SWbc-at02132130 ; lem-nat-SWbc-at02233440 ; lem-nat-SWbc-at022440 ; lem-nat-SWbc-at0310243241 ; lem-nat-SWbc-at03103441 ; lem-nat-SWbc-at03122031 ; lem-nat-SWbc-at03122130 ; lem-nat-SWbc-at03243240 ; lem-nat-SWbc-at033440 ; lem-nat-SWbc-at12233441 ; lem-nat-SWbc-at143143 ; lem-nat-SWbc-at233442 ; lem-nat-SWbc-at2442 ; lem-sym-ab-at0213243041)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-tQ-at0210213443 ; lem-box-tQ-at0213243140 ; lem-box-tQ-at0220 ; lem-nat-SWbc ; lem-nat-SWbc-at0210243143 ; lem-nat-SWbc-at0213213440 ; lem-nat-SWbc-at0312213440 ; lem-nat-SWbc-at0312243140 ; lem-nat-SWbc-at0330 ; lem-nat-SWbc-at043043 ; lem-nat-SWbc-at1221 ; lem-nat-SWbc-at122331 ; lem-nat-SWbc-at12243143 ; lem-nat-SWbc-at13213442 ; lem-nat-SWbc-at133441 ; lem-nat-SWbc-at1441 ; lem-nat-SWbc-at2332 ; lem-nat-SWbc-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at021021 ; lem-box-tQ-at0213243041 ; lem-box-tQ-at0214233041 ; lem-nat-SWbc-at0310243142 ; lem-nat-SWbc-at031031 ; lem-nat-SWbc-at0312203441 ; lem-nat-SWbc-at0312243041 ; lem-nat-SWbc-at0314203241 ; lem-nat-SWbc-at0314213240 ; lem-nat-SWbc-at03143041 ; lem-nat-SWbc-at03143140 ; lem-nat-SWbc-at12213443 ; lem-nat-SWbc-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-P-box-at0220 ; lem-P-box-at032032 ; lem-P-box-at13243142 ; lem-P-box-at13243241 ; lem-P-box-at14233142 ; lem-P-box-at14233241 ; lem-box-tQ ; lem-box-tQ-at0312243140 ; lem-box-tQ-at1221 ; lem-box-tQ-at12213443 ; lem-box-tQ-at3443 ; lem-nat-SWbc-at022330 ; lem-tP ; lem-tP-at0110 ; lem-tP-at0210233441 ; lem-tP-at0210243143 ; lem-tP-at0213203441 ; lem-tP-at0214213043 ; lem-tP-at0310243142 ; lem-tP-at0312243140 ; lem-tP-at0314203142 ; lem-tP-at0314213042 ; lem-tP-at0330 ; lem-tP-at043043 ; lem-tP-at1221 ; lem-tP-at12213443 ; lem-tP-at122331 ; lem-tP-at12233441 ; lem-tP-at122441 ; lem-tP-at132132 ; lem-tP-at13213442 ; lem-tP-at1331 ; lem-tP-at143143 ; lem-tP-at2332 ; lem-tP-at233442 ; lem-tP-at243243 ; lem-tP-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-P-box-at021021 ; lem-P-box-at0210213443 ; lem-P-box-at0213243041 ; lem-P-box-at0213243140 ; lem-P-box-at0214233041 ; lem-P-box-at03102132 ; lem-P-box-at0310213442 ; lem-box-tQ-at0312243041 ; lem-box-tQ-at03143041 ; lem-nat-SWbc-at02142041 ; lem-tP-at02102441 ; lem-tP-at02132031 ; lem-tP-at02132130 ; lem-tP-at0214203143 ; lem-tP-at022330 ; lem-tP-at02233440 ; lem-tP-at022440 ; lem-tP-at0310243241 ; lem-tP-at031031 ; lem-tP-at03103441 ; lem-tP-at03122031 ; lem-tP-at0312203441 ; lem-tP-at03122130 ; lem-tP-at0312243041 ; lem-tP-at0314213240 ; lem-tP-at03143041 ; lem-tP-at03143140 ; lem-tP-at03243240 ; lem-tP-at033440 ; lem-tP-at12243143 ; lem-tP-at14213243 ; lem-tP-at1441 ; lem-tP-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-QVQ ; lem-QVQ-at0110 ; lem-QVQ-at0210233441 ; lem-QVQ-at0210243143 ; lem-QVQ-at02102441 ; lem-QVQ-at0213203441 ; lem-QVQ-at0214203143 ; lem-QVQ-at0214213043 ; lem-QVQ-at022330 ; lem-QVQ-at02233440 ; lem-QVQ-at022440 ; lem-QVQ-at0310243142 ; lem-QVQ-at0310243241 ; lem-QVQ-at031031 ; lem-QVQ-at03103441 ; lem-QVQ-at0312203441 ; lem-QVQ-at0312243041 ; lem-QVQ-at0312243140 ; lem-QVQ-at0314203142 ; lem-QVQ-at0314213042 ; lem-QVQ-at0314213240 ; lem-QVQ-at03143140 ; lem-QVQ-at03243240 ; lem-QVQ-at0330 ; lem-QVQ-at033440 ; lem-QVQ-at043043 ; lem-QVQ-at1221 ; lem-QVQ-at12213443 ; lem-QVQ-at122331 ; lem-QVQ-at12233441 ; lem-QVQ-at12243143 ; lem-QVQ-at122441 ; lem-QVQ-at132132 ; lem-QVQ-at13213442 ; lem-QVQ-at1331 ; lem-QVQ-at14213243 ; lem-QVQ-at143143 ; lem-QVQ-at1441 ; lem-QVQ-at2332 ; lem-QVQ-at233442 ; lem-QVQ-at243243 ; lem-QVQ-at2442 ; lem-QVQ-at3443 ; lem-SWbc-box ; lem-SWbc-box-at0210233441 ; lem-SWbc-box-at0210243143 ; lem-SWbc-box-at02102441 ; lem-SWbc-box-at0213213440 ; lem-SWbc-box-at0214203143 ; lem-SWbc-box-at02142041 ; lem-SWbc-box-at0214213043 ; lem-SWbc-box-at022330 ; lem-SWbc-box-at02233440 ; lem-SWbc-box-at022440 ; lem-SWbc-box-at0310243142 ; lem-SWbc-box-at0310243241 ; lem-SWbc-box-at031031 ; lem-SWbc-box-at03103441 ; lem-SWbc-box-at0312203441 ; lem-SWbc-box-at0312213440 ; lem-SWbc-box-at0312243041 ; lem-SWbc-box-at0312243140 ; lem-SWbc-box-at0314203142 ; lem-SWbc-box-at0314213042 ; lem-SWbc-box-at0314213240 ; lem-SWbc-box-at03143041 ; lem-SWbc-box-at03143140 ; lem-SWbc-box-at03243240 ; lem-SWbc-box-at0330 ; lem-SWbc-box-at033440 ; lem-SWbc-box-at043043 ; lem-SWbc-box-at1221 ; lem-SWbc-box-at12213443 ; lem-SWbc-box-at122331 ; lem-SWbc-box-at12233441 ; lem-SWbc-box-at12243143 ; lem-SWbc-box-at122441 ; lem-SWbc-box-at132132 ; lem-SWbc-box-at13213442 ; lem-SWbc-box-at1331 ; lem-SWbc-box-at133441 ; lem-SWbc-box-at14213243 ; lem-SWbc-box-at143143 ; lem-SWbc-box-at1441 ; lem-SWbc-box-at2332 ; lem-SWbc-box-at233442 ; lem-SWbc-box-at243243 ; lem-SWbc-box-at2442 ; lem-SWbc-box-at3443 ; lem-XCSX-box-2-at0210243143 ; lem-XCSX-box-2-at122441 ; lem-XCSX-box-2-at243243 ; lem-box-cP-at021021 ; lem-box-cP-at0210213443 ; lem-box-cP-at0213243140 ; lem-box-cP-at0220 ; lem-box-cP-at03102132 ; lem-box-cP-at032032 ; lem-box-cP-at0410213243 ; lem-box-cP-at13243142 ; lem-box-cP-at13243241 ; lem-box-cP-at14233142 ; lem-box-cP-at14233241 ; lem-sym-bc-at03102132 ; lem-sym-bc-at0310213442 ; lem-sym-bc-at032032 ; lem-sym-bc-at04203243 ; lem-sym-bc-at13243142)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-QVQ-at02132031 ; lem-QVQ-at02132130 ; lem-QVQ-at03122031 ; lem-QVQ-at03122130 ; lem-QVQ-at03143041 ; lem-SWbc-box-at02132031 ; lem-SWbc-box-at02132130 ; lem-SWbc-box-at03122031 ; lem-SWbc-box-at03122130 ; lem-SWbc-box-at0314203241 ; lem-box-cP-at0213243041 ; lem-box-cP-at0214233041 ; lem-box-cP-at0310213442 ; lem-sym-bc-at0214233041)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-CCZ034 ; lem-comm-CS23-CCZ014 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX12-CCZ034)

-- box-cP: 12 steps
lem-box-cP : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 2 4 (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ c4) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP c4) ▸
       at 2 2 [] (wl0162 (lit c4)) ▸ done

-- box-cP @0210243143: 12 steps
lem-box-cP-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-box-cP-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0413 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl0182 (lit c4)) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl0182 (lit c4)) ▸
       at 2 4 (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-QVQ-at0210243143 c4) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0210243143 c4) ▸
       at 2 2 [] (wp0019 c4) ▸ done

-- box-cP @243243: 12 steps
lem-box-cP-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1423 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0205 (lit c4)) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (wl0205 (lit c4)) ▸
       at 2 4 (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-QVQ-at243243 c4) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at243243 c4) ▸
       at 2 2 [] (wp0051 c4) ▸ done

-- box-cP @122441: 12 steps
lem-box-cP-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at122441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2431 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 2 4 (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at122441 c4) ▸
       at 1 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at122441 c4) ▸
       at 2 2 [] (wp0080 c4) ▸ done

-- sym-bc: 2 steps
lem-sym-bc : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym-bc c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1324 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (sym (lem-SWbc-box c4)) ▸
       at 0 3 (Bx0-1324 ∷ []) (lem-nat-SWbc c4) ▸ done

-- sym-bc @1221: 2 steps
lem-sym-bc-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym-bc-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at1221 c4)) ▸
       at 0 3 (Bx0-2314 ∷ []) (lem-nat-SWbc-at1221 c4) ▸ done

-- box-cP @1221: 12 steps
lem-box-cP-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2134 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 2 4 (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ-at1221 c4) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at1221 c4) ▸
       at 2 2 [] (wl0162 (lit c4)) ▸ done

-- box-cP @2332: 12 steps
lem-box-cP-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1324 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 2 4 (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at2332 c4) ▸
       at 1 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at2332 c4) ▸
       at 2 2 [] (wl0229 (lit c4)) ▸ done

-- box-cP @122331: 12 steps
lem-box-cP-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-box-cP-at122331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2314 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (wp0153 c4) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (wp0153 c4) ▸
       at 2 4 (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-QVQ-at122331 c4) ▸
       at 1 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at122331 c4) ▸
       at 2 2 [] (wl0203 (lit c4)) ▸ done

-- box-cP @132132: 12 steps
lem-box-cP-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3124 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 2 4 (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at132132 c4) ▸
       at 1 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at132132 c4) ▸
       at 2 2 [] (wl0229 (lit c4)) ▸ done

-- sym-bc @12243143: 2 steps
lem-sym-bc-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-sym-bc-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at12243143 c4)) ▸
       at 0 3 (Bx0-2143 ∷ []) (lem-nat-SWbc-at12243143 c4) ▸ done

-- pairs @14233142: 4 steps
lem-pairs-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-pairs-at14233142 c4 = run b0
  where
  b0 : Chain (Bx0-4312 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (Toff012 ∷ Bx0-4312 ∷ Toff012 ∷ []) (sym (lem-P-box-at14233142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at14233142 c4) ▸
       at 4 2 [] (wl0162 (lit c4)) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸ done

-- box-cP @13213442: 12 steps
lem-box-cP-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at13213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3142 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 2 4 (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at13213442 c4) ▸
       at 1 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at13213442 c4) ▸
       at 2 2 [] (wl0229 (lit c4)) ▸ done

-- box-cP @1331: 12 steps
lem-box-cP-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-box-cP-at1331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3214 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (wp0154 c4) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (wp0154 c4) ▸
       at 2 4 (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-QVQ-at1331 c4) ▸
       at 1 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at1331 c4) ▸
       at 2 2 [] (wl0203 (lit c4)) ▸ done

-- box-cP @0110: 12 steps
lem-box-cP-at0110 : Ws → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ []) ⟫ʷ
lem-box-cP-at0110 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx1-0234 ∷ []) (CCZ012 ∷ Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 2 4 (Toff134 ∷ Toff102 ∷ CCZ012 ∷ Toff134 ∷ []) (lem-QVQ-at0110 c4) ▸
       at 1 2 (Toff134 ∷ Toff102 ∷ []) (lem-tP-at0110 c4) ▸
       at 2 2 [] (wl0403 (lit c4)) ▸ done

-- sym-bc @133441: 2 steps
lem-sym-bc-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-sym-bc-at133441 c4 = run b0
  where
  b0 : Chain (Bx0-3241 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at133441 c4)) ▸
       at 0 3 (Bx0-3421 ∷ []) (lem-nat-SWbc-at133441 c4) ▸ done

-- pairs @13243241: 4 steps
lem-pairs-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-pairs-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 1 (Toff012 ∷ Bx0-3421 ∷ Toff012 ∷ []) (sym (lem-P-box-at13243241 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at13243241 c4) ▸
       at 4 2 [] (wl0162 (lit c4)) ▸
       at 0 4 (Bx0-2134 ∷ []) (sym (lem-box-tQ-at1221 c4)) ▸ done

-- sym-bc @13213442: 2 steps
lem-sym-bc-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-sym-bc-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at13213442 c4)) ▸
       at 0 3 (Bx0-3412 ∷ []) (lem-nat-SWbc-at13213442 c4) ▸ done

-- pairs @13243142: 4 steps
lem-pairs-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-pairs-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Toff012 ∷ Bx0-3412 ∷ Toff012 ∷ []) (sym (lem-P-box-at13243142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at13243142 c4) ▸
       at 4 2 [] (wl0162 (lit c4)) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

-- box-cP @3443: 12 steps
lem-box-cP-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP-at3443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1243 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0210 c4) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0210 c4) ▸
       at 2 4 (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ-at3443 c4) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at3443 c4) ▸
       at 2 2 [] (wl0162 (lit c4)) ▸ done

-- box-box-4: 103 steps
lem-box-box-4 : Ws → ⟪ (Bx0-1234 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-box-box-4 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Bx0-1234 ∷ Bx4-0123 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CCZ014 ∷ CX02 ∷ CS03 ∷ CCZ034 ∷ Toff423 ∷ [])
  b0 = at 0 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸
       at 3 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 4 2 (Toff423 ∷ CCZ023 ∷ CCZ034 ∷ []) (wp0307 c4) ▸
       at 6 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 5 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl0458 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 8 2 (CCZ014 ∷ CX02 ∷ []) (sym (wp0308 c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CCZ014 ∷ CX02 ∷ CS03 ∷ CCZ034 ∷ Toff423 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff012 ∷ CCZ124 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CX02 ∷ []) (sym (wp0308 c4)) ▸
       at 5 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 6 5 (CCZ023 ∷ []) (sym (wl0458 (lit c4))) ▸
       at 6 3 (Toff423 ∷ CCZ034 ∷ []) (wp0309 c4) ▸
       at 3 4 (Bx4-0123 ∷ []) (sym (lem-box-cP-at0410213243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸
       at 2 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (sym (wp0310 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff012 ∷ CCZ124 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ K0 ∷ Toff423 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ [])
  b2 = at 4 2 (Toff423 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0459 (lit c4)) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 9 2 (Toff423 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ ↑)) ▸
       at 8 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸
       at 5 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 4 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸ done

  b3 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ K0 ∷ Toff423 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ Toff012 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ124 ∷ Toff423 ∷ CCZ034 ∷ [])
  b3 = at 3 2 (Toff423 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ ↑)) ▸
       at 4 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 8 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 7 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b4 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ Toff012 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ124 ∷ Toff423 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Toff423 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ034 ∷ [])
  b4 = at 5 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 4 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (sym (wp0310 c4)) ▸
       at 6 3 (CCZ123 ∷ []) (sym (wl0462 (lit c4))) ▸
       at 6 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 11 2 (Toff423 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ ↑)) ▸
       at 10 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸ done

  b5 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Toff423 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b5 = at 9 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 5 2 (Toff423 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ ↑)) ▸
       at 6 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 2 4 (Bx4-0123 ∷ []) (sym (lem-box-cP-at0410213243 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸ done

  b6 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ034 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b6 = at 1 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 2 2 (Toff423 ∷ CCZ023 ∷ CCZ034 ∷ []) (wp0307 c4) ▸
       at 4 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 3 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl0458 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 6 2 (CCZ014 ∷ CX02 ∷ []) (sym (wp0308 c4)) ▸
       at 5 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CX02 ∷ []) (sym (wp0308 c4)) ▸ done

  b7 : Chain (Toff012 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ034 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Toff423 ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b7 = at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 4 5 (CCZ023 ∷ []) (sym (wl0458 (lit c4))) ▸
       at 4 3 (Toff423 ∷ CCZ034 ∷ []) (wp0309 c4) ▸
       at 1 4 (Bx4-0123 ∷ []) (sym (lem-box-cP-at0410213243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸
       at 0 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (sym (wp0310 c4)) ▸
       at 2 2 (Toff423 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0459 (lit c4)) ▸
       at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸ done

  b8 : Chain (CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Toff423 ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b8 = at 7 2 (Toff423 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ ↑)) ▸
       at 6 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 5 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 4 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸
       at 3 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 2 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 1 2 (Toff423 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ ↑)) ▸
       at 2 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸ done

  b9 : Chain (CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ014 ∷ CCZ123 ∷ CCZ124 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b9 = at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 6 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 5 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸ done

  b10 : Chain (CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ014 ∷ CCZ123 ∷ CCZ124 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ Toff423 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b10 = at 2 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (sym (wp0310 c4)) ▸
       at 4 3 (CCZ123 ∷ []) (sym (wl0462 (lit c4))) ▸
       at 4 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 9 2 (Toff423 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ ↑)) ▸
       at 8 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸ done

  b11 : Chain (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ Toff423 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (Bx4-0123 ∷ Toff012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b11 = at 5 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 4 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 3 2 (Toff423 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ ↑)) ▸
       at 4 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 0 4 (Bx4-0123 ∷ []) (sym (lem-box-cP-at0410213243 c4)) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b12 : Chain (Bx4-0123 ∷ Toff012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (Bx4-0123 ∷ Bx0-1234 ∷ [])
  b12 = at 4 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff012 ∷ CCZ123 ∷ []) (wl0464 (lit c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸
       at 1 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

-- box-cP @043043: 12 steps
lem-box-cP-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-box-cP-at043043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1203 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0210 c4) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0210 c4) ▸
       at 2 4 (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-QVQ-at043043 c4) ▸
       at 1 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at043043 c4) ▸
       at 2 2 [] (wl0470 (lit c4)) ▸ done

-- sym-bc @043043: 2 steps
lem-sym-bc-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-sym-bc-at043043 c4 = run b0
  where
  b0 : Chain (Bx4-1203 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at043043 c4)) ▸
       at 0 3 (Bx4-1023 ∷ []) (lem-nat-SWbc-at043043 c4) ▸ done

-- box-cP @0330: 12 steps
lem-box-cP-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-box-cP-at0330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1204 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 2 4 (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-QVQ-at0330 c4) ▸
       at 1 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at0330 c4) ▸
       at 2 2 [] (wl0489 (lit c4)) ▸ done

-- box-cP @0314203142: 12 steps
lem-box-cP-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0314203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4012 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl0494 (lit c4))) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl0494 (lit c4))) ▸
       at 2 4 (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-QVQ-at0314203142 c4) ▸
       at 1 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203142 c4) ▸
       at 2 2 [] (wp0351 c4) ▸ done

-- box-cP @0310243142: 12 steps
lem-box-cP-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0310243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0412 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl0493 (lit c4)) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl0493 (lit c4)) ▸
       at 2 4 (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-QVQ-at0310243142 c4) ▸
       at 1 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243142 c4) ▸
       at 2 2 [] (wp0351 c4) ▸ done

-- box-perm-2314 @0410213243: 2 steps
lem-box-perm-2314-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-box-perm-2314-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ []) (Bx4-1203 ∷ [])
  b0 = at 0 1 (Bx4-1023 ∷ []) (lem-sym-ab-at0410213243 c4) ▸
       at 0 1 (Bx4-1203 ∷ []) (lem-sym-bc-at04203243 c4) ▸ done

-- box-perm-2314 @03102132: 2 steps
lem-box-perm-2314-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-2314-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-sym-bc-at032032 c4) ▸ done

-- sym-bc @0330: 2 steps
lem-sym-bc-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym-bc-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at0330 c4)) ▸
       at 0 3 (Bx3-1024 ∷ []) (lem-nat-SWbc-at0330 c4) ▸ done

-- CXu-box-4 @03102132: 15 steps
lem-CXu-box-4-at03102132 : Ws → ⟪ (CX43 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CX43 ∷ []) ⟫ʷ
lem-CXu-box-4-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX43 ∷ Bx3-0124 ∷ []) (CCZ013 ∷ CX43 ∷ Toff324 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ013 ∷ Toff324 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸
       at 0 2 (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (sym (wp0392 c4)) ▸
       at 2 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 6 2 (Toff324 ∷ CS04 ∷ []) (wp0393 c4) ▸
       at 5 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff324 ∷ CS14⁻ ∷ []) (wl0542 (lit c4)) ▸
       at 3 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff324 ∷ CS14 ∷ []) (wl0543 (lit c4)) ▸ done

  b1 : Chain (CCZ013 ∷ CX43 ∷ Toff324 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ013 ∷ Toff324 ∷ []) (Bx3-0124 ∷ CX43 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 1 2 (Toff324 ∷ CX43 ∷ []) (wl0544 (lit c4)) ▸
       at 3 2 (CCZ013 ∷ CCZ014 ∷ []) (sym (wp0394 c4)) ▸
       at 2 2 (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (sym (wp0392 c4)) ▸
       at 3 3 (CX43 ∷ []) (wp0395 c4) ▸
       at 3 2 (Toff324 ∷ CX43 ∷ []) (wl0544 (lit c4)) ▸
       at 0 4 (Bx3-0124 ∷ []) (sym (lem-box-cP-at03102132 c4)) ▸ done

-- F4-S0-CS1: 13 steps
lem-F4-S0-CS1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 4 (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-XCSX-box-2-at243243 c4) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0428 c4)) ▸
       at 2 4 (CS13 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0429 c4)) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0428 c4)) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0430 c4)) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (S0 ∷ CS04⁻ ∷ []) (sym (wp0257 c4)) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (wp0257 c4) ▸ done

-- F4-S0-CS2: 13 steps
lem-F4-S0-CS2 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 4 (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-XCSX-box-2-at122441 c4) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0437 c4)) ▸
       at 2 4 (CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0438 c4)) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0437 c4)) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0439 c4)) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (S0 ∷ CS04⁻ ∷ []) (sym (wp0257 c4)) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (wp0257 c4) ▸ done

-- F4-S2-CS0: 13 steps
lem-F4-S2-CS0 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 4 (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-XCSX-box-2-at0210243143 c4) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0584 (lit c4))) ▸
       at 2 4 (CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0456 c4)) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0584 (lit c4))) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0457 c4)) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 3 (S2 ∷ CS24⁻ ∷ []) (sym (wl0583 (lit c4))) ▸
       at 1 2 (X4 ∷ CS24 ∷ X4 ∷ []) (wl0583 (lit c4)) ▸ done

-- sym-bc @0214203143: 2 steps
lem-sym-bc-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-sym-bc-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0214203143 c4)) ▸
       at 0 3 (Bx2-4103 ∷ []) (lem-nat-SWbc-at0214203143 c4) ▸ done

-- box-cP @0214213043: 12 steps
lem-box-cP-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-box-cP-at0214213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4103 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 2 4 (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-QVQ-at0214213043 c4) ▸
       at 1 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at0214213043 c4) ▸
       at 2 2 [] (wl0636 (lit c4)) ▸ done

-- box-cP @0210233441: 12 steps
lem-box-cP-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at0210233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0341 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 2 4 (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-QVQ-at0210233441 c4) ▸
       at 1 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0210233441 c4) ▸
       at 2 2 [] (wl0635 (lit c4)) ▸ done

-- sym-bc @122441: 2 steps
lem-sym-bc-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym-bc-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at122441 c4)) ▸
       at 0 3 (Bx0-2341 ∷ []) (lem-nat-SWbc-at122441 c4) ▸ done

-- box-cP @12233441: 12 steps
lem-box-cP-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-box-cP-at12233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2341 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp0218 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (sym (wp0218 c4)) ▸
       at 2 4 (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-QVQ-at12233441 c4) ▸
       at 1 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at12233441 c4) ▸
       at 2 2 [] (wl0203 (lit c4)) ▸ done

-- sym-bc @14213243: 2 steps
lem-sym-bc-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym-bc-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at14213243 c4)) ▸
       at 0 3 (Bx0-4213 ∷ []) (lem-nat-SWbc-at14213243 c4) ▸ done

-- box-cP @143143: 12 steps
lem-box-cP-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at143143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4213 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0180 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0180 c4)) ▸
       at 2 4 (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at143143 c4) ▸
       at 1 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at143143 c4) ▸
       at 2 2 [] (wp0080 c4) ▸ done

-- box-cP @233442: 12 steps
lem-box-cP-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at233442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1342 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 2 4 (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at233442 c4) ▸
       at 1 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at233442 c4) ▸
       at 2 2 [] (wl0229 (lit c4)) ▸ done

-- sym-bc @0210243143: 2 steps
lem-sym-bc-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-sym-bc-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0210243143 c4)) ▸
       at 0 3 (Bx2-0143 ∷ []) (lem-nat-SWbc-at0210243143 c4) ▸ done

-- sym-bc @243243: 2 steps
lem-sym-bc-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-sym-bc-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at243243 c4)) ▸
       at 0 3 (Bx0-1243 ∷ []) (lem-nat-SWbc-at243243 c4) ▸ done

-- sym-bc @1441: 2 steps
lem-sym-bc-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-sym-bc-at1441 c4 = run b0
  where
  b0 : Chain (Bx0-4231 ∷ []) (Bx0-4321 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at1441 c4)) ▸
       at 0 3 (Bx0-4321 ∷ []) (lem-nat-SWbc-at1441 c4) ▸ done

-- pairs @14233241: 4 steps
lem-pairs-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-pairs-at14233241 c4 = run b0
  where
  b0 : Chain (Bx0-4321 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Toff012 ∷ Bx0-4321 ∷ Toff012 ∷ []) (sym (lem-P-box-at14233241 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at14233241 c4) ▸
       at 4 2 [] (wl0162 (lit c4)) ▸
       at 0 4 (Bx0-2143 ∷ []) (sym (lem-box-tQ-at12213443 c4)) ▸ done

-- box-cP @12213443: 12 steps
lem-box-cP-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP-at12213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2143 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 2 4 (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ-at12213443 c4) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at12213443 c4) ▸
       at 2 2 [] (wl0162 (lit c4)) ▸ done

-- sym-bc @0314213042: 2 steps
lem-sym-bc-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym-bc-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0314213042 c4)) ▸
       at 0 3 (Bx3-4012 ∷ []) (lem-nat-SWbc-at0314213042 c4) ▸ done

-- box-cP @0213203441: 12 steps
lem-box-cP-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at0213203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3041 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 2 4 (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-QVQ-at0213203441 c4) ▸
       at 1 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0213203441 c4) ▸
       at 2 2 [] (wl0635 (lit c4)) ▸ done

-- sym-bc @0314203142: 2 steps
lem-sym-bc-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-sym-bc-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0314203142 c4)) ▸
       at 0 3 (Bx3-4102 ∷ []) (lem-nat-SWbc-at0314203142 c4) ▸ done

-- box-cP @0314213042: 12 steps
lem-box-cP-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-box-cP-at0314213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4102 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 2 4 (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-QVQ-at0314213042 c4) ▸
       at 1 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213042 c4) ▸
       at 2 2 [] (wl0788 (lit c4)) ▸ done

-- sym-bc @0214213043: 2 steps
lem-sym-bc-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym-bc-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0214213043 c4)) ▸
       at 0 3 (Bx2-4013 ∷ []) (lem-nat-SWbc-at0214213043 c4) ▸ done

-- sym-bc @1331: 2 steps
lem-sym-bc-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym-bc-at1331 c4 = run b0
  where
  b0 : Chain (Bx0-3214 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at1331 c4)) ▸
       at 0 3 (Bx0-3124 ∷ []) (lem-nat-SWbc-at1331 c4) ▸ done

-- pairs @032032: 4 steps
lem-pairs-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-pairs-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-2410 ∷ [])
  b0 = at 0 1 (Toff324 ∷ Bx3-1024 ∷ Toff324 ∷ []) (sym (lem-P-box-at032032 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 4 2 [] (wl0442 (lit c4)) ▸
       at 0 4 (Bx3-2410 ∷ []) (sym (lem-box-tQ-at0312243140 c4)) ▸ done

-- sym-bc @0312243140: 2 steps
lem-sym-bc-at0312243140 : Ws → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-sym-bc-at0312243140 c4 = run b0
  where
  b0 : Chain (Bx3-2410 ∷ []) (Bx3-2140 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0312243140 c4)) ▸
       at 0 3 (Bx3-2140 ∷ []) (lem-nat-SWbc-at0312243140 c4) ▸ done

-- sym-bc @0312213440: 2 steps
lem-sym-bc-at0312213440 : Ws → ⟪ (Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-sym-bc-at0312213440 c4 = run b0
  where
  b0 : Chain (Bx3-2140 ∷ []) (Bx3-2410 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0312213440 c4)) ▸
       at 0 3 (Bx3-2410 ∷ []) (lem-nat-SWbc-at0312213440 c4) ▸ done

-- box-cP @0312243140: 12 steps
lem-box-cP-at0312243140 : Ws → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-box-cP-at0312243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2410 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wl0845 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wl0845 (lit c4))) ▸
       at 2 4 (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-QVQ-at0312243140 c4) ▸
       at 1 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at0312243140 c4) ▸
       at 2 2 [] (wl0442 (lit c4)) ▸ done

-- sym-bc @132132: 2 steps
lem-sym-bc-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym-bc-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at132132 c4)) ▸
       at 0 3 (Bx0-3214 ∷ []) (lem-nat-SWbc-at132132 c4) ▸ done

-- sym-bc @022330: 2 steps
lem-sym-bc-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym-bc-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at022330 c4)) ▸
       at 0 3 (Bx2-1034 ∷ []) (lem-nat-SWbc-at022330 c4) ▸ done

-- pairs @0220: 4 steps
lem-pairs-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-pairs-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-3410 ∷ [])
  b0 = at 0 1 (Toff234 ∷ Bx2-1034 ∷ Toff234 ∷ []) (sym (lem-P-box-at0220 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0220 c4) ▸
       at 4 2 [] (wl0420 (lit c4)) ▸
       at 0 4 (Bx2-3410 ∷ []) (sym (lem-box-tQ-at0213243140 c4)) ▸ done

-- sym-bc @0213213440: 2 steps
lem-sym-bc-at0213213440 : Ws → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-sym-bc-at0213213440 c4 = run b0
  where
  b0 : Chain (Bx2-3140 ∷ []) (Bx2-3410 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0213213440 c4)) ▸
       at 0 3 (Bx2-3410 ∷ []) (lem-nat-SWbc-at0213213440 c4) ▸ done

-- pairs @0213243140: 4 steps
lem-pairs-at0213243140 : Ws → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-pairs-at0213243140 c4 = run b0
  where
  b0 : Chain (Bx2-3410 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 1 (Toff201 ∷ Bx2-3410 ∷ Toff201 ∷ []) (sym (lem-P-box-at0213243140 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243140 c4) ▸
       at 4 2 [] (wl0421 (lit c4)) ▸
       at 0 4 (Bx2-1034 ∷ []) (sym (lem-box-tQ-at0220 c4)) ▸ done

-- box-cP @022330: 12 steps
lem-box-cP-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-box-cP-at022330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1304 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 2 4 (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-QVQ-at022330 c4) ▸
       at 1 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at022330 c4) ▸
       at 2 2 [] (wl0180 (lit c4)) ▸ done

-- sym-bc @122331: 2 steps
lem-sym-bc-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym-bc-at122331 c4 = run b0
  where
  b0 : Chain (Bx0-2314 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at122331 c4)) ▸
       at 0 3 (Bx0-2134 ∷ []) (lem-nat-SWbc-at122331 c4) ▸ done

-- box-cP @14213243: 12 steps
lem-box-cP-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4123 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 2 4 (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-QVQ-at14213243 c4) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at14213243 c4) ▸
       at 2 2 [] (wp0051 c4) ▸ done

-- sym-bc @12233441: 2 steps
lem-sym-bc-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-sym-bc-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at12233441 c4)) ▸
       at 0 3 (Bx0-2431 ∷ []) (lem-nat-SWbc-at12233441 c4) ▸ done

-- sym-bc @2332: 2 steps
lem-sym-bc-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym-bc-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at2332 c4)) ▸
       at 0 3 (Bx0-1234 ∷ []) (lem-nat-SWbc-at2332 c4) ▸ done

-- box-perm-1324 @03102132: 1 steps
lem-box-perm-1324-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-box-perm-1324-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 0 1 (Bx3-0214 ∷ []) (lem-sym-bc-at03102132 c4) ▸ done

-- box-cP @0214203143: 12 steps
lem-box-cP-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-box-cP-at0214203143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4013 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl0610 (lit c4))) ▸
       at 5 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl0610 (lit c4))) ▸
       at 2 4 (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-QVQ-at0214203143 c4) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0214203143 c4) ▸
       at 2 2 [] (wp0019 c4) ▸ done

-- sym-bc @02233440: 2 steps
lem-sym-bc-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-sym-bc-at02233440 c4 = run b0
  where
  b0 : Chain (Bx2-1340 ∷ []) (Bx2-1430 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at02233440 c4)) ▸
       at 0 3 (Bx2-1430 ∷ []) (lem-nat-SWbc-at02233440 c4) ▸ done

-- box-cP @022440: 12 steps
lem-box-cP-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-box-cP-at022440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1430 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 2 4 (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-QVQ-at022440 c4) ▸
       at 1 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at022440 c4) ▸
       at 2 2 [] (wl0636 (lit c4)) ▸ done

-- sym-bc @022440: 2 steps
lem-sym-bc-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-sym-bc-at022440 c4 = run b0
  where
  b0 : Chain (Bx2-1430 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at022440 c4)) ▸
       at 0 3 (Bx2-1340 ∷ []) (lem-nat-SWbc-at022440 c4) ▸ done

-- box-cP @02233440: 12 steps
lem-box-cP-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-box-cP-at02233440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1340 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 2 4 (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-QVQ-at02233440 c4) ▸
       at 1 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at02233440 c4) ▸
       at 2 2 [] (wl0180 (lit c4)) ▸ done

-- box-cP @1441: 12 steps
lem-box-cP-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at1441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4231 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 2 4 (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at1441 c4) ▸
       at 1 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at1441 c4) ▸
       at 2 2 [] (wp0080 c4) ▸ done

-- Xb-box @13243142: 18 steps
lem-Xb-box-at13243142 : Ws → ⟪ (X4 ∷ Bx0-3412 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at13243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx0-3412 ∷ X4 ∷ []) (CCZ034 ∷ Toff012 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX31 ∷ CCZ034 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff012 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at13243142 c4) ▸
       at 0 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 2 2 (Toff012 ∷ CZ03 ∷ CCZ123 ∷ []) (wl1074 (lit c4)) ▸
       at 1 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 4 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 7 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (CCZ034 ∷ Toff012 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX31 ∷ CCZ034 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff012 ∷ X4 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ CCZ123 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸
       at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CZ03 ∷ []) (sym (wp0797 c4)) ▸
       at 2 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 3 3 (X4 ∷ []) (wp0798 c4) ▸
       at 4 2 (Toff012 ∷ CCZ123 ∷ []) (wl0464 (lit c4)) ▸
       at 3 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸ done

  b2 : Chain (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (Bx0-3412 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-3412 ∷ []) (sym (lem-box-cP-at13243142 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0210 (lit c4))) ▸ done

-- box-perm-1324 @13243142: 1 steps
lem-box-perm-1324-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-1324-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Bx0-3142 ∷ []) (lem-sym-bc-at13243142 c4) ▸ done

-- sym-bc @0210233441: 2 steps
lem-sym-bc-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-sym-bc-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at0210233441 c4)) ▸
       at 0 3 (Bx2-0431 ∷ []) (lem-nat-SWbc-at0210233441 c4) ▸ done

-- box-cP @02102441: 12 steps
lem-box-cP-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-box-cP-at02102441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0431 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 2 4 (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-QVQ-at02102441 c4) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02102441 c4) ▸
       at 2 2 [] (wp0019 c4) ▸ done

-- sym-bc @02102441: 2 steps
lem-sym-bc-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym-bc-at02102441 c4 = run b0
  where
  b0 : Chain (Bx2-0431 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at02102441 c4)) ▸
       at 0 3 (Bx2-0341 ∷ []) (lem-nat-SWbc-at02102441 c4) ▸ done

-- sym-bc @233442: 2 steps
lem-sym-bc-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-sym-bc-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at233442 c4)) ▸
       at 0 3 (Bx0-1432 ∷ []) (lem-nat-SWbc-at233442 c4) ▸ done

-- box-cP @2442: 12 steps
lem-box-cP-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at2442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1432 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 2 4 (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-QVQ-at2442 c4) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at2442 c4) ▸
       at 2 2 [] (wp0051 c4) ▸ done

-- sym-bc @2442: 2 steps
lem-sym-bc-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym-bc-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at2442 c4)) ▸
       at 0 3 (Bx0-1342 ∷ []) (lem-nat-SWbc-at2442 c4) ▸ done

-- sym-bc @143143: 2 steps
lem-sym-bc-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-sym-bc-at143143 c4 = run b0
  where
  b0 : Chain (Bx0-4213 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at143143 c4)) ▸
       at 0 3 (Bx0-4123 ∷ []) (lem-nat-SWbc-at143143 c4) ▸ done

-- sym-bc @12213443: 2 steps
lem-sym-bc-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-sym-bc-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at12213443 c4)) ▸
       at 0 3 (Bx0-2413 ∷ []) (lem-nat-SWbc-at12213443 c4) ▸ done

-- box-cP @12243143: 12 steps
lem-box-cP-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at12243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2413 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (wl0292 (lit c4)) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (wl0292 (lit c4)) ▸
       at 2 4 (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at12243143 c4) ▸
       at 1 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at12243143 c4) ▸
       at 2 2 [] (wp0080 c4) ▸ done

-- sym-bc @03143140: 2 steps
lem-sym-bc-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym-bc-at03143140 c4 = run b0
  where
  b0 : Chain (Bx3-4210 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at03143140 c4)) ▸
       at 0 3 (Bx3-4120 ∷ []) (lem-nat-SWbc-at03143140 c4) ▸ done

-- box-cP @0314213240: 12 steps
lem-box-cP-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-box-cP-at0314213240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4120 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 2 4 (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-QVQ-at0314213240 c4) ▸
       at 1 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213240 c4) ▸
       at 2 2 [] (wl0788 (lit c4)) ▸ done

-- sym-bc @0314213240: 2 steps
lem-sym-bc-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-sym-bc-at0314213240 c4 = run b0
  where
  b0 : Chain (Bx3-4120 ∷ []) (Bx3-4210 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at0314213240 c4)) ▸
       at 0 3 (Bx3-4210 ∷ []) (lem-nat-SWbc-at0314213240 c4) ▸ done

-- box-cP @03143140: 12 steps
lem-box-cP-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-box-cP-at03143140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4210 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ134 ∷ Toff413 ∷ CZ04 ∷ Toff413 ∷ CCZ134 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0988 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ134 ∷ Toff413 ∷ CZ04 ∷ Toff413 ∷ CCZ134 ∷ CZ04 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0988 c4)) ▸
       at 2 4 (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-QVQ-at03143140 c4) ▸
       at 1 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143140 c4) ▸
       at 2 2 [] (wl0442 (lit c4)) ▸ done

-- box-cP @03243240: 12 steps
lem-box-cP-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-box-cP-at03243240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1420 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 2 4 (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-QVQ-at03243240 c4) ▸
       at 1 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at03243240 c4) ▸
       at 2 2 [] (wl0788 (lit c4)) ▸ done

-- sym-bc @033440: 2 steps
lem-sym-bc-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym-bc-at033440 c4 = run b0
  where
  b0 : Chain (Bx3-1240 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at033440 c4)) ▸
       at 0 3 (Bx3-1420 ∷ []) (lem-nat-SWbc-at033440 c4) ▸ done

-- sym-bc @03243240: 2 steps
lem-sym-bc-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-sym-bc-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-1240 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at03243240 c4)) ▸
       at 0 3 (Bx3-1240 ∷ []) (lem-nat-SWbc-at03243240 c4) ▸ done

-- box-cP @033440: 12 steps
lem-box-cP-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-box-cP-at033440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1240 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 2 4 (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-QVQ-at033440 c4) ▸
       at 1 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at033440 c4) ▸
       at 2 2 [] (wl0489 (lit c4)) ▸ done

-- sym-bc @03103441: 2 steps
lem-sym-bc-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym-bc-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at03103441 c4)) ▸
       at 0 3 (Bx3-0421 ∷ []) (lem-nat-SWbc-at03103441 c4) ▸ done

-- box-cP @0310243241: 12 steps
lem-box-cP-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0310243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0421 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 2 4 (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-QVQ-at0310243241 c4) ▸
       at 1 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243241 c4) ▸
       at 2 2 [] (wp0351 c4) ▸ done

-- sym-bc @0310243241: 2 steps
lem-sym-bc-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-sym-bc-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at0310243241 c4)) ▸
       at 0 3 (Bx3-0241 ∷ []) (lem-nat-SWbc-at0310243241 c4) ▸ done

-- box-cP @03103441: 12 steps
lem-box-cP-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-box-cP-at03103441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0241 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp1048 c4) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp1048 c4) ▸
       at 2 4 (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-QVQ-at03103441 c4) ▸
       at 1 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at03103441 c4) ▸
       at 2 2 [] (wl0787 (lit c4)) ▸ done

-- sym-bc @0310243142: 2 steps
lem-sym-bc-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym-bc-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0310243142 c4)) ▸
       at 0 3 (Bx3-0142 ∷ []) (lem-nat-SWbc-at0310243142 c4) ▸ done

-- box-perm-1324 @0310213442: 1 steps
lem-box-perm-1324-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-1324-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Bx3-0412 ∷ []) (lem-sym-bc-at0310213442 c4) ▸ done

-- sym-bc @0312203441: 2 steps
lem-sym-bc-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-sym-bc-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 0 1 (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) (sym (lem-SWbc-box-at0312203441 c4)) ▸
       at 0 3 (Bx3-2401 ∷ []) (lem-nat-SWbc-at0312203441 c4) ▸ done

-- box-cP @0312243041: 12 steps
lem-box-cP-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-box-cP-at0312243041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2401 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 2 4 (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-QVQ-at0312243041 c4) ▸
       at 1 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at0312243041 c4) ▸
       at 2 2 [] (wl0442 (lit c4)) ▸ done

-- sym-bc @0312243041: 2 steps
lem-sym-bc-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-sym-bc-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 1 (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) (sym (lem-SWbc-box-at0312243041 c4)) ▸
       at 0 3 (Bx3-2041 ∷ []) (lem-nat-SWbc-at0312243041 c4) ▸ done

-- box-cP @0312203441: 12 steps
lem-box-cP-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-box-cP-at0312203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2041 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 2 4 (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-QVQ-at0312203441 c4) ▸
       at 1 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at0312203441 c4) ▸
       at 2 2 [] (wl0787 (lit c4)) ▸ done

-- sym-bc @3443: 2 steps
lem-sym-bc-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym-bc-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at3443 c4)) ▸
       at 0 3 (Bx0-1423 ∷ []) (lem-nat-SWbc-at3443 c4) ▸ done

-- sym-bc @031031: 2 steps
lem-sym-bc-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym-bc-at031031 c4 = run b0
  where
  b0 : Chain (Bx3-0214 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at031031 c4)) ▸
       at 0 3 (Bx3-0124 ∷ []) (lem-nat-SWbc-at031031 c4) ▸ done

-- box-cP @031031: 12 steps
lem-box-cP-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-box-cP-at031031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0214 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 2 4 (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-QVQ-at031031 c4) ▸
       at 1 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at031031 c4) ▸
       at 2 2 [] (wl0787 (lit c4)) ▸ done

-- pairs @03102132: 4 steps
lem-pairs-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-pairs-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 0 1 (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) (sym (lem-P-box-at03102132 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸
       at 4 2 [] (wl0442 (lit c4)) ▸
       at 0 4 (Bx3-2401 ∷ []) (sym (lem-box-tQ-at0312243041 c4)) ▸ done

-- sym-bc @03143041: 2 steps
lem-sym-bc-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym-bc-at03143041 c4 = run b0
  where
  b0 : Chain (Bx3-4201 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at03143041 c4)) ▸
       at 0 3 (Bx3-4021 ∷ []) (lem-nat-SWbc-at03143041 c4) ▸ done

-- sym-bc @02142041: 2 steps
lem-sym-bc-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-sym-bc-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-4301 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at02142041 c4)) ▸
       at 0 3 (Bx2-4301 ∷ []) (lem-nat-SWbc-at02142041 c4) ▸ done

-- sym-bc @0314203241: 2 steps
lem-sym-bc-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-sym-bc-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-4201 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at0314203241 c4)) ▸
       at 0 3 (Bx3-4201 ∷ []) (lem-nat-SWbc-at0314203241 c4) ▸ done

-- pairs @0214233041: 4 steps
lem-pairs-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-pairs-at0214233041 c4 = run b0
  where
  b0 : Chain (Bx2-4301 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 1 (Toff201 ∷ Bx2-4301 ∷ Toff201 ∷ []) (sym (lem-P-box-at0214233041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4) ▸
       at 4 2 [] (wl0421 (lit c4)) ▸
       at 0 4 (Bx2-0143 ∷ []) (sym (lem-box-tQ-at0210213443 c4)) ▸ done

-- pairs @0210213443: 4 steps
lem-pairs-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-pairs-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-4301 ∷ [])
  b0 = at 0 1 (Toff234 ∷ Bx2-0143 ∷ Toff234 ∷ []) (sym (lem-P-box-at0210213443 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0210213443 c4) ▸
       at 4 2 [] (wl0420 (lit c4)) ▸
       at 0 4 (Bx2-4301 ∷ []) (sym (lem-box-tQ-at0214233041 c4)) ▸ done

-- box-perm-2314 @0213243041: 2 steps
lem-box-perm-2314-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-box-perm-2314-at0213243041 c4 = run b0
  where
  b0 : Chain (Bx2-3401 ∷ []) (Bx2-4031 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-sym-ab-at0213243041 c4) ▸
       at 0 1 (Bx2-4031 ∷ []) (lem-sym-bc-at0214233041 c4) ▸ done

-- sym-bc @02132130: 2 steps
lem-sym-bc-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-sym-bc-at02132130 c4 = run b0
  where
  b0 : Chain (Bx2-3104 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at02132130 c4)) ▸
       at 0 3 (Bx2-3014 ∷ []) (lem-nat-SWbc-at02132130 c4) ▸ done

-- box-cP @03143041: 12 steps
lem-box-cP-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-box-cP-at03143041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4201 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 2 4 (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-QVQ-at03143041 c4) ▸
       at 1 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143041 c4) ▸
       at 2 2 [] (wl0442 (lit c4)) ▸ done

-- box-cP @02132031: 12 steps
lem-box-cP-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at02132031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3014 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ123 ∷ Toff312 ∷ CZ34 ∷ Toff312 ∷ CCZ123 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wl1341 (lit c4)) ▸
       at 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ123 ∷ Toff312 ∷ CZ34 ∷ Toff312 ∷ CCZ123 ∷ CZ34 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wl1341 (lit c4)) ▸
       at 2 4 (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-QVQ-at02132031 c4) ▸
       at 1 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at02132031 c4) ▸
       at 2 2 [] (wl0635 (lit c4)) ▸ done

-- pairs @0310213442: 4 steps
lem-pairs-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-pairs-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-4201 ∷ [])
  b0 = at 0 1 (Toff324 ∷ Bx3-0142 ∷ Toff324 ∷ []) (sym (lem-P-box-at0310213442 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at0310213442 c4) ▸
       at 4 2 [] (wl0442 (lit c4)) ▸
       at 0 4 (Bx3-4201 ∷ []) (sym (lem-box-tQ-at03143041 c4)) ▸ done

-- sym-bc @02132031: 2 steps
lem-sym-bc-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-sym-bc-at02132031 c4 = run b0
  where
  b0 : Chain (Bx2-3014 ∷ []) (Bx2-3104 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at02132031 c4)) ▸
       at 0 3 (Bx2-3104 ∷ []) (lem-nat-SWbc-at02132031 c4) ▸ done

-- box-cP @02132130: 12 steps
lem-box-cP-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-box-cP-at02132130 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3104 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 2 4 (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-QVQ-at02132130 c4) ▸
       at 1 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at02132130 c4) ▸
       at 2 2 [] (wl0180 (lit c4)) ▸ done

-- pairs @0213243041: 4 steps
lem-pairs-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-pairs-at0213243041 c4 = run b0
  where
  b0 : Chain (Bx2-3401 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Toff201 ∷ Bx2-3401 ∷ Toff201 ∷ []) (sym (lem-P-box-at0213243041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 4 2 [] (wl0421 (lit c4)) ▸
       at 0 4 (Bx2-0134 ∷ []) (sym (lem-box-tQ-at021021 c4)) ▸ done

-- sym-bc @03122130: 2 steps
lem-sym-bc-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-sym-bc-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ []) (Bx3-2014 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at03122130 c4)) ▸
       at 0 3 (Bx3-2014 ∷ []) (lem-nat-SWbc-at03122130 c4) ▸ done

-- pairs @021021: 4 steps
lem-pairs-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-pairs-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-3401 ∷ [])
  b0 = at 0 1 (Toff234 ∷ Bx2-0134 ∷ Toff234 ∷ []) (sym (lem-P-box-at021021 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at021021 c4) ▸
       at 4 2 [] (wl0420 (lit c4)) ▸
       at 0 4 (Bx2-3401 ∷ []) (sym (lem-box-tQ-at0213243041 c4)) ▸ done

-- box-cP @03122031: 12 steps
lem-box-cP-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-box-cP-at03122031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2014 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wl1303 (lit c4)) ▸
       at 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wl1303 (lit c4)) ▸
       at 2 4 (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-QVQ-at03122031 c4) ▸
       at 1 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at03122031 c4) ▸
       at 2 2 [] (wl0787 (lit c4)) ▸ done

-- sym-bc @03122031: 2 steps
lem-sym-bc-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-sym-bc-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Bx3-2104 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at03122031 c4)) ▸
       at 0 3 (Bx3-2104 ∷ []) (lem-nat-SWbc-at03122031 c4) ▸ done

-- box-cP @03122130: 12 steps
lem-box-cP-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-box-cP-at03122130 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2104 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 2 4 (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-QVQ-at03122130 c4) ▸
       at 1 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at03122130 c4) ▸
       at 2 2 [] (wl0489 (lit c4)) ▸ done
