{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D021 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0190 ; wl0191 ; wl0193 ; wl0194 ; wl0195 ; wl0196 ; wl0197 ; wl0217 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0241 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0263 ; wl0305 ; wl0747 ; wl1000 ; wl1037 ; wp0021 ; wp0032 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0038 ; wp0041 ; wp0044 ; wp0053 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0069 ; wp0070 ; wp0072 ; wp0074 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0094 ; wp0095 ; wp0097 ; wp0161 ; wp0651 ; wp0654 ; wp0805 ; wp0806 ; wp0842 ; wp0843 ; wp0845 ; wl0180 ; wl0181 ; wl0186 ; wl0204 ; wl0230 ; wl0280 ; wl0289 ; wl0621 ; wl0671 ; wl1127 ; wl1128 ; wl1129 ; wl1130 ; wl1131 ; wp0019 ; wp0024 ; wp0039 ; wp0513 ; wp0523 ; wp0820 ; wp0919 ; wl0183 ; wl0185 ; wl0209 ; wl0210 ; wl0229 ; wl0234 ; wl0905 ; wp0020 ; wp0023 ; wp0067 ; wp0080 ; wp0092 ; wp0756 ; wp0796 ; wp0797 ; wp0798 ; wl0203 ; wl0206 ; wl0208 ; wl0242 ; wl0324 ; wl0326 ; wp0051 ; wp0052 ; wp0055 ; wp0795 ; wp0970 ; wl0232 ; wl0293 ; wl0442 ; wl0443 ; wl0645 ; wl0698 ; wl0787 ; wl0788 ; wl0974 ; wl1182 ; wp0006 ; wp0189 ; wp0394 ; wp0590 ; wp0740 ; wp0742 ; wp0743 ; wp0749 ; wp0990 ; wp0993 ; wp0994 ; wp0995 ; wp0996 ; wl0155 ; wl0323 ; wl0336 ; wl0432 ; wl0433 ; wl0489 ; wl1191 ; wl1192 ; wl1193 ; wl1194 ; wl1200 ; wl1201 ; wl1202 ; wl1207 ; wp0001 ; wp0003 ; wp0007 ; wp0261 ; wp0272 ; wp0294 ; wp0351 ; wp0725 ; wp0823 ; wp1010 ; wp1011 ; wl0348 ; wl0391 ; wl0415 ; wl0503 ; wl0512 ; wl1243 ; wl1251 ; wp0333 ; wl0679 ; wl1071 ; wl1265 ; wl1273 ; wl1274 ; wl1275 ; wl1276 ; wl1279 ; wl1280 ; wl1281 ; wl1282 ; wp0221 ; wp0366)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym-ab-at0210243143 ; lem-sym-ab-at0214203143 ; lem-sym-ab-at03102132 ; lem-sym-ab-at0314203142 ; lem-sym-ab-at13243142 ; lem-sym-ab-at14233142 ; lem-sym-ab-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym-ab-at0213243041 ; lem-sym-ab-at0214233041 ; lem-sym-ab-at03122031 ; lem-sym-ab-at03122130 ; lem-sym-ab-at0312243041 ; lem-sym-ab-at0314213240 ; lem-sym-ab-at03143041 ; lem-sym-ab-at03243240 ; lem-sym-ab-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym-ab-at02132031 ; lem-sym-ab-at02132130)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-tQ-at03102132 ; lem-box-tQ-at14233241)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0214203143 ; lem-box-tQ-at0310243142 ; lem-box-tQ-at0314203142 ; lem-box-tQ-at0314213042 ; lem-box-tQ-at033440 ; lem-box-tQ-at13213442 ; lem-box-tQ-at1331 ; lem-box-tQ-at143143)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at02102441 ; lem-box-tQ-at02132130 ; lem-box-tQ-at02142041 ; lem-box-tQ-at02233440 ; lem-box-tQ-at0310243241 ; lem-box-tQ-at031031 ; lem-box-tQ-at03103441 ; lem-box-tQ-at03122031 ; lem-box-tQ-at0312203441 ; lem-box-tQ-at03122130 ; lem-box-tQ-at0314203241 ; lem-box-tQ-at0314213240 ; lem-box-tQ-at03143140 ; lem-box-tQ-at03243042 ; lem-box-tQ-at03243240 ; lem-box-tQ-at142142)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-P-box-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-P-box-at02233440 ; lem-P-box-at03103441 ; lem-P-box-at0312203441 ; lem-P-box-at0314203142 ; lem-P-box-at0314213042 ; lem-P-box-at0314213240 ; lem-P-box-at03243240 ; lem-P-box-at033440 ; lem-P-box-at12213443 ; lem-P-box-at1441 ; lem-P-box-at233442 ; lem-t-cP-at0310243142 ; lem-t-cP-at03143140 ; lem-t-cP-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-P-box-at02102441 ; lem-P-box-at02132130 ; lem-P-box-at0310243241 ; lem-P-box-at031031 ; lem-P-box-at03122130 ; lem-P-box-at0312243041 ; lem-P-box-at03143041 ; lem-P-box-at03243042 ; lem-P-box-at2442 ; lem-t-cP-at02142041 ; lem-t-cP-at0314203241 ; lem-t-cP-at033440 ; lem-t-cP-at142142)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-sym-bc-at0210213443 ; lem-sym-bc-at0214233041)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0210243143 ; lem-box-cP-at02102441 ; lem-box-cP-at02132130 ; lem-box-cP-at0214203143 ; lem-box-cP-at02233440 ; lem-box-cP-at022440 ; lem-box-cP-at0310243142 ; lem-box-cP-at0310243241 ; lem-box-cP-at031031 ; lem-box-cP-at03103441 ; lem-box-cP-at0312203441 ; lem-box-cP-at03122130 ; lem-box-cP-at0312243041 ; lem-box-cP-at0314203142 ; lem-box-cP-at0314213042 ; lem-box-cP-at0314213240 ; lem-box-cP-at03143041 ; lem-box-cP-at03143140 ; lem-box-cP-at03243240 ; lem-box-cP-at033440 ; lem-box-cP-at12213443 ; lem-box-cP-at12243143 ; lem-box-cP-at122441 ; lem-box-cP-at13213442 ; lem-box-cP-at1441 ; lem-box-cP-at233442 ; lem-box-cP-at243243 ; lem-box-cP-at2442 ; lem-pairs-at021021 ; lem-pairs-at0210213443 ; lem-pairs-at0213243041 ; lem-pairs-at0214233041 ; lem-pairs-at03102132 ; lem-pairs-at0310213442 ; lem-pairs-at13243142 ; lem-pairs-at14233142 ; lem-sym-bc-at0210233441 ; lem-sym-bc-at0210243143 ; lem-sym-bc-at02102441 ; lem-sym-bc-at02142041 ; lem-sym-bc-at022330 ; lem-sym-bc-at02233440 ; lem-sym-bc-at022440 ; lem-sym-bc-at0310243142 ; lem-sym-bc-at0310243241 ; lem-sym-bc-at031031 ; lem-sym-bc-at03103441 ; lem-sym-bc-at0312203441 ; lem-sym-bc-at0312243041 ; lem-sym-bc-at0314203241 ; lem-sym-bc-at0314213240 ; lem-sym-bc-at03143041 ; lem-sym-bc-at03143140 ; lem-sym-bc-at03243240 ; lem-sym-bc-at0330 ; lem-sym-bc-at033440 ; lem-sym-bc-at12213443 ; lem-sym-bc-at12233441 ; lem-sym-bc-at12243143 ; lem-sym-bc-at13213442 ; lem-sym-bc-at14213243 ; lem-sym-bc-at143143 ; lem-sym-bc-at233442 ; lem-sym-bc-at2442 ; lem-sym-bc-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at02142041 ; lem-box-cP-at0314203241 ; lem-box-cP-at03243042 ; lem-box-cP-at142142 ; lem-sym-bc-at02102331 ; lem-sym-bc-at142142)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS03-CCZ124 ; lem-comm-CS12-CCZ034 ; lem-comm-CS13-CCZ024 ; lem-comm-CS23-CCZ014 ; lem-comm-CS24-CCZ013 ; lem-comm-CSd03-CCZ124 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CSd24-CCZ013 ; lem-comm-CX14-CCZ023 ; lem-comm-CX14-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CX13 ; lem-comm-CS02-CCZ134 ; lem-comm-CSd02-CCZ134 ; lem-comm-CX31-TOFF024 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF213-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CX14)

-- nf-comm-CS-S0@2: 83 steps
lem-nf-comm-CS-S0at2 : Ws → ⟪ (CS24 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-nf-comm-CS-S0at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CS24 ∷ Sb0-2-43-1 ∷ []) (CS24 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 3 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b1 : Chain (CS24 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 2 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b2 : Chain (CS24 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 4 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 3 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 4 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 3 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b3 : Chain (CS24 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 2 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 2 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b4 : Chain (CS24 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 2 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸ done

  b5 : Chain (CS24 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ [])
  b5 = at 3 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 6 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 8 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b6 : Chain (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b6 = at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 8 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸ done

  b7 : Chain (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b7 = at 6 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 10 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 5 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸ done

  b8 : Chain (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b8 = at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b9 : Chain (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b9 = at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 9 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 8 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸ done

  b10 : Chain (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (CS24 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b10 = at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸ done

-- nf-comm-CS-S1@0: 83 steps
lem-nf-comm-CS-S1at0 : Ws → ⟪ (CS14 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-nf-comm-CS-S1at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CS14 ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 3 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b1 : Chain (CS14 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 2 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸ done

  b2 : Chain (CS14 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 3 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 4 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 5 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 6 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 7 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸ done

  b3 : Chain (CS14 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b3 = at 2 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b4 : Chain (CS14 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b4 = at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 2 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 5 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 4 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸ done

  b5 : Chain (CS14 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ [])
  b5 = at 3 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b6 : Chain (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b6 = at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 8 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 5 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸
       at 7 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b7 : Chain (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b7 = at 6 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 7 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 8 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 10 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 5 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸ done

  b8 : Chain (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b8 = at 4 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b9 : Chain (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b9 = at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 9 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸ done

  b10 : Chain (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (CS14 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ [])
  b10 = at 7 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 3 (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp0651 c4) ▸
       at 3 2 [] (wp0161 c4) ▸ done

-- nf-comm-CS-S1@1: 83 steps
lem-nf-comm-CS-S1at1 : Ws → ⟪ (CS24 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-nf-comm-CS-S1at1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CS24 ∷ Sb0-1-42-3 ∷ []) (CS24 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 3 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b1 : Chain (CS24 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 2 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸ done

  b2 : Chain (CS24 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 4 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 3 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 4 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸ done

  b3 : Chain (CS24 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 2 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 3 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 4 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b4 : Chain (CS24 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 7 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 2 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b5 : Chain (CS24 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ [])
  b5 = at 3 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 6 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 9 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸ done

  b6 : Chain (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b6 = at 10 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 12 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸ done

  b7 : Chain (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b7 = at 6 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 10 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 5 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸ done

  b8 : Chain (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b8 = at 4 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸ done

  b9 : Chain (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b9 = at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 9 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 8 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸ done

  b10 : Chain (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (CS24 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b10 = at 7 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 3 2 [] (wl0263 (lit c4)) ▸ done

-- nf-comm-CS-S1@2: 83 steps
lem-nf-comm-CS-S1at2 : Ws → ⟪ (CS34 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-nf-comm-CS-S1at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CS34 ∷ Sb0-2-43-1 ∷ []) (CS34 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 3 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b1 : Chain (CS34 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 2 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b2 : Chain (CS34 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 4 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 3 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 4 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 3 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b3 : Chain (CS34 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 2 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 2 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b4 : Chain (CS34 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 2 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸ done

  b5 : Chain (CS34 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ [])
  b5 = at 3 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 6 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 8 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b6 : Chain (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b6 = at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 8 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸ done

  b7 : Chain (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b7 = at 6 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 10 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 5 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸ done

  b8 : Chain (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b8 = at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b9 : Chain (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b9 = at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 9 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 8 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸ done

  b10 : Chain (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (CS34 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b10 = at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸ done

-- pairs @0214203143: 4 steps
lem-pairs-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-pairs-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 0 1 (Toff213 ∷ Bx2-4013 ∷ Toff213 ∷ []) (sym (lem-P-box-at0214203143 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 4 2 [] (wl0180 (lit c4)) ▸
       at 0 4 (Bx2-1340 ∷ []) (sym (lem-box-tQ-at02233440 c4)) ▸ done

-- box-perm-1324 @02233440: 1 steps
lem-box-perm-1324-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-box-perm-1324-at02233440 c4 = run b0
  where
  b0 : Chain (Bx2-1340 ∷ []) (Bx2-1430 ∷ [])
  b0 = at 0 1 (Bx2-1430 ∷ []) (lem-sym-bc-at02233440 c4) ▸ done

-- Xb-box @022440: 18 steps
lem-Xb-box-at022440 : Ws → ⟪ (X4 ∷ Bx2-1430 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CCZ013 ∷ []) ⟫ʷ
lem-Xb-box-at022440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx2-1430 ∷ X4 ∷ []) (CCZ124 ∷ Toff203 ∷ X4 ∷ CZ12 ∷ CS03 ∷ CX13 ∷ CCZ124 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff203 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at022440 c4) ▸
       at 0 2 (CCZ124 ∷ X4 ∷ CZ12 ∷ []) (sym (wl1127 (lit c4))) ▸
       at 2 2 (Toff203 ∷ CZ12 ∷ CCZ013 ∷ []) (wl1128 (lit c4)) ▸
       at 1 2 (Toff203 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 8 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 7 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸ done

  b1 : Chain (CCZ124 ∷ Toff203 ∷ X4 ∷ CZ12 ∷ CS03 ∷ CX13 ∷ CCZ124 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff203 ∷ X4 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X4 ∷ CCZ013 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 4 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CZ12 ∷ []) (sym (wl1129 (lit c4))) ▸
       at 2 2 (CCZ124 ∷ X4 ∷ CZ12 ∷ []) (sym (wl1127 (lit c4))) ▸
       at 3 3 (X4 ∷ []) (wl1130 (lit c4)) ▸
       at 4 2 (Toff203 ∷ CCZ013 ∷ []) (wl1131 (lit c4)) ▸
       at 3 2 (Toff203 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b2 : Chain (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (Bx2-1430 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-1430 ∷ []) (sym (lem-box-cP-at022440 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wp0024 c4)) ▸ done

-- box-perm-1324 @022440: 1 steps
lem-box-perm-1324-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-box-perm-1324-at022440 c4 = run b0
  where
  b0 : Chain (Bx2-1430 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 0 1 (Bx2-1340 ∷ []) (lem-sym-bc-at022440 c4) ▸ done

-- pairs @02233440: 4 steps
lem-pairs-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-pairs-at02233440 c4 = run b0
  where
  b0 : Chain (Bx2-1340 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 1 (Toff204 ∷ Bx2-1340 ∷ Toff204 ∷ []) (sym (lem-P-box-at02233440 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02233440 c4) ▸
       at 4 2 [] (wp0019 c4) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-tQ-at0214203143 c4)) ▸ done

-- box-perm-1324 @12233441: 1 steps
lem-box-perm-1324-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-1324-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-2431 ∷ []) (lem-sym-bc-at12233441 c4) ▸ done

-- pairs @1441: 4 steps
lem-pairs-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-pairs-at1441 c4 = run b0
  where
  b0 : Chain (Bx0-4231 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Toff013 ∷ Bx0-4231 ∷ Toff013 ∷ []) (sym (lem-P-box-at1441 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at1441 c4) ▸
       at 4 2 [] (wl0229 (lit c4)) ▸
       at 0 4 (Bx0-3142 ∷ []) (sym (lem-box-tQ-at13213442 c4)) ▸ done

-- box-perm-1324 @13213442: 1 steps
lem-box-perm-1324-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-box-perm-1324-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-sym-bc-at13213442 c4) ▸ done

-- box-perm-1324 @0210233441: 1 steps
lem-box-perm-1324-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-box-perm-1324-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 0 1 (Bx2-0431 ∷ []) (lem-sym-bc-at0210233441 c4) ▸ done

-- Xb-box @02102441: 18 steps
lem-Xb-box-at02102441 : Ws → ⟪ (X4 ∷ Bx2-0431 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ013 ∷ []) ⟫ʷ
lem-Xb-box-at02102441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx2-0431 ∷ X4 ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX03 ∷ CCZ024 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff213 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at02102441 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 2 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl0183 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 7 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX03 ∷ CCZ024 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff213 ∷ X4 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CCZ013 ∷ []) (wl0186 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (Bx2-0431 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-0431 ∷ []) (sym (lem-box-cP-at02102441 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wp0024 c4)) ▸ done

-- box-perm-1324 @02102441: 1 steps
lem-box-perm-1324-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-box-perm-1324-at02102441 c4 = run b0
  where
  b0 : Chain (Bx2-0431 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 1 (Bx2-0341 ∷ []) (lem-sym-bc-at02102441 c4) ▸ done

-- box-perm-1324 @233442: 1 steps
lem-box-perm-1324-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-box-perm-1324-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 1 (Bx0-1432 ∷ []) (lem-sym-bc-at233442 c4) ▸ done

-- Xb-box @2442: 18 steps
lem-Xb-box-at2442 : Ws → ⟪ (X4 ∷ Bx0-1432 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at2442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx0-1432 ∷ X4 ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX13 ∷ CCZ014 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff023 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at2442 c4) ▸
       at 0 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 7 2 (CCZ014 ∷ CX13 ∷ []) (sym (wp0795 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX13 ∷ CCZ014 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff023 ∷ X4 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ014 ∷ CX13 ∷ []) (sym (wp0795 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0208 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b2 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (Bx0-1432 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-1432 ∷ []) (sym (lem-box-cP-at2442 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0210 (lit c4))) ▸ done

-- box-perm-1324 @2442: 1 steps
lem-box-perm-1324-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-box-perm-1324-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 1 (Bx0-1342 ∷ []) (lem-sym-bc-at2442 c4) ▸ done

-- pairs @233442: 4 steps
lem-pairs-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-pairs-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 1 (Toff024 ∷ Bx0-1342 ∷ Toff024 ∷ []) (sym (lem-P-box-at233442 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at233442 c4) ▸
       at 4 2 [] (wp0080 c4) ▸
       at 0 4 (Bx0-4213 ∷ []) (sym (lem-box-tQ-at143143 c4)) ▸ done

-- box-perm-1324 @12213443: 1 steps
lem-box-perm-1324-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-box-perm-1324-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 1 (Bx0-2413 ∷ []) (lem-sym-bc-at12213443 c4) ▸ done

-- Xb-box @12243143: 18 steps
lem-Xb-box-at12243143 : Ws → ⟪ (X4 ∷ Bx0-2413 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at12243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx0-2413 ∷ X4 ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX21 ∷ CCZ024 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff013 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at12243143 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 2 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl0232 (lit c4)) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX21 ∷ CCZ024 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff013 ∷ X4 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (Bx0-2413 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-2413 ∷ []) (sym (lem-box-cP-at12243143 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0210 (lit c4))) ▸ done

-- box-perm-1324 @12243143: 1 steps
lem-box-perm-1324-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-box-perm-1324-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Bx0-2143 ∷ []) (lem-sym-bc-at12243143 c4) ▸ done

-- pairs @12213443: 4 steps
lem-pairs-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-pairs-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-4321 ∷ [])
  b0 = at 0 1 (Toff034 ∷ Bx0-2143 ∷ Toff034 ∷ []) (sym (lem-P-box-at12213443 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at12213443 c4) ▸
       at 4 2 [] (wp0006 c4) ▸
       at 0 4 (Bx0-4321 ∷ []) (sym (lem-box-tQ-at14233241 c4)) ▸ done

-- box-perm-2314 @243243: 2 steps
lem-box-perm-2314-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-box-perm-2314-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸
       at 0 1 (Bx0-4213 ∷ []) (lem-sym-bc-at14213243 c4) ▸ done

-- box-perm-1324 @03143140: 1 steps
lem-box-perm-1324-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-box-perm-1324-at03143140 c4 = run b0
  where
  b0 : Chain (Bx3-4210 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 1 (Bx3-4120 ∷ []) (lem-sym-bc-at03143140 c4) ▸ done

-- box-perm-3124 @03143140: 2 steps
lem-box-perm-3124-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-3124-at03143140 c4 = run b0
  where
  b0 : Chain (Bx3-4210 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 1 (Bx3-4120 ∷ []) (lem-sym-bc-at03143140 c4) ▸
       at 0 1 (Bx3-1420 ∷ []) (lem-sym-ab-at0314213240 c4) ▸ done

-- box-box-4 @03243240: 103 steps
lem-box-box-4-at03243240 : Ws → ⟪ (Bx3-1420 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-box-box-4-at03243240 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Bx3-1420 ∷ Bx0-3142 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ013 ∷ Toff024 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ CCZ013 ∷ CX34 ∷ CS23 ∷ CCZ023 ∷ Toff024 ∷ [])
  b0 = at 0 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243240 c4) ▸
       at 4 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at13213442 c4) ▸
       at 3 2 (CCZ013 ∷ CCZ023 ∷ []) (sym (wl0671 (lit c4))) ▸
       at 4 2 (Toff024 ∷ CCZ234 ∷ CCZ023 ∷ []) (wp0993 c4) ▸
       at 6 2 (CCZ013 ∷ CCZ023 ∷ []) (sym (wl0671 (lit c4))) ▸
       at 5 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 8 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ013 ∷ Toff024 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ CCZ013 ∷ CX34 ∷ CS23 ∷ CCZ023 ∷ Toff024 ∷ []) (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff314 ∷ CCZ014 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 6 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸
       at 5 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸
       at 6 3 (Toff024 ∷ CCZ023 ∷ []) (wp0994 c4) ▸
       at 3 4 (Bx0-3142 ∷ []) (sym (lem-box-cP-at13213442 c4)) ▸
       at 3 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at13213442 c4) ▸
       at 2 2 (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0990 c4)) ▸ done

  b2 : Chain (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff314 ∷ CCZ014 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ []) (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ K3 ∷ Toff024 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CCZ124 ∷ CCZ014 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ [])
  b2 = at 4 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 3 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 9 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 8 2 (Toff024 ∷ CS34 ∷ []) (wp0970 c4) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 6 2 (Toff024 ∷ CS14⁻ ∷ []) (wp0995 c4) ▸
       at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 4 2 (Toff024 ∷ CS14 ∷ []) (wp0590 c4) ▸ done

  b3 : Chain (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ K3 ∷ Toff024 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CCZ124 ∷ CCZ014 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ []) (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff024 ∷ Toff314 ∷ CS24 ∷ CCZ013 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ014 ∷ Toff024 ∷ CCZ023 ∷ [])
  b3 = at 3 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 4 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 6 2 (CCZ013 ∷ CCZ014 ∷ []) (sym (wp0394 c4)) ▸
       at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ CS12 ∷ []) (sym (wl0645 (lit c4))) ▸
       at 8 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸
       at 7 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 6 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸ done

  b4 : Chain (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff024 ∷ Toff314 ∷ CS24 ∷ CCZ013 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ014 ∷ Toff024 ∷ CCZ023 ∷ []) (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ Toff024 ∷ CS34 ∷ K3⁻ ∷ CCZ124 ∷ CCZ023 ∷ [])
  b4 = at 5 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0990 c4)) ▸
       at 6 3 (CCZ124 ∷ []) (wp0996 c4) ▸
       at 6 2 (Toff024 ∷ CCZ124 ∷ []) (wp0743 c4) ▸
       at 5 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 11 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 10 2 (Toff024 ∷ CS34 ∷ []) (wp0970 c4) ▸ done

  b5 : Chain (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ Toff024 ∷ CS34 ∷ K3⁻ ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b5 = at 9 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 8 2 (Toff024 ∷ CS14⁻ ∷ []) (wp0995 c4) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 6 2 (Toff024 ∷ CS14 ∷ []) (wp0590 c4) ▸
       at 5 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 6 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 2 4 (Bx0-3142 ∷ []) (sym (lem-box-cP-at13213442 c4)) ▸
       at 2 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at13213442 c4) ▸ done

  b6 : Chain (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff314 ∷ CCZ013 ∷ Toff024 ∷ CS24 ∷ CCZ013 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ CCZ023 ∷ Toff024 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b6 = at 1 2 (CCZ013 ∷ CCZ023 ∷ []) (sym (wl0671 (lit c4))) ▸
       at 2 2 (Toff024 ∷ CCZ234 ∷ CCZ023 ∷ []) (wp0993 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ023 ∷ []) (sym (wl0671 (lit c4))) ▸
       at 3 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 7 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸
       at 5 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸ done

  b7 : Chain (Toff314 ∷ CCZ013 ∷ Toff024 ∷ CS24 ∷ CCZ013 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ CCZ023 ∷ Toff024 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ013 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b7 = at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 4 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸
       at 4 3 (Toff024 ∷ CCZ023 ∷ []) (wp0994 c4) ▸
       at 1 4 (Bx0-3142 ∷ []) (sym (lem-box-cP-at13213442 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at13213442 c4) ▸
       at 0 2 (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0990 c4)) ▸
       at 2 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 1 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸ done

  b8 : Chain (CCZ013 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ013 ∷ Toff024 ∷ Toff314 ∷ CCZ124 ∷ CCZ014 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b8 = at 7 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 6 2 (Toff024 ∷ CS34 ∷ []) (wp0970 c4) ▸
       at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 4 2 (Toff024 ∷ CS14⁻ ∷ []) (wp0995 c4) ▸
       at 3 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 2 2 (Toff024 ∷ CS14 ∷ []) (wp0590 c4) ▸
       at 1 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 2 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸ done

  b9 : Chain (CCZ013 ∷ Toff024 ∷ Toff314 ∷ CCZ124 ∷ CCZ014 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ013 ∷ Toff024 ∷ Toff314 ∷ CCZ013 ∷ CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b9 = at 4 2 (CCZ013 ∷ CCZ014 ∷ []) (sym (wp0394 c4)) ▸
       at 3 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 7 2 (CCZ013 ∷ CS12 ∷ []) (sym (wl0645 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸
       at 5 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸
       at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b10 : Chain (CCZ013 ∷ Toff024 ∷ Toff314 ∷ CCZ013 ∷ CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS14 ∷ CX31 ∷ Toff024 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b10 = at 2 2 (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0990 c4)) ▸
       at 4 3 (CCZ124 ∷ []) (wp0996 c4) ▸
       at 4 2 (Toff024 ∷ CCZ124 ∷ []) (wp0743 c4) ▸
       at 3 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 9 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 8 2 (Toff024 ∷ CS34 ∷ []) (wp0970 c4) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 6 2 (Toff024 ∷ CS14⁻ ∷ []) (wp0995 c4) ▸ done

  b11 : Chain (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS14 ∷ CX31 ∷ Toff024 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (Bx0-3142 ∷ Toff314 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CCZ023 ∷ CX14 ∷ CS12 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b11 = at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 4 2 (Toff024 ∷ CS14 ∷ []) (wp0590 c4) ▸
       at 3 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 4 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 0 4 (Bx0-3142 ∷ []) (sym (lem-box-cP-at13213442 c4)) ▸
       at 2 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸ done

  b12 : Chain (Bx0-3142 ∷ Toff314 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CCZ023 ∷ CX14 ∷ CS12 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (Bx0-3142 ∷ Bx3-1420 ∷ [])
  b12 = at 4 2 (CCZ023 ∷ CS24⁻ ∷ []) (sym (wp0820 c4)) ▸
       at 3 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 3 2 (Toff314 ∷ CCZ124 ∷ []) (wl0974 (lit c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸
       at 1 4 (Bx3-1420 ∷ []) (sym (lem-box-tQ-at03243240 c4)) ▸ done

-- box-perm-2314 @03243240: 2 steps
lem-box-perm-2314-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-box-perm-2314-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-4210 ∷ [])
  b0 = at 0 1 (Bx3-4120 ∷ []) (lem-sym-ab-at03243240 c4) ▸
       at 0 1 (Bx3-4210 ∷ []) (lem-sym-bc-at0314213240 c4) ▸ done

-- CSdu-box-3 @03143140: 17 steps
lem-CSdu-box-3-at03143140 : Ws → ⟪ (CS13⁻ ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at03143140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS13⁻ ∷ Bx3-4210 ∷ []) (CCZ234 ∷ Toff301 ∷ CS13⁻ ∷ CS01⁻ ∷ CS01 ∷ CCZ234 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ Toff301 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at03143140 c4) ▸
       at 0 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 1 2 (Toff301 ∷ CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ []) (wl1191 (lit c4)) ▸
       at 4 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 8 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 7 2 (CCZ234 ∷ CX31 ∷ []) (sym (wl0336 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX31 ∷ []) (sym (wl0336 (lit c4))) ▸ done

  b1 : Chain (CCZ234 ∷ Toff301 ∷ CS13⁻ ∷ CS01⁻ ∷ CS01 ∷ CCZ234 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ Toff301 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CS13⁻ ∷ [])
  b1 = at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 5 2 (Toff301 ∷ CZ01 ∷ CCZ013 ∷ []) (wl1192 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CS01⁻ ∷ []) (wl1193 (lit c4)) ▸
       at 3 2 (Toff301 ∷ CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ []) (wl1191 (lit c4)) ▸
       at 4 6 (CS13⁻ ∷ []) (wl1194 (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CS13⁻ ∷ []) (Bx3-4210 ∷ CS13⁻ ∷ [])
  b2 = at 0 4 (Bx3-4210 ∷ []) (sym (lem-box-cP-at03143140 c4)) ▸ done

-- CSu-box-3 @03143140: 17 steps
lem-CSu-box-3-at03143140 : Ws → ⟪ (CS13 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CS13 ∷ []) ⟫ʷ
lem-CSu-box-3-at03143140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS13 ∷ Bx3-4210 ∷ []) (CCZ234 ∷ Toff301 ∷ CS13 ∷ CS01 ∷ CS01 ∷ CCZ234 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ Toff301 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at03143140 c4) ▸
       at 0 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 1 2 (Toff301 ∷ CS13 ∷ CS01 ∷ CCZ013 ∷ []) (wl1200 (lit c4)) ▸
       at 4 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 8 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 7 2 (CCZ234 ∷ CX31 ∷ []) (sym (wl0336 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX31 ∷ []) (sym (wl0336 (lit c4))) ▸ done

  b1 : Chain (CCZ234 ∷ Toff301 ∷ CS13 ∷ CS01 ∷ CS01 ∷ CCZ234 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ Toff301 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CS13 ∷ [])
  b1 = at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 5 2 (Toff301 ∷ CZ01 ∷ CCZ013 ∷ []) (wl1192 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CS01 ∷ []) (wl1201 (lit c4)) ▸
       at 3 2 (Toff301 ∷ CS13 ∷ CS01 ∷ CCZ013 ∷ []) (wl1200 (lit c4)) ▸
       at 4 6 (CS13 ∷ []) (wl1202 (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CS13 ∷ []) (Bx3-4210 ∷ CS13 ∷ [])
  b2 = at 0 4 (Bx3-4210 ∷ []) (sym (lem-box-cP-at03143140 c4)) ▸ done

-- box2 @03143140: 11 steps
lem-box2-at03143140 : Ws → ⟪ (Bx3-4210 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at03143140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4210 ∷ Bx3-4210 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ [])
  b0 = at 0 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143140 c4) ▸
       at 4 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at03143140 c4) ▸
       at 4 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 5 5 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff324 ∷ []) (lem-t-cP-at03143140 c4) ▸
       at 5 4 (Bx3-4210 ∷ []) (sym (lem-box-cP-at03143140 c4)) ▸
       at 5 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143140 c4) ▸
       at 4 2 [] (wl0442 (lit c4)) ▸
       at 3 2 [] (wl0230 (lit c4)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) []
  b1 = at 2 2 [] (wl0442 (lit c4)) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸
       at 0 2 [] (wl0442 (lit c4)) ▸ done

-- box-perm-3124 @143143: 2 steps
lem-box-perm-3124-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-3124-at143143 c4 = run b0
  where
  b0 : Chain (Bx0-4213 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-sym-bc-at143143 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4) ▸ done

-- CXu-box-4 @243243: 15 steps
lem-CXu-box-4-at243243 : Ws → ⟪ (CX30 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CX30 ∷ []) ⟫ʷ
lem-CXu-box-4-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX30 ∷ Bx0-1423 ∷ []) (CCZ014 ∷ CX30 ∷ Toff023 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ CX30 ∷ CCZ134 ∷ []) (sym (wp1010 c4)) ▸
       at 2 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 5 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CS34⁻ ∷ []) (wp0823 c4) ▸
       at 3 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 2 2 (Toff023 ∷ CS34 ∷ []) (wp0725 c4) ▸ done

  b1 : Chain (CCZ014 ∷ CX30 ∷ Toff023 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ []) (Bx0-1423 ∷ CX30 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 1 2 (Toff023 ∷ CX30 ∷ []) (wl1207 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 2 2 (CCZ014 ∷ CX30 ∷ CCZ134 ∷ []) (sym (wp1010 c4)) ▸
       at 3 3 (CX30 ∷ []) (wp1011 c4) ▸
       at 3 2 (Toff023 ∷ CX30 ∷ []) (wl1207 (lit c4)) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

-- pairs @0314203142: 4 steps
lem-pairs-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-pairs-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-1240 ∷ [])
  b0 = at 0 1 (Toff312 ∷ Bx3-4012 ∷ Toff312 ∷ []) (sym (lem-P-box-at0314203142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 4 2 [] (wl0489 (lit c4)) ▸
       at 0 4 (Bx3-1240 ∷ []) (sym (lem-box-tQ-at033440 c4)) ▸ done

-- box2 @03243240: 11 steps
lem-box2-at03243240 : Ws → ⟪ (Bx3-1420 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at03243240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1420 ∷ Bx3-1420 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b0 = at 0 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243240 c4) ▸
       at 4 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0788 (lit c4))) ▸
       at 5 5 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ []) (lem-t-cP-at03243240 c4) ▸
       at 5 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 5 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243240 c4) ▸
       at 4 2 [] (wl0788 (lit c4)) ▸
       at 3 2 [] (wl0204 (lit c4)) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) []
  b1 = at 2 2 [] (wl0788 (lit c4)) ▸
       at 1 2 [] (wl0204 (lit c4)) ▸
       at 0 2 [] (wl0788 (lit c4)) ▸ done

-- box-perm-1324 @03243240: 1 steps
lem-box-perm-1324-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-box-perm-1324-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-1240 ∷ [])
  b0 = at 0 1 (Bx3-1240 ∷ []) (lem-sym-bc-at03243240 c4) ▸ done

-- pairs @033440: 4 steps
lem-pairs-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-pairs-at033440 c4 = run b0
  where
  b0 : Chain (Bx3-1240 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Toff304 ∷ Bx3-1240 ∷ Toff304 ∷ []) (sym (lem-P-box-at033440 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4) ▸
       at 4 2 [] (wp0351 c4) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-tQ-at0314203142 c4)) ▸ done

-- box2 @0310243142: 11 steps
lem-box2-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0310243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0412 ∷ Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  b0 = at 0 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4) ▸
       at 4 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 4 0 (Toff304 ∷ Toff304 ∷ []) (sym (wp0351 c4)) ▸
       at 5 5 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ []) (lem-t-cP-at0310243142 c4) ▸
       at 5 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 5 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4) ▸
       at 4 2 [] (wp0351 c4) ▸
       at 3 2 [] (wl0181 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) []
  b1 = at 2 2 [] (wp0351 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸
       at 0 2 [] (wp0351 c4) ▸ done

-- pairs @0314213042: 4 steps
lem-pairs-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-pairs-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 1 (Toff302 ∷ Bx3-4102 ∷ Toff302 ∷ []) (sym (lem-P-box-at0314213042 c4)) ▸
       at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213042 c4) ▸
       at 4 2 [] (wl0787 (lit c4)) ▸
       at 0 4 (Bx3-0241 ∷ []) (sym (lem-box-tQ-at03103441 c4)) ▸ done

-- box-perm-1324 @03103441: 1 steps
lem-box-perm-1324-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-box-perm-1324-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 0 1 (Bx3-0421 ∷ []) (lem-sym-bc-at03103441 c4) ▸ done

-- Xb-box @0310243241: 18 steps
lem-Xb-box-at0310243241 : Ws → ⟪ (X4 ∷ Bx3-0421 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Xb-box-at0310243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx3-0421 ∷ X4 ∷ []) (CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX02 ∷ CCZ034 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Toff312 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243241 c4) ▸
       at 0 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 2 2 (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) (wl0512 (lit c4)) ▸
       at 1 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸
       at 4 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 7 2 (CCZ034 ∷ CX02 ∷ []) (sym (wp0333 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX02 ∷ CCZ034 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Toff312 ∷ X4 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CCZ012 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ034 ∷ CX02 ∷ []) (sym (wp0333 c4)) ▸
       at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CZ03 ∷ []) (sym (wp0797 c4)) ▸
       at 2 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 3 3 (X4 ∷ []) (wp0798 c4) ▸
       at 4 2 (Toff312 ∷ CCZ012 ∷ []) (wl0503 (lit c4)) ▸
       at 3 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸ done

  b2 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (Bx3-0421 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-0421 ∷ []) (sym (lem-box-cP-at0310243241 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wl1243 (lit c4))) ▸ done

-- box-perm-1324 @0310243241: 1 steps
lem-box-perm-1324-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-box-perm-1324-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 1 (Bx3-0241 ∷ []) (lem-sym-bc-at0310243241 c4) ▸ done

-- pairs @03103441: 4 steps
lem-pairs-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-pairs-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 0 1 (Toff314 ∷ Bx3-0241 ∷ Toff314 ∷ []) (sym (lem-P-box-at03103441 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03103441 c4) ▸
       at 4 2 [] (wl0788 (lit c4)) ▸
       at 0 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸ done

-- box-perm-1324 @0310243142: 1 steps
lem-box-perm-1324-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-box-perm-1324-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 1 (Bx3-0142 ∷ []) (lem-sym-bc-at0310243142 c4) ▸ done

-- Xb-box @0310243142: 18 steps
lem-Xb-box-at0310243142 : Ws → ⟪ (X4 ∷ Bx3-0412 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Xb-box-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx3-0412 ∷ X4 ∷ []) (CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX01 ∷ CCZ034 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 0 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 2 2 (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) (wl0512 (lit c4)) ▸
       at 1 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 7 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX01 ∷ CCZ034 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ X4 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CCZ012 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CZ03 ∷ []) (sym (wp0797 c4)) ▸
       at 2 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 3 3 (X4 ∷ []) (wp0798 c4) ▸
       at 4 2 (Toff312 ∷ CCZ012 ∷ []) (wl0503 (lit c4)) ▸
       at 3 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸ done

  b2 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wl1243 (lit c4))) ▸ done

-- pairs @0314213240: 4 steps
lem-pairs-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-pairs-at0314213240 c4 = run b0
  where
  b0 : Chain (Bx3-4120 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 1 (Toff302 ∷ Bx3-4120 ∷ Toff302 ∷ []) (sym (lem-P-box-at0314213240 c4)) ▸
       at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4) ▸
       at 4 2 [] (wl0787 (lit c4)) ▸
       at 0 4 (Bx3-2041 ∷ []) (sym (lem-box-tQ-at0312203441 c4)) ▸ done

-- box-perm-1324 @0312203441: 1 steps
lem-box-perm-1324-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-box-perm-1324-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 0 1 (Bx3-2401 ∷ []) (lem-sym-bc-at0312203441 c4) ▸ done

-- Xb-box @0312243041: 18 steps
lem-Xb-box-at0312243041 : Ws → ⟪ (X4 ∷ Bx3-2401 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Xb-box-at0312243041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx3-2401 ∷ X4 ∷ []) (CCZ234 ∷ Toff301 ∷ X4 ∷ CZ23 ∷ CS01 ∷ CX20 ∷ CCZ234 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Toff301 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4) ▸
       at 0 2 (CCZ234 ∷ X4 ∷ CZ23 ∷ []) (sym (wl1274 (lit c4))) ▸
       at 2 2 (Toff301 ∷ CZ23 ∷ CCZ012 ∷ []) (wl1275 (lit c4)) ▸
       at 1 2 (Toff301 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 8 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸ done

  b1 : Chain (CCZ234 ∷ Toff301 ∷ X4 ∷ CZ23 ∷ CS01 ∷ CX20 ∷ CCZ234 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Toff301 ∷ X4 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ X4 ∷ CCZ012 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸
       at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CZ23 ∷ []) (sym (wl1071 (lit c4))) ▸
       at 2 2 (CCZ234 ∷ X4 ∷ CZ23 ∷ []) (sym (wl1274 (lit c4))) ▸
       at 3 3 (X4 ∷ []) (wl1276 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CCZ012 ∷ []) (wl1265 (lit c4)) ▸
       at 3 2 (Toff301 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (X))) ▸ done

  b2 : Chain (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (Bx3-2401 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-2401 ∷ []) (sym (lem-box-cP-at0312243041 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wl1243 (lit c4))) ▸ done

-- box-perm-1324 @0312243041: 1 steps
lem-box-perm-1324-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-box-perm-1324-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 1 (Bx3-2041 ∷ []) (lem-sym-bc-at0312243041 c4) ▸ done

-- pairs @0312203441: 4 steps
lem-pairs-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-pairs-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 1 (Toff314 ∷ Bx3-2041 ∷ Toff314 ∷ []) (sym (lem-P-box-at0312203441 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at0312203441 c4) ▸
       at 4 2 [] (wl0788 (lit c4)) ▸
       at 0 4 (Bx3-4120 ∷ []) (sym (lem-box-tQ-at0314213240 c4)) ▸ done

-- box-perm-1324 @033440: 1 steps
lem-box-perm-1324-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-1324-at033440 c4 = run b0
  where
  b0 : Chain (Bx3-1240 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 1 (Bx3-1420 ∷ []) (lem-sym-bc-at033440 c4) ▸ done

-- Xb-box @03243240: 18 steps
lem-Xb-box-at03243240 : Ws → ⟪ (X4 ∷ Bx3-1420 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Xb-box-at03243240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx3-1420 ∷ X4 ∷ []) (CCZ134 ∷ Toff302 ∷ X4 ∷ CZ13 ∷ CS02 ∷ CX12 ∷ CCZ134 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 0 2 (CCZ134 ∷ X4 ∷ CZ13 ∷ []) (sym (wl1279 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CZ13 ∷ CCZ012 ∷ []) (wl1280 (lit c4)) ▸
       at 1 2 (Toff302 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 8 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 7 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸ done

  b1 : Chain (CCZ134 ∷ Toff302 ∷ X4 ∷ CZ13 ∷ CS02 ∷ CX12 ∷ CCZ134 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ X4 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ X4 ∷ CCZ012 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 4 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CZ13 ∷ []) (sym (wl1281 (lit c4))) ▸
       at 2 2 (CCZ134 ∷ X4 ∷ CZ13 ∷ []) (sym (wl1279 (lit c4))) ▸
       at 3 3 (X4 ∷ []) (wl1282 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CCZ012 ∷ []) (wl1251 (lit c4)) ▸
       at 3 2 (Toff302 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b2 : Chain (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (Bx3-1420 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wl1243 (lit c4))) ▸ done

-- box-perm-1324 @3443: 1 steps
lem-box-perm-1324-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-1324-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-1423 ∷ []) (lem-sym-bc-at3443 c4) ▸ done

-- pairs @03243240: 4 steps
lem-pairs-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-pairs-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-2014 ∷ [])
  b0 = at 0 1 (Toff302 ∷ Bx3-1420 ∷ Toff302 ∷ []) (sym (lem-P-box-at03243240 c4)) ▸
       at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 4 2 [] (wl0787 (lit c4)) ▸
       at 0 4 (Bx3-2014 ∷ []) (sym (lem-box-tQ-at03122031 c4)) ▸ done

-- box-perm-4132 @03102132: 3 steps
lem-box-perm-4132-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-box-perm-4132-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 1 (Bx3-2401 ∷ []) (lem-pairs-at03102132 c4) ▸
       at 0 1 (Bx3-4201 ∷ []) (lem-sym-ab-at0312243041 c4) ▸
       at 0 1 (Bx3-4021 ∷ []) (lem-sym-bc-at03143041 c4) ▸ done

-- box-perm-1324 @02142041: 1 steps
lem-box-perm-1324-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-box-perm-1324-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-4301 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-sym-bc-at02142041 c4) ▸ done

-- box-perm-3124 @02142041: 2 steps
lem-box-perm-3124-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-box-perm-3124-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-3401 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-sym-bc-at02142041 c4) ▸
       at 0 1 (Bx2-3401 ∷ []) (lem-sym-ab-at0214233041 c4) ▸ done

-- box-perm-3124 @0314203241: 2 steps
lem-box-perm-3124-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-box-perm-3124-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 0 1 (Bx3-4201 ∷ []) (lem-sym-bc-at0314203241 c4) ▸
       at 0 1 (Bx3-2401 ∷ []) (lem-sym-ab-at03143041 c4) ▸ done

-- box-perm-2341 @0213243041: 4 steps
lem-box-perm-2341-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-box-perm-2341-at0213243041 c4 = run b0
  where
  b0 : Chain (Bx2-3401 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-sym-ab-at0213243041 c4) ▸
       at 0 1 (Bx2-0143 ∷ []) (lem-pairs-at0214233041 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym-bc-at0210213443 c4) ▸
       at 0 1 (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4) ▸ done

-- box-perm-4123 @0214203143: 4 steps
lem-box-perm-4123-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-box-perm-4123-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-3401 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4) ▸
       at 0 1 (Bx2-0143 ∷ []) (lem-sym-bc-at0210243143 c4) ▸
       at 0 1 (Bx2-4301 ∷ []) (lem-pairs-at0210213443 c4) ▸
       at 0 1 (Bx2-3401 ∷ []) (lem-sym-ab-at0214233041 c4) ▸ done

-- box-perm-2314 @0312243041: 2 steps
lem-box-perm-2314-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-box-perm-2314-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 1 (Bx3-4201 ∷ []) (lem-sym-ab-at0312243041 c4) ▸
       at 0 1 (Bx3-4021 ∷ []) (lem-sym-bc-at03143041 c4) ▸ done

-- pairs @0312243041: 4 steps
lem-pairs-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-pairs-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Toff301 ∷ Bx3-2401 ∷ Toff301 ∷ []) (sym (lem-P-box-at0312243041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4) ▸
       at 4 2 [] (wl0443 (lit c4)) ▸
       at 0 4 (Bx3-0124 ∷ []) (sym (lem-box-tQ-at03102132 c4)) ▸ done

-- pairs @02102441: 4 steps
lem-pairs-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-pairs-at02102441 c4 = run b0
  where
  b0 : Chain (Bx2-0431 ∷ []) (Bx2-3104 ∷ [])
  b0 = at 0 1 (Toff213 ∷ Bx2-0431 ∷ Toff213 ∷ []) (sym (lem-P-box-at02102441 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at02102441 c4) ▸
       at 4 2 [] (wl0180 (lit c4)) ▸
       at 0 4 (Bx2-3104 ∷ []) (sym (lem-box-tQ-at02132130 c4)) ▸ done

-- pairs @03143041: 4 steps
lem-pairs-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-pairs-at03143041 c4 = run b0
  where
  b0 : Chain (Bx3-4201 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 1 (Toff301 ∷ Bx3-4201 ∷ Toff301 ∷ []) (sym (lem-P-box-at03143041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at03143041 c4) ▸
       at 4 2 [] (wl0443 (lit c4)) ▸
       at 0 4 (Bx3-0142 ∷ []) (sym (lem-box-tQ-at0310213442 c4)) ▸ done

-- pairs @02132130: 4 steps
lem-pairs-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-pairs-at02132130 c4 = run b0
  where
  b0 : Chain (Bx2-3104 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 0 1 (Toff204 ∷ Bx2-3104 ∷ Toff204 ∷ []) (sym (lem-P-box-at02132130 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02132130 c4) ▸
       at 4 2 [] (wp0019 c4) ▸
       at 0 4 (Bx2-0431 ∷ []) (sym (lem-box-tQ-at02102441 c4)) ▸ done

-- box-perm-1324 @0314203241: 1 steps
lem-box-perm-1324-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-box-perm-1324-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-4201 ∷ [])
  b0 = at 0 1 (Bx3-4201 ∷ []) (lem-sym-bc-at0314203241 c4) ▸ done

-- box-perm-4123 @0314203142: 4 steps
lem-box-perm-4123-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-box-perm-4123-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 0 1 (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4) ▸
       at 0 1 (Bx3-0142 ∷ []) (lem-sym-bc-at0310243142 c4) ▸
       at 0 1 (Bx3-4201 ∷ []) (lem-pairs-at0310213442 c4) ▸
       at 0 1 (Bx3-2401 ∷ []) (lem-sym-ab-at03143041 c4) ▸ done

-- box-perm-2431 @02142041: 3 steps
lem-box-perm-2431-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-2431-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-sym-bc-at02142041 c4) ▸
       at 0 1 (Bx2-3401 ∷ []) (lem-sym-ab-at0214233041 c4) ▸
       at 0 1 (Bx2-0134 ∷ []) (lem-pairs-at0213243041 c4) ▸ done

-- pairs @0310243241: 4 steps
lem-pairs-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-pairs-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ []) (Bx3-2104 ∷ [])
  b0 = at 0 1 (Toff312 ∷ Bx3-0421 ∷ Toff312 ∷ []) (sym (lem-P-box-at0310243241 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243241 c4) ▸
       at 4 2 [] (wl0489 (lit c4)) ▸
       at 0 4 (Bx3-2104 ∷ []) (sym (lem-box-tQ-at03122130 c4)) ▸ done

-- box-perm-1243 @021021: 3 steps
lem-box-perm-1243-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-box-perm-1243-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 1 (Bx2-3401 ∷ []) (lem-pairs-at021021 c4) ▸
       at 0 1 (Bx2-4301 ∷ []) (lem-sym-ab-at0213243041 c4) ▸
       at 0 1 (Bx2-0143 ∷ []) (lem-pairs-at0214233041 c4) ▸ done

-- box-perm-1243 @0210213443: 3 steps
lem-box-perm-1243-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-1243-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-pairs-at0210213443 c4) ▸
       at 0 1 (Bx2-3401 ∷ []) (lem-sym-ab-at0214233041 c4) ▸
       at 0 1 (Bx2-0134 ∷ []) (lem-pairs-at0213243041 c4) ▸ done

-- pairs @03122130: 4 steps
lem-pairs-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-pairs-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 0 1 (Toff304 ∷ Bx3-2104 ∷ Toff304 ∷ []) (sym (lem-P-box-at03122130 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at03122130 c4) ▸
       at 4 2 [] (wp0351 c4) ▸
       at 0 4 (Bx3-0421 ∷ []) (sym (lem-box-tQ-at0310243241 c4)) ▸ done

-- box-perm-4132 @021021: 3 steps
lem-box-perm-4132-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-box-perm-4132-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-4031 ∷ [])
  b0 = at 0 1 (Bx2-3401 ∷ []) (lem-pairs-at021021 c4) ▸
       at 0 1 (Bx2-4301 ∷ []) (lem-sym-ab-at0213243041 c4) ▸
       at 0 1 (Bx2-4031 ∷ []) (lem-sym-bc-at0214233041 c4) ▸ done

-- box2 @02142041: 11 steps
lem-box2-at02142041 : Ws → ⟪ (Bx2-4031 ∷ Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at02142041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4031 ∷ Bx2-4031 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  b0 = at 0 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at02142041 c4) ▸
       at 4 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0019 c4)) ▸
       at 5 5 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) (lem-t-cP-at02142041 c4) ▸
       at 5 4 (Bx2-4031 ∷ []) (sym (lem-box-cP-at02142041 c4)) ▸
       at 5 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4) ▸
       at 4 2 [] (wp0019 c4) ▸
       at 3 2 [] (wl0181 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) []
  b1 = at 2 2 [] (wp0019 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸
       at 0 2 [] (wp0019 c4) ▸ done

-- box2 @0314203241: 11 steps
lem-box2-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0314203241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4021 ∷ Bx3-4021 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  b0 = at 0 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4) ▸
       at 4 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203241 c4) ▸
       at 4 0 (Toff304 ∷ Toff304 ∷ []) (sym (wp0351 c4)) ▸
       at 5 5 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ []) (lem-t-cP-at0314203241 c4) ▸
       at 5 4 (Bx3-4021 ∷ []) (sym (lem-box-cP-at0314203241 c4)) ▸
       at 5 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4) ▸
       at 4 2 [] (wp0351 c4) ▸
       at 3 2 [] (wl0181 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) []
  b1 = at 2 2 [] (wp0351 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸
       at 0 2 [] (wp0351 c4) ▸ done

-- box-perm-2314 @02132130: 2 steps
lem-box-perm-2314-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-box-perm-2314-at02132130 c4 = run b0
  where
  b0 : Chain (Bx2-3104 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 1 (Bx2-1304 ∷ []) (lem-sym-ab-at02132130 c4) ▸
       at 0 1 (Bx2-1034 ∷ []) (lem-sym-bc-at022330 c4) ▸ done

-- box-perm-2314 @03122130: 2 steps
lem-box-perm-2314-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-2314-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Bx3-1204 ∷ []) (lem-sym-ab-at03122130 c4) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-sym-bc-at0330 c4) ▸ done

-- box-perm-3214 @03122031: 3 steps
lem-box-perm-3214-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-3214-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Bx3-0214 ∷ []) (lem-sym-ab-at03122031 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-bc-at031031 c4) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸ done

-- pairs @031031: 4 steps
lem-pairs-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-pairs-at031031 c4 = run b0
  where
  b0 : Chain (Bx3-0214 ∷ []) (Bx3-1402 ∷ [])
  b0 = at 0 1 (Toff314 ∷ Bx3-0214 ∷ Toff314 ∷ []) (sym (lem-P-box-at031031 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 4 2 [] (wl0788 (lit c4)) ▸
       at 0 4 (Bx3-1402 ∷ []) (sym (lem-box-tQ-at03243042 c4)) ▸ done

-- box-perm-1324 @142142: 1 steps
lem-box-perm-1324-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-box-perm-1324-at142142 c4 = run b0
  where
  b0 : Chain (Bx0-4132 ∷ []) (Bx0-4312 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ []) (lem-sym-bc-at142142 c4) ▸ done

-- box-perm-3124 @142142: 2 steps
lem-box-perm-3124-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-box-perm-3124-at142142 c4 = run b0
  where
  b0 : Chain (Bx0-4132 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ []) (lem-sym-bc-at142142 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym-ab-at14233142 c4) ▸ done

-- box-perm-2341 @13243142: 4 steps
lem-box-perm-2341-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-box-perm-2341-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-pairs-at14233142 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym-bc-at3443 c4) ▸
       at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸ done

-- pairs @03243042: 4 steps
lem-pairs-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-pairs-at03243042 c4 = run b0
  where
  b0 : Chain (Bx3-1402 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 0 1 (Toff302 ∷ Bx3-1402 ∷ Toff302 ∷ []) (sym (lem-P-box-at03243042 c4)) ▸
       at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243042 c4) ▸
       at 4 2 [] (wl0787 (lit c4)) ▸
       at 0 4 (Bx3-0214 ∷ []) (sym (lem-box-tQ-at031031 c4)) ▸ done

-- pairs @2442: 4 steps
lem-pairs-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-pairs-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 0 1 (Toff023 ∷ Bx0-1432 ∷ Toff023 ∷ []) (sym (lem-P-box-at2442 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at2442 c4) ▸
       at 4 2 [] (wl0203 (lit c4)) ▸
       at 0 4 (Bx0-3214 ∷ []) (sym (lem-box-tQ-at1331 c4)) ▸ done

-- box-perm-2314 @02132031: 2 steps
lem-box-perm-2314-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-2314-at02132031 c4 = run b0
  where
  b0 : Chain (Bx2-3014 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Bx2-0314 ∷ []) (lem-sym-ab-at02132031 c4) ▸
       at 0 1 (Bx2-0134 ∷ []) (lem-sym-bc-at02102331 c4) ▸ done

-- box2 @142142: 11 steps
lem-box2-at142142 : Ws → ⟪ (Bx0-4132 ∷ Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at142142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4132 ∷ Bx0-4132 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at142142 c4) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 4 0 (Toff014 ∷ Toff014 ∷ []) (sym (wp0051 c4)) ▸
       at 5 5 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ []) (lem-t-cP-at142142 c4) ▸
       at 5 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸
       at 5 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at142142 c4) ▸
       at 4 2 [] (wp0051 c4) ▸
       at 3 2 [] (wl0204 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) []
  b1 = at 2 2 [] (wp0051 c4) ▸
       at 1 2 [] (wl0204 (lit c4)) ▸
       at 0 2 [] (wp0051 c4) ▸ done

-- box-perm-2431 @142142: 3 steps
lem-box-perm-2431-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-2431-at142142 c4 = run b0
  where
  b0 : Chain (Bx0-4132 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ []) (lem-sym-bc-at142142 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym-ab-at14233142 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-pairs-at13243142 c4) ▸ done

-- box2 @033440: 11 steps
lem-box2-at033440 : Ws → ⟪ (Bx3-1240 ∷ Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at033440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1240 ∷ Bx3-1240 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 0 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4) ▸
       at 4 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4) ▸
       at 4 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 5 5 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff312 ∷ []) (lem-t-cP-at033440 c4) ▸
       at 5 4 (Bx3-1240 ∷ []) (sym (lem-box-cP-at033440 c4)) ▸
       at 5 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4) ▸
       at 4 2 [] (wl0489 (lit c4)) ▸
       at 3 2 [] (wp0007 c4) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) []
  b1 = at 2 2 [] (wl0489 (lit c4)) ▸
       at 1 2 [] (wp0007 c4) ▸
       at 0 2 [] (wl0489 (lit c4)) ▸ done
