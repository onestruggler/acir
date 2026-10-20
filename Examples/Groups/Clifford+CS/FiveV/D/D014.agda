{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D014 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-nat-SWbc-at0213243140 ; lem-nat-SWbc-at03102132 ; lem-nat-SWbc-at032032 ; lem-nat-SWbc-at04203243 ; lem-nat-SWbc-at13243142 ; lem-nat-SWbc-at13243241 ; lem-nat-SWbc-at14233142 ; lem-tP-at021021 ; lem-tP-at0210213443 ; lem-tP-at0213243140 ; lem-tP-at0220 ; lem-tP-at03102132 ; lem-tP-at032032 ; lem-tP-at0410213243 ; lem-tP-at04203243 ; lem-tP-at13243142 ; lem-tP-at13243241 ; lem-tP-at14233142 ; lem-tP-at14233241)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-nat-SWbc-at0310213442 ; lem-nat-SWbc-at14233241)
open import Examples.Groups.Clifford+CS.FiveV.D.D007 using (lem-nat-SWbc-at0220)
open import Examples.Groups.Clifford+CS.FiveV.D.D009 using (lem-CSdu-box-1 ; lem-CSdu-box-2 ; lem-CSdu-box-2-at0210243143 ; lem-CSdu-box-2-at122441 ; lem-CSdu-box-2-at243243 ; lem-CSu-box-1 ; lem-CSu-box-2 ; lem-CSu-box-2-at122441 ; lem-CSu-box-2-at243243 ; lem-CXbc-box ; lem-CXbc-box-at0214203143 ; lem-CXbc-box-at0330 ; lem-CXbc-box-at043043 ; lem-CXbc-box-at1221 ; lem-CXbc-box-at12243143 ; lem-CXbc-box-at13213442 ; lem-CXbc-box-at133441 ; lem-CXcb-box ; lem-CXcb-box-at0214203143 ; lem-CXcb-box-at0330 ; lem-CXcb-box-at043043 ; lem-CXcb-box-at1221 ; lem-CXcb-box-at12243143 ; lem-CXcb-box-at13213442 ; lem-CXcb-box-at133441 ; lem-QVQ-at021021 ; lem-QVQ-at03102132 ; lem-QVQ-at0410213243 ; lem-QVQ-at04203243 ; lem-QVQ-at13243142 ; lem-QVQ-at13243241 ; lem-QVQ-at14233142 ; lem-SWbc-box-at032032 ; lem-SWbc-box-at04203243 ; lem-SWbc-box-at13243142 ; lem-SWbc-box-at13243241 ; lem-SWbc-box-at14233142 ; lem-Sdu-box ; lem-Su-box ; lem-Su-box-at0210243143 ; lem-Su-box-at122441 ; lem-Su-box-at243243 ; lem-VPQ ; lem-VPQ-at0110 ; lem-VPQ-at0210243143 ; lem-VPQ-at0310243142 ; lem-VPQ-at0314203142 ; lem-VPQ-at0330 ; lem-VPQ-at043043 ; lem-VPQ-at1221 ; lem-VPQ-at122331 ; lem-VPQ-at122441 ; lem-VPQ-at132132 ; lem-VPQ-at13213442 ; lem-VPQ-at1331 ; lem-VPQ-at2332 ; lem-VPQ-at243243 ; lem-VPQ-at3443)
open import Examples.Groups.Clifford+CS.FiveV.D.D010 using (lem-CSu-box-2-at0210243143 ; lem-CXbc-box-at0210243143 ; lem-CXbc-box-at0213213440 ; lem-CXbc-box-at0214213043 ; lem-CXbc-box-at022330 ; lem-CXbc-box-at02233440 ; lem-CXbc-box-at022440 ; lem-CXbc-box-at0312213440 ; lem-CXbc-box-at0312243140 ; lem-CXbc-box-at0314203142 ; lem-CXbc-box-at0314213042 ; lem-CXbc-box-at122331 ; lem-CXbc-box-at12233441 ; lem-CXbc-box-at122441 ; lem-CXbc-box-at132132 ; lem-CXbc-box-at1331 ; lem-CXbc-box-at14213243 ; lem-CXbc-box-at1441 ; lem-CXbc-box-at2332 ; lem-CXbc-box-at243243 ; lem-CXcb-box-at0210243143 ; lem-CXcb-box-at0213213440 ; lem-CXcb-box-at0214213043 ; lem-CXcb-box-at022330 ; lem-CXcb-box-at02233440 ; lem-CXcb-box-at0312213440 ; lem-CXcb-box-at0312243140 ; lem-CXcb-box-at0314203142 ; lem-CXcb-box-at0314213042 ; lem-CXcb-box-at122331 ; lem-CXcb-box-at12233441 ; lem-CXcb-box-at122441 ; lem-CXcb-box-at132132 ; lem-CXcb-box-at1331 ; lem-CXcb-box-at14213243 ; lem-CXcb-box-at1441 ; lem-CXcb-box-at2332 ; lem-CXcb-box-at243243 ; lem-QVQ-at0210213443 ; lem-QVQ-at0213243140 ; lem-QVQ-at0220 ; lem-QVQ-at032032 ; lem-QVQ-at14233241 ; lem-SWbc-box-at0213243140 ; lem-SWbc-box-at0220 ; lem-SWbc-box-at03102132 ; lem-VPQ-at0210233441 ; lem-VPQ-at0213203441 ; lem-VPQ-at0214203143 ; lem-VPQ-at0214213043 ; lem-VPQ-at022330 ; lem-VPQ-at022440 ; lem-VPQ-at0312243140 ; lem-VPQ-at0314213042 ; lem-VPQ-at12213443 ; lem-VPQ-at12233441 ; lem-VPQ-at14213243 ; lem-VPQ-at143143 ; lem-VPQ-at233442)
open import Examples.Groups.Clifford+CS.FiveV.D.D011 using (lem-CXbc-box-at0210233441 ; lem-CXbc-box-at02102441 ; lem-CXbc-box-at02142041 ; lem-CXbc-box-at0310243142 ; lem-CXbc-box-at0310243241 ; lem-CXbc-box-at031031 ; lem-CXbc-box-at03103441 ; lem-CXbc-box-at0312203441 ; lem-CXbc-box-at0312243041 ; lem-CXbc-box-at0314213240 ; lem-CXbc-box-at03143041 ; lem-CXbc-box-at03143140 ; lem-CXbc-box-at03243240 ; lem-CXbc-box-at033440 ; lem-CXbc-box-at12213443 ; lem-CXbc-box-at143143 ; lem-CXbc-box-at233442 ; lem-CXbc-box-at2442 ; lem-CXbc-box-at3443 ; lem-CXcb-box-at0210233441 ; lem-CXcb-box-at02102441 ; lem-CXcb-box-at022440 ; lem-CXcb-box-at0310243142 ; lem-CXcb-box-at0310243241 ; lem-CXcb-box-at031031 ; lem-CXcb-box-at03103441 ; lem-CXcb-box-at0312203441 ; lem-CXcb-box-at0312243041 ; lem-CXcb-box-at0314213240 ; lem-CXcb-box-at03143041 ; lem-CXcb-box-at03143140 ; lem-CXcb-box-at03243240 ; lem-CXcb-box-at033440 ; lem-CXcb-box-at12213443 ; lem-CXcb-box-at143143 ; lem-CXcb-box-at233442 ; lem-CXcb-box-at2442 ; lem-CXcb-box-at3443 ; lem-SWbc-box-at0310213442 ; lem-SWbc-box-at14233241 ; lem-VPQ-at02102441 ; lem-VPQ-at02233440 ; lem-VPQ-at0310243241 ; lem-VPQ-at031031 ; lem-VPQ-at03103441 ; lem-VPQ-at0312203441 ; lem-VPQ-at0312243041 ; lem-VPQ-at0314213240 ; lem-VPQ-at03143140 ; lem-VPQ-at03243240 ; lem-VPQ-at033440 ; lem-VPQ-at12243143 ; lem-VPQ-at1441 ; lem-VPQ-at2442)
open import Examples.Groups.Clifford+CS.FiveV.D.D012 using (lem-CXcb-box-at02142041)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Toff034 ∷ Toff034 ∷ []) [] (wp 6 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (lem-VPQ c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ034 ∷ CCZ034 ∷ []) [] (wp 7 c4)

-- QVQ: 3 steps
lem-QVQ : Ws → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ c4 = derive (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q4 : Ws → Eqn
  q4 c4 = eqn (Toff213 ∷ Toff213 ∷ []) [] (wl 180 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (lem-VPQ-at0210243143 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl 181 (lit c4))

-- QVQ @0210243143: 3 steps
lem-QVQ-at0210243143 : Ws → ⟪ (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-QVQ-at0210243143 c4 = derive (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ [])
  (rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw 4 (q6 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (Toff023 ∷ Toff023 ∷ []) [] (wl 203 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (lem-VPQ-at243243 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ023 ∷ CCZ023 ∷ []) [] (wl 204 (lit c4))

-- QVQ @243243: 3 steps
lem-QVQ-at243243 : Ws → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at243243 c4 = derive (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q8 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = eqn (Toff013 ∷ Toff013 ∷ []) [] (wl 229 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (lem-VPQ-at122441 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl 230 (lit c4))

-- QVQ @122441: 3 steps
lem-QVQ-at122441 : Ws → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at122441 c4 = derive (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = eqn (CX23 ∷ CX32 ∷ CX23 ∷ []) (Sw23 ∷ []) (wl 258 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CXbc-box c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ124 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl 259 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CX32 ∷ Bx0-1234 ∷ CX32 ∷ []) (Bx0-1234 ∷ CCZ134 ∷ []) (lem-CXcb-box c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ124 ∷ CX23 ∷ []) (CX23 ∷ CCZ124 ∷ []) (wl 260 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ134 ∷ CX23 ∷ []) (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl 261 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) (wl 262 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl 263 (lit c4))

-- SWbc-box: 11 steps
lem-SWbc-box : Ws → ⟪ (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-SWbc-box c4 = derive (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (Bx0-1234 ∷ [])
  (rw⁻ 0 (q13 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 2 (q14 c4) ∷
   rw 3 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 4 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw 2 (q18 c4) ∷
   rw 3 (q19 c4) ∷
   rw 0 (q14 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = eqn (CX13 ∷ CX31 ∷ CX13 ∷ []) (Sw13 ∷ []) (wl 278 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1221 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ124 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl 279 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CX31 ∷ Bx0-2134 ∷ CX31 ∷ []) (Bx0-2134 ∷ CCZ234 ∷ []) (lem-CXcb-box-at1221 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ124 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ []) (wl 280 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ234 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl 281 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) (wl 282 (lit c4))

-- SWbc-box @1221: 11 steps
lem-SWbc-box-at1221 : Ws → ⟪ (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-SWbc-box-at1221 c4 = derive (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) (Bx0-2134 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw 3 (q23 c4) ∷
   rw 1 (q24 c4) ∷
   rw 4 (q25 c4) ∷
   rw 3 (q26 c4) ∷
   rw 2 (q26 c4) ∷
   rw 3 (q27 c4) ∷
   rw 0 (q22 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q28 : Ws → Eqn
  q28 c4 = eqn (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (lem-VPQ-at1221 c4)

-- QVQ @1221: 3 steps
lem-QVQ-at1221 : Ws → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ-at1221 c4 = derive (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q28 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = eqn (Toff024 ∷ Toff024 ∷ []) [] (wp 80 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (lem-VPQ-at2332 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp 135 c4)

-- QVQ @2332: 3 steps
lem-QVQ-at2332 : Ws → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at2332 c4 = derive (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  (rw⁻ 0 (q29 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw 4 (q31 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) (Bx0-3412 ∷ []) (lem-SWbc-box-at13243142 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) (Bx0-3142 ∷ []) (lem-nat-SWbc-at13243142 c4)

-- sym-bc @13243142: 2 steps
lem-sym-bc-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym-bc-at13243142 c4 = derive (Bx0-3412 ∷ []) (Bx0-3142 ∷ [])
  (rw⁻ 0 (q32 c4) ∷
   rw 0 (q33 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = eqn (Toff014 ∷ Toff014 ∷ []) [] (wp 51 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (lem-VPQ-at122331 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)

-- QVQ @122331: 3 steps
lem-QVQ-at122331 : Ws → ⟪ (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-QVQ-at122331 c4 = derive (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ [])
  (rw⁻ 0 (q34 c4) ∷
   rw⁻ 1 (q35 c4) ∷
   rw 4 (q36 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) (Bx0-3421 ∷ []) (lem-SWbc-box-at13243241 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) (Bx0-3241 ∷ []) (lem-nat-SWbc-at13243241 c4)

-- sym-bc @13243241: 2 steps
lem-sym-bc-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-sym-bc-at13243241 c4 = derive (Bx0-3421 ∷ []) (Bx0-3241 ∷ [])
  (rw⁻ 0 (q37 c4) ∷
   rw 0 (q38 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (lem-VPQ-at132132 c4)

-- QVQ @132132: 3 steps
lem-QVQ-at132132 : Ws → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at132132 c4 = derive (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  (rw⁻ 0 (q29 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw 4 (q31 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = eqn (CX41 ∷ CX14 ∷ CX41 ∷ []) (Sw14 ∷ []) (wl 300 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CX41 ∷ Bx0-2413 ∷ CX41 ∷ []) (Bx0-2413 ∷ CCZ234 ∷ []) (lem-CXbc-box-at12243143 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ234 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl 301 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CX14 ∷ Bx0-2413 ∷ CX14 ∷ []) (Bx0-2413 ∷ CCZ123 ∷ []) (lem-CXcb-box-at12243143 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ234 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ []) (wl 302 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ123 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl 303 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ []) (wl 304 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl 305 (lit c4))

-- SWbc-box @12243143: 11 steps
lem-SWbc-box-at12243143 : Ws → ⟪ (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-SWbc-box-at12243143 c4 = derive (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) (Bx0-2413 ∷ [])
  (rw⁻ 0 (q40 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 2 (q41 c4) ∷
   rw 3 (q42 c4) ∷
   rw 1 (q43 c4) ∷
   rw 4 (q44 c4) ∷
   rw 3 (q45 c4) ∷
   rw 2 (q45 c4) ∷
   rw 3 (q46 c4) ∷
   rw 0 (q41 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = eqn (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) (Bx0-4312 ∷ []) (lem-SWbc-box-at14233142 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) (Bx0-4132 ∷ []) (lem-nat-SWbc-at14233142 c4)

-- sym-bc @14233142: 2 steps
lem-sym-bc-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-sym-bc-at14233142 c4 = derive (Bx0-4312 ∷ []) (Bx0-4132 ∷ [])
  (rw⁻ 0 (q48 c4) ∷
   rw 0 (q49 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ012 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (wp 136 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at14233142 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ []) (lem-tP-at14233142 c4)

-- box-cP @14233142: 12 steps
lem-box-cP-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at14233142 c4 = derive (Bx0-4312 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw⁻ 2 (q50 c4) ∷
   re 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw⁻ 5 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = eqn (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (lem-VPQ-at13213442 c4)

-- QVQ @13213442: 3 steps
lem-QVQ-at13213442 : Ws → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at13213442 c4 = derive (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  (rw⁻ 0 (q29 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw 4 (q31 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = eqn (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (lem-VPQ-at1331 c4)

-- QVQ @1331: 3 steps
lem-QVQ-at1331 : Ws → ⟪ (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-QVQ-at1331 c4 = derive (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ [])
  (rw⁻ 0 (q34 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw 4 (q36 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = eqn (S0 ∷ CS01⁻ ∷ []) (X1 ∷ CS01 ∷ X1 ∷ []) (wl 364 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CS01⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (S0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4)

-- XCSX-box-1: 4 steps
lem-XCSX-box-1 : Ws → ⟪ (X1 ∷ CS01 ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-XCSX-box-1 c4 = derive (X1 ∷ CS01 ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw 0 (q57 c4) ∷
   rw 1 (q55 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = eqn (S0⁻ ∷ CS01 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ []) (wl 365 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CS01 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (S0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4)

-- XCSdX-box-1: 4 steps
lem-XCSdX-box-1 : Ws → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-XCSdX-box-1 c4 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw⁻ 0 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 1 (q58 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = eqn (S0 ∷ CS02⁻ ∷ []) (X2 ∷ CS02 ∷ X2 ∷ []) (wl 377 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (CS02⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4)

-- XCSX-box-2: 4 steps
lem-XCSX-box-2 : Ws → ⟪ (X2 ∷ CS02 ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-XCSX-box-2 c4 = derive (X2 ∷ CS02 ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  (rw⁻ 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 0 (q57 c4) ∷
   rw 1 (q61 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (S0⁻ ∷ CS02 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ []) (wl 378 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4)

-- XCSdX-box-2: 4 steps
lem-XCSdX-box-2 : Ws → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-XCSdX-box-2 c4 = derive (X2 ∷ CS02⁻ ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw⁻ 0 (q63 c4) ∷
   rw 1 (q64 c4) ∷
   rw 0 (q60 c4) ∷
   rw 1 (q63 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (Toff134 ∷ Toff134 ∷ []) [] (wl 402 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (Toff102 ∷ CCZ012 ∷ Toff134 ∷ CCZ134 ∷ []) (Toff134 ∷ CCZ134 ∷ Toff102 ∷ CCZ012 ∷ []) (lem-VPQ-at0110 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl 321 (lit c4))

-- QVQ @0110: 3 steps
lem-QVQ-at0110 : Ws → ⟪ (CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Toff102 ∷ CCZ012 ∷ Toff134 ∷ []) ⟫ʷ
lem-QVQ-at0110 c4 = derive (CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ134 ∷ []) (Toff134 ∷ Toff102 ∷ CCZ012 ∷ Toff134 ∷ [])
  (rw⁻ 0 (q65 c4) ∷
   rw⁻ 1 (q66 c4) ∷
   rw 4 (q67 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (CX24 ∷ CX42 ∷ CX24 ∷ []) (Sw24 ∷ []) (wl 405 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (CX24 ∷ Bx0-3241 ∷ CX24 ∷ []) (Bx0-3241 ∷ CCZ123 ∷ []) (lem-CXbc-box-at133441 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (CCZ123 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl 319 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CX42 ∷ Bx0-3241 ∷ CX42 ∷ []) (Bx0-3241 ∷ CCZ134 ∷ []) (lem-CXcb-box-at133441 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (CCZ123 ∷ CX24 ∷ []) (CX24 ∷ CCZ123 ∷ []) (wl 406 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ134 ∷ CX24 ∷ []) (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl 317 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) (wl 407 (lit c4))

-- SWbc-box @133441: 11 steps
lem-SWbc-box-at133441 : Ws → ⟪ (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-SWbc-box-at133441 c4 = derive (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) (Bx0-3241 ∷ [])
  (rw⁻ 0 (q68 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 2 (q69 c4) ∷
   rw 3 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   rw 4 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw 2 (q73 c4) ∷
   rw 3 (q74 c4) ∷
   rw 0 (q69 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ012 ∷ []) (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (wl 288 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at13243241 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ []) (lem-tP-at13243241 c4)

-- box-cP @13243241: 12 steps
lem-box-cP-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at13243241 c4 = derive (Bx0-3421 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q75 c4) ∷
   re 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw⁻ 5 (q75 c4) ∷
   rw 2 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = eqn (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ []) (wp 280 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-QVQ-at021021 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ []) (lem-tP-at021021 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (Toff201 ∷ Toff201 ∷ []) [] (wl 421 (lit c4))

-- box-cP @021021: 12 steps
lem-box-cP-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-box-cP-at021021 c4 = derive (Bx2-0134 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw 2 (q78 c4) ∷
   re 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw 5 (q78 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q81 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = eqn (CX14 ∷ CX41 ∷ CX14 ∷ []) (Sw14 ∷ []) (wl 423 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (CX14 ∷ Bx0-3142 ∷ CX14 ∷ []) (Bx0-3142 ∷ CCZ123 ∷ []) (lem-CXbc-box-at13213442 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (CX41 ∷ Bx0-3142 ∷ CX41 ∷ []) (Bx0-3142 ∷ CCZ234 ∷ []) (lem-CXcb-box-at13213442 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ123 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ []) (wl 424 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) (wl 425 (lit c4))

-- SWbc-box @13213442: 11 steps
lem-SWbc-box-at13213442 : Ws → ⟪ (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-SWbc-box-at13213442 c4 = derive (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) (Bx0-3142 ∷ [])
  (rw⁻ 0 (q82 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 3 (q45 c4) ∷
   rw 1 (q84 c4) ∷
   rw 4 (q85 c4) ∷
   rw 3 (q42 c4) ∷
   rw 2 (q42 c4) ∷
   rw 3 (q86 c4) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = eqn (CCZ012 ∷ []) (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (wl 269 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at13243142 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ []) (lem-tP-at13243142 c4)

-- box-cP @13243142: 12 steps
lem-box-cP-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at13243142 c4 = derive (Bx0-3412 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw⁻ 2 (q87 c4) ∷
   re 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw⁻ 5 (q87 c4) ∷
   rw 2 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = eqn (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-QVQ-at03102132 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ []) (lem-tP-at03102132 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (Toff301 ∷ Toff301 ∷ []) [] (wl 443 (lit c4))

-- box-cP @03102132: 12 steps
lem-box-cP-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-box-cP-at03102132 c4 = derive (Bx3-0124 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw 2 (q78 c4) ∷
   re 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw 5 (q78 c4) ∷
   rw 2 (q90 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q92 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = eqn (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (lem-VPQ-at3443 c4)

-- QVQ @3443: 3 steps
lem-QVQ-at3443 : Ws → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ-at3443 c4 = derive (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q93 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = eqn (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ []) (wp 305 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-QVQ-at0410213243 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (Toff401 ∷ Toff423 ∷ []) (Toff423 ∷ Toff401 ∷ []) (lem-tP-at0410213243 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (Toff401 ∷ Toff401 ∷ []) [] (wp 306 c4)

-- box-cP @0410213243: 12 steps
lem-box-cP-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-box-cP-at0410213243 c4 = derive (Bx4-0123 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw 2 (q94 c4) ∷
   re 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw 5 (q94 c4) ∷
   rw 2 (q95 c4) ∷
   rw 1 (q96 c4) ∷
   rw 2 (q97 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = eqn (Toff403 ∷ Toff403 ∷ []) [] (wp 317 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (lem-VPQ-at043043 c4)

-- QVQ @043043: 3 steps
lem-QVQ-at043043 : Ws → ⟪ (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-QVQ-at043043 c4 = derive (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ [])
  (rw⁻ 0 (q98 c4) ∷
   rw⁻ 1 (q99 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (CX20 ∷ CX02 ∷ CX20 ∷ []) (Sw02 ∷ []) (wl 480 (lit c4))
  q101 : Ws → Eqn
  q101 c4 = eqn (CX20 ∷ Bx4-1203 ∷ CX20 ∷ []) (Bx4-1203 ∷ CCZ123 ∷ []) (lem-CXbc-box-at043043 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (CCZ123 ∷ CX02 ∷ []) (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl 481 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (CX02 ∷ Bx4-1203 ∷ CX02 ∷ []) (Bx4-1203 ∷ CCZ013 ∷ []) (lem-CXcb-box-at043043 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (CCZ123 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ []) (wl 482 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (CCZ013 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl 483 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) (wl 484 (lit c4))

-- SWbc-box @043043: 11 steps
lem-SWbc-box-at043043 : Ws → ⟪ (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-SWbc-box-at043043 c4 = derive (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) (Bx4-1203 ∷ [])
  (rw⁻ 0 (q100 c4) ∷
   rw⁻ 4 (q100 c4) ∷
   rw 2 (q101 c4) ∷
   rw 3 (q102 c4) ∷
   rw 1 (q103 c4) ∷
   rw 4 (q104 c4) ∷
   rw 3 (q105 c4) ∷
   rw 2 (q105 c4) ∷
   rw 3 (q106 c4) ∷
   rw 0 (q101 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (CCZ234 ∷ []) (wl 486 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-QVQ-at04203243 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (Toff401 ∷ Toff423 ∷ []) (Toff423 ∷ Toff401 ∷ []) (lem-tP-at04203243 c4)

-- box-cP @04203243: 12 steps
lem-box-cP-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-box-cP-at04203243 c4 = derive (Bx4-1023 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw 2 (q107 c4) ∷
   re 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw 5 (q107 c4) ∷
   rw 2 (q108 c4) ∷
   rw 1 (q109 c4) ∷
   rw 2 (q97 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = eqn (Toff304 ∷ Toff304 ∷ []) [] (wp 351 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (lem-VPQ-at0330 c4)

-- QVQ @0330: 3 steps
lem-QVQ-at0330 : Ws → ⟪ (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-QVQ-at0330 c4 = derive (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ [])
  (rw⁻ 0 (q110 c4) ∷
   rw⁻ 1 (q111 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (Toff312 ∷ Toff312 ∷ []) [] (wl 489 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (lem-VPQ-at0314203142 c4)

-- QVQ @0314203142: 3 steps
lem-QVQ-at0314203142 : Ws → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0314203142 c4 = derive (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw⁻ 1 (q113 c4) ∷
   rw 4 (q6 c4) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = eqn (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (lem-VPQ-at0310243142 c4)

-- QVQ @0310243142: 3 steps
lem-QVQ-at0310243142 : Ws → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0310243142 c4 = derive (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw⁻ 1 (q114 c4) ∷
   rw 4 (q6 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = eqn (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) (Bx4-1023 ∷ []) (lem-SWbc-box-at04203243 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) (Bx4-1203 ∷ []) (lem-nat-SWbc-at04203243 c4)

-- sym-bc @04203243: 2 steps
lem-sym-bc-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-sym-bc-at04203243 c4 = derive (Bx4-1023 ∷ []) (Bx4-1203 ∷ [])
  (rw⁻ 0 (q115 c4) ∷
   rw 0 (q116 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) (Bx3-1024 ∷ []) (lem-SWbc-box-at032032 c4)
  q118 : Ws → Eqn
  q118 c4 = eqn (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) (Bx3-1204 ∷ []) (lem-nat-SWbc-at032032 c4)

-- sym-bc @032032: 2 steps
lem-sym-bc-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-sym-bc-at032032 c4 = derive (Bx3-1024 ∷ []) (Bx3-1204 ∷ [])
  (rw⁻ 0 (q117 c4) ∷
   rw 0 (q118 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = eqn (CX20 ∷ Bx3-1204 ∷ CX20 ∷ []) (Bx3-1204 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0330 c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (CCZ124 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp 382 c4)
  q121 : Ws → Eqn
  q121 c4 = eqn (CX02 ∷ Bx3-1204 ∷ CX02 ∷ []) (Bx3-1204 ∷ CCZ014 ∷ []) (lem-CXcb-box-at0330 c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (CCZ124 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ []) (wp 389 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (CCZ014 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp 381 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) (wp 390 c4)

-- SWbc-box @0330: 11 steps
lem-SWbc-box-at0330 : Ws → ⟪ (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-SWbc-box-at0330 c4 = derive (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) (Bx3-1204 ∷ [])
  (rw⁻ 0 (q100 c4) ∷
   rw⁻ 4 (q100 c4) ∷
   rw 2 (q119 c4) ∷
   rw 3 (q120 c4) ∷
   rw 1 (q121 c4) ∷
   rw 4 (q122 c4) ∷
   rw 3 (q123 c4) ∷
   rw 2 (q123 c4) ∷
   rw 3 (q124 c4) ∷
   rw 0 (q119 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = eqn (S0 ∷ CS04⁻ ∷ []) (X4 ∷ CS04 ∷ X4 ∷ []) (wp 257 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (CS04⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (S0 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ S0 ∷ []) (lem-Su-box-at243243 c4)

-- XCSX-box-2 @243243: 4 steps
lem-XCSX-box-2-at243243 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-2-at243243 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q125 c4) ∷
   rw 1 (q126 c4) ∷
   rw 0 (q127 c4) ∷
   rw 1 (q125 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (CS04⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4)
  q129 : Ws → Eqn
  q129 c4 = eqn (S0 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ S0 ∷ []) (lem-Su-box-at122441 c4)

-- XCSX-box-2 @122441: 4 steps
lem-XCSX-box-2-at122441 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-2-at122441 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q125 c4) ∷
   rw 1 (q128 c4) ∷
   rw 0 (q129 c4) ∷
   rw 1 (q125 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = eqn (S2 ∷ CS24⁻ ∷ []) (X4 ∷ CS24 ∷ X4 ∷ []) (wl 583 (lit c4))
  q131 : Ws → Eqn
  q131 c4 = eqn (CS24⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (S2 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ S2 ∷ []) (lem-Su-box-at0210243143 c4)

-- XCSX-box-2 @0210243143: 4 steps
lem-XCSX-box-2-at0210243143 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-2-at0210243143 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q130 c4) ∷
   rw 1 (q131 c4) ∷
   rw 0 (q132 c4) ∷
   rw 1 (q130 c4) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = eqn (CX01 ∷ CX10 ∷ CX01 ∷ []) (Sw01 ∷ []) (wl 619 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (CX01 ∷ Bx2-4013 ∷ CX01 ∷ []) (Bx2-4013 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0214203143 c4)
  q135 : Ws → Eqn
  q135 c4 = eqn (CCZ034 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp 506 c4)
  q136 : Ws → Eqn
  q136 c4 = eqn (CX10 ∷ Bx2-4013 ∷ CX10 ∷ []) (Bx2-4013 ∷ CCZ134 ∷ []) (lem-CXcb-box-at0214203143 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (CCZ034 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ []) (wp 221 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (CCZ134 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp 507 c4)
  q139 : Ws → Eqn
  q139 c4 = eqn (CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (CCZ034 ∷ []) (wp 508 c4)

-- SWbc-box @0214203143: 11 steps
lem-SWbc-box-at0214203143 : Ws → ⟪ (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-SWbc-box-at0214203143 c4 = derive (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) (Bx2-4013 ∷ [])
  (rw⁻ 0 (q133 c4) ∷
   rw⁻ 4 (q133 c4) ∷
   rw 2 (q134 c4) ∷
   rw 3 (q135 c4) ∷
   rw 1 (q136 c4) ∷
   rw 4 (q137 c4) ∷
   rw 3 (q138 c4) ∷
   rw 2 (q138 c4) ∷
   rw 3 (q139 c4) ∷
   rw 0 (q134 c4) ∷
   rw 1 (q3 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = eqn (Toff203 ∷ Toff203 ∷ []) [] (wl 635 (lit c4))
  q141 : Ws → Eqn
  q141 c4 = eqn (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (lem-VPQ-at0214213043 c4)

-- QVQ @0214213043: 3 steps
lem-QVQ-at0214213043 : Ws → ⟪ (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-QVQ-at0214213043 c4 = derive (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ [])
  (rw⁻ 0 (q140 c4) ∷
   rw⁻ 1 (q141 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = eqn (Toff214 ∷ Toff214 ∷ []) [] (wl 636 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (lem-VPQ-at0210233441 c4)

-- QVQ @0210233441: 3 steps
lem-QVQ-at0210233441 : Ws → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at0210233441 c4 = derive (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  (rw⁻ 0 (q142 c4) ∷
   rw⁻ 1 (q143 c4) ∷
   rw 4 (q20 c4) ∷ []) Eq.refl

private
  q144 : Ws → Eqn
  q144 c4 = eqn (CX43 ∷ CX34 ∷ CX43 ∷ []) (Sw34 ∷ []) (wl 649 (lit c4))
  q145 : Ws → Eqn
  q145 c4 = eqn (CX43 ∷ Bx0-2431 ∷ CX43 ∷ []) (Bx0-2431 ∷ CCZ124 ∷ []) (lem-CXbc-box-at122441 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ124 ∷ CX34 ∷ []) (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl 650 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (CX34 ∷ Bx0-2431 ∷ CX34 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ []) (lem-CXcb-box-at122441 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (CCZ124 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ []) (wl 651 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (CCZ123 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl 652 (lit c4))
  q150 : Ws → Eqn
  q150 c4 = eqn (CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) (wl 653 (lit c4))

-- SWbc-box @122441: 11 steps
lem-SWbc-box-at122441 : Ws → ⟪ (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-SWbc-box-at122441 c4 = derive (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) (Bx0-2431 ∷ [])
  (rw⁻ 0 (q144 c4) ∷
   rw⁻ 4 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw 3 (q146 c4) ∷
   rw 1 (q147 c4) ∷
   rw 4 (q148 c4) ∷
   rw 3 (q149 c4) ∷
   rw 2 (q149 c4) ∷
   rw 3 (q150 c4) ∷
   rw 0 (q145 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = eqn (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (lem-VPQ-at12233441 c4)

-- QVQ @12233441: 3 steps
lem-QVQ-at12233441 : Ws → ⟪ (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-QVQ-at12233441 c4 = derive (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ [])
  (rw⁻ 0 (q34 c4) ∷
   rw⁻ 1 (q151 c4) ∷
   rw 4 (q36 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = eqn (CX12 ∷ CX21 ∷ CX12 ∷ []) (Sw12 ∷ []) (wl 677 (lit c4))
  q153 : Ws → Eqn
  q153 c4 = eqn (CX12 ∷ Bx0-4123 ∷ CX12 ∷ []) (Bx0-4123 ∷ CCZ134 ∷ []) (lem-CXbc-box-at14213243 c4)
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ134 ∷ CX21 ∷ []) (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl 678 (lit c4))
  q155 : Ws → Eqn
  q155 c4 = eqn (CX21 ∷ Bx0-4123 ∷ CX21 ∷ []) (Bx0-4123 ∷ CCZ234 ∷ []) (lem-CXcb-box-at14213243 c4)
  q156 : Ws → Eqn
  q156 c4 = eqn (CCZ134 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ []) (wl 679 (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (CCZ234 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl 680 (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) (wl 681 (lit c4))

-- SWbc-box @14213243: 11 steps
lem-SWbc-box-at14213243 : Ws → ⟪ (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-SWbc-box-at14213243 c4 = derive (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) (Bx0-4123 ∷ [])
  (rw⁻ 0 (q152 c4) ∷
   rw⁻ 4 (q152 c4) ∷
   rw 2 (q153 c4) ∷
   rw 3 (q154 c4) ∷
   rw 1 (q155 c4) ∷
   rw 4 (q156 c4) ∷
   rw 3 (q157 c4) ∷
   rw 2 (q157 c4) ∷
   rw 3 (q158 c4) ∷
   rw 0 (q153 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q159 : Ws → Eqn
  q159 c4 = eqn (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (lem-VPQ-at143143 c4)

-- QVQ @143143: 3 steps
lem-QVQ-at143143 : Ws → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at143143 c4 = derive (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q159 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q160 : Ws → Eqn
  q160 c4 = eqn (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (lem-VPQ-at233442 c4)

-- QVQ @233442: 3 steps
lem-QVQ-at233442 : Ws → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at233442 c4 = derive (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  (rw⁻ 0 (q29 c4) ∷
   rw⁻ 1 (q160 c4) ∷
   rw 4 (q31 c4) ∷ []) Eq.refl

private
  q161 : Ws → Eqn
  q161 c4 = eqn (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0210243143 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (CCZ034 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp 566 c4)
  q163 : Ws → Eqn
  q163 c4 = eqn (CX14 ∷ Bx2-0413 ∷ CX14 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ []) (lem-CXcb-box-at0210243143 c4)
  q164 : Ws → Eqn
  q164 c4 = eqn (CCZ034 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ []) (wp 357 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (CCZ013 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp 567 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ []) (wp 568 c4)

-- SWbc-box @0210243143: 11 steps
lem-SWbc-box-at0210243143 : Ws → ⟪ (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-SWbc-box-at0210243143 c4 = derive (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) (Bx2-0413 ∷ [])
  (rw⁻ 0 (q40 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 2 (q161 c4) ∷
   rw 3 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   rw 4 (q164 c4) ∷
   rw 3 (q165 c4) ∷
   rw 2 (q165 c4) ∷
   rw 3 (q166 c4) ∷
   rw 0 (q161 c4) ∷
   rw 1 (q3 c4) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = eqn (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-QVQ-at0210213443 c4)
  q168 : Ws → Eqn
  q168 c4 = eqn (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0210213443 c4)

-- box-cP @0210213443: 12 steps
lem-box-cP-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-box-cP-at0210213443 c4 = derive (Bx2-0143 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw 2 (q94 c4) ∷
   re 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw 5 (q94 c4) ∷
   rw 2 (q167 c4) ∷
   rw 1 (q168 c4) ∷
   rw 2 (q81 c4) ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = eqn (CX42 ∷ CX24 ∷ CX42 ∷ []) (Sw24 ∷ []) (wl 316 (lit c4))
  q170 : Ws → Eqn
  q170 c4 = eqn (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CXbc-box-at243243 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (CX24 ∷ Bx0-1423 ∷ CX24 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ []) (lem-CXcb-box-at243243 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (CCZ134 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ []) (wl 318 (lit c4))
  q173 : Ws → Eqn
  q173 c4 = eqn (CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) (wl 320 (lit c4))

-- SWbc-box @243243: 11 steps
lem-SWbc-box-at243243 : Ws → ⟪ (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-SWbc-box-at243243 c4 = derive (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) (Bx0-1423 ∷ [])
  (rw⁻ 0 (q169 c4) ∷
   rw⁻ 4 (q169 c4) ∷
   rw 2 (q170 c4) ∷
   rw 3 (q73 c4) ∷
   rw 1 (q171 c4) ∷
   rw 4 (q172 c4) ∷
   rw 3 (q70 c4) ∷
   rw 2 (q70 c4) ∷
   rw 3 (q173 c4) ∷
   rw 0 (q170 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q174 : Ws → Eqn
  q174 c4 = eqn (CX23 ∷ Bx0-4231 ∷ CX23 ∷ []) (Bx0-4231 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1441 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (CX32 ∷ Bx0-4231 ∷ CX32 ∷ []) (Bx0-4231 ∷ CCZ134 ∷ []) (lem-CXcb-box-at1441 c4)

-- SWbc-box @1441: 11 steps
lem-SWbc-box-at1441 : Ws → ⟪ (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-SWbc-box-at1441 c4 = derive (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) (Bx0-4231 ∷ [])
  (rw⁻ 0 (q13 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 2 (q174 c4) ∷
   rw 3 (q15 c4) ∷
   rw 1 (q175 c4) ∷
   rw 4 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw 2 (q18 c4) ∷
   rw 3 (q19 c4) ∷
   rw 0 (q174 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q176 : Ws → Eqn
  q176 c4 = eqn (CCZ012 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (wp 162 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at14233241 c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ []) (lem-tP-at14233241 c4)

-- box-cP @14233241: 12 steps
lem-box-cP-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at14233241 c4 = derive (Bx0-4321 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q176 c4) ∷
   re 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q176 c4) ∷
   rw 2 (q177 c4) ∷
   rw 1 (q178 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = eqn (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (lem-VPQ-at12213443 c4)

-- QVQ @12213443: 3 steps
lem-QVQ-at12213443 : Ws → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ-at12213443 c4 = derive (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q179 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = eqn (S2 ∷ CS24⁻ ∷ X4 ∷ []) (X4 ∷ CS24 ∷ []) (wl 714 (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (CS03⁻ ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CS03⁻ ∷ []) (wp 606 c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (S2 ∷ CS24⁻ ∷ Toff314 ∷ []) (Toff314 ∷ S2 ∷ CS24⁻ ∷ []) (wl 715 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (CS03 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CS03 ∷ []) (wp 607 c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (CS24 ∷ X4 ∷ []) (X4 ∷ S2 ∷ CS24⁻ ∷ []) (wl 716 (lit c4))

-- F4-CS0-S2: 14 steps
lem-F4-CS0-S2 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S2 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q180 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 5 (q181 c4) ∷
   rw⁻ 4 (q182 c4) ∷
   rw 3 (q183 c4) ∷
   rw⁻ 2 (q182 c4) ∷
   rw⁻ 1 (q132 c4) ∷
   rw⁻ 2 (q131 c4) ∷
   re 5 1 (Sb2-0-3-1 ∷ []) ∷
   re 7 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q184 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = eqn (S0 ∷ CS04⁻ ∷ X4 ∷ []) (X4 ∷ CS04 ∷ []) (wp 602 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (CS13⁻ ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS13⁻ ∷ []) (wp 622 c4)
  q187 : Ws → Eqn
  q187 c4 = eqn (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) (Toff324 ∷ S0 ∷ CS04⁻ ∷ []) (wp 623 c4)
  q188 : Ws → Eqn
  q188 c4 = eqn (CS13 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS13 ∷ []) (wp 624 c4)
  q189 : Ws → Eqn
  q189 c4 = eqn (CS04 ∷ X4 ∷ []) (X4 ∷ S0 ∷ CS04⁻ ∷ []) (wp 603 c4)

-- F4-CS1-S0: 14 steps
lem-F4-CS1-S0 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S0 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q185 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 5 (q186 c4) ∷
   rw⁻ 4 (q187 c4) ∷
   rw 3 (q188 c4) ∷
   rw⁻ 2 (q187 c4) ∷
   rw⁻ 1 (q127 c4) ∷
   rw⁻ 2 (q126 c4) ∷
   re 5 1 (Sb0-1-3-2 ∷ []) ∷
   re 7 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 3 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q189 c4) ∷ []) Eq.refl

private
  q190 : Ws → Eqn
  q190 c4 = eqn (CS12⁻ ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS12⁻ ∷ []) (wp 639 c4)
  q191 : Ws → Eqn
  q191 c4 = eqn (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) (Toff134 ∷ S0 ∷ CS04⁻ ∷ []) (wp 640 c4)
  q192 : Ws → Eqn
  q192 c4 = eqn (CS12 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS12 ∷ []) (wp 641 c4)

-- F4-CS2-S0: 14 steps
lem-F4-CS2-S0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S0 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw⁻ 2 (q185 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 5 (q190 c4) ∷
   rw⁻ 4 (q191 c4) ∷
   rw 3 (q192 c4) ∷
   rw⁻ 2 (q191 c4) ∷
   rw⁻ 1 (q129 c4) ∷
   rw⁻ 2 (q128 c4) ∷
   re 5 1 (Sb0-2-1-3 ∷ []) ∷
   re 7 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 3 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 0 (q189 c4) ∷ []) Eq.refl

private
  q193 : Ws → Eqn
  q193 c4 = eqn (CX10 ∷ CX01 ∷ CX10 ∷ []) (Sw01 ∷ []) (wl 755 (lit c4))
  q194 : Ws → Eqn
  q194 c4 = eqn (CX10 ∷ Bx3-4102 ∷ CX10 ∷ []) (Bx3-4102 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0314213042 c4)
  q195 : Ws → Eqn
  q195 c4 = eqn (CCZ124 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp 671 c4)
  q196 : Ws → Eqn
  q196 c4 = eqn (CX01 ∷ Bx3-4102 ∷ CX01 ∷ []) (Bx3-4102 ∷ CCZ024 ∷ []) (lem-CXcb-box-at0314213042 c4)
  q197 : Ws → Eqn
  q197 c4 = eqn (CCZ124 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ []) (wp 672 c4)
  q198 : Ws → Eqn
  q198 c4 = eqn (CCZ024 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp 673 c4)
  q199 : Ws → Eqn
  q199 c4 = eqn (CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) (wp 674 c4)

-- SWbc-box @0314213042: 11 steps
lem-SWbc-box-at0314213042 : Ws → ⟪ (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-SWbc-box-at0314213042 c4 = derive (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) (Bx3-4102 ∷ [])
  (rw⁻ 0 (q193 c4) ∷
   rw⁻ 4 (q193 c4) ∷
   rw 2 (q194 c4) ∷
   rw 3 (q195 c4) ∷
   rw 1 (q196 c4) ∷
   rw 4 (q197 c4) ∷
   rw 3 (q198 c4) ∷
   rw 2 (q198 c4) ∷
   rw 3 (q199 c4) ∷
   rw 0 (q194 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q200 : Ws → Eqn
  q200 c4 = eqn (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (lem-VPQ-at0213203441 c4)

-- QVQ @0213203441: 3 steps
lem-QVQ-at0213203441 : Ws → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at0213203441 c4 = derive (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  (rw⁻ 0 (q142 c4) ∷
   rw⁻ 1 (q200 c4) ∷
   rw 4 (q20 c4) ∷ []) Eq.refl

private
  q201 : Ws → Eqn
  q201 c4 = eqn (CX01 ∷ Bx3-4012 ∷ CX01 ∷ []) (Bx3-4012 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0314203142 c4)
  q202 : Ws → Eqn
  q202 c4 = eqn (CX10 ∷ Bx3-4012 ∷ CX10 ∷ []) (Bx3-4012 ∷ CCZ124 ∷ []) (lem-CXcb-box-at0314203142 c4)
  q203 : Ws → Eqn
  q203 c4 = eqn (CCZ024 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ []) (wp 22 c4)
  q204 : Ws → Eqn
  q204 c4 = eqn (CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ []) (CCZ024 ∷ []) (wp 694 c4)

-- SWbc-box @0314203142: 11 steps
lem-SWbc-box-at0314203142 : Ws → ⟪ (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-SWbc-box-at0314203142 c4 = derive (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) (Bx3-4012 ∷ [])
  (rw⁻ 0 (q133 c4) ∷
   rw⁻ 4 (q133 c4) ∷
   rw 2 (q201 c4) ∷
   rw 3 (q198 c4) ∷
   rw 1 (q202 c4) ∷
   rw 4 (q203 c4) ∷
   rw 3 (q195 c4) ∷
   rw 2 (q195 c4) ∷
   rw 3 (q204 c4) ∷
   rw 0 (q201 c4) ∷
   rw 1 (q31 c4) ∷ []) Eq.refl

private
  q205 : Ws → Eqn
  q205 c4 = eqn (Toff302 ∷ Toff302 ∷ []) [] (wl 787 (lit c4))
  q206 : Ws → Eqn
  q206 c4 = eqn (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (lem-VPQ-at0314213042 c4)

-- QVQ @0314213042: 3 steps
lem-QVQ-at0314213042 : Ws → ⟪ (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-QVQ-at0314213042 c4 = derive (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ [])
  (rw⁻ 0 (q205 c4) ∷
   rw⁻ 1 (q206 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q207 : Ws → Eqn
  q207 c4 = eqn (CX10 ∷ Bx2-4103 ∷ CX10 ∷ []) (Bx2-4103 ∷ CCZ134 ∷ []) (lem-CXbc-box-at0214213043 c4)
  q208 : Ws → Eqn
  q208 c4 = eqn (CX01 ∷ Bx2-4103 ∷ CX01 ∷ []) (Bx2-4103 ∷ CCZ034 ∷ []) (lem-CXcb-box-at0214213043 c4)
  q209 : Ws → Eqn
  q209 c4 = eqn (CCZ134 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ []) (wp 712 c4)
  q210 : Ws → Eqn
  q210 c4 = eqn (CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) (wp 713 c4)

-- SWbc-box @0214213043: 11 steps
lem-SWbc-box-at0214213043 : Ws → ⟪ (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-SWbc-box-at0214213043 c4 = derive (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) (Bx2-4103 ∷ [])
  (rw⁻ 0 (q193 c4) ∷
   rw⁻ 4 (q193 c4) ∷
   rw 2 (q207 c4) ∷
   rw 3 (q138 c4) ∷
   rw 1 (q208 c4) ∷
   rw 4 (q209 c4) ∷
   rw 3 (q135 c4) ∷
   rw 2 (q135 c4) ∷
   rw 3 (q210 c4) ∷
   rw 0 (q207 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q211 : Ws → Eqn
  q211 c4 = eqn (CX21 ∷ CX12 ∷ CX21 ∷ []) (Sw12 ∷ []) (wl 835 (lit c4))
  q212 : Ws → Eqn
  q212 c4 = eqn (CX21 ∷ Bx0-3214 ∷ CX21 ∷ []) (Bx0-3214 ∷ CCZ234 ∷ []) (lem-CXbc-box-at1331 c4)
  q213 : Ws → Eqn
  q213 c4 = eqn (CX12 ∷ Bx0-3214 ∷ CX12 ∷ []) (Bx0-3214 ∷ CCZ134 ∷ []) (lem-CXcb-box-at1331 c4)
  q214 : Ws → Eqn
  q214 c4 = eqn (CCZ234 ∷ CX21 ∷ []) (CX21 ∷ CCZ234 ∷ []) (wl 836 (lit c4))
  q215 : Ws → Eqn
  q215 c4 = eqn (CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ []) (CCZ234 ∷ []) (wl 837 (lit c4))

-- SWbc-box @1331: 11 steps
lem-SWbc-box-at1331 : Ws → ⟪ (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-SWbc-box-at1331 c4 = derive (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) (Bx0-3214 ∷ [])
  (rw⁻ 0 (q211 c4) ∷
   rw⁻ 4 (q211 c4) ∷
   rw 2 (q212 c4) ∷
   rw 3 (q157 c4) ∷
   rw 1 (q213 c4) ∷
   rw 4 (q214 c4) ∷
   rw 3 (q154 c4) ∷
   rw 2 (q154 c4) ∷
   rw 3 (q215 c4) ∷
   rw 0 (q212 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

private
  q216 : Ws → Eqn
  q216 c4 = eqn (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) (wl 518 (lit c4))
  q217 : Ws → Eqn
  q217 c4 = eqn (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-QVQ-at032032 c4)
  q218 : Ws → Eqn
  q218 c4 = eqn (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ []) (lem-tP-at032032 c4)

-- box-cP @032032: 12 steps
lem-box-cP-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-box-cP-at032032 c4 = derive (Bx3-1024 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q216 c4) ∷
   re 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q216 c4) ∷
   rw 2 (q217 c4) ∷
   rw 1 (q218 c4) ∷
   rw 2 (q92 c4) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = eqn (CX41 ∷ Bx3-2410 ∷ CX41 ∷ []) (Bx3-2410 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0312243140 c4)
  q220 : Ws → Eqn
  q220 c4 = eqn (CCZ024 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp 729 c4)
  q221 : Ws → Eqn
  q221 c4 = eqn (CX14 ∷ Bx3-2410 ∷ CX14 ∷ []) (Bx3-2410 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0312243140 c4)
  q222 : Ws → Eqn
  q222 c4 = eqn (CCZ024 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ []) (wp 285 c4)
  q223 : Ws → Eqn
  q223 c4 = eqn (CCZ012 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp 730 c4)
  q224 : Ws → Eqn
  q224 c4 = eqn (CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ []) (wp 731 c4)

-- SWbc-box @0312243140: 11 steps
lem-SWbc-box-at0312243140 : Ws → ⟪ (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-SWbc-box-at0312243140 c4 = derive (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) (Bx3-2410 ∷ [])
  (rw⁻ 0 (q40 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 2 (q219 c4) ∷
   rw 3 (q220 c4) ∷
   rw 1 (q221 c4) ∷
   rw 4 (q222 c4) ∷
   rw 3 (q223 c4) ∷
   rw 2 (q223 c4) ∷
   rw 3 (q224 c4) ∷
   rw 0 (q219 c4) ∷
   rw 1 (q31 c4) ∷ []) Eq.refl

private
  q225 : Ws → Eqn
  q225 c4 = eqn (CX14 ∷ Bx3-2140 ∷ CX14 ∷ []) (Bx3-2140 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0312213440 c4)
  q226 : Ws → Eqn
  q226 c4 = eqn (CX41 ∷ Bx3-2140 ∷ CX41 ∷ []) (Bx3-2140 ∷ CCZ024 ∷ []) (lem-CXcb-box-at0312213440 c4)
  q227 : Ws → Eqn
  q227 c4 = eqn (CCZ012 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ []) (wp 145 c4)
  q228 : Ws → Eqn
  q228 c4 = eqn (CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) (wp 738 c4)
  q229 : Ws → Eqn
  q229 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl 341 (lit c4))

-- SWbc-box @0312213440: 11 steps
lem-SWbc-box-at0312213440 : Ws → ⟪ (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-SWbc-box-at0312213440 c4 = derive (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) (Bx3-2140 ∷ [])
  (rw⁻ 0 (q82 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 2 (q225 c4) ∷
   rw 3 (q223 c4) ∷
   rw 1 (q226 c4) ∷
   rw 4 (q227 c4) ∷
   rw 3 (q220 c4) ∷
   rw 2 (q220 c4) ∷
   rw 3 (q228 c4) ∷
   rw 0 (q225 c4) ∷
   rw 1 (q229 c4) ∷ []) Eq.refl

private
  q230 : Ws → Eqn
  q230 c4 = eqn (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (lem-VPQ-at0312243140 c4)

-- QVQ @0312243140: 3 steps
lem-QVQ-at0312243140 : Ws → ⟪ (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-QVQ-at0312243140 c4 = derive (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q92 c4) ∷
   rw⁻ 1 (q230 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q231 : Ws → Eqn
  q231 c4 = eqn (CX12 ∷ Bx0-3124 ∷ CX12 ∷ []) (Bx0-3124 ∷ CCZ134 ∷ []) (lem-CXbc-box-at132132 c4)
  q232 : Ws → Eqn
  q232 c4 = eqn (CX21 ∷ Bx0-3124 ∷ CX21 ∷ []) (Bx0-3124 ∷ CCZ234 ∷ []) (lem-CXcb-box-at132132 c4)

-- SWbc-box @132132: 11 steps
lem-SWbc-box-at132132 : Ws → ⟪ (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-SWbc-box-at132132 c4 = derive (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) (Bx0-3124 ∷ [])
  (rw⁻ 0 (q152 c4) ∷
   rw⁻ 4 (q152 c4) ∷
   rw 2 (q231 c4) ∷
   rw 3 (q154 c4) ∷
   rw 1 (q232 c4) ∷
   rw 4 (q156 c4) ∷
   rw 3 (q157 c4) ∷
   rw 2 (q157 c4) ∷
   rw 3 (q158 c4) ∷
   rw 0 (q231 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q233 : Ws → Eqn
  q233 c4 = eqn (CX30 ∷ CX03 ∷ CX30 ∷ []) (Sw03 ∷ []) (wl 923 (lit c4))
  q234 : Ws → Eqn
  q234 c4 = eqn (CX30 ∷ Bx2-1304 ∷ CX30 ∷ []) (Bx2-1304 ∷ CCZ134 ∷ []) (lem-CXbc-box-at022330 c4)
  q235 : Ws → Eqn
  q235 c4 = eqn (CCZ134 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp 762 c4)
  q236 : Ws → Eqn
  q236 c4 = eqn (CX03 ∷ Bx2-1304 ∷ CX03 ∷ []) (Bx2-1304 ∷ CCZ014 ∷ []) (lem-CXcb-box-at022330 c4)
  q237 : Ws → Eqn
  q237 c4 = eqn (CCZ134 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ []) (wp 705 c4)
  q238 : Ws → Eqn
  q238 c4 = eqn (CCZ014 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp 763 c4)
  q239 : Ws → Eqn
  q239 c4 = eqn (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) (wp 764 c4)

-- SWbc-box @022330: 11 steps
lem-SWbc-box-at022330 : Ws → ⟪ (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-SWbc-box-at022330 c4 = derive (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) (Bx2-1304 ∷ [])
  (rw⁻ 0 (q233 c4) ∷
   rw⁻ 4 (q233 c4) ∷
   rw 2 (q234 c4) ∷
   rw 3 (q235 c4) ∷
   rw 1 (q236 c4) ∷
   rw 4 (q237 c4) ∷
   rw 3 (q238 c4) ∷
   rw 2 (q238 c4) ∷
   rw 3 (q239 c4) ∷
   rw 0 (q234 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q240 : Ws → Eqn
  q240 c4 = eqn (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-QVQ-at0220 c4)
  q241 : Ws → Eqn
  q241 c4 = eqn (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0220 c4)

-- box-cP @0220: 12 steps
lem-box-cP-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-box-cP-at0220 c4 = derive (Bx2-1034 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q216 c4) ∷
   re 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q216 c4) ∷
   rw 2 (q240 c4) ∷
   rw 1 (q241 c4) ∷
   rw 2 (q81 c4) ∷ []) Eq.refl

private
  q242 : Ws → Eqn
  q242 c4 = eqn (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) (Bx2-3410 ∷ []) (lem-SWbc-box-at0213243140 c4)
  q243 : Ws → Eqn
  q243 c4 = eqn (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) (Bx2-3140 ∷ []) (lem-nat-SWbc-at0213243140 c4)

-- sym-bc @0213243140: 2 steps
lem-sym-bc-at0213243140 : Ws → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-sym-bc-at0213243140 c4 = derive (Bx2-3410 ∷ []) (Bx2-3140 ∷ [])
  (rw⁻ 0 (q242 c4) ∷
   rw 0 (q243 c4) ∷ []) Eq.refl

private
  q244 : Ws → Eqn
  q244 c4 = eqn (CX14 ∷ Bx2-3140 ∷ CX14 ∷ []) (Bx2-3140 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0213213440 c4)
  q245 : Ws → Eqn
  q245 c4 = eqn (CX41 ∷ Bx2-3140 ∷ CX41 ∷ []) (Bx2-3140 ∷ CCZ034 ∷ []) (lem-CXcb-box-at0213213440 c4)
  q246 : Ws → Eqn
  q246 c4 = eqn (CCZ013 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ []) (wp 189 c4)
  q247 : Ws → Eqn
  q247 c4 = eqn (CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) (wp 769 c4)

-- SWbc-box @0213213440: 11 steps
lem-SWbc-box-at0213213440 : Ws → ⟪ (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-SWbc-box-at0213213440 c4 = derive (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) (Bx2-3140 ∷ [])
  (rw⁻ 0 (q82 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 2 (q244 c4) ∷
   rw 3 (q165 c4) ∷
   rw 1 (q245 c4) ∷
   rw 4 (q246 c4) ∷
   rw 3 (q162 c4) ∷
   rw 2 (q162 c4) ∷
   rw 3 (q247 c4) ∷
   rw 0 (q244 c4) ∷
   rw 1 (q12 c4) ∷ []) Eq.refl

private
  q248 : Ws → Eqn
  q248 c4 = eqn (CCZ012 ∷ []) (CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ []) (wl 935 (lit c4))
  q249 : Ws → Eqn
  q249 c4 = eqn (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-QVQ-at0213243140 c4)
  q250 : Ws → Eqn
  q250 c4 = eqn (Toff234 ∷ Toff201 ∷ []) (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0213243140 c4)
  q251 : Ws → Eqn
  q251 c4 = eqn (Toff234 ∷ Toff234 ∷ []) [] (wl 420 (lit c4))

-- box-cP @0213243140: 12 steps
lem-box-cP-at0213243140 : Ws → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-box-cP-at0213243140 c4 = derive (Bx2-3410 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw⁻ 2 (q248 c4) ∷
   re 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw⁻ 5 (q248 c4) ∷
   rw 2 (q249 c4) ∷
   rw 1 (q250 c4) ∷
   rw 2 (q251 c4) ∷ []) Eq.refl

private
  q252 : Ws → Eqn
  q252 c4 = eqn (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) (Bx2-1034 ∷ []) (lem-SWbc-box-at0220 c4)
  q253 : Ws → Eqn
  q253 c4 = eqn (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) (Bx2-1304 ∷ []) (lem-nat-SWbc-at0220 c4)

-- sym-bc @0220: 2 steps
lem-sym-bc-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym-bc-at0220 c4 = derive (Bx2-1034 ∷ []) (Bx2-1304 ∷ [])
  (rw⁻ 0 (q252 c4) ∷
   rw 0 (q253 c4) ∷ []) Eq.refl

private
  q254 : Ws → Eqn
  q254 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp 19 c4)
  q255 : Ws → Eqn
  q255 c4 = eqn (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (lem-VPQ-at022330 c4)

-- QVQ @022330: 3 steps
lem-QVQ-at022330 : Ws → ⟪ (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-QVQ-at022330 c4 = derive (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ [])
  (rw⁻ 0 (q254 c4) ∷
   rw⁻ 1 (q255 c4) ∷
   rw 4 (q31 c4) ∷ []) Eq.refl

private
  q256 : Ws → Eqn
  q256 c4 = eqn (CX31 ∷ CX13 ∷ CX31 ∷ []) (Sw13 ∷ []) (wl 335 (lit c4))
  q257 : Ws → Eqn
  q257 c4 = eqn (CX31 ∷ Bx0-2314 ∷ CX31 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ []) (lem-CXbc-box-at122331 c4)
  q258 : Ws → Eqn
  q258 c4 = eqn (CX13 ∷ Bx0-2314 ∷ CX13 ∷ []) (Bx0-2314 ∷ CCZ124 ∷ []) (lem-CXcb-box-at122331 c4)
  q259 : Ws → Eqn
  q259 c4 = eqn (CCZ234 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ []) (wl 336 (lit c4))
  q260 : Ws → Eqn
  q260 c4 = eqn (CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) (CCZ234 ∷ []) (wl 337 (lit c4))

-- SWbc-box @122331: 11 steps
lem-SWbc-box-at122331 : Ws → ⟪ (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-SWbc-box-at122331 c4 = derive (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) (Bx0-2314 ∷ [])
  (rw⁻ 0 (q256 c4) ∷
   rw⁻ 4 (q256 c4) ∷
   rw 2 (q257 c4) ∷
   rw 3 (q26 c4) ∷
   rw 1 (q258 c4) ∷
   rw 4 (q259 c4) ∷
   rw 3 (q23 c4) ∷
   rw 2 (q23 c4) ∷
   rw 3 (q260 c4) ∷
   rw 0 (q257 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

private
  q261 : Ws → Eqn
  q261 c4 = eqn (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (lem-VPQ-at14213243 c4)

-- QVQ @14213243: 3 steps
lem-QVQ-at14213243 : Ws → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at14213243 c4 = derive (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q261 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q262 : Ws → Eqn
  q262 c4 = eqn (CX34 ∷ CX43 ∷ CX34 ∷ []) (Sw34 ∷ []) (wl 547 (lit c4))
  q263 : Ws → Eqn
  q263 c4 = eqn (CX34 ∷ Bx0-2341 ∷ CX34 ∷ []) (Bx0-2341 ∷ CCZ123 ∷ []) (lem-CXbc-box-at12233441 c4)
  q264 : Ws → Eqn
  q264 c4 = eqn (CX43 ∷ Bx0-2341 ∷ CX43 ∷ []) (Bx0-2341 ∷ CCZ124 ∷ []) (lem-CXcb-box-at12233441 c4)
  q265 : Ws → Eqn
  q265 c4 = eqn (CCZ123 ∷ CX34 ∷ []) (CX34 ∷ CCZ123 ∷ []) (wl 1008 (lit c4))
  q266 : Ws → Eqn
  q266 c4 = eqn (CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) (wl 1009 (lit c4))

-- SWbc-box @12233441: 11 steps
lem-SWbc-box-at12233441 : Ws → ⟪ (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-SWbc-box-at12233441 c4 = derive (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) (Bx0-2341 ∷ [])
  (rw⁻ 0 (q262 c4) ∷
   rw⁻ 4 (q262 c4) ∷
   rw 2 (q263 c4) ∷
   rw 3 (q149 c4) ∷
   rw 1 (q264 c4) ∷
   rw 4 (q265 c4) ∷
   rw 3 (q146 c4) ∷
   rw 2 (q146 c4) ∷
   rw 3 (q266 c4) ∷
   rw 0 (q263 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q267 : Ws → Eqn
  q267 c4 = eqn (CX32 ∷ CX23 ∷ CX32 ∷ []) (Sw23 ∷ []) (wl 1020 (lit c4))
  q268 : Ws → Eqn
  q268 c4 = eqn (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CXbc-box-at2332 c4)
  q269 : Ws → Eqn
  q269 c4 = eqn (CX23 ∷ Bx0-1324 ∷ CX23 ∷ []) (Bx0-1324 ∷ CCZ124 ∷ []) (lem-CXcb-box-at2332 c4)
  q270 : Ws → Eqn
  q270 c4 = eqn (CCZ134 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ []) (wl 1021 (lit c4))
  q271 : Ws → Eqn
  q271 c4 = eqn (CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) (wl 1022 (lit c4))

-- SWbc-box @2332: 11 steps
lem-SWbc-box-at2332 : Ws → ⟪ (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-SWbc-box-at2332 c4 = derive (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) (Bx0-1324 ∷ [])
  (rw⁻ 0 (q267 c4) ∷
   rw⁻ 4 (q267 c4) ∷
   rw 2 (q268 c4) ∷
   rw 3 (q18 c4) ∷
   rw 1 (q269 c4) ∷
   rw 4 (q270 c4) ∷
   rw 3 (q15 c4) ∷
   rw 2 (q15 c4) ∷
   rw 3 (q271 c4) ∷
   rw 0 (q268 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q272 : Ws → Eqn
  q272 c4 = eqn (CS04 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4)
  q273 : Ws → Eqn
  q273 c4 = eqn (CS04 ∷ Toff324 ∷ []) (Toff324 ∷ CS04 ∷ []) (wp 393 c4)
  q274 : Ws → Eqn
  q274 c4 = eqn (CS04 ∷ CS13 ∷ []) (CS13 ∷ CS04 ∷ []) (wp 856 c4)
  q275 : Ws → Eqn
  q275 c4 = eqn (CS04 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS04 ∷ []) (wp 857 c4)

-- F2-S0-CS1: 11 steps
lem-F2-S0-CS1 : Ws → ⟪ (CS04 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-CS1 c4 = derive (CS04 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS04 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 0 (q272 c4) ∷
   rw 1 (q273 c4) ∷
   rw 2 (q274 c4) ∷
   rw 3 (q273 c4) ∷
   rw 4 (q275 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q276 : Ws → Eqn
  q276 c4 = eqn (CS04 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4)
  q277 : Ws → Eqn
  q277 c4 = eqn (CS04 ∷ Toff134 ∷ []) (Toff134 ∷ CS04 ∷ []) (wp 858 c4)
  q278 : Ws → Eqn
  q278 c4 = eqn (CS04 ∷ CS12 ∷ []) (CS12 ∷ CS04 ∷ []) (wp 859 c4)
  q279 : Ws → Eqn
  q279 c4 = eqn (CS04 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04 ∷ []) (wp 860 c4)

-- F2-S0-CS2: 11 steps
lem-F2-S0-CS2 : Ws → ⟪ (CS04 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-CS2 c4 = derive (CS04 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS04 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 0 (q276 c4) ∷
   rw 1 (q277 c4) ∷
   rw 2 (q278 c4) ∷
   rw 3 (q277 c4) ∷
   rw 4 (q279 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q280 : Ws → Eqn
  q280 c4 = eqn (CS24 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4)
  q281 : Ws → Eqn
  q281 c4 = eqn (CS24 ∷ Toff314 ∷ []) (Toff314 ∷ CS24 ∷ []) (wl 754 (lit c4))
  q282 : Ws → Eqn
  q282 c4 = eqn (CS03 ∷ CS24 ∷ []) (CS24 ∷ CS03 ∷ []) (wp 863 c4)
  q283 : Ws → Eqn
  q283 c4 = eqn (CS03⁻ ∷ CS24 ∷ []) (CS24 ∷ CS03⁻ ∷ []) (wp 864 c4)

-- F2-S2-CS0: 11 steps
lem-F2-S2-CS0 : Ws → ⟪ (CS24 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-CS0 c4 = derive (CS24 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 0 (q280 c4) ∷
   rw 1 (q281 c4) ∷
   rw⁻ 2 (q282 c4) ∷
   rw 3 (q281 c4) ∷
   rw⁻ 4 (q283 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q284 : Ws → Eqn
  q284 c4 = eqn (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) (Bx3-0124 ∷ []) (lem-SWbc-box-at03102132 c4)
  q285 : Ws → Eqn
  q285 c4 = eqn (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) (Bx3-0214 ∷ []) (lem-nat-SWbc-at03102132 c4)

-- sym-bc @03102132: 2 steps
lem-sym-bc-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym-bc-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-0214 ∷ [])
  (rw⁻ 0 (q284 c4) ∷
   rw 0 (q285 c4) ∷ []) Eq.refl

private
  q286 : Ws → Eqn
  q286 c4 = eqn (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (lem-VPQ-at0214203143 c4)

-- QVQ @0214203143: 3 steps
lem-QVQ-at0214203143 : Ws → ⟪ (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-QVQ-at0214203143 c4 = derive (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ [])
  (rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q286 c4) ∷
   rw 4 (q6 c4) ∷ []) Eq.refl

private
  q287 : Ws → Eqn
  q287 c4 = eqn (CX34 ∷ Bx2-1340 ∷ CX34 ∷ []) (Bx2-1340 ∷ CCZ013 ∷ []) (lem-CXbc-box-at02233440 c4)
  q288 : Ws → Eqn
  q288 c4 = eqn (CCZ013 ∷ CX43 ∷ []) (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp 916 c4)
  q289 : Ws → Eqn
  q289 c4 = eqn (CX43 ∷ Bx2-1340 ∷ CX43 ∷ []) (Bx2-1340 ∷ CCZ014 ∷ []) (lem-CXcb-box-at02233440 c4)
  q290 : Ws → Eqn
  q290 c4 = eqn (CCZ013 ∷ CX34 ∷ []) (CX34 ∷ CCZ013 ∷ []) (wp 523 c4)
  q291 : Ws → Eqn
  q291 c4 = eqn (CCZ014 ∷ CX34 ∷ []) (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp 917 c4)
  q292 : Ws → Eqn
  q292 c4 = eqn (CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) (wp 918 c4)

-- SWbc-box @02233440: 11 steps
lem-SWbc-box-at02233440 : Ws → ⟪ (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-SWbc-box-at02233440 c4 = derive (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) (Bx2-1340 ∷ [])
  (rw⁻ 0 (q262 c4) ∷
   rw⁻ 4 (q262 c4) ∷
   rw 2 (q287 c4) ∷
   rw 3 (q288 c4) ∷
   rw 1 (q289 c4) ∷
   rw 4 (q290 c4) ∷
   rw 3 (q291 c4) ∷
   rw 2 (q291 c4) ∷
   rw 3 (q292 c4) ∷
   rw 0 (q287 c4) ∷
   rw 1 (q12 c4) ∷ []) Eq.refl

private
  q293 : Ws → Eqn
  q293 c4 = eqn (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (lem-VPQ-at022440 c4)

-- QVQ @022440: 3 steps
lem-QVQ-at022440 : Ws → ⟪ (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-QVQ-at022440 c4 = derive (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ [])
  (rw⁻ 0 (q140 c4) ∷
   rw⁻ 1 (q293 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q294 : Ws → Eqn
  q294 c4 = eqn (CX43 ∷ Bx2-1430 ∷ CX43 ∷ []) (Bx2-1430 ∷ CCZ014 ∷ []) (lem-CXbc-box-at022440 c4)
  q295 : Ws → Eqn
  q295 c4 = eqn (CX34 ∷ Bx2-1430 ∷ CX34 ∷ []) (Bx2-1430 ∷ CCZ013 ∷ []) (lem-CXcb-box-at022440 c4)
  q296 : Ws → Eqn
  q296 c4 = eqn (CCZ014 ∷ CX43 ∷ []) (CX43 ∷ CCZ014 ∷ []) (wp 810 c4)
  q297 : Ws → Eqn
  q297 c4 = eqn (CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) (wp 924 c4)

-- SWbc-box @022440: 11 steps
lem-SWbc-box-at022440 : Ws → ⟪ (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-SWbc-box-at022440 c4 = derive (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) (Bx2-1430 ∷ [])
  (rw⁻ 0 (q144 c4) ∷
   rw⁻ 4 (q144 c4) ∷
   rw 2 (q294 c4) ∷
   rw 3 (q291 c4) ∷
   rw 1 (q295 c4) ∷
   rw 4 (q296 c4) ∷
   rw 3 (q288 c4) ∷
   rw 2 (q288 c4) ∷
   rw 3 (q297 c4) ∷
   rw 0 (q294 c4) ∷
   rw 1 (q36 c4) ∷ []) Eq.refl

private
  q298 : Ws → Eqn
  q298 c4 = eqn (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (lem-VPQ-at02233440 c4)

-- QVQ @02233440: 3 steps
lem-QVQ-at02233440 : Ws → ⟪ (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-QVQ-at02233440 c4 = derive (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ [])
  (rw⁻ 0 (q254 c4) ∷
   rw⁻ 1 (q298 c4) ∷
   rw 4 (q31 c4) ∷ []) Eq.refl

private
  q299 : Ws → Eqn
  q299 c4 = eqn (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (lem-VPQ-at1441 c4)

-- QVQ @1441: 3 steps
lem-QVQ-at1441 : Ws → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at1441 c4 = derive (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q299 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q300 : Ws → Eqn
  q300 c4 = eqn (CX34 ∷ Bx2-0341 ∷ CX34 ∷ []) (Bx2-0341 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0210233441 c4)
  q301 : Ws → Eqn
  q301 c4 = eqn (CX43 ∷ Bx2-0341 ∷ CX43 ∷ []) (Bx2-0341 ∷ CCZ014 ∷ []) (lem-CXcb-box-at0210233441 c4)

-- SWbc-box @0210233441: 11 steps
lem-SWbc-box-at0210233441 : Ws → ⟪ (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-SWbc-box-at0210233441 c4 = derive (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) (Bx2-0341 ∷ [])
  (rw⁻ 0 (q262 c4) ∷
   rw⁻ 4 (q262 c4) ∷
   rw 2 (q300 c4) ∷
   rw 3 (q288 c4) ∷
   rw 1 (q301 c4) ∷
   rw 4 (q290 c4) ∷
   rw 3 (q291 c4) ∷
   rw 2 (q291 c4) ∷
   rw 3 (q292 c4) ∷
   rw 0 (q300 c4) ∷
   rw 1 (q12 c4) ∷ []) Eq.refl

private
  q302 : Ws → Eqn
  q302 c4 = eqn (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (lem-VPQ-at02102441 c4)

-- QVQ @02102441: 3 steps
lem-QVQ-at02102441 : Ws → ⟪ (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-QVQ-at02102441 c4 = derive (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ [])
  (rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q302 c4) ∷
   rw 4 (q6 c4) ∷ []) Eq.refl

private
  q303 : Ws → Eqn
  q303 c4 = eqn (CX43 ∷ Bx2-0431 ∷ CX43 ∷ []) (Bx2-0431 ∷ CCZ014 ∷ []) (lem-CXbc-box-at02102441 c4)
  q304 : Ws → Eqn
  q304 c4 = eqn (CX34 ∷ Bx2-0431 ∷ CX34 ∷ []) (Bx2-0431 ∷ CCZ013 ∷ []) (lem-CXcb-box-at02102441 c4)

-- SWbc-box @02102441: 11 steps
lem-SWbc-box-at02102441 : Ws → ⟪ (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-SWbc-box-at02102441 c4 = derive (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) (Bx2-0431 ∷ [])
  (rw⁻ 0 (q144 c4) ∷
   rw⁻ 4 (q144 c4) ∷
   rw 2 (q303 c4) ∷
   rw 3 (q291 c4) ∷
   rw 1 (q304 c4) ∷
   rw 4 (q296 c4) ∷
   rw 3 (q288 c4) ∷
   rw 2 (q288 c4) ∷
   rw 3 (q297 c4) ∷
   rw 0 (q303 c4) ∷
   rw 1 (q36 c4) ∷ []) Eq.refl

private
  q305 : Ws → Eqn
  q305 c4 = eqn (CX34 ∷ Bx0-1342 ∷ CX34 ∷ []) (Bx0-1342 ∷ CCZ123 ∷ []) (lem-CXbc-box-at233442 c4)
  q306 : Ws → Eqn
  q306 c4 = eqn (CX43 ∷ Bx0-1342 ∷ CX43 ∷ []) (Bx0-1342 ∷ CCZ124 ∷ []) (lem-CXcb-box-at233442 c4)

-- SWbc-box @233442: 11 steps
lem-SWbc-box-at233442 : Ws → ⟪ (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-SWbc-box-at233442 c4 = derive (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) (Bx0-1342 ∷ [])
  (rw⁻ 0 (q262 c4) ∷
   rw⁻ 4 (q262 c4) ∷
   rw 2 (q305 c4) ∷
   rw 3 (q149 c4) ∷
   rw 1 (q306 c4) ∷
   rw 4 (q265 c4) ∷
   rw 3 (q146 c4) ∷
   rw 2 (q146 c4) ∷
   rw 3 (q266 c4) ∷
   rw 0 (q305 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q307 : Ws → Eqn
  q307 c4 = eqn (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (lem-VPQ-at2442 c4)

-- QVQ @2442: 3 steps
lem-QVQ-at2442 : Ws → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at2442 c4 = derive (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q307 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q308 : Ws → Eqn
  q308 c4 = eqn (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) (Bx0-1432 ∷ CCZ124 ∷ []) (lem-CXbc-box-at2442 c4)
  q309 : Ws → Eqn
  q309 c4 = eqn (CX34 ∷ Bx0-1432 ∷ CX34 ∷ []) (Bx0-1432 ∷ CCZ123 ∷ []) (lem-CXcb-box-at2442 c4)

-- SWbc-box @2442: 11 steps
lem-SWbc-box-at2442 : Ws → ⟪ (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-SWbc-box-at2442 c4 = derive (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) (Bx0-1432 ∷ [])
  (rw⁻ 0 (q144 c4) ∷
   rw⁻ 4 (q144 c4) ∷
   rw 2 (q308 c4) ∷
   rw 3 (q146 c4) ∷
   rw 1 (q309 c4) ∷
   rw 4 (q148 c4) ∷
   rw 3 (q149 c4) ∷
   rw 2 (q149 c4) ∷
   rw 3 (q150 c4) ∷
   rw 0 (q308 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q310 : Ws → Eqn
  q310 c4 = eqn (CX21 ∷ Bx0-4213 ∷ CX21 ∷ []) (Bx0-4213 ∷ CCZ234 ∷ []) (lem-CXbc-box-at143143 c4)
  q311 : Ws → Eqn
  q311 c4 = eqn (CX12 ∷ Bx0-4213 ∷ CX12 ∷ []) (Bx0-4213 ∷ CCZ134 ∷ []) (lem-CXcb-box-at143143 c4)

-- SWbc-box @143143: 11 steps
lem-SWbc-box-at143143 : Ws → ⟪ (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-SWbc-box-at143143 c4 = derive (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) (Bx0-4213 ∷ [])
  (rw⁻ 0 (q211 c4) ∷
   rw⁻ 4 (q211 c4) ∷
   rw 2 (q310 c4) ∷
   rw 3 (q157 c4) ∷
   rw 1 (q311 c4) ∷
   rw 4 (q214 c4) ∷
   rw 3 (q154 c4) ∷
   rw 2 (q154 c4) ∷
   rw 3 (q215 c4) ∷
   rw 0 (q310 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

private
  q312 : Ws → Eqn
  q312 c4 = eqn (CX14 ∷ Bx0-2143 ∷ CX14 ∷ []) (Bx0-2143 ∷ CCZ123 ∷ []) (lem-CXbc-box-at12213443 c4)
  q313 : Ws → Eqn
  q313 c4 = eqn (CX41 ∷ Bx0-2143 ∷ CX41 ∷ []) (Bx0-2143 ∷ CCZ234 ∷ []) (lem-CXcb-box-at12213443 c4)

-- SWbc-box @12213443: 11 steps
lem-SWbc-box-at12213443 : Ws → ⟪ (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-SWbc-box-at12213443 c4 = derive (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) (Bx0-2143 ∷ [])
  (rw⁻ 0 (q82 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 2 (q312 c4) ∷
   rw 3 (q45 c4) ∷
   rw 1 (q313 c4) ∷
   rw 4 (q85 c4) ∷
   rw 3 (q42 c4) ∷
   rw 2 (q42 c4) ∷
   rw 3 (q86 c4) ∷
   rw 0 (q312 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q314 : Ws → Eqn
  q314 c4 = eqn (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (lem-VPQ-at12243143 c4)

-- QVQ @12243143: 3 steps
lem-QVQ-at12243143 : Ws → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at12243143 c4 = derive (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q314 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q315 : Ws → Eqn
  q315 c4 = eqn (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) (Bx0-4321 ∷ []) (lem-SWbc-box-at14233241 c4)
  q316 : Ws → Eqn
  q316 c4 = eqn (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) (Bx0-4231 ∷ []) (lem-nat-SWbc-at14233241 c4)

-- sym-bc @14233241: 2 steps
lem-sym-bc-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-sym-bc-at14233241 c4 = derive (Bx0-4321 ∷ []) (Bx0-4231 ∷ [])
  (rw⁻ 0 (q315 c4) ∷
   rw 0 (q316 c4) ∷ []) Eq.refl

private
  q317 : Ws → Eqn
  q317 c4 = eqn (CX21 ∷ Bx3-4210 ∷ CX21 ∷ []) (Bx3-4210 ∷ CCZ024 ∷ []) (lem-CXbc-box-at03143140 c4)
  q318 : Ws → Eqn
  q318 c4 = eqn (CCZ024 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp 653 c4)
  q319 : Ws → Eqn
  q319 c4 = eqn (CX12 ∷ Bx3-4210 ∷ CX12 ∷ []) (Bx3-4210 ∷ CCZ014 ∷ []) (lem-CXcb-box-at03143140 c4)
  q320 : Ws → Eqn
  q320 c4 = eqn (CCZ024 ∷ CX21 ∷ []) (CX21 ∷ CCZ024 ∷ []) (wp 749 c4)
  q321 : Ws → Eqn
  q321 c4 = eqn (CCZ014 ∷ CX21 ∷ []) (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp 899 c4)
  q322 : Ws → Eqn
  q322 c4 = eqn (CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ []) (wp 991 c4)

-- SWbc-box @03143140: 11 steps
lem-SWbc-box-at03143140 : Ws → ⟪ (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-SWbc-box-at03143140 c4 = derive (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) (Bx3-4210 ∷ [])
  (rw⁻ 0 (q211 c4) ∷
   rw⁻ 4 (q211 c4) ∷
   rw 2 (q317 c4) ∷
   rw 3 (q318 c4) ∷
   rw 1 (q319 c4) ∷
   rw 4 (q320 c4) ∷
   rw 3 (q321 c4) ∷
   rw 2 (q321 c4) ∷
   rw 3 (q322 c4) ∷
   rw 0 (q317 c4) ∷
   rw 1 (q31 c4) ∷ []) Eq.refl

private
  q323 : Ws → Eqn
  q323 c4 = eqn (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (lem-VPQ-at0314213240 c4)

-- QVQ @0314213240: 3 steps
lem-QVQ-at0314213240 : Ws → ⟪ (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-QVQ-at0314213240 c4 = derive (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ [])
  (rw⁻ 0 (q205 c4) ∷
   rw⁻ 1 (q323 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q324 : Ws → Eqn
  q324 c4 = eqn (CX12 ∷ Bx3-4120 ∷ CX12 ∷ []) (Bx3-4120 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0314213240 c4)
  q325 : Ws → Eqn
  q325 c4 = eqn (CX21 ∷ Bx3-4120 ∷ CX21 ∷ []) (Bx3-4120 ∷ CCZ024 ∷ []) (lem-CXcb-box-at0314213240 c4)
  q326 : Ws → Eqn
  q326 c4 = eqn (CCZ014 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ []) (wp 54 c4)
  q327 : Ws → Eqn
  q327 c4 = eqn (CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) (wp 900 c4)

-- SWbc-box @0314213240: 11 steps
lem-SWbc-box-at0314213240 : Ws → ⟪ (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-SWbc-box-at0314213240 c4 = derive (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) (Bx3-4120 ∷ [])
  (rw⁻ 0 (q152 c4) ∷
   rw⁻ 4 (q152 c4) ∷
   rw 2 (q324 c4) ∷
   rw 3 (q321 c4) ∷
   rw 1 (q325 c4) ∷
   rw 4 (q326 c4) ∷
   rw 3 (q318 c4) ∷
   rw 2 (q318 c4) ∷
   rw 3 (q327 c4) ∷
   rw 0 (q324 c4) ∷
   rw 1 (q36 c4) ∷ []) Eq.refl

private
  q328 : Ws → Eqn
  q328 c4 = eqn (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (lem-VPQ-at03143140 c4)

-- QVQ @03143140: 3 steps
lem-QVQ-at03143140 : Ws → ⟪ (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-QVQ-at03143140 c4 = derive (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q92 c4) ∷
   rw⁻ 1 (q328 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q329 : Ws → Eqn
  q329 c4 = eqn (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (lem-VPQ-at03243240 c4)

-- QVQ @03243240: 3 steps
lem-QVQ-at03243240 : Ws → ⟪ (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-QVQ-at03243240 c4 = derive (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ [])
  (rw⁻ 0 (q205 c4) ∷
   rw⁻ 1 (q329 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q330 : Ws → Eqn
  q330 c4 = eqn (CX24 ∷ Bx3-1240 ∷ CX24 ∷ []) (Bx3-1240 ∷ CCZ012 ∷ []) (lem-CXbc-box-at033440 c4)
  q331 : Ws → Eqn
  q331 c4 = eqn (CCZ012 ∷ CX42 ∷ []) (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp 1022 c4)
  q332 : Ws → Eqn
  q332 c4 = eqn (CX42 ∷ Bx3-1240 ∷ CX42 ∷ []) (Bx3-1240 ∷ CCZ014 ∷ []) (lem-CXcb-box-at033440 c4)
  q333 : Ws → Eqn
  q333 c4 = eqn (CCZ012 ∷ CX24 ∷ []) (CX24 ∷ CCZ012 ∷ []) (wp 170 c4)
  q334 : Ws → Eqn
  q334 c4 = eqn (CCZ014 ∷ CX24 ∷ []) (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp 1023 c4)
  q335 : Ws → Eqn
  q335 c4 = eqn (CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) (wp 1024 c4)

-- SWbc-box @033440: 11 steps
lem-SWbc-box-at033440 : Ws → ⟪ (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-SWbc-box-at033440 c4 = derive (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) (Bx3-1240 ∷ [])
  (rw⁻ 0 (q68 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 2 (q330 c4) ∷
   rw 3 (q331 c4) ∷
   rw 1 (q332 c4) ∷
   rw 4 (q333 c4) ∷
   rw 3 (q334 c4) ∷
   rw 2 (q334 c4) ∷
   rw 3 (q335 c4) ∷
   rw 0 (q330 c4) ∷
   rw 1 (q229 c4) ∷ []) Eq.refl

private
  q336 : Ws → Eqn
  q336 c4 = eqn (CX42 ∷ Bx3-1420 ∷ CX42 ∷ []) (Bx3-1420 ∷ CCZ014 ∷ []) (lem-CXbc-box-at03243240 c4)
  q337 : Ws → Eqn
  q337 c4 = eqn (CX24 ∷ Bx3-1420 ∷ CX24 ∷ []) (Bx3-1420 ∷ CCZ012 ∷ []) (lem-CXcb-box-at03243240 c4)
  q338 : Ws → Eqn
  q338 c4 = eqn (CCZ014 ∷ CX42 ∷ []) (CX42 ∷ CCZ014 ∷ []) (wp 269 c4)
  q339 : Ws → Eqn
  q339 c4 = eqn (CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) (wp 1032 c4)

-- SWbc-box @03243240: 11 steps
lem-SWbc-box-at03243240 : Ws → ⟪ (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-SWbc-box-at03243240 c4 = derive (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) (Bx3-1420 ∷ [])
  (rw⁻ 0 (q169 c4) ∷
   rw⁻ 4 (q169 c4) ∷
   rw 2 (q336 c4) ∷
   rw 3 (q334 c4) ∷
   rw 1 (q337 c4) ∷
   rw 4 (q338 c4) ∷
   rw 3 (q331 c4) ∷
   rw 2 (q331 c4) ∷
   rw 3 (q339 c4) ∷
   rw 0 (q336 c4) ∷
   rw 1 (q36 c4) ∷ []) Eq.refl

private
  q340 : Ws → Eqn
  q340 c4 = eqn (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (lem-VPQ-at033440 c4)

-- QVQ @033440: 3 steps
lem-QVQ-at033440 : Ws → ⟪ (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-QVQ-at033440 c4 = derive (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ [])
  (rw⁻ 0 (q110 c4) ∷
   rw⁻ 1 (q340 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q341 : Ws → Eqn
  q341 c4 = eqn (CX24 ∷ Bx3-0241 ∷ CX24 ∷ []) (Bx3-0241 ∷ CCZ012 ∷ []) (lem-CXbc-box-at03103441 c4)
  q342 : Ws → Eqn
  q342 c4 = eqn (CX42 ∷ Bx3-0241 ∷ CX42 ∷ []) (Bx3-0241 ∷ CCZ014 ∷ []) (lem-CXcb-box-at03103441 c4)

-- SWbc-box @03103441: 11 steps
lem-SWbc-box-at03103441 : Ws → ⟪ (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-SWbc-box-at03103441 c4 = derive (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) (Bx3-0241 ∷ [])
  (rw⁻ 0 (q68 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 2 (q341 c4) ∷
   rw 3 (q331 c4) ∷
   rw 1 (q342 c4) ∷
   rw 4 (q333 c4) ∷
   rw 3 (q334 c4) ∷
   rw 2 (q334 c4) ∷
   rw 3 (q335 c4) ∷
   rw 0 (q341 c4) ∷
   rw 1 (q229 c4) ∷ []) Eq.refl

private
  q343 : Ws → Eqn
  q343 c4 = eqn (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (lem-VPQ-at0310243241 c4)

-- QVQ @0310243241: 3 steps
lem-QVQ-at0310243241 : Ws → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0310243241 c4 = derive (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw⁻ 1 (q343 c4) ∷
   rw 4 (q6 c4) ∷ []) Eq.refl

private
  q344 : Ws → Eqn
  q344 c4 = eqn (CX42 ∷ Bx3-0421 ∷ CX42 ∷ []) (Bx3-0421 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0310243241 c4)
  q345 : Ws → Eqn
  q345 c4 = eqn (CX24 ∷ Bx3-0421 ∷ CX24 ∷ []) (Bx3-0421 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0310243241 c4)

-- SWbc-box @0310243241: 11 steps
lem-SWbc-box-at0310243241 : Ws → ⟪ (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-SWbc-box-at0310243241 c4 = derive (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) (Bx3-0421 ∷ [])
  (rw⁻ 0 (q169 c4) ∷
   rw⁻ 4 (q169 c4) ∷
   rw 2 (q344 c4) ∷
   rw 3 (q334 c4) ∷
   rw 1 (q345 c4) ∷
   rw 4 (q338 c4) ∷
   rw 3 (q331 c4) ∷
   rw 2 (q331 c4) ∷
   rw 3 (q339 c4) ∷
   rw 0 (q344 c4) ∷
   rw 1 (q36 c4) ∷ []) Eq.refl

private
  q346 : Ws → Eqn
  q346 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl 788 (lit c4))
  q347 : Ws → Eqn
  q347 c4 = eqn (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (lem-VPQ-at03103441 c4)

-- QVQ @03103441: 3 steps
lem-QVQ-at03103441 : Ws → ⟪ (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-QVQ-at03103441 c4 = derive (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ [])
  (rw⁻ 0 (q346 c4) ∷
   rw⁻ 1 (q347 c4) ∷
   rw 4 (q67 c4) ∷ []) Eq.refl

private
  q348 : Ws → Eqn
  q348 c4 = eqn (CX41 ∷ Bx3-0412 ∷ CX41 ∷ []) (Bx3-0412 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0310243142 c4)
  q349 : Ws → Eqn
  q349 c4 = eqn (CX14 ∷ Bx3-0412 ∷ CX14 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0310243142 c4)

-- SWbc-box @0310243142: 11 steps
lem-SWbc-box-at0310243142 : Ws → ⟪ (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-SWbc-box-at0310243142 c4 = derive (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) (Bx3-0412 ∷ [])
  (rw⁻ 0 (q40 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 2 (q348 c4) ∷
   rw 3 (q220 c4) ∷
   rw 1 (q349 c4) ∷
   rw 4 (q222 c4) ∷
   rw 3 (q223 c4) ∷
   rw 2 (q223 c4) ∷
   rw 3 (q224 c4) ∷
   rw 0 (q348 c4) ∷
   rw 1 (q31 c4) ∷ []) Eq.refl

private
  q350 : Ws → Eqn
  q350 c4 = eqn (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) (Bx3-0142 ∷ []) (lem-SWbc-box-at0310213442 c4)
  q351 : Ws → Eqn
  q351 c4 = eqn (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) (Bx3-0412 ∷ []) (lem-nat-SWbc-at0310213442 c4)

-- sym-bc @0310213442: 2 steps
lem-sym-bc-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym-bc-at0310213442 c4 = derive (Bx3-0142 ∷ []) (Bx3-0412 ∷ [])
  (rw⁻ 0 (q350 c4) ∷
   rw 0 (q351 c4) ∷ []) Eq.refl

private
  q352 : Ws → Eqn
  q352 c4 = eqn (CX04 ∷ CX40 ∷ CX04 ∷ []) (Sw04 ∷ []) (wp 1084 c4)
  q353 : Ws → Eqn
  q353 c4 = eqn (CX04 ∷ Bx3-2041 ∷ CX04 ∷ []) (Bx3-2041 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0312203441 c4)
  q354 : Ws → Eqn
  q354 c4 = eqn (CCZ012 ∷ CX40 ∷ []) (CX40 ∷ CCZ124 ∷ CCZ012 ∷ []) (wp 1085 c4)
  q355 : Ws → Eqn
  q355 c4 = eqn (CX40 ∷ Bx3-2041 ∷ CX40 ∷ []) (Bx3-2041 ∷ CCZ124 ∷ []) (lem-CXcb-box-at0312203441 c4)
  q356 : Ws → Eqn
  q356 c4 = eqn (CCZ012 ∷ CX04 ∷ []) (CX04 ∷ CCZ012 ∷ []) (wp 1086 c4)
  q357 : Ws → Eqn
  q357 c4 = eqn (CCZ124 ∷ CX04 ∷ []) (CX04 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp 1087 c4)
  q358 : Ws → Eqn
  q358 c4 = eqn (CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) (wp 1088 c4)

-- SWbc-box @0312203441: 11 steps
lem-SWbc-box-at0312203441 : Ws → ⟪ (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-SWbc-box-at0312203441 c4 = derive (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) (Bx3-2041 ∷ [])
  (rw⁻ 0 (q352 c4) ∷
   rw⁻ 4 (q352 c4) ∷
   rw 2 (q353 c4) ∷
   rw 3 (q354 c4) ∷
   rw 1 (q355 c4) ∷
   rw 4 (q356 c4) ∷
   rw 3 (q357 c4) ∷
   rw 2 (q357 c4) ∷
   rw 3 (q358 c4) ∷
   rw 0 (q353 c4) ∷
   rw 1 (q229 c4) ∷ []) Eq.refl

private
  q359 : Ws → Eqn
  q359 c4 = eqn (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (lem-VPQ-at0312243041 c4)

-- QVQ @0312243041: 3 steps
lem-QVQ-at0312243041 : Ws → ⟪ (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-QVQ-at0312243041 c4 = derive (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q92 c4) ∷
   rw⁻ 1 (q359 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q360 : Ws → Eqn
  q360 c4 = eqn (CX40 ∷ CX04 ∷ CX40 ∷ []) (Sw04 ∷ []) (wp 1101 c4)
  q361 : Ws → Eqn
  q361 c4 = eqn (CX40 ∷ Bx3-2401 ∷ CX40 ∷ []) (Bx3-2401 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0312243041 c4)
  q362 : Ws → Eqn
  q362 c4 = eqn (CX04 ∷ Bx3-2401 ∷ CX04 ∷ []) (Bx3-2401 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0312243041 c4)
  q363 : Ws → Eqn
  q363 c4 = eqn (CCZ124 ∷ CX40 ∷ []) (CX40 ∷ CCZ124 ∷ []) (wp 321 c4)
  q364 : Ws → Eqn
  q364 c4 = eqn (CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) (wp 1102 c4)

-- SWbc-box @0312243041: 11 steps
lem-SWbc-box-at0312243041 : Ws → ⟪ (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-SWbc-box-at0312243041 c4 = derive (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) (Bx3-2401 ∷ [])
  (rw⁻ 0 (q360 c4) ∷
   rw⁻ 4 (q360 c4) ∷
   rw 2 (q361 c4) ∷
   rw 3 (q357 c4) ∷
   rw 1 (q362 c4) ∷
   rw 4 (q363 c4) ∷
   rw 3 (q354 c4) ∷
   rw 2 (q354 c4) ∷
   rw 3 (q364 c4) ∷
   rw 0 (q361 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q365 : Ws → Eqn
  q365 c4 = eqn (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (lem-VPQ-at0312203441 c4)

-- QVQ @0312203441: 3 steps
lem-QVQ-at0312203441 : Ws → ⟪ (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-QVQ-at0312203441 c4 = derive (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ [])
  (rw⁻ 0 (q346 c4) ∷
   rw⁻ 1 (q365 c4) ∷
   rw 4 (q67 c4) ∷ []) Eq.refl

private
  q366 : Ws → Eqn
  q366 c4 = eqn (CX24 ∷ Bx0-1243 ∷ CX24 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ []) (lem-CXbc-box-at3443 c4)
  q367 : Ws → Eqn
  q367 c4 = eqn (CX42 ∷ Bx0-1243 ∷ CX42 ∷ []) (Bx0-1243 ∷ CCZ134 ∷ []) (lem-CXcb-box-at3443 c4)

-- SWbc-box @3443: 11 steps
lem-SWbc-box-at3443 : Ws → ⟪ (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-SWbc-box-at3443 c4 = derive (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) (Bx0-1243 ∷ [])
  (rw⁻ 0 (q68 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 2 (q366 c4) ∷
   rw 3 (q70 c4) ∷
   rw 1 (q367 c4) ∷
   rw 4 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw 2 (q73 c4) ∷
   rw 3 (q74 c4) ∷
   rw 0 (q366 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q368 : Ws → Eqn
  q368 c4 = eqn (CX21 ∷ Bx3-0214 ∷ CX21 ∷ []) (Bx3-0214 ∷ CCZ024 ∷ []) (lem-CXbc-box-at031031 c4)
  q369 : Ws → Eqn
  q369 c4 = eqn (CX12 ∷ Bx3-0214 ∷ CX12 ∷ []) (Bx3-0214 ∷ CCZ014 ∷ []) (lem-CXcb-box-at031031 c4)

-- SWbc-box @031031: 11 steps
lem-SWbc-box-at031031 : Ws → ⟪ (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-SWbc-box-at031031 c4 = derive (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) (Bx3-0214 ∷ [])
  (rw⁻ 0 (q211 c4) ∷
   rw⁻ 4 (q211 c4) ∷
   rw 2 (q368 c4) ∷
   rw 3 (q318 c4) ∷
   rw 1 (q369 c4) ∷
   rw 4 (q320 c4) ∷
   rw 3 (q321 c4) ∷
   rw 2 (q321 c4) ∷
   rw 3 (q322 c4) ∷
   rw 0 (q368 c4) ∷
   rw 1 (q31 c4) ∷ []) Eq.refl

private
  q370 : Ws → Eqn
  q370 c4 = eqn (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (lem-VPQ-at031031 c4)

-- QVQ @031031: 3 steps
lem-QVQ-at031031 : Ws → ⟪ (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-QVQ-at031031 c4 = derive (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ [])
  (rw⁻ 0 (q346 c4) ∷
   rw⁻ 1 (q370 c4) ∷
   rw 4 (q67 c4) ∷ []) Eq.refl

private
  q371 : Ws → Eqn
  q371 c4 = eqn (CX20 ∷ Bx3-4201 ∷ CX20 ∷ []) (Bx3-4201 ∷ CCZ124 ∷ []) (lem-CXbc-box-at03143041 c4)
  q372 : Ws → Eqn
  q372 c4 = eqn (CX02 ∷ Bx3-4201 ∷ CX02 ∷ []) (Bx3-4201 ∷ CCZ014 ∷ []) (lem-CXcb-box-at03143041 c4)

-- SWbc-box @03143041: 11 steps
lem-SWbc-box-at03143041 : Ws → ⟪ (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-SWbc-box-at03143041 c4 = derive (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) (Bx3-4201 ∷ [])
  (rw⁻ 0 (q100 c4) ∷
   rw⁻ 4 (q100 c4) ∷
   rw 2 (q371 c4) ∷
   rw 3 (q120 c4) ∷
   rw 1 (q372 c4) ∷
   rw 4 (q122 c4) ∷
   rw 3 (q123 c4) ∷
   rw 2 (q123 c4) ∷
   rw 3 (q124 c4) ∷
   rw 0 (q371 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q373 : Ws → Eqn
  q373 c4 = eqn (CX03 ∷ CX30 ∷ CX03 ∷ []) (Sw03 ∷ []) (wl 961 (lit c4))
  q374 : Ws → Eqn
  q374 c4 = eqn (CX03 ∷ Bx2-4031 ∷ CX03 ∷ []) (Bx2-4031 ∷ CCZ014 ∷ []) (lem-CXbc-box-at02142041 c4)
  q375 : Ws → Eqn
  q375 c4 = eqn (CX30 ∷ Bx2-4031 ∷ CX30 ∷ []) (Bx2-4031 ∷ CCZ134 ∷ []) (lem-CXcb-box-at02142041 c4)
  q376 : Ws → Eqn
  q376 c4 = eqn (CCZ014 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ []) (wp 778 c4)
  q377 : Ws → Eqn
  q377 c4 = eqn (CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) (wp 779 c4)

-- SWbc-box @02142041: 11 steps
lem-SWbc-box-at02142041 : Ws → ⟪ (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-SWbc-box-at02142041 c4 = derive (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) (Bx2-4031 ∷ [])
  (rw⁻ 0 (q373 c4) ∷
   rw⁻ 4 (q373 c4) ∷
   rw 2 (q374 c4) ∷
   rw 3 (q238 c4) ∷
   rw 1 (q375 c4) ∷
   rw 4 (q376 c4) ∷
   rw 3 (q235 c4) ∷
   rw 2 (q235 c4) ∷
   rw 3 (q377 c4) ∷
   rw 0 (q374 c4) ∷
   rw 1 (q36 c4) ∷ []) Eq.refl
