{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D016 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-nat-SWbc-at0214203143 ; lem-nat-SWbc-at0214213043 ; lem-nat-SWbc-at0314203142 ; lem-nat-SWbc-at0314213042 ; lem-nat-SWbc-at122441 ; lem-nat-SWbc-at132132 ; lem-nat-SWbc-at1331 ; lem-nat-SWbc-at14213243 ; lem-sym-ab-at03102132 ; lem-sym-ab-at0410213243)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-nat-SWbc-at0210233441 ; lem-nat-SWbc-at02102441 ; lem-nat-SWbc-at02132031 ; lem-nat-SWbc-at02132130 ; lem-nat-SWbc-at02233440 ; lem-nat-SWbc-at022440 ; lem-nat-SWbc-at0310243241 ; lem-nat-SWbc-at03103441 ; lem-nat-SWbc-at03122031 ; lem-nat-SWbc-at03122130 ; lem-nat-SWbc-at03243240 ; lem-nat-SWbc-at033440 ; lem-nat-SWbc-at12233441 ; lem-nat-SWbc-at143143 ; lem-nat-SWbc-at233442 ; lem-nat-SWbc-at2442 ; lem-sym-ab-at0213243041)
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-box-tQ-at0210213443 ; lem-box-tQ-at0213243140 ; lem-box-tQ-at0220 ; lem-nat-SWbc ; lem-nat-SWbc-at0210243143 ; lem-nat-SWbc-at0213213440 ; lem-nat-SWbc-at0312213440 ; lem-nat-SWbc-at0312243140 ; lem-nat-SWbc-at0330 ; lem-nat-SWbc-at043043 ; lem-nat-SWbc-at1221 ; lem-nat-SWbc-at122331 ; lem-nat-SWbc-at12243143 ; lem-nat-SWbc-at13213442 ; lem-nat-SWbc-at133441 ; lem-nat-SWbc-at1441 ; lem-nat-SWbc-at2332 ; lem-nat-SWbc-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-box-tQ-at021021 ; lem-box-tQ-at0213243041 ; lem-box-tQ-at0214233041 ; lem-nat-SWbc-at0310243142 ; lem-nat-SWbc-at031031 ; lem-nat-SWbc-at0312203441 ; lem-nat-SWbc-at0312243041 ; lem-nat-SWbc-at0314203241 ; lem-nat-SWbc-at0314213240 ; lem-nat-SWbc-at03143041 ; lem-nat-SWbc-at03143140 ; lem-nat-SWbc-at12213443 ; lem-nat-SWbc-at3443)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-P-box-at0220 ; lem-P-box-at032032 ; lem-P-box-at13243142 ; lem-P-box-at13243241 ; lem-P-box-at14233142 ; lem-P-box-at14233241 ; lem-box-tQ ; lem-box-tQ-at0312243140 ; lem-box-tQ-at1221 ; lem-box-tQ-at12213443 ; lem-box-tQ-at3443 ; lem-nat-SWbc-at022330 ; lem-tP ; lem-tP-at0110 ; lem-tP-at0210233441 ; lem-tP-at0210243143 ; lem-tP-at0213203441 ; lem-tP-at0214213043 ; lem-tP-at0310243142 ; lem-tP-at0312243140 ; lem-tP-at0314203142 ; lem-tP-at0314213042 ; lem-tP-at0330 ; lem-tP-at043043 ; lem-tP-at1221 ; lem-tP-at12213443 ; lem-tP-at122331 ; lem-tP-at12233441 ; lem-tP-at122441 ; lem-tP-at132132 ; lem-tP-at13213442 ; lem-tP-at1331 ; lem-tP-at143143 ; lem-tP-at2332 ; lem-tP-at233442 ; lem-tP-at243243 ; lem-tP-at3443)
open import Examples.Groups.Clifford+CS.FiveV.D.D007 using (lem-P-box-at021021 ; lem-P-box-at0210213443 ; lem-P-box-at0213243041 ; lem-P-box-at0213243140 ; lem-P-box-at0214233041 ; lem-P-box-at03102132 ; lem-P-box-at0310213442 ; lem-box-tQ-at0312243041 ; lem-box-tQ-at03143041 ; lem-nat-SWbc-at02142041 ; lem-tP-at02102441 ; lem-tP-at02132031 ; lem-tP-at02132130 ; lem-tP-at0214203143 ; lem-tP-at022330 ; lem-tP-at02233440 ; lem-tP-at022440 ; lem-tP-at0310243241 ; lem-tP-at031031 ; lem-tP-at03103441 ; lem-tP-at03122031 ; lem-tP-at0312203441 ; lem-tP-at03122130 ; lem-tP-at0312243041 ; lem-tP-at0314213240 ; lem-tP-at03143041 ; lem-tP-at03143140 ; lem-tP-at03243240 ; lem-tP-at033440 ; lem-tP-at12243143 ; lem-tP-at14213243 ; lem-tP-at1441 ; lem-tP-at2442)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-QVQ ; lem-QVQ-at0110 ; lem-QVQ-at0210233441 ; lem-QVQ-at0210243143 ; lem-QVQ-at02102441 ; lem-QVQ-at0213203441 ; lem-QVQ-at0214203143 ; lem-QVQ-at0214213043 ; lem-QVQ-at022330 ; lem-QVQ-at02233440 ; lem-QVQ-at022440 ; lem-QVQ-at0310243142 ; lem-QVQ-at0310243241 ; lem-QVQ-at031031 ; lem-QVQ-at03103441 ; lem-QVQ-at0312203441 ; lem-QVQ-at0312243041 ; lem-QVQ-at0312243140 ; lem-QVQ-at0314203142 ; lem-QVQ-at0314213042 ; lem-QVQ-at0314213240 ; lem-QVQ-at03143140 ; lem-QVQ-at03243240 ; lem-QVQ-at0330 ; lem-QVQ-at033440 ; lem-QVQ-at043043 ; lem-QVQ-at1221 ; lem-QVQ-at12213443 ; lem-QVQ-at122331 ; lem-QVQ-at12233441 ; lem-QVQ-at12243143 ; lem-QVQ-at122441 ; lem-QVQ-at132132 ; lem-QVQ-at13213442 ; lem-QVQ-at1331 ; lem-QVQ-at14213243 ; lem-QVQ-at143143 ; lem-QVQ-at1441 ; lem-QVQ-at2332 ; lem-QVQ-at233442 ; lem-QVQ-at243243 ; lem-QVQ-at2442 ; lem-QVQ-at3443 ; lem-SWbc-box ; lem-SWbc-box-at0210233441 ; lem-SWbc-box-at0210243143 ; lem-SWbc-box-at02102441 ; lem-SWbc-box-at0213213440 ; lem-SWbc-box-at0214203143 ; lem-SWbc-box-at02142041 ; lem-SWbc-box-at0214213043 ; lem-SWbc-box-at022330 ; lem-SWbc-box-at02233440 ; lem-SWbc-box-at022440 ; lem-SWbc-box-at0310243142 ; lem-SWbc-box-at0310243241 ; lem-SWbc-box-at031031 ; lem-SWbc-box-at03103441 ; lem-SWbc-box-at0312203441 ; lem-SWbc-box-at0312213440 ; lem-SWbc-box-at0312243041 ; lem-SWbc-box-at0312243140 ; lem-SWbc-box-at0314203142 ; lem-SWbc-box-at0314213042 ; lem-SWbc-box-at0314213240 ; lem-SWbc-box-at03143041 ; lem-SWbc-box-at03143140 ; lem-SWbc-box-at03243240 ; lem-SWbc-box-at0330 ; lem-SWbc-box-at033440 ; lem-SWbc-box-at043043 ; lem-SWbc-box-at1221 ; lem-SWbc-box-at12213443 ; lem-SWbc-box-at122331 ; lem-SWbc-box-at12233441 ; lem-SWbc-box-at12243143 ; lem-SWbc-box-at122441 ; lem-SWbc-box-at132132 ; lem-SWbc-box-at13213442 ; lem-SWbc-box-at1331 ; lem-SWbc-box-at133441 ; lem-SWbc-box-at14213243 ; lem-SWbc-box-at143143 ; lem-SWbc-box-at1441 ; lem-SWbc-box-at2332 ; lem-SWbc-box-at233442 ; lem-SWbc-box-at243243 ; lem-SWbc-box-at2442 ; lem-SWbc-box-at3443 ; lem-XCSX-box-2-at0210243143 ; lem-XCSX-box-2-at122441 ; lem-XCSX-box-2-at243243 ; lem-box-cP-at021021 ; lem-box-cP-at0210213443 ; lem-box-cP-at0213243140 ; lem-box-cP-at0220 ; lem-box-cP-at03102132 ; lem-box-cP-at032032 ; lem-box-cP-at0410213243 ; lem-box-cP-at13243142 ; lem-box-cP-at13243241 ; lem-box-cP-at14233142 ; lem-box-cP-at14233241 ; lem-sym-bc-at03102132 ; lem-sym-bc-at0310213442 ; lem-sym-bc-at032032 ; lem-sym-bc-at04203243 ; lem-sym-bc-at13243142)
open import Examples.Groups.Clifford+CS.FiveV.D.D015 using (lem-QVQ-at02132031 ; lem-QVQ-at02132130 ; lem-QVQ-at03122031 ; lem-QVQ-at03122130 ; lem-QVQ-at03143041 ; lem-SWbc-box-at02132031 ; lem-SWbc-box-at02132130 ; lem-SWbc-box-at03122031 ; lem-SWbc-box-at03122130 ; lem-SWbc-box-at0314203241 ; lem-box-cP-at0213243041 ; lem-box-cP-at0214233041 ; lem-box-cP-at0310213442 ; lem-sym-bc-at0214233041)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CS12-CCZ034 ; lem-comm-CS23-CCZ014 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX12-CCZ034)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) (wp 8 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ []) (lem-tP c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wl 162 (lit c4))

-- box-cP: 12 steps
lem-box-cP : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP c4 = derive (Bx0-1234 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q1 c4) ∷
   re 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 2 (q4 c4) ∷ []) Eq.refl

private
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ123 ∷ []) (wl 182 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-QVQ-at0210243143 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0210243143 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp 19 c4)

-- box-cP @0210243143: 12 steps
lem-box-cP-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-box-cP-at0210243143 c4 = derive (Bx2-0413 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw 2 (q5 c4) ∷
   re 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw 5 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

private
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ023 ∷ []) (wl 205 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-QVQ-at243243 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ []) (lem-tP-at243243 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Toff014 ∷ Toff014 ∷ []) [] (wp 51 c4)

-- box-cP @243243: 12 steps
lem-box-cP-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at243243 c4 = derive (Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ013 ∷ []) (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (wl 231 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at122441 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ []) (lem-tP-at122441 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Toff024 ∷ Toff024 ∷ []) [] (wp 80 c4)

-- box-cP @122441: 12 steps
lem-box-cP-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at122441 c4 = derive (Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q13 c4) ∷
   re 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 2 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 2 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (Bx0-1234 ∷ []) (lem-SWbc-box c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (Bx0-1324 ∷ []) (lem-nat-SWbc c4)

-- sym-bc: 2 steps
lem-sym-bc : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym-bc c4 = derive (Bx0-1234 ∷ []) (Bx0-1324 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 0 (q18 c4) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) (Bx0-2134 ∷ []) (lem-SWbc-box-at1221 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) (Bx0-2314 ∷ []) (lem-nat-SWbc-at1221 c4)

-- sym-bc @1221: 2 steps
lem-sym-bc-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym-bc-at1221 c4 = derive (Bx0-2134 ∷ []) (Bx0-2314 ∷ [])
  (rw⁻ 0 (q19 c4) ∷
   rw 0 (q20 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ034 ∷ []) (wp 111 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ-at1221 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ []) (lem-tP-at1221 c4)

-- box-cP @1221: 12 steps
lem-box-cP-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP-at1221 c4 = derive (Bx0-2134 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw 2 (q21 c4) ∷
   re 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw 5 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 2 (q4 c4) ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) (wp 130 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at2332 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ []) (lem-tP-at2332 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Toff013 ∷ Toff013 ∷ []) [] (wl 229 (lit c4))

-- box-cP @2332: 12 steps
lem-box-cP-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at2332 c4 = derive (Bx0-1324 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q24 c4) ∷
   re 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q24 c4) ∷
   rw 2 (q25 c4) ∷
   rw 1 (q26 c4) ∷
   rw 2 (q27 c4) ∷ []) Eq.refl

private
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ014 ∷ []) (wp 153 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-QVQ-at122331 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ []) (lem-tP-at122331 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Toff023 ∷ Toff023 ∷ []) [] (wl 203 (lit c4))

-- box-cP @122331: 12 steps
lem-box-cP-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-box-cP-at122331 c4 = derive (Bx0-2314 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw 2 (q28 c4) ∷
   re 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw 5 (q28 c4) ∷
   rw 2 (q29 c4) ∷
   rw 1 (q30 c4) ∷
   rw 2 (q31 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ024 ∷ []) (wp 131 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at132132 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ []) (lem-tP-at132132 c4)

-- box-cP @132132: 12 steps
lem-box-cP-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at132132 c4 = derive (Bx0-3124 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw 2 (q32 c4) ∷
   re 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw 5 (q32 c4) ∷
   rw 2 (q33 c4) ∷
   rw 1 (q34 c4) ∷
   rw 2 (q27 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) (Bx0-2413 ∷ []) (lem-SWbc-box-at12243143 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) (Bx0-2143 ∷ []) (lem-nat-SWbc-at12243143 c4)

-- sym-bc @12243143: 2 steps
lem-sym-bc-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-sym-bc-at12243143 c4 = derive (Bx0-2413 ∷ []) (Bx0-2143 ∷ [])
  (rw⁻ 0 (q35 c4) ∷
   rw 0 (q36 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = eqn (Toff012 ∷ Bx0-4312 ∷ Toff012 ∷ []) (Bx0-4312 ∷ []) (lem-P-box-at14233142 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx0-4312 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at14233142 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx0-1243 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4)

-- pairs @14233142: 4 steps
lem-pairs-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-pairs-at14233142 c4 = derive (Bx0-4312 ∷ []) (Bx0-1243 ∷ [])
  (rw⁻ 0 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 0 (q39 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ024 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (wp 211 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at13213442 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ []) (lem-tP-at13213442 c4)

-- box-cP @13213442: 12 steps
lem-box-cP-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at13213442 c4 = derive (Bx0-3142 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw⁻ 2 (q40 c4) ∷
   re 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw⁻ 5 (q40 c4) ∷
   rw 2 (q41 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q27 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ014 ∷ []) (wp 154 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-QVQ-at1331 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ []) (lem-tP-at1331 c4)

-- box-cP @1331: 12 steps
lem-box-cP-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-box-cP-at1331 c4 = derive (Bx0-3214 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw 2 (q43 c4) ∷
   re 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw 5 (q43 c4) ∷
   rw 2 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q31 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (CCZ134 ∷ []) (wp 262 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ134 ∷ []) (Toff134 ∷ Toff102 ∷ CCZ012 ∷ Toff134 ∷ []) (lem-QVQ-at0110 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (Toff102 ∷ Toff134 ∷ []) (Toff134 ∷ Toff102 ∷ []) (lem-tP-at0110 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (Toff102 ∷ Toff102 ∷ []) [] (wl 403 (lit c4))

-- box-cP @0110: 12 steps
lem-box-cP-at0110 : Ws → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ []) ⟫ʷ
lem-box-cP-at0110 c4 = derive (Bx1-0234 ∷ []) (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw 2 (q46 c4) ∷
   re 5 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw 5 (q46 c4) ∷
   rw 2 (q47 c4) ∷
   rw 1 (q48 c4) ∷
   rw 2 (q49 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = eqn (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) (Bx0-3241 ∷ []) (lem-SWbc-box-at133441 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) (Bx0-3421 ∷ []) (lem-nat-SWbc-at133441 c4)

-- sym-bc @133441: 2 steps
lem-sym-bc-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-sym-bc-at133441 c4 = derive (Bx0-3241 ∷ []) (Bx0-3421 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (Toff012 ∷ Bx0-3421 ∷ Toff012 ∷ []) (Bx0-3421 ∷ []) (lem-P-box-at13243241 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Bx0-3421 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at13243241 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx0-2134 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at1221 c4)

-- pairs @13243241: 4 steps
lem-pairs-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-pairs-at13243241 c4 = derive (Bx0-3421 ∷ []) (Bx0-2134 ∷ [])
  (rw⁻ 0 (q52 c4) ∷
   rw 1 (q53 c4) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 0 (q54 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = eqn (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) (Bx0-3142 ∷ []) (lem-SWbc-box-at13213442 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) (Bx0-3412 ∷ []) (lem-nat-SWbc-at13213442 c4)

-- sym-bc @13213442: 2 steps
lem-sym-bc-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-sym-bc-at13213442 c4 = derive (Bx0-3142 ∷ []) (Bx0-3412 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 0 (q56 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (Toff012 ∷ Bx0-3412 ∷ Toff012 ∷ []) (Bx0-3412 ∷ []) (lem-P-box-at13243142 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (Bx0-3412 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at13243142 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4)

-- pairs @13243142: 4 steps
lem-pairs-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-pairs-at13243142 c4 = derive (Bx0-3412 ∷ []) (Bx0-1234 ∷ [])
  (rw⁻ 0 (q57 c4) ∷
   rw 1 (q58 c4) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 0 (q59 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ034 ∷ []) (wp 210 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ-at3443 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ []) (lem-tP-at3443 c4)

-- box-cP @3443: 12 steps
lem-box-cP-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP-at3443 c4 = derive (Bx0-1243 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw 2 (q60 c4) ∷
   re 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw 5 (q60 c4) ∷
   rw 2 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 2 (q4 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx4-0123 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ014 ∷ []) (wp 124 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ CCZ034 ∷ []) (wp 307 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ023 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl 458 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ014 ∷ CS03 ∷ []) (CS03 ∷ CCZ014 ∷ []) (wp 157 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ014 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ []) (wp 308 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (CS23⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (CS23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CCZ023 ∷ CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ034 ∷ []) (wp 309 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (Toff012 ∷ CCZ014 ∷ []) (wp 310 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ124 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl 459 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wl 446 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (K0⁻ ∷ Toff423 ∷ []) (Toff423 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ ↑))
  q76 : Ws → Eqn
  q76 c4 = eqn (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ []) (wp 311 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (CX01 ∷ Toff423 ∷ []) (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ))
  q78 : Ws → Eqn
  q78 c4 = eqn (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) (wl 460 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) (wl 461 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (K0 ∷ Toff423 ∷ []) (Toff423 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ ↑))
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) (wp 66 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl 207 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp 53 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (CCZ014 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ []) (wp 54 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ123 ∷ []) (CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl 462 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ123 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ []) (wl 463 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (CCZ034 ∷ CS13 ∷ []) (CS13 ∷ CCZ034 ∷ []) (wp 312 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ034 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ034 ∷ []) (wp 313 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (CCZ034 ∷ CS23 ∷ []) (CS23 ∷ CCZ034 ∷ []) (wp 314 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (CCZ123 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ123 ∷ []) (wl 464 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl 181 (lit c4))

-- box-box-4: 103 steps
lem-box-box-4 : Ws → ⟪ (Bx0-1234 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-box-box-4 c4 = derive (Bx0-1234 ∷ Bx4-0123 ∷ []) (Bx4-0123 ∷ Bx0-1234 ∷ [])
  (rw 0 (q59 c4) ∷
   rw 4 (q63 c4) ∷
   rw⁻ 3 (q64 c4) ∷
   rw 4 (q65 c4) ∷
   rw⁻ 6 (q64 c4) ∷
   rw 5 (q66 c4) ∷
   rw⁻ 9 (q67 c4) ∷
   rw⁻ 8 (q68 c4) ∷
   rw 7 (q69 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   rw 5 (q70 c4) ∷
   rw⁻ 6 (q66 c4) ∷
   rw 6 (q71 c4) ∷
   rw⁻ 3 (q63 c4) ∷
   rw 3 (q63 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   rw 4 (q73 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   rw 9 (q75 c4) ∷
   rw 8 (q76 c4) ∷
   rw 7 (q77 c4) ∷
   rw 6 (q78 c4) ∷
   rw 5 (q77 c4) ∷
   rw 4 (q79 c4) ∷
   rw 3 (q80 c4) ∷
   rw 4 (q74 c4) ∷
   rw⁻ 6 (q81 c4) ∷
   rw 5 (q82 c4) ∷
   rw⁻ 9 (q83 c4) ∷
   rw⁻ 8 (q84 c4) ∷
   rw 7 (q69 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 5 (q70 c4) ∷
   rw⁻ 6 (q82 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw 6 (q86 c4) ∷
   rw⁻ 5 (q74 c4) ∷
   rw 11 (q75 c4) ∷
   rw 10 (q76 c4) ∷
   rw 9 (q77 c4) ∷
   rw 8 (q78 c4) ∷
   rw 7 (q77 c4) ∷
   rw 6 (q79 c4) ∷
   rw 5 (q80 c4) ∷
   rw 6 (q74 c4) ∷
   rw⁻ 2 (q63 c4) ∷
   rw 2 (q63 c4) ∷
   rw⁻ 1 (q64 c4) ∷
   rw 2 (q65 c4) ∷
   rw⁻ 4 (q64 c4) ∷
   rw 3 (q66 c4) ∷
   rw⁻ 7 (q67 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   rw 5 (q69 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 3 (q70 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   rw 4 (q71 c4) ∷
   rw⁻ 1 (q63 c4) ∷
   rw 1 (q63 c4) ∷
   rw⁻ 0 (q72 c4) ∷
   rw 2 (q73 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   rw 7 (q75 c4) ∷
   rw 6 (q76 c4) ∷
   rw 5 (q77 c4) ∷
   rw 4 (q78 c4) ∷
   rw 3 (q77 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q74 c4) ∷
   rw⁻ 4 (q81 c4) ∷
   rw 3 (q82 c4) ∷
   rw⁻ 7 (q83 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 5 (q69 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw 3 (q70 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   rw⁻ 4 (q85 c4) ∷
   rw 4 (q86 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   rw 9 (q75 c4) ∷
   rw 8 (q76 c4) ∷
   rw 7 (q77 c4) ∷
   rw 6 (q78 c4) ∷
   rw 5 (q77 c4) ∷
   rw 4 (q79 c4) ∷
   rw 3 (q80 c4) ∷
   rw 4 (q74 c4) ∷
   rw⁻ 0 (q63 c4) ∷
   rw 2 (q82 c4) ∷
   rw⁻ 6 (q87 c4) ∷
   rw 5 (q88 c4) ∷
   rw⁻ 4 (q89 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 2 (q90 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw 3 (q91 c4) ∷
   rw 4 (q92 c4) ∷
   rw⁻ 1 (q59 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = eqn (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-QVQ-at043043 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ []) (lem-tP-at043043 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (Toff412 ∷ Toff412 ∷ []) [] (wl 470 (lit c4))

-- box-cP @043043: 12 steps
lem-box-cP-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-box-cP-at043043 c4 = derive (Bx4-1203 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw 2 (q60 c4) ∷
   re 5 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw 5 (q60 c4) ∷
   rw 2 (q93 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q95 c4) ∷ []) Eq.refl

private
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) (Bx4-1203 ∷ []) (lem-SWbc-box-at043043 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) (Bx4-1023 ∷ []) (lem-nat-SWbc-at043043 c4)

-- sym-bc @043043: 2 steps
lem-sym-bc-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-sym-bc-at043043 c4 = derive (Bx4-1203 ∷ []) (Bx4-1023 ∷ [])
  (rw⁻ 0 (q96 c4) ∷
   rw 0 (q97 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = eqn (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-QVQ-at0330 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ []) (lem-tP-at0330 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (Toff312 ∷ Toff312 ∷ []) [] (wl 489 (lit c4))

-- box-cP @0330: 12 steps
lem-box-cP-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-box-cP-at0330 c4 = derive (Bx3-1204 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q1 c4) ∷
   re 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw 2 (q98 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q100 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (CCZ123 ∷ []) (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (wl 494 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-QVQ-at0314203142 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203142 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Toff304 ∷ Toff304 ∷ []) [] (wp 351 c4)

-- box-cP @0314203142: 12 steps
lem-box-cP-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0314203142 c4 = derive (Bx3-4012 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw⁻ 2 (q101 c4) ∷
   re 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw⁻ 5 (q101 c4) ∷
   rw 2 (q102 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q104 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (CCZ123 ∷ []) (wl 493 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-QVQ-at0310243142 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243142 c4)

-- box-cP @0310243142: 12 steps
lem-box-cP-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0310243142 c4 = derive (Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw 2 (q105 c4) ∷
   re 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw 5 (q105 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q107 c4) ∷
   rw 2 (q104 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (Bx4-0123 ∷ []) (Bx4-1023 ∷ []) (lem-sym-ab-at0410213243 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (Bx4-1023 ∷ []) (Bx4-1203 ∷ []) (lem-sym-bc-at04203243 c4)

-- box-perm-2314 @0410213243: 2 steps
lem-box-perm-2314-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-box-perm-2314-at0410213243 c4 = derive (Bx4-0123 ∷ []) (Bx4-1203 ∷ [])
  (rw 0 (q108 c4) ∷
   rw 0 (q109 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = eqn (Bx3-0124 ∷ []) (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (Bx3-1024 ∷ []) (Bx3-1204 ∷ []) (lem-sym-bc-at032032 c4)

-- box-perm-2314 @03102132: 2 steps
lem-box-perm-2314-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-2314-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-1204 ∷ [])
  (rw 0 (q110 c4) ∷
   rw 0 (q111 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) (Bx3-1204 ∷ []) (lem-SWbc-box-at0330 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) (Bx3-1024 ∷ []) (lem-nat-SWbc-at0330 c4)

-- sym-bc @0330: 2 steps
lem-sym-bc-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym-bc-at0330 c4 = derive (Bx3-1204 ∷ []) (Bx3-1024 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw 0 (q113 c4) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = eqn (Bx3-0124 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (CX43 ∷ CCZ013 ∷ []) (wp 392 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp 301 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (CS04 ∷ Toff324 ∷ []) (Toff324 ∷ CS04 ∷ []) (wp 393 c4)
  q118 : Ws → Eqn
  q118 c4 = eqn (CX01 ∷ Toff324 ∷ []) (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))
  q119 : Ws → Eqn
  q119 c4 = eqn (CS14⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS14⁻ ∷ []) (wl 542 (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (CS14 ∷ Toff324 ∷ []) (Toff324 ∷ CS14 ∷ []) (wl 543 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (CX43 ∷ Toff324 ∷ []) (Toff324 ∷ CX43 ∷ []) (wl 544 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (CCZ013 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ013 ∷ []) (wp 394 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (CX43 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX43 ∷ []) (wp 395 c4)

-- CXu-box-4 @03102132: 15 steps
lem-CXu-box-4-at03102132 : Ws → ⟪ (CX43 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CX43 ∷ []) ⟫ʷ
lem-CXu-box-4-at03102132 c4 = derive (CX43 ∷ Bx3-0124 ∷ []) (Bx3-0124 ∷ CX43 ∷ [])
  (rw 1 (q114 c4) ∷
   rw⁻ 0 (q115 c4) ∷
   rw 2 (q116 c4) ∷
   rw 6 (q117 c4) ∷
   rw 5 (q118 c4) ∷
   rw 4 (q119 c4) ∷
   rw 3 (q118 c4) ∷
   rw 2 (q120 c4) ∷
   rw⁻ 3 (q116 c4) ∷
   rw 1 (q121 c4) ∷
   rw⁻ 3 (q122 c4) ∷
   rw⁻ 2 (q115 c4) ∷
   rw 3 (q123 c4) ∷
   rw 3 (q121 c4) ∷
   rw⁻ 0 (q114 c4) ∷ []) Eq.refl

private
  q124 : Ws → Eqn
  q124 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-XCSX-box-2-at243243 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ []) (wp 428 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (CS13 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS13 ∷ []) (wp 429 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS13⁻ ∷ []) (wp 430 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (S0 ∷ CS04⁻ ∷ []) (X4 ∷ CS04 ∷ X4 ∷ []) (wp 257 c4)

-- F4-S0-CS1: 13 steps
lem-F4-S0-CS1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-CS1 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 0 (q124 c4) ∷
   rw⁻ 1 (q125 c4) ∷
   rw⁻ 2 (q126 c4) ∷
   rw⁻ 3 (q125 c4) ∷
   rw⁻ 4 (q127 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 1 (q128 c4) ∷
   rw 1 (q128 c4) ∷ []) Eq.refl

private
  q129 : Ws → Eqn
  q129 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-XCSX-box-2-at122441 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ []) (wp 437 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ []) (wp 438 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS12⁻ ∷ []) (wp 439 c4)

-- F4-S0-CS2: 13 steps
lem-F4-S0-CS2 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-CS2 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 0 (q129 c4) ∷
   rw⁻ 1 (q130 c4) ∷
   rw⁻ 2 (q131 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw⁻ 4 (q132 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 1 (q128 c4) ∷
   rw 1 (q128 c4) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-XCSX-box-2-at0210243143 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ []) (wl 584 (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ []) (wp 456 c4)
  q136 : Ws → Eqn
  q136 c4 = eqn (CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ []) (wp 457 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (S2 ∷ CS24⁻ ∷ []) (X4 ∷ CS24 ∷ X4 ∷ []) (wl 583 (lit c4))

-- F4-S2-CS0: 13 steps
lem-F4-S2-CS0 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-CS0 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 0 (q133 c4) ∷
   rw⁻ 1 (q134 c4) ∷
   rw⁻ 2 (q135 c4) ∷
   rw⁻ 3 (q134 c4) ∷
   rw⁻ 4 (q136 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 1 (q137 c4) ∷
   rw 1 (q137 c4) ∷ []) Eq.refl

private
  q138 : Ws → Eqn
  q138 c4 = eqn (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) (Bx2-4013 ∷ []) (lem-SWbc-box-at0214203143 c4)
  q139 : Ws → Eqn
  q139 c4 = eqn (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) (Bx2-4103 ∷ []) (lem-nat-SWbc-at0214203143 c4)

-- sym-bc @0214203143: 2 steps
lem-sym-bc-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-sym-bc-at0214203143 c4 = derive (Bx2-4013 ∷ []) (Bx2-4103 ∷ [])
  (rw⁻ 0 (q138 c4) ∷
   rw 0 (q139 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = eqn (CCZ023 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (wp 216 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-QVQ-at0214213043 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ []) (lem-tP-at0214213043 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (Toff214 ∷ Toff214 ∷ []) [] (wl 636 (lit c4))

-- box-cP @0214213043: 12 steps
lem-box-cP-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-box-cP-at0214213043 c4 = derive (Bx2-4103 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw⁻ 2 (q140 c4) ∷
   re 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw⁻ 5 (q140 c4) ∷
   rw 2 (q141 c4) ∷
   rw 1 (q142 c4) ∷
   rw 2 (q143 c4) ∷ []) Eq.refl

private
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ124 ∷ []) (wp 516 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-QVQ-at0210233441 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0210233441 c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (Toff203 ∷ Toff203 ∷ []) [] (wl 635 (lit c4))

-- box-cP @0210233441: 12 steps
lem-box-cP-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at0210233441 c4 = derive (Bx2-0341 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q144 c4) ∷
   re 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw 1 (q146 c4) ∷
   rw 2 (q147 c4) ∷ []) Eq.refl

private
  q148 : Ws → Eqn
  q148 c4 = eqn (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) (Bx0-2431 ∷ []) (lem-SWbc-box-at122441 c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) (Bx0-2341 ∷ []) (lem-nat-SWbc-at122441 c4)

-- sym-bc @122441: 2 steps
lem-sym-bc-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym-bc-at122441 c4 = derive (Bx0-2431 ∷ []) (Bx0-2341 ∷ [])
  (rw⁻ 0 (q148 c4) ∷
   rw 0 (q149 c4) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = eqn (CCZ014 ∷ []) (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (wp 218 c4)
  q151 : Ws → Eqn
  q151 c4 = eqn (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-QVQ-at12233441 c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ []) (lem-tP-at12233441 c4)

-- box-cP @12233441: 12 steps
lem-box-cP-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-box-cP-at12233441 c4 = derive (Bx0-2341 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q150 c4) ∷
   re 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q150 c4) ∷
   rw 2 (q151 c4) ∷
   rw 1 (q152 c4) ∷
   rw 2 (q31 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = eqn (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) (Bx0-4123 ∷ []) (lem-SWbc-box-at14213243 c4)
  q154 : Ws → Eqn
  q154 c4 = eqn (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) (Bx0-4213 ∷ []) (lem-nat-SWbc-at14213243 c4)

-- sym-bc @14213243: 2 steps
lem-sym-bc-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym-bc-at14213243 c4 = derive (Bx0-4123 ∷ []) (Bx0-4213 ∷ [])
  (rw⁻ 0 (q153 c4) ∷
   rw 0 (q154 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = eqn (CCZ013 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (wp 180 c4)
  q156 : Ws → Eqn
  q156 c4 = eqn (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at143143 c4)
  q157 : Ws → Eqn
  q157 c4 = eqn (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ []) (lem-tP-at143143 c4)

-- box-cP @143143: 12 steps
lem-box-cP-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at143143 c4 = derive (Bx0-4213 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw⁻ 2 (q155 c4) ∷
   re 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw⁻ 5 (q155 c4) ∷
   rw 2 (q156 c4) ∷
   rw 1 (q157 c4) ∷
   rw 2 (q16 c4) ∷ []) Eq.refl

private
  q158 : Ws → Eqn
  q158 c4 = eqn (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ024 ∷ []) (wp 212 c4)
  q159 : Ws → Eqn
  q159 c4 = eqn (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at233442 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ []) (lem-tP-at233442 c4)

-- box-cP @233442: 12 steps
lem-box-cP-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at233442 c4 = derive (Bx0-1342 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q158 c4) ∷
   re 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q158 c4) ∷
   rw 2 (q159 c4) ∷
   rw 1 (q160 c4) ∷
   rw 2 (q27 c4) ∷ []) Eq.refl

private
  q161 : Ws → Eqn
  q161 c4 = eqn (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) (Bx2-0413 ∷ []) (lem-SWbc-box-at0210243143 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) (Bx2-0143 ∷ []) (lem-nat-SWbc-at0210243143 c4)

-- sym-bc @0210243143: 2 steps
lem-sym-bc-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-sym-bc-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-0143 ∷ [])
  (rw⁻ 0 (q161 c4) ∷
   rw 0 (q162 c4) ∷ []) Eq.refl

private
  q163 : Ws → Eqn
  q163 c4 = eqn (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) (Bx0-1423 ∷ []) (lem-SWbc-box-at243243 c4)
  q164 : Ws → Eqn
  q164 c4 = eqn (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) (Bx0-1243 ∷ []) (lem-nat-SWbc-at243243 c4)

-- sym-bc @243243: 2 steps
lem-sym-bc-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-sym-bc-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-1243 ∷ [])
  (rw⁻ 0 (q163 c4) ∷
   rw 0 (q164 c4) ∷ []) Eq.refl

private
  q165 : Ws → Eqn
  q165 c4 = eqn (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) (Bx0-4231 ∷ []) (lem-SWbc-box-at1441 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) (Bx0-4321 ∷ []) (lem-nat-SWbc-at1441 c4)

-- sym-bc @1441: 2 steps
lem-sym-bc-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-sym-bc-at1441 c4 = derive (Bx0-4231 ∷ []) (Bx0-4321 ∷ [])
  (rw⁻ 0 (q165 c4) ∷
   rw 0 (q166 c4) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = eqn (Toff012 ∷ Bx0-4321 ∷ Toff012 ∷ []) (Bx0-4321 ∷ []) (lem-P-box-at14233241 c4)
  q168 : Ws → Eqn
  q168 c4 = eqn (Bx0-4321 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at14233241 c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (Bx0-2143 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at12213443 c4)

-- pairs @14233241: 4 steps
lem-pairs-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-pairs-at14233241 c4 = derive (Bx0-4321 ∷ []) (Bx0-2143 ∷ [])
  (rw⁻ 0 (q167 c4) ∷
   rw 1 (q168 c4) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 0 (q169 c4) ∷ []) Eq.refl

private
  q170 : Ws → Eqn
  q170 c4 = eqn (CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ034 ∷ []) (wp 598 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ-at12213443 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ []) (lem-tP-at12213443 c4)

-- box-cP @12213443: 12 steps
lem-box-cP-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP-at12213443 c4 = derive (Bx0-2143 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw 2 (q170 c4) ∷
   re 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw 5 (q170 c4) ∷
   rw 2 (q171 c4) ∷
   rw 1 (q172 c4) ∷
   rw 2 (q4 c4) ∷ []) Eq.refl

private
  q173 : Ws → Eqn
  q173 c4 = eqn (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) (Bx3-4102 ∷ []) (lem-SWbc-box-at0314213042 c4)
  q174 : Ws → Eqn
  q174 c4 = eqn (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) (Bx3-4012 ∷ []) (lem-nat-SWbc-at0314213042 c4)

-- sym-bc @0314213042: 2 steps
lem-sym-bc-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym-bc-at0314213042 c4 = derive (Bx3-4102 ∷ []) (Bx3-4012 ∷ [])
  (rw⁻ 0 (q173 c4) ∷
   rw 0 (q174 c4) ∷ []) Eq.refl

private
  q175 : Ws → Eqn
  q175 c4 = eqn (CCZ124 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (wl 756 (lit c4))
  q176 : Ws → Eqn
  q176 c4 = eqn (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-QVQ-at0213203441 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0213203441 c4)

-- box-cP @0213203441: 12 steps
lem-box-cP-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at0213203441 c4 = derive (Bx2-3041 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q175 c4) ∷
   re 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw⁻ 5 (q175 c4) ∷
   rw 2 (q176 c4) ∷
   rw 1 (q177 c4) ∷
   rw 2 (q147 c4) ∷ []) Eq.refl

private
  q178 : Ws → Eqn
  q178 c4 = eqn (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) (Bx3-4012 ∷ []) (lem-SWbc-box-at0314203142 c4)
  q179 : Ws → Eqn
  q179 c4 = eqn (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) (Bx3-4102 ∷ []) (lem-nat-SWbc-at0314203142 c4)

-- sym-bc @0314203142: 2 steps
lem-sym-bc-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-sym-bc-at0314203142 c4 = derive (Bx3-4012 ∷ []) (Bx3-4102 ∷ [])
  (rw⁻ 0 (q178 c4) ∷
   rw 0 (q179 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = eqn (CCZ023 ∷ []) (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (wp 661 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-QVQ-at0314213042 c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213042 c4)
  q183 : Ws → Eqn
  q183 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl 788 (lit c4))

-- box-cP @0314213042: 12 steps
lem-box-cP-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-box-cP-at0314213042 c4 = derive (Bx3-4102 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw⁻ 2 (q180 c4) ∷
   re 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw⁻ 5 (q180 c4) ∷
   rw 2 (q181 c4) ∷
   rw 1 (q182 c4) ∷
   rw 2 (q183 c4) ∷ []) Eq.refl

private
  q184 : Ws → Eqn
  q184 c4 = eqn (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) (Bx2-4103 ∷ []) (lem-SWbc-box-at0214213043 c4)
  q185 : Ws → Eqn
  q185 c4 = eqn (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) (Bx2-4013 ∷ []) (lem-nat-SWbc-at0214213043 c4)

-- sym-bc @0214213043: 2 steps
lem-sym-bc-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym-bc-at0214213043 c4 = derive (Bx2-4103 ∷ []) (Bx2-4013 ∷ [])
  (rw⁻ 0 (q184 c4) ∷
   rw 0 (q185 c4) ∷ []) Eq.refl

private
  q186 : Ws → Eqn
  q186 c4 = eqn (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) (Bx0-3214 ∷ []) (lem-SWbc-box-at1331 c4)
  q187 : Ws → Eqn
  q187 c4 = eqn (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) (Bx0-3124 ∷ []) (lem-nat-SWbc-at1331 c4)

-- sym-bc @1331: 2 steps
lem-sym-bc-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym-bc-at1331 c4 = derive (Bx0-3214 ∷ []) (Bx0-3124 ∷ [])
  (rw⁻ 0 (q186 c4) ∷
   rw 0 (q187 c4) ∷ []) Eq.refl

private
  q188 : Ws → Eqn
  q188 c4 = eqn (Toff324 ∷ Bx3-1024 ∷ Toff324 ∷ []) (Bx3-1024 ∷ []) (lem-P-box-at032032 c4)
  q189 : Ws → Eqn
  q189 c4 = eqn (Bx3-1024 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4)
  q190 : Ws → Eqn
  q190 c4 = eqn (Toff324 ∷ Toff324 ∷ []) [] (wl 442 (lit c4))
  q191 : Ws → Eqn
  q191 c4 = eqn (Bx3-2410 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243140 c4)

-- pairs @032032: 4 steps
lem-pairs-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-pairs-at032032 c4 = derive (Bx3-1024 ∷ []) (Bx3-2410 ∷ [])
  (rw⁻ 0 (q188 c4) ∷
   rw 1 (q189 c4) ∷
   rw 4 (q190 c4) ∷
   rw⁻ 0 (q191 c4) ∷ []) Eq.refl

private
  q192 : Ws → Eqn
  q192 c4 = eqn (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) (Bx3-2410 ∷ []) (lem-SWbc-box-at0312243140 c4)
  q193 : Ws → Eqn
  q193 c4 = eqn (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) (Bx3-2140 ∷ []) (lem-nat-SWbc-at0312243140 c4)

-- sym-bc @0312243140: 2 steps
lem-sym-bc-at0312243140 : Ws → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-sym-bc-at0312243140 c4 = derive (Bx3-2410 ∷ []) (Bx3-2140 ∷ [])
  (rw⁻ 0 (q192 c4) ∷
   rw 0 (q193 c4) ∷ []) Eq.refl

private
  q194 : Ws → Eqn
  q194 c4 = eqn (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) (Bx3-2140 ∷ []) (lem-SWbc-box-at0312213440 c4)
  q195 : Ws → Eqn
  q195 c4 = eqn (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) (Bx3-2410 ∷ []) (lem-nat-SWbc-at0312213440 c4)

-- sym-bc @0312213440: 2 steps
lem-sym-bc-at0312213440 : Ws → ⟪ (Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-sym-bc-at0312213440 c4 = derive (Bx3-2140 ∷ []) (Bx3-2410 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 0 (q195 c4) ∷ []) Eq.refl

private
  q196 : Ws → Eqn
  q196 c4 = eqn (CCZ013 ∷ []) (CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ []) (wl 845 (lit c4))
  q197 : Ws → Eqn
  q197 c4 = eqn (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-QVQ-at0312243140 c4)
  q198 : Ws → Eqn
  q198 c4 = eqn (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ []) (lem-tP-at0312243140 c4)

-- box-cP @0312243140: 12 steps
lem-box-cP-at0312243140 : Ws → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-box-cP-at0312243140 c4 = derive (Bx3-2410 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw⁻ 2 (q196 c4) ∷
   re 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw⁻ 5 (q196 c4) ∷
   rw 2 (q197 c4) ∷
   rw 1 (q198 c4) ∷
   rw 2 (q190 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = eqn (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) (Bx0-3124 ∷ []) (lem-SWbc-box-at132132 c4)
  q200 : Ws → Eqn
  q200 c4 = eqn (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) (Bx0-3214 ∷ []) (lem-nat-SWbc-at132132 c4)

-- sym-bc @132132: 2 steps
lem-sym-bc-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym-bc-at132132 c4 = derive (Bx0-3124 ∷ []) (Bx0-3214 ∷ [])
  (rw⁻ 0 (q199 c4) ∷
   rw 0 (q200 c4) ∷ []) Eq.refl

private
  q201 : Ws → Eqn
  q201 c4 = eqn (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) (Bx2-1304 ∷ []) (lem-SWbc-box-at022330 c4)
  q202 : Ws → Eqn
  q202 c4 = eqn (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) (Bx2-1034 ∷ []) (lem-nat-SWbc-at022330 c4)

-- sym-bc @022330: 2 steps
lem-sym-bc-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym-bc-at022330 c4 = derive (Bx2-1304 ∷ []) (Bx2-1034 ∷ [])
  (rw⁻ 0 (q201 c4) ∷
   rw 0 (q202 c4) ∷ []) Eq.refl

private
  q203 : Ws → Eqn
  q203 c4 = eqn (Toff234 ∷ Bx2-1034 ∷ Toff234 ∷ []) (Bx2-1034 ∷ []) (lem-P-box-at0220 c4)
  q204 : Ws → Eqn
  q204 c4 = eqn (Bx2-1034 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0220 c4)
  q205 : Ws → Eqn
  q205 c4 = eqn (Toff234 ∷ Toff234 ∷ []) [] (wl 420 (lit c4))
  q206 : Ws → Eqn
  q206 c4 = eqn (Bx2-3410 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0213243140 c4)

-- pairs @0220: 4 steps
lem-pairs-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-pairs-at0220 c4 = derive (Bx2-1034 ∷ []) (Bx2-3410 ∷ [])
  (rw⁻ 0 (q203 c4) ∷
   rw 1 (q204 c4) ∷
   rw 4 (q205 c4) ∷
   rw⁻ 0 (q206 c4) ∷ []) Eq.refl

private
  q207 : Ws → Eqn
  q207 c4 = eqn (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) (Bx2-3140 ∷ []) (lem-SWbc-box-at0213213440 c4)
  q208 : Ws → Eqn
  q208 c4 = eqn (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) (Bx2-3410 ∷ []) (lem-nat-SWbc-at0213213440 c4)

-- sym-bc @0213213440: 2 steps
lem-sym-bc-at0213213440 : Ws → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-sym-bc-at0213213440 c4 = derive (Bx2-3140 ∷ []) (Bx2-3410 ∷ [])
  (rw⁻ 0 (q207 c4) ∷
   rw 0 (q208 c4) ∷ []) Eq.refl

private
  q209 : Ws → Eqn
  q209 c4 = eqn (Toff201 ∷ Bx2-3410 ∷ Toff201 ∷ []) (Bx2-3410 ∷ []) (lem-P-box-at0213243140 c4)
  q210 : Ws → Eqn
  q210 c4 = eqn (Bx2-3410 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243140 c4)
  q211 : Ws → Eqn
  q211 c4 = eqn (Toff201 ∷ Toff201 ∷ []) [] (wl 421 (lit c4))
  q212 : Ws → Eqn
  q212 c4 = eqn (Bx2-1034 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0220 c4)

-- pairs @0213243140: 4 steps
lem-pairs-at0213243140 : Ws → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-pairs-at0213243140 c4 = derive (Bx2-3410 ∷ []) (Bx2-1034 ∷ [])
  (rw⁻ 0 (q209 c4) ∷
   rw 1 (q210 c4) ∷
   rw 4 (q211 c4) ∷
   rw⁻ 0 (q212 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = eqn (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-QVQ-at022330 c4)
  q214 : Ws → Eqn
  q214 c4 = eqn (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ []) (lem-tP-at022330 c4)
  q215 : Ws → Eqn
  q215 c4 = eqn (Toff213 ∷ Toff213 ∷ []) [] (wl 180 (lit c4))

-- box-cP @022330: 12 steps
lem-box-cP-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-box-cP-at022330 c4 = derive (Bx2-1304 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q24 c4) ∷
   re 5 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q24 c4) ∷
   rw 2 (q213 c4) ∷
   rw 1 (q214 c4) ∷
   rw 2 (q215 c4) ∷ []) Eq.refl

private
  q216 : Ws → Eqn
  q216 c4 = eqn (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) (Bx0-2314 ∷ []) (lem-SWbc-box-at122331 c4)
  q217 : Ws → Eqn
  q217 c4 = eqn (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) (Bx0-2134 ∷ []) (lem-nat-SWbc-at122331 c4)

-- sym-bc @122331: 2 steps
lem-sym-bc-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym-bc-at122331 c4 = derive (Bx0-2314 ∷ []) (Bx0-2134 ∷ [])
  (rw⁻ 0 (q216 c4) ∷
   rw 0 (q217 c4) ∷ []) Eq.refl

private
  q218 : Ws → Eqn
  q218 c4 = eqn (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-QVQ-at14213243 c4)
  q219 : Ws → Eqn
  q219 c4 = eqn (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ []) (lem-tP-at14213243 c4)

-- box-cP @14213243: 12 steps
lem-box-cP-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at14213243 c4 = derive (Bx0-4123 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw⁻ 2 (q140 c4) ∷
   re 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw⁻ 5 (q140 c4) ∷
   rw 2 (q218 c4) ∷
   rw 1 (q219 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = eqn (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) (Bx0-2341 ∷ []) (lem-SWbc-box-at12233441 c4)
  q221 : Ws → Eqn
  q221 c4 = eqn (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) (Bx0-2431 ∷ []) (lem-nat-SWbc-at12233441 c4)

-- sym-bc @12233441: 2 steps
lem-sym-bc-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-sym-bc-at12233441 c4 = derive (Bx0-2341 ∷ []) (Bx0-2431 ∷ [])
  (rw⁻ 0 (q220 c4) ∷
   rw 0 (q221 c4) ∷ []) Eq.refl

private
  q222 : Ws → Eqn
  q222 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) (Bx0-1324 ∷ []) (lem-SWbc-box-at2332 c4)
  q223 : Ws → Eqn
  q223 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) (Bx0-1234 ∷ []) (lem-nat-SWbc-at2332 c4)

-- sym-bc @2332: 2 steps
lem-sym-bc-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym-bc-at2332 c4 = derive (Bx0-1324 ∷ []) (Bx0-1234 ∷ [])
  (rw⁻ 0 (q222 c4) ∷
   rw 0 (q223 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0214 ∷ []) (lem-sym-bc-at03102132 c4)

-- box-perm-1324 @03102132: 1 steps
lem-box-perm-1324-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-box-perm-1324-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-0214 ∷ [])
  (rw 0 (q224 c4) ∷ []) Eq.refl

private
  q225 : Ws → Eqn
  q225 c4 = eqn (CCZ123 ∷ []) (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (wl 610 (lit c4))
  q226 : Ws → Eqn
  q226 c4 = eqn (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-QVQ-at0214203143 c4)
  q227 : Ws → Eqn
  q227 c4 = eqn (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0214203143 c4)

-- box-cP @0214203143: 12 steps
lem-box-cP-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-box-cP-at0214203143 c4 = derive (Bx2-4013 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw⁻ 2 (q225 c4) ∷
   re 5 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw⁻ 5 (q225 c4) ∷
   rw 2 (q226 c4) ∷
   rw 1 (q227 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

private
  q228 : Ws → Eqn
  q228 c4 = eqn (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) (Bx2-1340 ∷ []) (lem-SWbc-box-at02233440 c4)
  q229 : Ws → Eqn
  q229 c4 = eqn (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) (Bx2-1430 ∷ []) (lem-nat-SWbc-at02233440 c4)

-- sym-bc @02233440: 2 steps
lem-sym-bc-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-sym-bc-at02233440 c4 = derive (Bx2-1340 ∷ []) (Bx2-1430 ∷ [])
  (rw⁻ 0 (q228 c4) ∷
   rw 0 (q229 c4) ∷ []) Eq.refl

private
  q230 : Ws → Eqn
  q230 c4 = eqn (CCZ023 ∷ []) (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (wl 1126 (lit c4))
  q231 : Ws → Eqn
  q231 c4 = eqn (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-QVQ-at022440 c4)
  q232 : Ws → Eqn
  q232 c4 = eqn (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ []) (lem-tP-at022440 c4)

-- box-cP @022440: 12 steps
lem-box-cP-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-box-cP-at022440 c4 = derive (Bx2-1430 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q230 c4) ∷
   re 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q230 c4) ∷
   rw 2 (q231 c4) ∷
   rw 1 (q232 c4) ∷
   rw 2 (q143 c4) ∷ []) Eq.refl

private
  q233 : Ws → Eqn
  q233 c4 = eqn (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) (Bx2-1430 ∷ []) (lem-SWbc-box-at022440 c4)
  q234 : Ws → Eqn
  q234 c4 = eqn (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) (Bx2-1340 ∷ []) (lem-nat-SWbc-at022440 c4)

-- sym-bc @022440: 2 steps
lem-sym-bc-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-sym-bc-at022440 c4 = derive (Bx2-1430 ∷ []) (Bx2-1340 ∷ [])
  (rw⁻ 0 (q233 c4) ∷
   rw 0 (q234 c4) ∷ []) Eq.refl

private
  q235 : Ws → Eqn
  q235 c4 = eqn (CCZ024 ∷ []) (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (wp 767 c4)
  q236 : Ws → Eqn
  q236 c4 = eqn (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-QVQ-at02233440 c4)
  q237 : Ws → Eqn
  q237 c4 = eqn (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ []) (lem-tP-at02233440 c4)

-- box-cP @02233440: 12 steps
lem-box-cP-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-box-cP-at02233440 c4 = derive (Bx2-1340 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q235 c4) ∷
   re 5 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q235 c4) ∷
   rw 2 (q236 c4) ∷
   rw 1 (q237 c4) ∷
   rw 2 (q215 c4) ∷ []) Eq.refl

private
  q238 : Ws → Eqn
  q238 c4 = eqn (CCZ013 ∷ []) (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (wp 214 c4)
  q239 : Ws → Eqn
  q239 c4 = eqn (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at1441 c4)
  q240 : Ws → Eqn
  q240 c4 = eqn (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ []) (lem-tP-at1441 c4)

-- box-cP @1441: 12 steps
lem-box-cP-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at1441 c4 = derive (Bx0-4231 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q238 c4) ∷
   re 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q238 c4) ∷
   rw 2 (q239 c4) ∷
   rw 1 (q240 c4) ∷
   rw 2 (q16 c4) ∷ []) Eq.refl

private
  q241 : Ws → Eqn
  q241 c4 = eqn (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (X4 ∷ CCZ034 ∷ []) (wp 796 c4)
  q242 : Ws → Eqn
  q242 c4 = eqn (CZ03 ∷ Toff012 ∷ []) (Toff012 ∷ CZ03 ∷ CCZ123 ∷ []) (wl 1074 (lit c4))
  q243 : Ws → Eqn
  q243 c4 = eqn (Toff012 ∷ X4 ∷ []) (X4 ∷ Toff012 ∷ []) (c₃ (Toff) (X ↑))
  q244 : Ws → Eqn
  q244 c4 = eqn (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl 297 (lit c4))
  q245 : Ws → Eqn
  q245 c4 = eqn (CCZ034 ∷ CX31 ∷ []) (CX31 ∷ CCZ034 ∷ []) (wp 127 c4)
  q246 : Ws → Eqn
  q246 c4 = eqn (CS12⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4))
  q247 : Ws → Eqn
  q247 c4 = eqn (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4))
  q248 : Ws → Eqn
  q248 c4 = eqn (CCZ034 ∷ CZ03 ∷ []) (CZ03 ∷ CCZ034 ∷ []) (wp 797 c4)
  q249 : Ws → Eqn
  q249 c4 = eqn (X4 ∷ CZ03 ∷ CZ03 ∷ []) (X4 ∷ []) (wp 798 c4)
  q250 : Ws → Eqn
  q250 c4 = eqn (CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ []) (wl 210 (lit c4))

-- Xb-box @13243142: 18 steps
lem-Xb-box-at13243142 : Ws → ⟪ (X4 ∷ Bx0-3412 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at13243142 c4 = derive (X4 ∷ Bx0-3412 ∷ X4 ∷ []) (Bx0-3412 ∷ CCZ123 ∷ [])
  (rw 1 (q58 c4) ∷
   rw⁻ 0 (q241 c4) ∷
   rw 2 (q242 c4) ∷
   rw⁻ 1 (q243 c4) ∷
   rw 4 (q244 c4) ∷
   rw⁻ 8 (q90 c4) ∷
   rw⁻ 7 (q245 c4) ∷
   rw 6 (q246 c4) ∷
   rw⁻ 5 (q245 c4) ∷
   rw 4 (q247 c4) ∷
   rw⁻ 5 (q244 c4) ∷
   rw⁻ 3 (q248 c4) ∷
   rw⁻ 2 (q241 c4) ∷
   rw 3 (q249 c4) ∷
   rw 4 (q91 c4) ∷
   rw⁻ 3 (q243 c4) ∷
   rw⁻ 0 (q58 c4) ∷
   rw⁻ 1 (q250 c4) ∷ []) Eq.refl

private
  q251 : Ws → Eqn
  q251 c4 = eqn (Bx0-3412 ∷ []) (Bx0-3142 ∷ []) (lem-sym-bc-at13243142 c4)

-- box-perm-1324 @13243142: 1 steps
lem-box-perm-1324-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-1324-at13243142 c4 = derive (Bx0-3412 ∷ []) (Bx0-3142 ∷ [])
  (rw 0 (q251 c4) ∷ []) Eq.refl

private
  q252 : Ws → Eqn
  q252 c4 = eqn (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) (Bx2-0341 ∷ []) (lem-SWbc-box-at0210233441 c4)
  q253 : Ws → Eqn
  q253 c4 = eqn (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) (Bx2-0431 ∷ []) (lem-nat-SWbc-at0210233441 c4)

-- sym-bc @0210233441: 2 steps
lem-sym-bc-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-sym-bc-at0210233441 c4 = derive (Bx2-0341 ∷ []) (Bx2-0431 ∷ [])
  (rw⁻ 0 (q252 c4) ∷
   rw 0 (q253 c4) ∷ []) Eq.refl

private
  q254 : Ws → Eqn
  q254 c4 = eqn (CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (CCZ123 ∷ []) (wl 1155 (lit c4))
  q255 : Ws → Eqn
  q255 c4 = eqn (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-QVQ-at02102441 c4)
  q256 : Ws → Eqn
  q256 c4 = eqn (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02102441 c4)

-- box-cP @02102441: 12 steps
lem-box-cP-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-box-cP-at02102441 c4 = derive (Bx2-0431 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q254 c4) ∷
   re 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q254 c4) ∷
   rw 2 (q255 c4) ∷
   rw 1 (q256 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

private
  q257 : Ws → Eqn
  q257 c4 = eqn (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) (Bx2-0431 ∷ []) (lem-SWbc-box-at02102441 c4)
  q258 : Ws → Eqn
  q258 c4 = eqn (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) (Bx2-0341 ∷ []) (lem-nat-SWbc-at02102441 c4)

-- sym-bc @02102441: 2 steps
lem-sym-bc-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym-bc-at02102441 c4 = derive (Bx2-0431 ∷ []) (Bx2-0341 ∷ [])
  (rw⁻ 0 (q257 c4) ∷
   rw 0 (q258 c4) ∷ []) Eq.refl

private
  q259 : Ws → Eqn
  q259 c4 = eqn (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) (Bx0-1342 ∷ []) (lem-SWbc-box-at233442 c4)
  q260 : Ws → Eqn
  q260 c4 = eqn (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) (Bx0-1432 ∷ []) (lem-nat-SWbc-at233442 c4)

-- sym-bc @233442: 2 steps
lem-sym-bc-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-sym-bc-at233442 c4 = derive (Bx0-1342 ∷ []) (Bx0-1432 ∷ [])
  (rw⁻ 0 (q259 c4) ∷
   rw 0 (q260 c4) ∷ []) Eq.refl

private
  q261 : Ws → Eqn
  q261 c4 = eqn (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (CCZ023 ∷ []) (wl 344 (lit c4))
  q262 : Ws → Eqn
  q262 c4 = eqn (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-QVQ-at2442 c4)
  q263 : Ws → Eqn
  q263 c4 = eqn (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ []) (lem-tP-at2442 c4)

-- box-cP @2442: 12 steps
lem-box-cP-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at2442 c4 = derive (Bx0-1432 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q261 c4) ∷
   re 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q261 c4) ∷
   rw 2 (q262 c4) ∷
   rw 1 (q263 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q264 : Ws → Eqn
  q264 c4 = eqn (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) (Bx0-1432 ∷ []) (lem-SWbc-box-at2442 c4)
  q265 : Ws → Eqn
  q265 c4 = eqn (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) (Bx0-1342 ∷ []) (lem-nat-SWbc-at2442 c4)

-- sym-bc @2442: 2 steps
lem-sym-bc-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym-bc-at2442 c4 = derive (Bx0-1432 ∷ []) (Bx0-1342 ∷ [])
  (rw⁻ 0 (q264 c4) ∷
   rw 0 (q265 c4) ∷ []) Eq.refl

private
  q266 : Ws → Eqn
  q266 c4 = eqn (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) (Bx0-4213 ∷ []) (lem-SWbc-box-at143143 c4)
  q267 : Ws → Eqn
  q267 c4 = eqn (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) (Bx0-4123 ∷ []) (lem-nat-SWbc-at143143 c4)

-- sym-bc @143143: 2 steps
lem-sym-bc-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-sym-bc-at143143 c4 = derive (Bx0-4213 ∷ []) (Bx0-4123 ∷ [])
  (rw⁻ 0 (q266 c4) ∷
   rw 0 (q267 c4) ∷ []) Eq.refl

private
  q268 : Ws → Eqn
  q268 c4 = eqn (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) (Bx0-2143 ∷ []) (lem-SWbc-box-at12213443 c4)
  q269 : Ws → Eqn
  q269 c4 = eqn (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) (Bx0-2413 ∷ []) (lem-nat-SWbc-at12213443 c4)

-- sym-bc @12213443: 2 steps
lem-sym-bc-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-sym-bc-at12213443 c4 = derive (Bx0-2143 ∷ []) (Bx0-2413 ∷ [])
  (rw⁻ 0 (q268 c4) ∷
   rw 0 (q269 c4) ∷ []) Eq.refl

private
  q270 : Ws → Eqn
  q270 c4 = eqn (CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ []) (CCZ013 ∷ []) (wl 292 (lit c4))
  q271 : Ws → Eqn
  q271 c4 = eqn (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at12243143 c4)
  q272 : Ws → Eqn
  q272 c4 = eqn (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ []) (lem-tP-at12243143 c4)

-- box-cP @12243143: 12 steps
lem-box-cP-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at12243143 c4 = derive (Bx0-2413 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw 2 (q270 c4) ∷
   re 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw 5 (q270 c4) ∷
   rw 2 (q271 c4) ∷
   rw 1 (q272 c4) ∷
   rw 2 (q16 c4) ∷ []) Eq.refl

private
  q273 : Ws → Eqn
  q273 c4 = eqn (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) (Bx3-4210 ∷ []) (lem-SWbc-box-at03143140 c4)
  q274 : Ws → Eqn
  q274 c4 = eqn (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) (Bx3-4120 ∷ []) (lem-nat-SWbc-at03143140 c4)

-- sym-bc @03143140: 2 steps
lem-sym-bc-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym-bc-at03143140 c4 = derive (Bx3-4210 ∷ []) (Bx3-4120 ∷ [])
  (rw⁻ 0 (q273 c4) ∷
   rw 0 (q274 c4) ∷ []) Eq.refl

private
  q275 : Ws → Eqn
  q275 c4 = eqn (CCZ023 ∷ []) (CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (wp 992 c4)
  q276 : Ws → Eqn
  q276 c4 = eqn (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-QVQ-at0314213240 c4)
  q277 : Ws → Eqn
  q277 c4 = eqn (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213240 c4)

-- box-cP @0314213240: 12 steps
lem-box-cP-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-box-cP-at0314213240 c4 = derive (Bx3-4120 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw⁻ 2 (q275 c4) ∷
   re 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw⁻ 5 (q275 c4) ∷
   rw 2 (q276 c4) ∷
   rw 1 (q277 c4) ∷
   rw 2 (q183 c4) ∷ []) Eq.refl

private
  q278 : Ws → Eqn
  q278 c4 = eqn (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) (Bx3-4120 ∷ []) (lem-SWbc-box-at0314213240 c4)
  q279 : Ws → Eqn
  q279 c4 = eqn (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) (Bx3-4210 ∷ []) (lem-nat-SWbc-at0314213240 c4)

-- sym-bc @0314213240: 2 steps
lem-sym-bc-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-sym-bc-at0314213240 c4 = derive (Bx3-4120 ∷ []) (Bx3-4210 ∷ [])
  (rw⁻ 0 (q278 c4) ∷
   rw 0 (q279 c4) ∷ []) Eq.refl

private
  q280 : Ws → Eqn
  q280 c4 = eqn (CCZ013 ∷ []) (CCZ134 ∷ Toff413 ∷ CZ04 ∷ Toff413 ∷ CCZ134 ∷ CZ04 ∷ []) (wp 988 c4)
  q281 : Ws → Eqn
  q281 c4 = eqn (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-QVQ-at03143140 c4)
  q282 : Ws → Eqn
  q282 c4 = eqn (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143140 c4)

-- box-cP @03143140: 12 steps
lem-box-cP-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-box-cP-at03143140 c4 = derive (Bx3-4210 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw⁻ 2 (q280 c4) ∷
   re 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw⁻ 5 (q280 c4) ∷
   rw 2 (q281 c4) ∷
   rw 1 (q282 c4) ∷
   rw 2 (q190 c4) ∷ []) Eq.refl

private
  q283 : Ws → Eqn
  q283 c4 = eqn (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-QVQ-at03243240 c4)
  q284 : Ws → Eqn
  q284 c4 = eqn (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ []) (lem-tP-at03243240 c4)

-- box-cP @03243240: 12 steps
lem-box-cP-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-box-cP-at03243240 c4 = derive (Bx3-1420 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q230 c4) ∷
   re 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q230 c4) ∷
   rw 2 (q283 c4) ∷
   rw 1 (q284 c4) ∷
   rw 2 (q183 c4) ∷ []) Eq.refl

private
  q285 : Ws → Eqn
  q285 c4 = eqn (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) (Bx3-1240 ∷ []) (lem-SWbc-box-at033440 c4)
  q286 : Ws → Eqn
  q286 c4 = eqn (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) (Bx3-1420 ∷ []) (lem-nat-SWbc-at033440 c4)

-- sym-bc @033440: 2 steps
lem-sym-bc-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym-bc-at033440 c4 = derive (Bx3-1240 ∷ []) (Bx3-1420 ∷ [])
  (rw⁻ 0 (q285 c4) ∷
   rw 0 (q286 c4) ∷ []) Eq.refl

private
  q287 : Ws → Eqn
  q287 c4 = eqn (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) (Bx3-1420 ∷ []) (lem-SWbc-box-at03243240 c4)
  q288 : Ws → Eqn
  q288 c4 = eqn (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) (Bx3-1240 ∷ []) (lem-nat-SWbc-at03243240 c4)

-- sym-bc @03243240: 2 steps
lem-sym-bc-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-sym-bc-at03243240 c4 = derive (Bx3-1420 ∷ []) (Bx3-1240 ∷ [])
  (rw⁻ 0 (q287 c4) ∷
   rw 0 (q288 c4) ∷ []) Eq.refl

private
  q289 : Ws → Eqn
  q289 c4 = eqn (CCZ034 ∷ []) (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (wp 733 c4)
  q290 : Ws → Eqn
  q290 c4 = eqn (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-QVQ-at033440 c4)
  q291 : Ws → Eqn
  q291 c4 = eqn (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ []) (lem-tP-at033440 c4)

-- box-cP @033440: 12 steps
lem-box-cP-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-box-cP-at033440 c4 = derive (Bx3-1240 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q289 c4) ∷
   re 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q289 c4) ∷
   rw 2 (q290 c4) ∷
   rw 1 (q291 c4) ∷
   rw 2 (q100 c4) ∷ []) Eq.refl

private
  q292 : Ws → Eqn
  q292 c4 = eqn (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) (Bx3-0241 ∷ []) (lem-SWbc-box-at03103441 c4)
  q293 : Ws → Eqn
  q293 c4 = eqn (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) (Bx3-0421 ∷ []) (lem-nat-SWbc-at03103441 c4)

-- sym-bc @03103441: 2 steps
lem-sym-bc-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym-bc-at03103441 c4 = derive (Bx3-0241 ∷ []) (Bx3-0421 ∷ [])
  (rw⁻ 0 (q292 c4) ∷
   rw 0 (q293 c4) ∷ []) Eq.refl

private
  q294 : Ws → Eqn
  q294 c4 = eqn (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-QVQ-at0310243241 c4)
  q295 : Ws → Eqn
  q295 c4 = eqn (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243241 c4)

-- box-cP @0310243241: 12 steps
lem-box-cP-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0310243241 c4 = derive (Bx3-0421 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q254 c4) ∷
   re 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q254 c4) ∷
   rw 2 (q294 c4) ∷
   rw 1 (q295 c4) ∷
   rw 2 (q104 c4) ∷ []) Eq.refl

private
  q296 : Ws → Eqn
  q296 c4 = eqn (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) (Bx3-0421 ∷ []) (lem-SWbc-box-at0310243241 c4)
  q297 : Ws → Eqn
  q297 c4 = eqn (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) (Bx3-0241 ∷ []) (lem-nat-SWbc-at0310243241 c4)

-- sym-bc @0310243241: 2 steps
lem-sym-bc-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-sym-bc-at0310243241 c4 = derive (Bx3-0421 ∷ []) (Bx3-0241 ∷ [])
  (rw⁻ 0 (q296 c4) ∷
   rw 0 (q297 c4) ∷ []) Eq.refl

private
  q298 : Ws → Eqn
  q298 c4 = eqn (CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (CCZ134 ∷ []) (wp 1048 c4)
  q299 : Ws → Eqn
  q299 c4 = eqn (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-QVQ-at03103441 c4)
  q300 : Ws → Eqn
  q300 c4 = eqn (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ []) (lem-tP-at03103441 c4)
  q301 : Ws → Eqn
  q301 c4 = eqn (Toff302 ∷ Toff302 ∷ []) [] (wl 787 (lit c4))

-- box-cP @03103441: 12 steps
lem-box-cP-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-box-cP-at03103441 c4 = derive (Bx3-0241 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q298 c4) ∷
   re 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q298 c4) ∷
   rw 2 (q299 c4) ∷
   rw 1 (q300 c4) ∷
   rw 2 (q301 c4) ∷ []) Eq.refl

private
  q302 : Ws → Eqn
  q302 c4 = eqn (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) (Bx3-0412 ∷ []) (lem-SWbc-box-at0310243142 c4)
  q303 : Ws → Eqn
  q303 c4 = eqn (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) (Bx3-0142 ∷ []) (lem-nat-SWbc-at0310243142 c4)

-- sym-bc @0310243142: 2 steps
lem-sym-bc-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym-bc-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-0142 ∷ [])
  (rw⁻ 0 (q302 c4) ∷
   rw 0 (q303 c4) ∷ []) Eq.refl

private
  q304 : Ws → Eqn
  q304 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0412 ∷ []) (lem-sym-bc-at0310213442 c4)

-- box-perm-1324 @0310213442: 1 steps
lem-box-perm-1324-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-1324-at0310213442 c4 = derive (Bx3-0142 ∷ []) (Bx3-0412 ∷ [])
  (rw 0 (q304 c4) ∷ []) Eq.refl

private
  q305 : Ws → Eqn
  q305 c4 = eqn (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) (Bx3-2041 ∷ []) (lem-SWbc-box-at0312203441 c4)
  q306 : Ws → Eqn
  q306 c4 = eqn (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) (Bx3-2401 ∷ []) (lem-nat-SWbc-at0312203441 c4)

-- sym-bc @0312203441: 2 steps
lem-sym-bc-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-sym-bc-at0312203441 c4 = derive (Bx3-2041 ∷ []) (Bx3-2401 ∷ [])
  (rw⁻ 0 (q305 c4) ∷
   rw 0 (q306 c4) ∷ []) Eq.refl

private
  q307 : Ws → Eqn
  q307 c4 = eqn (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-QVQ-at0312243041 c4)
  q308 : Ws → Eqn
  q308 c4 = eqn (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ []) (lem-tP-at0312243041 c4)

-- box-cP @0312243041: 12 steps
lem-box-cP-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-box-cP-at0312243041 c4 = derive (Bx3-2401 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q13 c4) ∷
   re 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 2 (q307 c4) ∷
   rw 1 (q308 c4) ∷
   rw 2 (q190 c4) ∷ []) Eq.refl

private
  q309 : Ws → Eqn
  q309 c4 = eqn (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) (Bx3-2401 ∷ []) (lem-SWbc-box-at0312243041 c4)
  q310 : Ws → Eqn
  q310 c4 = eqn (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) (Bx3-2041 ∷ []) (lem-nat-SWbc-at0312243041 c4)

-- sym-bc @0312243041: 2 steps
lem-sym-bc-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-sym-bc-at0312243041 c4 = derive (Bx3-2401 ∷ []) (Bx3-2041 ∷ [])
  (rw⁻ 0 (q309 c4) ∷
   rw 0 (q310 c4) ∷ []) Eq.refl

private
  q311 : Ws → Eqn
  q311 c4 = eqn (CCZ134 ∷ []) (CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ []) (wl 1271 (lit c4))
  q312 : Ws → Eqn
  q312 c4 = eqn (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-QVQ-at0312203441 c4)
  q313 : Ws → Eqn
  q313 c4 = eqn (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ []) (lem-tP-at0312203441 c4)

-- box-cP @0312203441: 12 steps
lem-box-cP-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-box-cP-at0312203441 c4 = derive (Bx3-2041 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q311 c4) ∷
   re 5 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q311 c4) ∷
   rw 2 (q312 c4) ∷
   rw 1 (q313 c4) ∷
   rw 2 (q301 c4) ∷ []) Eq.refl

private
  q314 : Ws → Eqn
  q314 c4 = eqn (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) (Bx0-1243 ∷ []) (lem-SWbc-box-at3443 c4)
  q315 : Ws → Eqn
  q315 c4 = eqn (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) (Bx0-1423 ∷ []) (lem-nat-SWbc-at3443 c4)

-- sym-bc @3443: 2 steps
lem-sym-bc-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym-bc-at3443 c4 = derive (Bx0-1243 ∷ []) (Bx0-1423 ∷ [])
  (rw⁻ 0 (q314 c4) ∷
   rw 0 (q315 c4) ∷ []) Eq.refl

private
  q316 : Ws → Eqn
  q316 c4 = eqn (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) (Bx3-0214 ∷ []) (lem-SWbc-box-at031031 c4)
  q317 : Ws → Eqn
  q317 c4 = eqn (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) (Bx3-0124 ∷ []) (lem-nat-SWbc-at031031 c4)

-- sym-bc @031031: 2 steps
lem-sym-bc-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym-bc-at031031 c4 = derive (Bx3-0214 ∷ []) (Bx3-0124 ∷ [])
  (rw⁻ 0 (q316 c4) ∷
   rw 0 (q317 c4) ∷ []) Eq.refl

private
  q318 : Ws → Eqn
  q318 c4 = eqn (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-QVQ-at031031 c4)
  q319 : Ws → Eqn
  q319 c4 = eqn (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ []) (lem-tP-at031031 c4)

-- box-cP @031031: 12 steps
lem-box-cP-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-box-cP-at031031 c4 = derive (Bx3-0214 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw 2 (q46 c4) ∷
   re 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw 5 (q46 c4) ∷
   rw 2 (q318 c4) ∷
   rw 1 (q319 c4) ∷
   rw 2 (q301 c4) ∷ []) Eq.refl

private
  q320 : Ws → Eqn
  q320 c4 = eqn (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) (Bx3-0124 ∷ []) (lem-P-box-at03102132 c4)
  q321 : Ws → Eqn
  q321 c4 = eqn (Bx3-2401 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243041 c4)

-- pairs @03102132: 4 steps
lem-pairs-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-pairs-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-2401 ∷ [])
  (rw⁻ 0 (q320 c4) ∷
   rw 1 (q114 c4) ∷
   rw 4 (q190 c4) ∷
   rw⁻ 0 (q321 c4) ∷ []) Eq.refl

private
  q322 : Ws → Eqn
  q322 c4 = eqn (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) (Bx3-4201 ∷ []) (lem-SWbc-box-at03143041 c4)
  q323 : Ws → Eqn
  q323 c4 = eqn (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) (Bx3-4021 ∷ []) (lem-nat-SWbc-at03143041 c4)

-- sym-bc @03143041: 2 steps
lem-sym-bc-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym-bc-at03143041 c4 = derive (Bx3-4201 ∷ []) (Bx3-4021 ∷ [])
  (rw⁻ 0 (q322 c4) ∷
   rw 0 (q323 c4) ∷ []) Eq.refl

private
  q324 : Ws → Eqn
  q324 c4 = eqn (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) (Bx2-4031 ∷ []) (lem-SWbc-box-at02142041 c4)
  q325 : Ws → Eqn
  q325 c4 = eqn (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) (Bx2-4301 ∷ []) (lem-nat-SWbc-at02142041 c4)

-- sym-bc @02142041: 2 steps
lem-sym-bc-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-sym-bc-at02142041 c4 = derive (Bx2-4031 ∷ []) (Bx2-4301 ∷ [])
  (rw⁻ 0 (q324 c4) ∷
   rw 0 (q325 c4) ∷ []) Eq.refl

private
  q326 : Ws → Eqn
  q326 c4 = eqn (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) (Bx3-4021 ∷ []) (lem-SWbc-box-at0314203241 c4)
  q327 : Ws → Eqn
  q327 c4 = eqn (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) (Bx3-4201 ∷ []) (lem-nat-SWbc-at0314203241 c4)

-- sym-bc @0314203241: 2 steps
lem-sym-bc-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-sym-bc-at0314203241 c4 = derive (Bx3-4021 ∷ []) (Bx3-4201 ∷ [])
  (rw⁻ 0 (q326 c4) ∷
   rw 0 (q327 c4) ∷ []) Eq.refl

private
  q328 : Ws → Eqn
  q328 c4 = eqn (Toff201 ∷ Bx2-4301 ∷ Toff201 ∷ []) (Bx2-4301 ∷ []) (lem-P-box-at0214233041 c4)
  q329 : Ws → Eqn
  q329 c4 = eqn (Bx2-4301 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4)
  q330 : Ws → Eqn
  q330 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4)

-- pairs @0214233041: 4 steps
lem-pairs-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-pairs-at0214233041 c4 = derive (Bx2-4301 ∷ []) (Bx2-0143 ∷ [])
  (rw⁻ 0 (q328 c4) ∷
   rw 1 (q329 c4) ∷
   rw 4 (q211 c4) ∷
   rw⁻ 0 (q330 c4) ∷ []) Eq.refl

private
  q331 : Ws → Eqn
  q331 c4 = eqn (Toff234 ∷ Bx2-0143 ∷ Toff234 ∷ []) (Bx2-0143 ∷ []) (lem-P-box-at0210213443 c4)
  q332 : Ws → Eqn
  q332 c4 = eqn (Bx2-0143 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0210213443 c4)
  q333 : Ws → Eqn
  q333 c4 = eqn (Bx2-4301 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0214233041 c4)

-- pairs @0210213443: 4 steps
lem-pairs-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-pairs-at0210213443 c4 = derive (Bx2-0143 ∷ []) (Bx2-4301 ∷ [])
  (rw⁻ 0 (q331 c4) ∷
   rw 1 (q332 c4) ∷
   rw 4 (q205 c4) ∷
   rw⁻ 0 (q333 c4) ∷ []) Eq.refl

private
  q334 : Ws → Eqn
  q334 c4 = eqn (Bx2-3401 ∷ []) (Bx2-4301 ∷ []) (lem-sym-ab-at0213243041 c4)
  q335 : Ws → Eqn
  q335 c4 = eqn (Bx2-4301 ∷ []) (Bx2-4031 ∷ []) (lem-sym-bc-at0214233041 c4)

-- box-perm-2314 @0213243041: 2 steps
lem-box-perm-2314-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-box-perm-2314-at0213243041 c4 = derive (Bx2-3401 ∷ []) (Bx2-4031 ∷ [])
  (rw 0 (q334 c4) ∷
   rw 0 (q335 c4) ∷ []) Eq.refl

private
  q336 : Ws → Eqn
  q336 c4 = eqn (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) (Bx2-3104 ∷ []) (lem-SWbc-box-at02132130 c4)
  q337 : Ws → Eqn
  q337 c4 = eqn (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) (Bx2-3014 ∷ []) (lem-nat-SWbc-at02132130 c4)

-- sym-bc @02132130: 2 steps
lem-sym-bc-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-sym-bc-at02132130 c4 = derive (Bx2-3104 ∷ []) (Bx2-3014 ∷ [])
  (rw⁻ 0 (q336 c4) ∷
   rw 0 (q337 c4) ∷ []) Eq.refl

private
  q338 : Ws → Eqn
  q338 c4 = eqn (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-QVQ-at03143041 c4)
  q339 : Ws → Eqn
  q339 c4 = eqn (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143041 c4)

-- box-cP @03143041: 12 steps
lem-box-cP-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-box-cP-at03143041 c4 = derive (Bx3-4201 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q238 c4) ∷
   re 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q238 c4) ∷
   rw 2 (q338 c4) ∷
   rw 1 (q339 c4) ∷
   rw 2 (q190 c4) ∷ []) Eq.refl

private
  q340 : Ws → Eqn
  q340 c4 = eqn (CCZ123 ∷ Toff312 ∷ CZ34 ∷ Toff312 ∷ CCZ123 ∷ CZ34 ∷ []) (CCZ124 ∷ []) (wl 1341 (lit c4))
  q341 : Ws → Eqn
  q341 c4 = eqn (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-QVQ-at02132031 c4)
  q342 : Ws → Eqn
  q342 c4 = eqn (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ []) (lem-tP-at02132031 c4)

-- box-cP @02132031: 12 steps
lem-box-cP-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at02132031 c4 = derive (Bx2-3014 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw 2 (q340 c4) ∷
   re 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw 5 (q340 c4) ∷
   rw 2 (q341 c4) ∷
   rw 1 (q342 c4) ∷
   rw 2 (q147 c4) ∷ []) Eq.refl

private
  q343 : Ws → Eqn
  q343 c4 = eqn (Toff324 ∷ Bx3-0142 ∷ Toff324 ∷ []) (Bx3-0142 ∷ []) (lem-P-box-at0310213442 c4)
  q344 : Ws → Eqn
  q344 c4 = eqn (Bx3-0142 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at0310213442 c4)
  q345 : Ws → Eqn
  q345 c4 = eqn (Bx3-4201 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143041 c4)

-- pairs @0310213442: 4 steps
lem-pairs-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-pairs-at0310213442 c4 = derive (Bx3-0142 ∷ []) (Bx3-4201 ∷ [])
  (rw⁻ 0 (q343 c4) ∷
   rw 1 (q344 c4) ∷
   rw 4 (q190 c4) ∷
   rw⁻ 0 (q345 c4) ∷ []) Eq.refl

private
  q346 : Ws → Eqn
  q346 c4 = eqn (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) (Bx2-3014 ∷ []) (lem-SWbc-box-at02132031 c4)
  q347 : Ws → Eqn
  q347 c4 = eqn (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) (Bx2-3104 ∷ []) (lem-nat-SWbc-at02132031 c4)

-- sym-bc @02132031: 2 steps
lem-sym-bc-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-sym-bc-at02132031 c4 = derive (Bx2-3014 ∷ []) (Bx2-3104 ∷ [])
  (rw⁻ 0 (q346 c4) ∷
   rw 0 (q347 c4) ∷ []) Eq.refl

private
  q348 : Ws → Eqn
  q348 c4 = eqn (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-QVQ-at02132130 c4)
  q349 : Ws → Eqn
  q349 c4 = eqn (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ []) (lem-tP-at02132130 c4)

-- box-cP @02132130: 12 steps
lem-box-cP-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-box-cP-at02132130 c4 = derive (Bx2-3104 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw 2 (q32 c4) ∷
   re 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw 5 (q32 c4) ∷
   rw 2 (q348 c4) ∷
   rw 1 (q349 c4) ∷
   rw 2 (q215 c4) ∷ []) Eq.refl

private
  q350 : Ws → Eqn
  q350 c4 = eqn (Toff201 ∷ Bx2-3401 ∷ Toff201 ∷ []) (Bx2-3401 ∷ []) (lem-P-box-at0213243041 c4)
  q351 : Ws → Eqn
  q351 c4 = eqn (Bx2-3401 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4)
  q352 : Ws → Eqn
  q352 c4 = eqn (Bx2-0134 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at021021 c4)

-- pairs @0213243041: 4 steps
lem-pairs-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-pairs-at0213243041 c4 = derive (Bx2-3401 ∷ []) (Bx2-0134 ∷ [])
  (rw⁻ 0 (q350 c4) ∷
   rw 1 (q351 c4) ∷
   rw 4 (q211 c4) ∷
   rw⁻ 0 (q352 c4) ∷ []) Eq.refl

private
  q353 : Ws → Eqn
  q353 c4 = eqn (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) (Bx3-2104 ∷ []) (lem-SWbc-box-at03122130 c4)
  q354 : Ws → Eqn
  q354 c4 = eqn (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) (Bx3-2014 ∷ []) (lem-nat-SWbc-at03122130 c4)

-- sym-bc @03122130: 2 steps
lem-sym-bc-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-sym-bc-at03122130 c4 = derive (Bx3-2104 ∷ []) (Bx3-2014 ∷ [])
  (rw⁻ 0 (q353 c4) ∷
   rw 0 (q354 c4) ∷ []) Eq.refl

private
  q355 : Ws → Eqn
  q355 c4 = eqn (Toff234 ∷ Bx2-0134 ∷ Toff234 ∷ []) (Bx2-0134 ∷ []) (lem-P-box-at021021 c4)
  q356 : Ws → Eqn
  q356 c4 = eqn (Bx2-0134 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at021021 c4)
  q357 : Ws → Eqn
  q357 c4 = eqn (Bx2-3401 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0213243041 c4)

-- pairs @021021: 4 steps
lem-pairs-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-pairs-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-3401 ∷ [])
  (rw⁻ 0 (q355 c4) ∷
   rw 1 (q356 c4) ∷
   rw 4 (q205 c4) ∷
   rw⁻ 0 (q357 c4) ∷ []) Eq.refl

private
  q358 : Ws → Eqn
  q358 c4 = eqn (CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ []) (CCZ134 ∷ []) (wl 1303 (lit c4))
  q359 : Ws → Eqn
  q359 c4 = eqn (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-QVQ-at03122031 c4)
  q360 : Ws → Eqn
  q360 c4 = eqn (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ []) (lem-tP-at03122031 c4)

-- box-cP @03122031: 12 steps
lem-box-cP-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-box-cP-at03122031 c4 = derive (Bx3-2014 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw 2 (q358 c4) ∷
   re 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw 5 (q358 c4) ∷
   rw 2 (q359 c4) ∷
   rw 1 (q360 c4) ∷
   rw 2 (q301 c4) ∷ []) Eq.refl

private
  q361 : Ws → Eqn
  q361 c4 = eqn (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) (Bx3-2014 ∷ []) (lem-SWbc-box-at03122031 c4)
  q362 : Ws → Eqn
  q362 c4 = eqn (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) (Bx3-2104 ∷ []) (lem-nat-SWbc-at03122031 c4)

-- sym-bc @03122031: 2 steps
lem-sym-bc-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-sym-bc-at03122031 c4 = derive (Bx3-2014 ∷ []) (Bx3-2104 ∷ [])
  (rw⁻ 0 (q361 c4) ∷
   rw 0 (q362 c4) ∷ []) Eq.refl

private
  q363 : Ws → Eqn
  q363 c4 = eqn (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-QVQ-at03122130 c4)
  q364 : Ws → Eqn
  q364 c4 = eqn (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ []) (lem-tP-at03122130 c4)

-- box-cP @03122130: 12 steps
lem-box-cP-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-box-cP-at03122130 c4 = derive (Bx3-2104 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw 2 (q21 c4) ∷
   re 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw 5 (q21 c4) ∷
   rw 2 (q363 c4) ∷
   rw 1 (q364 c4) ∷
   rw 2 (q100 c4) ∷ []) Eq.refl
