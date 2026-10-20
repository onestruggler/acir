{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D025 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym-ab ; lem-sym-ab-at0210233441 ; lem-sym-ab-at0210243143 ; lem-sym-ab-at0213203441 ; lem-sym-ab-at03102132 ; lem-sym-ab-at0310243142 ; lem-sym-ab-at0314203142 ; lem-sym-ab-at032032 ; lem-sym-ab-at033440 ; lem-sym-ab-at1221 ; lem-sym-ab-at122331 ; lem-sym-ab-at12243143 ; lem-sym-ab-at13213442 ; lem-sym-ab-at13243142 ; lem-sym-ab-at13243241 ; lem-sym-ab-at133441 ; lem-sym-ab-at14233142 ; lem-sym-ab-at2332 ; lem-sym-ab-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym-ab-at021021 ; lem-sym-ab-at0220 ; lem-sym-ab-at132132 ; lem-sym-ab-at1331 ; lem-sym-ab-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0314213042 ; lem-box-tQ-at043043 ; lem-box-tQ-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at02233440)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-CSdu-box-1 ; lem-CSdu-box-2 ; lem-CSdu-box-2-at0210243143 ; lem-CSdu-box-2-at122441 ; lem-CSdu-box-2-at243243 ; lem-CSu-box-1 ; lem-CSu-box-2 ; lem-CSu-box-2-at122441 ; lem-CSu-box-2-at243243 ; lem-Sdu-box ; lem-Su-box)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-CSu-box-2-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-box-cP-at0210213443 ; lem-sym-bc-at0220 ; lem-sym-bc-at032032 ; lem-sym-bc-at13243142 ; lem-sym-bc-at13243241 ; lem-sym-bc-at14233142)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0210243143 ; lem-box-cP-at1221 ; lem-box-cP-at12213443 ; lem-box-cP-at12233441 ; lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box-cP-at3443 ; lem-pairs-at13243142 ; lem-pairs-at14233142 ; lem-sym-bc ; lem-sym-bc-at0214203143 ; lem-sym-bc-at022330 ; lem-sym-bc-at0312213440 ; lem-sym-bc-at0330 ; lem-sym-bc-at1221 ; lem-sym-bc-at122331 ; lem-sym-bc-at12233441 ; lem-sym-bc-at12243143 ; lem-sym-bc-at122441 ; lem-sym-bc-at132132 ; lem-sym-bc-at1331 ; lem-sym-bc-at14213243 ; lem-sym-bc-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-CSdu-box-3 ; lem-CSdu-box-3-at043043 ; lem-CSdu-box-4 ; lem-CSu-box-3 ; lem-CSu-box-4 ; lem-Kdu-box ; lem-Kdu-box-at0210243143 ; lem-Kdu-box-at122441 ; lem-Kdu-box-at243243 ; lem-Ku-box ; lem-Ku-box-at0210243143 ; lem-Ku-box-at122441 ; lem-Ku-box-at243243 ; lem-Xb-box-at0210243143 ; lem-Xb-box-at122441 ; lem-Xb-box-at243243 ; lem-box-perm-1324-at0210243143 ; lem-box-perm-1324-at122441 ; lem-box-perm-1324-at243243 ; lem-box-perm-1423-at122441 ; lem-box2-at0210243143 ; lem-box2-at122441 ; lem-box2-at243243 ; lem-pairs ; lem-pairs-at0214213043 ; lem-pairs-at0310243142 ; lem-pairs-at0330 ; lem-pairs-at1221 ; lem-pairs-at122331 ; lem-pairs-at132132 ; lem-pairs-at13213442 ; lem-pairs-at1331 ; lem-pairs-at143143 ; lem-pairs-at2332 ; lem-pairs-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-CSdu-box-3-at0314213042 ; lem-CXu-box-4-at0210243143 ; lem-box-perm-2341-at021021 ; lem-box-perm-4123-at02233440 ; lem-pairs-at0210233441 ; lem-pairs-at0210243143 ; lem-pairs-at022330 ; lem-pairs-at0312243140 ; lem-pairs-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-pairs-at12233441 ; lem-pairs-at122441 ; lem-pairs-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS03-TOFF412 ; lem-comm-CS13-CCZ024 ; lem-comm-CS23-CCZ014 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX04-TOFF213 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-TOFF023 ; lem-comm-CX23-CCZ014 ; lem-comm-CX24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CK41-CCZ023 ; lem-comm-CK41-TOFF023 ; lem-comm-CS02-TOFF314 ; lem-comm-CX21-TOFF034 ; lem-comm-TOFF214-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CCZ023-CK41)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb⁻2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Sb⁻2-0-3-1 ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (X))
  q2 : Ws → Eqn
  q2 c4 = eqn (Toff314 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ Toff314 ∷ []) (wl 187 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Sb2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Sb2-0-3-1 ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) (X))
  q4 : Ws → Eqn
  q4 c4 = eqn (CS03 ∷ CX13 ∷ []) (CX13 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ []) (wl 188 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CX13 ∷ Toff314 ∷ []) (Toff314 ∷ CX13 ∷ []) (wl 189 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CS01 ∷ Toff314 ∷ []) (Toff314 ∷ CS01 ∷ []) (wp 29 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ013 ∷ []) (wp 30 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X4 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) (X4 ∷ CX13 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp 31 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ Bx2-0413 ∷ X4 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ []) (lem-Xb-box-at0210243143 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx2-0413 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp 32 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl 190 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) (wp 33 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp 34 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) (wp 35 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp 36 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) (wp 37 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp 21 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) (wp 38 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl 184 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ024 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ []) (wp 22 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS13⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) (wp 39 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) (wp 40 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ []) (wl 191 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ Toff213 ∷ []) (wl 192 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp 41 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) (wl 193 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CX04 ∷ Toff213 ∷ []) (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS14⁻ ∷ []) (wl 194 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) (wl 195 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) (wl 196 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (Toff214 ∷ CCZ024 ∷ []) (wp 42 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ014 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ []) (wp 43 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Toff213 ∷ Toff214 ∷ []) (Toff214 ∷ Toff213 ∷ []) (wl 197 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Toff214 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ []) (wl 198 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ014 ∷ []) (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) (wp 44 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx2-0413 ∷ Bx2-0413 ∷ []) [] (lem-box2-at0210243143 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CS01 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp 45 c4)

-- F5-01: 112 steps
lem-F5-01 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-F5-01 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   re 4 1 (CS03 ∷ []) ∷
   rw 4 (q4 c4) ∷
   re 7 1 (Sb2-0-3-1 ∷ []) ∷
   rw 2 (q2 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 2 (q8 c4) ∷
   rw 0 (q9 c4) ∷
   rw 9 (q10 c4) ∷
   re 8 1 (CS03⁻ ∷ []) ∷
   rw⁻ 8 (q11 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw⁻ 13 (q13 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw 11 (q15 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw 9 (q15 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw 8 (q12 c4) ∷
   re 6 1 (CS03 ∷ []) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw 9 (q15 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw 7 (q15 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw 6 (q12 c4) ∷
   rw 4 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw 5 (q23 c4) ∷
   rw⁻ 4 (q22 c4) ∷
   rw 3 (q24 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw⁻ 2 (q25 c4) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 4 (q22 c4) ∷
   rw 3 (q23 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q24 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   rw 2 (q26 c4) ∷
   rw 7 (q27 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 5 (q29 c4) ∷
   rw 9 (q30 c4) ∷
   rw 8 (q31 c4) ∷
   rw 7 (q32 c4) ∷
   rw 6 (q31 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 6 (q29 c4) ∷
   rw 4 (q34 c4) ∷
   rw 3 (q30 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw⁻ 10 (q11 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 15 (q13 c4) ∷
   rw⁻ 14 (q14 c4) ∷
   rw 13 (q15 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw 11 (q15 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw⁻ 9 (q18 c4) ∷
   rw 10 (q12 c4) ∷
   rw⁻ 8 (q35 c4) ∷
   rw 7 (q20 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw 8 (q15 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   rw 5 (q36 c4) ∷
   rw 11 (q27 c4) ∷
   rw⁻ 10 (q28 c4) ∷
   rw 9 (q29 c4) ∷
   rw 13 (q30 c4) ∷
   rw 12 (q31 c4) ∷
   rw 11 (q32 c4) ∷
   rw 10 (q31 c4) ∷
   rw 9 (q33 c4) ∷
   rw⁻ 10 (q29 c4) ∷
   rw⁻ 8 (q37 c4) ∷
   rw 7 (q34 c4) ∷
   rw 6 (q30 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw⁻ 8 (q39 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw 0 (q40 c4) ∷
   re 7 1 (CS03 ∷ []) ∷
   re 9 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q41 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = eqn (Sb⁻0-1-3-2 ∷ X4 ∷ []) (X4 ∷ Sb⁻0-1-3-2 ∷ []) (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (X))
  q43 : Ws → Eqn
  q43 c4 = eqn (Toff324 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ Toff324 ∷ []) (wl 211 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (Sb0-1-3-2 ∷ X4 ∷ []) (X4 ∷ Sb0-1-3-2 ∷ []) (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))
  q45 : Ws → Eqn
  q45 c4 = eqn (CS13 ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ []) (wl 212 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CX23 ∷ Toff324 ∷ []) (Toff324 ∷ CX23 ∷ []) (wl 213 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CS12 ∷ Toff324 ∷ []) (Toff324 ∷ CS12 ∷ []) (wl 214 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ123 ∷ []) (wl 215 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (X4 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) (X4 ∷ CX23 ∷ CX23 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl 216 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (X4 ∷ Bx0-1423 ∷ X4 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ []) (lem-Xb-box-at243243 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) (wp 60 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) (wl 217 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ []) (wp 61 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) (wp 62 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CX23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) (wp 63 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) (wp 64 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ []) (wp 65 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp 53 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) (wp 66 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl 207 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ014 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ []) (wp 54 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CS23⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (CS23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) (wp 67 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ []) (wl 218 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CS13⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS13⁻ ∷ []) (wl 219 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ Toff023 ∷ []) (wp 68 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl 220 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) (wl 221 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (CX14 ∷ Toff023 ∷ []) (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ []) (wp 69 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) (wp 70 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) (wl 222 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (Toff024 ∷ CCZ014 ∷ []) (wp 71 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (CCZ124 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ []) (Toff324 ∷ CS12 ∷ CS13 ∷ []) (wl 223 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ []) (wp 72 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (Toff024 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ []) (wp 73 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (CCZ124 ∷ []) (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) (wp 74 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (Bx0-1423 ∷ Bx0-1423 ∷ []) [] (lem-box2-at243243 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (CS12 ∷ []) (Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (wl 224 (lit c4))

-- F5-12: 112 steps
lem-F5-12 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-F5-12 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw 5 (q42 c4) ∷
   rw 4 (q43 c4) ∷
   rw 3 (q44 c4) ∷
   re 4 1 (CS13 ∷ []) ∷
   rw 4 (q45 c4) ∷
   re 7 1 (Sb0-1-3-2 ∷ []) ∷
   rw 2 (q43 c4) ∷
   rw⁻ 4 (q46 c4) ∷
   rw⁻ 5 (q47 c4) ∷
   rw⁻ 6 (q48 c4) ∷
   rw⁻ 2 (q49 c4) ∷
   rw 0 (q50 c4) ∷
   rw 9 (q51 c4) ∷
   re 8 1 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q52 c4) ∷
   rw⁻ 7 (q53 c4) ∷
   rw⁻ 13 (q54 c4) ∷
   rw⁻ 12 (q55 c4) ∷
   rw 11 (q56 c4) ∷
   rw⁻ 10 (q57 c4) ∷
   rw 9 (q56 c4) ∷
   rw⁻ 8 (q58 c4) ∷
   rw⁻ 7 (q59 c4) ∷
   rw 8 (q53 c4) ∷
   re 6 1 (CS13 ∷ []) ∷
   rw⁻ 6 (q60 c4) ∷
   rw⁻ 5 (q53 c4) ∷
   rw⁻ 11 (q54 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   rw 9 (q56 c4) ∷
   rw⁻ 8 (q57 c4) ∷
   rw 7 (q56 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 6 (q53 c4) ∷
   rw⁻ 4 (q61 c4) ∷
   rw 3 (q62 c4) ∷
   rw⁻ 7 (q60 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   rw 5 (q64 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw⁻ 2 (q66 c4) ∷
   rw 1 (q62 c4) ∷
   rw⁻ 5 (q60 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   rw 3 (q64 c4) ∷
   rw⁻ 2 (q63 c4) ∷
   rw 1 (q65 c4) ∷
   rw⁻ 2 (q62 c4) ∷
   rw 2 (q67 c4) ∷
   rw 7 (q68 c4) ∷
   rw⁻ 6 (q69 c4) ∷
   rw 5 (q70 c4) ∷
   rw 9 (q71 c4) ∷
   rw 8 (q72 c4) ∷
   rw 7 (q73 c4) ∷
   rw 6 (q72 c4) ∷
   rw 5 (q74 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw 4 (q75 c4) ∷
   rw 3 (q71 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   rw⁻ 10 (q52 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   rw⁻ 15 (q54 c4) ∷
   rw⁻ 14 (q55 c4) ∷
   rw 13 (q56 c4) ∷
   rw⁻ 12 (q57 c4) ∷
   rw 11 (q56 c4) ∷
   rw⁻ 10 (q58 c4) ∷
   rw⁻ 9 (q59 c4) ∷
   rw 10 (q53 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw⁻ 7 (q61 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   rw⁻ 5 (q66 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw⁻ 10 (q54 c4) ∷
   rw⁻ 9 (q55 c4) ∷
   rw 8 (q56 c4) ∷
   rw⁻ 7 (q57 c4) ∷
   rw 6 (q56 c4) ∷
   rw⁻ 5 (q58 c4) ∷
   rw⁻ 4 (q59 c4) ∷
   rw 5 (q53 c4) ∷
   rw⁻ 3 (q76 c4) ∷
   rw 5 (q77 c4) ∷
   rw 11 (q68 c4) ∷
   rw⁻ 10 (q69 c4) ∷
   rw 9 (q70 c4) ∷
   rw 13 (q71 c4) ∷
   rw 12 (q72 c4) ∷
   rw 11 (q73 c4) ∷
   rw 10 (q72 c4) ∷
   rw 9 (q74 c4) ∷
   rw⁻ 10 (q70 c4) ∷
   rw⁻ 8 (q78 c4) ∷
   rw 7 (q75 c4) ∷
   rw 6 (q71 c4) ∷
   rw⁻ 5 (q69 c4) ∷
   rw⁻ 4 (q78 c4) ∷
   rw 5 (q79 c4) ∷
   rw⁻ 8 (q80 c4) ∷
   rw⁻ 1 (q51 c4) ∷
   rw 0 (q81 c4) ∷
   re 7 1 (CS13 ∷ []) ∷
   re 9 1 (CS13⁻ ∷ []) ∷
   rw⁻ 0 (q82 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = eqn (Sb⁻0-2-1-3 ∷ X4 ∷ []) (X4 ∷ Sb⁻0-2-1-3 ∷ []) (c₃ ((CS • CS • CS) ↑) (X ↑))
  q84 : Ws → Eqn
  q84 c4 = eqn (Toff134 ∷ X4 ∷ []) (X4 ∷ CX31 ∷ Toff134 ∷ []) (wl 235 (lit c4))
  q85 : Ws → Eqn
  q85 c4 = eqn (Sb0-2-1-3 ∷ X4 ∷ []) (X4 ∷ Sb0-2-1-3 ∷ []) (c₃ (CS ↑) (X ↑))
  q86 : Ws → Eqn
  q86 c4 = eqn (CS12 ∷ CX31 ∷ []) (CX31 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ []) (wl 236 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (CX31 ∷ Toff134 ∷ []) (Toff134 ∷ CX31 ∷ []) (wl 237 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (CS23 ∷ Toff134 ∷ []) (Toff134 ∷ CS23 ∷ []) (wl 238 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ123 ∷ CCZ234 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ123 ∷ []) (wl 239 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (X4 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ []) (X4 ∷ CX31 ∷ CX31 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl 240 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (X4 ∷ Bx0-2431 ∷ X4 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ []) (lem-Xb-box-at122441 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) (wp 87 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) (wl 241 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) (wp 88 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) (wp 89 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp 81 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) (wp 90 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl 242 (lit c4))
  q100 : Ws → Eqn
  q100 c4 = eqn (CCZ024 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ024 ∷ []) (wp 91 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) (wp 92 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ []) (wl 243 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (CS12⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS12⁻ ∷ []) (wl 244 (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (Toff134 ∷ Toff013 ∷ []) (wp 93 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl 245 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) (wl 246 (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (CX24 ∷ Toff013 ∷ []) (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS34⁻ ∷ []) (wp 94 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) (wp 95 c4)
  q110 : Ws → Eqn
  q110 c4 = eqn (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) (wl 247 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (Toff034 ∷ CCZ024 ∷ []) (wp 96 c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (CCZ234 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ []) (Toff134 ∷ CS12 ∷ CS23 ∷ []) (wl 248 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (Toff013 ∷ Toff034 ∷ []) (Toff034 ∷ Toff013 ∷ []) (wp 97 c4)
  q114 : Ws → Eqn
  q114 c4 = eqn (CS23 ∷ CCZ234 ∷ []) (CS23 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) (wp 98 c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (Toff034 ∷ Toff034 ∷ Toff134 ∷ []) (Toff134 ∷ []) (wp 99 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (Bx0-2431 ∷ Bx0-2431 ∷ []) [] (lem-box2-at122441 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (CS23 ∷ []) (Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (wl 249 (lit c4))

-- F5-23: 112 steps
lem-F5-23 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-F5-23 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw 5 (q83 c4) ∷
   rw 4 (q84 c4) ∷
   rw 3 (q85 c4) ∷
   re 4 1 (CS12 ∷ []) ∷
   rw 4 (q86 c4) ∷
   re 7 1 (Sb0-2-1-3 ∷ []) ∷
   rw 2 (q84 c4) ∷
   rw⁻ 4 (q87 c4) ∷
   rw⁻ 5 (q88 c4) ∷
   rw⁻ 6 (q89 c4) ∷
   rw⁻ 2 (q90 c4) ∷
   rw 0 (q91 c4) ∷
   rw 9 (q92 c4) ∷
   re 8 1 (CS12⁻ ∷ []) ∷
   rw⁻ 8 (q93 c4) ∷
   rw⁻ 7 (q94 c4) ∷
   rw⁻ 13 (q95 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw 11 (q15 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw 9 (q15 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw⁻ 7 (q96 c4) ∷
   rw 8 (q94 c4) ∷
   re 6 1 (CS12 ∷ []) ∷
   rw⁻ 6 (q97 c4) ∷
   rw⁻ 5 (q94 c4) ∷
   rw⁻ 11 (q95 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw 9 (q15 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw 7 (q15 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw⁻ 5 (q96 c4) ∷
   rw 6 (q94 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw 3 (q99 c4) ∷
   rw⁻ 7 (q97 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 5 (q100 c4) ∷
   rw 4 (q15 c4) ∷
   rw⁻ 3 (q101 c4) ∷
   rw⁻ 4 (q99 c4) ∷
   rw⁻ 2 (q101 c4) ∷
   rw 1 (q99 c4) ∷
   rw⁻ 5 (q97 c4) ∷
   rw 4 (q15 c4) ∷
   rw⁻ 3 (q100 c4) ∷
   rw 2 (q15 c4) ∷
   rw⁻ 1 (q101 c4) ∷
   rw⁻ 2 (q99 c4) ∷
   rw 2 (q102 c4) ∷
   rw 7 (q103 c4) ∷
   rw⁻ 6 (q104 c4) ∷
   rw 5 (q105 c4) ∷
   rw 9 (q106 c4) ∷
   rw 8 (q107 c4) ∷
   rw 7 (q108 c4) ∷
   rw 6 (q107 c4) ∷
   rw 5 (q109 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   rw 4 (q106 c4) ∷
   rw 3 (q110 c4) ∷
   rw⁻ 2 (q104 c4) ∷
   rw⁻ 10 (q93 c4) ∷
   rw⁻ 9 (q94 c4) ∷
   rw⁻ 15 (q95 c4) ∷
   rw⁻ 14 (q14 c4) ∷
   rw 13 (q15 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw 11 (q15 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw⁻ 9 (q96 c4) ∷
   rw 10 (q94 c4) ∷
   rw⁻ 8 (q111 c4) ∷
   rw⁻ 7 (q98 c4) ∷
   rw⁻ 6 (q101 c4) ∷
   rw⁻ 5 (q97 c4) ∷
   rw⁻ 4 (q94 c4) ∷
   rw⁻ 10 (q95 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw 8 (q15 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw 5 (q94 c4) ∷
   rw⁻ 3 (q111 c4) ∷
   rw 5 (q112 c4) ∷
   rw 11 (q103 c4) ∷
   rw⁻ 10 (q104 c4) ∷
   rw 9 (q105 c4) ∷
   rw 13 (q106 c4) ∷
   rw 12 (q107 c4) ∷
   rw 11 (q108 c4) ∷
   rw 10 (q107 c4) ∷
   rw 9 (q109 c4) ∷
   rw⁻ 10 (q105 c4) ∷
   rw⁻ 8 (q113 c4) ∷
   rw 7 (q106 c4) ∷
   rw 6 (q110 c4) ∷
   rw⁻ 5 (q104 c4) ∷
   rw⁻ 4 (q113 c4) ∷
   rw⁻ 9 (q114 c4) ∷
   rw 5 (q115 c4) ∷
   rw⁻ 1 (q92 c4) ∷
   rw 0 (q116 c4) ∷
   re 7 1 (CS12 ∷ []) ∷
   re 9 1 (CS12⁻ ∷ []) ∷
   rw⁻ 0 (q117 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = eqn (Bx0-1234 ∷ []) (Bx0-3412 ∷ []) (lem-pairs c4)

-- box-perm-3412: 1 steps
lem-box-perm-3412 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-box-perm-3412 c4 = derive (Bx0-1234 ∷ []) (Bx0-3412 ∷ [])
  (rw 0 (q118 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = eqn (Bx0-1234 ∷ []) (Bx0-2134 ∷ []) (lem-sym-ab c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (Bx0-2134 ∷ []) (Bx0-3421 ∷ []) (lem-pairs-at1221 c4)

-- box-perm-3421: 2 steps
lem-box-perm-3421 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-box-perm-3421 c4 = derive (Bx0-1234 ∷ []) (Bx0-3421 ∷ [])
  (rw 0 (q119 c4) ∷
   rw 0 (q120 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1324 ∷ []) (lem-sym-bc c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (Bx0-1324 ∷ []) (Bx0-2413 ∷ []) (lem-pairs-at2332 c4)

-- box-perm-2413: 2 steps
lem-box-perm-2413 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-box-perm-2413 c4 = derive (Bx0-1234 ∷ []) (Bx0-2413 ∷ [])
  (rw 0 (q121 c4) ∷
   rw 0 (q122 c4) ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = eqn (Bx0-3412 ∷ []) (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4)

-- box-perm-4312: 2 steps
lem-box-perm-4312 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-box-perm-4312 c4 = derive (Bx0-1234 ∷ []) (Bx0-4312 ∷ [])
  (rw 0 (q118 c4) ∷
   rw 0 (q123 c4) ∷ []) Eq.refl

private
  q124 : Ws → Eqn
  q124 c4 = eqn (Bx0-3412 ∷ []) (Bx0-3142 ∷ []) (lem-sym-bc-at13243142 c4)

-- box-perm-3142: 2 steps
lem-box-perm-3142 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-3142 c4 = derive (Bx0-1234 ∷ []) (Bx0-3142 ∷ [])
  (rw 0 (q118 c4) ∷
   rw 0 (q124 c4) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (Bx0-2314 ∷ []) (Bx0-1423 ∷ []) (lem-pairs-at122331 c4)

-- box-perm-1423: 3 steps
lem-box-perm-1423 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-1423 c4 = derive (Bx0-1234 ∷ []) (Bx0-1423 ∷ [])
  (rw 0 (q119 c4) ∷
   rw 0 (q125 c4) ∷
   rw 0 (q126 c4) ∷ []) Eq.refl

private
  q127 : Ws → Eqn
  q127 c4 = eqn (Bx0-3421 ∷ []) (Bx0-4321 ∷ []) (lem-sym-ab-at13243241 c4)

-- box-perm-4321: 3 steps
lem-box-perm-4321 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-box-perm-4321 c4 = derive (Bx0-1234 ∷ []) (Bx0-4321 ∷ [])
  (rw 0 (q119 c4) ∷
   rw 0 (q120 c4) ∷
   rw 0 (q127 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (Bx0-3421 ∷ []) (Bx0-3241 ∷ []) (lem-sym-bc-at13243241 c4)

-- box-perm-3241: 3 steps
lem-box-perm-3241 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-box-perm-3241 c4 = derive (Bx0-1234 ∷ []) (Bx0-3241 ∷ [])
  (rw 0 (q119 c4) ∷
   rw 0 (q120 c4) ∷
   rw 0 (q128 c4) ∷ []) Eq.refl

private
  q129 : Ws → Eqn
  q129 c4 = eqn (Bx0-1324 ∷ []) (Bx0-3124 ∷ []) (lem-sym-ab-at2332 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (Bx0-3124 ∷ []) (Bx0-2431 ∷ []) (lem-pairs-at132132 c4)

-- box-perm-2431: 3 steps
lem-box-perm-2431 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-2431 c4 = derive (Bx0-1234 ∷ []) (Bx0-2431 ∷ [])
  (rw 0 (q121 c4) ∷
   rw 0 (q129 c4) ∷
   rw 0 (q130 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = eqn (Bx0-2413 ∷ []) (Bx0-4213 ∷ []) (lem-sym-ab-at12243143 c4)

-- box-perm-4213: 3 steps
lem-box-perm-4213 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-box-perm-4213 c4 = derive (Bx0-1234 ∷ []) (Bx0-4213 ∷ [])
  (rw 0 (q121 c4) ∷
   rw 0 (q122 c4) ∷
   rw 0 (q131 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2143 ∷ []) (lem-sym-bc-at12243143 c4)

-- box-perm-2143: 3 steps
lem-box-perm-2143 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-box-perm-2143 c4 = derive (Bx0-1234 ∷ []) (Bx0-2143 ∷ [])
  (rw 0 (q121 c4) ∷
   rw 0 (q122 c4) ∷
   rw 0 (q132 c4) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = eqn (Bx0-4312 ∷ []) (Bx0-4132 ∷ []) (lem-sym-bc-at14233142 c4)

-- box-perm-4132: 3 steps
lem-box-perm-4132 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-box-perm-4132 c4 = derive (Bx0-1234 ∷ []) (Bx0-4132 ∷ [])
  (rw 0 (q118 c4) ∷
   rw 0 (q123 c4) ∷
   rw 0 (q133 c4) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = eqn (Bx0-4312 ∷ []) (Bx0-1243 ∷ []) (lem-pairs-at14233142 c4)

-- box-perm-1243: 3 steps
lem-box-perm-1243 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-box-perm-1243 c4 = derive (Bx0-1234 ∷ []) (Bx0-1243 ∷ [])
  (rw 0 (q118 c4) ∷
   rw 0 (q123 c4) ∷
   rw 0 (q134 c4) ∷ []) Eq.refl

private
  q135 : Ws → Eqn
  q135 c4 = eqn (Bx0-3142 ∷ []) (Bx0-1342 ∷ []) (lem-sym-ab-at13213442 c4)

-- box-perm-1342: 3 steps
lem-box-perm-1342 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-box-perm-1342 c4 = derive (Bx0-1234 ∷ []) (Bx0-1342 ∷ [])
  (rw 0 (q118 c4) ∷
   rw 0 (q124 c4) ∷
   rw 0 (q135 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = eqn (Bx0-3142 ∷ []) (Bx0-4231 ∷ []) (lem-pairs-at13213442 c4)

-- box-perm-4231: 3 steps
lem-box-perm-4231 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-box-perm-4231 c4 = derive (Bx0-1234 ∷ []) (Bx0-4231 ∷ [])
  (rw 0 (q118 c4) ∷
   rw 0 (q124 c4) ∷
   rw 0 (q136 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = eqn (Bx0-2314 ∷ []) (Bx0-3214 ∷ []) (lem-sym-ab-at122331 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (Bx0-3214 ∷ []) (Bx0-1432 ∷ []) (lem-pairs-at1331 c4)

-- box-perm-1432: 4 steps
lem-box-perm-1432 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-box-perm-1432 c4 = derive (Bx0-1234 ∷ []) (Bx0-1432 ∷ [])
  (rw 0 (q119 c4) ∷
   rw 0 (q125 c4) ∷
   rw 0 (q137 c4) ∷
   rw 0 (q138 c4) ∷ []) Eq.refl

private
  q139 : Ws → Eqn
  q139 c4 = eqn (Bx0-1423 ∷ []) (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4)

-- box-perm-4123: 4 steps
lem-box-perm-4123 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-box-perm-4123 c4 = derive (Bx0-1234 ∷ []) (Bx0-4123 ∷ [])
  (rw 0 (q119 c4) ∷
   rw 0 (q125 c4) ∷
   rw 0 (q126 c4) ∷
   rw 0 (q139 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = eqn (Bx0-3241 ∷ []) (Bx0-2341 ∷ []) (lem-sym-ab-at133441 c4)

-- box-perm-2341: 4 steps
lem-box-perm-2341 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-box-perm-2341 c4 = derive (Bx0-1234 ∷ []) (Bx0-2341 ∷ [])
  (rw 0 (q119 c4) ∷
   rw 0 (q120 c4) ∷
   rw 0 (q128 c4) ∷
   rw 0 (q140 c4) ∷ []) Eq.refl

private
  q141 : Ws → Eqn
  q141 c4 = eqn (CK10 ∷ []) (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0 ∷ CS01⁻ ∷ []) (wl 362 (lit c4))
  q142 : Ws → Eqn
  q142 c4 = eqn (CS01⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4)

-- CKu-box-1: 7 steps
lem-CKu-box-1 : Ws → ⟪ (CK10 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK10 ∷ []) ⟫ʷ
lem-CKu-box-1 c4 = derive (CK10 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK10 ∷ [])
  (rw 0 (q141 c4) ∷
   rw 4 (q142 c4) ∷
   rw 3 (q143 c4) ∷
   rw 2 (q142 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q142 c4) ∷
   rw⁻ 1 (q141 c4) ∷ []) Eq.refl

private
  q145 : Ws → Eqn
  q145 c4 = eqn (CK10⁻ ∷ []) (CS01 ∷ K0⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ []) (wl 363 (lit c4))
  q146 : Ws → Eqn
  q146 c4 = eqn (CS01 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4)

-- CKdu-box-1: 7 steps
lem-CKdu-box-1 : Ws → ⟪ (CK10⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK10⁻ ∷ []) ⟫ʷ
lem-CKdu-box-1 c4 = derive (CK10⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK10⁻ ∷ [])
  (rw 0 (q145 c4) ∷
   rw 4 (q146 c4) ∷
   rw 3 (q143 c4) ∷
   rw 2 (q146 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q146 c4) ∷
   rw⁻ 1 (q145 c4) ∷ []) Eq.refl

private
  q147 : Ws → Eqn
  q147 c4 = eqn (CK20 ∷ []) (CS02⁻ ∷ K0⁻ ∷ CS02⁻ ∷ K0 ∷ CS02⁻ ∷ []) (wl 375 (lit c4))
  q148 : Ws → Eqn
  q148 c4 = eqn (CS02⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4)

-- CKu-box-2: 7 steps
lem-CKu-box-2 : Ws → ⟪ (CK20 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK20 ∷ []) ⟫ʷ
lem-CKu-box-2 c4 = derive (CK20 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK20 ∷ [])
  (rw 0 (q147 c4) ∷
   rw 4 (q148 c4) ∷
   rw 3 (q143 c4) ∷
   rw 2 (q148 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q148 c4) ∷
   rw⁻ 1 (q147 c4) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = eqn (CK20⁻ ∷ []) (CS02 ∷ K0⁻ ∷ CS02 ∷ K0 ∷ CS02 ∷ []) (wl 376 (lit c4))
  q150 : Ws → Eqn
  q150 c4 = eqn (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4)

-- CKdu-box-2: 7 steps
lem-CKdu-box-2 : Ws → ⟪ (CK20⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2 c4 = derive (CK20⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK20⁻ ∷ [])
  (rw 0 (q149 c4) ∷
   rw 4 (q150 c4) ∷
   rw 3 (q143 c4) ∷
   rw 2 (q150 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q150 c4) ∷
   rw⁻ 1 (q149 c4) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = eqn (CK30 ∷ []) (CS03⁻ ∷ K0⁻ ∷ CS03⁻ ∷ K0 ∷ CS03⁻ ∷ []) (wl 385 (lit c4))
  q152 : Ws → Eqn
  q152 c4 = eqn (CS03⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3 c4)

-- CKu-box-3: 7 steps
lem-CKu-box-3 : Ws → ⟪ (CK30 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK30 ∷ []) ⟫ʷ
lem-CKu-box-3 c4 = derive (CK30 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK30 ∷ [])
  (rw 0 (q151 c4) ∷
   rw 4 (q152 c4) ∷
   rw 3 (q143 c4) ∷
   rw 2 (q152 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q152 c4) ∷
   rw⁻ 1 (q151 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = eqn (CK30⁻ ∷ []) (CS03 ∷ K0⁻ ∷ CS03 ∷ K0 ∷ CS03 ∷ []) (wl 386 (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (CS03 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS03 ∷ []) (lem-CSu-box-3 c4)

-- CKdu-box-3: 7 steps
lem-CKdu-box-3 : Ws → ⟪ (CK30⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-CKdu-box-3 c4 = derive (CK30⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK30⁻ ∷ [])
  (rw 0 (q153 c4) ∷
   rw 4 (q154 c4) ∷
   rw 3 (q143 c4) ∷
   rw 2 (q154 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q154 c4) ∷
   rw⁻ 1 (q153 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = eqn (S0 ∷ CS03⁻ ∷ []) (X3 ∷ CS03 ∷ X3 ∷ []) (wl 387 (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (S0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4)

-- XCSX-box-3: 4 steps
lem-XCSX-box-3 : Ws → ⟪ (X3 ∷ CS03 ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-XCSX-box-3 c4 = derive (X3 ∷ CS03 ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw⁻ 0 (q155 c4) ∷
   rw 1 (q152 c4) ∷
   rw 0 (q156 c4) ∷
   rw 1 (q155 c4) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = eqn (S0⁻ ∷ CS03 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ []) (wl 388 (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (S0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4)

-- XCSdX-box-3: 4 steps
lem-XCSdX-box-3 : Ws → ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-XCSdX-box-3 c4 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw⁻ 0 (q157 c4) ∷
   rw 1 (q154 c4) ∷
   rw 0 (q158 c4) ∷
   rw 1 (q157 c4) ∷ []) Eq.refl

private
  q159 : Ws → Eqn
  q159 c4 = eqn (CK40 ∷ []) (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) (wp 255 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (CS04⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS04⁻ ∷ []) (lem-CSdu-box-4 c4)

-- CKu-box-4: 7 steps
lem-CKu-box-4 : Ws → ⟪ (CK40 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK40 ∷ []) ⟫ʷ
lem-CKu-box-4 c4 = derive (CK40 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK40 ∷ [])
  (rw 0 (q159 c4) ∷
   rw 4 (q160 c4) ∷
   rw 3 (q143 c4) ∷
   rw 2 (q160 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q160 c4) ∷
   rw⁻ 1 (q159 c4) ∷ []) Eq.refl

private
  q161 : Ws → Eqn
  q161 c4 = eqn (CK40⁻ ∷ []) (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp 256 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (CS04 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS04 ∷ []) (lem-CSu-box-4 c4)

-- CKdu-box-4: 7 steps
lem-CKdu-box-4 : Ws → ⟪ (CK40⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-CKdu-box-4 c4 = derive (CK40⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK40⁻ ∷ [])
  (rw 0 (q161 c4) ∷
   rw 4 (q162 c4) ∷
   rw 3 (q143 c4) ∷
   rw 2 (q162 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q162 c4) ∷
   rw⁻ 1 (q161 c4) ∷ []) Eq.refl

private
  q163 : Ws → Eqn
  q163 c4 = eqn (S0 ∷ CS04⁻ ∷ []) (X4 ∷ CS04 ∷ X4 ∷ []) (wp 257 c4)

-- XCSX-box-4: 4 steps
lem-XCSX-box-4 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-4 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q163 c4) ∷
   rw 1 (q160 c4) ∷
   rw 0 (q156 c4) ∷
   rw 1 (q163 c4) ∷ []) Eq.refl

private
  q164 : Ws → Eqn
  q164 c4 = eqn (S0⁻ ∷ CS04 ∷ []) (X4 ∷ CS04⁻ ∷ X4 ∷ []) (wp 258 c4)

-- XCSdX-box-4: 4 steps
lem-XCSdX-box-4 : Ws → ⟪ (X4 ∷ CS04⁻ ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ []) ⟫ʷ
lem-XCSdX-box-4 c4 = derive (X4 ∷ CS04⁻ ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ [])
  (rw⁻ 0 (q164 c4) ∷
   rw 1 (q162 c4) ∷
   rw 0 (q158 c4) ∷
   rw 1 (q164 c4) ∷ []) Eq.refl

private
  q165 : Ws → Eqn
  q165 c4 = eqn (Bx0-1243 ∷ []) (Bx0-4312 ∷ []) (lem-pairs-at3443 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (Bx0-4312 ∷ []) (Bx0-3412 ∷ []) (lem-sym-ab-at14233142 c4)
  q167 : Ws → Eqn
  q167 c4 = eqn (Bx0-3412 ∷ []) (Bx0-1234 ∷ []) (lem-pairs-at13243142 c4)

-- box-perm-1243 @3443: 3 steps
lem-box-perm-1243-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1243-at3443 c4 = derive (Bx0-1243 ∷ []) (Bx0-1234 ∷ [])
  (rw 0 (q165 c4) ∷
   rw 0 (q166 c4) ∷
   rw 0 (q167 c4) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = eqn (CX34 ∷ Toff412 ∷ []) (Toff412 ∷ CX34 ∷ []) (wl 472 (lit c4))
  q169 : Ws → Eqn
  q169 c4 = eqn (CS04 ∷ CS03 ∷ CCZ034 ∷ CX34 ∷ []) (CX34 ∷ CS04 ∷ []) (wp 325 c4)
  q170 : Ws → Eqn
  q170 c4 = eqn (CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ CX34 ∷ []) (CX34 ∷ CS04⁻ ∷ []) (wp 326 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (CCZ034 ∷ CS03 ∷ []) (CS03 ∷ CCZ034 ∷ []) (wp 327 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (CS03 ∷ Toff412 ∷ []) (Toff412 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF412 (lit c4))
  q173 : Ws → Eqn
  q173 c4 = eqn (CS03 ∷ CS04⁻ ∷ CS03⁻ ∷ []) (CS04⁻ ∷ []) (wp 328 c4)
  q174 : Ws → Eqn
  q174 c4 = eqn (Toff412 ∷ Toff412 ∷ []) [] (wl 470 (lit c4))
  q175 : Ws → Eqn
  q175 c4 = eqn (CCZ034 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ034 ∷ []) (wp 329 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (Bx4-1203 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (CS04⁻ ∷ Bx4-1203 ∷ []) (Bx4-1203 ∷ CS04⁻ ∷ []) (lem-CSdu-box-3-at043043 c4)

-- F0-R: 11 steps
lem-F0-R : Ws → ⟪ (CX34 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Bx4-1203 ∷ CX34 ∷ []) ⟫ʷ
lem-F0-R c4 = derive (CX34 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Bx4-1203 ∷ CX34 ∷ [])
  (rw 0 (q168 c4) ∷
   rw⁻ 1 (q169 c4) ∷
   rw 4 (q168 c4) ∷
   rw⁻ 5 (q170 c4) ∷
   rw⁻ 2 (q171 c4) ∷
   rw 3 (q172 c4) ∷
   rw 4 (q173 c4) ∷
   rw⁻ 2 (q174 c4) ∷
   rw⁻ 6 (q175 c4) ∷
   rw⁻ 3 (q176 c4) ∷
   rw⁻ 3 (q177 c4) ∷ []) Eq.refl

private
  q178 : Ws → Eqn
  q178 c4 = eqn (Bx3-1204 ∷ []) (Bx3-0412 ∷ []) (lem-pairs-at0330 c4)
  q179 : Ws → Eqn
  q179 c4 = eqn (Bx3-0412 ∷ []) (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4)

-- box-perm-4312 @0330: 2 steps
lem-box-perm-4312-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-4312-at0330 c4 = derive (Bx3-1204 ∷ []) (Bx3-4012 ∷ [])
  (rw 0 (q178 c4) ∷
   rw 0 (q179 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = eqn (Bx3-4012 ∷ []) (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (Bx3-0412 ∷ []) (Bx3-1204 ∷ []) (lem-pairs-at0310243142 c4)

-- box-perm-3421 @0314203142: 2 steps
lem-box-perm-3421-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-3421-at0314203142 c4 = derive (Bx3-4012 ∷ []) (Bx3-1204 ∷ [])
  (rw 0 (q180 c4) ∷
   rw 0 (q181 c4) ∷ []) Eq.refl

private
  q182 : Ws → Eqn
  q182 c4 = eqn (CS04 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4)
  q183 : Ws → Eqn
  q183 c4 = eqn (K0 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ K0 ∷ []) (lem-Ku-box-at243243 c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (K0⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ K0⁻ ∷ []) (lem-Kdu-box-at243243 c4)

-- CKdu-box-2 @243243: 7 steps
lem-CKdu-box-2-at243243 : Ws → ⟪ (CK40⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at243243 c4 = derive (CK40⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CK40⁻ ∷ [])
  (rw 0 (q161 c4) ∷
   rw 4 (q182 c4) ∷
   rw 3 (q183 c4) ∷
   rw 2 (q182 c4) ∷
   rw 1 (q184 c4) ∷
   rw 0 (q182 c4) ∷
   rw⁻ 1 (q161 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = eqn (CS04 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (K0 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ K0 ∷ []) (lem-Ku-box-at122441 c4)
  q187 : Ws → Eqn
  q187 c4 = eqn (K0⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ K0⁻ ∷ []) (lem-Kdu-box-at122441 c4)

-- CKdu-box-2 @122441: 7 steps
lem-CKdu-box-2-at122441 : Ws → ⟪ (CK40⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at122441 c4 = derive (CK40⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CK40⁻ ∷ [])
  (rw 0 (q161 c4) ∷
   rw 4 (q185 c4) ∷
   rw 3 (q186 c4) ∷
   rw 2 (q185 c4) ∷
   rw 1 (q187 c4) ∷
   rw 0 (q185 c4) ∷
   rw⁻ 1 (q161 c4) ∷ []) Eq.refl

private
  q188 : Ws → Eqn
  q188 c4 = eqn (Bx2-0413 ∷ []) (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4)
  q189 : Ws → Eqn
  q189 c4 = eqn (Bx2-4013 ∷ []) (Bx2-4103 ∷ []) (lem-sym-bc-at0214203143 c4)
  q190 : Ws → Eqn
  q190 c4 = eqn (Bx2-4103 ∷ []) (Bx2-0341 ∷ []) (lem-pairs-at0214213043 c4)

-- box-perm-1423 @0210243143: 3 steps
lem-box-perm-1423-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-box-perm-1423-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-0341 ∷ [])
  (rw 0 (q188 c4) ∷
   rw 0 (q189 c4) ∷
   rw 0 (q190 c4) ∷ []) Eq.refl

private
  q191 : Ws → Eqn
  q191 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4)
  q192 : Ws → Eqn
  q192 c4 = eqn (Bx0-2341 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4)
  q193 : Ws → Eqn
  q193 c4 = eqn (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))
  q194 : Ws → Eqn
  q194 c4 = eqn (CK41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 (lit c4))
  q195 : Ws → Eqn
  q195 c4 = eqn (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) (wp 531 c4)
  q196 : Ws → Eqn
  q196 c4 = eqn (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (wl 654 (lit c4))

-- F4-K1-CS2: 19 steps
lem-F4-K1-CS2 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-CS2 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q191 c4) ∷
   rw 3 (q192 c4) ∷
   rw⁻ 2 (q193 c4) ∷
   rw 1 (q194 c4) ∷
   rw⁻ 0 (q193 c4) ∷
   rw⁻ 1 (q195 c4) ∷
   rw⁻ 4 (q193 c4) ∷
   rw 3 (q194 c4) ∷
   rw⁻ 2 (q193 c4) ∷
   rw⁻ 3 (q195 c4) ∷
   rw⁻ 0 (q192 c4) ∷
   rw⁻ 0 (q191 c4) ∷
   rw⁻ 1 (q196 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = eqn (CK42⁻ ∷ []) (CS24 ∷ K2⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (wl 664 (lit c4))
  q198 : Ws → Eqn
  q198 c4 = eqn (CS24 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4)
  q199 : Ws → Eqn
  q199 c4 = eqn (K2 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ K2 ∷ []) (lem-Ku-box-at0210243143 c4)
  q200 : Ws → Eqn
  q200 c4 = eqn (K2⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ K2⁻ ∷ []) (lem-Kdu-box-at0210243143 c4)

-- CKdu-box-2 @0210243143: 7 steps
lem-CKdu-box-2-at0210243143 : Ws → ⟪ (CK42⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CK42⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at0210243143 c4 = derive (CK42⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CK42⁻ ∷ [])
  (rw 0 (q197 c4) ∷
   rw 4 (q198 c4) ∷
   rw 3 (q199 c4) ∷
   rw 2 (q198 c4) ∷
   rw 1 (q200 c4) ∷
   rw 0 (q198 c4) ∷
   rw⁻ 1 (q197 c4) ∷ []) Eq.refl

private
  q201 : Ws → Eqn
  q201 c4 = eqn (Bx0-4123 ∷ []) (Bx0-4213 ∷ []) (lem-sym-bc-at14213243 c4)
  q202 : Ws → Eqn
  q202 c4 = eqn (Bx0-4213 ∷ []) (Bx0-1342 ∷ []) (lem-pairs-at143143 c4)

-- box-perm-1423 @243243: 3 steps
lem-box-perm-1423-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-box-perm-1423-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-1342 ∷ [])
  (rw 0 (q139 c4) ∷
   rw 0 (q201 c4) ∷
   rw 0 (q202 c4) ∷ []) Eq.refl

private
  q203 : Ws → Eqn
  q203 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-box-perm-1324-at0210243143 c4)
  q204 : Ws → Eqn
  q204 c4 = eqn (Bx2-0143 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0210213443 c4)
  q205 : Ws → Eqn
  q205 c4 = eqn (CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (X ↑))
  q206 : Ws → Eqn
  q206 c4 = eqn (CCZ012 ∷ CK43 ∷ []) (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀))
  q207 : Ws → Eqn
  q207 c4 = eqn (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ []) (wl 697 (lit c4))
  q208 : Ws → Eqn
  q208 c4 = eqn (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp 571 c4)

-- F4-K3-CS0: 19 steps
lem-F4-K3-CS0 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS0 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q203 c4) ∷
   rw 3 (q204 c4) ∷
   rw⁻ 2 (q205 c4) ∷
   rw⁻ 1 (q206 c4) ∷
   rw⁻ 0 (q205 c4) ∷
   rw⁻ 1 (q207 c4) ∷
   rw⁻ 4 (q205 c4) ∷
   rw⁻ 3 (q206 c4) ∷
   rw⁻ 2 (q205 c4) ∷
   rw⁻ 3 (q207 c4) ∷
   rw⁻ 0 (q204 c4) ∷
   rw⁻ 0 (q203 c4) ∷
   rw⁻ 1 (q208 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q209 : Ws → Eqn
  q209 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4)
  q210 : Ws → Eqn
  q210 c4 = eqn (Bx0-1243 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4)
  q211 : Ws → Eqn
  q211 c4 = eqn (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ []) (wp 586 c4)
  q212 : Ws → Eqn
  q212 c4 = eqn (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (wl 700 (lit c4))

-- F4-K3-CS1: 19 steps
lem-F4-K3-CS1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS1 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q209 c4) ∷
   rw 3 (q210 c4) ∷
   rw⁻ 2 (q205 c4) ∷
   rw⁻ 1 (q206 c4) ∷
   rw⁻ 0 (q205 c4) ∷
   rw⁻ 1 (q211 c4) ∷
   rw⁻ 4 (q205 c4) ∷
   rw⁻ 3 (q206 c4) ∷
   rw⁻ 2 (q205 c4) ∷
   rw⁻ 3 (q211 c4) ∷
   rw⁻ 0 (q210 c4) ∷
   rw⁻ 0 (q209 c4) ∷
   rw⁻ 1 (q212 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4)
  q214 : Ws → Eqn
  q214 c4 = eqn (Bx0-2143 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at12213443 c4)
  q215 : Ws → Eqn
  q215 c4 = eqn (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (wl 708 (lit c4))

-- F4-K3-CS2: 19 steps
lem-F4-K3-CS2 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS2 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q213 c4) ∷
   rw 3 (q214 c4) ∷
   rw⁻ 2 (q205 c4) ∷
   rw⁻ 1 (q206 c4) ∷
   rw⁻ 0 (q205 c4) ∷
   rw⁻ 1 (q211 c4) ∷
   rw⁻ 4 (q205 c4) ∷
   rw⁻ 3 (q206 c4) ∷
   rw⁻ 2 (q205 c4) ∷
   rw⁻ 3 (q211 c4) ∷
   rw⁻ 0 (q214 c4) ∷
   rw⁻ 0 (q213 c4) ∷
   rw⁻ 1 (q215 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q216 : Ws → Eqn
  q216 c4 = eqn (CK42 ∷ []) (CS24⁻ ∷ K2⁻ ∷ CS24⁻ ∷ K2 ∷ CS24⁻ ∷ []) (wl 724 (lit c4))
  q217 : Ws → Eqn
  q217 c4 = eqn (CS24⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4)

-- CKu-box-2 @0210243143: 7 steps
lem-CKu-box-2-at0210243143 : Ws → ⟪ (CK42 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CK42 ∷ []) ⟫ʷ
lem-CKu-box-2-at0210243143 c4 = derive (CK42 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CK42 ∷ [])
  (rw 0 (q216 c4) ∷
   rw 4 (q217 c4) ∷
   rw 3 (q199 c4) ∷
   rw 2 (q217 c4) ∷
   rw 1 (q200 c4) ∷
   rw 0 (q217 c4) ∷
   rw⁻ 1 (q216 c4) ∷ []) Eq.refl

private
  q218 : Ws → Eqn
  q218 c4 = eqn (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ []) (wl 729 (lit c4))
  q219 : Ws → Eqn
  q219 c4 = eqn (K3 ∷ CK43 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) (wp 618 c4)
  q220 : Ws → Eqn
  q220 c4 = eqn (K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ []) (Toff234 ∷ K3 ∷ CK43 ∷ S4 ∷ []) (wl 730 (lit c4))
  q221 : Ws → Eqn
  q221 c4 = eqn (CCZ012 ∷ K3 ∷ []) (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K))
  q222 : Ws → Eqn
  q222 c4 = eqn (CCZ012 ∷ S4 ∷ []) (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑))
  q223 : Ws → Eqn
  q223 c4 = eqn (CK43 ∷ X4 ∷ []) (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ []) (wl 731 (lit c4))

-- F4-CS0-K3: 21 steps
lem-F4-CS0-K3 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K3 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q218 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q219 c4) ∷
   rw 1 (q203 c4) ∷
   rw 1 (q204 c4) ∷
   rw⁻ 4 (q220 c4) ∷
   rw 3 (q221 c4) ∷
   rw 4 (q206 c4) ∷
   rw 5 (q222 c4) ∷
   rw⁻ 2 (q220 c4) ∷
   rw 1 (q221 c4) ∷
   rw 2 (q206 c4) ∷
   rw 3 (q222 c4) ∷
   rw⁻ 4 (q204 c4) ∷
   rw⁻ 4 (q203 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q223 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = eqn (CS04⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4)

-- CKu-box-2 @243243: 7 steps
lem-CKu-box-2-at243243 : Ws → ⟪ (CK40 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CK40 ∷ []) ⟫ʷ
lem-CKu-box-2-at243243 c4 = derive (CK40 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CK40 ∷ [])
  (rw 0 (q159 c4) ∷
   rw 4 (q224 c4) ∷
   rw 3 (q183 c4) ∷
   rw 2 (q224 c4) ∷
   rw 1 (q184 c4) ∷
   rw 0 (q224 c4) ∷
   rw⁻ 1 (q159 c4) ∷ []) Eq.refl

private
  q225 : Ws → Eqn
  q225 c4 = eqn (K3 ∷ CK43 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) (wl 738 (lit c4))
  q226 : Ws → Eqn
  q226 c4 = eqn (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (Toff034 ∷ K3 ∷ CK43 ∷ S4 ∷ []) (wp 636 c4)

-- F4-CS1-K3: 21 steps
lem-F4-CS1-K3 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K3 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q218 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q225 c4) ∷
   rw 1 (q209 c4) ∷
   rw 1 (q210 c4) ∷
   rw⁻ 4 (q226 c4) ∷
   rw 3 (q221 c4) ∷
   rw 4 (q206 c4) ∷
   rw 5 (q222 c4) ∷
   rw⁻ 2 (q226 c4) ∷
   rw 1 (q221 c4) ∷
   rw 2 (q206 c4) ∷
   rw 3 (q222 c4) ∷
   rw⁻ 4 (q210 c4) ∷
   rw⁻ 4 (q209 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q223 c4) ∷ []) Eq.refl

private
  q227 : Ws → Eqn
  q227 c4 = eqn (CS04⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4)

-- CKu-box-2 @122441: 7 steps
lem-CKu-box-2-at122441 : Ws → ⟪ (CK40 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CK40 ∷ []) ⟫ʷ
lem-CKu-box-2-at122441 c4 = derive (CK40 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CK40 ∷ [])
  (rw 0 (q159 c4) ∷
   rw 4 (q227 c4) ∷
   rw 3 (q186 c4) ∷
   rw 2 (q227 c4) ∷
   rw 1 (q187 c4) ∷
   rw 0 (q227 c4) ∷
   rw⁻ 1 (q159 c4) ∷ []) Eq.refl

private
  q228 : Ws → Eqn
  q228 c4 = eqn (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ []) (wl 720 (lit c4))
  q229 : Ws → Eqn
  q229 c4 = eqn (K1 ∷ CK41 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ []) (wl 741 (lit c4))
  q230 : Ws → Eqn
  q230 c4 = eqn (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) (Toff014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (wp 648 c4)
  q231 : Ws → Eqn
  q231 c4 = eqn (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) (wl 722 (lit c4))
  q232 : Ws → Eqn
  q232 c4 = eqn (CCZ023 ∷ CK41 ∷ []) (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 (lit c4))
  q233 : Ws → Eqn
  q233 c4 = eqn (CCZ023 ∷ S4 ∷ []) (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S))
  q234 : Ws → Eqn
  q234 c4 = eqn (CK41 ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (wl 723 (lit c4))

-- F4-CS2-K1: 21 steps
lem-F4-CS2-K1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw⁻ 2 (q228 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q229 c4) ∷
   rw 1 (q191 c4) ∷
   rw 1 (q192 c4) ∷
   rw⁻ 4 (q230 c4) ∷
   rw 3 (q231 c4) ∷
   rw 4 (q232 c4) ∷
   rw 5 (q233 c4) ∷
   rw⁻ 2 (q230 c4) ∷
   rw 1 (q231 c4) ∷
   rw 2 (q232 c4) ∷
   rw 3 (q233 c4) ∷
   rw⁻ 4 (q192 c4) ∷
   rw⁻ 4 (q191 c4) ∷
   re 6 1 (Sb0-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 0 (q234 c4) ∷ []) Eq.refl

private
  q235 : Ws → Eqn
  q235 c4 = eqn (K3 ∷ CK43 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) (wl 744 (lit c4))

-- F4-CS2-K3: 21 steps
lem-F4-CS2-K3 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K3 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw⁻ 2 (q218 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q235 c4) ∷
   rw 1 (q213 c4) ∷
   rw 1 (q214 c4) ∷
   rw⁻ 4 (q226 c4) ∷
   rw 3 (q221 c4) ∷
   rw 4 (q206 c4) ∷
   rw 5 (q222 c4) ∷
   rw⁻ 2 (q226 c4) ∷
   rw 1 (q221 c4) ∷
   rw 2 (q206 c4) ∷
   rw 3 (q222 c4) ∷
   rw⁻ 4 (q214 c4) ∷
   rw⁻ 4 (q213 c4) ∷
   re 6 1 (Sb0-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 0 (q223 c4) ∷ []) Eq.refl

private
  q236 : Ws → Eqn
  q236 c4 = eqn (Bx2-0341 ∷ []) (Bx2-3041 ∷ []) (lem-sym-ab-at0210233441 c4)

-- box-perm-4312 @0214213043: 2 steps
lem-box-perm-4312-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ []) ⟫ʷ
lem-box-perm-4312-at0214213043 c4 = derive (Bx2-4103 ∷ []) (Bx2-3041 ∷ [])
  (rw 0 (q190 c4) ∷
   rw 0 (q236 c4) ∷ []) Eq.refl

private
  q237 : Ws → Eqn
  q237 c4 = eqn (Bx2-3041 ∷ []) (Bx2-0341 ∷ []) (lem-sym-ab-at0213203441 c4)
  q238 : Ws → Eqn
  q238 c4 = eqn (Bx2-0341 ∷ []) (Bx2-4103 ∷ []) (lem-pairs-at0210233441 c4)

-- box-perm-3421 @0213203441: 2 steps
lem-box-perm-3421-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-box-perm-3421-at0213203441 c4 = derive (Bx2-3041 ∷ []) (Bx2-4103 ∷ [])
  (rw 0 (q237 c4) ∷
   rw 0 (q238 c4) ∷ []) Eq.refl

private
  q239 : Ws → Eqn
  q239 c4 = eqn (CX23 ∷ Toff314 ∷ []) (Toff314 ∷ CX23 ∷ []) (wl 794 (lit c4))
  q240 : Ws → Eqn
  q240 c4 = eqn (CS03 ∷ CS02 ∷ CCZ023 ∷ CX23 ∷ []) (CX23 ∷ CS03 ∷ []) (wl 795 (lit c4))
  q241 : Ws → Eqn
  q241 c4 = eqn (CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ CX23 ∷ []) (CX23 ∷ CS03⁻ ∷ []) (wl 796 (lit c4))
  q242 : Ws → Eqn
  q242 c4 = eqn (CCZ023 ∷ CS02 ∷ []) (CS02 ∷ CCZ023 ∷ []) (wl 797 (lit c4))
  q243 : Ws → Eqn
  q243 c4 = eqn (CS02 ∷ Toff314 ∷ []) (Toff314 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF314 (lit c4))
  q244 : Ws → Eqn
  q244 c4 = eqn (CS02 ∷ CS03⁻ ∷ CS02⁻ ∷ []) (CS03⁻ ∷ []) (wl 798 (lit c4))
  q245 : Ws → Eqn
  q245 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl 788 (lit c4))
  q246 : Ws → Eqn
  q246 c4 = eqn (CCZ023 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ023 ∷ []) (wl 799 (lit c4))
  q247 : Ws → Eqn
  q247 c4 = eqn (Bx3-4102 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4)
  q248 : Ws → Eqn
  q248 c4 = eqn (CS03⁻ ∷ Bx3-4102 ∷ []) (Bx3-4102 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3-at0314213042 c4)

-- F0-R @14213243: 11 steps
lem-F0-R-at14213243 : Ws → ⟪ (CX23 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx3-4102 ∷ CX23 ∷ []) ⟫ʷ
lem-F0-R-at14213243 c4 = derive (CX23 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx3-4102 ∷ CX23 ∷ [])
  (rw 0 (q239 c4) ∷
   rw⁻ 1 (q240 c4) ∷
   rw 4 (q239 c4) ∷
   rw⁻ 5 (q241 c4) ∷
   rw⁻ 2 (q242 c4) ∷
   rw 3 (q243 c4) ∷
   rw 4 (q244 c4) ∷
   rw⁻ 2 (q245 c4) ∷
   rw⁻ 6 (q246 c4) ∷
   rw⁻ 3 (q247 c4) ∷
   rw⁻ 3 (q248 c4) ∷ []) Eq.refl

private
  q249 : Ws → Eqn
  q249 c4 = eqn (CX32 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CX32 ∷ []) (lem-CXu-box-4-at0210243143 c4)
  q250 : Ws → Eqn
  q250 c4 = eqn (CX32 ∷ Toff314 ∷ []) (Toff314 ∷ CX32 ∷ Toff214 ∷ []) (wl 810 (lit c4))
  q251 : Ws → Eqn
  q251 c4 = eqn (Toff214 ∷ CS03 ∷ []) (CS03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CS03 (lit c4))
  q252 : Ws → Eqn
  q252 c4 = eqn (CS03 ∷ CX32 ∷ []) (CX32 ∷ CS03 ∷ []) (wl 811 (lit c4))
  q253 : Ws → Eqn
  q253 c4 = eqn (CX32 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ CX32 ∷ []) (wl 812 (lit c4))
  q254 : Ws → Eqn
  q254 c4 = eqn (CS03⁻ ∷ CX32 ∷ []) (CX32 ∷ CS03⁻ ∷ []) (wl 813 (lit c4))

-- CXAu-S @14213243: 12 steps
lem-CXAu-S-at14213243 : Ws → ⟪ (CX32 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CX32 ∷ []) ⟫ʷ
lem-CXAu-S-at14213243 c4 = derive (CX32 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CX32 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 0 (q249 c4) ∷
   rw 1 (q250 c4) ∷
   rw 3 (q251 c4) ∷
   rw⁻ 2 (q252 c4) ∷
   rw 3 (q253 c4) ∷
   rw⁻ 4 (q254 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q255 : Ws → Eqn
  q255 c4 = eqn (Bx3-1204 ∷ []) (Bx3-1024 ∷ []) (lem-sym-bc-at0330 c4)
  q256 : Ws → Eqn
  q256 c4 = eqn (Bx3-1024 ∷ []) (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4)

-- box-perm-1342 @0310243142: 3 steps
lem-box-perm-1342-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-1342-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-0124 ∷ [])
  (rw 0 (q181 c4) ∷
   rw 0 (q255 c4) ∷
   rw 0 (q256 c4) ∷ []) Eq.refl

private
  q257 : Ws → Eqn
  q257 c4 = eqn (Bx0-1423 ∷ []) (Bx0-2314 ∷ []) (lem-pairs-at243243 c4)
  q258 : Ws → Eqn
  q258 c4 = eqn (Bx0-3214 ∷ []) (Bx0-3124 ∷ []) (lem-sym-bc-at1331 c4)

-- box-perm-4132 @243243: 3 steps
lem-box-perm-4132-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-box-perm-4132-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-3124 ∷ [])
  (rw 0 (q257 c4) ∷
   rw 0 (q137 c4) ∷
   rw 0 (q258 c4) ∷ []) Eq.refl

private
  q259 : Ws → Eqn
  q259 c4 = eqn (Bx3-1240 ∷ []) (Bx3-2140 ∷ []) (lem-sym-ab-at033440 c4)
  q260 : Ws → Eqn
  q260 c4 = eqn (Bx3-2140 ∷ []) (Bx3-2410 ∷ []) (lem-sym-bc-at0312213440 c4)
  q261 : Ws → Eqn
  q261 c4 = eqn (Bx3-2410 ∷ []) (Bx3-1024 ∷ []) (lem-pairs-at0312243140 c4)

-- box-perm-4123 @033440: 4 steps
lem-box-perm-4123-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-4123-at033440 c4 = derive (Bx3-1240 ∷ []) (Bx3-0124 ∷ [])
  (rw 0 (q259 c4) ∷
   rw 0 (q260 c4) ∷
   rw 0 (q261 c4) ∷
   rw 0 (q256 c4) ∷ []) Eq.refl

private
  q262 : Ws → Eqn
  q262 c4 = eqn (Bx0-3124 ∷ []) (Bx0-3214 ∷ []) (lem-sym-bc-at132132 c4)
  q263 : Ws → Eqn
  q263 c4 = eqn (Bx0-3214 ∷ []) (Bx0-2314 ∷ []) (lem-sym-ab-at1331 c4)

-- box-perm-2431 @132132: 3 steps
lem-box-perm-2431-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-2431-at132132 c4 = derive (Bx0-3124 ∷ []) (Bx0-1423 ∷ [])
  (rw 0 (q262 c4) ∷
   rw 0 (q263 c4) ∷
   rw 0 (q126 c4) ∷ []) Eq.refl

private
  q264 : Ws → Eqn
  q264 c4 = eqn (Bx3-0124 ∷ []) (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4)
  q265 : Ws → Eqn
  q265 c4 = eqn (Bx3-1024 ∷ []) (Bx3-1204 ∷ []) (lem-sym-bc-at032032 c4)

-- box-perm-1423 @03102132: 3 steps
lem-box-perm-1423-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-1423-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-0412 ∷ [])
  (rw 0 (q264 c4) ∷
   rw 0 (q265 c4) ∷
   rw 0 (q178 c4) ∷ []) Eq.refl

private
  q266 : Ws → Eqn
  q266 c4 = eqn (Bx2-0413 ∷ []) (Bx2-1304 ∷ []) (lem-pairs-at0210243143 c4)
  q267 : Ws → Eqn
  q267 c4 = eqn (Bx2-1304 ∷ []) (Bx2-1034 ∷ []) (lem-sym-bc-at022330 c4)
  q268 : Ws → Eqn
  q268 c4 = eqn (Bx2-1034 ∷ []) (Bx2-0134 ∷ []) (lem-sym-ab-at0220 c4)

-- box-perm-1342 @0210243143: 3 steps
lem-box-perm-1342-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-1342-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-0134 ∷ [])
  (rw 0 (q266 c4) ∷
   rw 0 (q267 c4) ∷
   rw 0 (q268 c4) ∷ []) Eq.refl

private
  q269 : Ws → Eqn
  q269 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1340 ∷ []) (lem-box-perm-2341-at021021 c4)
  q270 : Ws → Eqn
  q270 c4 = eqn (Bx2-1340 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4)
  q271 : Ws → Eqn
  q271 c4 = eqn (Bx0-2134 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4)
  q272 : Ws → Eqn
  q272 c4 = eqn (CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ012 ∷ []) (wp 142 c4)
  q273 : Ws → Eqn
  q273 c4 = eqn (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp 139 c4)
  q274 : Ws → Eqn
  q274 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl 274 (lit c4))
  q275 : Ws → Eqn
  q275 c4 = eqn (CCZ012 ∷ CS24 ∷ []) (CS24 ∷ CCZ012 ∷ []) (wp 141 c4)
  q276 : Ws → Eqn
  q276 c4 = eqn (CCZ012 ∷ CX23 ∷ []) (CX23 ∷ CCZ012 ∷ []) (wl 411 (lit c4))
  q277 : Ws → Eqn
  q277 c4 = eqn (CCZ012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS))
  q278 : Ws → Eqn
  q278 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS))
  q279 : Ws → Eqn
  q279 c4 = eqn (CCZ024 ∷ CCZ234 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ024 ∷ []) (wp 770 c4)
  q280 : Ws → Eqn
  q280 c4 = eqn (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (Toff213 ∷ CCZ012 ∷ []) (wl 940 (lit c4))
  q281 : Ws → Eqn
  q281 c4 = eqn (CCZ013 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) (wp 771 c4)
  q282 : Ws → Eqn
  q282 c4 = eqn (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (Toff213 ∷ []) (wl 952 (lit c4))
  q283 : Ws → Eqn
  q283 c4 = eqn (K2⁻ ∷ Toff034 ∷ []) (Toff034 ∷ K2⁻ ∷ []) (wp 751 c4)
  q284 : Ws → Eqn
  q284 c4 = eqn (CS23 ∷ Toff034 ∷ []) (Toff034 ∷ CS23 ∷ []) (wp 146 c4)
  q285 : Ws → Eqn
  q285 c4 = eqn (CX21 ∷ Toff034 ∷ []) (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4))
  q286 : Ws → Eqn
  q286 c4 = eqn (CS13⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS13⁻ ∷ []) (wp 772 c4)
  q287 : Ws → Eqn
  q287 c4 = eqn (CS13 ∷ Toff034 ∷ []) (Toff034 ∷ CS13 ∷ []) (wp 171 c4)
  q288 : Ws → Eqn
  q288 c4 = eqn (K2 ∷ Toff034 ∷ []) (Toff034 ∷ K2 ∷ []) (wp 752 c4)
  q289 : Ws → Eqn
  q289 c4 = eqn (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl 166 (lit c4))
  q290 : Ws → Eqn
  q290 c4 = eqn (CCZ012 ∷ CS14 ∷ []) (CS14 ∷ CCZ012 ∷ []) (wp 11 c4)
  q291 : Ws → Eqn
  q291 c4 = eqn (CCZ012 ∷ CX13 ∷ []) (CX13 ∷ CCZ012 ∷ []) (wl 167 (lit c4))
  q292 : Ws → Eqn
  q292 c4 = eqn (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ []) (wl 704 (lit c4))
  q293 : Ws → Eqn
  q293 c4 = eqn (Toff213 ∷ CCZ013 ∷ CCZ013 ∷ []) (Toff213 ∷ []) (wl 953 (lit c4))
  q294 : Ws → Eqn
  q294 c4 = eqn (CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ []) (wp 12 c4)
  q295 : Ws → Eqn
  q295 c4 = eqn (CCZ134 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ134 ∷ []) (wl 954 (lit c4))
  q296 : Ws → Eqn
  q296 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl 321 (lit c4))
  q297 : Ws → Eqn
  q297 c4 = eqn (Bx2-1340 ∷ []) (Bx2-0134 ∷ []) (lem-box-perm-4123-at02233440 c4)

-- box-box-1 @021021: 105 steps
lem-box-box-1-at021021 : Ws → ⟪ (Bx2-0134 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-box-box-1-at021021 c4 = derive (Bx2-0134 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ Bx2-0134 ∷ [])
  (rw 0 (q269 c4) ∷
   rw 0 (q270 c4) ∷
   rw 4 (q271 c4) ∷
   rw⁻ 3 (q272 c4) ∷
   rw 4 (q273 c4) ∷
   rw 6 (q274 c4) ∷
   rw⁻ 10 (q275 c4) ∷
   rw⁻ 9 (q276 c4) ∷
   rw⁻ 8 (q277 c4) ∷
   rw⁻ 7 (q276 c4) ∷
   rw⁻ 6 (q278 c4) ∷
   rw⁻ 7 (q274 c4) ∷
   rw⁻ 5 (q272 c4) ∷
   rw 6 (q279 c4) ∷
   rw⁻ 3 (q271 c4) ∷
   rw 3 (q271 c4) ∷
   rw⁻ 2 (q280 c4) ∷
   rw 4 (q281 c4) ∷
   rw⁻ 3 (q282 c4) ∷
   rw 9 (q283 c4) ∷
   rw 8 (q284 c4) ∷
   rw 7 (q285 c4) ∷
   rw 6 (q286 c4) ∷
   rw 5 (q285 c4) ∷
   rw 4 (q287 c4) ∷
   rw 3 (q288 c4) ∷
   rw 4 (q282 c4) ∷
   rw 6 (q289 c4) ∷
   rw⁻ 10 (q290 c4) ∷
   rw⁻ 9 (q291 c4) ∷
   rw⁻ 8 (q277 c4) ∷
   rw⁻ 7 (q291 c4) ∷
   rw⁻ 6 (q278 c4) ∷
   rw⁻ 7 (q289 c4) ∷
   rw⁻ 5 (q292 c4) ∷
   rw⁻ 4 (q280 c4) ∷
   rw 5 (q293 c4) ∷
   rw 6 (q294 c4) ∷
   rw⁻ 5 (q282 c4) ∷
   rw 11 (q283 c4) ∷
   rw 10 (q284 c4) ∷
   rw 9 (q285 c4) ∷
   rw 8 (q286 c4) ∷
   rw 7 (q285 c4) ∷
   rw 6 (q287 c4) ∷
   rw 5 (q288 c4) ∷
   rw 6 (q282 c4) ∷
   rw⁻ 2 (q271 c4) ∷
   rw 2 (q271 c4) ∷
   rw⁻ 1 (q272 c4) ∷
   rw 2 (q273 c4) ∷
   rw 4 (q274 c4) ∷
   rw⁻ 8 (q275 c4) ∷
   rw⁻ 7 (q276 c4) ∷
   rw⁻ 6 (q277 c4) ∷
   rw⁻ 5 (q276 c4) ∷
   rw⁻ 4 (q278 c4) ∷
   rw⁻ 5 (q274 c4) ∷
   rw⁻ 3 (q272 c4) ∷
   rw 4 (q279 c4) ∷
   rw⁻ 1 (q271 c4) ∷
   rw 1 (q271 c4) ∷
   rw⁻ 0 (q280 c4) ∷
   rw 2 (q281 c4) ∷
   rw⁻ 1 (q282 c4) ∷
   rw 7 (q283 c4) ∷
   rw 6 (q284 c4) ∷
   rw 5 (q285 c4) ∷
   rw 4 (q286 c4) ∷
   rw 3 (q285 c4) ∷
   rw 2 (q287 c4) ∷
   rw 1 (q288 c4) ∷
   rw 2 (q282 c4) ∷
   rw 4 (q289 c4) ∷
   rw⁻ 8 (q290 c4) ∷
   rw⁻ 7 (q291 c4) ∷
   rw⁻ 6 (q277 c4) ∷
   rw⁻ 5 (q291 c4) ∷
   rw⁻ 4 (q278 c4) ∷
   rw⁻ 5 (q289 c4) ∷
   rw⁻ 3 (q292 c4) ∷
   rw⁻ 2 (q280 c4) ∷
   rw 3 (q293 c4) ∷
   rw 4 (q294 c4) ∷
   rw⁻ 3 (q282 c4) ∷
   rw 9 (q283 c4) ∷
   rw 8 (q284 c4) ∷
   rw 7 (q285 c4) ∷
   rw 6 (q286 c4) ∷
   rw 5 (q285 c4) ∷
   rw 4 (q287 c4) ∷
   rw 3 (q288 c4) ∷
   rw 4 (q282 c4) ∷
   rw⁻ 0 (q271 c4) ∷
   rw 2 (q289 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw⁻ 3 (q289 c4) ∷
   rw 3 (q295 c4) ∷
   rw 4 (q296 c4) ∷
   rw⁻ 1 (q270 c4) ∷
   rw 1 (q297 c4) ∷ []) Eq.refl

private
  q298 : Ws → Eqn
  q298 c4 = eqn (Bx0-2134 ∷ []) (Bx0-1234 ∷ []) (lem-sym-ab-at1221 c4)

-- box-perm-1432 @1221: 4 steps
lem-box-perm-1432-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-1432-at1221 c4 = derive (Bx0-2134 ∷ []) (Bx0-2431 ∷ [])
  (rw 0 (q298 c4) ∷
   rw 0 (q121 c4) ∷
   rw 0 (q129 c4) ∷
   rw 0 (q130 c4) ∷ []) Eq.refl

private
  q299 : Ws → Eqn
  q299 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym-ab-at021021 c4)
  q300 : Ws → Eqn
  q300 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1304 ∷ []) (lem-sym-bc-at0220 c4)
  q301 : Ws → Eqn
  q301 c4 = eqn (Bx2-1304 ∷ []) (Bx2-0413 ∷ []) (lem-pairs-at022330 c4)

-- box-perm-1423 @021021: 3 steps
lem-box-perm-1423-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-1423-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-0413 ∷ [])
  (rw 0 (q299 c4) ∷
   rw 0 (q300 c4) ∷
   rw 0 (q301 c4) ∷ []) Eq.refl

private
  q302 : Ws → Eqn
  q302 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2134 ∷ []) (lem-sym-bc-at122331 c4)

-- box-perm-1342 @243243: 3 steps
lem-box-perm-1342-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1342-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-1234 ∷ [])
  (rw 0 (q257 c4) ∷
   rw 0 (q302 c4) ∷
   rw 0 (q298 c4) ∷ []) Eq.refl

private
  q303 : Ws → Eqn
  q303 c4 = eqn (Bx0-4123 ∷ []) (Bx0-2341 ∷ []) (lem-pairs-at14213243 c4)
  q304 : Ws → Eqn
  q304 c4 = eqn (Bx0-2341 ∷ []) (Bx0-2431 ∷ []) (lem-sym-bc-at12233441 c4)

-- box-perm-3241 @243243: 3 steps
lem-box-perm-3241-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-3241-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-2431 ∷ [])
  (rw 0 (q139 c4) ∷
   rw 0 (q303 c4) ∷
   rw 0 (q304 c4) ∷ []) Eq.refl

private
  q305 : Ws → Eqn
  q305 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2341 ∷ []) (lem-sym-bc-at122441 c4)
  q306 : Ws → Eqn
  q306 c4 = eqn (Bx0-2341 ∷ []) (Bx0-4123 ∷ []) (lem-pairs-at12233441 c4)
  q307 : Ws → Eqn
  q307 c4 = eqn (Bx0-4123 ∷ []) (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4)

-- box-perm-4213 @122441: 3 steps
lem-box-perm-4213-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-4213-at122441 c4 = derive (Bx0-2431 ∷ []) (Bx0-1423 ∷ [])
  (rw 0 (q305 c4) ∷
   rw 0 (q306 c4) ∷
   rw 0 (q307 c4) ∷ []) Eq.refl

private
  q308 : Ws → Eqn
  q308 c4 = eqn (Bx0-2431 ∷ []) (Bx0-3124 ∷ []) (lem-pairs-at122441 c4)
  q309 : Ws → Eqn
  q309 c4 = eqn (Bx0-3124 ∷ []) (Bx0-1324 ∷ []) (lem-sym-ab-at132132 c4)
  q310 : Ws → Eqn
  q310 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1234 ∷ []) (lem-sym-bc-at2332 c4)

-- box-perm-4132 @122441: 3 steps
lem-box-perm-4132-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-4132-at122441 c4 = derive (Bx0-2431 ∷ []) (Bx0-1234 ∷ [])
  (rw 0 (q308 c4) ∷
   rw 0 (q309 c4) ∷
   rw 0 (q310 c4) ∷ []) Eq.refl

private
  q311 : Ws → Eqn
  q311 c4 = eqn (Bx0-2341 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4)
  q312 : Ws → Eqn
  q312 c4 = eqn (CK41 ∷ Toff023 ∷ []) (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4))
  q313 : Ws → Eqn
  q313 c4 = eqn (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) (CK41 ∷ CCZ014 ∷ []) (wp 876 c4)
  q314 : Ws → Eqn
  q314 c4 = eqn (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl 206 (lit c4))
  q315 : Ws → Eqn
  q315 c4 = eqn (CCZ014 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ014 ∷ []) (wp 55 c4)
  q316 : Ws → Eqn
  q316 c4 = eqn (CZ01 ∷ CK41 ∷ CZ01 ∷ CZ01 ∷ []) (CZ01 ∷ CK41 ∷ []) (wp 877 c4)
  q317 : Ws → Eqn
  q317 c4 = eqn (CCZ123 ∷ []) (CZ01 ∷ CCZ123 ∷ CZ01 ∷ []) (wl 1065 (lit c4))
  q318 : Ws → Eqn
  q318 c4 = eqn (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ []) (wl 1066 (lit c4))

-- F2-K1-CS2: 35 steps
lem-F2-K1-CS2 : Ws → ⟪ (CK41 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1-CS2 c4 = derive (CK41 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK41 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 1 (q191 c4) ∷
   rw 1 (q311 c4) ∷
   rw 0 (q312 c4) ∷
   rw⁻ 1 (q313 c4) ∷
   rw 4 (q314 c4) ∷
   rw 3 (q312 c4) ∷
   rw 2 (q314 c4) ∷
   rw 7 (q62 c4) ∷
   rw⁻ 11 (q60 c4) ∷
   rw⁻ 10 (q63 c4) ∷
   rw 9 (q64 c4) ∷
   rw⁻ 8 (q63 c4) ∷
   rw 7 (q65 c4) ∷
   rw⁻ 8 (q62 c4) ∷
   rw⁻ 6 (q315 c4) ∷
   rw⁻ 5 (q313 c4) ∷
   rw 4 (q62 c4) ∷
   rw⁻ 8 (q60 c4) ∷
   rw⁻ 7 (q63 c4) ∷
   rw 6 (q64 c4) ∷
   rw⁻ 5 (q63 c4) ∷
   rw 4 (q65 c4) ∷
   rw⁻ 5 (q62 c4) ∷
   rw⁻ 3 (q315 c4) ∷
   rw 6 (q316 c4) ∷
   rw⁻ 4 (q317 c4) ∷
   rw⁻ 0 (q311 c4) ∷
   rw⁻ 0 (q191 c4) ∷
   rw 1 (q318 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl
