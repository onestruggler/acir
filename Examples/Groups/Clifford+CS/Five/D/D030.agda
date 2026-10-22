{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD030 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D030 (Sᴰ : SD030) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS14-CCZ023 ; lem-comm-CSd14-CCZ023 ; lem-comm-CX40-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX20-TOFF314 ; lem-comm-CX24-TOFF301)

-- The lemmas of other derivation modules (DSig).
private
  lem-sym-ab-at0310243142 : Ws → St 754
  lem-sym-ab-at0310243142 = pickᴰ 0 Sᴰ
  lem-sym-ab-at02102441 : Ws → St 1165
  lem-sym-ab-at02102441 = pickᴰ 1 Sᴰ
  lem-sym-ab-at02142041 : Ws → St 1166
  lem-sym-ab-at02142041 = pickᴰ 2 Sᴰ
  lem-sym-ab-at0310243241 : Ws → St 1167
  lem-sym-ab-at0310243241 = pickᴰ 3 Sᴰ
  lem-sym-ab-at0312243041 : Ws → St 911
  lem-sym-ab-at0312243041 = pickᴰ 4 Sᴰ
  lem-sym-ab-at0314203241 : Ws → St 1168
  lem-sym-ab-at0314203241 = pickᴰ 5 Sᴰ
  lem-sym-ab-at03143041 : Ws → St 913
  lem-sym-ab-at03143041 = pickᴰ 6 Sᴰ
  lem-box-tQ-at0210213443 : Ws → St 77
  lem-box-tQ-at0210213443 = pickᴰ 7 Sᴰ
  lem-box-tQ-at0214203143 : Ws → St 148
  lem-box-tQ-at0214203143 = pickᴰ 8 Sᴰ
  lem-sym-bc-at0310213442 : Ws → St 736
  lem-sym-bc-at0310213442 = pickᴰ 9 Sᴰ
  lem-box-cP-at03122031 : Ws → St 1040
  lem-box-cP-at03122031 = pickᴰ 10 Sᴰ
  lem-box-cP-at0312243041 : Ws → St 956
  lem-box-cP-at0312243041 = pickᴰ 11 Sᴰ
  lem-pairs-at03102132 : Ws → St 971
  lem-pairs-at03102132 = pickᴰ 12 Sᴰ
  lem-pairs-at0310213442 : Ws → St 972
  lem-pairs-at0310213442 = pickᴰ 13 Sᴰ
  lem-sym-bc-at02132031 : Ws → St 1169
  lem-sym-bc-at02132031 = pickᴰ 14 Sᴰ
  lem-sym-bc-at02132130 : Ws → St 1170
  lem-sym-bc-at02132130 = pickᴰ 15 Sᴰ
  lem-sym-bc-at03122031 : Ws → St 1171
  lem-sym-bc-at03122031 = pickᴰ 16 Sᴰ
  lem-sym-bc-at03122130 : Ws → St 1172
  lem-sym-bc-at03122130 = pickᴰ 17 Sᴰ
  lem-sym-bc-at0314203241 : Ws → St 986
  lem-sym-bc-at0314203241 = pickᴰ 18 Sᴰ
  lem-box-perm-1243-at021021 : Ws → St 1173
  lem-box-perm-1243-at021021 = pickᴰ 19 Sᴰ
  lem-box-perm-1243-at0210213443 : Ws → St 1174
  lem-box-perm-1243-at0210213443 = pickᴰ 20 Sᴰ
  lem-box-perm-2341-at0213243041 : Ws → St 1175
  lem-box-perm-2341-at0213243041 = pickᴰ 21 Sᴰ
  lem-box-perm-4123-at0214203143 : Ws → St 1176
  lem-box-perm-4123-at0214203143 = pickᴰ 22 Sᴰ
  lem-pairs-at02102441 : Ws → St 1177
  lem-pairs-at02102441 = pickᴰ 23 Sᴰ
  lem-pairs-at02132130 : Ws → St 1178
  lem-pairs-at02132130 = pickᴰ 24 Sᴰ
  lem-pairs-at0310243241 : Ws → St 1179
  lem-pairs-at0310243241 = pickᴰ 25 Sᴰ
  lem-pairs-at03122130 : Ws → St 1180
  lem-pairs-at03122130 = pickᴰ 26 Sᴰ
  lem-pairs-at0312243041 : Ws → St 1181
  lem-pairs-at0312243041 = pickᴰ 27 Sᴰ
  lem-pairs-at03143041 : Ws → St 1182
  lem-pairs-at03143041 = pickᴰ 28 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx2-3401 ∷ []) (Bx2-4013 ∷ []) (lem-box-perm-2341-at0213243041 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx2-4013 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx3-2401 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ123 ∷ []) (wl 508 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ123 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl 1258 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ012 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl 1273 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ234 ∷ CS12 ∷ []) (CS12 ∷ CCZ234 ∷ []) (wl 415 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ234 ∷ CX20 ∷ []) (CX20 ∷ CCZ234 ∷ []) (wp 366 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CS01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ))
  q10 : Ws → Eqn
  q10 c4 = eqn (CS01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ))
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ123 ∷ CCZ012 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ123 ∷ []) (wl 1330 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (Toff204 ∷ CCZ234 ∷ []) (wp 1166 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ034 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp 377 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (Toff204 ∷ []) (wp 1169 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (K2⁻ ∷ Toff301 ∷ []) (Toff301 ∷ K2⁻ ∷ []) (wl 1331 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CS02 ∷ Toff301 ∷ []) (Toff301 ∷ CS02 ∷ []) (wl 1260 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CX24 ∷ Toff301 ∷ []) (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS04⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS04⁻ ∷ []) (wp 1170 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CS04 ∷ Toff301 ∷ []) (Toff301 ∷ CS04 ∷ []) (wp 897 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (K2 ∷ Toff301 ∷ []) (Toff301 ∷ K2 ∷ []) (wl 1266 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ014 ∷ []) (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp 1143 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ234 ∷ CS14 ∷ []) (CS14 ∷ CCZ234 ∷ []) (wl 452 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ234 ∷ CX40 ∷ []) (CX40 ∷ CCZ234 ∷ []) (wp 1171 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ034 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ034 ∷ []) (wp 129 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Toff204 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff204 ∷ []) (wp 1172 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ014 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ014 ∷ []) (wp 1173 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ []) (wl 765 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CX40 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ123 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ123 ∷ []) (wl 1321 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ123 ∷ CS01 ∷ []) (CS01 ∷ CCZ123 ∷ []) (wl 763 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ014 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ014 ∷ []) (wp 1174 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx2-4013 ∷ []) (Bx2-3401 ∷ []) (lem-box-perm-4123-at0214203143 c4)

-- box-box-1 @0213243041: 105 steps
lem-box-box-1-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ
lem-box-box-1-at0213243041 c4 = derive (Bx2-3401 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 9 (q15 c4) ∷
   rw 8 (q16 c4) ∷
   rw 7 (q17 c4) ∷
   rw 6 (q18 c4) ∷
   rw 5 (q17 c4) ∷
   rw 4 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q14 c4) ∷
   rw 6 (q21 c4) ∷
   rw⁻ 10 (q22 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw 8 (q9 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 5 (q24 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw 5 (q25 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 11 (q15 c4) ∷
   rw 10 (q16 c4) ∷
   rw 9 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw 7 (q17 c4) ∷
   rw 6 (q19 c4) ∷
   rw 5 (q20 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 5 (q8 c4) ∷
   rw 4 (q10 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 3 (q4 c4) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q12 c4) ∷
   rw 2 (q13 c4) ∷
   rw⁻ 1 (q14 c4) ∷
   rw 7 (q15 c4) ∷
   rw 6 (q16 c4) ∷
   rw 5 (q17 c4) ∷
   rw 4 (q18 c4) ∷
   rw 3 (q17 c4) ∷
   rw 2 (q19 c4) ∷
   rw 1 (q20 c4) ∷
   rw 2 (q14 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 8 (q22 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw 4 (q10 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw 3 (q24 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 9 (q15 c4) ∷
   rw 8 (q16 c4) ∷
   rw 7 (q17 c4) ∷
   rw 6 (q18 c4) ∷
   rw 5 (q17 c4) ∷
   rw 4 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q14 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw 5 (q28 c4) ∷
   rw⁻ 4 (q29 c4) ∷
   rw 3 (q28 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw 3 (q31 c4) ∷
   rw 4 (q32 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 1 (q33 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx3-4021 ∷ []) (Bx3-4201 ∷ []) (lem-sym-bc-at0314203241 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx3-4201 ∷ []) (Bx3-2401 ∷ []) (lem-sym-ab-at03143041 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx3-2401 ∷ []) (Bx3-0124 ∷ []) (lem-pairs-at0312243041 c4)

-- box-perm-2431 @0314203241: 3 steps
lem-box-perm-2431-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-2431-at0314203241 c4 = derive (Bx3-4021 ∷ []) (Bx3-0124 ∷ [])
  (rw 0 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 0 (q36 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx2-4031 ∷ []) (Bx2-0431 ∷ []) (lem-sym-ab-at02142041 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx2-0431 ∷ []) (Bx2-3104 ∷ []) (lem-pairs-at02102441 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx2-3104 ∷ []) (Bx2-3014 ∷ []) (lem-sym-bc-at02132130 c4)

-- box-perm-3241 @02142041: 3 steps
lem-box-perm-3241-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-box-perm-3241-at02142041 c4 = derive (Bx2-4031 ∷ []) (Bx2-3014 ∷ [])
  (rw 0 (q37 c4) ∷
   rw 0 (q38 c4) ∷
   rw 0 (q39 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx3-0124 ∷ []) (Bx3-2401 ∷ []) (lem-pairs-at03102132 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Bx3-2401 ∷ []) (Bx3-4201 ∷ []) (lem-sym-ab-at0312243041 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (Bx3-4201 ∷ []) (Bx3-0142 ∷ []) (lem-pairs-at03143041 c4)

-- box-perm-1243 @03102132: 3 steps
lem-box-perm-1243-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-box-perm-1243-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-0142 ∷ [])
  (rw 0 (q40 c4) ∷
   rw 0 (q41 c4) ∷
   rw 0 (q42 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = eqn (Bx3-0142 ∷ []) (Bx3-4201 ∷ []) (lem-pairs-at0310213442 c4)

-- box-perm-1243 @0310213442: 3 steps
lem-box-perm-1243-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-1243-at0310213442 c4 = derive (Bx3-0142 ∷ []) (Bx3-0124 ∷ [])
  (rw 0 (q43 c4) ∷
   rw 0 (q35 c4) ∷
   rw 0 (q36 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx2-3014 ∷ []) (Bx2-3104 ∷ []) (lem-sym-bc-at02132031 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx2-3104 ∷ []) (Bx2-0431 ∷ []) (lem-pairs-at02132130 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx2-0431 ∷ []) (Bx2-4031 ∷ []) (lem-sym-ab-at02102441 c4)

-- box-perm-4213 @02132031: 3 steps
lem-box-perm-4213-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-box-perm-4213-at02132031 c4 = derive (Bx2-3014 ∷ []) (Bx2-4031 ∷ [])
  (rw 0 (q44 c4) ∷
   rw 0 (q45 c4) ∷
   rw 0 (q46 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0412 ∷ []) (lem-sym-bc-at0310213442 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (Bx3-0412 ∷ []) (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4)

-- box-perm-2341 @0312243041: 4 steps
lem-box-perm-2341-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-2341-at0312243041 c4 = derive (Bx3-2401 ∷ []) (Bx3-4012 ∷ [])
  (rw 0 (q41 c4) ∷
   rw 0 (q42 c4) ∷
   rw 0 (q47 c4) ∷
   rw 0 (q48 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = eqn (Bx3-4021 ∷ []) (Bx3-0421 ∷ []) (lem-sym-ab-at0314203241 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (Bx3-0421 ∷ []) (Bx3-2104 ∷ []) (lem-pairs-at0310243241 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (Bx3-2104 ∷ []) (Bx3-2014 ∷ []) (lem-sym-bc-at03122130 c4)

-- box-perm-3241 @0314203241: 3 steps
lem-box-perm-3241-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-box-perm-3241-at0314203241 c4 = derive (Bx3-4021 ∷ []) (Bx3-2014 ∷ [])
  (rw 0 (q49 c4) ∷
   rw 0 (q50 c4) ∷
   rw 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (Bx2-0134 ∷ []) (Bx2-0143 ∷ []) (lem-box-perm-1243-at021021 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx3-2014 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03122031 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ023 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ023 ∷ []) (wp 550 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ234 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl 1360 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ124 ∷ []) (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl 271 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ023 ∷ CS24 ∷ []) (CS24 ∷ CCZ023 ∷ []) (wp 513 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ023 ∷ CX21 ∷ []) (CX21 ∷ CCZ023 ∷ []) (wl 674 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CS14⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CS14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ124 ∷ CCZ234 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ234 ∷ []) (wl 1361 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ023 ∷ Toff201 ∷ CCZ013 ∷ []) (Toff201 ∷ CCZ023 ∷ []) (wl 1362 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ013 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp 997 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ []) (Toff201 ∷ []) (wl 1363 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (K2⁻ ∷ Toff314 ∷ []) (Toff314 ∷ K2⁻ ∷ []) (wl 1364 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CS12 ∷ Toff314 ∷ []) (Toff314 ∷ CS12 ∷ []) (wl 982 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CX20 ∷ Toff314 ∷ []) (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (CS01⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS01⁻ ∷ []) (wp 1203 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (CS01 ∷ Toff314 ∷ []) (Toff314 ∷ CS01 ∷ []) (wp 29 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (K2 ∷ Toff314 ∷ []) (Toff314 ∷ K2 ∷ []) (wl 1365 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp 301 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ023 ∷ CS04 ∷ []) (CS04 ∷ CCZ023 ∷ []) (wp 48 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ023 ∷ CX01 ∷ []) (CX01 ∷ CCZ023 ∷ []) (wl 560 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ013 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ013 ∷ []) (wl 671 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (Toff201 ∷ CCZ013 ∷ CCZ013 ∷ []) (Toff201 ∷ []) (wl 1366 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ []) (wp 698 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (CCZ234 ∷ CS04 ∷ []) (CS04 ∷ CCZ234 ∷ []) (wp 302 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (CX01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ))
  q80 : Ws → Eqn
  q80 c4 = eqn (CCZ234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ234 ∷ []) (wl 451 (lit c4))
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ014 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ014 ∷ []) (wp 1189 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0134 ∷ []) (lem-box-perm-1243-at0210213443 c4)

-- box-box-3 @021021: 105 steps
lem-box-box-3-at021021 : Ws → ⟪ (Bx2-0134 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-box-box-3-at021021 c4 = derive (Bx2-0134 ∷ Bx3-2014 ∷ []) (Bx3-2014 ∷ Bx2-0134 ∷ [])
  (rw 0 (q52 c4) ∷
   rw 0 (q53 c4) ∷
   rw 4 (q54 c4) ∷
   rw⁻ 3 (q55 c4) ∷
   rw 4 (q56 c4) ∷
   rw⁻ 6 (q55 c4) ∷
   rw 5 (q57 c4) ∷
   rw⁻ 9 (q58 c4) ∷
   rw⁻ 8 (q59 c4) ∷
   rw 7 (q60 c4) ∷
   rw⁻ 6 (q59 c4) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 6 (q57 c4) ∷
   rw 6 (q62 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 2 (q63 c4) ∷
   rw 4 (q64 c4) ∷
   rw⁻ 3 (q65 c4) ∷
   rw 9 (q66 c4) ∷
   rw 8 (q67 c4) ∷
   rw 7 (q68 c4) ∷
   rw 6 (q69 c4) ∷
   rw 5 (q68 c4) ∷
   rw 4 (q70 c4) ∷
   rw 3 (q71 c4) ∷
   rw 4 (q65 c4) ∷
   rw 6 (q72 c4) ∷
   rw⁻ 10 (q73 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw 8 (q60 c4) ∷
   rw⁻ 7 (q74 c4) ∷
   rw 6 (q61 c4) ∷
   rw⁻ 7 (q72 c4) ∷
   rw 5 (q75 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   rw 5 (q76 c4) ∷
   rw 6 (q77 c4) ∷
   rw⁻ 5 (q65 c4) ∷
   rw 11 (q66 c4) ∷
   rw 10 (q67 c4) ∷
   rw 9 (q68 c4) ∷
   rw 8 (q69 c4) ∷
   rw 7 (q68 c4) ∷
   rw 6 (q70 c4) ∷
   rw 5 (q71 c4) ∷
   rw 6 (q65 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw 2 (q54 c4) ∷
   rw⁻ 1 (q55 c4) ∷
   rw 2 (q56 c4) ∷
   rw⁻ 4 (q55 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 7 (q58 c4) ∷
   rw⁻ 6 (q59 c4) ∷
   rw 5 (q60 c4) ∷
   rw⁻ 4 (q59 c4) ∷
   rw 3 (q61 c4) ∷
   rw⁻ 4 (q57 c4) ∷
   rw 4 (q62 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw 1 (q54 c4) ∷
   rw⁻ 0 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw⁻ 1 (q65 c4) ∷
   rw 7 (q66 c4) ∷
   rw 6 (q67 c4) ∷
   rw 5 (q68 c4) ∷
   rw 4 (q69 c4) ∷
   rw 3 (q68 c4) ∷
   rw 2 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q65 c4) ∷
   rw 4 (q72 c4) ∷
   rw⁻ 8 (q73 c4) ∷
   rw⁻ 7 (q74 c4) ∷
   rw 6 (q60 c4) ∷
   rw⁻ 5 (q74 c4) ∷
   rw 4 (q61 c4) ∷
   rw⁻ 5 (q72 c4) ∷
   rw 3 (q75 c4) ∷
   rw⁻ 2 (q63 c4) ∷
   rw 3 (q76 c4) ∷
   rw 4 (q77 c4) ∷
   rw⁻ 3 (q65 c4) ∷
   rw 9 (q66 c4) ∷
   rw 8 (q67 c4) ∷
   rw 7 (q68 c4) ∷
   rw 6 (q69 c4) ∷
   rw 5 (q68 c4) ∷
   rw 4 (q70 c4) ∷
   rw 3 (q71 c4) ∷
   rw 4 (q65 c4) ∷
   rw⁻ 0 (q54 c4) ∷
   rw 2 (q72 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw 5 (q79 c4) ∷
   rw⁻ 4 (q80 c4) ∷
   rw 3 (q79 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 3 (q72 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q32 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw 1 (q82 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = eqn (Bx3-2014 ∷ []) (Bx3-2104 ∷ []) (lem-sym-bc-at03122031 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (Bx3-2104 ∷ []) (Bx3-0421 ∷ []) (lem-pairs-at03122130 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (Bx3-0421 ∷ []) (Bx3-4021 ∷ []) (lem-sym-ab-at0310243241 c4)

-- box-perm-4213 @03122031: 3 steps
lem-box-perm-4213-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-box-perm-4213-at03122031 c4 = derive (Bx3-2014 ∷ []) (Bx3-4021 ∷ [])
  (rw 0 (q83 c4) ∷
   rw 0 (q84 c4) ∷
   rw 0 (q85 c4) ∷ []) Eq.refl
