{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D015 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0180 ; wl0181 ; wl0230 ; wl0263 ; wl0288 ; wl0321 ; wl0341 ; wl0381 ; wl0420 ; wl0443 ; wl0509 ; wl0787 ; wl0788 ; wl0923 ; wl0961 ; wl1324 ; wp0022 ; wp0161 ; wp0162 ; wp0308 ; wp0381 ; wp0382 ; wp0383 ; wl0489 ; wl0560 ; wl0619 ; wl0635 ; wl0636 ; wl0755 ; wl1343 ; wp0007 ; wp0019 ; wp0135 ; wp0221 ; wp0506 ; wp0507 ; wp0508 ; wp0671 ; wp0672 ; wp0673 ; wp0674 ; wp0712 ; wp0713 ; wp1068 ; wl0674 ; wp0351 ; wp0694 ; wl0204 ; wl0278 ; wl0279 ; wl0280 ; wl0281 ; wl0282 ; wl0616 ; wp1229 ; wp1230 ; wl0203 ; wl0335 ; wl0448 ; wp0127 ; wp1252 ; wl0677 ; wl1468 ; wl1469 ; wl1470 ; wl1474 ; wl1479 ; wl1480 ; wl1481 ; wl1497 ; wp0306 ; wp1323 ; wl0258 ; wl0411 ; wl0470 ; wl0706 ; wl1020 ; wl1566 ; wl1567 ; wl1568 ; wl1591 ; wp0317 ; wl1600 ; wl1601 ; wl1602 ; wl1604 ; wl1666 ; wl1667 ; wl1668 ; wl0167 ; wl1679 ; wl0835 ; wl1729 ; wp1281 ; wp1500 ; wp1501 ; wp1502)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-nat-SWbc-at021021 ; lem-nat-SWbc-at0210213443 ; lem-nat-SWbc-at0410213243 ; lem-tP-at0213243041 ; lem-tP-at0214233041 ; lem-tP-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-nat-SWbc-at0214233041)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-CXbc-box-at02102331 ; lem-CXbc-box-at02132031 ; lem-CXbc-box-at02132130 ; lem-CXbc-box-at03122031 ; lem-CXbc-box-at03122130 ; lem-CXbc-box-at0314203241 ; lem-CXbc-box-at041041 ; lem-CXbc-box-at04122041 ; lem-CXbc-box-at0412233041 ; lem-CXbc-box-at0413203142 ; lem-CXbc-box-at0413213042 ; lem-CXbc-box-at04233240 ; lem-CXbc-box-at0440 ; lem-CXbc-box-at142142 ; lem-CXcb-box-at02102331 ; lem-CXcb-box-at02132031 ; lem-CXcb-box-at02132130 ; lem-CXcb-box-at03122031 ; lem-CXcb-box-at03122130 ; lem-CXcb-box-at0314203241 ; lem-CXcb-box-at041041 ; lem-CXcb-box-at04122041 ; lem-CXcb-box-at0412233041 ; lem-CXcb-box-at0413203142 ; lem-CXcb-box-at0413213042 ; lem-CXcb-box-at04233240 ; lem-CXcb-box-at0440 ; lem-CXcb-box-at142142 ; lem-QVQ-at0213243041 ; lem-QVQ-at0214233041 ; lem-QVQ-at0310213442 ; lem-SWbc-box-at021021 ; lem-SWbc-box-at0210213443 ; lem-SWbc-box-at0214233041 ; lem-SWbc-box-at0410213243 ; lem-VPQ-at02102331 ; lem-VPQ-at02132031 ; lem-VPQ-at02132130 ; lem-VPQ-at02142041 ; lem-VPQ-at02142140 ; lem-VPQ-at03122031 ; lem-VPQ-at03122130 ; lem-VPQ-at0314203241 ; lem-VPQ-at03143041 ; lem-VPQ-at03243042 ; lem-VPQ-at0410233241 ; lem-VPQ-at04103143 ; lem-VPQ-at04122041 ; lem-VPQ-at0412213043 ; lem-VPQ-at0412233041 ; lem-VPQ-at0413203142 ; lem-VPQ-at04233042 ; lem-VPQ-at0440 ; lem-VPQ-at142142)
open import Examples.Groups.Clifford+CS.Five.D.D013 using (lem-CSdu-box-2-at04122041 ; lem-CXbc-box-at04122140 ; lem-CXbc-box-at0412233140 ; lem-CXbc-box-at0413213240 ; lem-CXbc-box-at04133140 ; lem-CXcb-box-at04122140 ; lem-CXcb-box-at0412233140 ; lem-CXcb-box-at0413213240 ; lem-CXcb-box-at04133140 ; lem-Su-box-at04122041 ; lem-VPQ-at0410233142 ; lem-VPQ-at04122140 ; lem-VPQ-at0412233140 ; lem-VPQ-at0413203241 ; lem-VPQ-at0413213240 ; lem-XCSX-box-2-at04203243)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CCZ012 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (wp0162 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-QVQ-at0214233041 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Toff234 ∷ Toff201 ∷ []) (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0214233041 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Toff234 ∷ Toff234 ∷ []) [] (wl0420 (lit c4))

-- box-cP @0214233041: 12 steps
lem-box-cP-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-box-cP-at0214233041 c4 = derive (Bx2-4301 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 2 (q4 c4) ∷ []) Eq.refl

private
  q5 : Ws → Eqn
  q5 c4 = eqn (CX02 ∷ CX20 ∷ CX02 ∷ []) (Sw02 ∷ []) (wl0509 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CX02 ∷ Bx3-4021 ∷ CX02 ∷ []) (Bx3-4021 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0314203241 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ014 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CX20 ∷ Bx3-4021 ∷ CX20 ∷ []) (Bx3-4021 ∷ CCZ124 ∷ []) (lem-CXcb-box-at0314203241 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ014 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ []) (wp0308 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ124 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0382 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) (wp0383 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp0161 c4)

-- SWbc-box @0314203241: 11 steps
lem-SWbc-box-at0314203241 : Ws → ⟪ (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-SWbc-box-at0314203241 c4 = derive (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) (Bx3-4021 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 4 (q9 c4) ∷
   rw 3 (q10 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 0 (q6 c4) ∷
   rw 1 (q12 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) (Bx2-0143 ∷ []) (lem-SWbc-box-at0210213443 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) (Bx2-0413 ∷ []) (lem-nat-SWbc-at0210213443 c4)

-- sym-bc @0210213443: 2 steps
lem-sym-bc-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym-bc-at0210213443 c4 = derive (Bx2-0143 ∷ []) (Bx2-0413 ∷ [])
  (rw⁻ 0 (q13 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) (Bx2-4301 ∷ []) (lem-SWbc-box-at0214233041 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) (Bx2-4031 ∷ []) (lem-nat-SWbc-at0214233041 c4)

-- sym-bc @0214233041: 2 steps
lem-sym-bc-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-sym-bc-at0214233041 c4 = derive (Bx2-4301 ∷ []) (Bx2-4031 ∷ [])
  (rw⁻ 0 (q15 c4) ∷
   rw 0 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (CX10 ∷ CX01 ∷ CX10 ∷ []) (Sw01 ∷ []) (wl0755 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CX10 ∷ Bx2-3104 ∷ CX10 ∷ []) (Bx2-3104 ∷ CCZ134 ∷ []) (lem-CXbc-box-at02132130 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ134 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0507 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CX01 ∷ Bx2-3104 ∷ CX01 ∷ []) (Bx2-3104 ∷ CCZ034 ∷ []) (lem-CXcb-box-at02132130 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ134 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ []) (wp0712 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ034 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp0506 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) (wp0713 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl0321 (lit c4))

-- SWbc-box @02132130: 11 steps
lem-SWbc-box-at02132130 : Ws → ⟪ (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-SWbc-box-at02132130 c4 = derive (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) (Bx2-3104 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 2 (q18 c4) ∷
   rw 3 (q19 c4) ∷
   rw 1 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw 3 (q22 c4) ∷
   rw 2 (q22 c4) ∷
   rw 3 (q23 c4) ∷
   rw 0 (q18 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = eqn (Toff301 ∷ Toff301 ∷ []) [] (wl0443 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (lem-VPQ-at03143041 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl0230 (lit c4))

-- QVQ @03143041: 3 steps
lem-QVQ-at03143041 : Ws → ⟪ (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-QVQ-at03143041 c4 = derive (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw 4 (q27 c4) ∷ []) Eq.refl

private
  q28 : Ws → Eqn
  q28 c4 = eqn (Toff214 ∷ Toff214 ∷ []) [] (wl0636 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (lem-VPQ-at02132031 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl0263 (lit c4))

-- QVQ @02132031: 3 steps
lem-QVQ-at02132031 : Ws → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at02132031 c4 = derive (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  (rw⁻ 0 (q28 c4) ∷
   rw⁻ 1 (q29 c4) ∷
   rw 4 (q30 c4) ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ []) (CCZ234 ∷ []) (wp1068 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-QVQ-at0310213442 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ []) (lem-tP-at0310213442 c4)

-- box-cP @0310213442: 12 steps
lem-box-cP-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-box-cP-at0310213442 c4 = derive (Bx3-0142 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw 2 (q31 c4) ∷
   re 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw 5 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = eqn (CX01 ∷ CX10 ∷ CX01 ∷ []) (Sw01 ∷ []) (wl0619 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CX01 ∷ Bx2-3014 ∷ CX01 ∷ []) (Bx2-3014 ∷ CCZ034 ∷ []) (lem-CXbc-box-at02132031 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CX10 ∷ Bx2-3014 ∷ CX10 ∷ []) (Bx2-3014 ∷ CCZ134 ∷ []) (lem-CXcb-box-at02132031 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ034 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ []) (wp0221 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (CCZ034 ∷ []) (wp0508 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ034 ∷ CCZ034 ∷ []) [] (wp0007 c4)

-- SWbc-box @02132031: 11 steps
lem-SWbc-box-at02132031 : Ws → ⟪ (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-SWbc-box-at02132031 c4 = derive (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) (Bx2-3014 ∷ [])
  (rw⁻ 0 (q34 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 3 (q22 c4) ∷
   rw 1 (q36 c4) ∷
   rw 4 (q37 c4) ∷
   rw 3 (q19 c4) ∷
   rw 2 (q19 c4) ∷
   rw 3 (q38 c4) ∷
   rw 0 (q35 c4) ∷
   rw 1 (q39 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp0019 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (lem-VPQ-at02132130 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp0135 c4)

-- QVQ @02132130: 3 steps
lem-QVQ-at02132130 : Ws → ⟪ (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-QVQ-at02132130 c4 = derive (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ [])
  (rw⁻ 0 (q40 c4) ∷
   rw⁻ 1 (q41 c4) ∷
   rw 4 (q42 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ012 ∷ []) (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (wl0288 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-QVQ-at0213243041 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Toff234 ∷ Toff201 ∷ []) (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0213243041 c4)

-- box-cP @0213243041: 12 steps
lem-box-cP-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-box-cP-at0213243041 c4 = derive (Bx2-3401 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q43 c4) ∷
   re 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw⁻ 5 (q43 c4) ∷
   rw 2 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q4 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = eqn (CX10 ∷ Bx3-2104 ∷ CX10 ∷ []) (Bx3-2104 ∷ CCZ124 ∷ []) (lem-CXbc-box-at03122130 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ124 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0671 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CX01 ∷ Bx3-2104 ∷ CX01 ∷ []) (Bx3-2104 ∷ CCZ024 ∷ []) (lem-CXcb-box-at03122130 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ124 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ []) (wp0672 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ024 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) (wp0674 c4)

-- SWbc-box @03122130: 11 steps
lem-SWbc-box-at03122130 : Ws → ⟪ (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-SWbc-box-at03122130 c4 = derive (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) (Bx3-2104 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 2 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw 1 (q48 c4) ∷
   rw 4 (q49 c4) ∷
   rw 3 (q50 c4) ∷
   rw 2 (q50 c4) ∷
   rw 3 (q51 c4) ∷
   rw 0 (q46 c4) ∷
   rw 1 (q30 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl0788 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (lem-VPQ-at03122031 c4)

-- QVQ @03122031: 3 steps
lem-QVQ-at03122031 : Ws → ⟪ (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-QVQ-at03122031 c4 = derive (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ [])
  (rw⁻ 0 (q52 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw 4 (q24 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = eqn (CX01 ∷ Bx3-2014 ∷ CX01 ∷ []) (Bx3-2014 ∷ CCZ024 ∷ []) (lem-CXbc-box-at03122031 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CX10 ∷ Bx3-2014 ∷ CX10 ∷ []) (Bx3-2014 ∷ CCZ124 ∷ []) (lem-CXcb-box-at03122031 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ024 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ []) (wp0022 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ []) (CCZ024 ∷ []) (wp0694 c4)

-- SWbc-box @03122031: 11 steps
lem-SWbc-box-at03122031 : Ws → ⟪ (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-SWbc-box-at03122031 c4 = derive (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) (Bx3-2014 ∷ [])
  (rw⁻ 0 (q34 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 2 (q54 c4) ∷
   rw 3 (q50 c4) ∷
   rw 1 (q55 c4) ∷
   rw 4 (q56 c4) ∷
   rw 3 (q47 c4) ∷
   rw 2 (q47 c4) ∷
   rw 3 (q57 c4) ∷
   rw 0 (q54 c4) ∷
   rw 1 (q42 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = eqn (Toff304 ∷ Toff304 ∷ []) [] (wp0351 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (lem-VPQ-at03122130 c4)

-- QVQ @03122130: 3 steps
lem-QVQ-at03122130 : Ws → ⟪ (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-QVQ-at03122130 c4 = derive (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ [])
  (rw⁻ 0 (q58 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw 4 (q39 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (Toff213 ∷ Toff213 ∷ []) [] (wl0180 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (lem-VPQ-at02142041 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0181 (lit c4))

-- QVQ @02142041: 3 steps
lem-QVQ-at02142041 : Ws → ⟪ (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-QVQ-at02142041 c4 = derive (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ [])
  (rw⁻ 0 (q60 c4) ∷
   rw⁻ 1 (q61 c4) ∷
   rw 4 (q62 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (Toff312 ∷ Toff312 ∷ []) [] (wl0489 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (lem-VPQ-at0314203241 c4)

-- QVQ @0314203241: 3 steps
lem-QVQ-at0314203241 : Ws → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0314203241 c4 = derive (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  (rw⁻ 0 (q63 c4) ∷
   rw⁻ 1 (q64 c4) ∷
   rw 4 (q62 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) (Bx2-0134 ∷ []) (lem-SWbc-box-at021021 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) (Bx2-0314 ∷ []) (lem-nat-SWbc-at021021 c4)

-- sym-bc @021021: 2 steps
lem-sym-bc-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym-bc-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-0314 ∷ [])
  (rw⁻ 0 (q65 c4) ∷
   rw 0 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = eqn (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (lem-VPQ-at02102331 c4)

-- QVQ @02102331: 3 steps
lem-QVQ-at02102331 : Ws → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at02102331 c4 = derive (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  (rw⁻ 0 (q28 c4) ∷
   rw⁻ 1 (q67 c4) ∷
   rw 4 (q30 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (CX13 ∷ CX31 ∷ CX13 ∷ []) (Sw13 ∷ []) (wl0278 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (CX13 ∷ Bx0-4132 ∷ CX13 ∷ []) (Bx0-4132 ∷ CCZ124 ∷ []) (lem-CXbc-box-at142142 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (CCZ124 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl0279 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CX31 ∷ Bx0-4132 ∷ CX31 ∷ []) (Bx0-4132 ∷ CCZ234 ∷ []) (lem-CXcb-box-at142142 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (CCZ124 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ []) (wl0280 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ234 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0281 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) (wl0282 (lit c4))

-- SWbc-box @142142: 11 steps
lem-SWbc-box-at142142 : Ws → ⟪ (Sw13 ∷ Bx0-4132 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-SWbc-box-at142142 c4 = derive (Sw13 ∷ Bx0-4132 ∷ Sw13 ∷ []) (Bx0-4132 ∷ [])
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
   rw 1 (q30 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = eqn (Toff302 ∷ Toff302 ∷ []) [] (wl0787 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (lem-VPQ-at03243042 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (CCZ023 ∷ CCZ023 ∷ []) [] (wl0204 (lit c4))

-- QVQ @03243042: 3 steps
lem-QVQ-at03243042 : Ws → ⟪ (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-QVQ-at03243042 c4 = derive (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ [])
  (rw⁻ 0 (q75 c4) ∷
   rw⁻ 1 (q76 c4) ∷
   rw 4 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = eqn (CX31 ∷ CX13 ∷ CX31 ∷ []) (Sw13 ∷ []) (wl0335 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (CX31 ∷ Bx2-0314 ∷ CX31 ∷ []) (Bx2-0314 ∷ CCZ034 ∷ []) (lem-CXbc-box-at02102331 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (CCZ034 ∷ CX13 ∷ []) (CX13 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp1230 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (CX13 ∷ Bx2-0314 ∷ CX13 ∷ []) (Bx2-0314 ∷ CCZ014 ∷ []) (lem-CXcb-box-at02102331 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (CCZ034 ∷ CX31 ∷ []) (CX31 ∷ CCZ034 ∷ []) (wp0127 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ014 ∷ CX31 ∷ []) (CX31 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1229 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ []) (wp1252 c4)

-- SWbc-box @02102331: 11 steps
lem-SWbc-box-at02102331 : Ws → ⟪ (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-SWbc-box-at02102331 c4 = derive (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) (Bx2-0314 ∷ [])
  (rw⁻ 0 (q78 c4) ∷
   rw⁻ 4 (q78 c4) ∷
   rw 2 (q79 c4) ∷
   rw 3 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 4 (q82 c4) ∷
   rw 3 (q83 c4) ∷
   rw 2 (q83 c4) ∷
   rw 3 (q84 c4) ∷
   rw 0 (q79 c4) ∷
   rw 1 (q39 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (Toff023 ∷ Toff023 ∷ []) [] (wl0203 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (lem-VPQ-at142142 c4)

-- QVQ @142142: 3 steps
lem-QVQ-at142142 : Ws → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at142142 c4 = derive (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  (rw⁻ 0 (q85 c4) ∷
   rw⁻ 1 (q86 c4) ∷
   rw 4 (q77 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = eqn (CX03 ∷ CX30 ∷ CX03 ∷ []) (Sw03 ∷ []) (wl0961 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (CX03 ∷ Bx4-2031 ∷ CX03 ∷ []) (Bx4-2031 ∷ CCZ012 ∷ []) (lem-CXbc-box-at04122041 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ012 ∷ CX30 ∷ []) (CX30 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1468 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (CX30 ∷ Bx4-2031 ∷ CX30 ∷ []) (Bx4-2031 ∷ CCZ123 ∷ []) (lem-CXcb-box-at04122041 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (CCZ012 ∷ CX03 ∷ []) (CX03 ∷ CCZ012 ∷ []) (wl0381 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ123 ∷ CX03 ∷ []) (CX03 ∷ CCZ012 ∷ CCZ123 ∷ []) (wl1469 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) (wl1470 (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl0341 (lit c4))

-- SWbc-box @04122041: 11 steps
lem-SWbc-box-at04122041 : Ws → ⟪ (Sw03 ∷ Bx4-2031 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-SWbc-box-at04122041 c4 = derive (Sw03 ∷ Bx4-2031 ∷ Sw03 ∷ []) (Bx4-2031 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw⁻ 4 (q87 c4) ∷
   rw 2 (q88 c4) ∷
   rw 3 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 4 (q91 c4) ∷
   rw 3 (q92 c4) ∷
   rw 2 (q92 c4) ∷
   rw 3 (q93 c4) ∷
   rw 0 (q88 c4) ∷
   rw 1 (q94 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (Toff401 ∷ Toff401 ∷ []) [] (wp0306 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (lem-VPQ-at0412233041 c4)

-- QVQ @0412233041: 3 steps
lem-QVQ-at0412233041 : Ws → ⟪ (CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ []) ⟫ʷ
lem-QVQ-at0412233041 c4 = derive (CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ014 ∷ []) (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ [])
  (rw⁻ 0 (q95 c4) ∷
   rw⁻ 1 (q96 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = eqn (Toff413 ∷ Toff413 ∷ []) [] (wl1474 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) (lem-VPQ-at04122041 c4)

-- QVQ @04122041: 3 steps
lem-QVQ-at04122041 : Ws → ⟪ (CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ []) ⟫ʷ
lem-QVQ-at04122041 c4 = derive (CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ134 ∷ []) (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw⁻ 1 (q98 c4) ∷
   rw 4 (q24 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = eqn (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) (Bx4-0123 ∷ []) (lem-SWbc-box-at0410213243 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) (Bx4-0213 ∷ []) (lem-nat-SWbc-at0410213243 c4)

-- sym-bc @0410213243: 2 steps
lem-sym-bc-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ []) ⟫ʷ
lem-sym-bc-at0410213243 c4 = derive (Bx4-0123 ∷ []) (Bx4-0213 ∷ [])
  (rw⁻ 0 (q99 c4) ∷
   rw 0 (q100 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) (lem-VPQ-at04103143 c4)

-- QVQ @04103143: 3 steps
lem-QVQ-at04103143 : Ws → ⟪ (CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ []) ⟫ʷ
lem-QVQ-at04103143 c4 = derive (CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ134 ∷ []) (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw⁻ 1 (q101 c4) ∷
   rw 4 (q24 c4) ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = eqn (Toff402 ∷ Toff402 ∷ []) [] (wp1323 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) (lem-VPQ-at04233042 c4)

-- QVQ @04233042: 3 steps
lem-QVQ-at04233042 : Ws → ⟪ (CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ []) ⟫ʷ
lem-QVQ-at04233042 c4 = derive (CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ [])
  (rw⁻ 0 (q102 c4) ∷
   rw⁻ 1 (q103 c4) ∷
   rw 4 (q42 c4) ∷ []) Eq.refl

private
  q104 : Ws → Eqn
  q104 c4 = eqn (CX30 ∷ CX03 ∷ CX30 ∷ []) (Sw03 ∷ []) (wl0923 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (CX30 ∷ Bx4-2301 ∷ CX30 ∷ []) (Bx4-2301 ∷ CCZ123 ∷ []) (lem-CXbc-box-at0412233041 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (CX03 ∷ Bx4-2301 ∷ CX03 ∷ []) (Bx4-2301 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0412233041 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ123 ∷ CX30 ∷ []) (CX30 ∷ CCZ123 ∷ []) (wl1324 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) (wl1497 (lit c4))

-- SWbc-box @0412233041: 11 steps
lem-SWbc-box-at0412233041 : Ws → ⟪ (Sw03 ∷ Bx4-2301 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-SWbc-box-at0412233041 c4 = derive (Sw03 ∷ Bx4-2301 ∷ Sw03 ∷ []) (Bx4-2301 ∷ [])
  (rw⁻ 0 (q104 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 2 (q105 c4) ∷
   rw 3 (q92 c4) ∷
   rw 1 (q106 c4) ∷
   rw 4 (q107 c4) ∷
   rw 3 (q89 c4) ∷
   rw 2 (q89 c4) ∷
   rw 3 (q108 c4) ∷
   rw 0 (q105 c4) ∷
   rw 1 (q62 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = eqn (CX23 ∷ CX32 ∷ CX23 ∷ []) (Sw23 ∷ []) (wl0258 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CX23 ∷ Bx4-0231 ∷ CX23 ∷ []) (Bx4-0231 ∷ CCZ012 ∷ []) (lem-CXbc-box-at041041 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (CCZ012 ∷ CX32 ∷ []) (CX32 ∷ CCZ013 ∷ CCZ012 ∷ []) (wl1566 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (CX32 ∷ Bx4-0231 ∷ CX32 ∷ []) (Bx4-0231 ∷ CCZ013 ∷ []) (lem-CXcb-box-at041041 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (CCZ012 ∷ CX23 ∷ []) (CX23 ∷ CCZ012 ∷ []) (wl0411 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (CCZ013 ∷ CX23 ∷ []) (CX23 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl1567 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) (wl1568 (lit c4))

-- SWbc-box @041041: 11 steps
lem-SWbc-box-at041041 : Ws → ⟪ (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ []) ⟫ʷ
lem-SWbc-box-at041041 c4 = derive (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) (Bx4-0231 ∷ [])
  (rw⁻ 0 (q109 c4) ∷
   rw⁻ 4 (q109 c4) ∷
   rw 2 (q110 c4) ∷
   rw 3 (q111 c4) ∷
   rw 1 (q112 c4) ∷
   rw 4 (q113 c4) ∷
   rw 3 (q114 c4) ∷
   rw 2 (q114 c4) ∷
   rw 3 (q115 c4) ∷
   rw 0 (q110 c4) ∷
   rw 1 (q94 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = eqn (Toff412 ∷ Toff412 ∷ []) [] (wl0470 (lit c4))
  q117 : Ws → Eqn
  q117 c4 = eqn (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (lem-VPQ-at0410233241 c4)

-- QVQ @0410233241: 3 steps
lem-QVQ-at0410233241 : Ws → ⟪ (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-QVQ-at0410233241 c4 = derive (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ [])
  (rw⁻ 0 (q116 c4) ∷
   rw⁻ 1 (q117 c4) ∷
   rw 4 (q30 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = eqn (Toff403 ∷ Toff403 ∷ []) [] (wp0317 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (lem-VPQ-at0412213043 c4)

-- QVQ @0412213043: 3 steps
lem-QVQ-at0412213043 : Ws → ⟪ (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-QVQ-at0412213043 c4 = derive (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ [])
  (rw⁻ 0 (q118 c4) ∷
   rw⁻ 1 (q119 c4) ∷
   rw 4 (q39 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = eqn (CX32 ∷ CX23 ∷ CX32 ∷ []) (Sw23 ∷ []) (wl1020 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (CX32 ∷ Bx4-1320 ∷ CX32 ∷ []) (Bx4-1320 ∷ CCZ013 ∷ []) (lem-CXbc-box-at04233240 c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (CX23 ∷ Bx4-1320 ∷ CX23 ∷ []) (Bx4-1320 ∷ CCZ012 ∷ []) (lem-CXcb-box-at04233240 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (CCZ013 ∷ CX32 ∷ []) (CX32 ∷ CCZ013 ∷ []) (wl0706 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) (wl1591 (lit c4))

-- SWbc-box @04233240: 11 steps
lem-SWbc-box-at04233240 : Ws → ⟪ (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-SWbc-box-at04233240 c4 = derive (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) (Bx4-1320 ∷ [])
  (rw⁻ 0 (q120 c4) ∷
   rw⁻ 4 (q120 c4) ∷
   rw 2 (q121 c4) ∷
   rw 3 (q114 c4) ∷
   rw 1 (q122 c4) ∷
   rw 4 (q123 c4) ∷
   rw 3 (q111 c4) ∷
   rw 2 (q111 c4) ∷
   rw 3 (q124 c4) ∷
   rw 0 (q121 c4) ∷
   rw 1 (q27 c4) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = eqn (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (lem-VPQ-at0440 c4)

-- QVQ @0440: 3 steps
lem-QVQ-at0440 : Ws → ⟪ (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-QVQ-at0440 c4 = derive (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ [])
  (rw⁻ 0 (q118 c4) ∷
   rw⁻ 1 (q125 c4) ∷
   rw 4 (q39 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (CX01 ∷ Bx4-3012 ∷ CX01 ∷ []) (Bx4-3012 ∷ CCZ023 ∷ []) (lem-CXbc-box-at0413203142 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (CCZ023 ∷ CX10 ∷ []) (CX10 ∷ CCZ123 ∷ CCZ023 ∷ []) (wl1600 (lit c4))
  q128 : Ws → Eqn
  q128 c4 = eqn (CX10 ∷ Bx4-3012 ∷ CX10 ∷ []) (Bx4-3012 ∷ CCZ123 ∷ []) (lem-CXcb-box-at0413203142 c4)
  q129 : Ws → Eqn
  q129 c4 = eqn (CCZ023 ∷ CX01 ∷ []) (CX01 ∷ CCZ023 ∷ []) (wl0560 (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (CCZ123 ∷ CX01 ∷ []) (CX01 ∷ CCZ023 ∷ CCZ123 ∷ []) (wl1601 (lit c4))
  q131 : Ws → Eqn
  q131 c4 = eqn (CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ []) (wl1602 (lit c4))

-- SWbc-box @0413203142: 11 steps
lem-SWbc-box-at0413203142 : Ws → ⟪ (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-SWbc-box-at0413203142 c4 = derive (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) (Bx4-3012 ∷ [])
  (rw⁻ 0 (q34 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 2 (q126 c4) ∷
   rw 3 (q127 c4) ∷
   rw 1 (q128 c4) ∷
   rw 4 (q129 c4) ∷
   rw 3 (q130 c4) ∷
   rw 2 (q130 c4) ∷
   rw 3 (q131 c4) ∷
   rw 0 (q126 c4) ∷
   rw 1 (q77 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = eqn (Toff203 ∷ Toff203 ∷ []) [] (wl0635 (lit c4))
  q133 : Ws → Eqn
  q133 c4 = eqn (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (lem-VPQ-at02142140 c4)

-- QVQ @02142140: 3 steps
lem-QVQ-at02142140 : Ws → ⟪ (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-QVQ-at02142140 c4 = derive (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ [])
  (rw⁻ 0 (q132 c4) ∷
   rw⁻ 1 (q133 c4) ∷
   rw 4 (q77 c4) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = eqn (CX10 ∷ Bx4-3102 ∷ CX10 ∷ []) (Bx4-3102 ∷ CCZ123 ∷ []) (lem-CXbc-box-at0413213042 c4)
  q135 : Ws → Eqn
  q135 c4 = eqn (CX01 ∷ Bx4-3102 ∷ CX01 ∷ []) (Bx4-3102 ∷ CCZ023 ∷ []) (lem-CXcb-box-at0413213042 c4)
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ123 ∷ CX10 ∷ []) (CX10 ∷ CCZ123 ∷ []) (wl0616 (lit c4))
  q137 : Ws → Eqn
  q137 c4 = eqn (CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) (wl1604 (lit c4))

-- SWbc-box @0413213042: 11 steps
lem-SWbc-box-at0413213042 : Ws → ⟪ (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-SWbc-box-at0413213042 c4 = derive (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) (Bx4-3102 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 2 (q134 c4) ∷
   rw 3 (q130 c4) ∷
   rw 1 (q135 c4) ∷
   rw 4 (q136 c4) ∷
   rw 3 (q127 c4) ∷
   rw 2 (q127 c4) ∷
   rw 3 (q137 c4) ∷
   rw 0 (q134 c4) ∷
   rw 1 (q62 c4) ∷ []) Eq.refl

private
  q138 : Ws → Eqn
  q138 c4 = eqn (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (lem-VPQ-at0413203142 c4)

-- QVQ @0413203142: 3 steps
lem-QVQ-at0413203142 : Ws → ⟪ (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-QVQ-at0413203142 c4 = derive (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ [])
  (rw⁻ 0 (q116 c4) ∷
   rw⁻ 1 (q138 c4) ∷
   rw 4 (q30 c4) ∷ []) Eq.refl

private
  q139 : Ws → Eqn
  q139 c4 = eqn (CX23 ∷ Bx4-1230 ∷ CX23 ∷ []) (Bx4-1230 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0440 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (CX32 ∷ Bx4-1230 ∷ CX32 ∷ []) (Bx4-1230 ∷ CCZ013 ∷ []) (lem-CXcb-box-at0440 c4)

-- SWbc-box @0440: 11 steps
lem-SWbc-box-at0440 : Ws → ⟪ (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-SWbc-box-at0440 c4 = derive (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) (Bx4-1230 ∷ [])
  (rw⁻ 0 (q109 c4) ∷
   rw⁻ 4 (q109 c4) ∷
   rw 2 (q139 c4) ∷
   rw 3 (q111 c4) ∷
   rw 1 (q140 c4) ∷
   rw 4 (q113 c4) ∷
   rw 3 (q114 c4) ∷
   rw 2 (q114 c4) ∷
   rw 3 (q115 c4) ∷
   rw 0 (q139 c4) ∷
   rw 1 (q94 c4) ∷ []) Eq.refl

private
  q141 : Ws → Eqn
  q141 c4 = eqn (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) (lem-VPQ-at0413213240 c4)

-- QVQ @0413213240: 3 steps
lem-QVQ-at0413213240 : Ws → ⟪ (CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ []) ⟫ʷ
lem-QVQ-at0413213240 c4 = derive (CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ [])
  (rw⁻ 0 (q102 c4) ∷
   rw⁻ 1 (q141 c4) ∷
   rw 4 (q42 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = eqn (CX31 ∷ Bx4-2310 ∷ CX31 ∷ []) (Bx4-2310 ∷ CCZ023 ∷ []) (lem-CXbc-box-at0412233140 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (CCZ023 ∷ CX13 ∷ []) (CX13 ∷ CCZ012 ∷ CCZ023 ∷ []) (wl1666 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (CX13 ∷ Bx4-2310 ∷ CX13 ∷ []) (Bx4-2310 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0412233140 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (CCZ023 ∷ CX31 ∷ []) (CX31 ∷ CCZ023 ∷ []) (wl1343 (lit c4))
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ012 ∷ CX31 ∷ []) (CX31 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl1667 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ []) (CCZ023 ∷ []) (wl1668 (lit c4))

-- SWbc-box @0412233140: 11 steps
lem-SWbc-box-at0412233140 : Ws → ⟪ (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-SWbc-box-at0412233140 c4 = derive (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) (Bx4-2310 ∷ [])
  (rw⁻ 0 (q78 c4) ∷
   rw⁻ 4 (q78 c4) ∷
   rw 2 (q142 c4) ∷
   rw 3 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   rw 4 (q145 c4) ∷
   rw 3 (q146 c4) ∷
   rw 2 (q146 c4) ∷
   rw 3 (q147 c4) ∷
   rw 0 (q142 c4) ∷
   rw 1 (q77 c4) ∷ []) Eq.refl

private
  q148 : Ws → Eqn
  q148 c4 = eqn (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (lem-VPQ-at0410233142 c4)

-- QVQ @0410233142: 3 steps
lem-QVQ-at0410233142 : Ws → ⟪ (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-QVQ-at0410233142 c4 = derive (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ [])
  (rw⁻ 0 (q116 c4) ∷
   rw⁻ 1 (q148 c4) ∷
   rw 4 (q30 c4) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = eqn (CX13 ∷ Bx4-2130 ∷ CX13 ∷ []) (Bx4-2130 ∷ CCZ012 ∷ []) (lem-CXbc-box-at04122140 c4)
  q150 : Ws → Eqn
  q150 c4 = eqn (CX31 ∷ Bx4-2130 ∷ CX31 ∷ []) (Bx4-2130 ∷ CCZ023 ∷ []) (lem-CXcb-box-at04122140 c4)
  q151 : Ws → Eqn
  q151 c4 = eqn (CCZ012 ∷ CX13 ∷ []) (CX13 ∷ CCZ012 ∷ []) (wl0167 (lit c4))
  q152 : Ws → Eqn
  q152 c4 = eqn (CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) (wl1679 (lit c4))

-- SWbc-box @04122140: 11 steps
lem-SWbc-box-at04122140 : Ws → ⟪ (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-SWbc-box-at04122140 c4 = derive (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) (Bx4-2130 ∷ [])
  (rw⁻ 0 (q68 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 2 (q149 c4) ∷
   rw 3 (q146 c4) ∷
   rw 1 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw 3 (q143 c4) ∷
   rw 2 (q143 c4) ∷
   rw 3 (q152 c4) ∷
   rw 0 (q149 c4) ∷
   rw 1 (q94 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = eqn (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (lem-VPQ-at0412233140 c4)

-- QVQ @0412233140: 3 steps
lem-QVQ-at0412233140 : Ws → ⟪ (CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ []) ⟫ʷ
lem-QVQ-at0412233140 c4 = derive (CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ014 ∷ []) (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ [])
  (rw⁻ 0 (q95 c4) ∷
   rw⁻ 1 (q153 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = eqn (S4 ∷ CS04⁻ ∷ []) (X0 ∷ CS04 ∷ X0 ∷ []) (wp1281 c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (CS04⁻ ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at04122041 c4)
  q156 : Ws → Eqn
  q156 c4 = eqn (S4 ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ S4 ∷ []) (lem-Su-box-at04122041 c4)

-- XCSX-box-2 @04122041: 4 steps
lem-XCSX-box-2-at04122041 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-XCSX-box-2-at04122041 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (rw⁻ 0 (q154 c4) ∷
   rw 1 (q155 c4) ∷
   rw 0 (q156 c4) ∷
   rw 1 (q154 c4) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = eqn (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (lem-VPQ-at0413203241 c4)

-- QVQ @0413203241: 3 steps
lem-QVQ-at0413203241 : Ws → ⟪ (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-QVQ-at0413203241 c4 = derive (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ [])
  (rw⁻ 0 (q116 c4) ∷
   rw⁻ 1 (q157 c4) ∷
   rw 4 (q30 c4) ∷ []) Eq.refl

private
  q158 : Ws → Eqn
  q158 c4 = eqn (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (lem-VPQ-at04122140 c4)

-- QVQ @04122140: 3 steps
lem-QVQ-at04122140 : Ws → ⟪ (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-QVQ-at04122140 c4 = derive (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ [])
  (rw⁻ 0 (q118 c4) ∷
   rw⁻ 1 (q158 c4) ∷
   rw 4 (q39 c4) ∷ []) Eq.refl

private
  q159 : Ws → Eqn
  q159 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-XCSX-box-2-at04203243 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (Toff302 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ Toff302 ∷ []) (wp1500 c4)
  q161 : Ws → Eqn
  q161 c4 = eqn (CS13 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS13 ∷ []) (wp1501 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (CS13⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS13⁻ ∷ []) (wp1502 c4)

-- F4-S0-CS1 @0440: 13 steps
lem-F4-S0-CS1-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-CS1-at0440 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (re 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 0 (q159 c4) ∷
   rw⁻ 1 (q160 c4) ∷
   rw⁻ 2 (q161 c4) ∷
   rw⁻ 3 (q160 c4) ∷
   rw⁻ 4 (q162 c4) ∷
   re 2 1 (Sb4-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 0 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 1 (q154 c4) ∷
   rw 1 (q154 c4) ∷ []) Eq.refl

private
  q163 : Ws → Eqn
  q163 c4 = eqn (CX21 ∷ CX12 ∷ CX21 ∷ []) (Sw12 ∷ []) (wl0835 (lit c4))
  q164 : Ws → Eqn
  q164 c4 = eqn (CX21 ∷ Bx4-3210 ∷ CX21 ∷ []) (Bx4-3210 ∷ CCZ023 ∷ []) (lem-CXbc-box-at04133140 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (CCZ023 ∷ CX12 ∷ []) (CX12 ∷ CCZ013 ∷ CCZ023 ∷ []) (wl1480 (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (CX12 ∷ Bx4-3210 ∷ CX12 ∷ []) (Bx4-3210 ∷ CCZ013 ∷ []) (lem-CXcb-box-at04133140 c4)
  q167 : Ws → Eqn
  q167 c4 = eqn (CCZ023 ∷ CX21 ∷ []) (CX21 ∷ CCZ023 ∷ []) (wl0674 (lit c4))
  q168 : Ws → Eqn
  q168 c4 = eqn (CCZ013 ∷ CX21 ∷ []) (CX21 ∷ CCZ023 ∷ CCZ013 ∷ []) (wl1479 (lit c4))
  q169 : Ws → Eqn
  q169 c4 = eqn (CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ []) (CCZ023 ∷ []) (wl1729 (lit c4))

-- SWbc-box @04133140: 11 steps
lem-SWbc-box-at04133140 : Ws → ⟪ (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ []) ⟫ʷ
lem-SWbc-box-at04133140 c4 = derive (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) (Bx4-3210 ∷ [])
  (rw⁻ 0 (q163 c4) ∷
   rw⁻ 4 (q163 c4) ∷
   rw 2 (q164 c4) ∷
   rw 3 (q165 c4) ∷
   rw 1 (q166 c4) ∷
   rw 4 (q167 c4) ∷
   rw 3 (q168 c4) ∷
   rw 2 (q168 c4) ∷
   rw 3 (q169 c4) ∷
   rw 0 (q164 c4) ∷
   rw 1 (q77 c4) ∷ []) Eq.refl

private
  q170 : Ws → Eqn
  q170 c4 = eqn (CX12 ∷ CX21 ∷ CX12 ∷ []) (Sw12 ∷ []) (wl0677 (lit c4))
  q171 : Ws → Eqn
  q171 c4 = eqn (CX12 ∷ Bx4-3120 ∷ CX12 ∷ []) (Bx4-3120 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0413213240 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (CX21 ∷ Bx4-3120 ∷ CX21 ∷ []) (Bx4-3120 ∷ CCZ023 ∷ []) (lem-CXcb-box-at0413213240 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (CCZ013 ∷ CX12 ∷ []) (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) (wl1481 (lit c4))

-- SWbc-box @0413213240: 11 steps
lem-SWbc-box-at0413213240 : Ws → ⟪ (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-SWbc-box-at0413213240 c4 = derive (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) (Bx4-3120 ∷ [])
  (rw⁻ 0 (q170 c4) ∷
   rw⁻ 4 (q170 c4) ∷
   rw 2 (q171 c4) ∷
   rw 3 (q168 c4) ∷
   rw 1 (q172 c4) ∷
   rw 4 (q173 c4) ∷
   rw 3 (q165 c4) ∷
   rw 2 (q165 c4) ∷
   rw 3 (q174 c4) ∷
   rw 0 (q171 c4) ∷
   rw 1 (q27 c4) ∷ []) Eq.refl
