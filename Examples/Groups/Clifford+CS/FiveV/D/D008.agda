{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D008 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-box-tQ-at0410213243 ; lem-box-tQ-at04203243 ; lem-tP-at0410213243 ; lem-tP-at04203243)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-cQ-at02142140 ; lem-cQ-at0410233142 ; lem-cQ-at0410233241 ; lem-cQ-at041041 ; lem-cQ-at0412213043 ; lem-cQ-at04122140 ; lem-cQ-at0412233041 ; lem-cQ-at0412233140 ; lem-cQ-at0413203142 ; lem-cQ-at0413203241 ; lem-cQ-at0413213042 ; lem-cQ-at0413213240 ; lem-cQ-at04133140 ; lem-cQ-at04233240 ; lem-cQ-at0440 ; lem-tP-at0310213442)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CZ12-CCZ034 ; lem-comm-CZ13-CCZ024 ; lem-comm-CZ23-CCZ014)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CZ03-CCZ124)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CZ02-CCZ134 ; lem-comm-CZ23-TOFF401)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx4-0123 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at0410213243 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Toff401 ∷ Toff423 ∷ []) (Toff423 ∷ Toff401 ∷ []) (lem-tP-at0410213243 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ234 ∷ CZ23 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ234 ∷ []) (wl 1491 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ234 ∷ CZ23 ∷ []) (Toff423 ∷ CCZ234 ∷ Toff423 ∷ []) (wl 1492 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CZ23 ∷ Toff401 ∷ []) (Toff401 ∷ CZ23 ∷ []) (lem-comm-CZ23-TOFF401 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ234 ∷ []) (CZ23 ∷ CCZ234 ∷ CZ23 ∷ []) (wl 1493 (lit c4))

-- P-box @0410213243: 8 steps
lem-P-box-at0410213243 : Ws → ⟪ (Toff423 ∷ Bx4-0123 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-P-box-at0410213243 c4 = derive (Toff423 ∷ Bx4-0123 ∷ Toff423 ∷ []) (Bx4-0123 ∷ [])
  (rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ014 ∷ []) (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (wp 218 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ234 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ234 ∷ CZ23 ∷ []) (wl 1494 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CZ23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ234 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ234 ∷ []) (lem-cQ-at0412233041 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ234 ∷ CZ23 ∷ Toff423 ∷ CCZ234 ∷ []) (Toff423 ∷ []) (wl 1495 (lit c4))

-- box-tQ @0412233041: 13 steps
lem-box-tQ-at0412233041 : Ws → ⟪ (Bx4-2301 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at0412233041 c4 = derive (Bx4-2301 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff423 ∷ Bx2-401 ∷ Toff423 ∷ CCZ234 ∷ Bx2-401 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q7 c4) ∷
   re 5 1 (CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw 0 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (CCZ134 ∷ []) (wp 1048 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ024 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ024 ∷ CZ02 ∷ []) (wp 1309 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CZ02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ []) (lem-cQ-at041041 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ024 ∷ CZ02 ∷ Toff402 ∷ CCZ024 ∷ []) (Toff402 ∷ []) (wp 1310 c4)

-- box-tQ @041041: 13 steps
lem-box-tQ-at041041 : Ws → ⟪ (Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at041041 c4 = derive (Bx4-0231 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q12 c4) ∷
   re 5 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q12 c4) ∷
   rw 0 (q13 c4) ∷
   rw 2 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 2 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ124 ∷ []) (wp 516 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ034 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ034 ∷ CZ03 ∷ []) (wp 1391 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CZ03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0410233241 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ034 ∷ CZ03 ∷ Toff403 ∷ CCZ034 ∷ []) (Toff403 ∷ []) (wp 1392 c4)

-- box-tQ @0410233241: 13 steps
lem-box-tQ-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0410233241 c4 = derive (Bx4-0321 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q17 c4) ∷
   re 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 1 (q20 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q22 : Ws → Eqn
  q22 c4 = eqn (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (Toff403 ∷ []) (wp 315 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (Toff412 ∷ []) (wl 467 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (K4⁻ ∷ K4 ∷ []) [] (wl 454 (lit c4))

-- tP @0410233241: 7 steps
lem-tP-at0410233241 : Ws → ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ
lem-tP-at0410233241 c4 = derive (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ [])
  (rw⁻ 0 (q22 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q20 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q23 c4) ∷
   rw 1 (q22 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ034 ∷ []) (wp 598 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ124 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ124 ∷ CZ12 ∷ []) (wl 465 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CZ12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at0412213043 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ124 ∷ CZ12 ∷ Toff412 ∷ CCZ124 ∷ []) (Toff412 ∷ []) (wl 466 (lit c4))

-- box-tQ @0412213043: 13 steps
lem-box-tQ-at0412213043 : Ws → ⟪ (Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at0412213043 c4 = derive (Bx4-2103 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-403 ∷ Toff412 ∷ CCZ124 ∷ Bx2-403 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw 2 (q25 c4) ∷
   re 5 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw 5 (q25 c4) ∷
   rw 0 (q26 c4) ∷
   rw 2 (q27 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q29 c4) ∷ []) Eq.refl

-- tP @0412213043: 7 steps
lem-tP-at0412213043 : Ws → ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-tP-at0412213043 c4 = derive (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ [])
  (rw⁻ 0 (q23 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q28 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ024 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (wp 766 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ134 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ134 ∷ CZ13 ∷ []) (wl 1485 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CZ13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at0413213240 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ134 ∷ CZ13 ∷ Toff413 ∷ CCZ134 ∷ []) (Toff413 ∷ []) (wl 1486 (lit c4))

-- box-tQ @0413213240: 13 steps
lem-box-tQ-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at0413213240 c4 = derive (Bx4-3120 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw⁻ 2 (q30 c4) ∷
   re 5 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw⁻ 5 (q30 c4) ∷
   rw 0 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 2 (q34 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ024 ∷ []) (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (wp 767 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at04233240 c4)

-- box-tQ @04233240: 13 steps
lem-box-tQ-at04233240 : Ws → ⟪ (Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at04233240 c4 = derive (Bx4-1320 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q35 c4) ∷
   re 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q35 c4) ∷
   rw 0 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 1 (q36 c4) ∷
   rw 2 (q34 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ034 ∷ []) (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (wp 733 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at0440 c4)

-- box-tQ @0440: 13 steps
lem-box-tQ-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at0440 c4 = derive (Bx4-1230 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q37 c4) ∷
   re 5 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q37 c4) ∷
   rw 0 (q26 c4) ∷
   rw 2 (q27 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q29 c4) ∷ []) Eq.refl

-- tP @0440: 7 steps
lem-tP-at0440 : Ws → ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-tP-at0440 c4 = derive (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ [])
  (rw⁻ 0 (q23 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q38 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ124 ∷ []) (CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ []) (wl 1596 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0413203142 c4)

-- box-tQ @0413203142: 13 steps
lem-box-tQ-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0413203142 c4 = derive (Bx4-3012 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw⁻ 2 (q39 c4) ∷
   re 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw⁻ 5 (q39 c4) ∷
   rw 0 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 1 (q40 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q41 : Ws → Eqn
  q41 c4 = eqn (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl 624 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl 625 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (K2⁻ ∷ K2 ∷ []) [] (wl 175 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ []) (lem-cQ-at02142140 c4)

-- tP @02142140: 7 steps
lem-tP-at02142140 : Ws → ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ
lem-tP-at02142140 c4 = derive (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ [])
  (rw⁻ 0 (q41 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   rw 2 (q43 c4) ∷
   rw 1 (q44 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   rw 0 (q42 c4) ∷
   rw 1 (q41 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ024 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (wp 211 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at0413213042 c4)

-- box-tQ @0413213042: 13 steps
lem-box-tQ-at0413213042 : Ws → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at0413213042 c4 = derive (Bx4-3102 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw⁻ 2 (q45 c4) ∷
   re 5 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw⁻ 5 (q45 c4) ∷
   rw 0 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 1 (q46 c4) ∷
   rw 2 (q34 c4) ∷ []) Eq.refl

-- tP @0413203142: 7 steps
lem-tP-at0413203142 : Ws → ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ
lem-tP-at0413203142 c4 = derive (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ [])
  (rw⁻ 0 (q22 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q23 c4) ∷
   rw 1 (q22 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = eqn (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (Toff413 ∷ []) (wl 1472 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (K4 ∷ CCZ024 ∷ K4⁻ ∷ []) (Toff402 ∷ []) (wp 1321 c4)

-- tP @0413213240: 7 steps
lem-tP-at0413213240 : Ws → ⟪ (Toff413 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Toff413 ∷ []) ⟫ʷ
lem-tP-at0413213240 c4 = derive (Toff413 ∷ Toff402 ∷ []) (Toff402 ∷ Toff413 ∷ [])
  (rw⁻ 0 (q47 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q33 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q48 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ013 ∷ Toff301 ∷ CZ01 ∷ []) (Toff301 ∷ CCZ013 ∷ []) (wl 1370 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CZ01 ∷ Toff324 ∷ []) (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI))
  q51 : Ws → Eqn
  q51 c4 = eqn (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ []) (lem-tP-at0310213442 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ013 ∷ Toff301 ∷ []) (Toff301 ∷ CZ01 ∷ CCZ013 ∷ []) (wl 1192 (lit c4))

-- t-cP @0310213442: 5 steps
lem-t-cP-at0310213442 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-t-cP-at0310213442 c4 = derive (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw⁻ 2 (q52 c4) ∷
   rw 3 (q51 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = eqn (Bx4-1023 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Toff401 ∷ Toff423 ∷ []) (Toff423 ∷ Toff401 ∷ []) (lem-tP-at04203243 c4)

-- P-box @04203243: 8 steps
lem-P-box-at04203243 : Ws → ⟪ (Toff423 ∷ Bx4-1023 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-P-box-at04203243 c4 = derive (Toff423 ∷ Bx4-1023 ∷ Toff423 ∷ []) (Bx4-1023 ∷ [])
  (rw 1 (q53 c4) ∷
   rw⁻ 0 (q54 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ014 ∷ []) (CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ []) (wp 1436 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ234 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ234 ∷ []) (lem-cQ-at0412233140 c4)

-- box-tQ @0412233140: 13 steps
lem-box-tQ-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at0412233140 c4 = derive (Bx4-2310 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw⁻ 2 (q55 c4) ∷
   re 5 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw⁻ 5 (q55 c4) ∷
   rw 0 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) (CCZ124 ∷ []) (wp 1437 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0410233142 c4)

-- box-tQ @0410233142: 13 steps
lem-box-tQ-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0410233142 c4 = derive (Bx4-0312 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw 2 (q57 c4) ∷
   re 5 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw 5 (q57 c4) ∷
   rw 0 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 1 (q58 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

-- tP @0410233142: 7 steps
lem-tP-at0410233142 : Ws → ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ
lem-tP-at0410233142 c4 = derive (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ [])
  (rw⁻ 0 (q22 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q58 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q23 c4) ∷
   rw 1 (q22 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ034 ∷ []) (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (wp 732 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at04122140 c4)

-- box-tQ @04122140: 13 steps
lem-box-tQ-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at04122140 c4 = derive (Bx4-2130 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw⁻ 2 (q59 c4) ∷
   re 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 0 (q26 c4) ∷
   rw 2 (q27 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q29 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = eqn (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) (wl 453 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (Toff401 ∷ []) (wp 303 c4)

-- tP @0412233140: 7 steps
lem-tP-at0412233140 : Ws → ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ
lem-tP-at0412233140 c4 = derive (Toff423 ∷ Toff401 ∷ []) (Toff401 ∷ Toff423 ∷ [])
  (rw⁻ 0 (q61 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q56 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q61 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ014 ∷ Toff401 ∷ CZ01 ∷ []) (Toff401 ∷ CCZ014 ∷ []) (wp 1456 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CZ01 ∷ Toff423 ∷ []) (Toff423 ∷ CZ01 ∷ []) (c₂ (CZ) (Toffᵗ))
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ014 ∷ Toff401 ∷ []) (Toff401 ∷ CZ01 ∷ CCZ014 ∷ []) (wp 1457 c4)

-- t-cP @04203243: 5 steps
lem-t-cP-at04203243 : Ws → ⟪ (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff401 ∷ []) ⟫ʷ
lem-t-cP-at04203243 c4 = derive (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff401 ∷ [])
  (rw⁻ 0 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 1 (q54 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw 3 (q54 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ124 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (wl 756 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0413203241 c4)

-- box-tQ @0413203241: 13 steps
lem-box-tQ-at0413203241 : Ws → ⟪ (Bx4-3021 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0413203241 c4 = derive (Bx4-3021 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff403 ∷ Bx3-421 ∷ Toff403 ∷ CCZ034 ∷ Bx3-421 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q66 c4) ∷
   re 5 1 (CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw⁻ 5 (q66 c4) ∷
   rw 0 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

-- tP @0413203241: 7 steps
lem-tP-at0413203241 : Ws → ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ
lem-tP-at0413203241 c4 = derive (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ [])
  (rw⁻ 0 (q22 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q23 c4) ∷
   rw 1 (q22 c4) ∷ []) Eq.refl

-- tP @04122140: 7 steps
lem-tP-at04122140 : Ws → ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-tP-at04122140 c4 = derive (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ [])
  (rw⁻ 0 (q23 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (CS04⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ []) (wp 1494 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (CCZ014 ∷ []) (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp 540 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (CCZ234 ∷ CS04 ∷ []) (CS04 ∷ CCZ234 ∷ []) (wp 302 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CCZ234 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ []) (wl 302 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (CS01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ))
  q73 : Ws → Eqn
  q73 c4 = eqn (CS01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ))
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ234 ∷ []) (wp 342 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CS01⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS01⁻ ∷ []) (wp 1495 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ CS01⁻ ∷ CZ01 ∷ CCZ014 ∷ []) (CS04⁻ ∷ []) (wp 1496 c4)

-- CSdu-box-2 @04203243: 17 steps
lem-CSdu-box-2-at04203243 : Ws → ⟪ (CS04⁻ ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at04203243 c4 = derive (CS04⁻ ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ CS04⁻ ∷ [])
  (rw 1 (q53 c4) ∷
   rw 0 (q68 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 7 (q70 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 4 (q69 c4) ∷
   rw 2 (q72 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   rw 4 (q65 c4) ∷
   rw 3 (q75 c4) ∷
   rw 2 (q68 c4) ∷
   rw 3 (q76 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (S4 ∷ Toff401 ∷ []) (Toff401 ∷ S4 ∷ CS01 ∷ CCZ014 ∷ []) (wp 1497 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (CCZ234 ∷ S4 ∷ []) (S4 ∷ CCZ234 ∷ []) (wl 1263 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (CS01 ∷ Toff401 ∷ []) (Toff401 ∷ CS01 ∷ []) (wp 1498 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (S4 ∷ CS01 ∷ CCZ014 ∷ CS01 ∷ CZ01 ∷ CCZ014 ∷ []) (S4 ∷ []) (wp 1499 c4)

-- Su-box @04203243: 17 steps
lem-Su-box-at04203243 : Ws → ⟪ (S4 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ S4 ∷ []) ⟫ʷ
lem-Su-box-at04203243 c4 = derive (S4 ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ S4 ∷ [])
  (rw 1 (q53 c4) ∷
   rw 0 (q77 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 7 (q70 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 4 (q69 c4) ∷
   rw 2 (q73 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   rw 4 (q65 c4) ∷
   rw 3 (q79 c4) ∷
   rw 2 (q77 c4) ∷
   rw 3 (q80 c4) ∷
   rw⁻ 3 (q78 c4) ∷
   rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ014 ∷ []) (CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ []) (wp 1503 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (CCZ234 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ234 ∷ []) (lem-cQ-at04133140 c4)

-- box-tQ @04133140: 13 steps
lem-box-tQ-at04133140 : Ws → ⟪ (Bx4-3210 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at04133140 c4 = derive (Bx4-3210 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff423 ∷ Bx3-410 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw⁻ 2 (q81 c4) ∷
   re 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw⁻ 5 (q81 c4) ∷
   rw 0 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl
