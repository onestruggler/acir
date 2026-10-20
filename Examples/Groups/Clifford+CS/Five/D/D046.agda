{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D046 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F4-I-K2 ; lem-F4-I-S3 ; lem-F4-K2-K2 ; lem-F4-S3-I ; lem-F4-S3-K2 ; lem-F4-S3-S3)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-K2-at02132031 ; lem-F4-I-S3-at02132031 ; lem-F4-K2-K2-at02132031 ; lem-F4-S3-I-at02132031 ; lem-F4-S3-K2-at02132031 ; lem-F4-S3-S3-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at03203442)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at02132130 ; lem-box-cP-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-F4-CS2-I ; lem-F4-CS2-S3 ; lem-F4-I-CS2 ; lem-F4-K2-CS2 ; lem-F4-S3-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-F4-CS2-K2)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F4-CS2-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-perm-2341-at13243142)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-F4-CS2-CS2-at02132031 ; lem-F4-CS2-I-at02132031 ; lem-F4-CS2-K2-at02132031 ; lem-F4-CS2-S3-at02132031 ; lem-F4-I-CS2-at02132031 ; lem-F4-K2-CS2-at02132031 ; lem-F4-S3-CS2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F5-23)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-F5-23-at02132031 ; lem-box-perm-2341-at03122130 ; lem-box-perm-4123-at03203442 ; lem-box-perm-4123-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS04-CCZ123 ; lem-comm-CSd04-CCZ123 ; lem-comm-CX04-TOFF312 ; lem-comm-CX41-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX31-TOFF204)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx3-2104 ∷ []) (Bx3-1042 ∷ []) (lem-box-perm-2341-at03122130 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx3-1042 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03203442 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx2-3104 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02132130 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ123 ∷ []) (wl 508 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ234 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp 559 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ034 ∷ []) (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp 1193 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ123 ∷ CS34 ∷ []) (CS34 ∷ CCZ123 ∷ []) (wl 492 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ123 ∷ CX30 ∷ []) (CX30 ∷ CCZ123 ∷ []) (wl 1324 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS04⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CS04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ234 ∷ CCZ034 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ234 ∷ []) (wp 1219 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (Toff301 ∷ CCZ123 ∷ []) (wl 1256 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ012 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp 1150 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (Toff301 ∷ []) (wl 1380 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (K3⁻ ∷ Toff204 ∷ []) (Toff204 ∷ K3⁻ ∷ []) (wp 1220 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS03 ∷ Toff204 ∷ []) (Toff204 ∷ CS03 ∷ []) (wp 562 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CX31 ∷ Toff204 ∷ []) (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS01⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS01⁻ ∷ []) (wp 1221 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CS01 ∷ Toff204 ∷ []) (Toff204 ∷ CS01 ∷ []) (wp 948 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (K3 ∷ Toff204 ∷ []) (Toff204 ∷ K3 ∷ []) (wp 1222 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ014 ∷ []) (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp 341 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ []) (wl 765 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ123 ∷ CX10 ∷ []) (CX10 ∷ CCZ123 ∷ []) (wl 616 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ012 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ012 ∷ []) (wl 298 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (Toff301 ∷ CCZ012 ∷ CCZ012 ∷ []) (Toff301 ∷ []) (wl 1347 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ014 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ014 ∷ []) (wp 1174 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ234 ∷ CS14 ∷ []) (CS14 ∷ CCZ234 ∷ []) (wl 452 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CX10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ234 ∷ []) (wp 342 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ234 ∷ CS04 ∷ []) (CS04 ∷ CCZ234 ∷ []) (wp 302 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ014 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ014 ∷ []) (wp 1173 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx3-1042 ∷ []) (Bx3-2104 ∷ []) (lem-box-perm-4123-at03203442 c4)

-- box-box-1 @03122130: 105 steps
lem-box-box-1-at03122130 : Ws → ⟪ (Bx3-2104 ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ Bx3-2104 ∷ []) ⟫ʷ
lem-box-box-1-at03122130 c4 = derive (Bx3-2104 ∷ Bx2-3104 ∷ []) (Bx2-3104 ∷ Bx3-2104 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   rw⁻ 5 (q4 c4) ∷
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
   rw⁻ 1 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 5 (q8 c4) ∷
   rw 4 (q10 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw⁻ 3 (q4 c4) ∷
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
  q34 c4 = eqn (Bx0-3412 ∷ []) (Bx0-4123 ∷ []) (lem-box-perm-2341-at13243142 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx0-4123 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at14213243 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ023 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ023 ∷ []) (wp 575 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ023 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl 1213 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl 348 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) (wp 3 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ034 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ []) (wp 221 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CS12⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ023 ∷ CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ023 ∷ []) (wl 1395 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (Toff014 ∷ CCZ034 ∷ []) (wp 1114 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ134 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl 1356 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ []) (Toff014 ∷ []) (wp 1239 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (K0⁻ ∷ Toff312 ∷ []) (Toff312 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ))
  q49 : Ws → Eqn
  q49 c4 = eqn (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) (wl 501 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CX04 ∷ Toff312 ∷ []) (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS14⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS14⁻ ∷ []) (wl 778 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) (wl 499 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (K0 ∷ Toff312 ∷ []) (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ))
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl 334 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ []) (wp 108 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ034 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ []) (wp 357 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ034 ∷ []) (wp 103 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (Toff014 ∷ CCZ134 ∷ CCZ134 ∷ []) (Toff014 ∷ []) (wp 1240 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ124 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ []) (wl 871 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ023 ∷ CS24 ∷ []) (CS24 ∷ CCZ023 ∷ []) (wp 513 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CX41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ023 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ023 ∷ []) (wl 620 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ023 ∷ CS12 ∷ []) (CS12 ∷ CCZ023 ∷ []) (wl 621 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ []) (wp 822 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl 263 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (Bx0-4123 ∷ []) (Bx0-3412 ∷ []) (lem-box-perm-4123-at14213243 c4)

-- box-box-1 @13243142: 105 steps
lem-box-box-1-at13243142 : Ws → ⟪ (Bx0-3412 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-box-box-1-at13243142 c4 = derive (Bx0-3412 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Bx0-3412 ∷ [])
  (rw 0 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 4 (q36 c4) ∷
   rw 3 (q37 c4) ∷
   rw 4 (q38 c4) ∷
   rw 6 (q39 c4) ∷
   rw⁻ 10 (q40 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw 6 (q43 c4) ∷
   rw⁻ 7 (q39 c4) ∷
   rw 5 (q37 c4) ∷
   rw 6 (q44 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 2 (q45 c4) ∷
   rw 4 (q46 c4) ∷
   rw⁻ 3 (q47 c4) ∷
   rw 9 (q48 c4) ∷
   rw 8 (q49 c4) ∷
   rw 7 (q50 c4) ∷
   rw 6 (q51 c4) ∷
   rw 5 (q50 c4) ∷
   rw 4 (q52 c4) ∷
   rw 3 (q53 c4) ∷
   rw 4 (q47 c4) ∷
   rw 6 (q54 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   rw⁻ 9 (q56 c4) ∷
   rw 8 (q42 c4) ∷
   rw⁻ 7 (q56 c4) ∷
   rw 6 (q43 c4) ∷
   rw⁻ 7 (q54 c4) ∷
   rw⁻ 5 (q57 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw 5 (q58 c4) ∷
   rw 6 (q59 c4) ∷
   rw⁻ 5 (q47 c4) ∷
   rw 11 (q48 c4) ∷
   rw 10 (q49 c4) ∷
   rw 9 (q50 c4) ∷
   rw 8 (q51 c4) ∷
   rw 7 (q50 c4) ∷
   rw 6 (q52 c4) ∷
   rw 5 (q53 c4) ∷
   rw 6 (q47 c4) ∷
   rw⁻ 2 (q36 c4) ∷
   rw 2 (q36 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q38 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 8 (q40 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw 3 (q37 c4) ∷
   rw 4 (q44 c4) ∷
   rw⁻ 1 (q36 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q45 c4) ∷
   rw 2 (q46 c4) ∷
   rw⁻ 1 (q47 c4) ∷
   rw 7 (q48 c4) ∷
   rw 6 (q49 c4) ∷
   rw 5 (q50 c4) ∷
   rw 4 (q51 c4) ∷
   rw 3 (q50 c4) ∷
   rw 2 (q52 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q47 c4) ∷
   rw 4 (q54 c4) ∷
   rw⁻ 8 (q55 c4) ∷
   rw⁻ 7 (q56 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 5 (q56 c4) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 5 (q54 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 2 (q45 c4) ∷
   rw 3 (q58 c4) ∷
   rw 4 (q59 c4) ∷
   rw⁻ 3 (q47 c4) ∷
   rw 9 (q48 c4) ∷
   rw 8 (q49 c4) ∷
   rw 7 (q50 c4) ∷
   rw 6 (q51 c4) ∷
   rw 5 (q50 c4) ∷
   rw 4 (q52 c4) ∷
   rw 3 (q53 c4) ∷
   rw 4 (q47 c4) ∷
   rw⁻ 0 (q36 c4) ∷
   rw 2 (q54 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw 3 (q61 c4) ∷
   rw⁻ 2 (q63 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw 3 (q64 c4) ∷
   rw 4 (q65 c4) ∷
   rw⁻ 1 (q35 c4) ∷
   rw 1 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ []) (lem-F5-23 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (K2 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl 1409 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-CS2 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K2 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-K2 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (S3 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl 1410 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-CS2 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-K2 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl 1411 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K2 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-I c4)

-- deb-P-hi-split-a: 136 steps
lem-deb-P-hi-split-a : Ws → ⟪ (CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-deb-P-hi-split-a c4 = derive (CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ [])
  (rw⁻ 0 (q67 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   rw⁻ 3 (q68 c4) ∷
   rw⁻ 8 (q67 c4) ∷
   rw⁻ 7 (q68 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   rw⁻ 12 (q67 c4) ∷
   rw⁻ 11 (q68 c4) ∷
   rw⁻ 10 (q68 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw⁻ 16 (q67 c4) ∷
   rw⁻ 15 (q68 c4) ∷
   rw⁻ 14 (q68 c4) ∷
   rw⁻ 13 (q68 c4) ∷
   rw⁻ 12 (q68 c4) ∷
   rw⁻ 20 (q67 c4) ∷
   rw⁻ 19 (q68 c4) ∷
   rw⁻ 18 (q68 c4) ∷
   rw⁻ 17 (q68 c4) ∷
   rw⁻ 16 (q68 c4) ∷
   rw⁻ 15 (q68 c4) ∷
   rw⁻ 24 (q67 c4) ∷
   rw⁻ 23 (q68 c4) ∷
   rw⁻ 22 (q68 c4) ∷
   rw⁻ 21 (q68 c4) ∷
   rw⁻ 20 (q68 c4) ∷
   rw⁻ 19 (q68 c4) ∷
   rw⁻ 18 (q68 c4) ∷
   rw 28 (q69 c4) ∷
   rw⁻ 27 (q70 c4) ∷
   rw⁻ 26 (q70 c4) ∷
   rw⁻ 25 (q70 c4) ∷
   rw⁻ 24 (q70 c4) ∷
   rw⁻ 23 (q70 c4) ∷
   rw⁻ 22 (q70 c4) ∷
   rw⁻ 21 (q70 c4) ∷
   rw⁻ 32 (q67 c4) ∷
   rw⁻ 31 (q71 c4) ∷
   rw⁻ 30 (q68 c4) ∷
   rw⁻ 29 (q68 c4) ∷
   rw⁻ 28 (q68 c4) ∷
   rw⁻ 27 (q68 c4) ∷
   rw⁻ 26 (q68 c4) ∷
   rw⁻ 25 (q68 c4) ∷
   rw⁻ 24 (q68 c4) ∷
   rw 36 (q69 c4) ∷
   rw⁻ 35 (q70 c4) ∷
   rw⁻ 34 (q72 c4) ∷
   rw⁻ 33 (q70 c4) ∷
   rw⁻ 32 (q70 c4) ∷
   rw⁻ 31 (q70 c4) ∷
   rw⁻ 30 (q70 c4) ∷
   rw⁻ 29 (q70 c4) ∷
   rw⁻ 28 (q70 c4) ∷
   rw⁻ 27 (q70 c4) ∷
   rw⁻ 40 (q67 c4) ∷
   rw⁻ 39 (q71 c4) ∷
   rw⁻ 38 (q68 c4) ∷
   rw⁻ 37 (q71 c4) ∷
   rw⁻ 36 (q68 c4) ∷
   rw⁻ 35 (q68 c4) ∷
   rw⁻ 34 (q68 c4) ∷
   rw⁻ 33 (q68 c4) ∷
   rw⁻ 32 (q68 c4) ∷
   rw⁻ 31 (q68 c4) ∷
   rw⁻ 30 (q68 c4) ∷
   rw 44 (q73 c4) ∷
   rw⁻ 43 (q74 c4) ∷
   rw⁻ 42 (q75 c4) ∷
   rw⁻ 41 (q74 c4) ∷
   rw⁻ 40 (q75 c4) ∷
   rw⁻ 39 (q74 c4) ∷
   rw⁻ 38 (q74 c4) ∷
   rw⁻ 37 (q74 c4) ∷
   rw⁻ 36 (q74 c4) ∷
   rw⁻ 35 (q74 c4) ∷
   rw⁻ 34 (q74 c4) ∷
   rw⁻ 33 (q74 c4) ∷
   rw 48 (q73 c4) ∷
   rw⁻ 47 (q76 c4) ∷
   rw⁻ 46 (q74 c4) ∷
   rw⁻ 45 (q75 c4) ∷
   rw⁻ 44 (q74 c4) ∷
   rw⁻ 43 (q75 c4) ∷
   rw⁻ 42 (q74 c4) ∷
   rw⁻ 41 (q74 c4) ∷
   rw⁻ 40 (q74 c4) ∷
   rw⁻ 39 (q74 c4) ∷
   rw⁻ 38 (q74 c4) ∷
   rw⁻ 37 (q74 c4) ∷
   rw⁻ 36 (q74 c4) ∷
   rw 52 (q73 c4) ∷
   rw⁻ 51 (q76 c4) ∷
   rw⁻ 50 (q76 c4) ∷
   rw⁻ 49 (q74 c4) ∷
   rw⁻ 48 (q75 c4) ∷
   rw⁻ 47 (q74 c4) ∷
   rw⁻ 46 (q75 c4) ∷
   rw⁻ 45 (q74 c4) ∷
   rw⁻ 44 (q74 c4) ∷
   rw⁻ 43 (q74 c4) ∷
   rw⁻ 42 (q74 c4) ∷
   rw⁻ 41 (q74 c4) ∷
   rw⁻ 40 (q74 c4) ∷
   rw⁻ 39 (q74 c4) ∷
   rw⁻ 56 (q77 c4) ∷
   rw⁻ 55 (q78 c4) ∷
   rw⁻ 54 (q78 c4) ∷
   rw⁻ 53 (q78 c4) ∷
   rw⁻ 52 (q79 c4) ∷
   rw⁻ 51 (q80 c4) ∷
   rw⁻ 50 (q79 c4) ∷
   rw⁻ 49 (q80 c4) ∷
   rw⁻ 48 (q79 c4) ∷
   rw⁻ 47 (q79 c4) ∷
   rw⁻ 46 (q79 c4) ∷
   rw⁻ 45 (q79 c4) ∷
   rw⁻ 44 (q79 c4) ∷
   rw⁻ 43 (q79 c4) ∷
   rw⁻ 42 (q79 c4) ∷
   rw 60 (q73 c4) ∷
   rw⁻ 59 (q81 c4) ∷
   rw⁻ 58 (q76 c4) ∷
   rw⁻ 57 (q76 c4) ∷
   rw⁻ 56 (q76 c4) ∷
   rw⁻ 55 (q74 c4) ∷
   rw⁻ 54 (q75 c4) ∷
   rw⁻ 53 (q74 c4) ∷
   rw⁻ 52 (q75 c4) ∷
   rw⁻ 51 (q74 c4) ∷
   rw⁻ 50 (q74 c4) ∷
   rw⁻ 49 (q74 c4) ∷
   rw⁻ 48 (q74 c4) ∷
   rw⁻ 47 (q74 c4) ∷
   rw⁻ 46 (q74 c4) ∷
   rw⁻ 45 (q74 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-I c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4)

-- deb-P-hi-split-b: 66 steps
lem-deb-P-hi-split-b : Ws → ⟪ (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-deb-P-hi-split-b c4 = derive (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q67 c4) ∷
   rw 4 (q69 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   rw⁻ 8 (q67 c4) ∷
   rw⁻ 7 (q71 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   rw 12 (q69 c4) ∷
   rw⁻ 11 (q70 c4) ∷
   rw⁻ 10 (q72 c4) ∷
   rw⁻ 9 (q70 c4) ∷
   rw⁻ 16 (q67 c4) ∷
   rw⁻ 15 (q71 c4) ∷
   rw⁻ 14 (q68 c4) ∷
   rw⁻ 13 (q71 c4) ∷
   rw⁻ 12 (q68 c4) ∷
   rw 20 (q73 c4) ∷
   rw⁻ 19 (q74 c4) ∷
   rw⁻ 18 (q75 c4) ∷
   rw⁻ 17 (q74 c4) ∷
   rw⁻ 16 (q75 c4) ∷
   rw⁻ 15 (q74 c4) ∷
   rw 24 (q73 c4) ∷
   rw⁻ 23 (q76 c4) ∷
   rw⁻ 22 (q74 c4) ∷
   rw⁻ 21 (q75 c4) ∷
   rw⁻ 20 (q74 c4) ∷
   rw⁻ 19 (q75 c4) ∷
   rw⁻ 18 (q74 c4) ∷
   rw 28 (q73 c4) ∷
   rw⁻ 27 (q76 c4) ∷
   rw⁻ 26 (q76 c4) ∷
   rw⁻ 25 (q74 c4) ∷
   rw⁻ 24 (q75 c4) ∷
   rw⁻ 23 (q74 c4) ∷
   rw⁻ 22 (q75 c4) ∷
   rw⁻ 21 (q74 c4) ∷
   rw⁻ 32 (q77 c4) ∷
   rw⁻ 31 (q78 c4) ∷
   rw⁻ 30 (q78 c4) ∷
   rw⁻ 29 (q78 c4) ∷
   rw⁻ 28 (q79 c4) ∷
   rw⁻ 27 (q80 c4) ∷
   rw⁻ 26 (q79 c4) ∷
   rw⁻ 25 (q80 c4) ∷
   rw⁻ 24 (q79 c4) ∷
   rw⁻ 36 (q67 c4) ∷
   rw⁻ 35 (q82 c4) ∷
   rw⁻ 34 (q83 c4) ∷
   rw⁻ 33 (q83 c4) ∷
   rw⁻ 32 (q83 c4) ∷
   rw⁻ 31 (q68 c4) ∷
   rw⁻ 30 (q71 c4) ∷
   rw⁻ 29 (q68 c4) ∷
   rw⁻ 28 (q71 c4) ∷
   rw⁻ 27 (q68 c4) ∷
   rw⁻ 40 (q67 c4) ∷
   rw⁻ 39 (q68 c4) ∷
   rw⁻ 38 (q82 c4) ∷
   rw⁻ 37 (q83 c4) ∷
   rw⁻ 36 (q83 c4) ∷
   rw⁻ 35 (q83 c4) ∷
   rw⁻ 34 (q68 c4) ∷
   rw⁻ 33 (q71 c4) ∷
   rw⁻ 32 (q68 c4) ∷
   rw⁻ 31 (q71 c4) ∷
   rw⁻ 30 (q68 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ []) (lem-F5-23-at02132031 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (K0 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp 1263 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K2-at02132031 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-K2-at02132031 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (S1 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl 1412 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-K2-at02132031 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3-at02132031 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K2-at02132031 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-I-at02132031 c4)

-- deb-P-hi-split-a @02132031: 136 steps
lem-deb-P-hi-split-a-at02132031 : Ws → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-P-hi-split-a-at02132031 c4 = derive (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ [])
  (rw⁻ 0 (q84 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw⁻ 3 (q85 c4) ∷
   rw⁻ 8 (q84 c4) ∷
   rw⁻ 7 (q85 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw⁻ 12 (q84 c4) ∷
   rw⁻ 11 (q85 c4) ∷
   rw⁻ 10 (q85 c4) ∷
   rw⁻ 9 (q85 c4) ∷
   rw⁻ 16 (q84 c4) ∷
   rw⁻ 15 (q85 c4) ∷
   rw⁻ 14 (q85 c4) ∷
   rw⁻ 13 (q85 c4) ∷
   rw⁻ 12 (q85 c4) ∷
   rw⁻ 20 (q84 c4) ∷
   rw⁻ 19 (q85 c4) ∷
   rw⁻ 18 (q85 c4) ∷
   rw⁻ 17 (q85 c4) ∷
   rw⁻ 16 (q85 c4) ∷
   rw⁻ 15 (q85 c4) ∷
   rw⁻ 24 (q84 c4) ∷
   rw⁻ 23 (q85 c4) ∷
   rw⁻ 22 (q85 c4) ∷
   rw⁻ 21 (q85 c4) ∷
   rw⁻ 20 (q85 c4) ∷
   rw⁻ 19 (q85 c4) ∷
   rw⁻ 18 (q85 c4) ∷
   rw 28 (q86 c4) ∷
   rw⁻ 27 (q87 c4) ∷
   rw⁻ 26 (q87 c4) ∷
   rw⁻ 25 (q87 c4) ∷
   rw⁻ 24 (q87 c4) ∷
   rw⁻ 23 (q87 c4) ∷
   rw⁻ 22 (q87 c4) ∷
   rw⁻ 21 (q87 c4) ∷
   rw⁻ 32 (q84 c4) ∷
   rw⁻ 31 (q88 c4) ∷
   rw⁻ 30 (q85 c4) ∷
   rw⁻ 29 (q85 c4) ∷
   rw⁻ 28 (q85 c4) ∷
   rw⁻ 27 (q85 c4) ∷
   rw⁻ 26 (q85 c4) ∷
   rw⁻ 25 (q85 c4) ∷
   rw⁻ 24 (q85 c4) ∷
   rw 36 (q86 c4) ∷
   rw⁻ 35 (q87 c4) ∷
   rw⁻ 34 (q89 c4) ∷
   rw⁻ 33 (q87 c4) ∷
   rw⁻ 32 (q87 c4) ∷
   rw⁻ 31 (q87 c4) ∷
   rw⁻ 30 (q87 c4) ∷
   rw⁻ 29 (q87 c4) ∷
   rw⁻ 28 (q87 c4) ∷
   rw⁻ 27 (q87 c4) ∷
   rw⁻ 40 (q84 c4) ∷
   rw⁻ 39 (q88 c4) ∷
   rw⁻ 38 (q85 c4) ∷
   rw⁻ 37 (q88 c4) ∷
   rw⁻ 36 (q85 c4) ∷
   rw⁻ 35 (q85 c4) ∷
   rw⁻ 34 (q85 c4) ∷
   rw⁻ 33 (q85 c4) ∷
   rw⁻ 32 (q85 c4) ∷
   rw⁻ 31 (q85 c4) ∷
   rw⁻ 30 (q85 c4) ∷
   rw 44 (q90 c4) ∷
   rw⁻ 43 (q91 c4) ∷
   rw⁻ 42 (q92 c4) ∷
   rw⁻ 41 (q91 c4) ∷
   rw⁻ 40 (q92 c4) ∷
   rw⁻ 39 (q91 c4) ∷
   rw⁻ 38 (q91 c4) ∷
   rw⁻ 37 (q91 c4) ∷
   rw⁻ 36 (q91 c4) ∷
   rw⁻ 35 (q91 c4) ∷
   rw⁻ 34 (q91 c4) ∷
   rw⁻ 33 (q91 c4) ∷
   rw 48 (q90 c4) ∷
   rw⁻ 47 (q93 c4) ∷
   rw⁻ 46 (q91 c4) ∷
   rw⁻ 45 (q92 c4) ∷
   rw⁻ 44 (q91 c4) ∷
   rw⁻ 43 (q92 c4) ∷
   rw⁻ 42 (q91 c4) ∷
   rw⁻ 41 (q91 c4) ∷
   rw⁻ 40 (q91 c4) ∷
   rw⁻ 39 (q91 c4) ∷
   rw⁻ 38 (q91 c4) ∷
   rw⁻ 37 (q91 c4) ∷
   rw⁻ 36 (q91 c4) ∷
   rw 52 (q90 c4) ∷
   rw⁻ 51 (q93 c4) ∷
   rw⁻ 50 (q93 c4) ∷
   rw⁻ 49 (q91 c4) ∷
   rw⁻ 48 (q92 c4) ∷
   rw⁻ 47 (q91 c4) ∷
   rw⁻ 46 (q92 c4) ∷
   rw⁻ 45 (q91 c4) ∷
   rw⁻ 44 (q91 c4) ∷
   rw⁻ 43 (q91 c4) ∷
   rw⁻ 42 (q91 c4) ∷
   rw⁻ 41 (q91 c4) ∷
   rw⁻ 40 (q91 c4) ∷
   rw⁻ 39 (q91 c4) ∷
   rw⁻ 56 (q77 c4) ∷
   rw⁻ 55 (q94 c4) ∷
   rw⁻ 54 (q94 c4) ∷
   rw⁻ 53 (q94 c4) ∷
   rw⁻ 52 (q95 c4) ∷
   rw⁻ 51 (q96 c4) ∷
   rw⁻ 50 (q95 c4) ∷
   rw⁻ 49 (q96 c4) ∷
   rw⁻ 48 (q95 c4) ∷
   rw⁻ 47 (q95 c4) ∷
   rw⁻ 46 (q95 c4) ∷
   rw⁻ 45 (q95 c4) ∷
   rw⁻ 44 (q95 c4) ∷
   rw⁻ 43 (q95 c4) ∷
   rw⁻ 42 (q95 c4) ∷
   rw 60 (q90 c4) ∷
   rw⁻ 59 (q97 c4) ∷
   rw⁻ 58 (q93 c4) ∷
   rw⁻ 57 (q93 c4) ∷
   rw⁻ 56 (q93 c4) ∷
   rw⁻ 55 (q91 c4) ∷
   rw⁻ 54 (q92 c4) ∷
   rw⁻ 53 (q91 c4) ∷
   rw⁻ 52 (q92 c4) ∷
   rw⁻ 51 (q91 c4) ∷
   rw⁻ 50 (q91 c4) ∷
   rw⁻ 49 (q91 c4) ∷
   rw⁻ 48 (q91 c4) ∷
   rw⁻ 47 (q91 c4) ∷
   rw⁻ 46 (q91 c4) ∷
   rw⁻ 45 (q91 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at02132031 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4)

-- deb-P-hi-split-b @02132031: 66 steps
lem-deb-P-hi-split-b-at02132031 : Ws → ⟪ (CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-deb-P-hi-split-b-at02132031 c4 = derive (CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q84 c4) ∷
   rw 4 (q86 c4) ∷
   rw⁻ 3 (q87 c4) ∷
   rw⁻ 8 (q84 c4) ∷
   rw⁻ 7 (q88 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw 12 (q86 c4) ∷
   rw⁻ 11 (q87 c4) ∷
   rw⁻ 10 (q89 c4) ∷
   rw⁻ 9 (q87 c4) ∷
   rw⁻ 16 (q84 c4) ∷
   rw⁻ 15 (q88 c4) ∷
   rw⁻ 14 (q85 c4) ∷
   rw⁻ 13 (q88 c4) ∷
   rw⁻ 12 (q85 c4) ∷
   rw 20 (q90 c4) ∷
   rw⁻ 19 (q91 c4) ∷
   rw⁻ 18 (q92 c4) ∷
   rw⁻ 17 (q91 c4) ∷
   rw⁻ 16 (q92 c4) ∷
   rw⁻ 15 (q91 c4) ∷
   rw 24 (q90 c4) ∷
   rw⁻ 23 (q93 c4) ∷
   rw⁻ 22 (q91 c4) ∷
   rw⁻ 21 (q92 c4) ∷
   rw⁻ 20 (q91 c4) ∷
   rw⁻ 19 (q92 c4) ∷
   rw⁻ 18 (q91 c4) ∷
   rw 28 (q90 c4) ∷
   rw⁻ 27 (q93 c4) ∷
   rw⁻ 26 (q93 c4) ∷
   rw⁻ 25 (q91 c4) ∷
   rw⁻ 24 (q92 c4) ∷
   rw⁻ 23 (q91 c4) ∷
   rw⁻ 22 (q92 c4) ∷
   rw⁻ 21 (q91 c4) ∷
   rw⁻ 32 (q77 c4) ∷
   rw⁻ 31 (q94 c4) ∷
   rw⁻ 30 (q94 c4) ∷
   rw⁻ 29 (q94 c4) ∷
   rw⁻ 28 (q95 c4) ∷
   rw⁻ 27 (q96 c4) ∷
   rw⁻ 26 (q95 c4) ∷
   rw⁻ 25 (q96 c4) ∷
   rw⁻ 24 (q95 c4) ∷
   rw⁻ 36 (q84 c4) ∷
   rw⁻ 35 (q98 c4) ∷
   rw⁻ 34 (q99 c4) ∷
   rw⁻ 33 (q99 c4) ∷
   rw⁻ 32 (q99 c4) ∷
   rw⁻ 31 (q85 c4) ∷
   rw⁻ 30 (q88 c4) ∷
   rw⁻ 29 (q85 c4) ∷
   rw⁻ 28 (q88 c4) ∷
   rw⁻ 27 (q85 c4) ∷
   rw⁻ 40 (q84 c4) ∷
   rw⁻ 39 (q85 c4) ∷
   rw⁻ 38 (q98 c4) ∷
   rw⁻ 37 (q99 c4) ∷
   rw⁻ 36 (q99 c4) ∷
   rw⁻ 35 (q99 c4) ∷
   rw⁻ 34 (q85 c4) ∷
   rw⁻ 33 (q88 c4) ∷
   rw⁻ 32 (q85 c4) ∷
   rw⁻ 31 (q88 c4) ∷
   rw⁻ 30 (q85 c4) ∷ []) Eq.refl
