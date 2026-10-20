{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D067 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-inv-SBOX⟨2·0·41·3⟩ ; lem-invr-SBOX⟨2·0·41·3⟩)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-box-tQ ; lem-box-tQ-at0330)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-box-cP-at032032 ; lem-box-cP-at04203243)
open import Examples.Groups.Clifford+CS.FiveV.D.D016 using (lem-box-cP-at0210243143 ; lem-box-cP-at0314203142 ; lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box-perm-2314-at03102132)
open import Examples.Groups.Clifford+CS.FiveV.D.D018 using (lem-CSdu-box-3-at043043 ; lem-CSu-box-3-at043043 ; lem-box-perm-1324-at043043 ; lem-box-perm-3124 ; lem-box-perm-3124-at0330 ; lem-box2-at043043)
open import Examples.Groups.Clifford+CS.FiveV.D.D019 using (lem-CSdu-box-3-at0210243143 ; lem-CSdu-box-3-at0314213042 ; lem-CSdu-box-3-at122441 ; lem-CSu-box-3-at0210243143 ; lem-CSu-box-3-at0314213042 ; lem-CSu-box-3-at122441 ; lem-box-perm-1324-at0314213042 ; lem-box-perm-2314-at0210243143 ; lem-box-perm-3124-at0214213043 ; lem-box2-at0314213042)
open import Examples.Groups.Clifford+CS.FiveV.D.D020 using (lem-box-perm-1324-at0330 ; lem-box-perm-2314-at132132)
open import Examples.Groups.Clifford+CS.FiveV.D.D025 using (lem-F0-R ; lem-F0-R-at14213243 ; lem-F5-01 ; lem-box-perm-1342-at0210243143 ; lem-box-perm-1423-at021021 ; lem-box-perm-2431 ; lem-box-perm-4132-at122441)
open import Examples.Groups.Clifford+CS.FiveV.D.D026 using (lem-AX-S23)
open import Examples.Groups.Clifford+CS.FiveV.D.D037 using (lem-F0-B ; lem-F0-B-at14213243 ; lem-XCKX-box-2-at0210243143 ; lem-XCKX-box-2-at122441 ; lem-XCKX-box-2-at243243 ; lem-box-box-1-at03102132 ; lem-box-box-2)
open import Examples.Groups.Clifford+CS.FiveV.D.D038 using (lem-F4-CS0-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D039 using (lem-nf-X-CS0at0 ; lem-nf-X-CS0at1 ; lem-nf-X-CS0at2 ; lem-nf-X-CS1at0 ; lem-nf-X-CS1at1)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CS24-CCZ013 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd24-CCZ013 ; lem-comm-CX04-TOFF213 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CZ13-CCZ024 ; lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CX13 ; lem-comm-CCZ034-CS12 ; lem-comm-CX04-TOFF312 ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF213-CX04)
open import Examples.Groups.Clifford+CS.FiveV.D.R009 using (lem-comm-TOFF023-CX14)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx3-0124 ∷ []) (Bx3-1204 ∷ []) (lem-box-perm-2314-at03102132 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CX34 ∷ CX34 ∷ []) [] (wl 541 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CX34 ∷ Bx3-1204 ∷ CX34 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ []) (lem-F0-B c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CX34 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Bx4-1203 ∷ CX34 ∷ []) (lem-F0-R c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CS04⁻ ∷ Bx4-1203 ∷ []) (Bx4-1203 ∷ CS04⁻ ∷ []) (lem-CSdu-box-3-at043043 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx4-1203 ∷ []) (Bx4-1023 ∷ []) (lem-box-perm-1324-at043043 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx4-1023 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) (Toff412 ∷ CCZ014 ∷ []) (wp 376 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl 348 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ []) (wp 311 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CX01 ∷ Toff423 ∷ []) (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ))
  q12 : Ws → Eqn
  q12 c4 = eqn (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) (wl 460 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) (wl 461 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Toff412 ∷ Toff423 ∷ []) (Toff423 ∷ Toff412 ∷ []) (wl 516 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ014 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp 391 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS04 ∷ Bx4-1203 ∷ []) (Bx4-1203 ∷ CS04 ∷ []) (lem-CSu-box-3-at043043 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx4-1203 ∷ Bx4-1203 ∷ []) [] (lem-box2-at043043 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx3-1204 ∷ []) (Bx3-0124 ∷ []) (lem-box-perm-3124-at0330 c4)

-- CXuA-S: 44 steps
lem-CXuA-S : Ws → ⟪ (CX34 ∷ Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-12-4 ∷ CX34 ∷ []) ⟫ʷ
lem-CXuA-S c4 = derive (CX34 ∷ Sb3-0-12-4 ∷ []) (Sb3-0-12-4 ∷ CX34 ∷ [])
  (re 1 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) ∷
   re 3 1 (CS04 ∷ []) ∷
   re 5 1 (CS04⁻ ∷ []) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 9 (q11 c4) ∷
   rw 8 (q12 c4) ∷
   rw 7 (q11 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 7 (q14 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 3 (q16 c4) ∷
   rw 3 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q8 c4) ∷
   rw 4 (q9 c4) ∷
   rw 8 (q10 c4) ∷
   rw 7 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw 5 (q11 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   re 2 1 (Sb3-0-4-2 ∷ []) ∷
   re 4 1 (Sb⁻3-0-4-2 ∷ []) ∷
   re 0 5 (Sb3-0-12-4 ∷ []) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-XCKX-box-2-at243243 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ []) (wp 484 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS13 ∷ []) (wp 485 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS13⁻ ∷ []) (wp 486 c4)

-- F4-K0-CS1: 11 steps
lem-F4-K0-CS1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-CS1 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 0 (q19 c4) ∷
   rw⁻ 1 (q20 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw⁻ 4 (q22 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q23 : Ws → Eqn
  q23 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-XCKX-box-2-at122441 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff134 ∷ []) (wp 491 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS12 ∷ []) (wp 492 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS12⁻ ∷ []) (wp 493 c4)

-- F4-K0-CS2: 11 steps
lem-F4-K0-CS2 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-CS2 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 0 (q23 c4) ∷
   rw⁻ 1 (q24 c4) ∷
   rw⁻ 2 (q25 c4) ∷
   rw⁻ 3 (q24 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-XCKX-box-2-at0210243143 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff314 ∷ []) (wl 666 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS03 ∷ []) (wp 538 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS03⁻ ∷ []) (wp 539 c4)

-- F4-K2-CS0: 11 steps
lem-F4-K2-CS0 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS0 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx2-0413 ∷ []) (Bx2-4103 ∷ []) (lem-box-perm-2314-at0210243143 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CX23 ∷ CX23 ∷ []) [] (wl 806 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CX23 ∷ Bx2-4103 ∷ CX23 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ []) (lem-F0-B-at14213243 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CX23 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx3-4102 ∷ CX23 ∷ []) (lem-F0-R-at14213243 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CS03⁻ ∷ Bx3-4102 ∷ []) (Bx3-4102 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3-at0314213042 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx3-4102 ∷ []) (Bx3-4012 ∷ []) (lem-box-perm-1324-at0314213042 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx3-4012 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (Toff314 ∷ CCZ034 ∷ []) (wp 702 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp 41 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) (wl 501 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CX04 ∷ Toff312 ∷ []) (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CS14⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS14⁻ ∷ []) (wl 778 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) (wl 499 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (Toff312 ∷ Toff314 ∷ []) (Toff314 ∷ Toff312 ∷ []) (wl 779 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ034 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp 716 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CS03 ∷ Bx3-4102 ∷ []) (Bx3-4102 ∷ CS03 ∷ []) (lem-CSu-box-3-at0314213042 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx3-4102 ∷ Bx3-4102 ∷ []) [] (lem-box2-at0314213042 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (Bx2-4103 ∷ []) (Bx2-0413 ∷ []) (lem-box-perm-3124-at0214213043 c4)

-- CXuA-S @14213243: 44 steps
lem-CXuA-S-at14213243 : Ws → ⟪ (CX23 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CX23 ∷ []) ⟫ʷ
lem-CXuA-S-at14213243 c4 = derive (CX23 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CX23 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 1 (q31 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 0 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   rw 5 (q35 c4) ∷
   rw 5 (q36 c4) ∷
   rw 5 (q37 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   rw 6 (q39 c4) ∷
   rw 10 (q40 c4) ∷
   rw 9 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw 7 (q41 c4) ∷
   rw 6 (q43 c4) ∷
   rw⁻ 7 (q39 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   rw⁻ 6 (q45 c4) ∷
   rw⁻ 7 (q44 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 3 (q46 c4) ∷
   rw 3 (q36 c4) ∷
   rw 3 (q37 c4) ∷
   rw⁻ 2 (q38 c4) ∷
   rw 4 (q39 c4) ∷
   rw 8 (q40 c4) ∷
   rw 7 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw 5 (q41 c4) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw⁻ 2 (q36 c4) ∷
   rw 1 (q47 c4) ∷
   rw 0 (q48 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = eqn (Bx2-0413 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (X4 ∷ CCZ024 ∷ []) (wp 20 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CZ02 ∷ Toff213 ∷ []) (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl 183 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Toff213 ∷ X4 ∷ []) (X4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl 184 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp 21 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ024 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ []) (wp 22 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CS13⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CS13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ024 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ024 ∷ []) (wp 23 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) (wl 185 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ []) (wl 186 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CS12⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12⁻ ∷ []) (lem-CSdu-box-3-at0210243143 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) (wl 241 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) (wp 88 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp 34 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) (wp 35 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp 36 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) (wp 89 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (Toff134 ∷ Toff213 ∷ []) (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) (wl 1025 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (Toff234 ∷ CCZ024 ∷ []) (wp 768 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp 352 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) (wl 196 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (CX04 ∷ Toff213 ∷ []) (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (CS34⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS34⁻ ∷ []) (wl 807 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ []) (wl 808 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (Toff213 ∷ Toff234 ∷ []) (Toff234 ∷ Toff213 ∷ []) (wl 942 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (Toff134 ∷ Toff234 ∷ Toff234 ∷ []) (Toff134 ∷ []) (wl 979 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (CS12 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12 ∷ []) (lem-CSu-box-3-at0210243143 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (Bx0-2431 ∷ []) (Bx0-1234 ∷ []) (lem-box-perm-4132-at122441 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0134 ∷ []) (lem-box-perm-1342-at0210243143 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (Bx0-1234 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ Bx0-1234 ∷ []) (lem-box-box-2 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (Bx2-0134 ∷ []) (Bx2-0413 ∷ []) (lem-box-perm-1423-at021021 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (Bx0-1234 ∷ []) (Bx0-2431 ∷ []) (lem-box-perm-2431 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) (wl 906 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CZ13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (CZ13 ∷ CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ []) (wl 1026 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (CCZ013 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp 828 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ034 ∷ CS12 ∷ []) (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ []) (wl 645 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (CCZ013 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp 829 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ013 ∷ []) (wl 703 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) (wp 830 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl 230 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (CCZ034 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ034 ∷ []) (wp 831 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (CCZ034 ∷ CCZ034 ∷ []) [] (wp 7 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (CX13 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ []) (wl 745 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (CX13 ∷ Toff314 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX13 ∷ Toff314 ∷ []) (wl 1027 (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (CX10 ∷ CX13 ∷ Toff013 ∷ []) (Toff013 ∷ CX13 ∷ []) (wl 1028 (lit c4))
  q100 : Ws → Eqn
  q100 c4 = eqn (Toff013 ∷ Toff314 ∷ []) (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) (wp 832 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (CCZ024 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp 673 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp 833 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl 190 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) (wp 37 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) (wp 33 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (CX10 ∷ Toff013 ∷ []) (Toff013 ∷ CX10 ∷ []) (wl 1029 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl 256 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (Toff013 ∷ CS24 ∷ []) (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) (wl 872 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (Toff013 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (CS14 ∷ Toff013 ∷ []) (Toff013 ∷ CS14 ∷ []) (wp 785 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (Toff013 ∷ Toff014 ∷ []) (Toff014 ∷ Toff013 ∷ []) (wp 786 c4)
  q114 : Ws → Eqn
  q114 c4 = eqn (CCZ124 ∷ []) (CX10 ∷ CCZ124 ∷ CX10 ∷ []) (wp 663 c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (CCZ124 ∷ []) (Toff014 ∷ CCZ124 ∷ Toff014 ∷ []) (wp 787 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (CCZ124 ∷ CX13 ∷ CCZ124 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ []) (wl 1030 (lit c4))
  q117 : Ws → Eqn
  q117 c4 = eqn (Toff314 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ Toff314 ∷ []) (wl 187 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ []) (wp 657 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (CS03 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS03 ∷ []) (wl 986 (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (CS03 ∷ Toff134 ∷ []) (Toff134 ∷ CS03 ∷ []) (wp 277 c4)
  q121 : Ws → Eqn
  q121 c4 = eqn (CS03 ∷ CS12 ∷ []) (CS12 ∷ CS03 ∷ []) (wl 983 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (CS03 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS03 ∷ []) (lem-CSu-box-3-at122441 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ []) (wp 659 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (CS03⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS03⁻ ∷ []) (wl 469 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = eqn (CS03⁻ ∷ Toff134 ∷ []) (Toff134 ∷ CS03⁻ ∷ []) (wp 834 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (CS03⁻ ∷ CS12 ∷ []) (CS12 ∷ CS03⁻ ∷ []) (wl 981 (lit c4))
  q127 : Ws → Eqn
  q127 c4 = eqn (CS03⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3-at122441 c4)

-- F4-CS2-CS0: 284 steps
lem-F4-CS2-CS0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-CS0 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q49 c4) ∷
   rw⁻ 2 (q50 c4) ∷
   rw 4 (q51 c4) ∷
   rw⁻ 3 (q52 c4) ∷
   rw 6 (q53 c4) ∷
   rw⁻ 10 (q54 c4) ∷
   rw⁻ 9 (q55 c4) ∷
   rw 8 (q56 c4) ∷
   rw⁻ 7 (q55 c4) ∷
   rw 6 (q57 c4) ∷
   rw⁻ 7 (q53 c4) ∷
   rw⁻ 5 (q58 c4) ∷
   rw⁻ 4 (q50 c4) ∷
   rw 5 (q59 c4) ∷
   rw 6 (q60 c4) ∷
   rw⁻ 5 (q52 c4) ∷
   rw⁻ 2 (q49 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 5 (q61 c4) ∷
   rw 5 (q49 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw⁻ 10 (q63 c4) ∷
   rw⁻ 9 (q64 c4) ∷
   rw 8 (q65 c4) ∷
   rw⁻ 7 (q66 c4) ∷
   rw 6 (q65 c4) ∷
   rw⁻ 5 (q67 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 5 (q62 c4) ∷
   rw 5 (q69 c4) ∷
   rw⁻ 7 (q70 c4) ∷
   rw⁻ 6 (q62 c4) ∷
   rw⁻ 12 (q63 c4) ∷
   rw⁻ 11 (q64 c4) ∷
   rw 10 (q65 c4) ∷
   rw⁻ 9 (q66 c4) ∷
   rw 8 (q65 c4) ∷
   rw⁻ 7 (q67 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   rw 7 (q62 c4) ∷
   rw 9 (q71 c4) ∷
   rw 13 (q72 c4) ∷
   rw 12 (q73 c4) ∷
   rw 11 (q74 c4) ∷
   rw 10 (q73 c4) ∷
   rw 9 (q75 c4) ∷
   rw⁻ 10 (q71 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw 7 (q69 c4) ∷
   rw 8 (q77 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw 3 (q78 c4) ∷
   rw 3 (q49 c4) ∷
   rw⁻ 2 (q62 c4) ∷
   rw⁻ 8 (q63 c4) ∷
   rw⁻ 7 (q64 c4) ∷
   rw 6 (q65 c4) ∷
   rw⁻ 5 (q66 c4) ∷
   rw 4 (q65 c4) ∷
   rw⁻ 3 (q67 c4) ∷
   rw⁻ 2 (q68 c4) ∷
   rw 3 (q62 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 5 (q70 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw⁻ 10 (q63 c4) ∷
   rw⁻ 9 (q64 c4) ∷
   rw 8 (q65 c4) ∷
   rw⁻ 7 (q66 c4) ∷
   rw 6 (q65 c4) ∷
   rw⁻ 5 (q67 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 5 (q62 c4) ∷
   rw 7 (q71 c4) ∷
   rw 11 (q72 c4) ∷
   rw 10 (q73 c4) ∷
   rw 9 (q74 c4) ∷
   rw 8 (q73 c4) ∷
   rw 7 (q75 c4) ∷
   rw⁻ 8 (q71 c4) ∷
   rw⁻ 6 (q76 c4) ∷
   rw 5 (q69 c4) ∷
   rw 6 (q77 c4) ∷
   rw⁻ 2 (q49 c4) ∷
   rw 1 (q79 c4) ∷
   rw 2 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q49 c4) ∷
   rw⁻ 0 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw⁻ 1 (q52 c4) ∷
   rw 4 (q53 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw⁻ 7 (q55 c4) ∷
   rw 6 (q56 c4) ∷
   rw⁻ 5 (q55 c4) ∷
   rw 4 (q57 c4) ∷
   rw⁻ 5 (q53 c4) ∷
   rw⁻ 3 (q58 c4) ∷
   rw⁻ 2 (q50 c4) ∷
   rw 3 (q59 c4) ∷
   rw 4 (q60 c4) ∷
   rw⁻ 3 (q52 c4) ∷
   rw⁻ 0 (q49 c4) ∷
   rw 3 (q84 c4) ∷
   rw 2 (q53 c4) ∷
   rw⁻ 6 (q54 c4) ∷
   rw⁻ 5 (q55 c4) ∷
   rw 4 (q56 c4) ∷
   rw⁻ 3 (q55 c4) ∷
   rw 2 (q57 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw 3 (q85 c4) ∷
   rw 5 (q53 c4) ∷
   rw⁻ 9 (q54 c4) ∷
   rw⁻ 8 (q55 c4) ∷
   rw 7 (q56 c4) ∷
   rw⁻ 6 (q55 c4) ∷
   rw 5 (q57 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw 4 (q86 c4) ∷
   rw 5 (q87 c4) ∷
   rw⁻ 2 (q84 c4) ∷
   rw 3 (q88 c4) ∷
   rw 6 (q89 c4) ∷
   rw 5 (q90 c4) ∷
   rw 6 (q91 c4) ∷
   rw 8 (q92 c4) ∷
   rw 9 (q93 c4) ∷
   rw 10 (q94 c4) ∷
   rw 4 (q89 c4) ∷
   rw 5 (q95 c4) ∷
   rw 6 (q96 c4) ∷
   re 4 1 (Sb0-2-1-3 ∷ []) ∷
   re 6 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 2 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 3 (q97 c4) ∷
   re 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 4 1 (CS12 ∷ []) ∷
   re 6 1 (CS12⁻ ∷ []) ∷
   rw⁻ 3 (q98 c4) ∷
   rw 2 (q84 c4) ∷
   rw⁻ 5 (q99 c4) ∷
   rw 7 (q100 c4) ∷
   rw 4 (q101 c4) ∷
   rw 6 (q102 c4) ∷
   rw 7 (q103 c4) ∷
   rw⁻ 10 (q104 c4) ∷
   rw 9 (q105 c4) ∷
   rw 10 (q67 c4) ∷
   rw 11 (q102 c4) ∷
   rw 12 (q66 c4) ∷
   rw 13 (q102 c4) ∷
   rw 14 (q64 c4) ∷
   rw 15 (q106 c4) ∷
   rw 9 (q104 c4) ∷
   rw⁻ 3 (q107 c4) ∷
   rw 5 (q108 c4) ∷
   rw 4 (q109 c4) ∷
   rw⁻ 5 (q110 c4) ∷
   rw 6 (q111 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw⁻ 8 (q112 c4) ∷
   rw⁻ 4 (q108 c4) ∷
   rw⁻ 5 (q99 c4) ∷
   rw 7 (q113 c4) ∷
   rw 9 (q108 c4) ∷
   rw 8 (q109 c4) ∷
   rw⁻ 9 (q110 c4) ∷
   rw 10 (q111 c4) ∷
   rw⁻ 11 (q110 c4) ∷
   rw⁻ 12 (q112 c4) ∷
   rw⁻ 8 (q108 c4) ∷
   rw 9 (q100 c4) ∷
   rw⁻ 3 (q114 c4) ∷
   rw⁻ 5 (q115 c4) ∷
   rw 3 (q116 c4) ∷
   rw 2 (q102 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 3 (q105 c4) ∷
   rw 4 (q67 c4) ∷
   rw 5 (q102 c4) ∷
   rw 6 (q66 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q64 c4) ∷
   rw 9 (q106 c4) ∷
   rw 3 (q104 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   re 6 1 (Sb0-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 1 (q117 c4) ∷
   rw⁻ 4 (q118 c4) ∷
   re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 7 (q119 c4) ∷
   rw⁻ 6 (q120 c4) ∷
   rw⁻ 5 (q121 c4) ∷
   rw⁻ 4 (q120 c4) ∷
   rw⁻ 3 (q122 c4) ∷
   re 6 1 (Sb0-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 2 (q118 c4) ∷
   rw⁻ 5 (q97 c4) ∷
   re 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 6 1 (CS12 ∷ []) ∷
   re 8 1 (CS12⁻ ∷ []) ∷
   rw⁻ 5 (q98 c4) ∷
   rw 4 (q84 c4) ∷
   rw⁻ 7 (q99 c4) ∷
   rw 9 (q100 c4) ∷
   rw 6 (q101 c4) ∷
   rw 8 (q102 c4) ∷
   rw 9 (q103 c4) ∷
   rw⁻ 12 (q104 c4) ∷
   rw 11 (q105 c4) ∷
   rw 12 (q67 c4) ∷
   rw 13 (q102 c4) ∷
   rw 14 (q66 c4) ∷
   rw 15 (q102 c4) ∷
   rw 16 (q64 c4) ∷
   rw 17 (q106 c4) ∷
   rw 11 (q104 c4) ∷
   rw⁻ 5 (q107 c4) ∷
   rw 7 (q108 c4) ∷
   rw 6 (q109 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw 8 (q111 c4) ∷
   rw⁻ 9 (q110 c4) ∷
   rw⁻ 10 (q112 c4) ∷
   rw⁻ 6 (q108 c4) ∷
   rw⁻ 7 (q99 c4) ∷
   rw 9 (q113 c4) ∷
   rw 11 (q108 c4) ∷
   rw 10 (q109 c4) ∷
   rw⁻ 11 (q110 c4) ∷
   rw 12 (q111 c4) ∷
   rw⁻ 13 (q110 c4) ∷
   rw⁻ 14 (q112 c4) ∷
   rw⁻ 10 (q108 c4) ∷
   rw 11 (q100 c4) ∷
   rw⁻ 5 (q114 c4) ∷
   rw⁻ 7 (q115 c4) ∷
   rw 5 (q116 c4) ∷
   rw 4 (q102 c4) ∷
   rw⁻ 6 (q104 c4) ∷
   rw 5 (q105 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q106 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   re 8 1 (Sb0-2-1-3 ∷ []) ∷
   re 10 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 6 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 3 (q117 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   re 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 7 1 (CS12 ∷ []) ∷
   re 9 1 (CS12⁻ ∷ []) ∷
   rw⁻ 9 (q124 c4) ∷
   rw⁻ 8 (q125 c4) ∷
   rw⁻ 7 (q126 c4) ∷
   rw⁻ 6 (q125 c4) ∷
   rw⁻ 5 (q127 c4) ∷
   re 8 1 (Sb0-2-1-3 ∷ []) ∷
   re 10 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 6 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 4 (q123 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl 1083 (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ []) [] (lem-invr-SBOX⟨2·0·41·3⟩ c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ []) (lem-F5-01 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (CS01 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS01 ∷ []) (lem-AX-S23 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) [] (lem-inv-SBOX⟨2·0·41·3⟩ c4)
  q133 : Ws → Eqn
  q133 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS0-CS2 c4)

-- F2-CS0-CS2: 16 steps
lem-F2-CS0-CS2 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F2-CS0-CS2 c4 = derive (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q128 c4) ∷
   rw⁻ 1 (q129 c4) ∷
   rw⁻ 2 (q128 c4) ∷
   rw 3 (q130 c4) ∷
   rw 3 (q131 c4) ∷
   rw⁻ 4 (q128 c4) ∷
   rw⁻ 5 (q132 c4) ∷
   rw⁻ 6 (q128 c4) ∷
   rw⁻ 3 (q133 c4) ∷
   rw 2 (q128 c4) ∷
   rw 1 (q129 c4) ∷
   rw 0 (q128 c4) ∷
   rw⁻ 4 (q130 c4) ∷
   rw 3 (q128 c4) ∷
   rw 2 (q129 c4) ∷
   rw 1 (q128 c4) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = eqn (Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4)
  q135 : Ws → Eqn
  q135 c4 = eqn (Toff012 ∷ Toff312 ∷ Toff301 ∷ []) (Toff301 ∷ Toff012 ∷ []) (wl 1084 (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ034 ∷ CCZ014 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ034 ∷ []) (wp 883 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (CCZ034 ∷ CCZ014 ∷ []) (Toff301 ∷ CCZ034 ∷ Toff301 ∷ []) (wp 884 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (CCZ014 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp 122 c4)
  q139 : Ws → Eqn
  q139 c4 = eqn (CCZ124 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ []) (wl 871 (lit c4))
  q140 : Ws → Eqn
  q140 c4 = eqn (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) (wp 66 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ []) (CCZ034 ∷ []) (wp 885 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (CCZ034 ∷ CS14 ∷ []) (CS14 ∷ CCZ034 ∷ []) (wp 106 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ034 ∷ []) (wp 107 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ []) (wp 108 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (Toff012 ∷ Toff312 ∷ []) (Toff312 ∷ Toff012 ∷ []) (wl 1085 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (Bx3-1204 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0330 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (Bx3-1204 ∷ []) (Bx3-1024 ∷ []) (lem-box-perm-1324-at0330 c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (Bx3-1024 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4)
  q150 : Ws → Eqn
  q150 c4 = eqn (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (Toff012 ∷ CCZ013 ∷ []) (wl 325 (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (CCZ123 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl 445 (lit c4))
  q152 : Ws → Eqn
  q152 c4 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wl 446 (lit c4))
  q153 : Ws → Eqn
  q153 c4 = eqn (K0⁻ ∷ Toff324 ∷ []) (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑))
  q154 : Ws → Eqn
  q154 c4 = eqn (CS02 ∷ Toff324 ∷ []) (Toff324 ∷ CS02 ∷ []) (wp 298 c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (CX01 ∷ Toff324 ∷ []) (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))
  q156 : Ws → Eqn
  q156 c4 = eqn (CS12⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS12⁻ ∷ []) (wl 447 (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (CS12 ∷ Toff324 ∷ []) (Toff324 ∷ CS12 ∷ []) (wl 214 (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (K0 ∷ Toff324 ∷ []) (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑))
  q159 : Ws → Eqn
  q159 c4 = eqn (CCZ013 ∷ CS14 ∷ []) (CS14 ∷ CCZ013 ∷ []) (wp 299 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (CCZ013 ∷ CX12 ∷ []) (CX12 ∷ CCZ013 ∷ []) (wl 448 (lit c4))
  q161 : Ws → Eqn
  q161 c4 = eqn (CS24⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (CS24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ []) (wl 327 (lit c4))
  q164 : Ws → Eqn
  q164 c4 = eqn (Toff012 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff012 ∷ []) (wl 449 (lit c4))
  q165 : Ws → Eqn
  q165 c4 = eqn (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) (wl 450 (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (CCZ124 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ124 ∷ []) (wp 300 c4)
  q167 : Ws → Eqn
  q167 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl 263 (lit c4))
  q168 : Ws → Eqn
  q168 c4 = eqn (Bx0-1234 ∷ []) (Bx0-3124 ∷ []) (lem-box-perm-3124 c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (Bx3-0124 ∷ Bx0-3124 ∷ []) (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-box-box-1-at03102132 c4)
  q170 : Ws → Eqn
  q170 c4 = eqn (Bx0-3124 ∷ []) (Bx0-1234 ∷ []) (lem-box-perm-2314-at132132 c4)

-- Tu-box: 83 steps
lem-Tu-box : Ws → ⟪ (Toff301 ∷ Bx0-1234 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Bx3-1204 ∷ []) ⟫ʷ
lem-Tu-box c4 = derive (Toff301 ∷ Bx0-1234 ∷ Toff301 ∷ []) (Bx0-1234 ∷ Bx3-1204 ∷ [])
  (rw 1 (q134 c4) ∷
   rw⁻ 0 (q135 c4) ∷
   rw⁻ 2 (q136 c4) ∷
   rw⁻ 4 (q135 c4) ∷
   rw⁻ 6 (q137 c4) ∷
   rw 3 (q138 c4) ∷
   rw 5 (q139 c4) ∷
   rw 4 (q39 c4) ∷
   rw 8 (q40 c4) ∷
   rw 7 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw 5 (q41 c4) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw 5 (q140 c4) ∷
   rw 6 (q141 c4) ∷
   rw 5 (q108 c4) ∷
   rw⁻ 9 (q142 c4) ∷
   rw 8 (q143 c4) ∷
   rw⁻ 7 (q144 c4) ∷
   rw 6 (q143 c4) ∷
   rw⁻ 5 (q145 c4) ∷
   rw⁻ 6 (q108 c4) ∷
   rw 3 (q146 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw⁻ 1 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw 1 (q149 c4) ∷
   rw⁻ 0 (q150 c4) ∷
   rw 2 (q151 c4) ∷
   rw⁻ 1 (q152 c4) ∷
   rw 7 (q153 c4) ∷
   rw 6 (q154 c4) ∷
   rw 5 (q155 c4) ∷
   rw 4 (q156 c4) ∷
   rw 3 (q155 c4) ∷
   rw 2 (q157 c4) ∷
   rw 1 (q158 c4) ∷
   rw 2 (q152 c4) ∷
   rw 4 (q108 c4) ∷
   rw⁻ 8 (q159 c4) ∷
   rw⁻ 7 (q160 c4) ∷
   rw 6 (q161 c4) ∷
   rw⁻ 5 (q160 c4) ∷
   rw 4 (q162 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw⁻ 3 (q163 c4) ∷
   rw⁻ 2 (q150 c4) ∷
   rw 3 (q164 c4) ∷
   rw 4 (q165 c4) ∷
   rw⁻ 3 (q152 c4) ∷
   rw 9 (q153 c4) ∷
   rw 8 (q154 c4) ∷
   rw 7 (q155 c4) ∷
   rw 6 (q156 c4) ∷
   rw 5 (q155 c4) ∷
   rw 4 (q157 c4) ∷
   rw 3 (q158 c4) ∷
   rw 4 (q152 c4) ∷
   rw⁻ 0 (q149 c4) ∷
   rw⁻ 0 (q148 c4) ∷
   rw 2 (q108 c4) ∷
   rw⁻ 6 (q142 c4) ∷
   rw 5 (q143 c4) ∷
   rw⁻ 4 (q144 c4) ∷
   rw 3 (q143 c4) ∷
   rw⁻ 2 (q145 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw 3 (q166 c4) ∷
   rw 4 (q108 c4) ∷
   rw⁻ 8 (q142 c4) ∷
   rw 7 (q143 c4) ∷
   rw⁻ 6 (q144 c4) ∷
   rw 5 (q143 c4) ∷
   rw⁻ 4 (q145 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw 5 (q167 c4) ∷
   rw⁻ 1 (q134 c4) ∷
   rw 0 (q18 c4) ∷
   rw 1 (q168 c4) ∷
   rw 0 (q169 c4) ∷
   rw 0 (q170 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q171 : Ws → Eqn
  q171 c4 = eqn (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CX40 ∷ []) (wp 931 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (Toff213 ∷ Toff314 ∷ []) (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl 747 (lit c4))
  q173 : Ws → Eqn
  q173 c4 = eqn (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp 654 c4)
  q174 : Ws → Eqn
  q174 c4 = eqn (Toff213 ∷ Toff214 ∷ []) (Toff214 ∷ Toff213 ∷ []) (wl 197 (lit c4))
  q175 : Ws → Eqn
  q175 c4 = eqn (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) (wl 195 (lit c4))
  q176 : Ws → Eqn
  q176 c4 = eqn (Toff213 ∷ CX04 ∷ []) (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4))
  q177 : Ws → Eqn
  q177 c4 = eqn (CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS14⁻ ∷ []) (wl 194 (lit c4))
  q178 : Ws → Eqn
  q178 c4 = eqn (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) (wl 193 (lit c4))
  q179 : Ws → Eqn
  q179 c4 = eqn (CCZ014 ∷ []) (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) (wp 44 c4)
  q180 : Ws → Eqn
  q180 c4 = eqn (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) (wp 38 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ []) (wl 191 (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp 32 c4)
  q183 : Ws → Eqn
  q183 c4 = eqn (CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp 651 c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)
  q185 : Ws → Eqn
  q185 c4 = eqn (CX40 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ CCZ013 ∷ S4 ∷ CS14 ∷ []) (wp 932 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ CCZ013 ∷ S4 ∷ CS14 ∷ Bx2-0413 ∷ []) (lem-nf-X-CS0at0 c4)

-- F1-X-CS0@0: 86 steps
lem-F1-X-CS0at0 : Ws → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-F1-X-CS0at0 c4 = derive (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  (re 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 7 1 (CS03 ∷ []) ∷
   re 9 1 (CS03⁻ ∷ []) ∷
   rw 0 (q171 c4) ∷
   rw 1 (q49 c4) ∷
   rw 4 (q172 c4) ∷
   rw 3 (q173 c4) ∷
   rw⁻ 6 (q104 c4) ∷
   rw 5 (q105 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q106 c4) ∷
   rw 5 (q104 c4) ∷
   rw 2 (q174 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 3 (q175 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 5 (q177 c4) ∷
   rw 6 (q176 c4) ∷
   rw⁻ 7 (q178 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   rw 4 (q172 c4) ∷
   rw⁻ 2 (q179 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw⁻ 3 (q104 c4) ∷
   rw 2 (q105 c4) ∷
   rw 3 (q67 c4) ∷
   rw 4 (q102 c4) ∷
   rw 5 (q66 c4) ∷
   rw 6 (q102 c4) ∷
   rw 7 (q64 c4) ∷
   rw 8 (q106 c4) ∷
   rw 2 (q104 c4) ∷
   rw⁻ 3 (q49 c4) ∷
   rw 3 (q49 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw 5 (q54 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   rw 4 (q49 c4) ∷
   rw 7 (q172 c4) ∷
   rw 6 (q173 c4) ∷
   rw⁻ 9 (q104 c4) ∷
   rw 8 (q105 c4) ∷
   rw 9 (q67 c4) ∷
   rw 10 (q102 c4) ∷
   rw 11 (q66 c4) ∷
   rw 12 (q102 c4) ∷
   rw 13 (q64 c4) ∷
   rw 14 (q106 c4) ∷
   rw 8 (q104 c4) ∷
   rw 5 (q174 c4) ∷
   rw 7 (q39 c4) ∷
   rw⁻ 6 (q175 c4) ∷
   rw 7 (q176 c4) ∷
   rw⁻ 8 (q177 c4) ∷
   rw 9 (q176 c4) ∷
   rw⁻ 10 (q178 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 7 (q172 c4) ∷
   rw⁻ 5 (q179 c4) ∷
   rw⁻ 4 (q180 c4) ∷
   rw⁻ 6 (q104 c4) ∷
   rw 5 (q105 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q106 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 6 (q49 c4) ∷
   rw 6 (q49 c4) ∷
   rw⁻ 9 (q181 c4) ∷
   rw 8 (q182 c4) ∷
   rw⁻ 7 (q181 c4) ∷
   rw 6 (q182 c4) ∷
   rw⁻ 7 (q49 c4) ∷
   rw 1 (q183 c4) ∷
   rw 3 (q184 c4) ∷
   rw 0 (q185 c4) ∷
   rw⁻ 0 (q186 c4) ∷ []) Eq.refl

private
  q187 : Ws → Eqn
  q187 c4 = eqn (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ []) (CX41 ∷ []) (wl 1142 (lit c4))
  q188 : Ws → Eqn
  q188 c4 = eqn (Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4)
  q189 : Ws → Eqn
  q189 c4 = eqn (Toff023 ∷ Toff324 ∷ []) (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp 805 c4)
  q190 : Ws → Eqn
  q190 c4 = eqn (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp 806 c4)
  q191 : Ws → Eqn
  q191 c4 = eqn (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) (wl 217 (lit c4))
  q192 : Ws → Eqn
  q192 c4 = eqn (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ []) (wp 65 c4)
  q193 : Ws → Eqn
  q193 c4 = eqn (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) (wp 64 c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4))
  q195 : Ws → Eqn
  q195 c4 = eqn (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) (wp 63 c4)
  q196 : Ws → Eqn
  q196 c4 = eqn (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) (wp 62 c4)
  q197 : Ws → Eqn
  q197 c4 = eqn (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ []) (wp 61 c4)
  q198 : Ws → Eqn
  q198 c4 = eqn (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ []) (wp 72 c4)
  q199 : Ws → Eqn
  q199 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl 220 (lit c4))
  q200 : Ws → Eqn
  q200 c4 = eqn (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) (wp 70 c4)
  q201 : Ws → Eqn
  q201 c4 = eqn (Toff023 ∷ CX14 ∷ []) (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4))
  q202 : Ws → Eqn
  q202 c4 = eqn (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ []) (wp 69 c4)
  q203 : Ws → Eqn
  q203 c4 = eqn (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) (wl 221 (lit c4))
  q204 : Ws → Eqn
  q204 c4 = eqn (CCZ124 ∷ []) (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) (wp 74 c4)
  q205 : Ws → Eqn
  q205 c4 = eqn (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) (wl 222 (lit c4))
  q206 : Ws → Eqn
  q206 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp 53 c4)
  q207 : Ws → Eqn
  q207 c4 = eqn (CS13⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS13⁻ ∷ []) (wl 219 (lit c4))
  q208 : Ws → Eqn
  q208 c4 = eqn (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) (wp 60 c4)
  q209 : Ws → Eqn
  q209 c4 = eqn (CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl 1000 (lit c4))
  q210 : Ws → Eqn
  q210 c4 = eqn (CX41 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ []) (wl 1143 (lit c4))
  q211 : Ws → Eqn
  q211 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ Bx0-1423 ∷ []) (lem-nf-X-CS0at1 c4)

-- F1-X-CS0@1: 86 steps
lem-F1-X-CS0at1 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-F1-X-CS0at1 c4 = derive (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  (re 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 7 1 (CS13 ∷ []) ∷
   re 9 1 (CS13⁻ ∷ []) ∷
   rw 0 (q187 c4) ∷
   rw 1 (q188 c4) ∷
   rw 4 (q189 c4) ∷
   rw 3 (q190 c4) ∷
   rw⁻ 6 (q191 c4) ∷
   rw 5 (q192 c4) ∷
   rw 6 (q193 c4) ∷
   rw 7 (q194 c4) ∷
   rw 8 (q195 c4) ∷
   rw 9 (q194 c4) ∷
   rw 10 (q196 c4) ∷
   rw 11 (q197 c4) ∷
   rw 5 (q191 c4) ∷
   rw 2 (q198 c4) ∷
   rw 4 (q199 c4) ∷
   rw⁻ 3 (q200 c4) ∷
   rw 4 (q201 c4) ∷
   rw⁻ 5 (q202 c4) ∷
   rw 6 (q201 c4) ∷
   rw⁻ 7 (q203 c4) ∷
   rw⁻ 3 (q199 c4) ∷
   rw 4 (q189 c4) ∷
   rw⁻ 2 (q204 c4) ∷
   rw 1 (q140 c4) ∷
   rw⁻ 3 (q191 c4) ∷
   rw 2 (q192 c4) ∷
   rw 3 (q193 c4) ∷
   rw 4 (q194 c4) ∷
   rw 5 (q195 c4) ∷
   rw 6 (q194 c4) ∷
   rw 7 (q196 c4) ∷
   rw 8 (q197 c4) ∷
   rw 2 (q191 c4) ∷
   rw⁻ 3 (q188 c4) ∷
   rw 3 (q188 c4) ∷
   rw⁻ 6 (q205 c4) ∷
   rw 5 (q206 c4) ∷
   rw⁻ 4 (q205 c4) ∷
   rw 3 (q206 c4) ∷
   rw⁻ 4 (q188 c4) ∷
   rw 4 (q188 c4) ∷
   rw 7 (q189 c4) ∷
   rw 6 (q190 c4) ∷
   rw⁻ 9 (q191 c4) ∷
   rw 8 (q192 c4) ∷
   rw 9 (q193 c4) ∷
   rw 10 (q194 c4) ∷
   rw 11 (q195 c4) ∷
   rw 12 (q194 c4) ∷
   rw 13 (q196 c4) ∷
   rw 14 (q197 c4) ∷
   rw 8 (q191 c4) ∷
   rw 5 (q198 c4) ∷
   rw 7 (q199 c4) ∷
   rw⁻ 6 (q200 c4) ∷
   rw 7 (q201 c4) ∷
   rw⁻ 8 (q202 c4) ∷
   rw 9 (q201 c4) ∷
   rw⁻ 10 (q203 c4) ∷
   rw⁻ 6 (q199 c4) ∷
   rw 7 (q189 c4) ∷
   rw⁻ 5 (q204 c4) ∷
   rw 4 (q140 c4) ∷
   rw⁻ 6 (q191 c4) ∷
   rw 5 (q192 c4) ∷
   rw 6 (q193 c4) ∷
   rw 7 (q194 c4) ∷
   rw 8 (q195 c4) ∷
   rw 9 (q194 c4) ∷
   rw 10 (q196 c4) ∷
   rw 11 (q197 c4) ∷
   rw 5 (q191 c4) ∷
   rw⁻ 6 (q188 c4) ∷
   rw 6 (q188 c4) ∷
   rw⁻ 9 (q207 c4) ∷
   rw 8 (q208 c4) ∷
   rw⁻ 7 (q207 c4) ∷
   rw 6 (q208 c4) ∷
   rw⁻ 7 (q188 c4) ∷
   rw 1 (q209 c4) ∷
   rw 3 (q167 c4) ∷
   rw 0 (q210 c4) ∷
   rw⁻ 0 (q211 c4) ∷ []) Eq.refl

private
  q212 : Ws → Eqn
  q212 c4 = eqn (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ []) (CX42 ∷ []) (wl 1147 (lit c4))
  q213 : Ws → Eqn
  q213 c4 = eqn (Toff013 ∷ Toff134 ∷ []) (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp 843 c4)
  q214 : Ws → Eqn
  q214 c4 = eqn (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp 845 c4)
  q215 : Ws → Eqn
  q215 c4 = eqn (Toff013 ∷ Toff034 ∷ []) (Toff034 ∷ Toff013 ∷ []) (wp 97 c4)
  q216 : Ws → Eqn
  q216 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl 245 (lit c4))
  q217 : Ws → Eqn
  q217 c4 = eqn (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) (wp 95 c4)
  q218 : Ws → Eqn
  q218 c4 = eqn (Toff013 ∷ CX24 ∷ []) (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4))
  q219 : Ws → Eqn
  q219 c4 = eqn (CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS34⁻ ∷ []) (wp 94 c4)
  q220 : Ws → Eqn
  q220 c4 = eqn (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) (wl 246 (lit c4))
  q221 : Ws → Eqn
  q221 c4 = eqn (CCZ234 ∷ []) (Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) (wp 842 c4)
  q222 : Ws → Eqn
  q222 c4 = eqn (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) (wp 90 c4)
  q223 : Ws → Eqn
  q223 c4 = eqn (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) (wl 247 (lit c4))
  q224 : Ws → Eqn
  q224 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp 81 c4)
  q225 : Ws → Eqn
  q225 c4 = eqn (CS12⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS12⁻ ∷ []) (wl 244 (lit c4))
  q226 : Ws → Eqn
  q226 c4 = eqn (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) (wp 87 c4)
  q227 : Ws → Eqn
  q227 c4 = eqn (CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl 1037 (lit c4))
  q228 : Ws → Eqn
  q228 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl 305 (lit c4))
  q229 : Ws → Eqn
  q229 c4 = eqn (CX42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS34 ∷ []) (wl 1148 (lit c4))
  q230 : Ws → Eqn
  q230 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS34 ∷ Bx0-2431 ∷ []) (lem-nf-X-CS0at2 c4)

-- F1-X-CS0@2: 86 steps
lem-F1-X-CS0at2 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-F1-X-CS0at2 c4 = derive (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  (re 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 7 1 (CS12 ∷ []) ∷
   re 9 1 (CS12⁻ ∷ []) ∷
   rw 0 (q212 c4) ∷
   rw 1 (q84 c4) ∷
   rw 4 (q213 c4) ∷
   rw 3 (q214 c4) ∷
   rw⁻ 6 (q62 c4) ∷
   rw 5 (q68 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q63 c4) ∷
   rw 5 (q62 c4) ∷
   rw 2 (q215 c4) ∷
   rw 4 (q216 c4) ∷
   rw⁻ 3 (q217 c4) ∷
   rw 4 (q218 c4) ∷
   rw⁻ 5 (q219 c4) ∷
   rw 6 (q218 c4) ∷
   rw⁻ 7 (q220 c4) ∷
   rw⁻ 3 (q216 c4) ∷
   rw 4 (q213 c4) ∷
   rw⁻ 2 (q221 c4) ∷
   rw 1 (q222 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw 2 (q68 c4) ∷
   rw 3 (q67 c4) ∷
   rw 4 (q102 c4) ∷
   rw 5 (q66 c4) ∷
   rw 6 (q102 c4) ∷
   rw 7 (q64 c4) ∷
   rw 8 (q63 c4) ∷
   rw 2 (q62 c4) ∷
   rw⁻ 3 (q84 c4) ∷
   rw 3 (q84 c4) ∷
   rw⁻ 6 (q223 c4) ∷
   rw 5 (q224 c4) ∷
   rw⁻ 4 (q223 c4) ∷
   rw 3 (q224 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw 4 (q84 c4) ∷
   rw 7 (q213 c4) ∷
   rw 6 (q214 c4) ∷
   rw⁻ 9 (q62 c4) ∷
   rw 8 (q68 c4) ∷
   rw 9 (q67 c4) ∷
   rw 10 (q102 c4) ∷
   rw 11 (q66 c4) ∷
   rw 12 (q102 c4) ∷
   rw 13 (q64 c4) ∷
   rw 14 (q63 c4) ∷
   rw 8 (q62 c4) ∷
   rw 5 (q215 c4) ∷
   rw 7 (q216 c4) ∷
   rw⁻ 6 (q217 c4) ∷
   rw 7 (q218 c4) ∷
   rw⁻ 8 (q219 c4) ∷
   rw 9 (q218 c4) ∷
   rw⁻ 10 (q220 c4) ∷
   rw⁻ 6 (q216 c4) ∷
   rw 7 (q213 c4) ∷
   rw⁻ 5 (q221 c4) ∷
   rw 4 (q222 c4) ∷
   rw⁻ 6 (q62 c4) ∷
   rw 5 (q68 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q63 c4) ∷
   rw 5 (q62 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 6 (q84 c4) ∷
   rw⁻ 9 (q225 c4) ∷
   rw 8 (q226 c4) ∷
   rw⁻ 7 (q225 c4) ∷
   rw 6 (q226 c4) ∷
   rw⁻ 7 (q84 c4) ∷
   rw 1 (q227 c4) ∷
   rw 3 (q228 c4) ∷
   rw 0 (q229 c4) ∷
   rw⁻ 0 (q230 c4) ∷ []) Eq.refl

private
  q231 : Ws → Eqn
  q231 c4 = eqn (CX41 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ013 ∷ S4 ∷ CS04 ∷ []) (wp 954 c4)
  q232 : Ws → Eqn
  q232 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ013 ∷ S4 ∷ CS04 ∷ Bx2-0413 ∷ []) (lem-nf-X-CS1at0 c4)

-- F1-X-CS1@0: 86 steps
lem-F1-X-CS1at0 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-F1-X-CS1at0 c4 = derive (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  (re 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 7 1 (CS03 ∷ []) ∷
   re 9 1 (CS03⁻ ∷ []) ∷
   rw 0 (q187 c4) ∷
   rw 1 (q49 c4) ∷
   rw 4 (q172 c4) ∷
   rw 3 (q173 c4) ∷
   rw⁻ 6 (q104 c4) ∷
   rw 5 (q105 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q106 c4) ∷
   rw 5 (q104 c4) ∷
   rw 2 (q174 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 3 (q175 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 5 (q177 c4) ∷
   rw 6 (q176 c4) ∷
   rw⁻ 7 (q178 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   rw 4 (q172 c4) ∷
   rw⁻ 2 (q179 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw⁻ 3 (q104 c4) ∷
   rw 2 (q105 c4) ∷
   rw 3 (q67 c4) ∷
   rw 4 (q102 c4) ∷
   rw 5 (q66 c4) ∷
   rw 6 (q102 c4) ∷
   rw 7 (q64 c4) ∷
   rw 8 (q106 c4) ∷
   rw 2 (q104 c4) ∷
   rw⁻ 3 (q49 c4) ∷
   rw 3 (q49 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw 5 (q54 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   rw 4 (q49 c4) ∷
   rw 7 (q172 c4) ∷
   rw 6 (q173 c4) ∷
   rw⁻ 9 (q104 c4) ∷
   rw 8 (q105 c4) ∷
   rw 9 (q67 c4) ∷
   rw 10 (q102 c4) ∷
   rw 11 (q66 c4) ∷
   rw 12 (q102 c4) ∷
   rw 13 (q64 c4) ∷
   rw 14 (q106 c4) ∷
   rw 8 (q104 c4) ∷
   rw 5 (q174 c4) ∷
   rw 7 (q39 c4) ∷
   rw⁻ 6 (q175 c4) ∷
   rw 7 (q176 c4) ∷
   rw⁻ 8 (q177 c4) ∷
   rw 9 (q176 c4) ∷
   rw⁻ 10 (q178 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 7 (q172 c4) ∷
   rw⁻ 5 (q179 c4) ∷
   rw⁻ 4 (q180 c4) ∷
   rw⁻ 6 (q104 c4) ∷
   rw 5 (q105 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q106 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 6 (q49 c4) ∷
   rw 6 (q49 c4) ∷
   rw⁻ 9 (q181 c4) ∷
   rw 8 (q182 c4) ∷
   rw⁻ 7 (q181 c4) ∷
   rw 6 (q182 c4) ∷
   rw⁻ 7 (q49 c4) ∷
   rw 1 (q183 c4) ∷
   rw 3 (q184 c4) ∷
   rw 0 (q231 c4) ∷
   rw⁻ 0 (q232 c4) ∷ []) Eq.refl

private
  q233 : Ws → Eqn
  q233 c4 = eqn (CX42 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS14 ∷ []) (wl 1169 (lit c4))
  q234 : Ws → Eqn
  q234 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS14 ∷ Bx0-1423 ∷ []) (lem-nf-X-CS1at1 c4)

-- F1-X-CS1@1: 86 steps
lem-F1-X-CS1at1 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-F1-X-CS1at1 c4 = derive (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  (re 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 7 1 (CS13 ∷ []) ∷
   re 9 1 (CS13⁻ ∷ []) ∷
   rw 0 (q212 c4) ∷
   rw 1 (q188 c4) ∷
   rw 4 (q189 c4) ∷
   rw 3 (q190 c4) ∷
   rw⁻ 6 (q191 c4) ∷
   rw 5 (q192 c4) ∷
   rw 6 (q193 c4) ∷
   rw 7 (q194 c4) ∷
   rw 8 (q195 c4) ∷
   rw 9 (q194 c4) ∷
   rw 10 (q196 c4) ∷
   rw 11 (q197 c4) ∷
   rw 5 (q191 c4) ∷
   rw 2 (q198 c4) ∷
   rw 4 (q199 c4) ∷
   rw⁻ 3 (q200 c4) ∷
   rw 4 (q201 c4) ∷
   rw⁻ 5 (q202 c4) ∷
   rw 6 (q201 c4) ∷
   rw⁻ 7 (q203 c4) ∷
   rw⁻ 3 (q199 c4) ∷
   rw 4 (q189 c4) ∷
   rw⁻ 2 (q204 c4) ∷
   rw 1 (q140 c4) ∷
   rw⁻ 3 (q191 c4) ∷
   rw 2 (q192 c4) ∷
   rw 3 (q193 c4) ∷
   rw 4 (q194 c4) ∷
   rw 5 (q195 c4) ∷
   rw 6 (q194 c4) ∷
   rw 7 (q196 c4) ∷
   rw 8 (q197 c4) ∷
   rw 2 (q191 c4) ∷
   rw⁻ 3 (q188 c4) ∷
   rw 3 (q188 c4) ∷
   rw⁻ 6 (q205 c4) ∷
   rw 5 (q206 c4) ∷
   rw⁻ 4 (q205 c4) ∷
   rw 3 (q206 c4) ∷
   rw⁻ 4 (q188 c4) ∷
   rw 4 (q188 c4) ∷
   rw 7 (q189 c4) ∷
   rw 6 (q190 c4) ∷
   rw⁻ 9 (q191 c4) ∷
   rw 8 (q192 c4) ∷
   rw 9 (q193 c4) ∷
   rw 10 (q194 c4) ∷
   rw 11 (q195 c4) ∷
   rw 12 (q194 c4) ∷
   rw 13 (q196 c4) ∷
   rw 14 (q197 c4) ∷
   rw 8 (q191 c4) ∷
   rw 5 (q198 c4) ∷
   rw 7 (q199 c4) ∷
   rw⁻ 6 (q200 c4) ∷
   rw 7 (q201 c4) ∷
   rw⁻ 8 (q202 c4) ∷
   rw 9 (q201 c4) ∷
   rw⁻ 10 (q203 c4) ∷
   rw⁻ 6 (q199 c4) ∷
   rw 7 (q189 c4) ∷
   rw⁻ 5 (q204 c4) ∷
   rw 4 (q140 c4) ∷
   rw⁻ 6 (q191 c4) ∷
   rw 5 (q192 c4) ∷
   rw 6 (q193 c4) ∷
   rw 7 (q194 c4) ∷
   rw 8 (q195 c4) ∷
   rw 9 (q194 c4) ∷
   rw 10 (q196 c4) ∷
   rw 11 (q197 c4) ∷
   rw 5 (q191 c4) ∷
   rw⁻ 6 (q188 c4) ∷
   rw 6 (q188 c4) ∷
   rw⁻ 9 (q207 c4) ∷
   rw 8 (q208 c4) ∷
   rw⁻ 7 (q207 c4) ∷
   rw 6 (q208 c4) ∷
   rw⁻ 7 (q188 c4) ∷
   rw 1 (q209 c4) ∷
   rw 3 (q167 c4) ∷
   rw 0 (q233 c4) ∷
   rw⁻ 0 (q234 c4) ∷ []) Eq.refl
