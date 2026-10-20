{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D205 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0310243142 ; lem-box-perm-1324-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-perm-1324-at0310243142 ; lem-box2-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-CKc-box-at0310213442 ; lem-CKc-box-at03103441 ; lem-S2-SBOX⟨3·0·41·2⟩ ; lem-S2-SBOX⟨3·1·42·0⟩ ; lem-box-perm-1342-at03103441 ; lem-box-perm-1423-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-F0-at01143043 ; lem-F0-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ034-CS12 ; lem-comm-CCZ034-CX12 ; lem-comm-TOFF312-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CCZ034-CSd12)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb0-1-42-3 ∷ []) (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ []) (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ []) (wl 1267 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (Toff312 ∷ Toff214 ∷ []) (wl 1225 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl 888 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ034 ∷ K2 ∷ []) (K2 ∷ CCZ034 ∷ []) (wp 701 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ []) (wp 108 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ034 ∷ CX12 ∷ []) (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ034 ∷ []) (wp 107 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ034 ∷ CS14 ∷ []) (CS14 ∷ CCZ034 ∷ []) (wp 106 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ034 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ034 ∷ []) (wp 700 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ034 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp 716 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Toff312 ∷ Toff314 ∷ []) (Toff314 ∷ Toff312 ∷ []) (wl 779 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp 41 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) (wl 499 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Toff312 ∷ CX04 ∷ []) (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS14⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS14⁻ ∷ []) (wl 778 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) (wl 501 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Toff214 ∷ Toff314 ∷ Toff314 ∷ []) (Toff214 ∷ []) (wl 780 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ014 ∷ []) (wp 124 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS02 ∷ Toff312 ∷ []) (Toff312 ∷ CS02 ∷ []) (wl 861 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) (wp 3 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS02⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS02⁻ ∷ []) (wl 1226 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ034 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ034 ∷ []) (wp 2 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0241 ∷ []) (lem-box-perm-1423-at0310243142 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx3-0241 ∷ CK41 ∷ []) (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) (lem-CKc-box-at03103441 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0412 ∷ []) (lem-box-perm-1342-at03103441 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ124 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ []) (wl 871 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl 256 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (S4 ∷ Toff312 ∷ []) (Toff312 ∷ S4 ∷ []) (wl 1268 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ034 ∷ S4 ∷ []) (S4 ∷ CCZ034 ∷ []) (wp 981 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0142 ∷ []) (lem-box-perm-1324-at0310243142 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx3-0142 ∷ CK42 ∷ []) (CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0142 ∷ []) (lem-CKc-box-at0310213442 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ014 ∷ CS02 ∷ Toff214 ∷ []) (CS02 ∷ Toff214 ∷ CCZ014 ∷ []) (wp 1030 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ012 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ012 ∷ []) (wp 205 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl 341 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ012 ∷ S4 ∷ []) (S4 ∷ CCZ012 ∷ []) (wl 1269 (lit c4))

-- nf-rel-266@0: 163 steps
lem-nf-rel-266at0 : Ws → ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-nf-rel-266at0 c4 = derive (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 2 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 10 (q2 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 1 (q3 c4) ∷
   rw 5 (q3 c4) ∷
   rw 10 (q3 c4) ∷
   rw 14 (q3 c4) ∷
   re 8 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 10 1 (CS02 ∷ []) ∷
   re 12 1 (CS02⁻ ∷ []) ∷
   rw 0 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q9 c4) ∷
   rw 6 (q10 c4) ∷
   rw 7 (q11 c4) ∷
   rw 8 (q10 c4) ∷
   rw 9 (q12 c4) ∷
   rw 10 (q13 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw 5 (q15 c4) ∷
   rw 7 (q16 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw 7 (q18 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw 9 (q18 c4) ∷
   rw⁻ 10 (q20 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q10 c4) ∷
   rw 7 (q12 c4) ∷
   rw 8 (q13 c4) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 6 (q24 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q10 c4) ∷
   rw 10 (q11 c4) ∷
   rw 11 (q10 c4) ∷
   rw 12 (q12 c4) ∷
   rw 13 (q13 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 8 (q15 c4) ∷
   rw 10 (q16 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 10 (q18 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw 12 (q18 c4) ∷
   rw⁻ 13 (q20 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw 6 (q21 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q11 c4) ∷
   rw 9 (q10 c4) ∷
   rw 10 (q12 c4) ∷
   rw 11 (q13 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   rw⁻ 10 (q25 c4) ∷
   rw 9 (q26 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw 7 (q26 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw 8 (q27 c4) ∷
   rw 8 (q28 c4) ∷
   rw 11 (q29 c4) ∷
   rw 11 (q5 c4) ∷
   rw⁻ 14 (q30 c4) ∷
   rw 14 (q31 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q10 c4) ∷
   rw 17 (q12 c4) ∷
   rw⁻ 13 (q31 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw 12 (q31 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 11 (q31 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 12 (q27 c4) ∷
   rw 12 (q28 c4) ∷
   rw 15 (q29 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 18 (q32 c4) ∷
   rw 17 (q33 c4) ∷
   rw⁻ 16 (q32 c4) ∷
   rw 15 (q33 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw 16 (q34 c4) ∷
   rw 16 (q35 c4) ∷
   rw 19 (q36 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 22 (q30 c4) ∷
   rw 22 (q31 c4) ∷
   rw 21 (q9 c4) ∷
   rw 22 (q10 c4) ∷
   rw 23 (q11 c4) ∷
   rw 24 (q10 c4) ∷
   rw 25 (q12 c4) ∷
   rw⁻ 21 (q31 c4) ∷
   rw⁻ 20 (q30 c4) ∷
   rw 20 (q31 c4) ∷
   rw 19 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw 21 (q11 c4) ∷
   rw 22 (q10 c4) ∷
   rw 23 (q12 c4) ∷
   rw⁻ 19 (q31 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw 20 (q34 c4) ∷
   rw 20 (q35 c4) ∷
   rw 23 (q36 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 26 (q32 c4) ∷
   rw 25 (q33 c4) ∷
   rw⁻ 24 (q32 c4) ∷
   rw 23 (q33 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 3 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw 8 (q39 c4) ∷
   rw 9 (q40 c4) ∷
   rw 10 (q41 c4) ∷
   rw 11 (q40 c4) ∷
   rw 12 (q39 c4) ∷
   rw 13 (q40 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = eqn (Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ []) (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ024 ∷ []) (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ []) (wp 1118 c4)

-- nf-rel-267@0: 13 steps
lem-nf-rel-267at0 : Ws → ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
lem-nf-rel-267at0 c4 = derive (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ024 ∷ [])
  (rw 1 (q2 c4) ∷
   rw 2 (q2 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 8 (q2 c4) ∷
   rw 9 (q2 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 1 (q42 c4) ∷
   rw 4 (q3 c4) ∷
   rw 6 (q42 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 0 (q43 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ []) (wl 503 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl 348 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ034 ∷ CS12 ∷ []) (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ034 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ []) (wp 221 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ034 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CSd12 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (Bx3-0412 ∷ Bx3-0412 ∷ []) [] (lem-box2-at0310243142 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ []) (CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ []) (wp 1121 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ []) (S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ []) (wp 1122 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ014 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ []) (wp 686 c4)

-- nf-rel-268@0: 482 steps
lem-nf-rel-268at0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) ⟫ʷ
lem-nf-rel-268at0 c4 = derive (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ [])
  (rw 0 (q2 c4) ∷
   rw 2 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q2 c4) ∷
   rw 8 (q2 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 2 (q3 c4) ∷
   rw 5 (q42 c4) ∷
   rw 8 (q3 c4) ∷
   re 0 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 2 1 (CS02 ∷ []) ∷
   re 4 1 (CS02⁻ ∷ []) ∷
   re 10 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 12 1 (CS02 ∷ []) ∷
   re 14 1 (CS02⁻ ∷ []) ∷
   rw 10 (q5 c4) ∷
   rw⁻ 13 (q6 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q10 c4) ∷
   rw 17 (q12 c4) ∷
   rw 18 (q13 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw 13 (q15 c4) ∷
   rw 15 (q16 c4) ∷
   rw⁻ 14 (q17 c4) ∷
   rw 15 (q18 c4) ∷
   rw⁻ 16 (q19 c4) ∷
   rw 17 (q18 c4) ∷
   rw⁻ 18 (q20 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   rw 11 (q21 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q12 c4) ∷
   rw 16 (q13 c4) ∷
   rw 10 (q7 c4) ∷
   rw⁻ 11 (q22 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 12 (q5 c4) ∷
   rw⁻ 15 (q23 c4) ∷
   rw 14 (q24 c4) ∷
   rw⁻ 13 (q23 c4) ∷
   rw 12 (q24 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw 13 (q5 c4) ∷
   rw⁻ 16 (q6 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q11 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q13 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q14 c4) ∷
   rw⁻ 14 (q6 c4) ∷
   rw 16 (q15 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 18 (q18 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw 20 (q18 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw 14 (q21 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw 13 (q8 c4) ∷
   rw 14 (q9 c4) ∷
   rw 15 (q10 c4) ∷
   rw 16 (q11 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q12 c4) ∷
   rw 19 (q13 c4) ∷
   rw 13 (q7 c4) ∷
   rw⁻ 14 (q22 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 18 (q25 c4) ∷
   rw 17 (q26 c4) ∷
   rw⁻ 16 (q25 c4) ∷
   rw 15 (q26 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw 16 (q27 c4) ∷
   rw 16 (q28 c4) ∷
   rw 19 (q29 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 22 (q30 c4) ∷
   rw 22 (q31 c4) ∷
   rw 21 (q9 c4) ∷
   rw 22 (q10 c4) ∷
   rw 23 (q11 c4) ∷
   rw 24 (q10 c4) ∷
   rw 25 (q12 c4) ∷
   rw⁻ 21 (q31 c4) ∷
   rw⁻ 20 (q30 c4) ∷
   rw 20 (q31 c4) ∷
   rw 19 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw 21 (q11 c4) ∷
   rw 22 (q10 c4) ∷
   rw 23 (q12 c4) ∷
   rw⁻ 19 (q31 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw 20 (q27 c4) ∷
   rw 20 (q28 c4) ∷
   rw 23 (q29 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 26 (q32 c4) ∷
   rw 25 (q33 c4) ∷
   rw⁻ 24 (q32 c4) ∷
   rw 23 (q33 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 0 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q10 c4) ∷
   rw 7 (q12 c4) ∷
   rw 8 (q13 c4) ∷
   rw 2 (q7 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw 3 (q15 c4) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw 7 (q18 c4) ∷
   rw⁻ 8 (q20 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 1 (q7 c4) ∷
   rw 0 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q12 c4) ∷
   rw 6 (q13 c4) ∷
   rw 0 (q7 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q11 c4) ∷
   rw 9 (q10 c4) ∷
   rw 10 (q12 c4) ∷
   rw 11 (q13 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 6 (q15 c4) ∷
   rw 8 (q16 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw 10 (q18 c4) ∷
   rw⁻ 11 (q20 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 3 (q8 c4) ∷
   rw 4 (q9 c4) ∷
   rw 5 (q10 c4) ∷
   rw 6 (q11 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q12 c4) ∷
   rw 9 (q13 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 4 (q22 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw 7 (q26 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw 5 (q26 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 6 (q27 c4) ∷
   rw 6 (q28 c4) ∷
   rw 9 (q29 c4) ∷
   rw 9 (q5 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw 12 (q31 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 11 (q31 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   rw 10 (q31 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q12 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw 10 (q27 c4) ∷
   rw 10 (q28 c4) ∷
   rw 13 (q29 c4) ∷
   rw 13 (q5 c4) ∷
   rw⁻ 16 (q32 c4) ∷
   rw 15 (q33 c4) ∷
   rw⁻ 14 (q32 c4) ∷
   rw 13 (q33 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw 14 (q5 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 18 (q18 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw 20 (q18 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw 16 (q16 c4) ∷
   rw⁻ 15 (q17 c4) ∷
   rw 16 (q18 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw 18 (q18 c4) ∷
   rw⁻ 19 (q20 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   rw⁻ 14 (q22 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 18 (q6 c4) ∷
   rw⁻ 18 (q7 c4) ∷
   rw 17 (q8 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q11 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q12 c4) ∷
   rw 23 (q13 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q14 c4) ∷
   rw⁻ 16 (q6 c4) ∷
   rw 18 (q15 c4) ∷
   rw 20 (q16 c4) ∷
   rw⁻ 19 (q17 c4) ∷
   rw 20 (q18 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw 22 (q18 c4) ∷
   rw⁻ 23 (q20 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw 16 (q21 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q11 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q13 c4) ∷
   rw 15 (q7 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   rw 17 (q5 c4) ∷
   rw 21 (q16 c4) ∷
   rw⁻ 20 (q17 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw 23 (q18 c4) ∷
   rw⁻ 24 (q20 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 19 (q22 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 18 (q17 c4) ∷
   rw 19 (q18 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 22 (q20 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 17 (q22 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw⁻ 21 (q23 c4) ∷
   rw 20 (q24 c4) ∷
   rw⁻ 19 (q23 c4) ∷
   rw 18 (q24 c4) ∷
   rw⁻ 19 (q5 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw⁻ 22 (q7 c4) ∷
   rw 21 (q8 c4) ∷
   rw 22 (q9 c4) ∷
   rw 23 (q10 c4) ∷
   rw 24 (q11 c4) ∷
   rw 25 (q10 c4) ∷
   rw 26 (q12 c4) ∷
   rw 27 (q13 c4) ∷
   rw 21 (q7 c4) ∷
   rw 22 (q14 c4) ∷
   rw⁻ 20 (q6 c4) ∷
   rw 22 (q15 c4) ∷
   rw 24 (q16 c4) ∷
   rw⁻ 23 (q17 c4) ∷
   rw 24 (q18 c4) ∷
   rw⁻ 25 (q19 c4) ∷
   rw 26 (q18 c4) ∷
   rw⁻ 27 (q20 c4) ∷
   rw⁻ 23 (q16 c4) ∷
   rw 20 (q21 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   rw 19 (q8 c4) ∷
   rw 20 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q10 c4) ∷
   rw 24 (q12 c4) ∷
   rw 25 (q13 c4) ∷
   rw 19 (q7 c4) ∷
   rw⁻ 20 (q22 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw 21 (q5 c4) ∷
   rw 25 (q16 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw 25 (q18 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw 27 (q18 c4) ∷
   rw⁻ 28 (q20 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw⁻ 23 (q22 c4) ∷
   rw 23 (q16 c4) ∷
   rw⁻ 22 (q17 c4) ∷
   rw 23 (q18 c4) ∷
   rw⁻ 24 (q19 c4) ∷
   rw 25 (q18 c4) ∷
   rw⁻ 26 (q20 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 21 (q22 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw 22 (q5 c4) ∷
   rw⁻ 25 (q25 c4) ∷
   rw 24 (q26 c4) ∷
   rw⁻ 23 (q25 c4) ∷
   rw 22 (q26 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 26 (q44 c4) ∷
   rw 26 (q45 c4) ∷
   rw 25 (q46 c4) ∷
   rw 26 (q47 c4) ∷
   rw 27 (q48 c4) ∷
   rw 28 (q47 c4) ∷
   rw 29 (q24 c4) ∷
   rw⁻ 25 (q45 c4) ∷
   rw⁻ 24 (q44 c4) ∷
   rw 24 (q45 c4) ∷
   rw 23 (q46 c4) ∷
   rw 24 (q47 c4) ∷
   rw 25 (q48 c4) ∷
   rw 26 (q47 c4) ∷
   rw 27 (q24 c4) ∷
   rw⁻ 23 (q45 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 24 (q27 c4) ∷
   rw 24 (q28 c4) ∷
   rw 27 (q29 c4) ∷
   rw 27 (q5 c4) ∷
   rw⁻ 30 (q44 c4) ∷
   rw 30 (q45 c4) ∷
   rw 29 (q46 c4) ∷
   rw 30 (q47 c4) ∷
   rw 31 (q48 c4) ∷
   rw 32 (q47 c4) ∷
   rw 33 (q24 c4) ∷
   rw⁻ 29 (q45 c4) ∷
   rw⁻ 28 (q44 c4) ∷
   rw 28 (q45 c4) ∷
   rw 27 (q46 c4) ∷
   rw 28 (q47 c4) ∷
   rw 29 (q48 c4) ∷
   rw 30 (q47 c4) ∷
   rw 31 (q24 c4) ∷
   rw⁻ 27 (q45 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw 28 (q5 c4) ∷
   rw⁻ 31 (q30 c4) ∷
   rw 31 (q31 c4) ∷
   rw 30 (q9 c4) ∷
   rw 31 (q10 c4) ∷
   rw 32 (q11 c4) ∷
   rw 33 (q10 c4) ∷
   rw 34 (q12 c4) ∷
   rw⁻ 30 (q31 c4) ∷
   rw⁻ 29 (q30 c4) ∷
   rw 29 (q31 c4) ∷
   rw 28 (q9 c4) ∷
   rw 29 (q10 c4) ∷
   rw 30 (q11 c4) ∷
   rw 31 (q10 c4) ∷
   rw 32 (q12 c4) ∷
   rw⁻ 28 (q31 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw 29 (q5 c4) ∷
   rw⁻ 32 (q44 c4) ∷
   rw 32 (q45 c4) ∷
   rw 31 (q46 c4) ∷
   rw 32 (q47 c4) ∷
   rw 33 (q48 c4) ∷
   rw 34 (q47 c4) ∷
   rw 35 (q24 c4) ∷
   rw⁻ 31 (q45 c4) ∷
   rw⁻ 30 (q44 c4) ∷
   rw 30 (q45 c4) ∷
   rw 29 (q46 c4) ∷
   rw 30 (q47 c4) ∷
   rw 31 (q48 c4) ∷
   rw 32 (q47 c4) ∷
   rw 33 (q24 c4) ∷
   rw⁻ 29 (q45 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw 30 (q27 c4) ∷
   rw 30 (q28 c4) ∷
   rw 33 (q29 c4) ∷
   rw 33 (q5 c4) ∷
   rw⁻ 36 (q44 c4) ∷
   rw 36 (q45 c4) ∷
   rw 35 (q46 c4) ∷
   rw 36 (q47 c4) ∷
   rw 37 (q48 c4) ∷
   rw 38 (q47 c4) ∷
   rw 39 (q24 c4) ∷
   rw⁻ 35 (q45 c4) ∷
   rw⁻ 34 (q44 c4) ∷
   rw 34 (q45 c4) ∷
   rw 33 (q46 c4) ∷
   rw 34 (q47 c4) ∷
   rw 35 (q48 c4) ∷
   rw 36 (q47 c4) ∷
   rw 37 (q24 c4) ∷
   rw⁻ 33 (q45 c4) ∷
   rw⁻ 34 (q5 c4) ∷
   rw 34 (q5 c4) ∷
   rw⁻ 37 (q32 c4) ∷
   rw 36 (q33 c4) ∷
   rw⁻ 35 (q32 c4) ∷
   rw 34 (q33 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw 35 (q49 c4) ∷
   rw 1 (q37 c4) ∷
   rw 3 (q38 c4) ∷
   rw 4 (q50 c4) ∷
   rw 29 (q40 c4) ∷
   rw 5 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 7 (q51 c4) ∷
   rw 17 (q40 c4) ∷
   rw 8 (q52 c4) ∷
   rw 9 (q38 c4) ∷
   rw 9 (q37 c4) ∷
   rw 11 (q38 c4) ∷
   rw 15 (q40 c4) ∷
   rw 16 (q40 c4) ∷ []) Eq.refl
