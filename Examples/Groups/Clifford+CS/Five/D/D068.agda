{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D068 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0314213240 ; lem-box-cP-at12233441 ; lem-box-cP-at122441 ; lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-box-perm-1324-at122441 ; lem-box2-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-CSdu-box-3-at03143140 ; lem-CSu-box-3-at03143140 ; lem-box-perm-1324-at03143140 ; lem-box-perm-1324-at12233441 ; lem-box-perm-2314-at243243 ; lem-box-perm-3124-at143143 ; lem-box2-at03143140)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-box-perm-4213-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-S2-SBOX⟨0·1·42·3⟩ ; lem-S2-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-CKc-box-at12233441 ; lem-CKc-box-at13213442 ; lem-F0-R-at01143043 ; lem-box-perm-3421-at122441 ; lem-box-perm-4312-at13213442)
open import Examples.Groups.Clifford+CS.Five.D.D039 using (lem-F0-B-at01143043 ; lem-nf-X-CS1at2)
open import Examples.Groups.Clifford+CS.Five.D.D040 using (lem-nf-comm-CSu-CSat1 ; lem-nf-rel-266at1 ; lem-nf-rel-267at1)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CS13 ; lem-comm-CCZ024-CSd13 ; lem-comm-CCZ024-CX13 ; lem-comm-CX14-TOFF302 ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF014-CX23)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CCZ023-CX14 ; lem-comm-TOFF023-CX14)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ []) (CX43 ∷ []) (wl 1177 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Toff013 ∷ Toff134 ∷ []) (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp 843 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp 845 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) (wl 241 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) (wp 89 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp 36 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) (wp 35 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp 34 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) (wp 88 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Toff013 ∷ Toff034 ∷ []) (Toff034 ∷ Toff013 ∷ []) (wp 97 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl 245 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) (wp 95 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Toff013 ∷ CX24 ∷ []) (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS34⁻ ∷ []) (wp 94 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) (wl 246 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ234 ∷ []) (Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) (wp 842 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) (wp 90 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) (wl 247 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp 81 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CS12⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS12⁻ ∷ []) (wl 244 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) (wp 87 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl 1037 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl 305 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CX43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ []) (wl 1178 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ Bx0-2431 ∷ []) (lem-nf-X-CS1at2 c4)

-- F1-X-CS1@2: 86 steps
lem-F1-X-CS1at2 : Ws → ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-F1-X-CS1at2 c4 = derive (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  (re 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 7 1 (CS12 ∷ []) ∷
   re 9 1 (CS12⁻ ∷ []) ∷
   rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 5 (q5 c4) ∷
   rw 2 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 4 (q15 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q9 c4) ∷
   rw 6 (q8 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q11 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 4 (q2 c4) ∷
   rw 7 (q3 c4) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q10 c4) ∷
   rw 14 (q11 c4) ∷
   rw 8 (q5 c4) ∷
   rw 5 (q12 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 7 (q15 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw 9 (q15 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw 4 (q19 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   rw 1 (q24 c4) ∷
   rw 3 (q25 c4) ∷
   rw 0 (q26 c4) ∷
   rw⁻ 0 (q27 c4) ∷ []) Eq.refl

private
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx0-1423 ∷ []) (Bx0-4213 ∷ []) (lem-box-perm-2314-at243243 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CX03 ∷ CX03 ∷ []) [] (wl 1205 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CX03 ∷ Bx0-4213 ∷ CX03 ∷ []) (Bx0-4213 ∷ Bx3-4210 ∷ []) (lem-F0-B-at01143043 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CX03 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx3-4210 ∷ CX03 ∷ []) (lem-F0-R-at01143043 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CS13⁻ ∷ Bx3-4210 ∷ []) (Bx3-4210 ∷ CS13⁻ ∷ []) (lem-CSdu-box-3-at03143140 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx3-4210 ∷ []) (Bx3-4120 ∷ []) (lem-box-perm-1324-at03143140 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx3-4120 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) (Toff324 ∷ CCZ134 ∷ []) (wl 1189 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl 220 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS12 ∷ Toff302 ∷ []) (Toff302 ∷ CS12 ∷ []) (wl 1190 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CX14 ∷ Toff302 ∷ []) (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS24⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS24⁻ ∷ []) (wp 1005 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS24 ∷ Toff302 ∷ []) (Toff302 ∷ CS24 ∷ []) (wp 1006 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Toff302 ∷ Toff324 ∷ []) (Toff324 ∷ Toff302 ∷ []) (wp 1007 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl 1206 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS13 ∷ Bx3-4210 ∷ []) (Bx3-4210 ∷ CS13 ∷ []) (lem-CSu-box-3-at03143140 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx3-4210 ∷ Bx3-4210 ∷ []) [] (lem-box2-at03143140 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx0-4213 ∷ []) (Bx0-1423 ∷ []) (lem-box-perm-3124-at143143 c4)

-- CXuA-S @01143043: 44 steps
lem-CXuA-S-at01143043 : Ws → ⟪ (CX03 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CX03 ∷ []) ⟫ʷ
lem-CXuA-S-at01143043 c4 = derive (CX03 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CX03 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 1 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 0 (q30 c4) ∷
   rw 2 (q31 c4) ∷
   rw 5 (q32 c4) ∷
   rw 5 (q33 c4) ∷
   rw 5 (q34 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 6 (q36 c4) ∷
   rw 10 (q37 c4) ∷
   rw 9 (q38 c4) ∷
   rw 8 (q39 c4) ∷
   rw 7 (q38 c4) ∷
   rw 6 (q40 c4) ∷
   rw⁻ 7 (q36 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   rw⁻ 6 (q42 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   rw 3 (q43 c4) ∷
   rw 3 (q33 c4) ∷
   rw 3 (q34 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw 4 (q36 c4) ∷
   rw 8 (q37 c4) ∷
   rw 7 (q38 c4) ∷
   rw 6 (q39 c4) ∷
   rw 5 (q38 c4) ∷
   rw 4 (q40 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   rw⁻ 3 (q41 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   rw 1 (q44 c4) ∷
   rw 0 (q45 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Toff023 ∷ Toff324 ∷ []) (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp 805 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp 806 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) (wl 217 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ []) (wp 65 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) (wp 64 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) (wp 63 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) (wp 62 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ []) (wp 61 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ []) (wp 72 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) (wp 70 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (Toff023 ∷ CX14 ∷ []) (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ []) (wp 69 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) (wl 221 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CCZ124 ∷ []) (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) (wp 74 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) (wp 66 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) (wl 222 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp 53 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CS13⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS13⁻ ∷ []) (wl 219 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) (wp 60 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl 256 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (Toff013 ∷ CS24 ∷ []) (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) (wl 872 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Toff013 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CS14 ∷ Toff013 ∷ []) (Toff013 ∷ CS14 ∷ []) (wp 785 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ024 ∷ []) (wp 827 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (Bx0-2341 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (K3 ∷ Toff014 ∷ []) (Toff014 ∷ K3 ∷ []) (wp 819 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (CS34 ∷ Toff014 ∷ []) (Toff014 ∷ CS34 ∷ []) (wp 546 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (Toff014 ∷ CX23 ∷ []) (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (CS34⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS34⁻ ∷ []) (wp 818 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (CS24 ∷ Toff014 ∷ []) (Toff014 ∷ CS24 ∷ []) (wp 817 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (K3⁻ ∷ Toff014 ∷ []) (Toff014 ∷ K3⁻ ∷ []) (wp 816 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ023 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp 1046 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ []) (wp 839 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ023 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ023 ∷ []) (wp 669 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (CCZ023 ∷ CS24 ∷ []) (CS24 ∷ CCZ023 ∷ []) (wp 513 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ023 ∷ CX14 ∷ []) (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ023 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ023 ∷ []) (wp 820 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (CCZ023 ∷ CS12 ∷ []) (CS12 ∷ CCZ023 ∷ []) (wl 621 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (Toff324 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff324 ∷ []) (wp 821 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CS13 ∷ Toff013 ∷ []) (Toff013 ∷ CS13 ∷ []) (wl 910 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (CCZ024 ∷ CS13 ∷ []) (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (CS13⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS13⁻ ∷ []) (wl 907 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ024 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (Bx0-2431 ∷ []) (Bx0-1423 ∷ []) (lem-box-perm-4213-at122441 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (Bx0-1423 ∷ Bx0-1423 ∷ []) [] (lem-box2-at243243 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) (wl 450 (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl 263 (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (wl 1234 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lem-nf-comm-CSu-CSat1 c4)

-- F1-comm-CSu-CS@1: 288 steps
lem-F1-comm-CSu-CSat1 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CSu-CSat1 c4 = derive (Sb0-2-43-1 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ [])
  (re 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 2 1 (CS12 ∷ []) ∷
   re 4 1 (CS12⁻ ∷ []) ∷
   re 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 7 1 (CS13 ∷ []) ∷
   re 9 1 (CS13⁻ ∷ []) ∷
   rw 5 (q46 c4) ∷
   rw 8 (q47 c4) ∷
   rw 7 (q48 c4) ∷
   rw⁻ 10 (q49 c4) ∷
   rw 9 (q50 c4) ∷
   rw 10 (q51 c4) ∷
   rw 11 (q52 c4) ∷
   rw 12 (q53 c4) ∷
   rw 13 (q52 c4) ∷
   rw 14 (q54 c4) ∷
   rw 15 (q55 c4) ∷
   rw 9 (q49 c4) ∷
   rw 6 (q56 c4) ∷
   rw 8 (q36 c4) ∷
   rw⁻ 7 (q57 c4) ∷
   rw 8 (q58 c4) ∷
   rw⁻ 9 (q59 c4) ∷
   rw 10 (q58 c4) ∷
   rw⁻ 11 (q60 c4) ∷
   rw⁻ 7 (q36 c4) ∷
   rw 8 (q47 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw 5 (q62 c4) ∷
   rw⁻ 7 (q49 c4) ∷
   rw 6 (q50 c4) ∷
   rw 7 (q51 c4) ∷
   rw 8 (q52 c4) ∷
   rw 9 (q53 c4) ∷
   rw 10 (q52 c4) ∷
   rw 11 (q54 c4) ∷
   rw 12 (q55 c4) ∷
   rw 6 (q49 c4) ∷
   rw⁻ 7 (q46 c4) ∷
   rw 7 (q46 c4) ∷
   rw⁻ 10 (q63 c4) ∷
   rw 9 (q64 c4) ∷
   rw⁻ 8 (q63 c4) ∷
   rw 7 (q64 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw 8 (q46 c4) ∷
   rw 11 (q47 c4) ∷
   rw 10 (q48 c4) ∷
   rw⁻ 13 (q49 c4) ∷
   rw 12 (q50 c4) ∷
   rw 13 (q51 c4) ∷
   rw 14 (q52 c4) ∷
   rw 15 (q53 c4) ∷
   rw 16 (q52 c4) ∷
   rw 17 (q54 c4) ∷
   rw 18 (q55 c4) ∷
   rw 12 (q49 c4) ∷
   rw 9 (q56 c4) ∷
   rw 11 (q36 c4) ∷
   rw⁻ 10 (q57 c4) ∷
   rw 11 (q58 c4) ∷
   rw⁻ 12 (q59 c4) ∷
   rw 13 (q58 c4) ∷
   rw⁻ 14 (q60 c4) ∷
   rw⁻ 10 (q36 c4) ∷
   rw 11 (q47 c4) ∷
   rw⁻ 9 (q61 c4) ∷
   rw 8 (q62 c4) ∷
   rw⁻ 10 (q49 c4) ∷
   rw 9 (q50 c4) ∷
   rw 10 (q51 c4) ∷
   rw 11 (q52 c4) ∷
   rw 12 (q53 c4) ∷
   rw 13 (q52 c4) ∷
   rw 14 (q54 c4) ∷
   rw 15 (q55 c4) ∷
   rw 9 (q49 c4) ∷
   rw⁻ 10 (q46 c4) ∷
   rw 10 (q46 c4) ∷
   rw⁻ 13 (q65 c4) ∷
   rw 12 (q66 c4) ∷
   rw⁻ 11 (q65 c4) ∷
   rw 10 (q66 c4) ∷
   rw⁻ 11 (q46 c4) ∷
   rw 0 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q8 c4) ∷
   rw 7 (q9 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q10 c4) ∷
   rw 10 (q11 c4) ∷
   rw 4 (q5 c4) ∷
   rw 1 (q12 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   rw 0 (q19 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 3 (q8 c4) ∷
   rw 4 (q9 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q10 c4) ∷
   rw 7 (q11 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 2 (q2 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw 3 (q2 c4) ∷
   rw 6 (q3 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q8 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 7 (q5 c4) ∷
   rw 4 (q12 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw 8 (q15 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   rw 3 (q19 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q8 c4) ∷
   rw 7 (q9 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q10 c4) ∷
   rw 10 (q11 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 8 (q22 c4) ∷
   rw 7 (q23 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw 5 (q23 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw 6 (q2 c4) ∷
   rw 10 (q67 c4) ∷
   rw 9 (q68 c4) ∷
   rw⁻ 10 (q69 c4) ∷
   rw 11 (q70 c4) ∷
   rw⁻ 12 (q69 c4) ∷
   rw⁻ 13 (q71 c4) ∷
   rw⁻ 9 (q67 c4) ∷
   rw 8 (q72 c4) ∷
   rw 8 (q67 c4) ∷
   rw 7 (q68 c4) ∷
   rw⁻ 8 (q69 c4) ∷
   rw 9 (q70 c4) ∷
   rw⁻ 10 (q69 c4) ∷
   rw⁻ 11 (q71 c4) ∷
   rw⁻ 7 (q67 c4) ∷
   rw 6 (q72 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   rw 7 (q73 c4) ∷
   rw 7 (q74 c4) ∷
   rw⁻ 11 (q49 c4) ∷
   rw⁻ 10 (q75 c4) ∷
   rw⁻ 11 (q76 c4) ∷
   rw 12 (q77 c4) ∷
   rw⁻ 13 (q78 c4) ∷
   rw 14 (q77 c4) ∷
   rw⁻ 15 (q79 c4) ∷
   rw⁻ 16 (q80 c4) ∷
   rw 10 (q49 c4) ∷
   rw 9 (q81 c4) ∷
   rw⁻ 9 (q49 c4) ∷
   rw⁻ 8 (q75 c4) ∷
   rw⁻ 9 (q76 c4) ∷
   rw 10 (q77 c4) ∷
   rw⁻ 11 (q78 c4) ∷
   rw 12 (q77 c4) ∷
   rw⁻ 13 (q79 c4) ∷
   rw⁻ 14 (q80 c4) ∷
   rw 8 (q49 c4) ∷
   rw⁻ 9 (q82 c4) ∷
   rw 7 (q81 c4) ∷
   rw 9 (q83 c4) ∷
   rw 11 (q36 c4) ∷
   rw 10 (q84 c4) ∷
   rw 11 (q85 c4) ∷
   rw 12 (q86 c4) ∷
   rw 13 (q85 c4) ∷
   rw 14 (q87 c4) ∷
   rw⁻ 10 (q36 c4) ∷
   rw 7 (q88 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw⁻ 9 (q73 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 12 (q89 c4) ∷
   rw 11 (q90 c4) ∷
   rw⁻ 10 (q89 c4) ∷
   rw 9 (q90 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   rw 10 (q2 c4) ∷
   rw 14 (q67 c4) ∷
   rw 13 (q68 c4) ∷
   rw⁻ 14 (q69 c4) ∷
   rw 15 (q70 c4) ∷
   rw⁻ 16 (q69 c4) ∷
   rw⁻ 17 (q71 c4) ∷
   rw⁻ 13 (q67 c4) ∷
   rw 12 (q72 c4) ∷
   rw 12 (q67 c4) ∷
   rw 11 (q68 c4) ∷
   rw⁻ 12 (q69 c4) ∷
   rw 13 (q70 c4) ∷
   rw⁻ 14 (q69 c4) ∷
   rw⁻ 15 (q71 c4) ∷
   rw⁻ 11 (q67 c4) ∷
   rw 10 (q72 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   rw 11 (q73 c4) ∷
   rw 11 (q74 c4) ∷
   rw⁻ 15 (q49 c4) ∷
   rw⁻ 14 (q75 c4) ∷
   rw⁻ 15 (q76 c4) ∷
   rw 16 (q77 c4) ∷
   rw⁻ 17 (q78 c4) ∷
   rw 18 (q77 c4) ∷
   rw⁻ 19 (q79 c4) ∷
   rw⁻ 20 (q80 c4) ∷
   rw 14 (q49 c4) ∷
   rw 13 (q81 c4) ∷
   rw⁻ 13 (q49 c4) ∷
   rw⁻ 12 (q75 c4) ∷
   rw⁻ 13 (q76 c4) ∷
   rw 14 (q77 c4) ∷
   rw⁻ 15 (q78 c4) ∷
   rw 16 (q77 c4) ∷
   rw⁻ 17 (q79 c4) ∷
   rw⁻ 18 (q80 c4) ∷
   rw 12 (q49 c4) ∷
   rw⁻ 13 (q82 c4) ∷
   rw 11 (q81 c4) ∷
   rw 13 (q83 c4) ∷
   rw 15 (q36 c4) ∷
   rw 14 (q84 c4) ∷
   rw 15 (q85 c4) ∷
   rw 16 (q86 c4) ∷
   rw 17 (q85 c4) ∷
   rw 18 (q87 c4) ∷
   rw⁻ 14 (q36 c4) ∷
   rw 11 (q88 c4) ∷
   rw⁻ 13 (q74 c4) ∷
   rw⁻ 13 (q73 c4) ∷
   rw 13 (q2 c4) ∷
   rw⁻ 16 (q91 c4) ∷
   rw 15 (q92 c4) ∷
   rw⁻ 14 (q91 c4) ∷
   rw 13 (q92 c4) ∷
   rw⁻ 14 (q2 c4) ∷
   rw 14 (q93 c4) ∷
   rw 14 (q94 c4) ∷
   rw 0 (q24 c4) ∷
   rw 2 (q25 c4) ∷
   rw 4 (q95 c4) ∷
   rw 5 (q96 c4) ∷
   rw 6 (q95 c4) ∷
   rw 7 (q96 c4) ∷
   rw 0 (q97 c4) ∷
   rw⁻ 0 (q98 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ []) (wl 1287 (lit c4))
  q101 : Ws → Eqn
  q101 c4 = eqn (Bx0-2431 ∷ []) (Bx0-3142 ∷ []) (lem-box-perm-3421-at122441 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (Bx0-3142 ∷ CK42 ∷ []) (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ []) (lem-CKc-box-at13213442 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (Bx0-3142 ∷ []) (Bx0-2431 ∷ []) (lem-box-perm-4312-at13213442 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (S4 ∷ Toff013 ∷ []) (Toff013 ∷ S4 ∷ []) (wp 647 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (CCZ024 ∷ S4 ∷ []) (S4 ∷ CCZ024 ∷ []) (wp 617 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (Bx0-2341 ∷ CK41 ∷ []) (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Bx0-2341 ∷ []) (lem-CKc-box-at12233441 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (Bx0-2341 ∷ []) (Bx0-2431 ∷ []) (lem-box-perm-1324-at12233441 c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ123 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ123 ∷ []) (wl 770 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl 181 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ123 ∷ S4 ∷ []) (S4 ∷ CCZ123 ∷ []) (wl 1286 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (Toff124 ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ []) (wl 1288 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (lem-nf-rel-266at1 c4)

-- F1-rel-266@1: 157 steps
lem-F1-rel-266at1 : Ws → ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266at1 c4 = derive (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  (rw 1 (q99 c4) ∷
   rw 5 (q99 c4) ∷
   rw 10 (q99 c4) ∷
   rw 14 (q99 c4) ∷
   re 8 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 10 1 (CS12 ∷ []) ∷
   re 12 1 (CS12⁻ ∷ []) ∷
   rw 0 (q100 c4) ∷
   rw 2 (q2 c4) ∷
   rw 5 (q3 c4) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q10 c4) ∷
   rw 12 (q11 c4) ∷
   rw 6 (q5 c4) ∷
   rw 3 (q12 c4) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw 7 (q15 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q10 c4) ∷
   rw 9 (q11 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw 6 (q21 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   rw 5 (q2 c4) ∷
   rw 8 (q3 c4) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw 9 (q6 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q8 c4) ∷
   rw 12 (q9 c4) ∷
   rw 13 (q8 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q11 c4) ∷
   rw 9 (q5 c4) ∷
   rw 6 (q12 c4) ∷
   rw 8 (q13 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q15 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw 10 (q15 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 6 (q18 c4) ∷
   rw 5 (q19 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q10 c4) ∷
   rw 12 (q11 c4) ∷
   rw 6 (q5 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 10 (q22 c4) ∷
   rw 9 (q23 c4) ∷
   rw⁻ 8 (q22 c4) ∷
   rw 7 (q23 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   rw 8 (q101 c4) ∷
   rw 8 (q102 c4) ∷
   rw 11 (q103 c4) ∷
   rw 11 (q2 c4) ∷
   rw 15 (q67 c4) ∷
   rw 14 (q68 c4) ∷
   rw⁻ 15 (q69 c4) ∷
   rw 16 (q70 c4) ∷
   rw⁻ 17 (q69 c4) ∷
   rw⁻ 18 (q71 c4) ∷
   rw⁻ 14 (q67 c4) ∷
   rw 13 (q72 c4) ∷
   rw 13 (q67 c4) ∷
   rw 12 (q68 c4) ∷
   rw⁻ 13 (q69 c4) ∷
   rw 14 (q70 c4) ∷
   rw⁻ 15 (q69 c4) ∷
   rw⁻ 16 (q71 c4) ∷
   rw⁻ 12 (q67 c4) ∷
   rw 11 (q72 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw 12 (q101 c4) ∷
   rw 12 (q102 c4) ∷
   rw 15 (q103 c4) ∷
   rw 15 (q2 c4) ∷
   rw⁻ 18 (q104 c4) ∷
   rw 17 (q105 c4) ∷
   rw⁻ 16 (q104 c4) ∷
   rw 15 (q105 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw 16 (q73 c4) ∷
   rw 16 (q106 c4) ∷
   rw 19 (q107 c4) ∷
   rw 19 (q2 c4) ∷
   rw 23 (q67 c4) ∷
   rw 22 (q68 c4) ∷
   rw⁻ 23 (q69 c4) ∷
   rw 24 (q70 c4) ∷
   rw⁻ 25 (q69 c4) ∷
   rw⁻ 26 (q71 c4) ∷
   rw⁻ 22 (q67 c4) ∷
   rw 21 (q72 c4) ∷
   rw 21 (q67 c4) ∷
   rw 20 (q68 c4) ∷
   rw⁻ 21 (q69 c4) ∷
   rw 22 (q70 c4) ∷
   rw⁻ 23 (q69 c4) ∷
   rw⁻ 24 (q71 c4) ∷
   rw⁻ 20 (q67 c4) ∷
   rw 19 (q72 c4) ∷
   rw⁻ 20 (q2 c4) ∷
   rw 20 (q73 c4) ∷
   rw 20 (q106 c4) ∷
   rw 23 (q107 c4) ∷
   rw 23 (q2 c4) ∷
   rw⁻ 26 (q104 c4) ∷
   rw 25 (q105 c4) ∷
   rw⁻ 24 (q104 c4) ∷
   rw 23 (q105 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw 2 (q24 c4) ∷
   rw 4 (q25 c4) ∷
   rw 8 (q108 c4) ∷
   rw 9 (q109 c4) ∷
   rw 10 (q110 c4) ∷
   rw 11 (q109 c4) ∷
   rw 12 (q108 c4) ∷
   rw 13 (q109 c4) ∷
   rw 16 (q93 c4) ∷
   rw 0 (q111 c4) ∷
   rw⁻ 0 (q112 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q114 : Ws → Eqn
  q114 c4 = eqn (CCZ134 ∷ []) (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (wl 1290 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (CCZ134 ∷ []) (CCZ134 ∷ []) (wl 1291 (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ134 ∷ []) (lem-nf-rel-267at1 c4)

-- F1-rel-267@1: 8 steps
lem-F1-rel-267at1 : Ws → ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-rel-267at1 c4 = derive (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  (rw 1 (q99 c4) ∷
   rw 5 (q99 c4) ∷
   rw 8 (q113 c4) ∷
   rw 10 (q99 c4) ∷
   rw 14 (q99 c4) ∷
   rw⁻ 0 (q114 c4) ∷
   rw 0 (q115 c4) ∷
   rw⁻ 0 (q116 c4) ∷ []) Eq.refl
