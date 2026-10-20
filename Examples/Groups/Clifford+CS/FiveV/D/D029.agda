{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D029 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.FiveV.D.D016 using (lem-box-cP-at03243240 ; lem-box-cP-at033440)
open import Examples.Groups.Clifford+CS.FiveV.D.D021 using (lem-box-perm-1324-at03243240)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CCZ134-CS02 ; lem-comm-CCZ134-CX02 ; lem-comm-TOFF304-CX12)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CCZ123-CX04 ; lem-comm-CCZ134-CSd02)
open import Examples.Groups.Clifford+CS.FiveV.D.R009 using (lem-comm-TOFF302-CS14 ; lem-comm-TOFF302-CSd14 ; lem-comm-TOFF302-CX14)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CCZ123 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ123 ∷ []) (wl 764 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ123 ∷ CX04 ∷ []) (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ123 ∷ CS01 ∷ []) (CS01 ∷ CCZ123 ∷ []) (wl 763 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp 41 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ123 ∷ []) (wl 618 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ014 ∷ []) (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp 1040 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx3-1240 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx3-1420 ∷ []) (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx3-1420 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp 301 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Toff302 ∷ CS14 ∷ []) (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CX01 ∷ Toff302 ∷ []) (Toff302 ∷ CX01 ∷ []) (wl 1233 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Toff302 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS04 ∷ Toff302 ∷ []) (Toff302 ∷ CS04 ∷ []) (wp 1041 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ []) (wp 272 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (K1 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ K1⁻ ∷ []) (Toff124 ∷ []) (wl 1313 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (K1 ∷ Toff302 ∷ []) (Toff302 ∷ K1 ∷ []) (wl 1252 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS24 ∷ Toff302 ∷ []) (Toff302 ∷ CS24 ∷ []) (wp 1006 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Toff302 ∷ CX14 ∷ []) (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS24⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS24⁻ ∷ []) (wp 1005 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS12 ∷ Toff302 ∷ []) (Toff302 ∷ CS12 ∷ []) (wl 1190 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (K1⁻ ∷ Toff302 ∷ []) (Toff302 ∷ K1⁻ ∷ []) (wl 1312 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ134 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl 1314 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ024 ∷ CCZ234 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ234 ∷ []) (wp 1136 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp 296 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ134 ∷ CS24 ∷ []) (CS24 ∷ CCZ134 ∷ []) (wl 1220 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ134 ∷ CX02 ∷ []) (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ134 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ134 ∷ []) (wl 1221 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ134 ∷ CS04 ∷ []) (CS04 ∷ CCZ134 ∷ []) (wp 1003 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ134 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ134 ∷ []) (wl 960 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ024 ∷ []) (CCZ234 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp 1137 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ024 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ []) (wp 1138 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl 888 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (K2 ∷ Toff304 ∷ []) (Toff304 ∷ K2 ∷ []) (wp 1035 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CS24 ∷ Toff304 ∷ []) (Toff304 ∷ CS24 ∷ []) (wp 691 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Toff304 ∷ CX12 ∷ []) (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS24⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS24⁻ ∷ []) (wp 1036 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CS14 ∷ Toff304 ∷ []) (Toff304 ∷ CS14 ∷ []) (wp 1037 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (K2⁻ ∷ Toff304 ∷ []) (Toff304 ∷ K2⁻ ∷ []) (wp 1038 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl 758 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ014 ∷ CCZ134 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ134 ∷ []) (wp 1039 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ []) (wl 765 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS02 ∷ Toff302 ∷ []) (Toff302 ∷ CS02 ∷ []) (wl 801 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ134 ∷ CS02 ∷ []) (CS02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CS02 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CS02⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS02⁻ ∷ []) (wl 792 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ134 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CSd02 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ124 ∷ CS01 ∷ Toff024 ∷ []) (CS01 ∷ Toff024 ∷ CCZ124 ∷ []) (wp 1042 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl 263 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ []) (CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ []) (wp 1139 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp 135 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ124 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ []) (wp 743 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)

-- L-CCZ-0 part2: 500 steps
lem-L-CCZ-0-part2 : Ws → ⟪ (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CCZ123 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-L-CCZ-0-part2 c4 = derive (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CCZ123 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ [])
  (rw 24 (q1 c4) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q3 c4) ∷
   rw⁻ 22 (q4 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 21 (q6 c4) ∷
   rw⁻ 22 (q7 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw 22 (q9 c4) ∷
   rw 26 (q10 c4) ∷
   rw 25 (q11 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw 27 (q13 c4) ∷
   rw⁻ 28 (q12 c4) ∷
   rw⁻ 29 (q14 c4) ∷
   rw⁻ 25 (q10 c4) ∷
   rw⁻ 24 (q15 c4) ∷
   rw 24 (q10 c4) ∷
   rw 23 (q11 c4) ∷
   rw⁻ 24 (q12 c4) ∷
   rw 25 (q13 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 22 (q15 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw 23 (q9 c4) ∷
   rw⁻ 27 (q16 c4) ∷
   rw⁻ 26 (q17 c4) ∷
   rw⁻ 27 (q18 c4) ∷
   rw 28 (q19 c4) ∷
   rw⁻ 29 (q20 c4) ∷
   rw 30 (q19 c4) ∷
   rw⁻ 31 (q21 c4) ∷
   rw⁻ 32 (q22 c4) ∷
   rw 26 (q16 c4) ∷
   rw 25 (q23 c4) ∷
   rw⁻ 25 (q16 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw⁻ 25 (q18 c4) ∷
   rw 26 (q19 c4) ∷
   rw⁻ 27 (q20 c4) ∷
   rw 28 (q19 c4) ∷
   rw⁻ 29 (q21 c4) ∷
   rw⁻ 30 (q22 c4) ∷
   rw 24 (q16 c4) ∷
   rw⁻ 25 (q24 c4) ∷
   rw 23 (q23 c4) ∷
   rw 26 (q25 c4) ∷
   rw 25 (q26 c4) ∷
   rw 26 (q27 c4) ∷
   rw 27 (q28 c4) ∷
   rw 28 (q27 c4) ∷
   rw 29 (q29 c4) ∷
   rw⁻ 25 (q25 c4) ∷
   rw 26 (q30 c4) ∷
   rw⁻ 24 (q31 c4) ∷
   rw⁻ 25 (q9 c4) ∷
   rw 25 (q9 c4) ∷
   rw⁻ 28 (q32 c4) ∷
   rw 28 (q25 c4) ∷
   rw 27 (q26 c4) ∷
   rw 28 (q27 c4) ∷
   rw 29 (q28 c4) ∷
   rw 30 (q27 c4) ∷
   rw 31 (q29 c4) ∷
   rw⁻ 27 (q25 c4) ∷
   rw⁻ 26 (q32 c4) ∷
   rw 26 (q25 c4) ∷
   rw 25 (q26 c4) ∷
   rw 26 (q27 c4) ∷
   rw 27 (q28 c4) ∷
   rw 28 (q27 c4) ∷
   rw 29 (q29 c4) ∷
   rw⁻ 25 (q25 c4) ∷
   rw⁻ 26 (q9 c4) ∷
   rw 26 (q8 c4) ∷
   rw 26 (q7 c4) ∷
   rw⁻ 30 (q33 c4) ∷
   rw⁻ 29 (q34 c4) ∷
   rw⁻ 30 (q35 c4) ∷
   rw 31 (q36 c4) ∷
   rw⁻ 32 (q37 c4) ∷
   rw 33 (q36 c4) ∷
   rw⁻ 34 (q38 c4) ∷
   rw⁻ 35 (q39 c4) ∷
   rw 29 (q33 c4) ∷
   rw 28 (q40 c4) ∷
   rw⁻ 28 (q33 c4) ∷
   rw⁻ 27 (q34 c4) ∷
   rw⁻ 28 (q35 c4) ∷
   rw 29 (q36 c4) ∷
   rw⁻ 30 (q37 c4) ∷
   rw 31 (q36 c4) ∷
   rw⁻ 32 (q38 c4) ∷
   rw⁻ 33 (q39 c4) ∷
   rw 27 (q33 c4) ∷
   rw⁻ 28 (q41 c4) ∷
   rw 26 (q40 c4) ∷
   rw 29 (q4 c4) ∷
   rw 28 (q42 c4) ∷
   rw 29 (q2 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q2 c4) ∷
   rw 32 (q3 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw 29 (q5 c4) ∷
   rw⁻ 27 (q6 c4) ∷
   rw⁻ 28 (q7 c4) ∷
   rw⁻ 28 (q8 c4) ∷
   rw 28 (q9 c4) ∷
   rw 32 (q10 c4) ∷
   rw 31 (q11 c4) ∷
   rw⁻ 32 (q12 c4) ∷
   rw 33 (q13 c4) ∷
   rw⁻ 34 (q12 c4) ∷
   rw⁻ 35 (q14 c4) ∷
   rw⁻ 31 (q10 c4) ∷
   rw⁻ 30 (q15 c4) ∷
   rw 30 (q10 c4) ∷
   rw 29 (q11 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw 31 (q13 c4) ∷
   rw⁻ 32 (q12 c4) ∷
   rw⁻ 33 (q14 c4) ∷
   rw⁻ 29 (q10 c4) ∷
   rw⁻ 28 (q15 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw 29 (q8 c4) ∷
   rw 29 (q7 c4) ∷
   rw⁻ 33 (q33 c4) ∷
   rw⁻ 32 (q34 c4) ∷
   rw⁻ 33 (q35 c4) ∷
   rw 34 (q36 c4) ∷
   rw⁻ 35 (q37 c4) ∷
   rw 36 (q36 c4) ∷
   rw⁻ 37 (q38 c4) ∷
   rw⁻ 38 (q39 c4) ∷
   rw 32 (q33 c4) ∷
   rw 31 (q40 c4) ∷
   rw⁻ 31 (q33 c4) ∷
   rw⁻ 30 (q34 c4) ∷
   rw⁻ 31 (q35 c4) ∷
   rw 32 (q36 c4) ∷
   rw⁻ 33 (q37 c4) ∷
   rw 34 (q36 c4) ∷
   rw⁻ 35 (q38 c4) ∷
   rw⁻ 36 (q39 c4) ∷
   rw 30 (q33 c4) ∷
   rw⁻ 31 (q41 c4) ∷
   rw 29 (q40 c4) ∷
   rw 32 (q4 c4) ∷
   rw 31 (q42 c4) ∷
   rw 32 (q2 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q2 c4) ∷
   rw 35 (q3 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw 32 (q5 c4) ∷
   rw⁻ 30 (q6 c4) ∷
   rw⁻ 31 (q7 c4) ∷
   rw⁻ 31 (q8 c4) ∷
   rw 31 (q9 c4) ∷
   rw 35 (q10 c4) ∷
   rw 34 (q11 c4) ∷
   rw⁻ 35 (q12 c4) ∷
   rw 36 (q13 c4) ∷
   rw⁻ 37 (q12 c4) ∷
   rw⁻ 38 (q14 c4) ∷
   rw⁻ 34 (q10 c4) ∷
   rw⁻ 33 (q15 c4) ∷
   rw 33 (q10 c4) ∷
   rw 32 (q11 c4) ∷
   rw⁻ 33 (q12 c4) ∷
   rw 34 (q13 c4) ∷
   rw⁻ 35 (q12 c4) ∷
   rw⁻ 36 (q14 c4) ∷
   rw⁻ 32 (q10 c4) ∷
   rw⁻ 31 (q15 c4) ∷
   rw⁻ 32 (q9 c4) ∷
   rw 32 (q9 c4) ∷
   rw 36 (q10 c4) ∷
   rw 35 (q11 c4) ∷
   rw⁻ 36 (q12 c4) ∷
   rw 37 (q13 c4) ∷
   rw⁻ 38 (q12 c4) ∷
   rw⁻ 39 (q14 c4) ∷
   rw⁻ 35 (q10 c4) ∷
   rw⁻ 34 (q15 c4) ∷
   rw 34 (q10 c4) ∷
   rw 33 (q11 c4) ∷
   rw⁻ 34 (q12 c4) ∷
   rw 35 (q13 c4) ∷
   rw⁻ 36 (q12 c4) ∷
   rw⁻ 37 (q14 c4) ∷
   rw⁻ 33 (q10 c4) ∷
   rw⁻ 32 (q15 c4) ∷
   rw⁻ 33 (q9 c4) ∷
   rw 33 (q9 c4) ∷
   rw⁻ 36 (q43 c4) ∷
   rw 35 (q44 c4) ∷
   rw⁻ 34 (q43 c4) ∷
   rw 33 (q44 c4) ∷
   rw⁻ 34 (q9 c4) ∷
   rw 34 (q8 c4) ∷
   rw 34 (q7 c4) ∷
   rw⁻ 38 (q33 c4) ∷
   rw⁻ 37 (q34 c4) ∷
   rw⁻ 38 (q35 c4) ∷
   rw 39 (q36 c4) ∷
   rw⁻ 40 (q37 c4) ∷
   rw 41 (q36 c4) ∷
   rw⁻ 42 (q38 c4) ∷
   rw⁻ 43 (q39 c4) ∷
   rw 37 (q33 c4) ∷
   rw 36 (q40 c4) ∷
   rw⁻ 36 (q33 c4) ∷
   rw⁻ 35 (q34 c4) ∷
   rw⁻ 36 (q35 c4) ∷
   rw 37 (q36 c4) ∷
   rw⁻ 38 (q37 c4) ∷
   rw 39 (q36 c4) ∷
   rw⁻ 40 (q38 c4) ∷
   rw⁻ 41 (q39 c4) ∷
   rw 35 (q33 c4) ∷
   rw⁻ 36 (q41 c4) ∷
   rw 34 (q40 c4) ∷
   rw 37 (q4 c4) ∷
   rw 36 (q42 c4) ∷
   rw 37 (q2 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q2 c4) ∷
   rw 40 (q3 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw 37 (q5 c4) ∷
   rw⁻ 35 (q6 c4) ∷
   rw⁻ 36 (q7 c4) ∷
   rw⁻ 36 (q8 c4) ∷
   rw 36 (q9 c4) ∷
   rw 40 (q10 c4) ∷
   rw 39 (q11 c4) ∷
   rw⁻ 40 (q12 c4) ∷
   rw 41 (q13 c4) ∷
   rw⁻ 42 (q12 c4) ∷
   rw⁻ 43 (q14 c4) ∷
   rw⁻ 39 (q10 c4) ∷
   rw⁻ 38 (q15 c4) ∷
   rw 38 (q10 c4) ∷
   rw 37 (q11 c4) ∷
   rw⁻ 38 (q12 c4) ∷
   rw 39 (q13 c4) ∷
   rw⁻ 40 (q12 c4) ∷
   rw⁻ 41 (q14 c4) ∷
   rw⁻ 37 (q10 c4) ∷
   rw⁻ 36 (q15 c4) ∷
   rw⁻ 37 (q9 c4) ∷
   rw 37 (q9 c4) ∷
   rw 41 (q10 c4) ∷
   rw 40 (q11 c4) ∷
   rw⁻ 41 (q12 c4) ∷
   rw 42 (q13 c4) ∷
   rw⁻ 43 (q12 c4) ∷
   rw⁻ 44 (q14 c4) ∷
   rw⁻ 40 (q10 c4) ∷
   rw⁻ 39 (q15 c4) ∷
   rw 39 (q10 c4) ∷
   rw 38 (q11 c4) ∷
   rw⁻ 39 (q12 c4) ∷
   rw 40 (q13 c4) ∷
   rw⁻ 41 (q12 c4) ∷
   rw⁻ 42 (q14 c4) ∷
   rw⁻ 38 (q10 c4) ∷
   rw⁻ 37 (q15 c4) ∷
   rw⁻ 38 (q9 c4) ∷
   rw 38 (q9 c4) ∷
   rw⁻ 41 (q45 c4) ∷
   rw 40 (q46 c4) ∷
   rw⁻ 39 (q45 c4) ∷
   rw 38 (q46 c4) ∷
   rw⁻ 39 (q9 c4) ∷
   rw 39 (q8 c4) ∷
   rw 39 (q7 c4) ∷
   rw⁻ 43 (q33 c4) ∷
   rw⁻ 42 (q34 c4) ∷
   rw⁻ 43 (q35 c4) ∷
   rw 44 (q36 c4) ∷
   rw⁻ 45 (q37 c4) ∷
   rw 46 (q36 c4) ∷
   rw⁻ 47 (q38 c4) ∷
   rw⁻ 48 (q39 c4) ∷
   rw 42 (q33 c4) ∷
   rw 41 (q40 c4) ∷
   rw⁻ 41 (q33 c4) ∷
   rw⁻ 40 (q34 c4) ∷
   rw⁻ 41 (q35 c4) ∷
   rw 42 (q36 c4) ∷
   rw⁻ 43 (q37 c4) ∷
   rw 44 (q36 c4) ∷
   rw⁻ 45 (q38 c4) ∷
   rw⁻ 46 (q39 c4) ∷
   rw 40 (q33 c4) ∷
   rw⁻ 41 (q41 c4) ∷
   rw 39 (q40 c4) ∷
   rw 42 (q4 c4) ∷
   rw 41 (q42 c4) ∷
   rw 42 (q2 c4) ∷
   rw 43 (q1 c4) ∷
   rw 44 (q2 c4) ∷
   rw 45 (q3 c4) ∷
   rw⁻ 41 (q4 c4) ∷
   rw 42 (q5 c4) ∷
   rw⁻ 40 (q6 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   rw⁻ 41 (q8 c4) ∷
   rw 41 (q9 c4) ∷
   rw 45 (q10 c4) ∷
   rw 44 (q11 c4) ∷
   rw⁻ 45 (q12 c4) ∷
   rw 46 (q13 c4) ∷
   rw⁻ 47 (q12 c4) ∷
   rw⁻ 48 (q14 c4) ∷
   rw⁻ 44 (q10 c4) ∷
   rw⁻ 43 (q15 c4) ∷
   rw 43 (q10 c4) ∷
   rw 42 (q11 c4) ∷
   rw⁻ 43 (q12 c4) ∷
   rw 44 (q13 c4) ∷
   rw⁻ 45 (q12 c4) ∷
   rw⁻ 46 (q14 c4) ∷
   rw⁻ 42 (q10 c4) ∷
   rw⁻ 41 (q15 c4) ∷
   rw⁻ 42 (q9 c4) ∷
   rw 42 (q9 c4) ∷
   rw 46 (q10 c4) ∷
   rw 45 (q11 c4) ∷
   rw⁻ 46 (q12 c4) ∷
   rw 47 (q13 c4) ∷
   rw⁻ 48 (q12 c4) ∷
   rw⁻ 49 (q14 c4) ∷
   rw⁻ 45 (q10 c4) ∷
   rw⁻ 44 (q15 c4) ∷
   rw 44 (q10 c4) ∷
   rw 43 (q11 c4) ∷
   rw⁻ 44 (q12 c4) ∷
   rw 45 (q13 c4) ∷
   rw⁻ 46 (q12 c4) ∷
   rw⁻ 47 (q14 c4) ∷
   rw⁻ 43 (q10 c4) ∷
   rw⁻ 42 (q15 c4) ∷
   rw⁻ 43 (q9 c4) ∷
   rw 43 (q9 c4) ∷
   rw⁻ 47 (q16 c4) ∷
   rw⁻ 46 (q17 c4) ∷
   rw⁻ 47 (q18 c4) ∷
   rw 48 (q19 c4) ∷
   rw⁻ 49 (q20 c4) ∷
   rw 50 (q19 c4) ∷
   rw⁻ 51 (q21 c4) ∷
   rw⁻ 52 (q22 c4) ∷
   rw 46 (q16 c4) ∷
   rw 45 (q23 c4) ∷
   rw⁻ 45 (q16 c4) ∷
   rw⁻ 44 (q17 c4) ∷
   rw⁻ 45 (q18 c4) ∷
   rw 46 (q19 c4) ∷
   rw⁻ 47 (q20 c4) ∷
   rw 48 (q19 c4) ∷
   rw⁻ 49 (q21 c4) ∷
   rw⁻ 50 (q22 c4) ∷
   rw 44 (q16 c4) ∷
   rw⁻ 45 (q24 c4) ∷
   rw 43 (q23 c4) ∷
   rw 46 (q25 c4) ∷
   rw 45 (q26 c4) ∷
   rw 46 (q27 c4) ∷
   rw 47 (q28 c4) ∷
   rw 48 (q27 c4) ∷
   rw 49 (q29 c4) ∷
   rw⁻ 45 (q25 c4) ∷
   rw 46 (q30 c4) ∷
   rw⁻ 44 (q31 c4) ∷
   rw⁻ 45 (q9 c4) ∷
   rw 45 (q9 c4) ∷
   rw⁻ 48 (q32 c4) ∷
   rw 48 (q25 c4) ∷
   rw 47 (q26 c4) ∷
   rw 48 (q27 c4) ∷
   rw 49 (q28 c4) ∷
   rw 50 (q27 c4) ∷
   rw 51 (q29 c4) ∷
   rw⁻ 47 (q25 c4) ∷
   rw⁻ 46 (q32 c4) ∷
   rw 46 (q25 c4) ∷
   rw 45 (q26 c4) ∷
   rw 46 (q27 c4) ∷
   rw 47 (q28 c4) ∷
   rw 48 (q27 c4) ∷
   rw 49 (q29 c4) ∷
   rw⁻ 45 (q25 c4) ∷
   rw⁻ 46 (q9 c4) ∷
   rw 46 (q9 c4) ∷
   rw⁻ 49 (q32 c4) ∷
   rw 49 (q25 c4) ∷
   rw 48 (q26 c4) ∷
   rw 49 (q27 c4) ∷
   rw 50 (q28 c4) ∷
   rw 51 (q27 c4) ∷
   rw 52 (q29 c4) ∷
   rw⁻ 48 (q25 c4) ∷
   rw⁻ 47 (q32 c4) ∷
   rw 47 (q25 c4) ∷
   rw 46 (q26 c4) ∷
   rw 47 (q27 c4) ∷
   rw 48 (q28 c4) ∷
   rw 49 (q27 c4) ∷
   rw 50 (q29 c4) ∷
   rw⁻ 46 (q25 c4) ∷
   rw⁻ 47 (q9 c4) ∷
   rw 47 (q8 c4) ∷
   rw 47 (q7 c4) ∷
   rw⁻ 51 (q33 c4) ∷
   rw⁻ 50 (q34 c4) ∷
   rw⁻ 51 (q35 c4) ∷
   rw 52 (q36 c4) ∷
   rw⁻ 53 (q37 c4) ∷
   rw 54 (q36 c4) ∷
   rw⁻ 55 (q38 c4) ∷
   rw⁻ 56 (q39 c4) ∷
   rw 50 (q33 c4) ∷
   rw 49 (q40 c4) ∷
   rw⁻ 49 (q33 c4) ∷
   rw⁻ 48 (q34 c4) ∷
   rw⁻ 49 (q35 c4) ∷
   rw 50 (q36 c4) ∷
   rw⁻ 51 (q37 c4) ∷
   rw 52 (q36 c4) ∷
   rw⁻ 53 (q38 c4) ∷
   rw⁻ 54 (q39 c4) ∷
   rw 48 (q33 c4) ∷
   rw⁻ 49 (q41 c4) ∷
   rw 47 (q40 c4) ∷
   rw 50 (q4 c4) ∷
   rw 49 (q42 c4) ∷
   rw 50 (q2 c4) ∷
   rw 51 (q1 c4) ∷
   rw 52 (q2 c4) ∷
   rw 53 (q3 c4) ∷
   rw⁻ 49 (q4 c4) ∷
   rw 50 (q5 c4) ∷
   rw⁻ 48 (q6 c4) ∷
   rw⁻ 49 (q7 c4) ∷
   rw⁻ 49 (q8 c4) ∷
   rw 49 (q9 c4) ∷
   rw 53 (q10 c4) ∷
   rw 52 (q11 c4) ∷
   rw⁻ 53 (q12 c4) ∷
   rw 54 (q13 c4) ∷
   rw⁻ 55 (q12 c4) ∷
   rw⁻ 56 (q14 c4) ∷
   rw⁻ 52 (q10 c4) ∷
   rw⁻ 51 (q15 c4) ∷
   rw 51 (q10 c4) ∷
   rw 50 (q11 c4) ∷
   rw⁻ 51 (q12 c4) ∷
   rw 52 (q13 c4) ∷
   rw⁻ 53 (q12 c4) ∷
   rw⁻ 54 (q14 c4) ∷
   rw⁻ 50 (q10 c4) ∷
   rw⁻ 49 (q15 c4) ∷
   rw⁻ 50 (q9 c4) ∷
   rw 50 (q9 c4) ∷
   rw 54 (q10 c4) ∷
   rw 53 (q11 c4) ∷
   rw⁻ 54 (q12 c4) ∷
   rw 55 (q13 c4) ∷
   rw⁻ 56 (q12 c4) ∷
   rw⁻ 57 (q14 c4) ∷
   rw⁻ 53 (q10 c4) ∷
   rw⁻ 52 (q15 c4) ∷
   rw 52 (q10 c4) ∷
   rw 51 (q11 c4) ∷
   rw⁻ 52 (q12 c4) ∷
   rw 53 (q13 c4) ∷
   rw⁻ 54 (q12 c4) ∷
   rw⁻ 55 (q14 c4) ∷
   rw⁻ 51 (q10 c4) ∷
   rw⁻ 50 (q15 c4) ∷
   rw⁻ 51 (q9 c4) ∷
   rw 1 (q47 c4) ∷
   rw 3 (q48 c4) ∷
   rw 5 (q49 c4) ∷
   rw 15 (q50 c4) ∷
   rw 5 (q51 c4) ∷
   rw 6 (q48 c4) ∷
   rw 6 (q47 c4) ∷
   rw 8 (q48 c4) ∷
   rw 13 (q52 c4) ∷
   rw 14 (q50 c4) ∷
   rw 15 (q52 c4) ∷
   rw 16 (q52 c4) ∷ []) Eq.refl
