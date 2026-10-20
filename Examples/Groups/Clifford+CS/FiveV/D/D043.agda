{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D043 where

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
open import Examples.Groups.Clifford+CS.FiveV.D.D021 using (lem-box-perm-1324-at03243240 ; lem-box2-at0310243142)
open import Examples.Groups.Clifford+CS.FiveV.D.D026 using (lem-S2-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.FiveV.D.D027 using (lem-box-perm-4213-at03243240)
open import Examples.Groups.Clifford+CS.FiveV.D.D028 using (lem-box-perm-4132-at03243240)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CCZ134-CX02 ; lem-comm-TOFF304-CX12)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CCZ123-CX04 ; lem-comm-CCZ134-CSd02)
open import Examples.Groups.Clifford+CS.FiveV.D.R009 using (lem-comm-TOFF302-CS14 ; lem-comm-TOFF302-CSd14 ; lem-comm-TOFF302-CX14)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx3-1240 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx3-1420 ∷ []) (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx3-1420 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp 301 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Toff302 ∷ CS14 ∷ []) (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CX01 ∷ Toff302 ∷ []) (Toff302 ∷ CX01 ∷ []) (wl 1233 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Toff302 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CS04 ∷ Toff302 ∷ []) (Toff302 ∷ CS04 ∷ []) (wp 1041 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ []) (wp 272 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CS02⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS02⁻ ∷ []) (wl 792 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ134 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CSd02 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl 888 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (K2 ∷ Toff304 ∷ []) (Toff304 ∷ K2 ∷ []) (wp 1035 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CS24 ∷ Toff304 ∷ []) (Toff304 ∷ CS24 ∷ []) (wp 691 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Toff304 ∷ CX12 ∷ []) (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CS24⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS24⁻ ∷ []) (wp 1036 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CS14 ∷ Toff304 ∷ []) (Toff304 ∷ CS14 ∷ []) (wp 1037 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (K2⁻ ∷ Toff304 ∷ []) (Toff304 ∷ K2⁻ ∷ []) (wp 1038 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl 758 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ014 ∷ CCZ134 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ134 ∷ []) (wp 1039 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp 41 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ []) (wl 765 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ123 ∷ CX04 ∷ []) (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ123 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ123 ∷ []) (wl 764 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ123 ∷ CS01 ∷ []) (CS01 ∷ CCZ123 ∷ []) (wl 763 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ123 ∷ []) (wl 618 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ014 ∷ []) (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp 1040 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (K1 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ K1⁻ ∷ []) (Toff124 ∷ []) (wl 1313 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (K1 ∷ Toff302 ∷ []) (Toff302 ∷ K1 ∷ []) (wl 1252 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CS24 ∷ Toff302 ∷ []) (Toff302 ∷ CS24 ∷ []) (wp 1006 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Toff302 ∷ CX14 ∷ []) (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CS24⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS24⁻ ∷ []) (wp 1005 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CS12 ∷ Toff302 ∷ []) (Toff302 ∷ CS12 ∷ []) (wl 1190 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (K1⁻ ∷ Toff302 ∷ []) (Toff302 ∷ K1⁻ ∷ []) (wl 1312 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ134 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl 1314 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ024 ∷ CCZ234 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ234 ∷ []) (wp 1136 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp 296 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ134 ∷ CS24 ∷ []) (CS24 ∷ CCZ134 ∷ []) (wl 1220 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ134 ∷ CX02 ∷ []) (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ134 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ134 ∷ []) (wl 1221 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ134 ∷ CS04 ∷ []) (CS04 ∷ CCZ134 ∷ []) (wp 1003 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ134 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ134 ∷ []) (wl 960 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ024 ∷ []) (CCZ234 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp 1137 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ024 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ []) (wp 1138 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx3-1420 ∷ []) (Bx3-0412 ∷ []) (lem-box-perm-4213-at03243240 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx3-0412 ∷ Bx3-0412 ∷ []) [] (lem-box2-at0310243142 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (Toff302 ∷ Toff024 ∷ []) (wp 1025 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (Toff024 ∷ []) (wp 1026 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (K0 ∷ CCZ134 ∷ []) (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q50 : Ws → Eqn
  q50 c4 = eqn (K0⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl 1206 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Toff302 ∷ Toff324 ∷ []) (Toff324 ∷ Toff302 ∷ []) (wp 1007 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl 220 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Toff024 ∷ Toff324 ∷ Toff324 ∷ []) (Toff024 ∷ []) (wp 1008 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ []) (wl 1222 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CS01 ∷ Toff302 ∷ []) (Toff302 ∷ CS01 ∷ []) (wl 1223 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ134 ∷ CS01 ∷ []) (CS01 ∷ CCZ134 ∷ []) (wp 261 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CS01⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS01⁻ ∷ []) (wl 1224 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ134 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ134 ∷ []) (wp 1027 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1⁻ ∷ []) (Toff104 ∷ []) (wp 1132 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CCZ134 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp 1133 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ024 ∷ CCZ034 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ034 ∷ []) (wp 1134 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ034 ∷ []) (wp 103 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ024 ∷ []) (CCZ034 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp 1135 c4)

-- L-CCZ-0 part1: 500 steps
lem-L-CCZ-0-part1 : Ws → ⟪ (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CCZ123 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ
lem-L-CCZ-0-part1 c4 = derive (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CCZ123 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ [])
  (rw⁻ 27 (q1 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw 27 (q3 c4) ∷
   rw 31 (q4 c4) ∷
   rw 30 (q5 c4) ∷
   rw⁻ 31 (q6 c4) ∷
   rw 32 (q7 c4) ∷
   rw⁻ 33 (q6 c4) ∷
   rw⁻ 34 (q8 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw 29 (q4 c4) ∷
   rw 28 (q5 c4) ∷
   rw⁻ 29 (q6 c4) ∷
   rw 30 (q7 c4) ∷
   rw⁻ 31 (q6 c4) ∷
   rw⁻ 32 (q8 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 27 (q9 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw 28 (q3 c4) ∷
   rw⁻ 31 (q10 c4) ∷
   rw 30 (q11 c4) ∷
   rw⁻ 29 (q10 c4) ∷
   rw 28 (q11 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw 29 (q2 c4) ∷
   rw 29 (q1 c4) ∷
   rw⁻ 33 (q12 c4) ∷
   rw⁻ 32 (q13 c4) ∷
   rw⁻ 33 (q14 c4) ∷
   rw 34 (q15 c4) ∷
   rw⁻ 35 (q16 c4) ∷
   rw 36 (q15 c4) ∷
   rw⁻ 37 (q17 c4) ∷
   rw⁻ 38 (q18 c4) ∷
   rw 32 (q12 c4) ∷
   rw 31 (q19 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 30 (q13 c4) ∷
   rw⁻ 31 (q14 c4) ∷
   rw 32 (q15 c4) ∷
   rw⁻ 33 (q16 c4) ∷
   rw 34 (q15 c4) ∷
   rw⁻ 35 (q17 c4) ∷
   rw⁻ 36 (q18 c4) ∷
   rw 30 (q12 c4) ∷
   rw⁻ 31 (q20 c4) ∷
   rw 29 (q19 c4) ∷
   rw 32 (q21 c4) ∷
   rw 31 (q22 c4) ∷
   rw 32 (q23 c4) ∷
   rw 33 (q24 c4) ∷
   rw 34 (q23 c4) ∷
   rw 35 (q25 c4) ∷
   rw⁻ 31 (q21 c4) ∷
   rw 32 (q26 c4) ∷
   rw⁻ 30 (q27 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw 31 (q3 c4) ∷
   rw 35 (q4 c4) ∷
   rw 34 (q5 c4) ∷
   rw⁻ 35 (q6 c4) ∷
   rw 36 (q7 c4) ∷
   rw⁻ 37 (q6 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 33 (q9 c4) ∷
   rw 33 (q4 c4) ∷
   rw 32 (q5 c4) ∷
   rw⁻ 33 (q6 c4) ∷
   rw 34 (q7 c4) ∷
   rw⁻ 35 (q6 c4) ∷
   rw⁻ 36 (q8 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 31 (q9 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   rw 32 (q3 c4) ∷
   rw⁻ 36 (q28 c4) ∷
   rw⁻ 35 (q29 c4) ∷
   rw⁻ 36 (q30 c4) ∷
   rw 37 (q31 c4) ∷
   rw⁻ 38 (q32 c4) ∷
   rw 39 (q31 c4) ∷
   rw⁻ 40 (q33 c4) ∷
   rw⁻ 41 (q34 c4) ∷
   rw 35 (q28 c4) ∷
   rw 34 (q35 c4) ∷
   rw⁻ 34 (q28 c4) ∷
   rw⁻ 33 (q29 c4) ∷
   rw⁻ 34 (q30 c4) ∷
   rw 35 (q31 c4) ∷
   rw⁻ 36 (q32 c4) ∷
   rw 37 (q31 c4) ∷
   rw⁻ 38 (q33 c4) ∷
   rw⁻ 39 (q34 c4) ∷
   rw 33 (q28 c4) ∷
   rw⁻ 34 (q36 c4) ∷
   rw 32 (q35 c4) ∷
   rw 35 (q37 c4) ∷
   rw 34 (q38 c4) ∷
   rw 35 (q39 c4) ∷
   rw 36 (q40 c4) ∷
   rw 37 (q39 c4) ∷
   rw 38 (q41 c4) ∷
   rw⁻ 34 (q37 c4) ∷
   rw 35 (q42 c4) ∷
   rw⁻ 33 (q43 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw 34 (q3 c4) ∷
   rw⁻ 37 (q44 c4) ∷
   rw 37 (q37 c4) ∷
   rw 36 (q38 c4) ∷
   rw 37 (q39 c4) ∷
   rw 38 (q40 c4) ∷
   rw 39 (q39 c4) ∷
   rw 40 (q41 c4) ∷
   rw⁻ 36 (q37 c4) ∷
   rw⁻ 35 (q44 c4) ∷
   rw 35 (q37 c4) ∷
   rw 34 (q38 c4) ∷
   rw 35 (q39 c4) ∷
   rw 36 (q40 c4) ∷
   rw 37 (q39 c4) ∷
   rw 38 (q41 c4) ∷
   rw⁻ 34 (q37 c4) ∷
   rw⁻ 35 (q3 c4) ∷
   rw 35 (q2 c4) ∷
   rw 35 (q1 c4) ∷
   rw⁻ 39 (q12 c4) ∷
   rw⁻ 38 (q13 c4) ∷
   rw⁻ 39 (q14 c4) ∷
   rw 40 (q15 c4) ∷
   rw⁻ 41 (q16 c4) ∷
   rw 42 (q15 c4) ∷
   rw⁻ 43 (q17 c4) ∷
   rw⁻ 44 (q18 c4) ∷
   rw 38 (q12 c4) ∷
   rw 37 (q19 c4) ∷
   rw⁻ 37 (q12 c4) ∷
   rw⁻ 36 (q13 c4) ∷
   rw⁻ 37 (q14 c4) ∷
   rw 38 (q15 c4) ∷
   rw⁻ 39 (q16 c4) ∷
   rw 40 (q15 c4) ∷
   rw⁻ 41 (q17 c4) ∷
   rw⁻ 42 (q18 c4) ∷
   rw 36 (q12 c4) ∷
   rw⁻ 37 (q20 c4) ∷
   rw 35 (q19 c4) ∷
   rw 38 (q21 c4) ∷
   rw 37 (q22 c4) ∷
   rw 38 (q23 c4) ∷
   rw 39 (q24 c4) ∷
   rw 40 (q23 c4) ∷
   rw 41 (q25 c4) ∷
   rw⁻ 37 (q21 c4) ∷
   rw 38 (q26 c4) ∷
   rw⁻ 36 (q27 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 37 (q2 c4) ∷
   rw 37 (q3 c4) ∷
   rw 41 (q4 c4) ∷
   rw 40 (q5 c4) ∷
   rw⁻ 41 (q6 c4) ∷
   rw 42 (q7 c4) ∷
   rw⁻ 43 (q6 c4) ∷
   rw⁻ 44 (q8 c4) ∷
   rw⁻ 40 (q4 c4) ∷
   rw⁻ 39 (q9 c4) ∷
   rw 39 (q4 c4) ∷
   rw 38 (q5 c4) ∷
   rw⁻ 39 (q6 c4) ∷
   rw 40 (q7 c4) ∷
   rw⁻ 41 (q6 c4) ∷
   rw⁻ 42 (q8 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw⁻ 37 (q9 c4) ∷
   rw⁻ 38 (q3 c4) ∷
   rw 38 (q45 c4) ∷
   rw 38 (q46 c4) ∷
   rw 0 (q3 c4) ∷
   rw⁻ 3 (q47 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw⁻ 2 (q49 c4) ∷
   rw 3 (q38 c4) ∷
   rw 4 (q39 c4) ∷
   rw 5 (q40 c4) ∷
   rw 6 (q39 c4) ∷
   rw 7 (q41 c4) ∷
   rw⁻ 8 (q50 c4) ∷
   rw 2 (q48 c4) ∷
   rw 3 (q51 c4) ∷
   rw⁻ 1 (q47 c4) ∷
   rw 3 (q52 c4) ∷
   rw 5 (q53 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw 5 (q31 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   rw 7 (q31 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw 1 (q54 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   rw⁻ 0 (q49 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 3 (q40 c4) ∷
   rw 4 (q39 c4) ∷
   rw 5 (q41 c4) ∷
   rw⁻ 6 (q50 c4) ∷
   rw 0 (q48 c4) ∷
   rw⁻ 1 (q55 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 5 (q56 c4) ∷
   rw 4 (q57 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 6 (q47 c4) ∷
   rw⁻ 6 (q48 c4) ∷
   rw⁻ 5 (q49 c4) ∷
   rw 6 (q38 c4) ∷
   rw 7 (q39 c4) ∷
   rw 8 (q40 c4) ∷
   rw 9 (q39 c4) ∷
   rw 10 (q41 c4) ∷
   rw⁻ 11 (q50 c4) ∷
   rw 5 (q48 c4) ∷
   rw 6 (q51 c4) ∷
   rw⁻ 4 (q47 c4) ∷
   rw 6 (q52 c4) ∷
   rw 8 (q53 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw 8 (q31 c4) ∷
   rw⁻ 9 (q32 c4) ∷
   rw 10 (q31 c4) ∷
   rw⁻ 11 (q33 c4) ∷
   rw⁻ 7 (q53 c4) ∷
   rw 4 (q54 c4) ∷
   rw⁻ 4 (q48 c4) ∷
   rw⁻ 3 (q49 c4) ∷
   rw 4 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 7 (q39 c4) ∷
   rw 8 (q41 c4) ∷
   rw⁻ 9 (q50 c4) ∷
   rw 3 (q48 c4) ∷
   rw⁻ 4 (q55 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 8 (q58 c4) ∷
   rw 7 (q59 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 5 (q59 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 10 (q60 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 10 (q5 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw 12 (q7 c4) ∷
   rw⁻ 13 (q6 c4) ∷
   rw⁻ 14 (q8 c4) ∷
   rw⁻ 15 (q34 c4) ∷
   rw 9 (q60 c4) ∷
   rw 8 (q61 c4) ∷
   rw⁻ 8 (q60 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 8 (q5 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   rw 10 (q7 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw⁻ 12 (q8 c4) ∷
   rw⁻ 13 (q34 c4) ∷
   rw 7 (q60 c4) ∷
   rw⁻ 8 (q62 c4) ∷
   rw 6 (q61 c4) ∷
   rw 9 (q37 c4) ∷
   rw 8 (q38 c4) ∷
   rw 9 (q39 c4) ∷
   rw 10 (q40 c4) ∷
   rw 11 (q39 c4) ∷
   rw 12 (q41 c4) ∷
   rw⁻ 8 (q37 c4) ∷
   rw⁻ 9 (q63 c4) ∷
   rw⁻ 7 (q64 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   rw 8 (q3 c4) ∷
   rw 12 (q53 c4) ∷
   rw⁻ 11 (q30 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 13 (q32 c4) ∷
   rw 14 (q31 c4) ∷
   rw⁻ 15 (q33 c4) ∷
   rw⁻ 11 (q53 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   rw 10 (q53 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw 10 (q31 c4) ∷
   rw⁻ 11 (q32 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 13 (q33 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   rw⁻ 8 (q55 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 12 (q47 c4) ∷
   rw⁻ 12 (q48 c4) ∷
   rw⁻ 11 (q49 c4) ∷
   rw 12 (q38 c4) ∷
   rw 13 (q39 c4) ∷
   rw 14 (q40 c4) ∷
   rw 15 (q39 c4) ∷
   rw 16 (q41 c4) ∷
   rw⁻ 17 (q50 c4) ∷
   rw 11 (q48 c4) ∷
   rw 12 (q51 c4) ∷
   rw⁻ 10 (q47 c4) ∷
   rw 12 (q52 c4) ∷
   rw 14 (q53 c4) ∷
   rw⁻ 13 (q30 c4) ∷
   rw 14 (q31 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw 16 (q31 c4) ∷
   rw⁻ 17 (q33 c4) ∷
   rw⁻ 13 (q53 c4) ∷
   rw 10 (q54 c4) ∷
   rw⁻ 10 (q48 c4) ∷
   rw⁻ 9 (q49 c4) ∷
   rw 10 (q38 c4) ∷
   rw 11 (q39 c4) ∷
   rw 12 (q40 c4) ∷
   rw 13 (q39 c4) ∷
   rw 14 (q41 c4) ∷
   rw⁻ 15 (q50 c4) ∷
   rw 9 (q48 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw 11 (q3 c4) ∷
   rw 15 (q53 c4) ∷
   rw⁻ 14 (q30 c4) ∷
   rw 15 (q31 c4) ∷
   rw⁻ 16 (q32 c4) ∷
   rw 17 (q31 c4) ∷
   rw⁻ 18 (q33 c4) ∷
   rw⁻ 14 (q53 c4) ∷
   rw⁻ 13 (q55 c4) ∷
   rw 13 (q53 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw 13 (q31 c4) ∷
   rw⁻ 14 (q32 c4) ∷
   rw 15 (q31 c4) ∷
   rw⁻ 16 (q33 c4) ∷
   rw⁻ 12 (q53 c4) ∷
   rw⁻ 11 (q55 c4) ∷
   rw⁻ 12 (q3 c4) ∷
   rw 12 (q3 c4) ∷
   rw⁻ 15 (q56 c4) ∷
   rw 14 (q57 c4) ∷
   rw⁻ 13 (q56 c4) ∷
   rw 12 (q57 c4) ∷
   rw⁻ 13 (q3 c4) ∷
   rw 13 (q3 c4) ∷
   rw⁻ 16 (q47 c4) ∷
   rw⁻ 16 (q48 c4) ∷
   rw⁻ 15 (q49 c4) ∷
   rw 16 (q38 c4) ∷
   rw 17 (q39 c4) ∷
   rw 18 (q40 c4) ∷
   rw 19 (q39 c4) ∷
   rw 20 (q41 c4) ∷
   rw⁻ 21 (q50 c4) ∷
   rw 15 (q48 c4) ∷
   rw 16 (q51 c4) ∷
   rw⁻ 14 (q47 c4) ∷
   rw 16 (q52 c4) ∷
   rw 18 (q53 c4) ∷
   rw⁻ 17 (q30 c4) ∷
   rw 18 (q31 c4) ∷
   rw⁻ 19 (q32 c4) ∷
   rw 20 (q31 c4) ∷
   rw⁻ 21 (q33 c4) ∷
   rw⁻ 17 (q53 c4) ∷
   rw 14 (q54 c4) ∷
   rw⁻ 14 (q48 c4) ∷
   rw⁻ 13 (q49 c4) ∷
   rw 14 (q38 c4) ∷
   rw 15 (q39 c4) ∷
   rw 16 (q40 c4) ∷
   rw 17 (q39 c4) ∷
   rw 18 (q41 c4) ∷
   rw⁻ 19 (q50 c4) ∷
   rw 13 (q48 c4) ∷
   rw⁻ 14 (q55 c4) ∷
   rw⁻ 15 (q3 c4) ∷
   rw 15 (q3 c4) ∷
   rw 19 (q53 c4) ∷
   rw⁻ 18 (q30 c4) ∷
   rw 19 (q31 c4) ∷
   rw⁻ 20 (q32 c4) ∷
   rw 21 (q31 c4) ∷
   rw⁻ 22 (q33 c4) ∷
   rw⁻ 18 (q53 c4) ∷
   rw⁻ 17 (q55 c4) ∷
   rw 17 (q53 c4) ∷
   rw⁻ 16 (q30 c4) ∷
   rw 17 (q31 c4) ∷
   rw⁻ 18 (q32 c4) ∷
   rw 19 (q31 c4) ∷
   rw⁻ 20 (q33 c4) ∷
   rw⁻ 16 (q53 c4) ∷
   rw⁻ 15 (q55 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   rw 16 (q3 c4) ∷
   rw⁻ 19 (q58 c4) ∷
   rw 18 (q59 c4) ∷
   rw⁻ 17 (q58 c4) ∷
   rw 16 (q59 c4) ∷
   rw⁻ 17 (q3 c4) ∷
   rw 17 (q3 c4) ∷
   rw⁻ 21 (q60 c4) ∷
   rw⁻ 20 (q29 c4) ∷
   rw 21 (q5 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw 23 (q7 c4) ∷
   rw⁻ 24 (q6 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw 20 (q60 c4) ∷
   rw 19 (q61 c4) ∷
   rw⁻ 19 (q60 c4) ∷
   rw⁻ 18 (q29 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 20 (q6 c4) ∷
   rw 21 (q7 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 24 (q34 c4) ∷
   rw 18 (q60 c4) ∷
   rw⁻ 19 (q62 c4) ∷
   rw 17 (q61 c4) ∷
   rw 20 (q37 c4) ∷
   rw 19 (q38 c4) ∷
   rw 20 (q39 c4) ∷
   rw 21 (q40 c4) ∷
   rw 22 (q39 c4) ∷
   rw 23 (q41 c4) ∷
   rw⁻ 19 (q37 c4) ∷
   rw⁻ 20 (q63 c4) ∷
   rw⁻ 18 (q64 c4) ∷
   rw⁻ 19 (q3 c4) ∷
   rw 19 (q3 c4) ∷
   rw⁻ 22 (q44 c4) ∷
   rw 22 (q37 c4) ∷
   rw 21 (q38 c4) ∷
   rw 22 (q39 c4) ∷
   rw 23 (q40 c4) ∷
   rw 24 (q39 c4) ∷
   rw 25 (q41 c4) ∷
   rw⁻ 21 (q37 c4) ∷
   rw⁻ 20 (q44 c4) ∷
   rw 20 (q37 c4) ∷
   rw 19 (q38 c4) ∷
   rw 20 (q39 c4) ∷
   rw 21 (q40 c4) ∷
   rw 22 (q39 c4) ∷
   rw 23 (q41 c4) ∷
   rw⁻ 19 (q37 c4) ∷
   rw⁻ 20 (q3 c4) ∷
   rw 20 (q2 c4) ∷
   rw 20 (q1 c4) ∷
   rw⁻ 24 (q12 c4) ∷
   rw⁻ 23 (q13 c4) ∷
   rw⁻ 24 (q14 c4) ∷
   rw 25 (q15 c4) ∷
   rw⁻ 26 (q16 c4) ∷
   rw 27 (q15 c4) ∷
   rw⁻ 28 (q17 c4) ∷
   rw⁻ 29 (q18 c4) ∷
   rw 23 (q12 c4) ∷
   rw 22 (q19 c4) ∷
   rw⁻ 22 (q12 c4) ∷
   rw⁻ 21 (q13 c4) ∷
   rw⁻ 22 (q14 c4) ∷
   rw 23 (q15 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw 25 (q15 c4) ∷
   rw⁻ 26 (q17 c4) ∷
   rw⁻ 27 (q18 c4) ∷
   rw 21 (q12 c4) ∷
   rw⁻ 22 (q20 c4) ∷
   rw 20 (q19 c4) ∷
   rw 23 (q21 c4) ∷
   rw 22 (q22 c4) ∷
   rw 23 (q23 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ014 ∷ CS02 ∷ Toff214 ∷ []) (CS02 ∷ Toff214 ∷ CCZ014 ∷ []) (wp 1030 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp 135 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) [] (wp 1140 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (Bx3-1420 ∷ []) (Bx3-0124 ∷ []) (lem-box-perm-4132-at03243240 c4)

-- L-CCZ-0 part3: 8 steps
lem-L-CCZ-0-part3 : Ws → ⟪ (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-L-CCZ-0-part3 c4 = derive (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ []) (Bx3-0124 ∷ [])
  (rw 16 (q65 c4) ∷
   rw 18 (q66 c4) ∷
   rw 18 (q66 c4) ∷
   rw 20 (q66 c4) ∷
   rw 22 (q67 c4) ∷
   rw 24 (q66 c4) ∷
   rw 0 (q68 c4) ∷
   rw 0 (q69 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ []) (wl 1315 (lit c4))

-- L-CX01-2: 2 steps
lem-L-CX01-2 : Ws → ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ []) ⟫ʷ
lem-L-CX01-2 c4 = derive (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ [])
  (rw 1 (q70 c4) ∷
   rw 0 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Toff234 ∷ []) (wl 1316 (lit c4))

-- L-CX10-2: 2 steps
lem-L-CX10-2 : Ws → ⟪ (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ []) ⟫ʷ
lem-L-CX10-2 c4 = derive (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (Toff234 ∷ [])
  (rw 1 (q70 c4) ∷
   rw 0 (q72 c4) ∷ []) Eq.refl
