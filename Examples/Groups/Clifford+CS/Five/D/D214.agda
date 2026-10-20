{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D214 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0220 ; wl0263 ; wl0499 ; wl0501 ; wl0618 ; wl0758 ; wl0763 ; wl0764 ; wl0765 ; wl0778 ; wl0779 ; wl0780 ; wl0792 ; wl0801 ; wl0861 ; wl0888 ; wl1190 ; wl1206 ; wl1220 ; wl1221 ; wl1222 ; wl1223 ; wl1224 ; wl1225 ; wl1226 ; wl1233 ; wp0002 ; wp0003 ; wp0041 ; wp0106 ; wp0107 ; wp0108 ; wp0124 ; wp0161 ; wp0261 ; wp0272 ; wp0301 ; wp0691 ; wp0700 ; wp0701 ; wp0716 ; wp1003 ; wp1005 ; wp1006 ; wp1007 ; wp1008 ; wp1025 ; wp1026 ; wp1027 ; wp1035 ; wp1036 ; wp1037 ; wp1038 ; wp1039 ; wp1040 ; wp1041 ; wp1042 ; wp1043 ; wl0341 ; wl1249 ; wl1269 ; wp0167 ; wp1110 ; wp1111 ; wp1112 ; wp1119 ; wp1120)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0310243142 ; lem-box-cP-at03243240 ; lem-box-cP-at033440)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-perm-1324-at03243240 ; lem-box-perm-1324-at033440 ; lem-box2-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-CKc-box-at0312203441 ; lem-CKc-box-at033440 ; lem-S2-SBOX⟨3·0·41·2⟩ ; lem-S2-SBOX⟨3·1·42·0⟩ ; lem-box-perm-3421-at03243240 ; lem-box-perm-4213-at03243240 ; lem-box-perm-4312-at0312203441)
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-F0-at01143043 ; lem-F0-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D204 using (lem-nf-comm-CSu-CSat0)
open import Examples.Groups.Clifford+CS.Five.D.D205 using (lem-nf-rel-266at0 ; lem-nf-rel-267at0)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ034-CX12 ; lem-comm-CCZ134-CS02 ; lem-comm-CCZ134-CX02 ; lem-comm-TOFF304-CX12 ; lem-comm-TOFF312-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CCZ123-CX04 ; lem-comm-CCZ134-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF302-CS14 ; lem-comm-TOFF302-CSd14 ; lem-comm-TOFF302-CX14)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb0-1-42-3 ∷ []) (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (Toff312 ∷ Toff214 ∷ []) (wl1225 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl0888 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ034 ∷ K2 ∷ []) (K2 ∷ CCZ034 ∷ []) (wp0701 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ []) (wp0108 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ034 ∷ CX12 ∷ []) (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ034 ∷ CS14 ∷ []) (CS14 ∷ CCZ034 ∷ []) (wp0106 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ034 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ034 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Toff312 ∷ Toff314 ∷ []) (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Toff312 ∷ CX04 ∷ []) (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS14⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Toff214 ∷ Toff314 ∷ Toff314 ∷ []) (Toff214 ∷ []) (wl0780 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ014 ∷ []) (wp0124 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS02 ∷ Toff312 ∷ []) (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) (wp0003 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS02⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS02⁻ ∷ []) (wl1226 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ034 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx3-1420 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (Toff302 ∷ Toff024 ∷ []) (wp1025 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (Toff024 ∷ []) (wp1026 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (K0 ∷ CCZ134 ∷ []) (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ134 ∷ CS24 ∷ []) (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ134 ∷ CX02 ∷ []) (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ134 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ134 ∷ CS04 ∷ []) (CS04 ∷ CCZ134 ∷ []) (wp1003 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (K0⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (Toff302 ∷ Toff324 ∷ []) (Toff324 ∷ Toff302 ∷ []) (wp1007 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS24 ∷ Toff302 ∷ []) (Toff302 ∷ CS24 ∷ []) (wp1006 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Toff302 ∷ CX14 ∷ []) (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS24⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS24⁻ ∷ []) (wp1005 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS12 ∷ Toff302 ∷ []) (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (Toff024 ∷ Toff324 ∷ Toff324 ∷ []) (Toff024 ∷ []) (wp1008 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ []) (wl1222 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS01 ∷ Toff302 ∷ []) (Toff302 ∷ CS01 ∷ []) (wl1223 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ134 ∷ CS01 ∷ []) (CS01 ∷ CCZ134 ∷ []) (wp0261 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CS01⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS01⁻ ∷ []) (wl1224 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ134 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx3-1420 ∷ []) (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (Bx3-1240 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (K2 ∷ Toff304 ∷ []) (Toff304 ∷ K2 ∷ []) (wp1035 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CS24 ∷ Toff304 ∷ []) (Toff304 ∷ CS24 ∷ []) (wp0691 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (Toff304 ∷ CX12 ∷ []) (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CS24⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS24⁻ ∷ []) (wp1036 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CS14 ∷ Toff304 ∷ []) (Toff304 ∷ CS14 ∷ []) (wp1037 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (K2⁻ ∷ Toff304 ∷ []) (Toff304 ∷ K2⁻ ∷ []) (wp1038 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ014 ∷ CCZ134 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ134 ∷ []) (wp1039 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ []) (wl0765 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ123 ∷ CX04 ∷ []) (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ123 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ123 ∷ []) (wl0764 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ123 ∷ CS01 ∷ []) (CS01 ∷ CCZ123 ∷ []) (wl0763 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ014 ∷ []) (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp1040 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Toff302 ∷ CS14 ∷ []) (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (CX01 ∷ Toff302 ∷ []) (Toff302 ∷ CX01 ∷ []) (wl1233 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (Toff302 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CS04 ∷ Toff302 ∷ []) (Toff302 ∷ CS04 ∷ []) (wp1041 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (CS02 ∷ Toff302 ∷ []) (Toff302 ∷ CS02 ∷ []) (wl0801 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (CCZ134 ∷ CS02 ∷ []) (CS02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CS02 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CS02⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS02⁻ ∷ []) (wl0792 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (CCZ134 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CSd02 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (Bx3-1420 ∷ []) (Bx3-0412 ∷ []) (lem-box-perm-4213-at03243240 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (Bx3-0412 ∷ Bx3-0412 ∷ []) [] (lem-box2-at0310243142 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ124 ∷ CS01 ∷ Toff024 ∷ []) (CS01 ∷ Toff024 ∷ CCZ124 ∷ []) (wp1042 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl0263 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp0161 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (wp1043 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (lem-nf-comm-CSu-CSat0 c4)

-- F1-comm-CSu-CS@0: 288 steps
lem-F1-comm-CSu-CSat0 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CSu-CSat0 c4 = derive (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   re 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 2 1 (CS01 ∷ []) ∷
   re 4 1 (CS01⁻ ∷ []) ∷
   re 5 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 7 1 (CS02 ∷ []) ∷
   re 9 1 (CS02⁻ ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q8 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q12 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 8 (q13 c4) ∷
   rw 10 (q14 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 10 (q16 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   rw 12 (q16 c4) ∷
   rw⁻ 13 (q18 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw 6 (q19 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 10 (q21 c4) ∷
   rw 9 (q22 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw 10 (q6 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q8 c4) ∷
   rw 15 (q10 c4) ∷
   rw 16 (q11 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q12 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 11 (q13 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 13 (q16 c4) ∷
   rw⁻ 14 (q17 c4) ∷
   rw 15 (q16 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw 9 (q19 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q10 c4) ∷
   rw 14 (q11 c4) ∷
   rw 8 (q5 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 13 (q23 c4) ∷
   rw 12 (q24 c4) ∷
   rw⁻ 11 (q23 c4) ∷
   rw 10 (q24 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw 0 (q25 c4) ∷
   rw⁻ 3 (q26 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw 3 (q29 c4) ∷
   rw 4 (q30 c4) ∷
   rw 5 (q31 c4) ∷
   rw 6 (q30 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   rw 2 (q27 c4) ∷
   rw 3 (q34 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw 3 (q35 c4) ∷
   rw 5 (q36 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 7 (q38 c4) ∷
   rw⁻ 8 (q40 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 1 (q41 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw⁻ 0 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q31 c4) ∷
   rw 4 (q30 c4) ∷
   rw 5 (q32 c4) ∷
   rw⁻ 6 (q33 c4) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw⁻ 2 (q25 c4) ∷
   rw 2 (q25 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   rw 4 (q44 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   rw 2 (q44 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   rw 3 (q25 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   rw 6 (q29 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q31 c4) ∷
   rw 9 (q30 c4) ∷
   rw 10 (q32 c4) ∷
   rw⁻ 11 (q33 c4) ∷
   rw 5 (q27 c4) ∷
   rw 6 (q34 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 6 (q35 c4) ∷
   rw 8 (q36 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw 8 (q38 c4) ∷
   rw⁻ 9 (q39 c4) ∷
   rw 10 (q38 c4) ∷
   rw⁻ 11 (q40 c4) ∷
   rw⁻ 7 (q36 c4) ∷
   rw 4 (q41 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   rw 4 (q29 c4) ∷
   rw 5 (q30 c4) ∷
   rw 6 (q31 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q32 c4) ∷
   rw⁻ 9 (q33 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   rw 5 (q25 c4) ∷
   rw⁻ 8 (q45 c4) ∷
   rw 7 (q46 c4) ∷
   rw⁻ 6 (q45 c4) ∷
   rw 5 (q46 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw 6 (q47 c4) ∷
   rw 6 (q48 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 9 (q49 c4) ∷
   rw⁻ 10 (q50 c4) ∷
   rw 11 (q51 c4) ∷
   rw⁻ 12 (q52 c4) ∷
   rw 13 (q51 c4) ∷
   rw⁻ 14 (q53 c4) ∷
   rw⁻ 15 (q54 c4) ∷
   rw 9 (q5 c4) ∷
   rw 8 (q55 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 7 (q49 c4) ∷
   rw⁻ 8 (q50 c4) ∷
   rw 9 (q51 c4) ∷
   rw⁻ 10 (q52 c4) ∷
   rw 11 (q51 c4) ∷
   rw⁻ 12 (q53 c4) ∷
   rw⁻ 13 (q54 c4) ∷
   rw 7 (q5 c4) ∷
   rw⁻ 8 (q56 c4) ∷
   rw 6 (q55 c4) ∷
   rw 9 (q14 c4) ∷
   rw 8 (q57 c4) ∷
   rw 9 (q58 c4) ∷
   rw 10 (q59 c4) ∷
   rw 11 (q58 c4) ∷
   rw 12 (q60 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q61 c4) ∷
   rw⁻ 7 (q62 c4) ∷
   rw⁻ 8 (q48 c4) ∷
   rw⁻ 8 (q47 c4) ∷
   rw 8 (q25 c4) ∷
   rw 12 (q63 c4) ∷
   rw 11 (q64 c4) ∷
   rw⁻ 12 (q65 c4) ∷
   rw 13 (q66 c4) ∷
   rw⁻ 14 (q65 c4) ∷
   rw⁻ 15 (q67 c4) ∷
   rw⁻ 11 (q63 c4) ∷
   rw⁻ 10 (q68 c4) ∷
   rw 10 (q63 c4) ∷
   rw 9 (q64 c4) ∷
   rw⁻ 10 (q65 c4) ∷
   rw 11 (q66 c4) ∷
   rw⁻ 12 (q65 c4) ∷
   rw⁻ 13 (q67 c4) ∷
   rw⁻ 9 (q63 c4) ∷
   rw⁻ 8 (q68 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw 9 (q25 c4) ∷
   rw⁻ 12 (q69 c4) ∷
   rw 11 (q70 c4) ∷
   rw⁻ 10 (q69 c4) ∷
   rw 9 (q70 c4) ∷
   rw⁻ 10 (q25 c4) ∷
   rw 10 (q47 c4) ∷
   rw 10 (q48 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 13 (q49 c4) ∷
   rw⁻ 14 (q50 c4) ∷
   rw 15 (q51 c4) ∷
   rw⁻ 16 (q52 c4) ∷
   rw 17 (q51 c4) ∷
   rw⁻ 18 (q53 c4) ∷
   rw⁻ 19 (q54 c4) ∷
   rw 13 (q5 c4) ∷
   rw 12 (q55 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw⁻ 11 (q49 c4) ∷
   rw⁻ 12 (q50 c4) ∷
   rw 13 (q51 c4) ∷
   rw⁻ 14 (q52 c4) ∷
   rw 15 (q51 c4) ∷
   rw⁻ 16 (q53 c4) ∷
   rw⁻ 17 (q54 c4) ∷
   rw 11 (q5 c4) ∷
   rw⁻ 12 (q56 c4) ∷
   rw 10 (q55 c4) ∷
   rw 13 (q14 c4) ∷
   rw 12 (q57 c4) ∷
   rw 13 (q58 c4) ∷
   rw 14 (q59 c4) ∷
   rw 15 (q58 c4) ∷
   rw 16 (q60 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw 13 (q61 c4) ∷
   rw⁻ 11 (q62 c4) ∷
   rw⁻ 12 (q48 c4) ∷
   rw⁻ 12 (q47 c4) ∷
   rw 12 (q25 c4) ∷
   rw 16 (q63 c4) ∷
   rw 15 (q64 c4) ∷
   rw⁻ 16 (q65 c4) ∷
   rw 17 (q66 c4) ∷
   rw⁻ 18 (q65 c4) ∷
   rw⁻ 19 (q67 c4) ∷
   rw⁻ 15 (q63 c4) ∷
   rw⁻ 14 (q68 c4) ∷
   rw 14 (q63 c4) ∷
   rw 13 (q64 c4) ∷
   rw⁻ 14 (q65 c4) ∷
   rw 15 (q66 c4) ∷
   rw⁻ 16 (q65 c4) ∷
   rw⁻ 17 (q67 c4) ∷
   rw⁻ 13 (q63 c4) ∷
   rw⁻ 12 (q68 c4) ∷
   rw⁻ 13 (q25 c4) ∷
   rw 13 (q25 c4) ∷
   rw⁻ 16 (q71 c4) ∷
   rw 15 (q72 c4) ∷
   rw⁻ 14 (q71 c4) ∷
   rw 13 (q72 c4) ∷
   rw⁻ 14 (q25 c4) ∷
   rw 14 (q73 c4) ∷
   rw 14 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw 3 (q76 c4) ∷
   rw 5 (q77 c4) ∷
   rw 7 (q77 c4) ∷
   rw 0 (q78 c4) ∷
   rw⁻ 0 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ []) (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ []) (wp1110 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (Bx3-1420 ∷ []) (Bx3-2041 ∷ []) (lem-box-perm-3421-at03243240 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (Bx3-2041 ∷ CK41 ∷ []) (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ []) (lem-CKc-box-at0312203441 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (Bx3-2041 ∷ []) (Bx3-1420 ∷ []) (lem-box-perm-4312-at0312203441 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (S4 ∷ Toff302 ∷ []) (Toff302 ∷ S4 ∷ []) (wp1111 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ134 ∷ S4 ∷ []) (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (Bx3-1240 ∷ CK40 ∷ []) (CCZ012 ∷ CK40 ∷ CCZ012 ∷ Bx3-1240 ∷ []) (lem-CKc-box-at033440 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (Bx3-1240 ∷ []) (Bx3-1420 ∷ []) (lem-box-perm-1324-at033440 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ012 ∷ []) (wp0167 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl0341 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (CCZ012 ∷ S4 ∷ []) (S4 ∷ CCZ012 ∷ []) (wl1269 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (Toff014 ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ CCZ012 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ []) (wp1112 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (lem-nf-rel-266at0 c4)

-- F1-rel-266@0: 166 steps
lem-F1-rel-266at0 : Ws → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266at0 c4 = derive (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ [])
  (rw 1 (q2 c4) ∷
   rw 2 (q2 c4) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q2 c4) ∷
   rw 10 (q1 c4) ∷
   rw 12 (q2 c4) ∷
   rw 13 (q2 c4) ∷
   rw 17 (q2 c4) ∷
   rw 18 (q2 c4) ∷
   rw 1 (q80 c4) ∷
   rw 5 (q80 c4) ∷
   rw 10 (q80 c4) ∷
   rw 14 (q80 c4) ∷
   re 8 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 10 1 (CS01 ∷ []) ∷
   re 12 1 (CS01⁻ ∷ []) ∷
   rw 0 (q81 c4) ∷
   rw 2 (q25 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 5 (q29 c4) ∷
   rw 6 (q30 c4) ∷
   rw 7 (q31 c4) ∷
   rw 8 (q30 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 10 (q33 c4) ∷
   rw 4 (q27 c4) ∷
   rw 5 (q34 c4) ∷
   rw⁻ 3 (q26 c4) ∷
   rw 5 (q35 c4) ∷
   rw 7 (q36 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   rw 7 (q38 c4) ∷
   rw⁻ 8 (q39 c4) ∷
   rw 9 (q38 c4) ∷
   rw⁻ 10 (q40 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw 3 (q29 c4) ∷
   rw 4 (q30 c4) ∷
   rw 5 (q31 c4) ∷
   rw 6 (q30 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   rw 2 (q27 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   rw 4 (q25 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   rw 6 (q44 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   rw 4 (q44 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   rw 5 (q25 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw⁻ 7 (q28 c4) ∷
   rw 8 (q29 c4) ∷
   rw 9 (q30 c4) ∷
   rw 10 (q31 c4) ∷
   rw 11 (q30 c4) ∷
   rw 12 (q32 c4) ∷
   rw⁻ 13 (q33 c4) ∷
   rw 7 (q27 c4) ∷
   rw 8 (q34 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw 8 (q35 c4) ∷
   rw 10 (q36 c4) ∷
   rw⁻ 9 (q37 c4) ∷
   rw 10 (q38 c4) ∷
   rw⁻ 11 (q39 c4) ∷
   rw 12 (q38 c4) ∷
   rw⁻ 13 (q40 c4) ∷
   rw⁻ 9 (q36 c4) ∷
   rw 6 (q41 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   rw 6 (q29 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q31 c4) ∷
   rw 9 (q30 c4) ∷
   rw 10 (q32 c4) ∷
   rw⁻ 11 (q33 c4) ∷
   rw 5 (q27 c4) ∷
   rw⁻ 6 (q42 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   rw 7 (q25 c4) ∷
   rw⁻ 10 (q45 c4) ∷
   rw 9 (q46 c4) ∷
   rw⁻ 8 (q45 c4) ∷
   rw 7 (q46 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw 8 (q82 c4) ∷
   rw 8 (q83 c4) ∷
   rw 11 (q84 c4) ∷
   rw 11 (q25 c4) ∷
   rw 15 (q63 c4) ∷
   rw 14 (q64 c4) ∷
   rw⁻ 15 (q65 c4) ∷
   rw 16 (q66 c4) ∷
   rw⁻ 17 (q65 c4) ∷
   rw⁻ 18 (q67 c4) ∷
   rw⁻ 14 (q63 c4) ∷
   rw⁻ 13 (q68 c4) ∷
   rw 13 (q63 c4) ∷
   rw 12 (q64 c4) ∷
   rw⁻ 13 (q65 c4) ∷
   rw 14 (q66 c4) ∷
   rw⁻ 15 (q65 c4) ∷
   rw⁻ 16 (q67 c4) ∷
   rw⁻ 12 (q63 c4) ∷
   rw⁻ 11 (q68 c4) ∷
   rw⁻ 12 (q25 c4) ∷
   rw 12 (q82 c4) ∷
   rw 12 (q83 c4) ∷
   rw 15 (q84 c4) ∷
   rw 15 (q25 c4) ∷
   rw⁻ 18 (q85 c4) ∷
   rw 17 (q86 c4) ∷
   rw⁻ 16 (q85 c4) ∷
   rw 15 (q86 c4) ∷
   rw⁻ 16 (q25 c4) ∷
   rw 16 (q47 c4) ∷
   rw 16 (q87 c4) ∷
   rw 19 (q88 c4) ∷
   rw 19 (q25 c4) ∷
   rw 23 (q63 c4) ∷
   rw 22 (q64 c4) ∷
   rw⁻ 23 (q65 c4) ∷
   rw 24 (q66 c4) ∷
   rw⁻ 25 (q65 c4) ∷
   rw⁻ 26 (q67 c4) ∷
   rw⁻ 22 (q63 c4) ∷
   rw⁻ 21 (q68 c4) ∷
   rw 21 (q63 c4) ∷
   rw 20 (q64 c4) ∷
   rw⁻ 21 (q65 c4) ∷
   rw 22 (q66 c4) ∷
   rw⁻ 23 (q65 c4) ∷
   rw⁻ 24 (q67 c4) ∷
   rw⁻ 20 (q63 c4) ∷
   rw⁻ 19 (q68 c4) ∷
   rw⁻ 20 (q25 c4) ∷
   rw 20 (q47 c4) ∷
   rw 20 (q87 c4) ∷
   rw 23 (q88 c4) ∷
   rw 23 (q25 c4) ∷
   rw⁻ 26 (q85 c4) ∷
   rw 25 (q86 c4) ∷
   rw⁻ 24 (q85 c4) ∷
   rw 23 (q86 c4) ∷
   rw⁻ 24 (q25 c4) ∷
   rw 3 (q75 c4) ∷
   rw 5 (q76 c4) ∷
   rw 8 (q89 c4) ∷
   rw 9 (q90 c4) ∷
   rw 10 (q91 c4) ∷
   rw 11 (q90 c4) ∷
   rw 12 (q89 c4) ∷
   rw 13 (q90 c4) ∷
   rw 16 (q73 c4) ∷
   rw 0 (q92 c4) ∷
   rw⁻ 0 (q93 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = eqn (Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ []) (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (CCZ024 ∷ []) (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (wp1119 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (CCZ024 ∷ []) (CCZ024 ∷ []) (wp1120 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ024 ∷ []) (lem-nf-rel-267at0 c4)

-- F1-rel-267@0: 18 steps
lem-F1-rel-267at0 : Ws → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-rel-267at0 c4 = derive (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  (rw 1 (q2 c4) ∷
   rw 2 (q2 c4) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q2 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 13 (q2 c4) ∷
   rw 14 (q2 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw 1 (q80 c4) ∷
   rw 5 (q80 c4) ∷
   rw 8 (q94 c4) ∷
   rw 10 (q80 c4) ∷
   rw 14 (q80 c4) ∷
   rw⁻ 0 (q95 c4) ∷
   rw 0 (q96 c4) ∷
   rw⁻ 0 (q97 c4) ∷ []) Eq.refl
