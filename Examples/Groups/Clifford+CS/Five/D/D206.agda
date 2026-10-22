{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD206 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D206 (Sᴰ : SD206) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ034-CX12 ; lem-comm-CCZ134-CS02 ; lem-comm-CCZ134-CX02 ; lem-comm-TOFF304-CX12 ; lem-comm-TOFF312-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CCZ123-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF302-CS14 ; lem-comm-TOFF302-CSd14 ; lem-comm-TOFF302-CX14)

-- The lemmas of other derivation modules (DSig).
private
  lem-box-cP-at0310243142 : Ws → St 844
  lem-box-cP-at0310243142 = pickᴰ 0 Sᴰ
  lem-box-cP-at03243240 : Ws → St 960
  lem-box-cP-at03243240 = pickᴰ 1 Sᴰ
  lem-box-cP-at033440 : Ws → St 961
  lem-box-cP-at033440 = pickᴰ 2 Sᴰ
  lem-box-perm-1324-at03243240 : Ws → St 1141
  lem-box-perm-1324-at03243240 = pickᴰ 3 Sᴰ
  lem-S2-SBOX⟨3·1·42·0⟩ : Ws → St 1808
  lem-S2-SBOX⟨3·1·42·0⟩ = pickᴰ 4 Sᴰ
  lem-L-CX01-0 : Ws → St 1811
  lem-L-CX01-0 = pickᴰ 5 Sᴰ
  lem-L-CX01-1 : Ws → St 1526
  lem-L-CX01-1 = pickᴰ 6 Sᴰ
  lem-L-CX10-1 : Ws → St 1812
  lem-L-CX10-1 = pickᴰ 7 Sᴰ
  lem-deb-P-hi-at02132031-part1 : Ws → St 1813
  lem-deb-P-hi-at02132031-part1 = pickᴰ 8 Sᴰ
  lem-deb-P-hi-at132132-part1 : Ws → St 1814
  lem-deb-P-hi-at132132-part1 = pickᴰ 9 Sᴰ
  lem-deb-P-hi-part1 : Ws → St 1815
  lem-deb-P-hi-part1 = pickᴰ 10 Sᴰ
  lem-deb-P-lo-part1 : Ws → St 1816
  lem-deb-P-lo-part1 = pickᴰ 11 Sᴰ
  lem-deb-P-lo-at02132031-part1 : Ws → St 1817
  lem-deb-P-lo-at02132031-part1 = pickᴰ 12 Sᴰ
  lem-deb-P-lo-at132132-part1 : Ws → St 1818
  lem-deb-P-lo-at132132-part1 = pickᴰ 13 Sᴰ
  lem-F0-at01143043 : Ws → St 1803
  lem-F0-at01143043 = pickᴰ 14 Sᴰ
  lem-F0-at14213243 : Ws → St 1804
  lem-F0-at14213243 = pickᴰ 15 Sᴰ
  lem-deb-P-hi-part0 : Ws → St 1819
  lem-deb-P-hi-part0 = pickᴰ 16 Sᴰ
  lem-deb-P-hi-at02132031-part0 : Ws → St 1820
  lem-deb-P-hi-at02132031-part0 = pickᴰ 17 Sᴰ
  lem-deb-P-hi-at132132-part0 : Ws → St 1821
  lem-deb-P-hi-at132132-part0 = pickᴰ 18 Sᴰ
  lem-deb-P-lo-part0 : Ws → St 1822
  lem-deb-P-lo-part0 = pickᴰ 19 Sᴰ
  lem-deb-P-lo-at02132031-part0 : Ws → St 1823
  lem-deb-P-lo-at02132031-part0 = pickᴰ 20 Sᴰ
  lem-deb-P-lo-at132132-part0 : Ws → St 1824
  lem-deb-P-lo-at132132-part0 = pickᴰ 21 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1811 (lem-L-CX01-0 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1526 (lem-L-CX01-1 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1812 (lem-L-CX10-1 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1803 (lem-F0-at01143043 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1804 (lem-F0-at14213243 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1808 (lem-S2-SBOX⟨3·1·42·0⟩ c4)
  q7 : Ws → Eqn
  q7 c4 = sE 844 (lem-box-cP-at0310243142 c4)
  q8 : Ws → Eqn
  q8 c4 = wlE 1225 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = wlE 888 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = wpE 701 c4
  q11 : Ws → Eqn
  q11 c4 = wpE 108 c4
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ034 ∷ CX12 ∷ []) (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = wpE 107 c4
  q14 : Ws → Eqn
  q14 c4 = wpE 106 c4
  q15 : Ws → Eqn
  q15 c4 = wpE 700 c4
  q16 : Ws → Eqn
  q16 c4 = wpE 716 c4
  q17 : Ws → Eqn
  q17 c4 = wlE 779 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = wpE 41 c4
  q19 : Ws → Eqn
  q19 c4 = wlE 499 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Toff312 ∷ CX04 ∷ []) (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = wlE 778 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = wlE 501 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = wlE 780 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 124 c4
  q25 : Ws → Eqn
  q25 c4 = wlE 861 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wpE 3 c4
  q27 : Ws → Eqn
  q27 c4 = wlE 1226 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = wpE 2 c4
  q29 : Ws → Eqn
  q29 c4 = wlE 1309 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = wlE 1310 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = wpE 1130 c4
  q32 : Ws → Eqn
  q32 c4 = wpE 1131 c4
  q33 : Ws → Eqn
  q33 c4 = wpE 295 c4
  q34 : Ws → Eqn
  q34 c4 = wlE 852 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = wpE 13 c4
  q36 : Ws → Eqn
  q36 c4 = wlE 879 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 878 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wlE 1311 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wpE 109 c4
  q40 : Ws → Eqn
  q40 c4 = sE 960 (lem-box-cP-at03243240 c4)
  q41 : Ws → Eqn
  q41 c4 = wpE 1025 c4
  q42 : Ws → Eqn
  q42 c4 = wpE 1026 c4
  q43 : Ws → Eqn
  q43 c4 = eqn (K0 ∷ CCZ134 ∷ []) (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q44 : Ws → Eqn
  q44 c4 = wlE 1220 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ134 ∷ CX02 ∷ []) (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = wlE 1221 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wpE 1003 c4
  q48 : Ws → Eqn
  q48 c4 = eqn (K0⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q49 : Ws → Eqn
  q49 c4 = wlE 1206 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = wpE 1007 c4
  q51 : Ws → Eqn
  q51 c4 = wlE 220 (lit c4)
  q52 : Ws → Eqn
  q52 c4 = wpE 1006 c4
  q53 : Ws → Eqn
  q53 c4 = eqn (Toff302 ∷ CX14 ∷ []) (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = wpE 1005 c4
  q55 : Ws → Eqn
  q55 c4 = wlE 1190 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wpE 1008 c4
  q57 : Ws → Eqn
  q57 c4 = wlE 1222 (lit c4)
  q58 : Ws → Eqn
  q58 c4 = wlE 1223 (lit c4)
  q59 : Ws → Eqn
  q59 c4 = wpE 261 c4
  q60 : Ws → Eqn
  q60 c4 = wlE 1224 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = wpE 1027 c4
  q62 : Ws → Eqn
  q62 c4 = wpE 1132 c4
  q63 : Ws → Eqn
  q63 c4 = wlE 1252 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Toff302 ∷ CS14 ∷ []) (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = wlE 1233 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Toff302 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = wpE 1041 c4
  q68 : Ws → Eqn
  q68 c4 = wlE 1312 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = wpE 1133 c4
  q70 : Ws → Eqn
  q70 c4 = wpE 1134 c4
  q71 : Ws → Eqn
  q71 c4 = wpE 296 c4
  q72 : Ws → Eqn
  q72 c4 = wpE 103 c4
  q73 : Ws → Eqn
  q73 c4 = wpE 1135 c4
  q74 : Ws → Eqn
  q74 c4 = sE 1141 (lem-box-perm-1324-at03243240 c4)
  q75 : Ws → Eqn
  q75 c4 = sE 961 (lem-box-cP-at033440 c4)
  q76 : Ws → Eqn
  q76 c4 = wpE 1035 c4
  q77 : Ws → Eqn
  q77 c4 = wpE 691 c4
  q78 : Ws → Eqn
  q78 c4 = eqn (Toff304 ∷ CX12 ∷ []) (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = wpE 1036 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 1037 c4
  q81 : Ws → Eqn
  q81 c4 = wpE 1038 c4
  q82 : Ws → Eqn
  q82 c4 = wlE 758 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = wpE 1039 c4
  q84 : Ws → Eqn
  q84 c4 = wlE 765 (lit c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ123 ∷ CX04 ∷ []) (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = wlE 764 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = wlE 763 (lit c4)
  q88 : Ws → Eqn
  q88 c4 = wlE 618 (lit c4)
  q89 : Ws → Eqn
  q89 c4 = wpE 1040 c4
  q90 : Ws → Eqn
  q90 c4 = wlE 1313 (lit c4)
  q91 : Ws → Eqn
  q91 c4 = wlE 1314 (lit c4)
  q92 : Ws → Eqn
  q92 c4 = wpE 1136 c4
  q93 : Ws → Eqn
  q93 c4 = wlE 960 (lit c4)
  q94 : Ws → Eqn
  q94 c4 = wpE 1137 c4
  q95 : Ws → Eqn
  q95 c4 = wpE 301 c4
  q96 : Ws → Eqn
  q96 c4 = wpE 272 c4
  q97 : Ws → Eqn
  q97 c4 = wlE 801 (lit c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (CCZ134 ∷ CS02 ∷ []) (CS02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CS02 (lit c4))

-- L-CCZ-0 part0: 500 steps
lem-L-CCZ-0-part0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-L-CCZ-0-part0 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q3 c4) ∷
   rw 8 (q2 c4) ∷
   rw 10 (q2 c4) ∷
   rw 11 (q3 c4) ∷
   rw 12 (q2 c4) ∷
   rw 0 (q4 c4) ∷
   rw 2 (q4 c4) ∷
   rw 3 (q4 c4) ∷
   rw 4 (q4 c4) ∷
   rw 9 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   re 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 2 1 (CS01 ∷ []) ∷
   re 4 1 (CS01⁻ ∷ []) ∷
   re 7 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 9 1 (CS01 ∷ []) ∷
   re 11 1 (CS01⁻ ∷ []) ∷
   re 16 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 18 1 (CS02 ∷ []) ∷
   re 20 1 (CS02⁻ ∷ []) ∷
   rw 16 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q13 c4) ∷
   rw 22 (q12 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q15 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw 19 (q17 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw 21 (q20 c4) ∷
   rw⁻ 22 (q21 c4) ∷
   rw 23 (q20 c4) ∷
   rw⁻ 24 (q22 c4) ∷
   rw⁻ 20 (q18 c4) ∷
   rw 17 (q23 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw 16 (q10 c4) ∷
   rw 17 (q11 c4) ∷
   rw 18 (q12 c4) ∷
   rw 19 (q13 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q15 c4) ∷
   rw 16 (q9 c4) ∷
   rw⁻ 17 (q24 c4) ∷
   rw⁻ 18 (q7 c4) ∷
   rw 18 (q7 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw 20 (q26 c4) ∷
   rw⁻ 19 (q25 c4) ∷
   rw 18 (q26 c4) ∷
   rw⁻ 19 (q7 c4) ∷
   rw 19 (q7 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q12 c4) ∷
   rw 24 (q13 c4) ∷
   rw 25 (q12 c4) ∷
   rw 26 (q14 c4) ∷
   rw 27 (q15 c4) ∷
   rw 21 (q9 c4) ∷
   rw 22 (q16 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw 22 (q17 c4) ∷
   rw 24 (q18 c4) ∷
   rw⁻ 23 (q19 c4) ∷
   rw 24 (q20 c4) ∷
   rw⁻ 25 (q21 c4) ∷
   rw 26 (q20 c4) ∷
   rw⁻ 27 (q22 c4) ∷
   rw⁻ 23 (q18 c4) ∷
   rw 20 (q23 c4) ∷
   rw⁻ 20 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q11 c4) ∷
   rw 21 (q12 c4) ∷
   rw 22 (q13 c4) ∷
   rw 23 (q12 c4) ∷
   rw 24 (q14 c4) ∷
   rw 25 (q15 c4) ∷
   rw 19 (q9 c4) ∷
   rw⁻ 20 (q24 c4) ∷
   rw⁻ 21 (q7 c4) ∷
   rw 21 (q7 c4) ∷
   rw⁻ 24 (q27 c4) ∷
   rw 23 (q28 c4) ∷
   rw⁻ 22 (q27 c4) ∷
   rw 21 (q28 c4) ∷
   rw⁻ 22 (q7 c4) ∷
   rw 22 (q7 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 25 (q9 c4) ∷
   rw 24 (q10 c4) ∷
   rw 25 (q11 c4) ∷
   rw 26 (q12 c4) ∷
   rw 27 (q13 c4) ∷
   rw 28 (q12 c4) ∷
   rw 29 (q14 c4) ∷
   rw 30 (q15 c4) ∷
   rw 24 (q9 c4) ∷
   rw 25 (q16 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw 25 (q17 c4) ∷
   rw 27 (q18 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw 27 (q20 c4) ∷
   rw⁻ 28 (q21 c4) ∷
   rw 29 (q20 c4) ∷
   rw⁻ 30 (q22 c4) ∷
   rw⁻ 26 (q18 c4) ∷
   rw 23 (q23 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw 22 (q10 c4) ∷
   rw 23 (q11 c4) ∷
   rw 24 (q12 c4) ∷
   rw 25 (q13 c4) ∷
   rw 26 (q12 c4) ∷
   rw 27 (q14 c4) ∷
   rw 28 (q15 c4) ∷
   rw 22 (q9 c4) ∷
   rw⁻ 23 (q24 c4) ∷
   rw⁻ 24 (q7 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 27 (q29 c4) ∷
   rw⁻ 27 (q30 c4) ∷
   rw 26 (q31 c4) ∷
   rw 27 (q11 c4) ∷
   rw 28 (q12 c4) ∷
   rw 29 (q13 c4) ∷
   rw 30 (q12 c4) ∷
   rw 31 (q14 c4) ∷
   rw 32 (q32 c4) ∷
   rw 26 (q30 c4) ∷
   rw 27 (q33 c4) ∷
   rw⁻ 25 (q29 c4) ∷
   rw 27 (q34 c4) ∷
   rw 29 (q35 c4) ∷
   rw⁻ 28 (q36 c4) ∷
   rw 29 (q20 c4) ∷
   rw⁻ 30 (q37 c4) ∷
   rw 31 (q20 c4) ∷
   rw⁻ 32 (q25 c4) ∷
   rw⁻ 28 (q35 c4) ∷
   rw 25 (q38 c4) ∷
   rw⁻ 25 (q30 c4) ∷
   rw 24 (q31 c4) ∷
   rw 25 (q11 c4) ∷
   rw 26 (q12 c4) ∷
   rw 27 (q13 c4) ∷
   rw 28 (q12 c4) ∷
   rw 29 (q14 c4) ∷
   rw 30 (q32 c4) ∷
   rw 24 (q30 c4) ∷
   rw⁻ 25 (q39 c4) ∷
   rw⁻ 26 (q7 c4) ∷
   rw 26 (q7 c4) ∷
   rw⁻ 29 (q8 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw 28 (q10 c4) ∷
   rw 29 (q11 c4) ∷
   rw 30 (q12 c4) ∷
   rw 31 (q13 c4) ∷
   rw 32 (q12 c4) ∷
   rw 33 (q14 c4) ∷
   rw 34 (q15 c4) ∷
   rw 28 (q9 c4) ∷
   rw 29 (q16 c4) ∷
   rw⁻ 27 (q8 c4) ∷
   rw 29 (q17 c4) ∷
   rw 31 (q18 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw 31 (q20 c4) ∷
   rw⁻ 32 (q21 c4) ∷
   rw 33 (q20 c4) ∷
   rw⁻ 34 (q22 c4) ∷
   rw⁻ 30 (q18 c4) ∷
   rw 27 (q23 c4) ∷
   rw⁻ 27 (q9 c4) ∷
   rw 26 (q10 c4) ∷
   rw 27 (q11 c4) ∷
   rw 28 (q12 c4) ∷
   rw 29 (q13 c4) ∷
   rw 30 (q12 c4) ∷
   rw 31 (q14 c4) ∷
   rw 32 (q15 c4) ∷
   rw 26 (q9 c4) ∷
   rw⁻ 27 (q24 c4) ∷
   rw⁻ 28 (q7 c4) ∷
   rw 7 (q40 c4) ∷
   rw⁻ 10 (q41 c4) ∷
   rw⁻ 10 (q42 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   rw 10 (q44 c4) ∷
   rw 11 (q45 c4) ∷
   rw 12 (q46 c4) ∷
   rw 13 (q45 c4) ∷
   rw 14 (q47 c4) ∷
   rw⁻ 15 (q48 c4) ∷
   rw 9 (q42 c4) ∷
   rw 10 (q49 c4) ∷
   rw⁻ 8 (q41 c4) ∷
   rw 10 (q50 c4) ∷
   rw 12 (q51 c4) ∷
   rw⁻ 11 (q52 c4) ∷
   rw 12 (q53 c4) ∷
   rw⁻ 13 (q54 c4) ∷
   rw 14 (q53 c4) ∷
   rw⁻ 15 (q55 c4) ∷
   rw⁻ 11 (q51 c4) ∷
   rw 8 (q56 c4) ∷
   rw⁻ 8 (q42 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   rw 8 (q44 c4) ∷
   rw 9 (q45 c4) ∷
   rw 10 (q46 c4) ∷
   rw 11 (q45 c4) ∷
   rw 12 (q47 c4) ∷
   rw⁻ 13 (q48 c4) ∷
   rw 7 (q42 c4) ∷
   rw⁻ 8 (q57 c4) ∷
   rw⁻ 9 (q40 c4) ∷
   rw 9 (q40 c4) ∷
   rw⁻ 12 (q58 c4) ∷
   rw 11 (q59 c4) ∷
   rw⁻ 10 (q58 c4) ∷
   rw 9 (q59 c4) ∷
   rw⁻ 10 (q40 c4) ∷
   rw 10 (q40 c4) ∷
   rw⁻ 13 (q41 c4) ∷
   rw⁻ 13 (q42 c4) ∷
   rw⁻ 12 (q43 c4) ∷
   rw 13 (q44 c4) ∷
   rw 14 (q45 c4) ∷
   rw 15 (q46 c4) ∷
   rw 16 (q45 c4) ∷
   rw 17 (q47 c4) ∷
   rw⁻ 18 (q48 c4) ∷
   rw 12 (q42 c4) ∷
   rw 13 (q49 c4) ∷
   rw⁻ 11 (q41 c4) ∷
   rw 13 (q50 c4) ∷
   rw 15 (q51 c4) ∷
   rw⁻ 14 (q52 c4) ∷
   rw 15 (q53 c4) ∷
   rw⁻ 16 (q54 c4) ∷
   rw 17 (q53 c4) ∷
   rw⁻ 18 (q55 c4) ∷
   rw⁻ 14 (q51 c4) ∷
   rw 11 (q56 c4) ∷
   rw⁻ 11 (q42 c4) ∷
   rw⁻ 10 (q43 c4) ∷
   rw 11 (q44 c4) ∷
   rw 12 (q45 c4) ∷
   rw 13 (q46 c4) ∷
   rw 14 (q45 c4) ∷
   rw 15 (q47 c4) ∷
   rw⁻ 16 (q48 c4) ∷
   rw 10 (q42 c4) ∷
   rw⁻ 11 (q57 c4) ∷
   rw⁻ 12 (q40 c4) ∷
   rw 12 (q40 c4) ∷
   rw⁻ 15 (q60 c4) ∷
   rw 14 (q61 c4) ∷
   rw⁻ 13 (q60 c4) ∷
   rw 12 (q61 c4) ∷
   rw⁻ 13 (q40 c4) ∷
   rw 13 (q40 c4) ∷
   rw⁻ 17 (q62 c4) ∷
   rw⁻ 16 (q63 c4) ∷
   rw 17 (q64 c4) ∷
   rw⁻ 18 (q65 c4) ∷
   rw 19 (q66 c4) ∷
   rw⁻ 20 (q65 c4) ∷
   rw⁻ 21 (q67 c4) ∷
   rw⁻ 22 (q68 c4) ∷
   rw 16 (q62 c4) ∷
   rw 15 (q69 c4) ∷
   rw⁻ 15 (q62 c4) ∷
   rw⁻ 14 (q63 c4) ∷
   rw 15 (q64 c4) ∷
   rw⁻ 16 (q65 c4) ∷
   rw 17 (q66 c4) ∷
   rw⁻ 18 (q65 c4) ∷
   rw⁻ 19 (q67 c4) ∷
   rw⁻ 20 (q68 c4) ∷
   rw 14 (q62 c4) ∷
   rw⁻ 15 (q70 c4) ∷
   rw 13 (q69 c4) ∷
   rw 16 (q71 c4) ∷
   rw 15 (q44 c4) ∷
   rw 16 (q45 c4) ∷
   rw 17 (q46 c4) ∷
   rw 18 (q45 c4) ∷
   rw 19 (q47 c4) ∷
   rw⁻ 15 (q71 c4) ∷
   rw⁻ 16 (q72 c4) ∷
   rw⁻ 14 (q73 c4) ∷
   rw⁻ 15 (q40 c4) ∷
   rw 15 (q74 c4) ∷
   rw 15 (q75 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q76 c4) ∷
   rw⁻ 19 (q77 c4) ∷
   rw 20 (q78 c4) ∷
   rw⁻ 21 (q79 c4) ∷
   rw 22 (q78 c4) ∷
   rw⁻ 23 (q80 c4) ∷
   rw⁻ 24 (q81 c4) ∷
   rw 18 (q9 c4) ∷
   rw 17 (q82 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw⁻ 16 (q76 c4) ∷
   rw⁻ 17 (q77 c4) ∷
   rw 18 (q78 c4) ∷
   rw⁻ 19 (q79 c4) ∷
   rw 20 (q78 c4) ∷
   rw⁻ 21 (q80 c4) ∷
   rw⁻ 22 (q81 c4) ∷
   rw 16 (q9 c4) ∷
   rw⁻ 17 (q83 c4) ∷
   rw 15 (q82 c4) ∷
   rw 18 (q18 c4) ∷
   rw 17 (q84 c4) ∷
   rw 18 (q85 c4) ∷
   rw 19 (q86 c4) ∷
   rw 20 (q85 c4) ∷
   rw 21 (q87 c4) ∷
   rw⁻ 17 (q18 c4) ∷
   rw 18 (q88 c4) ∷
   rw⁻ 16 (q89 c4) ∷
   rw⁻ 17 (q75 c4) ∷
   rw⁻ 17 (q74 c4) ∷
   rw 17 (q40 c4) ∷
   rw⁻ 21 (q90 c4) ∷
   rw⁻ 20 (q63 c4) ∷
   rw⁻ 21 (q52 c4) ∷
   rw 22 (q53 c4) ∷
   rw⁻ 23 (q54 c4) ∷
   rw 24 (q53 c4) ∷
   rw⁻ 25 (q55 c4) ∷
   rw⁻ 26 (q68 c4) ∷
   rw 20 (q90 c4) ∷
   rw 19 (q91 c4) ∷
   rw⁻ 19 (q90 c4) ∷
   rw⁻ 18 (q63 c4) ∷
   rw⁻ 19 (q52 c4) ∷
   rw 20 (q53 c4) ∷
   rw⁻ 21 (q54 c4) ∷
   rw 22 (q53 c4) ∷
   rw⁻ 23 (q55 c4) ∷
   rw⁻ 24 (q68 c4) ∷
   rw 18 (q90 c4) ∷
   rw⁻ 19 (q92 c4) ∷
   rw 17 (q91 c4) ∷
   rw 20 (q71 c4) ∷
   rw 19 (q44 c4) ∷
   rw 20 (q45 c4) ∷
   rw 21 (q46 c4) ∷
   rw 22 (q45 c4) ∷
   rw 23 (q47 c4) ∷
   rw⁻ 19 (q71 c4) ∷
   rw 20 (q93 c4) ∷
   rw⁻ 18 (q94 c4) ∷
   rw⁻ 19 (q40 c4) ∷
   rw 19 (q74 c4) ∷
   rw 19 (q75 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw⁻ 22 (q76 c4) ∷
   rw⁻ 23 (q77 c4) ∷
   rw 24 (q78 c4) ∷
   rw⁻ 25 (q79 c4) ∷
   rw 26 (q78 c4) ∷
   rw⁻ 27 (q80 c4) ∷
   rw⁻ 28 (q81 c4) ∷
   rw 22 (q9 c4) ∷
   rw 21 (q82 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 20 (q76 c4) ∷
   rw⁻ 21 (q77 c4) ∷
   rw 22 (q78 c4) ∷
   rw⁻ 23 (q79 c4) ∷
   rw 24 (q78 c4) ∷
   rw⁻ 25 (q80 c4) ∷
   rw⁻ 26 (q81 c4) ∷
   rw 20 (q9 c4) ∷
   rw⁻ 21 (q83 c4) ∷
   rw 19 (q82 c4) ∷
   rw 22 (q18 c4) ∷
   rw 21 (q84 c4) ∷
   rw 22 (q85 c4) ∷
   rw 23 (q86 c4) ∷
   rw 24 (q85 c4) ∷
   rw 25 (q87 c4) ∷
   rw⁻ 21 (q18 c4) ∷
   rw 22 (q88 c4) ∷
   rw⁻ 20 (q89 c4) ∷
   rw⁻ 21 (q75 c4) ∷
   rw⁻ 21 (q74 c4) ∷
   rw 21 (q74 c4) ∷
   rw 21 (q75 c4) ∷
   rw⁻ 25 (q9 c4) ∷
   rw⁻ 24 (q76 c4) ∷
   rw⁻ 25 (q77 c4) ∷
   rw 26 (q78 c4) ∷
   rw⁻ 27 (q79 c4) ∷
   rw 28 (q78 c4) ∷
   rw⁻ 29 (q80 c4) ∷
   rw⁻ 30 (q81 c4) ∷
   rw 24 (q9 c4) ∷
   rw 23 (q82 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw⁻ 22 (q76 c4) ∷
   rw⁻ 23 (q77 c4) ∷
   rw 24 (q78 c4) ∷
   rw⁻ 25 (q79 c4) ∷
   rw 26 (q78 c4) ∷
   rw⁻ 27 (q80 c4) ∷
   rw⁻ 28 (q81 c4) ∷
   rw 22 (q9 c4) ∷
   rw⁻ 23 (q83 c4) ∷
   rw 21 (q82 c4) ∷
   rw 24 (q18 c4) ∷
   rw 23 (q84 c4) ∷
   rw 24 (q85 c4) ∷
   rw 25 (q86 c4) ∷
   rw 26 (q85 c4) ∷
   rw 27 (q87 c4) ∷
   rw⁻ 23 (q18 c4) ∷
   rw 24 (q88 c4) ∷
   rw⁻ 22 (q89 c4) ∷
   rw⁻ 23 (q75 c4) ∷
   rw⁻ 23 (q74 c4) ∷
   rw 23 (q40 c4) ∷
   rw 27 (q95 c4) ∷
   rw 26 (q64 c4) ∷
   rw⁻ 27 (q65 c4) ∷
   rw 28 (q66 c4) ∷
   rw⁻ 29 (q65 c4) ∷
   rw⁻ 30 (q67 c4) ∷
   rw⁻ 26 (q95 c4) ∷
   rw⁻ 25 (q96 c4) ∷
   rw 25 (q95 c4) ∷
   rw 24 (q64 c4) ∷
   rw⁻ 25 (q65 c4) ∷
   rw 26 (q66 c4) ∷
   rw⁻ 27 (q65 c4) ∷
   rw⁻ 28 (q67 c4) ∷
   rw⁻ 24 (q95 c4) ∷
   rw⁻ 23 (q96 c4) ∷
   rw⁻ 24 (q40 c4) ∷
   rw 24 (q40 c4) ∷
   rw⁻ 27 (q97 c4) ∷
   rw 26 (q98 c4) ∷
   rw⁻ 25 (q97 c4) ∷
   rw 24 (q98 c4) ∷
   rw⁻ 25 (q40 c4) ∷
   rw 25 (q74 c4) ∷
   rw 25 (q75 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw⁻ 28 (q76 c4) ∷
   rw⁻ 29 (q77 c4) ∷
   rw 30 (q78 c4) ∷
   rw⁻ 31 (q79 c4) ∷
   rw 32 (q78 c4) ∷
   rw⁻ 33 (q80 c4) ∷
   rw⁻ 34 (q81 c4) ∷
   rw 28 (q9 c4) ∷
   rw 27 (q82 c4) ∷
   rw⁻ 27 (q9 c4) ∷
   rw⁻ 26 (q76 c4) ∷
   rw⁻ 27 (q77 c4) ∷
   rw 28 (q78 c4) ∷
   rw⁻ 29 (q79 c4) ∷
   rw 30 (q78 c4) ∷
   rw⁻ 31 (q80 c4) ∷
   rw⁻ 32 (q81 c4) ∷
   rw 26 (q9 c4) ∷
   rw⁻ 27 (q83 c4) ∷
   rw 25 (q82 c4) ∷
   rw 28 (q18 c4) ∷
   rw 27 (q84 c4) ∷
   rw 28 (q85 c4) ∷
   rw 29 (q86 c4) ∷
   rw 30 (q85 c4) ∷
   rw 31 (q87 c4) ∷
   rw⁻ 27 (q18 c4) ∷
   rw 28 (q88 c4) ∷
   rw⁻ 26 (q89 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = sE 1819 (lem-deb-P-hi-part0 c4)
  q100 : Ws → Eqn
  q100 c4 = sE 1815 (lem-deb-P-hi-part1 c4)

-- deb-P-hi: 2 steps
lem-deb-P-hi : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-P-hi c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  (rw 0 (q99 c4) ∷
   rw 0 (q100 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = sE 1820 (lem-deb-P-hi-at02132031-part0 c4)
  q102 : Ws → Eqn
  q102 c4 = sE 1813 (lem-deb-P-hi-at02132031-part1 c4)

-- deb-P-hi @02132031: 2 steps
lem-deb-P-hi-at02132031 : Ws → ⟪ (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ
lem-deb-P-hi-at02132031 c4 = derive (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  (rw 0 (q101 c4) ∷
   rw 0 (q102 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = sE 1821 (lem-deb-P-hi-at132132-part0 c4)
  q104 : Ws → Eqn
  q104 c4 = sE 1814 (lem-deb-P-hi-at132132-part1 c4)

-- deb-P-hi @132132: 2 steps
lem-deb-P-hi-at132132 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-P-hi-at132132 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw 0 (q103 c4) ∷
   rw 0 (q104 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = sE 1822 (lem-deb-P-lo-part0 c4)
  q106 : Ws → Eqn
  q106 c4 = sE 1816 (lem-deb-P-lo-part1 c4)

-- deb-P-lo: 2 steps
lem-deb-P-lo : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ
lem-deb-P-lo c4 = derive (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (CK43 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS34 ∷ CS34 ∷ CS34 ∷ [])
  (rw 0 (q105 c4) ∷
   rw 0 (q106 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = sE 1823 (lem-deb-P-lo-at02132031-part0 c4)
  q108 : Ws → Eqn
  q108 c4 = sE 1817 (lem-deb-P-lo-at02132031-part1 c4)

-- deb-P-lo @02132031: 2 steps
lem-deb-P-lo-at02132031 : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-P-lo-at02132031 c4 = derive (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw 0 (q107 c4) ∷
   rw 0 (q108 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = sE 1824 (lem-deb-P-lo-at132132-part0 c4)
  q110 : Ws → Eqn
  q110 c4 = sE 1818 (lem-deb-P-lo-at132132-part1 c4)

-- deb-P-lo @132132: 2 steps
lem-deb-P-lo-at132132 : Ws → ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-P-lo-at132132 c4 = derive (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  (rw 0 (q109 c4) ∷
   rw 0 (q110 c4) ∷ []) Eq.refl
