{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD018 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D018 (Sᴰ : SD018) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS03-CCZ124 ; lem-comm-CS12-CCZ034 ; lem-comm-CS13-CCZ024 ; lem-comm-CS14-TOFF023 ; lem-comm-CS23-CCZ014 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd03-CCZ124 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-CCZ014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX12-TOFF034 ; lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CK40-TOFF213 ; lem-comm-CK41-TOFF023 ; lem-comm-CK42-TOFF013 ; lem-comm-CS04-TOFF213 ; lem-comm-CX40-TOFF312 ; lem-comm-TOFF213-CK40 ; lem-comm-TOFF213-CSd04 ; lem-comm-TOFF312-CS04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CK41 ; lem-comm-TOFF023-CSd14)

-- The lemmas of other derivation modules (DSig).
private
  lem-sym-ab : Ws → St 10
  lem-sym-ab = pickᴰ 0 Sᴰ
  lem-sym-ab-at032032 : Ws → St 15
  lem-sym-ab-at032032 = pickᴰ 1 Sᴰ
  lem-sym-ab-at04203243 : Ws → St 817
  lem-sym-ab-at04203243 = pickᴰ 2 Sᴰ
  lem-sym-ab-at1221 : Ws → St 16
  lem-sym-ab-at1221 = pickᴰ 3 Sᴰ
  lem-sym-ab-at122331 : Ws → St 818
  lem-sym-ab-at122331 = pickᴰ 4 Sᴰ
  lem-sym-ab-at12233441 : Ws → St 819
  lem-sym-ab-at12233441 = pickᴰ 5 Sᴰ
  lem-sym-ab-at122441 : Ws → St 820
  lem-sym-ab-at122441 = pickᴰ 6 Sᴰ
  lem-sym-ab-at2332 : Ws → St 821
  lem-sym-ab-at2332 = pickᴰ 7 Sᴰ
  lem-sym-ab-at233442 : Ws → St 822
  lem-sym-ab-at233442 = pickᴰ 8 Sᴰ
  lem-box-tQ-at0410213243 : Ws → St 79
  lem-box-tQ-at0410213243 = pickᴰ 9 Sᴰ
  lem-box-tQ-at13243142 : Ws → St 27
  lem-box-tQ-at13243142 = pickᴰ 10 Sᴰ
  lem-box-tQ-at13243241 : Ws → St 28
  lem-box-tQ-at13243241 = pickᴰ 11 Sᴰ
  lem-box-tQ-at14233142 : Ws → St 29
  lem-box-tQ-at14233142 = pickᴰ 12 Sᴰ
  lem-box-tQ : Ws → St 146
  lem-box-tQ = pickᴰ 13 Sᴰ
  lem-box-tQ-at0210233441 : Ws → St 187
  lem-box-tQ-at0210233441 = pickᴰ 14 Sᴰ
  lem-box-tQ-at0210243143 : Ws → St 147
  lem-box-tQ-at0210243143 = pickᴰ 15 Sᴰ
  lem-box-tQ-at0310243142 : Ws → St 150
  lem-box-tQ-at0310243142 = pickᴰ 16 Sᴰ
  lem-box-tQ-at0330 : Ws → St 151
  lem-box-tQ-at0330 = pickᴰ 17 Sᴰ
  lem-box-tQ-at043043 : Ws → St 152
  lem-box-tQ-at043043 = pickᴰ 18 Sᴰ
  lem-box-tQ-at12243143 : Ws → St 155
  lem-box-tQ-at12243143 = pickᴰ 19 Sᴰ
  lem-box-tQ-at122441 : Ws → St 156
  lem-box-tQ-at122441 = pickᴰ 20 Sᴰ
  lem-box-tQ-at1441 : Ws → St 196
  lem-box-tQ-at1441 = pickᴰ 21 Sᴰ
  lem-box-tQ-at233442 : Ws → St 219
  lem-box-tQ-at233442 = pickᴰ 22 Sᴰ
  lem-box-tQ-at243243 : Ws → St 162
  lem-box-tQ-at243243 = pickᴰ 23 Sᴰ
  lem-box-tQ-at2442 : Ws → St 220
  lem-box-tQ-at2442 = pickᴰ 24 Sᴰ
  lem-P-box : Ws → St 823
  lem-P-box = pickᴰ 25 Sᴰ
  lem-P-box-at0214213043 : Ws → St 824
  lem-P-box-at0214213043 = pickᴰ 26 Sᴰ
  lem-P-box-at0310243142 : Ws → St 825
  lem-P-box-at0310243142 = pickᴰ 27 Sᴰ
  lem-P-box-at0330 : Ws → St 826
  lem-P-box-at0330 = pickᴰ 28 Sᴰ
  lem-P-box-at1221 : Ws → St 827
  lem-P-box-at1221 = pickᴰ 29 Sᴰ
  lem-P-box-at122331 : Ws → St 828
  lem-P-box-at122331 = pickᴰ 30 Sᴰ
  lem-P-box-at132132 : Ws → St 829
  lem-P-box-at132132 = pickᴰ 31 Sᴰ
  lem-P-box-at13213442 : Ws → St 830
  lem-P-box-at13213442 = pickᴰ 32 Sᴰ
  lem-P-box-at1331 : Ws → St 831
  lem-P-box-at1331 = pickᴰ 33 Sᴰ
  lem-P-box-at2332 : Ws → St 832
  lem-P-box-at2332 = pickᴰ 34 Sᴰ
  lem-P-box-at3443 : Ws → St 833
  lem-P-box-at3443 = pickᴰ 35 Sᴰ
  lem-t-cP : Ws → St 834
  lem-t-cP = pickᴰ 36 Sᴰ
  lem-t-cP-at0210243143 : Ws → St 835
  lem-t-cP-at0210243143 = pickᴰ 37 Sᴰ
  lem-t-cP-at043043 : Ws → St 836
  lem-t-cP-at043043 = pickᴰ 38 Sᴰ
  lem-t-cP-at122441 : Ws → St 837
  lem-t-cP-at122441 = pickᴰ 39 Sᴰ
  lem-t-cP-at243243 : Ws → St 838
  lem-t-cP-at243243 = pickᴰ 40 Sᴰ
  lem-P-box-at143143 : Ws → St 839
  lem-P-box-at143143 = pickᴰ 41 Sᴰ
  lem-CXu-box-4-at03102132 : Ws → St 840
  lem-CXu-box-4-at03102132 = pickᴰ 42 Sᴰ
  lem-box-cP : Ws → St 841
  lem-box-cP = pickᴰ 43 Sᴰ
  lem-box-cP-at0210243143 : Ws → St 842
  lem-box-cP-at0210243143 = pickᴰ 44 Sᴰ
  lem-box-cP-at0214213043 : Ws → St 843
  lem-box-cP-at0214213043 = pickᴰ 45 Sᴰ
  lem-box-cP-at0310243142 : Ws → St 844
  lem-box-cP-at0310243142 = pickᴰ 46 Sᴰ
  lem-box-cP-at0314203142 : Ws → St 845
  lem-box-cP-at0314203142 = pickᴰ 47 Sᴰ
  lem-box-cP-at0330 : Ws → St 846
  lem-box-cP-at0330 = pickᴰ 48 Sᴰ
  lem-box-cP-at043043 : Ws → St 847
  lem-box-cP-at043043 = pickᴰ 49 Sᴰ
  lem-box-cP-at1221 : Ws → St 848
  lem-box-cP-at1221 = pickᴰ 50 Sᴰ
  lem-box-cP-at122331 : Ws → St 849
  lem-box-cP-at122331 = pickᴰ 51 Sᴰ
  lem-box-cP-at122441 : Ws → St 850
  lem-box-cP-at122441 = pickᴰ 52 Sᴰ
  lem-box-cP-at132132 : Ws → St 851
  lem-box-cP-at132132 = pickᴰ 53 Sᴰ
  lem-box-cP-at13213442 : Ws → St 852
  lem-box-cP-at13213442 = pickᴰ 54 Sᴰ
  lem-box-cP-at1331 : Ws → St 853
  lem-box-cP-at1331 = pickᴰ 55 Sᴰ
  lem-box-cP-at143143 : Ws → St 854
  lem-box-cP-at143143 = pickᴰ 56 Sᴰ
  lem-box-cP-at2332 : Ws → St 855
  lem-box-cP-at2332 = pickᴰ 57 Sᴰ
  lem-box-cP-at243243 : Ws → St 856
  lem-box-cP-at243243 = pickᴰ 58 Sᴰ
  lem-box-cP-at3443 : Ws → St 857
  lem-box-cP-at3443 = pickᴰ 59 Sᴰ
  lem-pairs-at13243142 : Ws → St 858
  lem-pairs-at13243142 = pickᴰ 60 Sᴰ
  lem-pairs-at13243241 : Ws → St 859
  lem-pairs-at13243241 = pickᴰ 61 Sᴰ
  lem-pairs-at14233241 : Ws → St 860
  lem-pairs-at14233241 = pickᴰ 62 Sᴰ
  lem-sym-bc : Ws → St 861
  lem-sym-bc = pickᴰ 63 Sᴰ
  lem-sym-bc-at0210243143 : Ws → St 862
  lem-sym-bc-at0210243143 = pickᴰ 64 Sᴰ
  lem-sym-bc-at0330 : Ws → St 863
  lem-sym-bc-at0330 = pickᴰ 65 Sᴰ
  lem-sym-bc-at043043 : Ws → St 864
  lem-sym-bc-at043043 = pickᴰ 66 Sᴰ
  lem-sym-bc-at1221 : Ws → St 865
  lem-sym-bc-at1221 = pickᴰ 67 Sᴰ
  lem-sym-bc-at122441 : Ws → St 866
  lem-sym-bc-at122441 = pickᴰ 68 Sᴰ
  lem-sym-bc-at13213442 : Ws → St 867
  lem-sym-bc-at13213442 = pickᴰ 69 Sᴰ
  lem-sym-bc-at133441 : Ws → St 868
  lem-sym-bc-at133441 = pickᴰ 70 Sᴰ
  lem-sym-bc-at1441 : Ws → St 869
  lem-sym-bc-at1441 = pickᴰ 71 Sᴰ
  lem-sym-bc-at243243 : Ws → St 870
  lem-sym-bc-at243243 = pickᴰ 72 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 146 (lem-box-tQ c4)
  q2 : Ws → Eqn
  q2 c4 = sE 841 (lem-box-cP c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 162 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = sE 834 (lem-t-cP c4)
  q5 : Ws → Eqn
  q5 c4 = wpE 7 c4

-- box2: 11 steps
lem-box2 : Ws → ⟪ (Bx0-1234 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2 c4 = derive (Bx0-1234 ∷ Bx0-1234 ∷ []) []
  (rw 0 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   rw 5 (q1 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q3 c4) ∷ []) Eq.refl

private
  q6 : Ws → Eqn
  q6 c4 = wlE 165 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = wpE 9 c4
  q8 : Ws → Eqn
  q8 c4 = wpE 10 c4
  q9 : Ws → Eqn
  q9 c4 = wlE 166 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = wpE 11 c4
  q11 : Ws → Eqn
  q11 c4 = wlE 167 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS))
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS))
  q14 : Ws → Eqn
  q14 c4 = wlE 168 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 169 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = wpE 12 c4
  q17 : Ws → Eqn
  q17 c4 = wlE 170 (lit c4)

-- Xb-box: 18 steps
lem-Xb-box : Ws → ⟪ (X2 ∷ Bx0-1234 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ
lem-Xb-box c4 = derive (X2 ∷ Bx0-1234 ∷ X2 ∷ []) (Bx0-1234 ∷ CCZ134 ∷ [])
  (rw 1 (q2 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 1 (q8 c4) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 8 (q10 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 3 (q15 c4) ∷
   rw 4 (q16 c4) ∷
   rw⁻ 3 (q8 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 1 (q17 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = sE 842 (lem-box-cP-at0210243143 c4)
  q19 : Ws → Eqn
  q19 c4 = wpE 20 c4
  q20 : Ws → Eqn
  q20 c4 = wlE 183 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Toff213 ∷ X4 ∷ []) (X4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))
  q22 : Ws → Eqn
  q22 c4 = wlE 184 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = wpE 21 c4
  q24 : Ws → Eqn
  q24 c4 = wpE 22 c4
  q25 : Ws → Eqn
  q25 c4 = eqn (CS13⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = wpE 23 c4
  q28 : Ws → Eqn
  q28 c4 = wlE 185 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = wlE 186 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = wpE 24 c4

-- Xb-box @0210243143: 18 steps
lem-Xb-box-at0210243143 : Ws → ⟪ (X4 ∷ Bx2-0413 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ013 ∷ []) ⟫ʷ
lem-Xb-box-at0210243143 c4 = derive (X4 ∷ Bx2-0413 ∷ X4 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ [])
  (rw 1 (q18 c4) ∷
   rw⁻ 0 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw⁻ 1 (q21 c4) ∷
   rw 4 (q22 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw 6 (q25 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 5 (q22 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 3 (q28 c4) ∷
   rw 4 (q29 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw⁻ 0 (q18 c4) ∷
   rw⁻ 1 (q30 c4) ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = sE 147 (lem-box-tQ-at0210243143 c4)
  q32 : Ws → Eqn
  q32 c4 = wpE 19 c4
  q33 : Ws → Eqn
  q33 c4 = sE 835 (lem-t-cP-at0210243143 c4)
  q34 : Ws → Eqn
  q34 c4 = wlE 181 (lit c4)

-- box2 @0210243143: 11 steps
lem-box2-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0210243143 c4 = derive (Bx2-0413 ∷ Bx2-0413 ∷ []) []
  (rw 0 (q31 c4) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q32 c4) ∷
   rw 3 (q34 c4) ∷
   rw 2 (q32 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q32 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = sE 856 (lem-box-cP-at243243 c4)
  q36 : Ws → Eqn
  q36 c4 = wpE 52 c4
  q37 : Ws → Eqn
  q37 c4 = wlE 206 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Toff023 ∷ X4 ∷ []) (X4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))
  q39 : Ws → Eqn
  q39 c4 = wlE 207 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wpE 53 c4
  q41 : Ws → Eqn
  q41 c4 = wpE 54 c4
  q42 : Ws → Eqn
  q42 c4 = eqn (CS23⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = wpE 55 c4
  q45 : Ws → Eqn
  q45 c4 = wlE 208 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = wlE 209 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wlE 210 (lit c4)

-- Xb-box @243243: 18 steps
lem-Xb-box-at243243 : Ws → ⟪ (X4 ∷ Bx0-1423 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at243243 c4 = derive (X4 ∷ Bx0-1423 ∷ X4 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ [])
  (rw 1 (q35 c4) ∷
   rw⁻ 0 (q36 c4) ∷
   rw 2 (q37 c4) ∷
   rw⁻ 1 (q38 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 8 (q40 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw⁻ 2 (q36 c4) ∷
   rw 3 (q45 c4) ∷
   rw 4 (q46 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q47 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = sE 162 (lem-box-tQ-at243243 c4)
  q49 : Ws → Eqn
  q49 c4 = wpE 51 c4
  q50 : Ws → Eqn
  q50 c4 = sE 838 (lem-t-cP-at243243 c4)
  q51 : Ws → Eqn
  q51 c4 = wlE 204 (lit c4)

-- box2 @243243: 11 steps
lem-box2-at243243 : Ws → ⟪ (Bx0-1423 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at243243 c4 = derive (Bx0-1423 ∷ Bx0-1423 ∷ []) []
  (rw 0 (q48 c4) ∷
   rw 4 (q35 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   rw 5 (q50 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   rw 5 (q48 c4) ∷
   rw 4 (q49 c4) ∷
   rw 3 (q51 c4) ∷
   rw 2 (q49 c4) ∷
   rw 1 (q51 c4) ∷
   rw 0 (q49 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = sE 850 (lem-box-cP-at122441 c4)
  q53 : Ws → Eqn
  q53 c4 = wlE 232 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Toff013 ∷ X4 ∷ []) (X4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))
  q55 : Ws → Eqn
  q55 c4 = wlE 233 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wpE 81 c4
  q57 : Ws → Eqn
  q57 c4 = wpE 82 c4
  q58 : Ws → Eqn
  q58 c4 = wlE 234 (lit c4)

-- Xb-box @122441: 18 steps
lem-Xb-box-at122441 : Ws → ⟪ (X4 ∷ Bx0-2431 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at122441 c4 = derive (X4 ∷ Bx0-2431 ∷ X4 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ [])
  (rw 1 (q52 c4) ∷
   rw⁻ 0 (q19 c4) ∷
   rw 2 (q53 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw 4 (q55 c4) ∷
   rw⁻ 8 (q56 c4) ∷
   rw⁻ 7 (q57 c4) ∷
   rw 6 (q25 c4) ∷
   rw⁻ 5 (q57 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 5 (q55 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 3 (q28 c4) ∷
   rw 4 (q58 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw⁻ 0 (q52 c4) ∷
   rw⁻ 1 (q47 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = sE 156 (lem-box-tQ-at122441 c4)
  q60 : Ws → Eqn
  q60 c4 = wpE 80 c4
  q61 : Ws → Eqn
  q61 c4 = sE 837 (lem-t-cP-at122441 c4)
  q62 : Ws → Eqn
  q62 c4 = wlE 230 (lit c4)

-- box2 @122441: 11 steps
lem-box2-at122441 : Ws → ⟪ (Bx0-2431 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at122441 c4 = derive (Bx0-2431 ∷ Bx0-2431 ∷ []) []
  (rw 0 (q59 c4) ∷
   rw 4 (q52 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 5 (q52 c4) ∷
   rw 5 (q59 c4) ∷
   rw 4 (q60 c4) ∷
   rw 3 (q62 c4) ∷
   rw 2 (q60 c4) ∷
   rw 1 (q62 c4) ∷
   rw 0 (q60 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = sE 823 (lem-P-box c4)
  q64 : Ws → Eqn
  q64 c4 = wpE 6 c4
  q65 : Ws → Eqn
  q65 c4 = sE 27 (lem-box-tQ-at13243142 c4)

-- pairs: 4 steps
lem-pairs : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-pairs c4 = derive (Bx0-1234 ∷ []) (Bx0-3412 ∷ [])
  (rw⁻ 0 (q63 c4) ∷
   rw 1 (q2 c4) ∷
   rw 4 (q64 c4) ∷
   rw⁻ 0 (q65 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = sE 861 (lem-sym-bc c4)

-- box-perm-1324: 1 steps
lem-box-perm-1324 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-box-perm-1324 c4 = derive (Bx0-1234 ∷ []) (Bx0-1324 ∷ [])
  (rw 0 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = sE 10 (lem-sym-ab c4)
  q68 : Ws → Eqn
  q68 c4 = sE 865 (lem-sym-bc-at1221 c4)

-- box-perm-2314: 2 steps
lem-box-perm-2314 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-box-perm-2314 c4 = derive (Bx0-1234 ∷ []) (Bx0-2314 ∷ [])
  (rw 0 (q67 c4) ∷
   rw 0 (q68 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = sE 827 (lem-P-box-at1221 c4)
  q70 : Ws → Eqn
  q70 c4 = sE 848 (lem-box-cP-at1221 c4)
  q71 : Ws → Eqn
  q71 c4 = sE 28 (lem-box-tQ-at13243241 c4)

-- pairs @1221: 4 steps
lem-pairs-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-pairs-at1221 c4 = derive (Bx0-2134 ∷ []) (Bx0-3421 ∷ [])
  (rw⁻ 0 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   rw 4 (q64 c4) ∷
   rw⁻ 0 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = sE 821 (lem-sym-ab-at2332 c4)

-- box-perm-3124: 2 steps
lem-box-perm-3124 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-box-perm-3124 c4 = derive (Bx0-1234 ∷ []) (Bx0-3124 ∷ [])
  (rw 0 (q66 c4) ∷
   rw 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = sE 832 (lem-P-box-at2332 c4)
  q74 : Ws → Eqn
  q74 c4 = sE 855 (lem-box-cP-at2332 c4)
  q75 : Ws → Eqn
  q75 c4 = sE 155 (lem-box-tQ-at12243143 c4)

-- pairs @2332: 4 steps
lem-pairs-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-pairs-at2332 c4 = derive (Bx0-1324 ∷ []) (Bx0-2413 ∷ [])
  (rw⁻ 0 (q73 c4) ∷
   rw 1 (q74 c4) ∷
   rw 4 (q60 c4) ∷
   rw⁻ 0 (q75 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = sE 818 (lem-sym-ab-at122331 c4)

-- box-perm-3214: 3 steps
lem-box-perm-3214 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-box-perm-3214 c4 = derive (Bx0-1234 ∷ []) (Bx0-3214 ∷ [])
  (rw 0 (q67 c4) ∷
   rw 0 (q68 c4) ∷
   rw 0 (q76 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = sE 828 (lem-P-box-at122331 c4)
  q78 : Ws → Eqn
  q78 c4 = sE 849 (lem-box-cP-at122331 c4)

-- pairs @122331: 4 steps
lem-pairs-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-pairs-at122331 c4 = derive (Bx0-2314 ∷ []) (Bx0-1423 ∷ [])
  (rw⁻ 0 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 4 (q49 c4) ∷
   rw⁻ 0 (q48 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = sE 829 (lem-P-box-at132132 c4)
  q80 : Ws → Eqn
  q80 c4 = sE 851 (lem-box-cP-at132132 c4)

-- pairs @132132: 4 steps
lem-pairs-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-pairs-at132132 c4 = derive (Bx0-3124 ∷ []) (Bx0-2431 ∷ [])
  (rw⁻ 0 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 4 (q60 c4) ∷
   rw⁻ 0 (q59 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = sE 830 (lem-P-box-at13213442 c4)
  q82 : Ws → Eqn
  q82 c4 = sE 852 (lem-box-cP-at13213442 c4)
  q83 : Ws → Eqn
  q83 c4 = sE 196 (lem-box-tQ-at1441 c4)

-- pairs @13213442: 4 steps
lem-pairs-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-pairs-at13213442 c4 = derive (Bx0-3142 ∷ []) (Bx0-4231 ∷ [])
  (rw⁻ 0 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 4 (q60 c4) ∷
   rw⁻ 0 (q83 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = sE 831 (lem-P-box-at1331 c4)
  q85 : Ws → Eqn
  q85 c4 = sE 853 (lem-box-cP-at1331 c4)
  q86 : Ws → Eqn
  q86 c4 = sE 220 (lem-box-tQ-at2442 c4)

-- pairs @1331: 4 steps
lem-pairs-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-pairs-at1331 c4 = derive (Bx0-3214 ∷ []) (Bx0-1432 ∷ [])
  (rw⁻ 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 4 (q49 c4) ∷
   rw⁻ 0 (q86 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = wlE 345 (lit c4)
  q88 : Ws → Eqn
  q88 c4 = wpE 219 c4

-- Ku-box: 6 steps
lem-Ku-box : Ws → ⟪ (K0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0 ∷ []) ⟫ʷ
lem-Ku-box c4 = derive (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ [])
  (rw 1 (q1 c4) ∷
   rw⁻ 0 (q87 c4) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 2 (q87 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 0 (q2 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = wlE 346 (lit c4)
  q90 : Ws → Eqn
  q90 c4 = wpE 220 c4

-- Kdu-box: 6 steps
lem-Kdu-box : Ws → ⟪ (K0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ
lem-Kdu-box c4 = derive (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ [])
  (rw 1 (q1 c4) ∷
   rw⁻ 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 3 (q90 c4) ∷
   rw⁻ 0 (q2 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = wlE 268 (lit c4)
  q92 : Ws → Eqn
  q92 c4 = wpE 230 c4
  q93 : Ws → Eqn
  q93 c4 = wpE 231 c4
  q94 : Ws → Eqn
  q94 c4 = wpE 117 c4
  q95 : Ws → Eqn
  q95 c4 = wlE 381 (lit c4)
  q96 : Ws → Eqn
  q96 c4 = wpE 232 c4
  q97 : Ws → Eqn
  q97 c4 = wpE 233 c4
  q98 : Ws → Eqn
  q98 c4 = wpE 234 c4

-- CSu-box-3: 17 steps
lem-CSu-box-3 : Ws → ⟪ (CS03 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS03 ∷ []) ⟫ʷ
lem-CSu-box-3 c4 = derive (CS03 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS03 ∷ [])
  (rw 1 (q2 c4) ∷
   rw⁻ 0 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   rw 4 (q93 c4) ∷
   rw⁻ 8 (q94 c4) ∷
   rw⁻ 7 (q95 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 5 (q95 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 5 (q93 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw⁻ 2 (q91 c4) ∷
   rw 5 (q96 c4) ∷
   rw 4 (q97 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q98 c4) ∷
   rw⁻ 0 (q2 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = wlE 328 (lit c4)
  q100 : Ws → Eqn
  q100 c4 = wpE 235 c4
  q101 : Ws → Eqn
  q101 c4 = wpE 236 c4
  q102 : Ws → Eqn
  q102 c4 = wpE 237 c4

-- CSdu-box-3: 17 steps
lem-CSdu-box-3 : Ws → ⟪ (CS03⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3 c4 = derive (CS03⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS03⁻ ∷ [])
  (rw 1 (q2 c4) ∷
   rw⁻ 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 4 (q93 c4) ∷
   rw⁻ 8 (q94 c4) ∷
   rw⁻ 7 (q95 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 5 (q95 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 5 (q93 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 2 (q99 c4) ∷
   rw 5 (q96 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q100 c4) ∷
   rw 4 (q102 c4) ∷
   rw⁻ 0 (q2 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = wlE 382 (lit c4)
  q104 : Ws → Eqn
  q104 c4 = wpE 238 c4
  q105 : Ws → Eqn
  q105 c4 = eqn (CCZ012 ∷ CZ34 ∷ []) (CZ34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CZ))
  q106 : Ws → Eqn
  q106 c4 = wpE 239 c4
  q107 : Ws → Eqn
  q107 c4 = wpE 240 c4

-- CZu-box-3: 9 steps
lem-CZu-box-3 : Ws → ⟪ (CZ03 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ03 ∷ []) ⟫ʷ
lem-CZu-box-3 c4 = derive (CZ03 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CZ03 ∷ [])
  (rw 1 (q2 c4) ∷
   rw⁻ 0 (q103 c4) ∷
   rw 1 (q104 c4) ∷
   rw⁻ 3 (q105 c4) ∷
   rw⁻ 2 (q103 c4) ∷
   rw 4 (q106 c4) ∷
   rw 3 (q104 c4) ∷
   rw 4 (q107 c4) ∷
   rw⁻ 0 (q2 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = wlE 383 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = wpE 171 c4
  q110 : Ws → Eqn
  q110 c4 = eqn (CX12 ∷ Toff034 ∷ []) (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = wpE 241 c4
  q112 : Ws → Eqn
  q112 c4 = wpE 146 c4
  q113 : Ws → Eqn
  q113 c4 = wpE 242 c4
  q114 : Ws → Eqn
  q114 c4 = wlE 298 (lit c4)
  q115 : Ws → Eqn
  q115 c4 = wlE 384 (lit c4)

-- CXu-box-3: 15 steps
lem-CXu-box-3 : Ws → ⟪ (CX30 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX30 ∷ []) ⟫ʷ
lem-CXu-box-3 c4 = derive (CX30 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CX30 ∷ [])
  (rw 1 (q2 c4) ∷
   rw⁻ 0 (q108 c4) ∷
   rw 2 (q39 c4) ∷
   rw 6 (q109 c4) ∷
   rw 5 (q110 c4) ∷
   rw 4 (q111 c4) ∷
   rw 3 (q110 c4) ∷
   rw 2 (q112 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   rw 1 (q113 c4) ∷
   rw⁻ 3 (q114 c4) ∷
   rw⁻ 2 (q108 c4) ∷
   rw 3 (q115 c4) ∷
   rw 3 (q113 c4) ∷
   rw⁻ 0 (q2 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = wpE 243 c4
  q117 : Ws → Eqn
  q117 c4 = wpE 244 c4

-- CSu-box-4: 17 steps
lem-CSu-box-4 : Ws → ⟪ (CS04 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS04 ∷ []) ⟫ʷ
lem-CSu-box-4 c4 = derive (CS04 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS04 ∷ [])
  (rw 1 (q2 c4) ∷
   rw⁻ 0 (q94 c4) ∷
   rw 1 (q116 c4) ∷
   rw 4 (q93 c4) ∷
   rw⁻ 8 (q94 c4) ∷
   rw⁻ 7 (q95 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 5 (q95 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 5 (q93 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw⁻ 2 (q94 c4) ∷
   rw 5 (q96 c4) ∷
   rw 4 (q97 c4) ∷
   rw 3 (q116 c4) ∷
   rw 4 (q117 c4) ∷
   rw⁻ 0 (q2 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = wpE 116 c4
  q119 : Ws → Eqn
  q119 c4 = wpE 245 c4
  q120 : Ws → Eqn
  q120 c4 = wpE 246 c4

-- CSdu-box-4: 17 steps
lem-CSdu-box-4 : Ws → ⟪ (CS04⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-4 c4 = derive (CS04⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS04⁻ ∷ [])
  (rw 1 (q2 c4) ∷
   rw⁻ 0 (q118 c4) ∷
   rw 1 (q119 c4) ∷
   rw 4 (q93 c4) ∷
   rw⁻ 8 (q94 c4) ∷
   rw⁻ 7 (q95 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 5 (q95 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 5 (q93 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 2 (q118 c4) ∷
   rw 5 (q96 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q119 c4) ∷
   rw 4 (q120 c4) ∷
   rw⁻ 0 (q2 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = wpE 247 c4
  q122 : Ws → Eqn
  q122 c4 = wpE 248 c4
  q123 : Ws → Eqn
  q123 c4 = wpE 249 c4

-- CZu-box-4: 9 steps
lem-CZu-box-4 : Ws → ⟪ (CZ04 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ04 ∷ []) ⟫ʷ
lem-CZu-box-4 c4 = derive (CZ04 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CZ04 ∷ [])
  (rw 1 (q2 c4) ∷
   rw⁻ 0 (q121 c4) ∷
   rw 1 (q122 c4) ∷
   rw⁻ 3 (q105 c4) ∷
   rw⁻ 2 (q121 c4) ∷
   rw 4 (q106 c4) ∷
   rw 3 (q122 c4) ∷
   rw 4 (q123 c4) ∷
   rw⁻ 0 (q2 c4) ∷ []) Eq.refl

private
  q124 : Ws → Eqn
  q124 c4 = wpE 250 c4
  q125 : Ws → Eqn
  q125 c4 = wlE 256 (lit c4)
  q126 : Ws → Eqn
  q126 c4 = wpE 251 c4
  q127 : Ws → Eqn
  q127 c4 = wpE 252 c4
  q128 : Ws → Eqn
  q128 c4 = wpE 202 c4
  q129 : Ws → Eqn
  q129 c4 = wpE 253 c4
  q130 : Ws → Eqn
  q130 c4 = wpE 205 c4
  q131 : Ws → Eqn
  q131 c4 = wpE 254 c4

-- CXu-box-4: 15 steps
lem-CXu-box-4 : Ws → ⟪ (CX40 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX40 ∷ []) ⟫ʷ
lem-CXu-box-4 c4 = derive (CX40 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CX40 ∷ [])
  (rw 1 (q2 c4) ∷
   rw⁻ 0 (q124 c4) ∷
   rw 2 (q125 c4) ∷
   rw 6 (q126 c4) ∷
   rw 5 (q110 c4) ∷
   rw 4 (q127 c4) ∷
   rw 3 (q110 c4) ∷
   rw 2 (q128 c4) ∷
   rw⁻ 3 (q125 c4) ∷
   rw 1 (q129 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw⁻ 2 (q124 c4) ∷
   rw 3 (q131 c4) ∷
   rw 3 (q129 c4) ∷
   rw⁻ 0 (q2 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = sE 819 (lem-sym-ab-at12233441 c4)
  q133 : Ws → Eqn
  q133 c4 = sE 868 (lem-sym-bc-at133441 c4)
  q134 : Ws → Eqn
  q134 c4 = sE 859 (lem-pairs-at13243241 c4)
  q135 : Ws → Eqn
  q135 c4 = sE 16 (lem-sym-ab-at1221 c4)

-- box-perm-4123 @12233441: 4 steps
lem-box-perm-4123-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-4123-at12233441 c4 = derive (Bx0-2341 ∷ []) (Bx0-1234 ∷ [])
  (rw 0 (q132 c4) ∷
   rw 0 (q133 c4) ∷
   rw 0 (q134 c4) ∷
   rw 0 (q135 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = sE 822 (lem-sym-ab-at233442 c4)
  q137 : Ws → Eqn
  q137 c4 = sE 867 (lem-sym-bc-at13213442 c4)
  q138 : Ws → Eqn
  q138 c4 = sE 858 (lem-pairs-at13243142 c4)

-- box-perm-1423 @233442: 3 steps
lem-box-perm-1423-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1423-at233442 c4 = derive (Bx0-1342 ∷ []) (Bx0-1234 ∷ [])
  (rw 0 (q136 c4) ∷
   rw 0 (q137 c4) ∷
   rw 0 (q138 c4) ∷ []) Eq.refl

private
  q139 : Ws → Eqn
  q139 c4 = sE 833 (lem-P-box-at3443 c4)
  q140 : Ws → Eqn
  q140 c4 = sE 857 (lem-box-cP-at3443 c4)
  q141 : Ws → Eqn
  q141 c4 = sE 29 (lem-box-tQ-at14233142 c4)

-- pairs @3443: 4 steps
lem-pairs-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-pairs-at3443 c4 = derive (Bx0-1243 ∷ []) (Bx0-4312 ∷ [])
  (rw⁻ 0 (q139 c4) ∷
   rw 1 (q140 c4) ∷
   rw 4 (q64 c4) ∷
   rw⁻ 0 (q141 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = sE 847 (lem-box-cP-at043043 c4)
  q143 : Ws → Eqn
  q143 c4 = wpE 318 c4
  q144 : Ws → Eqn
  q144 c4 = wpE 319 c4
  q145 : Ws → Eqn
  q145 c4 = wpE 320 c4
  q146 : Ws → Eqn
  q146 c4 = wlE 471 (lit c4)
  q147 : Ws → Eqn
  q147 c4 = wpE 321 c4
  q148 : Ws → Eqn
  q148 c4 = eqn (CS03⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (CS03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4))
  q150 : Ws → Eqn
  q150 c4 = wpE 322 c4
  q151 : Ws → Eqn
  q151 c4 = wpE 323 c4
  q152 : Ws → Eqn
  q152 c4 = wpE 324 c4

-- CSdu-box-3 @043043: 17 steps
lem-CSdu-box-3-at043043 : Ws → ⟪ (CS04⁻ ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at043043 c4 = derive (CS04⁻ ∷ Bx4-1203 ∷ []) (Bx4-1203 ∷ CS04⁻ ∷ [])
  (rw 1 (q142 c4) ∷
   rw⁻ 0 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   rw 4 (q145 c4) ∷
   rw⁻ 8 (q146 c4) ∷
   rw⁻ 7 (q147 c4) ∷
   rw 6 (q148 c4) ∷
   rw⁻ 5 (q147 c4) ∷
   rw 4 (q149 c4) ∷
   rw⁻ 5 (q145 c4) ∷
   rw 3 (q148 c4) ∷
   rw⁻ 2 (q143 c4) ∷
   rw 5 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw 3 (q144 c4) ∷
   rw 4 (q152 c4) ∷
   rw⁻ 0 (q142 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = sE 864 (lem-sym-bc-at043043 c4)

-- box-perm-1324 @043043: 1 steps
lem-box-perm-1324-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-box-perm-1324-at043043 c4 = derive (Bx4-1203 ∷ []) (Bx4-1023 ∷ [])
  (rw 0 (q153 c4) ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = sE 817 (lem-sym-ab-at04203243 c4)

-- box-perm-3124 @043043: 2 steps
lem-box-perm-3124-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-box-perm-3124-at043043 c4 = derive (Bx4-1203 ∷ []) (Bx4-0123 ∷ [])
  (rw 0 (q153 c4) ∷
   rw 0 (q154 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = sE 826 (lem-P-box-at0330 c4)
  q156 : Ws → Eqn
  q156 c4 = sE 846 (lem-box-cP-at0330 c4)
  q157 : Ws → Eqn
  q157 c4 = wpE 351 c4
  q158 : Ws → Eqn
  q158 c4 = sE 150 (lem-box-tQ-at0310243142 c4)

-- pairs @0330: 4 steps
lem-pairs-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-pairs-at0330 c4 = derive (Bx3-1204 ∷ []) (Bx3-0412 ∷ [])
  (rw⁻ 0 (q155 c4) ∷
   rw 1 (q156 c4) ∷
   rw 4 (q157 c4) ∷
   rw⁻ 0 (q158 c4) ∷ []) Eq.refl

private
  q159 : Ws → Eqn
  q159 c4 = sE 79 (lem-box-tQ-at0410213243 c4)
  q160 : Ws → Eqn
  q160 c4 = sE 845 (lem-box-cP-at0314203142 c4)
  q161 : Ws → Eqn
  q161 c4 = wpE 129 c4
  q162 : Ws → Eqn
  q162 c4 = wlE 496 (lit c4)
  q163 : Ws → Eqn
  q163 c4 = wlE 334 (lit c4)
  q164 : Ws → Eqn
  q164 c4 = wpE 108 c4
  q165 : Ws → Eqn
  q165 c4 = wpE 357 c4
  q166 : Ws → Eqn
  q166 c4 = eqn (CS12⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4))
  q167 : Ws → Eqn
  q167 c4 = eqn (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4))
  q168 : Ws → Eqn
  q168 c4 = wlE 497 (lit c4)
  q169 : Ws → Eqn
  q169 c4 = wpE 332 c4
  q170 : Ws → Eqn
  q170 c4 = wlE 498 (lit c4)
  q171 : Ws → Eqn
  q171 c4 = wpE 358 c4
  q172 : Ws → Eqn
  q172 c4 = eqn (Toff312 ∷ K4⁻ ∷ []) (K4⁻ ∷ Toff312 ∷ []) (c₄ (Toffᵗ ↑) (K • iI))
  q173 : Ws → Eqn
  q173 c4 = wlE 499 (lit c4)
  q174 : Ws → Eqn
  q174 c4 = eqn (CX40 ∷ Toff312 ∷ []) (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4))
  q175 : Ws → Eqn
  q175 c4 = wlE 500 (lit c4)
  q176 : Ws → Eqn
  q176 c4 = wlE 501 (lit c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (Toff312 ∷ K4 ∷ []) (K4 ∷ Toff312 ∷ []) (c₄ (Toffᵗ ↑) (K))
  q178 : Ws → Eqn
  q178 c4 = wpE 186 c4
  q179 : Ws → Eqn
  q179 c4 = wlE 348 (lit c4)
  q180 : Ws → Eqn
  q180 c4 = wpE 3 c4
  q181 : Ws → Eqn
  q181 c4 = wpE 221 c4
  q182 : Ws → Eqn
  q182 c4 = wlE 502 (lit c4)
  q183 : Ws → Eqn
  q183 c4 = wlE 503 (lit c4)
  q184 : Ws → Eqn
  q184 c4 = wpE 279 c4
  q185 : Ws → Eqn
  q185 c4 = eqn (CX01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ))
  q186 : Ws → Eqn
  q186 c4 = wlE 414 (lit c4)
  q187 : Ws → Eqn
  q187 c4 = wlE 415 (lit c4)
  q188 : Ws → Eqn
  q188 c4 = wpE 359 c4
  q189 : Ws → Eqn
  q189 c4 = wlE 341 (lit c4)

-- box-box-4 @0410213243: 103 steps
lem-box-box-4-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-box-box-4-at0410213243 c4 = derive (Bx4-0123 ∷ Bx3-4012 ∷ []) (Bx3-4012 ∷ Bx4-0123 ∷ [])
  (rw 0 (q159 c4) ∷
   rw 4 (q160 c4) ∷
   rw⁻ 3 (q161 c4) ∷
   rw 4 (q162 c4) ∷
   rw⁻ 6 (q161 c4) ∷
   rw 5 (q163 c4) ∷
   rw⁻ 9 (q164 c4) ∷
   rw⁻ 8 (q165 c4) ∷
   rw 7 (q166 c4) ∷
   rw⁻ 6 (q165 c4) ∷
   rw 5 (q167 c4) ∷
   rw⁻ 6 (q163 c4) ∷
   rw 6 (q168 c4) ∷
   rw⁻ 3 (q160 c4) ∷
   rw 3 (q160 c4) ∷
   rw⁻ 2 (q169 c4) ∷
   rw 4 (q170 c4) ∷
   rw⁻ 3 (q171 c4) ∷
   rw⁻ 9 (q172 c4) ∷
   rw 8 (q173 c4) ∷
   rw 7 (q174 c4) ∷
   rw 6 (q175 c4) ∷
   rw 5 (q174 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 3 (q177 c4) ∷
   rw 4 (q171 c4) ∷
   rw 6 (q178 c4) ∷
   rw 5 (q179 c4) ∷
   rw⁻ 9 (q180 c4) ∷
   rw⁻ 8 (q181 c4) ∷
   rw 7 (q166 c4) ∷
   rw⁻ 6 (q181 c4) ∷
   rw 5 (q167 c4) ∷
   rw⁻ 6 (q179 c4) ∷
   rw⁻ 4 (q169 c4) ∷
   rw⁻ 6 (q182 c4) ∷
   rw 6 (q183 c4) ∷
   rw⁻ 5 (q171 c4) ∷
   rw⁻ 11 (q172 c4) ∷
   rw 10 (q173 c4) ∷
   rw 9 (q174 c4) ∷
   rw 8 (q175 c4) ∷
   rw 7 (q174 c4) ∷
   rw 6 (q176 c4) ∷
   rw⁻ 5 (q177 c4) ∷
   rw 6 (q171 c4) ∷
   rw⁻ 2 (q160 c4) ∷
   rw 2 (q160 c4) ∷
   rw⁻ 1 (q161 c4) ∷
   rw 2 (q162 c4) ∷
   rw⁻ 4 (q161 c4) ∷
   rw 3 (q163 c4) ∷
   rw⁻ 7 (q164 c4) ∷
   rw⁻ 6 (q165 c4) ∷
   rw 5 (q166 c4) ∷
   rw⁻ 4 (q165 c4) ∷
   rw 3 (q167 c4) ∷
   rw⁻ 4 (q163 c4) ∷
   rw 4 (q168 c4) ∷
   rw⁻ 1 (q160 c4) ∷
   rw 1 (q160 c4) ∷
   rw⁻ 0 (q169 c4) ∷
   rw 2 (q170 c4) ∷
   rw⁻ 1 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw 4 (q175 c4) ∷
   rw 3 (q174 c4) ∷
   rw 2 (q176 c4) ∷
   rw⁻ 1 (q177 c4) ∷
   rw 2 (q171 c4) ∷
   rw 4 (q178 c4) ∷
   rw 3 (q179 c4) ∷
   rw⁻ 7 (q180 c4) ∷
   rw⁻ 6 (q181 c4) ∷
   rw 5 (q166 c4) ∷
   rw⁻ 4 (q181 c4) ∷
   rw 3 (q167 c4) ∷
   rw⁻ 4 (q179 c4) ∷
   rw⁻ 2 (q169 c4) ∷
   rw⁻ 4 (q182 c4) ∷
   rw 4 (q183 c4) ∷
   rw⁻ 3 (q171 c4) ∷
   rw⁻ 9 (q172 c4) ∷
   rw 8 (q173 c4) ∷
   rw 7 (q174 c4) ∷
   rw 6 (q175 c4) ∷
   rw 5 (q174 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 3 (q177 c4) ∷
   rw 4 (q171 c4) ∷
   rw⁻ 0 (q160 c4) ∷
   rw 2 (q179 c4) ∷
   rw⁻ 6 (q184 c4) ∷
   rw 5 (q185 c4) ∷
   rw⁻ 4 (q186 c4) ∷
   rw 3 (q185 c4) ∷
   rw⁻ 2 (q187 c4) ∷
   rw⁻ 3 (q179 c4) ∷
   rw 3 (q188 c4) ∷
   rw 4 (q189 c4) ∷
   rw⁻ 1 (q159 c4) ∷ []) Eq.refl

private
  q190 : Ws → Eqn
  q190 c4 = sE 825 (lem-P-box-at0310243142 c4)
  q191 : Ws → Eqn
  q191 c4 = sE 844 (lem-box-cP-at0310243142 c4)
  q192 : Ws → Eqn
  q192 c4 = wlE 489 (lit c4)
  q193 : Ws → Eqn
  q193 c4 = sE 151 (lem-box-tQ-at0330 c4)

-- pairs @0310243142: 4 steps
lem-pairs-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-pairs-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-1204 ∷ [])
  (rw⁻ 0 (q190 c4) ∷
   rw 1 (q191 c4) ∷
   rw 4 (q192 c4) ∷
   rw⁻ 0 (q193 c4) ∷ []) Eq.refl

private
  q194 : Ws → Eqn
  q194 c4 = wpE 384 c4
  q195 : Ws → Eqn
  q195 c4 = wpE 385 c4
  q196 : Ws → Eqn
  q196 c4 = wpE 386 c4
  q197 : Ws → Eqn
  q197 c4 = wpE 387 c4

-- CSu-box-3 @043043: 17 steps
lem-CSu-box-3-at043043 : Ws → ⟪ (CS04 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ CS04 ∷ []) ⟫ʷ
lem-CSu-box-3-at043043 c4 = derive (CS04 ∷ Bx4-1203 ∷ []) (Bx4-1203 ∷ CS04 ∷ [])
  (rw 1 (q142 c4) ∷
   rw⁻ 0 (q194 c4) ∷
   rw 1 (q195 c4) ∷
   rw 4 (q145 c4) ∷
   rw⁻ 8 (q146 c4) ∷
   rw⁻ 7 (q147 c4) ∷
   rw 6 (q148 c4) ∷
   rw⁻ 5 (q147 c4) ∷
   rw 4 (q149 c4) ∷
   rw⁻ 5 (q145 c4) ∷
   rw 3 (q149 c4) ∷
   rw⁻ 2 (q194 c4) ∷
   rw 5 (q150 c4) ∷
   rw 4 (q196 c4) ∷
   rw 3 (q195 c4) ∷
   rw 4 (q197 c4) ∷
   rw⁻ 0 (q142 c4) ∷ []) Eq.refl

private
  q198 : Ws → Eqn
  q198 c4 = sE 152 (lem-box-tQ-at043043 c4)
  q199 : Ws → Eqn
  q199 c4 = wlE 470 (lit c4)
  q200 : Ws → Eqn
  q200 c4 = sE 836 (lem-t-cP-at043043 c4)

-- box2 @043043: 11 steps
lem-box2-at043043 : Ws → ⟪ (Bx4-1203 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at043043 c4 = derive (Bx4-1203 ∷ Bx4-1203 ∷ []) []
  (rw 0 (q198 c4) ∷
   rw 4 (q142 c4) ∷
   rw⁻ 4 (q199 c4) ∷
   rw 5 (q200 c4) ∷
   rw⁻ 5 (q142 c4) ∷
   rw 5 (q198 c4) ∷
   rw 4 (q199 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q199 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q199 c4) ∷ []) Eq.refl

private
  q201 : Ws → Eqn
  q201 c4 = sE 863 (lem-sym-bc-at0330 c4)
  q202 : Ws → Eqn
  q202 c4 = sE 15 (lem-sym-ab-at032032 c4)

-- box-perm-3124 @0330: 2 steps
lem-box-perm-3124-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-3124-at0330 c4 = derive (Bx3-1204 ∷ []) (Bx3-0124 ∷ [])
  (rw 0 (q201 c4) ∷
   rw 0 (q202 c4) ∷ []) Eq.refl

private
  q203 : Ws → Eqn
  q203 c4 = sE 840 (lem-CXu-box-4-at03102132 c4)
  q204 : Ws → Eqn
  q204 c4 = wlE 545 (lit c4)
  q205 : Ws → Eqn
  q205 c4 = eqn (Toff312 ∷ CS04 ∷ []) (CS04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CS04 (lit c4))
  q206 : Ws → Eqn
  q206 c4 = wpE 396 c4
  q207 : Ws → Eqn
  q207 c4 = wlE 546 (lit c4)
  q208 : Ws → Eqn
  q208 c4 = wpE 397 c4

-- CXAu-S: 12 steps
lem-CXAu-S : Ws → ⟪ (CX43 ∷ Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-12-4 ∷ CX43 ∷ []) ⟫ʷ
lem-CXAu-S c4 = derive (CX43 ∷ Sb3-0-12-4 ∷ []) (Sb3-0-12-4 ∷ CX43 ∷ [])
  (re 1 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) ∷
   re 3 1 (CS04 ∷ []) ∷
   re 5 1 (CS04⁻ ∷ []) ∷
   rw 0 (q203 c4) ∷
   rw 1 (q204 c4) ∷
   rw 3 (q205 c4) ∷
   rw⁻ 2 (q206 c4) ∷
   rw 3 (q207 c4) ∷
   rw⁻ 4 (q208 c4) ∷
   re 2 1 (Sb3-0-4-2 ∷ []) ∷
   re 4 1 (Sb⁻3-0-4-2 ∷ []) ∷
   re 0 5 (Sb3-0-12-4 ∷ []) ∷ []) Eq.refl

private
  q209 : Ws → Eqn
  q209 c4 = wpE 405 c4
  q210 : Ws → Eqn
  q210 c4 = wlE 556 (lit c4)
  q211 : Ws → Eqn
  q211 c4 = wpE 406 c4
  q212 : Ws → Eqn
  q212 c4 = wlE 557 (lit c4)

-- F4-I-CS0: 15 steps
lem-F4-I-CS0 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-CS0 c4 = derive (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 0 (q209 c4) ∷
   rw⁻ 1 (q210 c4) ∷
   rw⁻ 2 (q209 c4) ∷
   rw⁻ 3 (q210 c4) ∷
   rw⁻ 0 (q18 c4) ∷
   rw⁻ 1 (q211 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷
   rw 1 (q212 c4) ∷
   rw⁻ 1 (q212 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = wpE 407 c4
  q214 : Ws → Eqn
  q214 c4 = wpE 408 c4
  q215 : Ws → Eqn
  q215 c4 = wlE 558 (lit c4)

-- F4-I-CS1: 15 steps
lem-F4-I-CS1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-CS1 c4 = derive (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 0 (q213 c4) ∷
   rw⁻ 1 (q214 c4) ∷
   rw⁻ 2 (q213 c4) ∷
   rw⁻ 3 (q214 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q215 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷
   rw 1 (q212 c4) ∷
   rw⁻ 1 (q212 c4) ∷ []) Eq.refl

private
  q216 : Ws → Eqn
  q216 c4 = wpE 409 c4
  q217 : Ws → Eqn
  q217 c4 = wlE 559 (lit c4)

-- F4-I-CS2: 15 steps
lem-F4-I-CS2 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-CS2 c4 = derive (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 0 (q209 c4) ∷
   rw⁻ 1 (q216 c4) ∷
   rw⁻ 2 (q209 c4) ∷
   rw⁻ 3 (q216 c4) ∷
   rw⁻ 0 (q52 c4) ∷
   rw⁻ 1 (q217 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷
   rw 1 (q212 c4) ∷
   rw⁻ 1 (q212 c4) ∷ []) Eq.refl

private
  q218 : Ws → Eqn
  q218 c4 = wpE 419 c4
  q219 : Ws → Eqn
  q219 c4 = eqn (CS04 ∷ Toff213 ∷ []) (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4))
  q220 : Ws → Eqn
  q220 c4 = wpE 257 c4
  q221 : Ws → Eqn
  q221 c4 = wpE 420 c4
  q222 : Ws → Eqn
  q222 c4 = eqn (CS04⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4))
  q223 : Ws → Eqn
  q223 c4 = eqn (S0 ∷ Toff213 ∷ []) (Toff213 ∷ S0 ∷ []) (c₁ (S) (K ↑ • CCZ • K ↑ • iI))
  q224 : Ws → Eqn
  q224 c4 = wpE 421 c4

-- F4-S0-CS0: 18 steps
lem-F4-S0-CS0 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-CS0 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 0 (q218 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw 2 (q219 c4) ∷
   rw⁻ 1 (q21 c4) ∷
   rw⁻ 2 (q220 c4) ∷
   rw⁻ 2 (q221 c4) ∷
   rw 4 (q222 c4) ∷
   rw 3 (q223 c4) ∷
   rw⁻ 0 (q18 c4) ∷
   rw 1 (q224 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷
   rw 1 (q220 c4) ∷ []) Eq.refl

private
  q225 : Ws → Eqn
  q225 c4 = wpE 442 c4
  q226 : Ws → Eqn
  q226 c4 = wlE 570 (lit c4)
  q227 : Ws → Eqn
  q227 c4 = wpE 443 c4
  q228 : Ws → Eqn
  q228 c4 = wlE 571 (lit c4)

-- F4-S1-CS0: 15 steps
lem-F4-S1-CS0 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-CS0 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 0 (q225 c4) ∷
   rw⁻ 1 (q226 c4) ∷
   rw⁻ 2 (q225 c4) ∷
   rw⁻ 3 (q226 c4) ∷
   rw⁻ 0 (q18 c4) ∷
   rw⁻ 1 (q227 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 1 (q228 c4) ∷
   rw 1 (q228 c4) ∷ []) Eq.refl

private
  q229 : Ws → Eqn
  q229 c4 = wpE 444 c4
  q230 : Ws → Eqn
  q230 c4 = eqn (CS14 ∷ Toff023 ∷ []) (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 (lit c4))
  q231 : Ws → Eqn
  q231 c4 = wpE 445 c4
  q232 : Ws → Eqn
  q232 c4 = eqn (CS14⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4))
  q233 : Ws → Eqn
  q233 c4 = wlE 572 (lit c4)
  q234 : Ws → Eqn
  q234 c4 = wlE 573 (lit c4)

-- F4-S1-CS1: 18 steps
lem-F4-S1-CS1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-CS1 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 0 (q229 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 2 (q230 c4) ∷
   rw⁻ 1 (q38 c4) ∷
   rw⁻ 2 (q228 c4) ∷
   rw⁻ 2 (q231 c4) ∷
   rw 4 (q232 c4) ∷
   rw 3 (q233 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw 1 (q234 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷
   rw 1 (q228 c4) ∷ []) Eq.refl

private
  q235 : Ws → Eqn
  q235 c4 = wpE 446 c4
  q236 : Ws → Eqn
  q236 c4 = wlE 574 (lit c4)

-- F4-S1-CS2: 15 steps
lem-F4-S1-CS2 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-CS2 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 0 (q225 c4) ∷
   rw⁻ 1 (q235 c4) ∷
   rw⁻ 2 (q225 c4) ∷
   rw⁻ 3 (q235 c4) ∷
   rw⁻ 0 (q52 c4) ∷
   rw⁻ 1 (q236 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 1 (q228 c4) ∷
   rw 1 (q228 c4) ∷ []) Eq.refl

private
  q237 : Ws → Eqn
  q237 c4 = wpE 458 c4
  q238 : Ws → Eqn
  q238 c4 = wpE 459 c4
  q239 : Ws → Eqn
  q239 c4 = wlE 585 (lit c4)
  q240 : Ws → Eqn
  q240 c4 = wlE 583 (lit c4)

-- F4-S2-CS1: 15 steps
lem-F4-S2-CS1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-CS1 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 0 (q237 c4) ∷
   rw⁻ 1 (q238 c4) ∷
   rw⁻ 2 (q237 c4) ∷
   rw⁻ 3 (q238 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q239 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 1 (q240 c4) ∷
   rw 1 (q240 c4) ∷ []) Eq.refl

private
  q241 : Ws → Eqn
  q241 c4 = wpE 460 c4
  q242 : Ws → Eqn
  q242 c4 = eqn (CS24 ∷ Toff013 ∷ []) (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 (lit c4))
  q243 : Ws → Eqn
  q243 c4 = wpE 461 c4
  q244 : Ws → Eqn
  q244 c4 = eqn (CS24⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4))
  q245 : Ws → Eqn
  q245 c4 = wlE 586 (lit c4)
  q246 : Ws → Eqn
  q246 c4 = wlE 587 (lit c4)

-- F4-S2-CS2: 18 steps
lem-F4-S2-CS2 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-CS2 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 0 (q241 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw 2 (q242 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw⁻ 2 (q240 c4) ∷
   rw⁻ 2 (q243 c4) ∷
   rw 4 (q244 c4) ∷
   rw 3 (q245 c4) ∷
   rw⁻ 0 (q52 c4) ∷
   rw 1 (q246 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷
   rw 1 (q240 c4) ∷ []) Eq.refl

private
  q247 : Ws → Eqn
  q247 c4 = wpE 464 c4
  q248 : Ws → Eqn
  q248 c4 = wlE 595 (lit c4)
  q249 : Ws → Eqn
  q249 c4 = wpE 465 c4
  q250 : Ws → Eqn
  q250 c4 = wlE 596 (lit c4)

-- F4-S3-CS0: 15 steps
lem-F4-S3-CS0 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-CS0 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 0 (q247 c4) ∷
   rw⁻ 1 (q248 c4) ∷
   rw⁻ 2 (q247 c4) ∷
   rw⁻ 3 (q248 c4) ∷
   rw⁻ 0 (q18 c4) ∷
   rw⁻ 1 (q249 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 1 (q250 c4) ∷
   rw 1 (q250 c4) ∷ []) Eq.refl

private
  q251 : Ws → Eqn
  q251 c4 = wpE 466 c4
  q252 : Ws → Eqn
  q252 c4 = wpE 467 c4
  q253 : Ws → Eqn
  q253 c4 = wlE 597 (lit c4)

-- F4-S3-CS1: 15 steps
lem-F4-S3-CS1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-CS1 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 0 (q251 c4) ∷
   rw⁻ 1 (q252 c4) ∷
   rw⁻ 2 (q251 c4) ∷
   rw⁻ 3 (q252 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q253 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 1 (q250 c4) ∷
   rw 1 (q250 c4) ∷ []) Eq.refl

private
  q254 : Ws → Eqn
  q254 c4 = wpE 468 c4
  q255 : Ws → Eqn
  q255 c4 = wlE 598 (lit c4)

-- F4-S3-CS2: 15 steps
lem-F4-S3-CS2 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-CS2 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 0 (q247 c4) ∷
   rw⁻ 1 (q254 c4) ∷
   rw⁻ 2 (q247 c4) ∷
   rw⁻ 3 (q254 c4) ∷
   rw⁻ 0 (q52 c4) ∷
   rw⁻ 1 (q255 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 1 (q250 c4) ∷
   rw 1 (q250 c4) ∷ []) Eq.refl

private
  q256 : Ws → Eqn
  q256 c4 = wpE 478 c4
  q257 : Ws → Eqn
  q257 c4 = eqn (CK40 ∷ Toff213 ∷ []) (Toff213 ∷ CK40 ∷ []) (lem-comm-CK40-TOFF213 (lit c4))
  q258 : Ws → Eqn
  q258 c4 = wpE 479 c4

-- F4-K0-CS0: 17 steps
lem-F4-K0-CS0 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-CS0 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 0 (q256 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw 2 (q257 c4) ∷
   rw⁻ 1 (q21 c4) ∷
   rw⁻ 2 (q256 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw 4 (q257 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw⁻ 0 (q18 c4) ∷
   rw⁻ 1 (q258 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q259 : Ws → Eqn
  q259 c4 = wpE 482 c4
  q260 : Ws → Eqn
  q260 c4 = wlE 599 (lit c4)

-- Ku-box @243243: 6 steps
lem-Ku-box-at243243 : Ws → ⟪ (K0 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ K0 ∷ []) ⟫ʷ
lem-Ku-box-at243243 c4 = derive (K0 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ K0 ∷ [])
  (rw 1 (q48 c4) ∷
   rw⁻ 0 (q259 c4) ∷
   rw 1 (q260 c4) ∷
   rw⁻ 2 (q259 c4) ∷
   rw 3 (q260 c4) ∷
   rw⁻ 0 (q35 c4) ∷ []) Eq.refl

private
  q261 : Ws → Eqn
  q261 c4 = wpE 483 c4
  q262 : Ws → Eqn
  q262 c4 = wlE 600 (lit c4)

-- Kdu-box @243243: 6 steps
lem-Kdu-box-at243243 : Ws → ⟪ (K0⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ K0⁻ ∷ []) ⟫ʷ
lem-Kdu-box-at243243 c4 = derive (K0⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ K0⁻ ∷ [])
  (rw 1 (q48 c4) ∷
   rw⁻ 0 (q261 c4) ∷
   rw 1 (q262 c4) ∷
   rw⁻ 2 (q261 c4) ∷
   rw 3 (q262 c4) ∷
   rw⁻ 0 (q35 c4) ∷ []) Eq.refl

private
  q263 : Ws → Eqn
  q263 c4 = wpE 489 c4
  q264 : Ws → Eqn
  q264 c4 = wlE 601 (lit c4)

-- Ku-box @122441: 6 steps
lem-Ku-box-at122441 : Ws → ⟪ (K0 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ K0 ∷ []) ⟫ʷ
lem-Ku-box-at122441 c4 = derive (K0 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ K0 ∷ [])
  (rw 1 (q59 c4) ∷
   rw⁻ 0 (q263 c4) ∷
   rw 1 (q264 c4) ∷
   rw⁻ 2 (q263 c4) ∷
   rw 3 (q264 c4) ∷
   rw⁻ 0 (q52 c4) ∷ []) Eq.refl

private
  q265 : Ws → Eqn
  q265 c4 = wpE 490 c4
  q266 : Ws → Eqn
  q266 c4 = wlE 602 (lit c4)

-- Kdu-box @122441: 6 steps
lem-Kdu-box-at122441 : Ws → ⟪ (K0⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ K0⁻ ∷ []) ⟫ʷ
lem-Kdu-box-at122441 c4 = derive (K0⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ K0⁻ ∷ [])
  (rw 1 (q59 c4) ∷
   rw⁻ 0 (q265 c4) ∷
   rw 1 (q266 c4) ∷
   rw⁻ 2 (q265 c4) ∷
   rw 3 (q266 c4) ∷
   rw⁻ 0 (q52 c4) ∷ []) Eq.refl

private
  q267 : Ws → Eqn
  q267 c4 = sE 824 (lem-P-box-at0214213043 c4)
  q268 : Ws → Eqn
  q268 c4 = sE 843 (lem-box-cP-at0214213043 c4)
  q269 : Ws → Eqn
  q269 c4 = wlE 635 (lit c4)
  q270 : Ws → Eqn
  q270 c4 = sE 187 (lem-box-tQ-at0210233441 c4)

-- pairs @0214213043: 4 steps
lem-pairs-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-pairs-at0214213043 c4 = derive (Bx2-4103 ∷ []) (Bx2-0341 ∷ [])
  (rw⁻ 0 (q267 c4) ∷
   rw 1 (q268 c4) ∷
   rw 4 (q269 c4) ∷
   rw⁻ 0 (q270 c4) ∷ []) Eq.refl

private
  q271 : Ws → Eqn
  q271 c4 = wpE 518 c4
  q272 : Ws → Eqn
  q272 c4 = eqn (CK41 ∷ Toff023 ∷ []) (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4))
  q273 : Ws → Eqn
  q273 c4 = wlE 643 (lit c4)

-- F4-K1-CS1: 17 steps
lem-F4-K1-CS1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-CS1 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 0 (q271 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 2 (q272 c4) ∷
   rw⁻ 1 (q38 c4) ∷
   rw⁻ 2 (q271 c4) ∷
   rw⁻ 5 (q38 c4) ∷
   rw 4 (q272 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q273 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q274 : Ws → Eqn
  q274 c4 = sE 866 (lem-sym-bc-at122441 c4)

-- box-perm-1324 @122441: 1 steps
lem-box-perm-1324-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-box-perm-1324-at122441 c4 = derive (Bx0-2431 ∷ []) (Bx0-2341 ∷ [])
  (rw 0 (q274 c4) ∷ []) Eq.refl

private
  q275 : Ws → Eqn
  q275 c4 = wpE 536 c4
  q276 : Ws → Eqn
  q276 c4 = wlE 662 (lit c4)

-- Ku-box @0210243143: 6 steps
lem-Ku-box-at0210243143 : Ws → ⟪ (K2 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ K2 ∷ []) ⟫ʷ
lem-Ku-box-at0210243143 c4 = derive (K2 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ K2 ∷ [])
  (rw 1 (q31 c4) ∷
   rw⁻ 0 (q275 c4) ∷
   rw 1 (q276 c4) ∷
   rw⁻ 2 (q275 c4) ∷
   rw 3 (q276 c4) ∷
   rw⁻ 0 (q18 c4) ∷ []) Eq.refl

private
  q277 : Ws → Eqn
  q277 c4 = wpE 537 c4
  q278 : Ws → Eqn
  q278 c4 = wlE 663 (lit c4)

-- Kdu-box @0210243143: 6 steps
lem-Kdu-box-at0210243143 : Ws → ⟪ (K2⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ K2⁻ ∷ []) ⟫ʷ
lem-Kdu-box-at0210243143 c4 = derive (K2⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ K2⁻ ∷ [])
  (rw 1 (q31 c4) ∷
   rw⁻ 0 (q277 c4) ∷
   rw 1 (q278 c4) ∷
   rw⁻ 2 (q277 c4) ∷
   rw 3 (q278 c4) ∷
   rw⁻ 0 (q18 c4) ∷ []) Eq.refl

private
  q279 : Ws → Eqn
  q279 c4 = sE 839 (lem-P-box-at143143 c4)
  q280 : Ws → Eqn
  q280 c4 = sE 854 (lem-box-cP-at143143 c4)
  q281 : Ws → Eqn
  q281 c4 = wlE 229 (lit c4)
  q282 : Ws → Eqn
  q282 c4 = sE 219 (lem-box-tQ-at233442 c4)

-- pairs @143143: 4 steps
lem-pairs-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-pairs-at143143 c4 = derive (Bx0-4213 ∷ []) (Bx0-1342 ∷ [])
  (rw⁻ 0 (q279 c4) ∷
   rw 1 (q280 c4) ∷
   rw 4 (q281 c4) ∷
   rw⁻ 0 (q282 c4) ∷ []) Eq.refl

private
  q283 : Ws → Eqn
  q283 c4 = wpE 556 c4
  q284 : Ws → Eqn
  q284 c4 = eqn (CK42 ∷ Toff013 ∷ []) (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 (lit c4))
  q285 : Ws → Eqn
  q285 c4 = wlE 686 (lit c4)

-- F4-K2-CS2: 17 steps
lem-F4-K2-CS2 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS2 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 0 (q283 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw 2 (q284 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw⁻ 2 (q283 c4) ∷
   rw⁻ 5 (q54 c4) ∷
   rw 4 (q284 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw⁻ 0 (q52 c4) ∷
   rw⁻ 1 (q285 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q286 : Ws → Eqn
  q286 c4 = sE 862 (lem-sym-bc-at0210243143 c4)

-- box-perm-1324 @0210243143: 1 steps
lem-box-perm-1324-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-box-perm-1324-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-0143 ∷ [])
  (rw 0 (q286 c4) ∷ []) Eq.refl

private
  q287 : Ws → Eqn
  q287 c4 = sE 870 (lem-sym-bc-at243243 c4)

-- box-perm-1324 @243243: 1 steps
lem-box-perm-1324-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-box-perm-1324-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-1243 ∷ [])
  (rw 0 (q287 c4) ∷ []) Eq.refl

private
  q288 : Ws → Eqn
  q288 c4 = sE 820 (lem-sym-ab-at122441 c4)
  q289 : Ws → Eqn
  q289 c4 = sE 869 (lem-sym-bc-at1441 c4)
  q290 : Ws → Eqn
  q290 c4 = sE 860 (lem-pairs-at14233241 c4)

-- box-perm-1423 @122441: 3 steps
lem-box-perm-1423-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-box-perm-1423-at122441 c4 = derive (Bx0-2431 ∷ []) (Bx0-2143 ∷ [])
  (rw 0 (q288 c4) ∷
   rw 0 (q289 c4) ∷
   rw 0 (q290 c4) ∷ []) Eq.refl

private
  q291 : Ws → Eqn
  q291 c4 = wlE 709 (lit c4)
  q292 : Ws → Eqn
  q292 c4 = wpE 599 c4
  q293 : Ws → Eqn
  q293 c4 = eqn (ι ∷ []) (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl)
  q294 : Ws → Eqn
  q294 c4 = wpE 600 c4
  q295 : Ws → Eqn
  q295 c4 = eqn (ι1 ∷ []) (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl)
  q296 : Ws → Eqn
  q296 c4 = wpE 601 c4
  q297 : Ws → Eqn
  q297 c4 = wlE 710 (lit c4)

-- F4-CS0-I: 19 steps
lem-F4-CS0-I : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-I c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 2 (q291 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 2 (q292 c4) ∷
   rw 1 (q18 c4) ∷
   rw 5 (q293 c4) ∷
   rw 4 (q294 c4) ∷
   rw 4 (q295 c4) ∷
   rw 3 (q296 c4) ∷
   rw 3 (q293 c4) ∷
   rw 2 (q294 c4) ∷
   rw 2 (q295 c4) ∷
   rw 1 (q296 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   re 5 1 (Sb2-0-3-1 ∷ []) ∷
   re 7 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q297 c4) ∷ []) Eq.refl

private
  q298 : Ws → Eqn
  q298 c4 = wpE 602 c4
  q299 : Ws → Eqn
  q299 c4 = eqn (Toff213 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4))
  q300 : Ws → Eqn
  q300 c4 = wpE 603 c4

-- F4-CS0-S0: 17 steps
lem-F4-CS0-S0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S0 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q298 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q224 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 4 (q223 c4) ∷
   rw 5 (q299 c4) ∷
   rw 3 (q221 c4) ∷
   rw⁻ 2 (q223 c4) ∷
   rw 3 (q299 c4) ∷
   rw 1 (q221 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   re 5 1 (Sb2-0-3-1 ∷ []) ∷
   re 7 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q300 c4) ∷ []) Eq.refl

private
  q301 : Ws → Eqn
  q301 c4 = wlE 711 (lit c4)
  q302 : Ws → Eqn
  q302 c4 = wpE 604 c4
  q303 : Ws → Eqn
  q303 c4 = wlE 712 (lit c4)
  q304 : Ws → Eqn
  q304 c4 = wpE 605 c4
  q305 : Ws → Eqn
  q305 c4 = wlE 713 (lit c4)

-- F4-CS0-S1: 15 steps
lem-F4-CS0-S1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q301 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q302 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 4 (q303 c4) ∷
   rw 3 (q304 c4) ∷
   rw⁻ 2 (q303 c4) ∷
   rw 1 (q304 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   re 5 1 (Sb2-0-3-1 ∷ []) ∷
   re 7 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q305 c4) ∷ []) Eq.refl

private
  q306 : Ws → Eqn
  q306 c4 = wlE 717 (lit c4)
  q307 : Ws → Eqn
  q307 c4 = wpE 608 c4
  q308 : Ws → Eqn
  q308 c4 = wlE 718 (lit c4)
  q309 : Ws → Eqn
  q309 c4 = wpE 609 c4
  q310 : Ws → Eqn
  q310 c4 = wlE 719 (lit c4)

-- F4-CS0-S3: 15 steps
lem-F4-CS0-S3 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S3 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q306 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q307 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 4 (q308 c4) ∷
   rw 3 (q309 c4) ∷
   rw⁻ 2 (q308 c4) ∷
   rw 1 (q309 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   re 5 1 (Sb2-0-3-1 ∷ []) ∷
   re 7 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q310 c4) ∷ []) Eq.refl

private
  q311 : Ws → Eqn
  q311 c4 = wpE 610 c4
  q312 : Ws → Eqn
  q312 c4 = wpE 611 c4
  q313 : Ws → Eqn
  q313 c4 = eqn (K0 ∷ Toff213 ∷ []) (Toff213 ∷ K0 ∷ []) (c₁ (K) (K ↑ • CCZ • K ↑ • iI))
  q314 : Ws → Eqn
  q314 c4 = eqn (Toff213 ∷ CK40 ∷ []) (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 (lit c4))
  q315 : Ws → Eqn
  q315 c4 = eqn (Toff213 ∷ S4 ∷ []) (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S))
  q316 : Ws → Eqn
  q316 c4 = wpE 612 c4
  q317 : Ws → Eqn
  q317 c4 = wpE 613 c4

-- F4-CS0-K0: 19 steps
lem-F4-CS0-K0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K0 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q311 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q312 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 4 (q313 c4) ∷
   rw 5 (q314 c4) ∷
   rw 6 (q315 c4) ∷
   rw 3 (q316 c4) ∷
   rw⁻ 2 (q313 c4) ∷
   rw 3 (q314 c4) ∷
   rw 4 (q315 c4) ∷
   rw 1 (q316 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q317 c4) ∷ []) Eq.refl

private
  q318 : Ws → Eqn
  q318 c4 = wpE 619 c4
  q319 : Ws → Eqn
  q319 c4 = wpE 620 c4
  q320 : Ws → Eqn
  q320 c4 = wpE 621 c4

-- F4-CS1-I: 17 steps
lem-F4-CS1-I : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-I c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 2 (q291 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 6 (q293 c4) ∷
   rw 2 (q318 c4) ∷
   rw 2 (q295 c4) ∷
   rw 1 (q35 c4) ∷
   rw 4 (q319 c4) ∷
   rw 3 (q320 c4) ∷
   rw 2 (q319 c4) ∷
   rw 1 (q320 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   re 5 1 (Sb0-1-3-2 ∷ []) ∷
   re 7 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 3 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q297 c4) ∷ []) Eq.refl

private
  q321 : Ws → Eqn
  q321 c4 = eqn (Toff023 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 (lit c4))

-- F4-CS1-S1: 17 steps
lem-F4-CS1-S1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q301 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q234 c4) ∷
   rw 1 (q35 c4) ∷
   rw⁻ 4 (q233 c4) ∷
   rw 5 (q321 c4) ∷
   rw 3 (q231 c4) ∷
   rw⁻ 2 (q233 c4) ∷
   rw 3 (q321 c4) ∷
   rw 1 (q231 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   re 5 1 (Sb0-1-3-2 ∷ []) ∷
   re 7 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 3 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q305 c4) ∷ []) Eq.refl

private
  q322 : Ws → Eqn
  q322 c4 = wlE 714 (lit c4)
  q323 : Ws → Eqn
  q323 c4 = wlE 732 (lit c4)
  q324 : Ws → Eqn
  q324 c4 = wpE 625 c4
  q325 : Ws → Eqn
  q325 c4 = wpE 626 c4
  q326 : Ws → Eqn
  q326 c4 = wlE 716 (lit c4)

-- F4-CS1-S2: 15 steps
lem-F4-CS1-S2 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S2 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q322 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q323 c4) ∷
   rw 1 (q35 c4) ∷
   rw⁻ 4 (q324 c4) ∷
   rw 3 (q325 c4) ∷
   rw⁻ 2 (q324 c4) ∷
   rw 1 (q325 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   re 5 1 (Sb0-1-3-2 ∷ []) ∷
   re 7 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 3 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q326 c4) ∷ []) Eq.refl

private
  q327 : Ws → Eqn
  q327 c4 = wlE 733 (lit c4)
  q328 : Ws → Eqn
  q328 c4 = wpE 627 c4
  q329 : Ws → Eqn
  q329 c4 = wpE 628 c4

-- F4-CS1-S3: 15 steps
lem-F4-CS1-S3 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S3 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q306 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q327 c4) ∷
   rw 1 (q35 c4) ∷
   rw⁻ 4 (q328 c4) ∷
   rw 3 (q329 c4) ∷
   rw⁻ 2 (q328 c4) ∷
   rw 1 (q329 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   re 5 1 (Sb0-1-3-2 ∷ []) ∷
   re 7 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 3 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q310 c4) ∷ []) Eq.refl

private
  q330 : Ws → Eqn
  q330 c4 = wlE 720 (lit c4)
  q331 : Ws → Eqn
  q331 c4 = wlE 734 (lit c4)
  q332 : Ws → Eqn
  q332 c4 = wlE 735 (lit c4)
  q333 : Ws → Eqn
  q333 c4 = eqn (Toff023 ∷ CK41 ∷ []) (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4))
  q334 : Ws → Eqn
  q334 c4 = eqn (Toff023 ∷ S4 ∷ []) (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S))
  q335 : Ws → Eqn
  q335 c4 = wpE 634 c4
  q336 : Ws → Eqn
  q336 c4 = wlE 723 (lit c4)

-- F4-CS1-K1: 19 steps
lem-F4-CS1-K1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q330 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q331 c4) ∷
   rw 1 (q35 c4) ∷
   rw⁻ 4 (q332 c4) ∷
   rw 5 (q333 c4) ∷
   rw 6 (q334 c4) ∷
   rw 3 (q335 c4) ∷
   rw⁻ 2 (q332 c4) ∷
   rw 3 (q333 c4) ∷
   rw 4 (q334 c4) ∷
   rw 1 (q335 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q336 c4) ∷ []) Eq.refl

private
  q337 : Ws → Eqn
  q337 c4 = wpE 637 c4
  q338 : Ws → Eqn
  q338 c4 = wpE 638 c4

-- F4-CS2-I: 17 steps
lem-F4-CS2-I : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-I c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 2 (q291 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 6 (q293 c4) ∷
   rw 2 (q337 c4) ∷
   rw 2 (q295 c4) ∷
   rw 1 (q52 c4) ∷
   rw 4 (q338 c4) ∷
   rw 3 (q296 c4) ∷
   rw 2 (q338 c4) ∷
   rw 1 (q296 c4) ∷
   rw⁻ 3 (q52 c4) ∷
   re 5 1 (Sb0-2-1-3 ∷ []) ∷
   re 7 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 3 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 0 (q297 c4) ∷ []) Eq.refl

private
  q339 : Ws → Eqn
  q339 c4 = wlE 739 (lit c4)
  q340 : Ws → Eqn
  q340 c4 = wpE 642 c4

-- F4-CS2-S1: 15 steps
lem-F4-CS2-S1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw⁻ 2 (q301 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q339 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 4 (q340 c4) ∷
   rw 3 (q304 c4) ∷
   rw⁻ 2 (q340 c4) ∷
   rw 1 (q304 c4) ∷
   rw⁻ 3 (q52 c4) ∷
   re 5 1 (Sb0-2-1-3 ∷ []) ∷
   re 7 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 3 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 0 (q305 c4) ∷ []) Eq.refl

private
  q341 : Ws → Eqn
  q341 c4 = eqn (Toff013 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4))

-- F4-CS2-S2: 17 steps
lem-F4-CS2-S2 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S2 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw⁻ 2 (q322 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q246 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 4 (q245 c4) ∷
   rw 5 (q341 c4) ∷
   rw 3 (q243 c4) ∷
   rw⁻ 2 (q245 c4) ∷
   rw 3 (q341 c4) ∷
   rw 1 (q243 c4) ∷
   rw⁻ 3 (q52 c4) ∷
   re 5 1 (Sb0-2-1-3 ∷ []) ∷
   re 7 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 3 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 0 (q326 c4) ∷ []) Eq.refl

private
  q342 : Ws → Eqn
  q342 c4 = wlE 740 (lit c4)
  q343 : Ws → Eqn
  q343 c4 = wpE 643 c4

-- F4-CS2-S3: 15 steps
lem-F4-CS2-S3 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S3 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw⁻ 2 (q306 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q342 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 4 (q343 c4) ∷
   rw 3 (q309 c4) ∷
   rw⁻ 2 (q343 c4) ∷
   rw 1 (q309 c4) ∷
   rw⁻ 3 (q52 c4) ∷
   re 5 1 (Sb0-2-1-3 ∷ []) ∷
   re 7 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 3 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 0 (q310 c4) ∷ []) Eq.refl
