{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD019 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D019 (Sᴰ : SD019) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-CCZ034 ; lem-comm-CS13-CCZ024 ; lem-comm-CS23-CCZ014 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX04-CCZ123 ; lem-comm-CX04-TOFF213 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CX13 ; lem-comm-CS02-CCZ134 ; lem-comm-CS14-CCZ023 ; lem-comm-CSd02-CCZ134 ; lem-comm-CSd14-CCZ023 ; lem-comm-CX04-TOFF312 ; lem-comm-CX30-TOFF214 ; lem-comm-TOFF013-CK42 ; lem-comm-TOFF213-CX04)

-- The lemmas of other derivation modules (DSig).
private
  lem-sym-ab-at0210243143 : Ws → St 14
  lem-sym-ab-at0210243143 = pickᴰ 0 Sᴰ
  lem-sym-ab-at0214203143 : Ws → St 871
  lem-sym-ab-at0214203143 = pickᴰ 1 Sᴰ
  lem-sym-ab-at03102132 : Ws → St 11
  lem-sym-ab-at03102132 = pickᴰ 2 Sᴰ
  lem-sym-ab-at0310243142 : Ws → St 754
  lem-sym-ab-at0310243142 = pickᴰ 3 Sᴰ
  lem-sym-ab-at0312213440 : Ws → St 872
  lem-sym-ab-at0312213440 = pickᴰ 4 Sᴰ
  lem-sym-ab-at0314203142 : Ws → St 873
  lem-sym-ab-at0314203142 = pickᴰ 5 Sᴰ
  lem-sym-ab-at122441 : Ws → St 820
  lem-sym-ab-at122441 = pickᴰ 6 Sᴰ
  lem-sym-ab-at021021 : Ws → St 20
  lem-sym-ab-at021021 = pickᴰ 7 Sᴰ
  lem-sym-ab-at0213213440 : Ws → St 874
  lem-sym-ab-at0213213440 = pickᴰ 8 Sᴰ
  lem-sym-ab-at0220 : Ws → St 21
  lem-sym-ab-at0220 = pickᴰ 9 Sᴰ
  lem-sym-ab-at02233440 : Ws → St 875
  lem-sym-ab-at02233440 = pickᴰ 10 Sᴰ
  lem-sym-ab-at14233241 : Ws → St 876
  lem-sym-ab-at14233241 = pickᴰ 11 Sᴰ
  lem-box-tQ-at032032 : Ws → St 25
  lem-box-tQ-at032032 = pickᴰ 12 Sᴰ
  lem-box-tQ-at0210243143 : Ws → St 147
  lem-box-tQ-at0210243143 = pickᴰ 13 Sᴰ
  lem-box-tQ-at0214213043 : Ws → St 149
  lem-box-tQ-at0214213043 = pickᴰ 14 Sᴰ
  lem-box-tQ-at022330 : Ws → St 188
  lem-box-tQ-at022330 = pickᴰ 15 Sᴰ
  lem-box-tQ-at0310243142 : Ws → St 150
  lem-box-tQ-at0310243142 = pickᴰ 16 Sᴰ
  lem-box-tQ-at0314213042 : Ws → St 192
  lem-box-tQ-at0314213042 = pickᴰ 17 Sᴰ
  lem-box-tQ-at122331 : Ws → St 154
  lem-box-tQ-at122331 = pickᴰ 18 Sᴰ
  lem-P-box-at0210233441 : Ws → St 877
  lem-P-box-at0210233441 = pickᴰ 19 Sᴰ
  lem-P-box-at0210243143 : Ws → St 878
  lem-P-box-at0210243143 = pickᴰ 20 Sᴰ
  lem-P-box-at022330 : Ws → St 879
  lem-P-box-at022330 = pickᴰ 21 Sᴰ
  lem-P-box-at0312243140 : Ws → St 880
  lem-P-box-at0312243140 = pickᴰ 22 Sᴰ
  lem-P-box-at243243 : Ws → St 881
  lem-P-box-at243243 = pickᴰ 23 Sᴰ
  lem-t-cP-at0314213042 : Ws → St 882
  lem-t-cP-at0314213042 = pickᴰ 24 Sᴰ
  lem-sym-bc-at0213243140 : Ws → St 883
  lem-sym-bc-at0213243140 = pickᴰ 25 Sᴰ
  lem-box-cP-at0210233441 : Ws → St 884
  lem-box-cP-at0210233441 = pickᴰ 26 Sᴰ
  lem-box-cP-at0210243143 : Ws → St 842
  lem-box-cP-at0210243143 = pickᴰ 27 Sᴰ
  lem-box-cP-at0213203441 : Ws → St 885
  lem-box-cP-at0213203441 = pickᴰ 28 Sᴰ
  lem-box-cP-at022330 : Ws → St 886
  lem-box-cP-at022330 = pickᴰ 29 Sᴰ
  lem-box-cP-at0310243142 : Ws → St 844
  lem-box-cP-at0310243142 = pickᴰ 30 Sᴰ
  lem-box-cP-at0312243140 : Ws → St 887
  lem-box-cP-at0312243140 = pickᴰ 31 Sᴰ
  lem-box-cP-at0314213042 : Ws → St 888
  lem-box-cP-at0314213042 = pickᴰ 32 Sᴰ
  lem-box-cP-at122441 : Ws → St 850
  lem-box-cP-at122441 = pickᴰ 33 Sᴰ
  lem-box-cP-at243243 : Ws → St 856
  lem-box-cP-at243243 = pickᴰ 34 Sᴰ
  lem-pairs-at0213243140 : Ws → St 889
  lem-pairs-at0213243140 = pickᴰ 35 Sᴰ
  lem-pairs-at0220 : Ws → St 890
  lem-pairs-at0220 = pickᴰ 36 Sᴰ
  lem-pairs-at032032 : Ws → St 891
  lem-pairs-at032032 = pickᴰ 37 Sᴰ
  lem-pairs-at13243241 : Ws → St 859
  lem-pairs-at13243241 = pickᴰ 38 Sᴰ
  lem-sym-bc-at0213213440 : Ws → St 892
  lem-sym-bc-at0213213440 = pickᴰ 39 Sᴰ
  lem-sym-bc-at0214203143 : Ws → St 893
  lem-sym-bc-at0214203143 = pickᴰ 40 Sᴰ
  lem-sym-bc-at0214213043 : Ws → St 894
  lem-sym-bc-at0214213043 = pickᴰ 41 Sᴰ
  lem-sym-bc-at0312243140 : Ws → St 895
  lem-sym-bc-at0312243140 = pickᴰ 42 Sᴰ
  lem-sym-bc-at0314203142 : Ws → St 896
  lem-sym-bc-at0314203142 = pickᴰ 43 Sᴰ
  lem-sym-bc-at0314213042 : Ws → St 897
  lem-sym-bc-at0314213042 = pickᴰ 44 Sᴰ
  lem-sym-bc-at1441 : Ws → St 869
  lem-sym-bc-at1441 = pickᴰ 45 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ []) (wl 725 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (K2 ∷ CK42 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ []) (wl 742 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (K2 ∷ Toff013 ∷ []) (Toff013 ∷ K2 ∷ []) (wl 743 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Toff013 ∷ CK42 ∷ []) (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Toff013 ∷ S4 ∷ []) (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S))
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CCZ024 ∷ []) (wp 649 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CK42 ∷ X4 ∷ []) (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (wl 728 (lit c4))

-- F4-CS2-K2: 19 steps
lem-F4-CS2-K2 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K2 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw⁻ 2 (q1 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw 3 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (Sb0-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 0 (q8 c4) ∷ []) Eq.refl

private
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx2-0413 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (X4 ∷ CCZ024 ∷ []) (wp 20 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CZ02 ∷ Toff213 ∷ []) (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl 183 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Toff213 ∷ X4 ∷ []) (X4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl 184 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp 21 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ024 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ []) (wp 22 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS13⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ024 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ024 ∷ []) (wp 23 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) (wl 185 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ []) (wl 186 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp 32 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ []) (wl 191 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl 190 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) (wp 33 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp 34 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) (wp 35 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp 36 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) (wp 37 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ Toff213 ∷ []) (wl 192 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (Toff214 ∷ CCZ024 ∷ []) (wp 42 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp 41 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) (wl 193 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CX04 ∷ Toff213 ∷ []) (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS14⁻ ∷ []) (wl 194 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) (wl 195 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Toff213 ∷ Toff214 ∷ []) (Toff214 ∷ Toff213 ∷ []) (wl 197 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ014 ∷ []) (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) (wp 44 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) (wl 196 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ []) (wp 650 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl 230 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp 651 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CX13 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ []) (wl 745 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CX13 ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX13 ∷ Toff314 ∷ []) (wp 652 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CX12 ∷ CX13 ∷ Toff213 ∷ []) (Toff213 ∷ CX13 ∷ []) (wl 746 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (Toff213 ∷ Toff314 ∷ []) (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl 747 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ024 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp 653 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp 654 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CX12 ∷ Toff213 ∷ []) (Toff213 ∷ CX12 ∷ []) (wl 748 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Toff213 ∷ CX04 ∷ []) (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ014 ∷ []) (CX12 ∷ CCZ014 ∷ CX12 ∷ []) (wp 655 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ014 ∷ CX13 ∷ CCZ014 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ []) (wp 656 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Toff314 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ Toff314 ∷ []) (wl 187 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ []) (wp 657 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ []) (wp 658 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ []) (wp 659 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03⁻ ∷ []) (wp 660 c4)

-- F4-CS0-CS0: 286 steps
lem-F4-CS0-CS0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-CS0 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 8 (q16 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 6 (q17 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q20 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw 6 (q22 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 8 (q22 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw 5 (q9 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   rw⁻ 10 (q24 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw 8 (q26 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   rw⁻ 4 (q29 c4) ∷
   rw 5 (q23 c4) ∷
   rw⁻ 5 (q30 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw⁻ 13 (q24 c4) ∷
   rw⁻ 12 (q25 c4) ∷
   rw 11 (q26 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 9 (q26 c4) ∷
   rw⁻ 8 (q28 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 8 (q23 c4) ∷
   rw⁻ 6 (q31 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw 8 (q32 c4) ∷
   rw 12 (q33 c4) ∷
   rw 11 (q34 c4) ∷
   rw 10 (q35 c4) ∷
   rw 9 (q34 c4) ∷
   rw 8 (q36 c4) ∷
   rw⁻ 9 (q32 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 3 1 (CS03 ∷ []) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 6 (q39 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 2 (q23 c4) ∷
   rw⁻ 8 (q24 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 3 (q23 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw⁻ 11 (q24 c4) ∷
   rw⁻ 10 (q25 c4) ∷
   rw 9 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 7 (q26 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 4 (q31 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw 6 (q32 c4) ∷
   rw 10 (q33 c4) ∷
   rw 9 (q34 c4) ∷
   rw 8 (q35 c4) ∷
   rw 7 (q34 c4) ∷
   rw 6 (q36 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 0 (q10 c4) ∷
   rw 2 (q11 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   rw 3 (q9 c4) ∷
   rw 2 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw 4 (q16 c4) ∷
   rw⁻ 3 (q15 c4) ∷
   rw 2 (q17 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 5 (q20 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 3 (q40 c4) ∷
   rw 10 (q41 c4) ∷
   rw 3 (q42 c4) ∷
   rw 5 (q43 c4) ∷
   re 4 1 (Sb2-0-3-1 ∷ []) ∷
   re 6 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 2 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 3 (q44 c4) ∷
   re 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 4 1 (CS03 ∷ []) ∷
   re 6 1 (CS03⁻ ∷ []) ∷
   rw⁻ 3 (q45 c4) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 5 (q46 c4) ∷
   rw 7 (q47 c4) ∷
   rw 4 (q48 c4) ∷
   rw 6 (q49 c4) ∷
   rw 7 (q50 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw 9 (q29 c4) ∷
   rw 10 (q28 c4) ∷
   rw 11 (q49 c4) ∷
   rw 12 (q27 c4) ∷
   rw 13 (q49 c4) ∷
   rw 14 (q25 c4) ∷
   rw 15 (q24 c4) ∷
   rw 9 (q23 c4) ∷
   rw⁻ 3 (q51 c4) ∷
   rw 5 (q32 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 5 (q52 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   rw 7 (q52 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw⁻ 5 (q46 c4) ∷
   rw 7 (q37 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 8 (q36 c4) ∷
   rw 9 (q52 c4) ∷
   rw⁻ 10 (q35 c4) ∷
   rw 11 (q52 c4) ∷
   rw⁻ 12 (q33 c4) ∷
   rw⁻ 8 (q32 c4) ∷
   rw 9 (q47 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw⁻ 5 (q38 c4) ∷
   rw 3 (q54 c4) ∷
   rw 2 (q49 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   rw 3 (q29 c4) ∷
   rw 4 (q28 c4) ∷
   rw 5 (q49 c4) ∷
   rw 6 (q27 c4) ∷
   rw 7 (q49 c4) ∷
   rw 8 (q25 c4) ∷
   rw 9 (q24 c4) ∷
   rw 3 (q23 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 1 (q55 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 4 (q57 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 2 (q56 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   re 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 6 1 (CS03 ∷ []) ∷
   re 8 1 (CS03⁻ ∷ []) ∷
   rw⁻ 5 (q45 c4) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 7 (q46 c4) ∷
   rw 9 (q47 c4) ∷
   rw 6 (q48 c4) ∷
   rw 8 (q49 c4) ∷
   rw 9 (q50 c4) ∷
   rw⁻ 12 (q23 c4) ∷
   rw 11 (q29 c4) ∷
   rw 12 (q28 c4) ∷
   rw 13 (q49 c4) ∷
   rw 14 (q27 c4) ∷
   rw 15 (q49 c4) ∷
   rw 16 (q25 c4) ∷
   rw 17 (q24 c4) ∷
   rw 11 (q23 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw 7 (q52 c4) ∷
   rw⁻ 8 (q35 c4) ∷
   rw 9 (q52 c4) ∷
   rw⁻ 10 (q33 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   rw⁻ 7 (q46 c4) ∷
   rw 9 (q37 c4) ∷
   rw 11 (q32 c4) ∷
   rw⁻ 10 (q36 c4) ∷
   rw 11 (q52 c4) ∷
   rw⁻ 12 (q35 c4) ∷
   rw 13 (q52 c4) ∷
   rw⁻ 14 (q33 c4) ∷
   rw⁻ 10 (q32 c4) ∷
   rw 11 (q47 c4) ∷
   rw⁻ 5 (q53 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 5 (q54 c4) ∷
   rw 4 (q49 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   rw 5 (q29 c4) ∷
   rw 6 (q28 c4) ∷
   rw 7 (q49 c4) ∷
   rw 8 (q27 c4) ∷
   rw 9 (q49 c4) ∷
   rw 10 (q25 c4) ∷
   rw 11 (q24 c4) ∷
   rw 5 (q23 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 3 (q55 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   re 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 7 1 (CS03 ∷ []) ∷
   re 9 1 (CS03⁻ ∷ []) ∷
   rw⁻ 6 (q59 c4) ∷
   rw 5 (q9 c4) ∷
   rw⁻ 8 (q22 c4) ∷
   rw 7 (q21 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 4 (q58 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (Bx2-0413 ∷ []) (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx2-4013 ∷ []) (Bx2-4103 ∷ []) (lem-sym-bc-at0214203143 c4)

-- box-perm-2314 @0210243143: 2 steps
lem-box-perm-2314-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-box-perm-2314-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-4103 ∷ [])
  (rw 0 (q60 c4) ∷
   rw 0 (q61 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = eqn (Bx3-4102 ∷ []) (Bx3-4012 ∷ []) (lem-sym-bc-at0314213042 c4)

-- box-perm-1324 @0314213042: 1 steps
lem-box-perm-1324-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-1324-at0314213042 c4 = derive (Bx3-4102 ∷ []) (Bx3-4012 ∷ [])
  (rw 0 (q62 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx3-4012 ∷ []) (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4)

-- box-perm-3124 @0314213042: 2 steps
lem-box-perm-3124-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-3124-at0314213042 c4 = derive (Bx3-4102 ∷ []) (Bx3-0412 ∷ [])
  (rw 0 (q62 c4) ∷
   rw 0 (q63 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = eqn (Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (Bx2-3041 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0213203441 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ023 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ023 ∷ []) (wl 613 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl 758 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl 310 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) (wl 670 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (CCZ023 ∷ CX34 ∷ []) (CX34 ∷ CCZ023 ∷ []) (wp 680 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CS14⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (CS14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ134 ∷ CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ123 ∷ []) (wl 759 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (Toff304 ∷ CCZ023 ∷ []) (wp 665 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (Toff304 ∷ []) (wp 681 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (K3⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K3⁻ ∷ []) (wl 760 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (CS34 ∷ Toff214 ∷ []) (Toff214 ∷ CS34 ∷ []) (wl 761 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (CX30 ∷ Toff214 ∷ []) (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (CS04⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS04⁻ ∷ []) (wp 682 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (CS04 ∷ Toff214 ∷ []) (Toff214 ∷ CS04 ∷ []) (wp 683 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (K3 ∷ Toff214 ∷ []) (Toff214 ∷ K3 ∷ []) (wl 762 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (CCZ023 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ023 ∷ []) (wp 669 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ023 ∷ CS01 ∷ []) (CS01 ∷ CCZ023 ∷ []) (wl 199 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (CCZ023 ∷ CX04 ∷ []) (CX04 ∷ CCZ023 ∷ []) (wp 684 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ014 ∷ []) (CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp 685 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ014 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ []) (wp 686 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (CCZ123 ∷ CS01 ∷ []) (CS01 ∷ CCZ123 ∷ []) (wl 763 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (CX04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ123 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ123 ∷ []) (wl 764 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ []) (wl 765 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (CCZ014 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ014 ∷ []) (wp 687 c4)

-- box-box-4 @0310243142: 103 steps
lem-box-box-4-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-box-box-4-at0310243142 c4 = derive (Bx3-0412 ∷ Bx2-3041 ∷ []) (Bx2-3041 ∷ Bx3-0412 ∷ [])
  (rw 0 (q64 c4) ∷
   rw 4 (q65 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 6 (q66 c4) ∷
   rw 5 (q68 c4) ∷
   rw⁻ 9 (q69 c4) ∷
   rw⁻ 8 (q70 c4) ∷
   rw 7 (q71 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   rw 6 (q73 c4) ∷
   rw⁻ 3 (q65 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 2 (q74 c4) ∷
   rw 4 (q50 c4) ∷
   rw⁻ 3 (q75 c4) ∷
   rw 9 (q76 c4) ∷
   rw 8 (q77 c4) ∷
   rw 7 (q78 c4) ∷
   rw 6 (q79 c4) ∷
   rw 5 (q78 c4) ∷
   rw 4 (q80 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q75 c4) ∷
   rw⁻ 6 (q82 c4) ∷
   rw 5 (q32 c4) ∷
   rw⁻ 9 (q83 c4) ∷
   rw⁻ 8 (q84 c4) ∷
   rw 7 (q71 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   rw⁻ 4 (q74 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw 6 (q86 c4) ∷
   rw⁻ 5 (q75 c4) ∷
   rw 11 (q76 c4) ∷
   rw 10 (q77 c4) ∷
   rw 9 (q78 c4) ∷
   rw 8 (q79 c4) ∷
   rw 7 (q78 c4) ∷
   rw 6 (q80 c4) ∷
   rw 5 (q81 c4) ∷
   rw 6 (q75 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw 2 (q65 c4) ∷
   rw⁻ 1 (q66 c4) ∷
   rw 2 (q67 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   rw 3 (q68 c4) ∷
   rw⁻ 7 (q69 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw 5 (q71 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 4 (q73 c4) ∷
   rw⁻ 1 (q65 c4) ∷
   rw 1 (q65 c4) ∷
   rw⁻ 0 (q74 c4) ∷
   rw 2 (q50 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   rw 7 (q76 c4) ∷
   rw 6 (q77 c4) ∷
   rw 5 (q78 c4) ∷
   rw 4 (q79 c4) ∷
   rw 3 (q78 c4) ∷
   rw 2 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 2 (q75 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 3 (q32 c4) ∷
   rw⁻ 7 (q83 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 5 (q71 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw⁻ 2 (q74 c4) ∷
   rw⁻ 4 (q85 c4) ∷
   rw 4 (q86 c4) ∷
   rw⁻ 3 (q75 c4) ∷
   rw 9 (q76 c4) ∷
   rw 8 (q77 c4) ∷
   rw 7 (q78 c4) ∷
   rw 6 (q79 c4) ∷
   rw 5 (q78 c4) ∷
   rw 4 (q80 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q75 c4) ∷
   rw⁻ 0 (q65 c4) ∷
   rw 2 (q32 c4) ∷
   rw⁻ 6 (q87 c4) ∷
   rw 5 (q88 c4) ∷
   rw⁻ 4 (q89 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 2 (q90 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw 3 (q91 c4) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 1 (q64 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = eqn (Toff214 ∷ Bx2-0341 ∷ Toff214 ∷ []) (Bx2-0341 ∷ []) (lem-P-box-at0210233441 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (Bx2-0341 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0210233441 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (Toff214 ∷ Toff214 ∷ []) [] (wl 636 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (Bx2-4103 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at0214213043 c4)

-- pairs @0210233441: 4 steps
lem-pairs-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-pairs-at0210233441 c4 = derive (Bx2-0341 ∷ []) (Bx2-4103 ∷ [])
  (rw⁻ 0 (q92 c4) ∷
   rw 1 (q93 c4) ∷
   rw 4 (q94 c4) ∷
   rw⁻ 0 (q95 c4) ∷ []) Eq.refl

private
  q96 : Ws → Eqn
  q96 c4 = eqn (Bx3-0412 ∷ []) (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (Bx3-4012 ∷ []) (Bx3-4102 ∷ []) (lem-sym-bc-at0314203142 c4)

-- box-perm-2314 @0310243142: 2 steps
lem-box-perm-2314-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-box-perm-2314-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-4102 ∷ [])
  (rw 0 (q96 c4) ∷
   rw 0 (q97 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = eqn (Bx3-4102 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213042 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (CCZ134 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ134 ∷ []) (wp 704 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (CS03⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ []) (wl 789 (lit c4))
  q101 : Ws → Eqn
  q101 c4 = eqn (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl 757 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (CCZ134 ∷ CS23 ∷ []) (CS23 ∷ CCZ134 ∷ []) (wl 790 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (CCZ134 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ []) (wp 705 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (CS02⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (CS02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ023 ∷ Toff302 ∷ []) (Toff302 ∷ CZ02 ∷ CCZ023 ∷ []) (wl 791 (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (CS02⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS02⁻ ∷ []) (wl 792 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ CS02⁻ ∷ CZ02 ∷ CCZ023 ∷ []) (CS03⁻ ∷ []) (wl 793 (lit c4))

-- CSdu-box-3 @0314213042: 17 steps
lem-CSdu-box-3-at0314213042 : Ws → ⟪ (CS03⁻ ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0314213042 c4 = derive (CS03⁻ ∷ Bx3-4102 ∷ []) (Bx3-4102 ∷ CS03⁻ ∷ [])
  (rw 1 (q98 c4) ∷
   rw⁻ 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 4 (q101 c4) ∷
   rw⁻ 8 (q102 c4) ∷
   rw⁻ 7 (q103 c4) ∷
   rw 6 (q104 c4) ∷
   rw⁻ 5 (q103 c4) ∷
   rw 4 (q105 c4) ∷
   rw⁻ 5 (q101 c4) ∷
   rw 3 (q104 c4) ∷
   rw⁻ 2 (q99 c4) ∷
   rw 5 (q106 c4) ∷
   rw 4 (q107 c4) ∷
   rw 3 (q100 c4) ∷
   rw 4 (q108 c4) ∷
   rw⁻ 0 (q98 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = eqn (CCZ134 ∷ CS03 ∷ []) (CS03 ∷ CCZ134 ∷ []) (wp 706 c4)
  q110 : Ws → Eqn
  q110 c4 = eqn (CS03 ∷ Toff302 ∷ []) (Toff302 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ []) (wl 800 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (CS02 ∷ Toff302 ∷ []) (Toff302 ∷ CS02 ∷ []) (wl 801 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (CS03 ∷ CS02 ∷ CCZ023 ∷ CS02 ∷ CZ02 ∷ CCZ023 ∷ []) (CS03 ∷ []) (wl 802 (lit c4))

-- CSu-box-3 @0314213042: 17 steps
lem-CSu-box-3-at0314213042 : Ws → ⟪ (CS03 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CS03 ∷ []) ⟫ʷ
lem-CSu-box-3-at0314213042 c4 = derive (CS03 ∷ Bx3-4102 ∷ []) (Bx3-4102 ∷ CS03 ∷ [])
  (rw 1 (q98 c4) ∷
   rw⁻ 0 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw 4 (q101 c4) ∷
   rw⁻ 8 (q102 c4) ∷
   rw⁻ 7 (q103 c4) ∷
   rw 6 (q104 c4) ∷
   rw⁻ 5 (q103 c4) ∷
   rw 4 (q105 c4) ∷
   rw⁻ 5 (q101 c4) ∷
   rw 3 (q105 c4) ∷
   rw⁻ 2 (q109 c4) ∷
   rw 5 (q106 c4) ∷
   rw 4 (q111 c4) ∷
   rw 3 (q110 c4) ∷
   rw 4 (q112 c4) ∷
   rw⁻ 0 (q98 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (Bx3-4102 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4)
  q114 : Ws → Eqn
  q114 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl 788 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ []) (lem-t-cP-at0314213042 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (CCZ023 ∷ CCZ023 ∷ []) [] (wl 204 (lit c4))

-- box2 @0314213042: 11 steps
lem-box2-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0314213042 c4 = derive (Bx3-4102 ∷ Bx3-4102 ∷ []) []
  (rw 0 (q113 c4) ∷
   rw 4 (q98 c4) ∷
   rw⁻ 4 (q114 c4) ∷
   rw 5 (q115 c4) ∷
   rw⁻ 5 (q98 c4) ∷
   rw 5 (q113 c4) ∷
   rw 4 (q114 c4) ∷
   rw 3 (q116 c4) ∷
   rw 2 (q114 c4) ∷
   rw 1 (q116 c4) ∷
   rw 0 (q114 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (Bx2-4103 ∷ []) (Bx2-4013 ∷ []) (lem-sym-bc-at0214213043 c4)
  q118 : Ws → Eqn
  q118 c4 = eqn (Bx2-4013 ∷ []) (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4)

-- box-perm-3124 @0214213043: 2 steps
lem-box-perm-3124-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-3124-at0214213043 c4 = derive (Bx2-4103 ∷ []) (Bx2-0413 ∷ [])
  (rw 0 (q117 c4) ∷
   rw 0 (q118 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = eqn (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (CX32 ∷ CCZ024 ∷ []) (wp 717 c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp 352 c4)
  q121 : Ws → Eqn
  q121 c4 = eqn (CS34⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS34⁻ ∷ []) (wl 807 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ []) (wl 808 (lit c4))
  q123 : Ws → Eqn
  q123 c4 = eqn (CX32 ∷ Toff213 ∷ []) (Toff213 ∷ CX32 ∷ []) (wl 809 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) (wp 109 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (CX32 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX32 ∷ []) (wp 718 c4)

-- CXu-box-4 @0210243143: 15 steps
lem-CXu-box-4-at0210243143 : Ws → ⟪ (CX32 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CX32 ∷ []) ⟫ʷ
lem-CXu-box-4-at0210243143 c4 = derive (CX32 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CX32 ∷ [])
  (rw 1 (q9 c4) ∷
   rw⁻ 0 (q119 c4) ∷
   rw 2 (q120 c4) ∷
   rw 6 (q39 c4) ∷
   rw 5 (q34 c4) ∷
   rw 4 (q121 c4) ∷
   rw 3 (q34 c4) ∷
   rw 2 (q122 c4) ∷
   rw⁻ 3 (q120 c4) ∷
   rw 1 (q123 c4) ∷
   rw⁻ 3 (q124 c4) ∷
   rw⁻ 2 (q119 c4) ∷
   rw 3 (q125 c4) ∷
   rw 3 (q123 c4) ∷
   rw⁻ 0 (q9 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (CCZ014 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ014 ∷ []) (wp 215 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (CS02⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ []) (wl 818 (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (CCZ023 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl 458 (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (CCZ014 ∷ CS03 ∷ []) (CS03 ∷ CCZ014 ∷ []) (wp 157 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (CCZ014 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ []) (wp 308 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (CS23⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4))
  q133 : Ws → Eqn
  q133 c4 = eqn (CS23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (CCZ023 ∷ Toff023 ∷ []) (Toff023 ∷ CZ23 ∷ CCZ023 ∷ []) (wl 819 (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (CS23⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS23⁻ ∷ []) (wl 820 (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ []) (CS02⁻ ∷ []) (wl 821 (lit c4))

-- CSdu-box-3 @243243: 17 steps
lem-CSdu-box-3-at243243 : Ws → ⟪ (CS02⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at243243 c4 = derive (CS02⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS02⁻ ∷ [])
  (rw 1 (q126 c4) ∷
   rw⁻ 0 (q127 c4) ∷
   rw 1 (q128 c4) ∷
   rw 4 (q129 c4) ∷
   rw⁻ 8 (q130 c4) ∷
   rw⁻ 7 (q131 c4) ∷
   rw 6 (q132 c4) ∷
   rw⁻ 5 (q131 c4) ∷
   rw 4 (q133 c4) ∷
   rw⁻ 5 (q129 c4) ∷
   rw 3 (q132 c4) ∷
   rw⁻ 2 (q127 c4) ∷
   rw 5 (q134 c4) ∷
   rw 4 (q135 c4) ∷
   rw 3 (q128 c4) ∷
   rw 4 (q136 c4) ∷
   rw⁻ 0 (q126 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = eqn (CCZ014 ∷ CS02 ∷ []) (CS02 ∷ CCZ014 ∷ []) (wp 155 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (CS02 ∷ Toff023 ∷ []) (Toff023 ∷ CS02 ∷ CS23 ∷ CCZ023 ∷ []) (wl 822 (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (CS23 ∷ Toff023 ∷ []) (Toff023 ∷ CS23 ∷ []) (wl 823 (lit c4))
  q140 : Ws → Eqn
  q140 c4 = eqn (CS02 ∷ CS23 ∷ CCZ023 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ []) (CS02 ∷ []) (wl 824 (lit c4))

-- CSu-box-3 @243243: 17 steps
lem-CSu-box-3-at243243 : Ws → ⟪ (CS02 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS02 ∷ []) ⟫ʷ
lem-CSu-box-3-at243243 c4 = derive (CS02 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS02 ∷ [])
  (rw 1 (q126 c4) ∷
   rw⁻ 0 (q137 c4) ∷
   rw 1 (q138 c4) ∷
   rw 4 (q129 c4) ∷
   rw⁻ 8 (q130 c4) ∷
   rw⁻ 7 (q131 c4) ∷
   rw 6 (q132 c4) ∷
   rw⁻ 5 (q131 c4) ∷
   rw 4 (q133 c4) ∷
   rw⁻ 5 (q129 c4) ∷
   rw 3 (q133 c4) ∷
   rw⁻ 2 (q137 c4) ∷
   rw 5 (q134 c4) ∷
   rw 4 (q139 c4) ∷
   rw 3 (q138 c4) ∷
   rw 4 (q140 c4) ∷
   rw⁻ 0 (q126 c4) ∷ []) Eq.refl

private
  q141 : Ws → Eqn
  q141 c4 = eqn (Toff023 ∷ Bx0-1423 ∷ Toff023 ∷ []) (Bx0-1423 ∷ []) (lem-P-box-at243243 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (Toff023 ∷ Toff023 ∷ []) [] (wl 203 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (Bx0-2314 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at122331 c4)

-- pairs @243243: 4 steps
lem-pairs-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-pairs-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-2314 ∷ [])
  (rw⁻ 0 (q141 c4) ∷
   rw 1 (q126 c4) ∷
   rw 4 (q142 c4) ∷
   rw⁻ 0 (q143 c4) ∷ []) Eq.refl

private
  q144 : Ws → Eqn
  q144 c4 = eqn (Bx3-0124 ∷ []) (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (Bx3-1024 ∷ []) (Bx3-2410 ∷ []) (lem-pairs-at032032 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (Bx3-2410 ∷ []) (Bx3-2140 ∷ []) (lem-sym-bc-at0312243140 c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (Bx3-2140 ∷ []) (Bx3-1240 ∷ []) (lem-sym-ab-at0312213440 c4)

-- box-perm-2341 @03102132: 4 steps
lem-box-perm-2341-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-box-perm-2341-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-1240 ∷ [])
  (rw 0 (q144 c4) ∷
   rw 0 (q145 c4) ∷
   rw 0 (q146 c4) ∷
   rw 0 (q147 c4) ∷ []) Eq.refl

private
  q148 : Ws → Eqn
  q148 c4 = eqn (Toff301 ∷ Bx3-2410 ∷ Toff301 ∷ []) (Bx3-2410 ∷ []) (lem-P-box-at0312243140 c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (Bx3-2410 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243140 c4)
  q150 : Ws → Eqn
  q150 c4 = eqn (Toff301 ∷ Toff301 ∷ []) [] (wl 443 (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (Bx3-1024 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at032032 c4)

-- pairs @0312243140: 4 steps
lem-pairs-at0312243140 : Ws → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-pairs-at0312243140 c4 = derive (Bx3-2410 ∷ []) (Bx3-1024 ∷ [])
  (rw⁻ 0 (q148 c4) ∷
   rw 1 (q149 c4) ∷
   rw 4 (q150 c4) ∷
   rw⁻ 0 (q151 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = eqn (Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (CX23 ∷ CCZ034 ∷ []) (wp 104 c4)
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp 13 c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (CS02 ∷ Toff312 ∷ []) (Toff312 ∷ CS02 ∷ []) (wl 861 (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (CX04 ∷ Toff312 ∷ []) (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (CS24⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS24⁻ ∷ []) (wl 878 (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (CS24 ∷ Toff312 ∷ []) (Toff312 ∷ CS24 ∷ []) (wl 879 (lit c4))
  q159 : Ws → Eqn
  q159 c4 = eqn (CX23 ∷ Toff312 ∷ []) (Toff312 ∷ CX23 ∷ []) (wl 880 (lit c4))
  q160 : Ws → Eqn
  q160 c4 = eqn (CX23 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX23 ∷ []) (wp 110 c4)

-- CXu-box-4 @0310243142: 15 steps
lem-CXu-box-4-at0310243142 : Ws → ⟪ (CX23 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CX23 ∷ []) ⟫ʷ
lem-CXu-box-4-at0310243142 c4 = derive (CX23 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CX23 ∷ [])
  (rw 1 (q152 c4) ∷
   rw⁻ 0 (q153 c4) ∷
   rw 2 (q154 c4) ∷
   rw 6 (q155 c4) ∷
   rw 5 (q156 c4) ∷
   rw 4 (q157 c4) ∷
   rw 3 (q156 c4) ∷
   rw 2 (q158 c4) ∷
   rw⁻ 3 (q154 c4) ∷
   rw 1 (q159 c4) ∷
   rw 3 (q124 c4) ∷
   rw⁻ 2 (q153 c4) ∷
   rw 3 (q160 c4) ∷
   rw 3 (q159 c4) ∷
   rw⁻ 0 (q152 c4) ∷ []) Eq.refl

private
  q161 : Ws → Eqn
  q161 c4 = eqn (CCZ034 ∷ CS13 ∷ []) (CS13 ∷ CCZ034 ∷ []) (wp 312 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (CS13 ∷ Toff312 ∷ []) (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ []) (wl 881 (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl 297 (lit c4))
  q164 : Ws → Eqn
  q164 c4 = eqn (CCZ034 ∷ CS23 ∷ []) (CS23 ∷ CCZ034 ∷ []) (wp 314 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (CCZ034 ∷ CX31 ∷ []) (CX31 ∷ CCZ034 ∷ []) (wp 127 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (CS12⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4))
  q167 : Ws → Eqn
  q167 c4 = eqn (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4))
  q168 : Ws → Eqn
  q168 c4 = eqn (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (wl 882 (lit c4))
  q169 : Ws → Eqn
  q169 c4 = eqn (CS12 ∷ Toff312 ∷ []) (Toff312 ∷ CS12 ∷ []) (wl 883 (lit c4))
  q170 : Ws → Eqn
  q170 c4 = eqn (CS13 ∷ CS12 ∷ CCZ123 ∷ CS12 ∷ CZ12 ∷ CCZ123 ∷ []) (CS13 ∷ []) (wl 884 (lit c4))

-- CSu-box-3 @0310243142: 17 steps
lem-CSu-box-3-at0310243142 : Ws → ⟪ (CS13 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CS13 ∷ []) ⟫ʷ
lem-CSu-box-3-at0310243142 c4 = derive (CS13 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CS13 ∷ [])
  (rw 1 (q152 c4) ∷
   rw⁻ 0 (q161 c4) ∷
   rw 1 (q162 c4) ∷
   rw 4 (q163 c4) ∷
   rw⁻ 8 (q164 c4) ∷
   rw⁻ 7 (q165 c4) ∷
   rw 6 (q166 c4) ∷
   rw⁻ 5 (q165 c4) ∷
   rw 4 (q167 c4) ∷
   rw⁻ 5 (q163 c4) ∷
   rw 3 (q167 c4) ∷
   rw⁻ 2 (q161 c4) ∷
   rw 5 (q168 c4) ∷
   rw 4 (q169 c4) ∷
   rw 3 (q162 c4) ∷
   rw 4 (q170 c4) ∷
   rw⁻ 0 (q152 c4) ∷ []) Eq.refl

private
  q171 : Ws → Eqn
  q171 c4 = eqn (CCZ034 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ034 ∷ []) (wp 734 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (CS13⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ []) (wl 885 (lit c4))
  q173 : Ws → Eqn
  q173 c4 = eqn (CS12⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS12⁻ ∷ []) (wl 886 (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ CS12⁻ ∷ CZ12 ∷ CCZ123 ∷ []) (CS13⁻ ∷ []) (wl 887 (lit c4))

-- CSdu-box-3 @0310243142: 17 steps
lem-CSdu-box-3-at0310243142 : Ws → ⟪ (CS13⁻ ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0310243142 c4 = derive (CS13⁻ ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CS13⁻ ∷ [])
  (rw 1 (q152 c4) ∷
   rw⁻ 0 (q171 c4) ∷
   rw 1 (q172 c4) ∷
   rw 4 (q163 c4) ∷
   rw⁻ 8 (q164 c4) ∷
   rw⁻ 7 (q165 c4) ∷
   rw 6 (q166 c4) ∷
   rw⁻ 5 (q165 c4) ∷
   rw 4 (q167 c4) ∷
   rw⁻ 5 (q163 c4) ∷
   rw 3 (q166 c4) ∷
   rw⁻ 2 (q171 c4) ∷
   rw 5 (q168 c4) ∷
   rw 4 (q173 c4) ∷
   rw 3 (q172 c4) ∷
   rw 4 (q174 c4) ∷
   rw⁻ 0 (q152 c4) ∷ []) Eq.refl

private
  q175 : Ws → Eqn
  q175 c4 = eqn (CS03⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ []) (wl 904 (lit c4))
  q176 : Ws → Eqn
  q176 c4 = eqn (CCZ013 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl 905 (lit c4))
  q177 : Ws → Eqn
  q177 c4 = eqn (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) (wp 39 c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (CCZ024 ∷ CX03 ∷ []) (CX03 ∷ CCZ024 ∷ []) (wp 756 c4)
  q179 : Ws → Eqn
  q179 c4 = eqn (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) (wl 906 (lit c4))
  q180 : Ws → Eqn
  q180 c4 = eqn (CS13⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS13⁻ ∷ []) (wl 907 (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ []) (CS03⁻ ∷ []) (wl 908 (lit c4))

-- CSdu-box-3 @122441: 17 steps
lem-CSdu-box-3-at122441 : Ws → ⟪ (CS03⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at122441 c4 = derive (CS03⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS03⁻ ∷ [])
  (rw 1 (q3 c4) ∷
   rw⁻ 0 (q21 c4) ∷
   rw 1 (q175 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 8 (q177 c4) ∷
   rw⁻ 7 (q178 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 5 (q178 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 5 (q176 c4) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   rw 5 (q179 c4) ∷
   rw 4 (q180 c4) ∷
   rw 3 (q175 c4) ∷
   rw 4 (q181 c4) ∷
   rw⁻ 0 (q3 c4) ∷ []) Eq.refl

private
  q182 : Ws → Eqn
  q182 c4 = eqn (CS03 ∷ Toff013 ∷ []) (Toff013 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ []) (wl 909 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (CS13 ∷ Toff013 ∷ []) (Toff013 ∷ CS13 ∷ []) (wl 910 (lit c4))
  q184 : Ws → Eqn
  q184 c4 = eqn (CS03 ∷ CS13 ∷ CCZ013 ∷ CS13 ∷ CZ13 ∷ CCZ013 ∷ []) (CS03 ∷ []) (wl 911 (lit c4))

-- CSu-box-3 @122441: 17 steps
lem-CSu-box-3-at122441 : Ws → ⟪ (CS03 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS03 ∷ []) ⟫ʷ
lem-CSu-box-3-at122441 c4 = derive (CS03 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS03 ∷ [])
  (rw 1 (q3 c4) ∷
   rw⁻ 0 (q14 c4) ∷
   rw 1 (q182 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 8 (q177 c4) ∷
   rw⁻ 7 (q178 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 5 (q178 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 5 (q176 c4) ∷
   rw 3 (q17 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 5 (q179 c4) ∷
   rw 4 (q183 c4) ∷
   rw 3 (q182 c4) ∷
   rw 4 (q184 c4) ∷
   rw⁻ 0 (q3 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = eqn (Toff213 ∷ Bx2-0413 ∷ Toff213 ∷ []) (Bx2-0413 ∷ []) (lem-P-box-at0210243143 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (Toff213 ∷ Toff213 ∷ []) [] (wl 180 (lit c4))
  q187 : Ws → Eqn
  q187 c4 = eqn (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at022330 c4)

-- pairs @0210243143: 4 steps
lem-pairs-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-pairs-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-1304 ∷ [])
  (rw⁻ 0 (q185 c4) ∷
   rw 1 (q9 c4) ∷
   rw 4 (q186 c4) ∷
   rw⁻ 0 (q187 c4) ∷ []) Eq.refl

private
  q188 : Ws → Eqn
  q188 c4 = eqn (Bx0-2431 ∷ []) (Bx0-4231 ∷ []) (lem-sym-ab-at122441 c4)
  q189 : Ws → Eqn
  q189 c4 = eqn (Bx0-4231 ∷ []) (Bx0-4321 ∷ []) (lem-sym-bc-at1441 c4)
  q190 : Ws → Eqn
  q190 c4 = eqn (Bx0-4321 ∷ []) (Bx0-3421 ∷ []) (lem-sym-ab-at14233241 c4)
  q191 : Ws → Eqn
  q191 c4 = eqn (Bx0-3421 ∷ []) (Bx0-2134 ∷ []) (lem-pairs-at13243241 c4)

-- box-perm-1432 @122441: 4 steps
lem-box-perm-1432-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-box-perm-1432-at122441 c4 = derive (Bx0-2431 ∷ []) (Bx0-2134 ∷ [])
  (rw 0 (q188 c4) ∷
   rw 0 (q189 c4) ∷
   rw 0 (q190 c4) ∷
   rw 0 (q191 c4) ∷ []) Eq.refl

private
  q192 : Ws → Eqn
  q192 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym-ab-at021021 c4)
  q193 : Ws → Eqn
  q193 c4 = eqn (Bx2-1034 ∷ []) (Bx2-3410 ∷ []) (lem-pairs-at0220 c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (Bx2-3410 ∷ []) (Bx2-3140 ∷ []) (lem-sym-bc-at0213243140 c4)
  q195 : Ws → Eqn
  q195 c4 = eqn (Bx2-3140 ∷ []) (Bx2-1340 ∷ []) (lem-sym-ab-at0213213440 c4)

-- box-perm-2341 @021021: 4 steps
lem-box-perm-2341-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-box-perm-2341-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-1340 ∷ [])
  (rw 0 (q192 c4) ∷
   rw 0 (q193 c4) ∷
   rw 0 (q194 c4) ∷
   rw 0 (q195 c4) ∷ []) Eq.refl

private
  q196 : Ws → Eqn
  q196 c4 = eqn (Bx2-1340 ∷ []) (Bx2-3140 ∷ []) (lem-sym-ab-at02233440 c4)
  q197 : Ws → Eqn
  q197 c4 = eqn (Bx2-3140 ∷ []) (Bx2-3410 ∷ []) (lem-sym-bc-at0213213440 c4)
  q198 : Ws → Eqn
  q198 c4 = eqn (Bx2-3410 ∷ []) (Bx2-1034 ∷ []) (lem-pairs-at0213243140 c4)
  q199 : Ws → Eqn
  q199 c4 = eqn (Bx2-1034 ∷ []) (Bx2-0134 ∷ []) (lem-sym-ab-at0220 c4)

-- box-perm-4123 @02233440: 4 steps
lem-box-perm-4123-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-4123-at02233440 c4 = derive (Bx2-1340 ∷ []) (Bx2-0134 ∷ [])
  (rw 0 (q196 c4) ∷
   rw 0 (q197 c4) ∷
   rw 0 (q198 c4) ∷
   rw 0 (q199 c4) ∷ []) Eq.refl

private
  q200 : Ws → Eqn
  q200 c4 = eqn (Toff204 ∷ Bx2-1304 ∷ Toff204 ∷ []) (Bx2-1304 ∷ []) (lem-P-box-at022330 c4)
  q201 : Ws → Eqn
  q201 c4 = eqn (Bx2-1304 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at022330 c4)
  q202 : Ws → Eqn
  q202 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp 19 c4)
  q203 : Ws → Eqn
  q203 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4)

-- pairs @022330: 4 steps
lem-pairs-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-pairs-at022330 c4 = derive (Bx2-1304 ∷ []) (Bx2-0413 ∷ [])
  (rw⁻ 0 (q200 c4) ∷
   rw 1 (q201 c4) ∷
   rw 4 (q202 c4) ∷
   rw⁻ 0 (q203 c4) ∷ []) Eq.refl

private
  q204 : Ws → Eqn
  q204 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp 81 c4)
  q205 : Ws → Eqn
  q205 c4 = eqn (CS12 ∷ Toff213 ∷ []) (Toff213 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ []) (wl 964 (lit c4))
  q206 : Ws → Eqn
  q206 c4 = eqn (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl 326 (lit c4))
  q207 : Ws → Eqn
  q207 c4 = eqn (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) (wp 92 c4)
  q208 : Ws → Eqn
  q208 c4 = eqn (CCZ024 ∷ CX21 ∷ []) (CX21 ∷ CCZ024 ∷ []) (wp 749 c4)
  q209 : Ws → Eqn
  q209 c4 = eqn (CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) (wl 965 (lit c4))
  q210 : Ws → Eqn
  q210 c4 = eqn (CS13 ∷ Toff213 ∷ []) (Toff213 ∷ CS13 ∷ []) (wl 966 (lit c4))
  q211 : Ws → Eqn
  q211 c4 = eqn (CS12 ∷ CS13 ∷ CCZ123 ∷ CS13 ∷ CZ13 ∷ CCZ123 ∷ []) (CS12 ∷ []) (wl 967 (lit c4))

-- CSu-box-3 @0210243143: 17 steps
lem-CSu-box-3-at0210243143 : Ws → ⟪ (CS12 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12 ∷ []) ⟫ʷ
lem-CSu-box-3-at0210243143 c4 = derive (CS12 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12 ∷ [])
  (rw 1 (q9 c4) ∷
   rw⁻ 0 (q204 c4) ∷
   rw 1 (q205 c4) ∷
   rw 4 (q206 c4) ∷
   rw⁻ 8 (q207 c4) ∷
   rw⁻ 7 (q208 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 5 (q208 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 5 (q206 c4) ∷
   rw 3 (q17 c4) ∷
   rw⁻ 2 (q204 c4) ∷
   rw 5 (q209 c4) ∷
   rw 4 (q210 c4) ∷
   rw 3 (q205 c4) ∷
   rw 4 (q211 c4) ∷
   rw⁻ 0 (q9 c4) ∷ []) Eq.refl

private
  q212 : Ws → Eqn
  q212 c4 = eqn (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) (wp 87 c4)
  q213 : Ws → Eqn
  q213 c4 = eqn (CS12⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ []) (wl 968 (lit c4))
  q214 : Ws → Eqn
  q214 c4 = eqn (CS13⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS13⁻ ∷ []) (wl 969 (lit c4))
  q215 : Ws → Eqn
  q215 c4 = eqn (CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ CS13⁻ ∷ CZ13 ∷ CCZ123 ∷ []) (CS12⁻ ∷ []) (wl 970 (lit c4))

-- CSdu-box-3 @0210243143: 17 steps
lem-CSdu-box-3-at0210243143 : Ws → ⟪ (CS12⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0210243143 c4 = derive (CS12⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12⁻ ∷ [])
  (rw 1 (q9 c4) ∷
   rw⁻ 0 (q212 c4) ∷
   rw 1 (q213 c4) ∷
   rw 4 (q206 c4) ∷
   rw⁻ 8 (q207 c4) ∷
   rw⁻ 7 (q208 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 5 (q208 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 5 (q206 c4) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 2 (q212 c4) ∷
   rw 5 (q209 c4) ∷
   rw 4 (q214 c4) ∷
   rw 3 (q213 c4) ∷
   rw 4 (q215 c4) ∷
   rw⁻ 0 (q9 c4) ∷ []) Eq.refl
