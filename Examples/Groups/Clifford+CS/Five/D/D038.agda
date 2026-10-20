{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D038 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-nf-order-CSat0 ; lem-nf-order-CSat1 ; lem-nf-order-CSat2)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0210243143 ; lem-box-cP-at12233441 ; lem-box-cP-at122441 ; lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-box-perm-1324-at122441 ; lem-box2)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-CSdu-box-3-at0210243143 ; lem-CSdu-box-3-at122441 ; lem-CSu-box-3-at0210243143 ; lem-CSu-box-3-at122441 ; lem-box-perm-1432-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-CKu-box-2-at0210243143 ; lem-CKu-box-2-at122441 ; lem-CKu-box-2-at243243 ; lem-box-box-1-at021021 ; lem-box-perm-1342-at0210243143 ; lem-box-perm-1423-at021021 ; lem-box-perm-1432-at1221 ; lem-box-perm-3241-at243243 ; lem-box-perm-4213-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-CKc-box ; lem-CKdc-box ; lem-S2-SBOX⟨0·1·42·3⟩ ; lem-S2-SBOX⟨0·2·43·1⟩ ; lem-S2-SBOX⟨2·0·41·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CS23-CCZ014 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-CX14-TOFF023 ; lem-comm-CX23-CCZ014 ; lem-comm-CZ13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CS13 ; lem-comm-CCZ024-CSd13 ; lem-comm-CCZ024-CX13 ; lem-comm-CCZ024-CX31 ; lem-comm-CCZ124-CS03 ; lem-comm-CX23-TOFF014 ; lem-comm-TOFF014-CX23 ; lem-comm-TOFF213-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CX14)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (X4 ∷ CCZ024 ∷ []) (wp 20 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CZ02 ∷ Toff013 ∷ []) (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl 232 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Toff013 ∷ X4 ∷ []) (X4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl 242 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp 81 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ024 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ024 ∷ []) (wp 91 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) (wp 92 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ024 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ024 ∷ []) (wp 23 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) (wl 185 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) (wl 234 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CS03⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3-at122441 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl 190 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) (wp 33 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp 34 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) (wp 35 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp 36 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) (wp 37 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) (Toff314 ∷ Toff013 ∷ []) (wp 783 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) (Toff014 ∷ CCZ024 ∷ []) (wp 784 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl 256 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS14 ∷ Toff013 ∷ []) (Toff013 ∷ CS14 ∷ []) (wp 785 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) (wl 872 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS24⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS24 ∷ Toff013 ∷ []) (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Toff013 ∷ Toff014 ∷ []) (Toff014 ∷ Toff013 ∷ []) (wp 786 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ124 ∷ []) (Toff014 ∷ CCZ124 ∷ Toff014 ∷ []) (wp 787 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS03 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS03 ∷ []) (lem-CSu-box-3-at122441 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0134 ∷ []) (lem-box-perm-1342-at0210243143 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2134 ∷ []) (lem-box-perm-1432-at122441 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx2-0134 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ Bx2-0134 ∷ []) (lem-box-box-1-at021021 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2431 ∷ []) (lem-box-perm-1432-at1221 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx2-0134 ∷ []) (Bx2-0413 ∷ []) (lem-box-perm-1423-at021021 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx2-0413 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) (wl 965 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CZ13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CZ13 ∷ CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ123 ∷ []) (wl 971 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ123 ∷ CCZ124 ∷ Toff314 ∷ []) (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl 972 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ124 ∷ CS03 ∷ []) (CS03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CS03 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ123 ∷ CS03 ∷ []) (CS03 ∷ CCZ123 ∷ []) (wl 490 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ123 ∷ CCZ124 ∷ CCZ124 ∷ Toff314 ∷ []) (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ []) (wl 973 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ123 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ123 ∷ []) (wl 495 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) (wl 892 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl 181 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ124 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ124 ∷ []) (wl 974 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl 263 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CX31 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ []) (wl 975 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CX31 ∷ Toff134 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX31 ∷ Toff134 ∷ []) (wp 788 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CX31 ∷ CX32 ∷ Toff213 ∷ []) (Toff213 ∷ CX31 ∷ []) (wl 976 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) (Toff213 ∷ Toff134 ∷ []) (wl 977 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ024 ∷ CX31 ∷ []) (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ024 ∷ CX32 ∷ []) (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp 789 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) (wl 241 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) (wp 89 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) (wp 88 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ024 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp 790 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CX32 ∷ Toff213 ∷ []) (Toff213 ∷ CX32 ∷ []) (wl 809 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp 352 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ []) (wl 808 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Toff213 ∷ CX04 ∷ []) (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CS34⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS34⁻ ∷ []) (wl 807 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) (wl 196 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (Toff213 ∷ Toff234 ∷ []) (Toff234 ∷ Toff213 ∷ []) (wl 942 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CX31 ∷ CX32 ∷ CX32 ∷ []) (CX31 ∷ []) (wl 978 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (Toff134 ∷ Toff234 ∷ Toff234 ∷ []) (Toff134 ∷ []) (wl 979 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CX31 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) (CX31 ∷ Toff134 ∷ []) (wp 791 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (Toff134 ∷ X4 ∷ []) (X4 ∷ CX31 ∷ Toff134 ∷ []) (wl 235 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ []) (wl 980 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CS03⁻ ∷ CS12 ∷ []) (CS12 ∷ CS03⁻ ∷ []) (wl 981 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (CS12 ∷ Toff314 ∷ []) (Toff314 ∷ CS12 ∷ []) (wl 982 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (CS03 ∷ CS12 ∷ []) (CS12 ∷ CS03 ∷ []) (wl 983 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (CS12 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12 ∷ []) (lem-CSu-box-3-at0210243143 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ []) (wl 984 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CS03⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS03⁻ ∷ []) (wl 469 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (CS12⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS12⁻ ∷ []) (wl 985 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (CS03 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS03 ∷ []) (wl 986 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (CS12⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12⁻ ∷ []) (lem-CSdu-box-3-at0210243143 c4)

-- F4-CS0-CS2: 284 steps
lem-F4-CS0-CS2 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-CS2 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw⁻ 13 (q15 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   rw 8 (q22 c4) ∷
   rw 12 (q23 c4) ∷
   rw 11 (q24 c4) ∷
   rw 10 (q25 c4) ∷
   rw 9 (q24 c4) ∷
   rw 8 (q26 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw⁻ 8 (q28 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 3 1 (CS03 ∷ []) ∷
   rw 3 (q29 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw⁻ 11 (q15 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q18 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw 6 (q22 c4) ∷
   rw 10 (q23 c4) ∷
   rw 9 (q24 c4) ∷
   rw 8 (q25 c4) ∷
   rw 7 (q24 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q30 c4) ∷
   rw 2 (q31 c4) ∷
   rw 1 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 3 (q35 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 3 (q36 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 4 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw 3 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 5 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw 8 (q43 c4) ∷
   rw 9 (q44 c4) ∷
   rw 10 (q45 c4) ∷
   rw 3 (q46 c4) ∷
   rw 4 (q40 c4) ∷
   rw 5 (q47 c4) ∷
   re 4 1 (Sb2-0-3-1 ∷ []) ∷
   re 6 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 2 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 3 (q48 c4) ∷
   re 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 4 1 (CS03 ∷ []) ∷
   re 6 1 (CS03⁻ ∷ []) ∷
   rw⁻ 3 (q49 c4) ∷
   rw 2 (q35 c4) ∷
   rw⁻ 5 (q50 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw 4 (q52 c4) ∷
   rw 5 (q53 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw 7 (q55 c4) ∷
   rw 8 (q18 c4) ∷
   rw 9 (q56 c4) ∷
   rw 10 (q17 c4) ∷
   rw 11 (q56 c4) ∷
   rw 12 (q16 c4) ∷
   rw 13 (q57 c4) ∷
   rw 7 (q54 c4) ∷
   rw 8 (q58 c4) ∷
   rw⁻ 3 (q50 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 7 (q60 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw 7 (q62 c4) ∷
   rw⁻ 8 (q63 c4) ∷
   rw 9 (q62 c4) ∷
   rw⁻ 10 (q64 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw 9 (q65 c4) ∷
   rw 11 (q60 c4) ∷
   rw⁻ 10 (q61 c4) ∷
   rw 11 (q62 c4) ∷
   rw⁻ 12 (q63 c4) ∷
   rw 13 (q62 c4) ∷
   rw⁻ 14 (q64 c4) ∷
   rw⁻ 10 (q60 c4) ∷
   rw 3 (q66 c4) ∷
   rw 5 (q67 c4) ∷
   rw 3 (q68 c4) ∷
   rw 2 (q52 c4) ∷
   rw⁻ 4 (q54 c4) ∷
   rw 3 (q55 c4) ∷
   rw 4 (q18 c4) ∷
   rw 5 (q56 c4) ∷
   rw 6 (q17 c4) ∷
   rw 7 (q56 c4) ∷
   rw 8 (q16 c4) ∷
   rw 9 (q57 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 1 (q69 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 7 (q71 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 2 (q70 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   re 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 6 1 (CS03 ∷ []) ∷
   re 8 1 (CS03⁻ ∷ []) ∷
   rw⁻ 5 (q49 c4) ∷
   rw 4 (q35 c4) ∷
   rw⁻ 7 (q50 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   rw 6 (q52 c4) ∷
   rw 7 (q53 c4) ∷
   rw⁻ 10 (q54 c4) ∷
   rw 9 (q55 c4) ∷
   rw 10 (q18 c4) ∷
   rw 11 (q56 c4) ∷
   rw 12 (q17 c4) ∷
   rw 13 (q56 c4) ∷
   rw 14 (q16 c4) ∷
   rw 15 (q57 c4) ∷
   rw 9 (q54 c4) ∷
   rw 10 (q58 c4) ∷
   rw⁻ 5 (q50 c4) ∷
   rw⁻ 7 (q59 c4) ∷
   rw 9 (q60 c4) ∷
   rw⁻ 8 (q61 c4) ∷
   rw 9 (q62 c4) ∷
   rw⁻ 10 (q63 c4) ∷
   rw 11 (q62 c4) ∷
   rw⁻ 12 (q64 c4) ∷
   rw⁻ 8 (q60 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   rw 11 (q65 c4) ∷
   rw 13 (q60 c4) ∷
   rw⁻ 12 (q61 c4) ∷
   rw 13 (q62 c4) ∷
   rw⁻ 14 (q63 c4) ∷
   rw 15 (q62 c4) ∷
   rw⁻ 16 (q64 c4) ∷
   rw⁻ 12 (q60 c4) ∷
   rw 5 (q66 c4) ∷
   rw 7 (q67 c4) ∷
   rw 5 (q68 c4) ∷
   rw 4 (q52 c4) ∷
   rw⁻ 6 (q54 c4) ∷
   rw 5 (q55 c4) ∷
   rw 6 (q18 c4) ∷
   rw 7 (q56 c4) ∷
   rw 8 (q17 c4) ∷
   rw 9 (q56 c4) ∷
   rw 10 (q16 c4) ∷
   rw 11 (q57 c4) ∷
   rw 5 (q54 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 3 (q69 c4) ∷
   rw⁻ 6 (q75 c4) ∷
   re 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 7 1 (CS03 ∷ []) ∷
   re 9 1 (CS03⁻ ∷ []) ∷
   rw 9 (q76 c4) ∷
   rw⁻ 8 (q77 c4) ∷
   rw 7 (q78 c4) ∷
   rw⁻ 6 (q77 c4) ∷
   rw⁻ 5 (q79 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 4 (q75 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (CS13⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4))
  q81 : Ws → Eqn
  q81 c4 = eqn (CS13⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS13⁻ ∷ []) (wl 907 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (Bx0-2341 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (Toff324 ∷ CCZ023 ∷ []) (wp 814 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp 815 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) (wl 217 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (K3⁻ ∷ Toff014 ∷ []) (Toff014 ∷ K3⁻ ∷ []) (wp 816 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (CS24 ∷ Toff014 ∷ []) (Toff014 ∷ CS24 ∷ []) (wp 817 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CX23 ∷ Toff014 ∷ []) (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (CS34⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS34⁻ ∷ []) (wp 818 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (CS34 ∷ Toff014 ∷ []) (Toff014 ∷ CS34 ∷ []) (wp 546 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (K3 ∷ Toff014 ∷ []) (Toff014 ∷ K3 ∷ []) (wp 819 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl 220 (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (CCZ023 ∷ CS12 ∷ []) (CS12 ∷ CCZ023 ∷ []) (wl 621 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (CX14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (CCZ023 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ023 ∷ []) (wp 820 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (CCZ023 ∷ CS24 ∷ []) (CS24 ∷ CCZ023 ∷ []) (wp 513 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (CCZ023 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ023 ∷ []) (wp 669 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (Toff324 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff324 ∷ []) (wp 821 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ []) (wp 822 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (CS13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (CS13 ∷ Toff013 ∷ []) (Toff013 ∷ CS13 ∷ []) (wl 910 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (Bx0-1423 ∷ []) (Bx0-2431 ∷ []) (lem-box-perm-3241-at243243 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Bx0-2431 ∷ []) (Bx0-1423 ∷ []) (lem-box-perm-4213-at122441 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl 207 (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp 53 c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ014 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ []) (wp 54 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (CS23⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CS23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) (wl 209 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (CCZ123 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ []) (Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) (wl 1010 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (CCZ124 ∷ CS13 ∷ Toff324 ∷ []) (CS13 ∷ Toff324 ∷ CCZ124 ∷ []) (wl 1011 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (CX31 ∷ Toff134 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX31 ∷ Toff134 ∷ []) (wl 1012 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (CX31 ∷ Toff023 ∷ []) (Toff023 ∷ CX31 ∷ []) (wl 832 (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (Toff134 ∷ []) (wl 1013 (lit c4))
  q117 : Ws → Eqn
  q117 c4 = eqn (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) (wl 735 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (CS34 ∷ Toff023 ∷ []) (Toff023 ∷ CS34 ∷ []) (wp 725 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (Toff023 ∷ CX14 ∷ []) (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (CS34⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS34⁻ ∷ []) (wp 823 c4)
  q121 : Ws → Eqn
  q121 c4 = eqn (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) (wl 222 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (K1⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K1⁻ ∷ []) (wl 1014 (lit c4))
  q123 : Ws → Eqn
  q123 c4 = eqn (CCZ014 ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) (wp 824 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (CS12 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS12 ∷ []) (wl 1015 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = eqn (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) (wl 221 (lit c4))
  q126 : Ws → Eqn
  q126 c4 = eqn (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) (wp 67 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (CS12⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS12⁻ ∷ []) (wl 1016 (lit c4))
  q128 : Ws → Eqn
  q128 c4 = eqn (CS12⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS12⁻ ∷ []) (wl 1017 (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (CCZ014 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ014 ∷ []) (wp 265 c4)

-- F4-CS1-CS2: 248 steps
lem-F4-CS1-CS2 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-CS2 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw 5 (q80 c4) ∷
   rw 6 (q81 c4) ∷
   rw 7 (q80 c4) ∷
   rw 8 (q81 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 5 (q82 c4) ∷
   rw 5 (q83 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw 6 (q85 c4) ∷
   rw⁻ 5 (q86 c4) ∷
   rw 11 (q87 c4) ∷
   rw 10 (q88 c4) ∷
   rw 9 (q89 c4) ∷
   rw 8 (q90 c4) ∷
   rw 7 (q89 c4) ∷
   rw 6 (q91 c4) ∷
   rw 5 (q92 c4) ∷
   rw 6 (q86 c4) ∷
   rw 8 (q93 c4) ∷
   rw⁻ 12 (q94 c4) ∷
   rw 11 (q95 c4) ∷
   rw⁻ 10 (q96 c4) ∷
   rw 9 (q95 c4) ∷
   rw⁻ 8 (q97 c4) ∷
   rw⁻ 9 (q93 c4) ∷
   rw⁻ 7 (q98 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 7 (q99 c4) ∷
   rw 8 (q100 c4) ∷
   rw⁻ 7 (q86 c4) ∷
   rw 13 (q87 c4) ∷
   rw 12 (q88 c4) ∷
   rw 11 (q89 c4) ∷
   rw 10 (q90 c4) ∷
   rw 9 (q89 c4) ∷
   rw 8 (q91 c4) ∷
   rw 7 (q92 c4) ∷
   rw 8 (q86 c4) ∷
   rw⁻ 4 (q83 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   re 3 1 (CS13 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw 3 (q101 c4) ∷
   rw 4 (q102 c4) ∷
   rw 5 (q101 c4) ∷
   rw 6 (q102 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q82 c4) ∷
   rw 3 (q83 c4) ∷
   rw⁻ 2 (q84 c4) ∷
   rw 4 (q85 c4) ∷
   rw⁻ 3 (q86 c4) ∷
   rw 9 (q87 c4) ∷
   rw 8 (q88 c4) ∷
   rw 7 (q89 c4) ∷
   rw 6 (q90 c4) ∷
   rw 5 (q89 c4) ∷
   rw 4 (q91 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q86 c4) ∷
   rw 6 (q93 c4) ∷
   rw⁻ 10 (q94 c4) ∷
   rw 9 (q95 c4) ∷
   rw⁻ 8 (q96 c4) ∷
   rw 7 (q95 c4) ∷
   rw⁻ 6 (q97 c4) ∷
   rw⁻ 7 (q93 c4) ∷
   rw⁻ 5 (q98 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw 5 (q99 c4) ∷
   rw 6 (q100 c4) ∷
   rw⁻ 5 (q86 c4) ∷
   rw 11 (q87 c4) ∷
   rw 10 (q88 c4) ∷
   rw 9 (q89 c4) ∷
   rw 8 (q90 c4) ∷
   rw 7 (q89 c4) ∷
   rw 6 (q91 c4) ∷
   rw 5 (q92 c4) ∷
   rw 6 (q86 c4) ∷
   rw⁻ 2 (q83 c4) ∷
   rw⁻ 2 (q82 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q104 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 3 (q105 c4) ∷
   rw 2 (q106 c4) ∷
   rw⁻ 6 (q107 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw 4 (q109 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw 2 (q110 c4) ∷
   rw⁻ 3 (q106 c4) ∷
   rw 3 (q111 c4) ∷
   rw 4 (q106 c4) ∷
   rw⁻ 8 (q107 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   rw 6 (q109 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw 4 (q110 c4) ∷
   rw⁻ 5 (q106 c4) ∷
   rw 5 (q111 c4) ∷
   rw⁻ 2 (q105 c4) ∷
   rw 3 (q112 c4) ∷
   rw 10 (q45 c4) ∷
   rw 4 (q113 c4) ∷
   rw 6 (q47 c4) ∷
   re 4 1 (Sb0-1-3-2 ∷ []) ∷
   re 6 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 2 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 3 (q48 c4) ∷
   re 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 4 1 (CS13 ∷ []) ∷
   re 6 1 (CS13⁻ ∷ []) ∷
   rw⁻ 3 (q114 c4) ∷
   rw 2 (q105 c4) ∷
   rw⁻ 5 (q115 c4) ∷
   rw⁻ 7 (q116 c4) ∷
   rw⁻ 6 (q117 c4) ∷
   rw⁻ 7 (q118 c4) ∷
   rw 8 (q119 c4) ∷
   rw⁻ 9 (q120 c4) ∷
   rw 10 (q119 c4) ∷
   rw⁻ 11 (q121 c4) ∷
   rw⁻ 12 (q122 c4) ∷
   rw 6 (q116 c4) ∷
   rw 4 (q123 c4) ∷
   rw⁻ 3 (q115 c4) ∷
   rw⁻ 5 (q116 c4) ∷
   rw⁻ 4 (q117 c4) ∷
   rw⁻ 5 (q118 c4) ∷
   rw 6 (q119 c4) ∷
   rw⁻ 7 (q120 c4) ∷
   rw 8 (q119 c4) ∷
   rw⁻ 9 (q121 c4) ∷
   rw⁻ 10 (q122 c4) ∷
   rw 4 (q116 c4) ∷
   rw 2 (q123 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 1 (q69 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q124 c4) ∷
   rw 3 (q105 c4) ∷
   rw⁻ 6 (q125 c4) ∷
   rw 5 (q126 c4) ∷
   rw⁻ 4 (q125 c4) ∷
   rw 3 (q126 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 2 (q70 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   re 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 6 1 (CS13 ∷ []) ∷
   re 8 1 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q114 c4) ∷
   rw 4 (q105 c4) ∷
   rw⁻ 7 (q115 c4) ∷
   rw⁻ 9 (q116 c4) ∷
   rw⁻ 8 (q117 c4) ∷
   rw⁻ 9 (q118 c4) ∷
   rw 10 (q119 c4) ∷
   rw⁻ 11 (q120 c4) ∷
   rw 12 (q119 c4) ∷
   rw⁻ 13 (q121 c4) ∷
   rw⁻ 14 (q122 c4) ∷
   rw 8 (q116 c4) ∷
   rw 6 (q123 c4) ∷
   rw⁻ 5 (q115 c4) ∷
   rw⁻ 7 (q116 c4) ∷
   rw⁻ 6 (q117 c4) ∷
   rw⁻ 7 (q118 c4) ∷
   rw 8 (q119 c4) ∷
   rw⁻ 9 (q120 c4) ∷
   rw 10 (q119 c4) ∷
   rw⁻ 11 (q121 c4) ∷
   rw⁻ 12 (q122 c4) ∷
   rw 6 (q116 c4) ∷
   rw 4 (q123 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   re 8 1 (Sb0-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 6 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 3 (q69 c4) ∷
   rw⁻ 6 (q75 c4) ∷
   re 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 7 1 (CS13 ∷ []) ∷
   re 9 1 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q127 c4) ∷
   rw 5 (q105 c4) ∷
   rw⁻ 8 (q128 c4) ∷
   rw 7 (q129 c4) ∷
   rw⁻ 6 (q128 c4) ∷
   rw 5 (q129 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   re 8 1 (Sb0-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 6 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 4 (q75 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = eqn (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (X4 ∷ CCZ014 ∷ []) (wp 52 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl 206 (lit c4))
  q132 : Ws → Eqn
  q132 c4 = eqn (Toff023 ∷ X4 ∷ []) (X4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))
  q133 : Ws → Eqn
  q133 c4 = eqn (CCZ014 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ014 ∷ []) (wp 55 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (X4 ∷ CZ01 ∷ CZ01 ∷ []) (X4 ∷ []) (wl 208 (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ014 ∷ []) (wp 835 c4)
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ034 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) (wp 793 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (CX14 ∷ Toff023 ∷ []) (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl 274 (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) (wp 62 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (CX23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4))
  q141 : Ws → Eqn
  q141 c4 = eqn (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) (wp 63 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) (wp 64 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ014 ∷ []) (wp 124 c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (Toff134 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff134 ∷ []) (wp 836 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (CCZ234 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ234 ∷ []) (wp 278 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ123 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ []) (wl 1031 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (CCZ234 ∷ CS12 ∷ Toff134 ∷ []) (CS12 ∷ Toff134 ∷ CCZ234 ∷ []) (wl 1032 (lit c4))
  q148 : Ws → Eqn
  q148 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl 305 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (CX23 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ []) (wl 894 (lit c4))
  q150 : Ws → Eqn
  q150 c4 = eqn (CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX23 ∷ Toff324 ∷ []) (wl 1033 (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (Toff014 ∷ CX23 ∷ []) (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4))
  q152 : Ws → Eqn
  q152 c4 = eqn (CCZ023 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp 837 c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (CZ02 ∷ CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CZ02 ∷ []) (wp 838 c4)
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ []) (wp 839 c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (CZ02 ∷ CCZ024 ∷ []) (CZ02 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp 840 c4)
  q156 : Ws → Eqn
  q156 c4 = eqn (CCZ023 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ []) (CX23 ∷ Toff324 ∷ CCZ023 ∷ []) (wp 841 c4)
  q157 : Ws → Eqn
  q157 c4 = eqn (Toff324 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ Toff324 ∷ []) (wl 211 (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ []) (wl 896 (lit c4))
  q159 : Ws → Eqn
  q159 c4 = eqn (CS13 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13 ∷ []) (wl 1034 (lit c4))
  q160 : Ws → Eqn
  q160 c4 = eqn (CCZ024 ∷ CS13 ∷ []) (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4))
  q161 : Ws → Eqn
  q161 c4 = eqn (CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ []) (wl 900 (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13⁻ ∷ []) (wl 1035 (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (CCZ024 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4))

-- F4-CS2-CS1: 254 steps
lem-F4-CS2-CS1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-CS1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q105 c4) ∷
   rw⁻ 2 (q130 c4) ∷
   rw 4 (q131 c4) ∷
   rw⁻ 3 (q132 c4) ∷
   rw 6 (q106 c4) ∷
   rw⁻ 10 (q107 c4) ∷
   rw⁻ 9 (q108 c4) ∷
   rw 8 (q109 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   rw 6 (q110 c4) ∷
   rw⁻ 7 (q106 c4) ∷
   rw⁻ 5 (q133 c4) ∷
   rw⁻ 4 (q130 c4) ∷
   rw 5 (q134 c4) ∷
   rw 6 (q111 c4) ∷
   rw⁻ 5 (q132 c4) ∷
   rw⁻ 2 (q105 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 6 (q105 c4) ∷
   rw⁻ 5 (q129 c4) ∷
   rw 6 (q128 c4) ∷
   rw⁻ 7 (q129 c4) ∷
   rw 8 (q128 c4) ∷
   rw⁻ 5 (q105 c4) ∷
   rw 5 (q105 c4) ∷
   rw⁻ 4 (q135 c4) ∷
   rw 6 (q136 c4) ∷
   rw⁻ 5 (q116 c4) ∷
   rw 11 (q122 c4) ∷
   rw 10 (q121 c4) ∷
   rw 9 (q137 c4) ∷
   rw 8 (q120 c4) ∷
   rw 7 (q137 c4) ∷
   rw 6 (q118 c4) ∷
   rw 5 (q117 c4) ∷
   rw 6 (q116 c4) ∷
   rw 8 (q138 c4) ∷
   rw⁻ 12 (q139 c4) ∷
   rw 11 (q140 c4) ∷
   rw⁻ 10 (q141 c4) ∷
   rw 9 (q140 c4) ∷
   rw⁻ 8 (q142 c4) ∷
   rw⁻ 9 (q138 c4) ∷
   rw⁻ 7 (q143 c4) ∷
   rw⁻ 6 (q135 c4) ∷
   rw 7 (q144 c4) ∷
   rw 8 (q145 c4) ∷
   rw⁻ 7 (q116 c4) ∷
   rw 13 (q122 c4) ∷
   rw 12 (q121 c4) ∷
   rw 11 (q137 c4) ∷
   rw 10 (q120 c4) ∷
   rw 9 (q137 c4) ∷
   rw 8 (q118 c4) ∷
   rw 7 (q117 c4) ∷
   rw 8 (q116 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw 4 (q105 c4) ∷
   rw⁻ 3 (q126 c4) ∷
   rw 4 (q125 c4) ∷
   rw⁻ 5 (q126 c4) ∷
   rw 6 (q125 c4) ∷
   rw⁻ 3 (q105 c4) ∷
   rw 3 (q105 c4) ∷
   rw⁻ 2 (q135 c4) ∷
   rw 4 (q136 c4) ∷
   rw⁻ 3 (q116 c4) ∷
   rw 9 (q122 c4) ∷
   rw 8 (q121 c4) ∷
   rw 7 (q137 c4) ∷
   rw 6 (q120 c4) ∷
   rw 5 (q137 c4) ∷
   rw 4 (q118 c4) ∷
   rw 3 (q117 c4) ∷
   rw 4 (q116 c4) ∷
   rw 6 (q138 c4) ∷
   rw⁻ 10 (q139 c4) ∷
   rw 9 (q140 c4) ∷
   rw⁻ 8 (q141 c4) ∷
   rw 7 (q140 c4) ∷
   rw⁻ 6 (q142 c4) ∷
   rw⁻ 7 (q138 c4) ∷
   rw⁻ 5 (q143 c4) ∷
   rw⁻ 4 (q135 c4) ∷
   rw 5 (q144 c4) ∷
   rw 6 (q145 c4) ∷
   rw⁻ 5 (q116 c4) ∷
   rw 11 (q122 c4) ∷
   rw 10 (q121 c4) ∷
   rw 9 (q137 c4) ∷
   rw 8 (q120 c4) ∷
   rw 7 (q137 c4) ∷
   rw 6 (q118 c4) ∷
   rw 5 (q117 c4) ∷
   rw 6 (q116 c4) ∷
   rw⁻ 2 (q105 c4) ∷
   rw 1 (q104 c4) ∷
   rw 2 (q103 c4) ∷
   rw 1 (q105 c4) ∷
   rw⁻ 0 (q130 c4) ∷
   rw 2 (q131 c4) ∷
   rw⁻ 1 (q132 c4) ∷
   rw 4 (q106 c4) ∷
   rw⁻ 8 (q107 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   rw 6 (q109 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw 4 (q110 c4) ∷
   rw⁻ 5 (q106 c4) ∷
   rw⁻ 3 (q133 c4) ∷
   rw⁻ 2 (q130 c4) ∷
   rw 3 (q134 c4) ∷
   rw 4 (q111 c4) ∷
   rw⁻ 3 (q132 c4) ∷
   rw⁻ 0 (q105 c4) ∷
   rw 3 (q1 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 3 (q12 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 3 (q146 c4) ∷
   rw 10 (q45 c4) ∷
   rw 4 (q147 c4) ∷
   rw 6 (q148 c4) ∷
   re 4 1 (Sb0-2-1-3 ∷ []) ∷
   re 6 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 2 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 3 (q149 c4) ∷
   re 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 4 1 (CS12 ∷ []) ∷
   re 6 1 (CS12⁻ ∷ []) ∷
   rw⁻ 3 (q150 c4) ∷
   rw 2 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 5 (q151 c4) ∷
   rw⁻ 7 (q86 c4) ∷
   rw⁻ 6 (q92 c4) ∷
   rw⁻ 7 (q91 c4) ∷
   rw 8 (q151 c4) ∷
   rw⁻ 9 (q90 c4) ∷
   rw 10 (q151 c4) ∷
   rw⁻ 11 (q88 c4) ∷
   rw⁻ 12 (q87 c4) ∷
   rw 6 (q86 c4) ∷
   rw 4 (q152 c4) ∷
   rw 3 (q151 c4) ∷
   rw⁻ 5 (q86 c4) ∷
   rw⁻ 4 (q92 c4) ∷
   rw⁻ 5 (q91 c4) ∷
   rw 6 (q151 c4) ∷
   rw⁻ 7 (q90 c4) ∷
   rw 8 (q151 c4) ∷
   rw⁻ 9 (q88 c4) ∷
   rw⁻ 10 (q87 c4) ∷
   rw 4 (q86 c4) ∷
   rw⁻ 5 (q153 c4) ∷
   rw⁻ 7 (q154 c4) ∷
   rw⁻ 5 (q155 c4) ∷
   rw 2 (q156 c4) ∷
   rw⁻ 4 (q83 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   re 6 1 (Sb0-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 1 (q157 c4) ∷
   rw⁻ 4 (q158 c4) ∷
   re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q159 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 6 (q102 c4) ∷
   rw 5 (q160 c4) ∷
   rw⁻ 4 (q102 c4) ∷
   rw 3 (q160 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (Sb0-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 2 (q158 c4) ∷
   rw⁻ 5 (q149 c4) ∷
   re 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 6 1 (CS12 ∷ []) ∷
   re 8 1 (CS12⁻ ∷ []) ∷
   rw⁻ 5 (q150 c4) ∷
   rw 4 (q82 c4) ∷
   rw 4 (q83 c4) ∷
   rw 7 (q151 c4) ∷
   rw⁻ 9 (q86 c4) ∷
   rw⁻ 8 (q92 c4) ∷
   rw⁻ 9 (q91 c4) ∷
   rw 10 (q151 c4) ∷
   rw⁻ 11 (q90 c4) ∷
   rw 12 (q151 c4) ∷
   rw⁻ 13 (q88 c4) ∷
   rw⁻ 14 (q87 c4) ∷
   rw 8 (q86 c4) ∷
   rw 6 (q152 c4) ∷
   rw 5 (q151 c4) ∷
   rw⁻ 7 (q86 c4) ∷
   rw⁻ 6 (q92 c4) ∷
   rw⁻ 7 (q91 c4) ∷
   rw 8 (q151 c4) ∷
   rw⁻ 9 (q90 c4) ∷
   rw 10 (q151 c4) ∷
   rw⁻ 11 (q88 c4) ∷
   rw⁻ 12 (q87 c4) ∷
   rw 6 (q86 c4) ∷
   rw⁻ 7 (q153 c4) ∷
   rw⁻ 9 (q154 c4) ∷
   rw⁻ 7 (q155 c4) ∷
   rw 4 (q156 c4) ∷
   rw⁻ 6 (q83 c4) ∷
   rw⁻ 6 (q82 c4) ∷
   re 8 1 (Sb0-2-1-3 ∷ []) ∷
   re 10 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 6 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 3 (q157 c4) ∷
   rw⁻ 6 (q161 c4) ∷
   re 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 7 1 (CS12 ∷ []) ∷
   re 9 1 (CS12⁻ ∷ []) ∷
   rw⁻ 6 (q162 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 8 (q81 c4) ∷
   rw 7 (q163 c4) ∷
   rw⁻ 6 (q81 c4) ∷
   rw 5 (q163 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 8 1 (Sb0-2-1-3 ∷ []) ∷
   re 10 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 6 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 4 (q161 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q164 : Ws → Eqn
  q164 c4 = eqn (CK40 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CK40 ∷ []) (lem-CKu-box-2-at243243 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (CK40 ∷ Toff324 ∷ []) (Toff324 ∷ CK40 ∷ []) (wp 870 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (CK40 ∷ CS13 ∷ []) (CS13 ∷ CK40 ∷ []) (wp 871 c4)
  q167 : Ws → Eqn
  q167 c4 = eqn (CK40 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CK40 ∷ []) (wp 872 c4)

-- F2-K0-CS1: 11 steps
lem-F2-K0-CS1 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-CS1 c4 = derive (CK40 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK40 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 0 (q164 c4) ∷
   rw 1 (q165 c4) ∷
   rw 2 (q166 c4) ∷
   rw 3 (q165 c4) ∷
   rw 4 (q167 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = eqn (CK40 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CK40 ∷ []) (lem-CKu-box-2-at122441 c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (CK40 ∷ Toff134 ∷ []) (Toff134 ∷ CK40 ∷ []) (wp 873 c4)
  q170 : Ws → Eqn
  q170 c4 = eqn (CK40 ∷ CS12 ∷ []) (CS12 ∷ CK40 ∷ []) (wp 874 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (CK40 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK40 ∷ []) (wp 875 c4)

-- F2-K0-CS2: 11 steps
lem-F2-K0-CS2 : Ws → ⟪ (CK40 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-CS2 c4 = derive (CK40 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK40 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 0 (q168 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q170 c4) ∷
   rw 3 (q169 c4) ∷
   rw 4 (q171 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q172 : Ws → Eqn
  q172 c4 = eqn (CK42 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CK42 ∷ []) (lem-CKu-box-2-at0210243143 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (CK42 ∷ Toff314 ∷ []) (Toff314 ∷ CK42 ∷ []) (wl 1068 (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (CK42 ∷ CS03 ∷ []) (CS03 ∷ CK42 ∷ []) (wp 878 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (CK42 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CK42 ∷ []) (wp 879 c4)

-- F2-K2-CS0: 11 steps
lem-F2-K2-CS0 : Ws → ⟪ (CK42 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK42 ∷ []) ⟫ʷ
lem-F2-K2-CS0 c4 = derive (CK42 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 0 (q172 c4) ∷
   rw 1 (q173 c4) ∷
   rw 2 (q174 c4) ∷
   rw 3 (q173 c4) ∷
   rw 4 (q175 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q176 : Ws → Eqn
  q176 c4 = eqn (Bx0-1234 ∷ Bx0-1234 ∷ []) [] (lem-box2 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (Bx0-1234 ∷ CK34 ∷ []) (CCZ124 ∷ CK34 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (lem-CKc-box c4)

-- CKc-boxL: 3 steps
lem-CKc-boxL : Ws → ⟪ (CK34 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ CK34 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CKc-boxL c4 = derive (CK34 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ CK34 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q176 c4) ∷
   rw 1 (q177 c4) ∷
   rw 4 (q176 c4) ∷ []) Eq.refl

private
  q178 : Ws → Eqn
  q178 c4 = eqn (Bx0-1234 ∷ CK34⁻ ∷ []) (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ Bx0-1234 ∷ []) (lem-CKdc-box c4)

-- CKdc-boxL: 3 steps
lem-CKdc-boxL : Ws → ⟪ (CK34⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ []) ⟫ʷ
lem-CKdc-boxL c4 = derive (CK34⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q176 c4) ∷
   rw 1 (q178 c4) ∷
   rw 4 (q176 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ []) (lem-S2-SBOX⟨2·0·41·3⟩ c4)
  q180 : Ws → Eqn
  q180 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn [] [] (wl 1112 (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn [] [] (lem-nf-order-CSat0 c4)

-- F1-order-CS@0: 5 steps
lem-F1-order-CSat0 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CSat0 c4 = derive (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) []
  (rw 0 (q179 c4) ∷
   rw 1 (q179 c4) ∷
   rw 0 (q180 c4) ∷
   rw 0 (q181 c4) ∷
   rw⁻ 0 (q182 c4) ∷ []) Eq.refl

private
  q183 : Ws → Eqn
  q183 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4)
  q184 : Ws → Eqn
  q184 c4 = eqn [] [] (lem-nf-order-CSat1 c4)

-- F1-order-CS@1: 5 steps
lem-F1-order-CSat1 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CSat1 c4 = derive (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) []
  (rw 0 (q183 c4) ∷
   rw 1 (q183 c4) ∷
   rw 0 (q47 c4) ∷
   rw 0 (q181 c4) ∷
   rw⁻ 0 (q184 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q186 : Ws → Eqn
  q186 c4 = eqn [] [] (lem-nf-order-CSat2 c4)

-- F1-order-CS@2: 5 steps
lem-F1-order-CSat2 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CSat2 c4 = derive (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) []
  (rw 0 (q185 c4) ∷
   rw 1 (q185 c4) ∷
   rw 0 (q148 c4) ∷
   rw 0 (q181 c4) ∷
   rw⁻ 0 (q186 c4) ∷ []) Eq.refl
