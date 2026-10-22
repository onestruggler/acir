{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD022 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D022 (Sᴰ : SD022) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS14-TOFF023 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd14-TOFF023 ; lem-comm-CX04-TOFF213 ; lem-comm-CX14-TOFF023 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CX13 ; lem-comm-CCZ024-CX31 ; lem-comm-CK40-TOFF213 ; lem-comm-CK41-TOFF023 ; lem-comm-CS04-TOFF213 ; lem-comm-TOFF213-CK40 ; lem-comm-TOFF213-CSd04 ; lem-comm-TOFF213-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CCZ014-CX32)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CK41 ; lem-comm-TOFF023-CSd14 ; lem-comm-TOFF023-CX14)

-- The lemmas of other derivation modules (DSig).
private
  lem-box-tQ-at0214203143 : Ws → St 148
  lem-box-tQ-at0214203143 = pickᴰ 0 Sᴰ
  lem-t-cP-at0214203143 : Ws → St 1006
  lem-t-cP-at0214203143 = pickᴰ 1 Sᴰ
  lem-box-cP-at0210243143 : Ws → St 842
  lem-box-cP-at0210243143 = pickᴰ 2 Sᴰ
  lem-box-cP-at0214203143 : Ws → St 948
  lem-box-cP-at0214203143 = pickᴰ 3 Sᴰ
  lem-box-cP-at243243 : Ws → St 856
  lem-box-cP-at243243 = pickᴰ 4 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx2-0413 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (X4 ∷ CCZ024 ∷ []) (wp 20 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CZ02 ∷ Toff213 ∷ []) (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl 183 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Toff213 ∷ X4 ∷ []) (X4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl 323 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp 21 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CX31 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ024 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ024 ∷ []) (wp 179 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) (wp 39 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ024 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ024 ∷ []) (wp 23 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) (wl 185 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ []) (wl 186 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp 32 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ []) (wl 191 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl 1182 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) (wp 33 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp 36 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ024 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ024 ∷ []) (wp 746 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp 34 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) (wp 37 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ Toff213 ∷ []) (wl 192 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (Toff214 ∷ CCZ024 ∷ []) (wp 42 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp 41 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) (wl 193 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CX04 ∷ Toff213 ∷ []) (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS14⁻ ∷ []) (wl 194 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) (wl 195 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Toff213 ∷ Toff214 ∷ []) (Toff214 ∷ Toff213 ∷ []) (wl 197 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ014 ∷ []) (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) (wp 44 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) (wl 196 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ []) (wp 650 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl 230 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp 651 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CX13 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ []) (wl 745 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CX13 ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX13 ∷ Toff314 ∷ []) (wp 652 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CX12 ∷ CX13 ∷ Toff213 ∷ []) (Toff213 ∷ CX13 ∷ []) (wl 746 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Toff213 ∷ Toff314 ∷ []) (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl 747 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ024 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp 653 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp 654 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ024 ∷ CX31 ∷ []) (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CX12 ∷ Toff213 ∷ []) (Toff213 ∷ CX12 ∷ []) (wl 748 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (Toff213 ∷ CX04 ∷ []) (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ014 ∷ []) (CX12 ∷ CCZ014 ∷ CX12 ∷ []) (wp 655 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ014 ∷ CX13 ∷ CCZ014 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ []) (wp 656 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Toff314 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ Toff314 ∷ []) (wl 187 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ []) (wp 657 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ []) (wp 658 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ []) (wp 659 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03⁻ ∷ []) (wp 660 c4)

-- F4-CS2-CS2 @02132031: 286 steps
lem-F4-CS2-CS2-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-CS2-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
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
   rw 6 (q1 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw⁻ 12 (q17 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw 8 (q15 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw 8 (q23 c4) ∷
   rw 12 (q24 c4) ∷
   rw 11 (q25 c4) ∷
   rw 10 (q26 c4) ∷
   rw 9 (q25 c4) ∷
   rw 8 (q27 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw⁻ 7 (q28 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 3 1 (CS03 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw 4 (q30 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 6 (q30 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw⁻ 11 (q16 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 4 (q22 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 6 (q23 c4) ∷
   rw 10 (q24 c4) ∷
   rw 9 (q25 c4) ∷
   rw 8 (q26 c4) ∷
   rw 7 (q25 c4) ∷
   rw 6 (q27 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   rw⁻ 6 (q29 c4) ∷
   rw⁻ 2 (q1 c4) ∷
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
   rw 3 (q31 c4) ∷
   rw 10 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 5 (q34 c4) ∷
   re 4 1 (Sb2-0-3-1 ∷ []) ∷
   re 6 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 2 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 3 (q35 c4) ∷
   re 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 4 1 (CS03 ∷ []) ∷
   re 6 1 (CS03⁻ ∷ []) ∷
   rw⁻ 3 (q36 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw 7 (q38 c4) ∷
   rw 4 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 7 (q41 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw 9 (q20 c4) ∷
   rw 10 (q19 c4) ∷
   rw 11 (q42 c4) ∷
   rw 12 (q18 c4) ∷
   rw 13 (q42 c4) ∷
   rw 14 (q17 c4) ∷
   rw 15 (q16 c4) ∷
   rw 9 (q15 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   rw 5 (q23 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   rw 5 (q44 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw 7 (q44 c4) ∷
   rw⁻ 8 (q24 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw 7 (q28 c4) ∷
   rw 9 (q23 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q44 c4) ∷
   rw⁻ 10 (q26 c4) ∷
   rw 11 (q44 c4) ∷
   rw⁻ 12 (q24 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   rw 9 (q38 c4) ∷
   rw⁻ 3 (q45 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw 3 (q46 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q42 c4) ∷
   rw 6 (q18 c4) ∷
   rw 7 (q42 c4) ∷
   rw 8 (q17 c4) ∷
   rw 9 (q16 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 1 (q47 c4) ∷
   rw⁻ 4 (q48 c4) ∷
   re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 4 (q49 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 2 (q48 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   re 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 6 1 (CS03 ∷ []) ∷
   re 8 1 (CS03⁻ ∷ []) ∷
   rw⁻ 5 (q36 c4) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw 9 (q38 c4) ∷
   rw 6 (q39 c4) ∷
   rw 8 (q40 c4) ∷
   rw 9 (q41 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 11 (q20 c4) ∷
   rw 12 (q19 c4) ∷
   rw 13 (q42 c4) ∷
   rw 14 (q18 c4) ∷
   rw 15 (q42 c4) ∷
   rw 16 (q17 c4) ∷
   rw 17 (q16 c4) ∷
   rw 11 (q15 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   rw 7 (q23 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw 7 (q44 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw 9 (q44 c4) ∷
   rw⁻ 10 (q24 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw 9 (q28 c4) ∷
   rw 11 (q23 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 11 (q44 c4) ∷
   rw⁻ 12 (q26 c4) ∷
   rw 13 (q44 c4) ∷
   rw⁻ 14 (q24 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw 11 (q38 c4) ∷
   rw⁻ 5 (q45 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 5 (q46 c4) ∷
   rw 4 (q40 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 5 (q20 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q42 c4) ∷
   rw 8 (q18 c4) ∷
   rw 9 (q42 c4) ∷
   rw 10 (q17 c4) ∷
   rw 11 (q16 c4) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 3 (q47 c4) ∷
   rw⁻ 6 (q50 c4) ∷
   re 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 7 1 (CS03 ∷ []) ∷
   re 9 1 (CS03⁻ ∷ []) ∷
   rw⁻ 6 (q51 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 4 (q50 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ024 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ024 ∷ []) (wp 405 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Toff213 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff213 ∷ []) (wl 556 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp 406 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ []) (wl 557 (lit c4))

-- F4-I-CS2 @02132031: 15 steps
lem-F4-I-CS2-at02132031 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-CS2-at02132031 c4 = derive (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 0 (q52 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw⁻ 2 (q52 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷
   rw 1 (q55 c4) ∷
   rw⁻ 1 (q55 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CCZ024 ∷ []) (wp 442 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff213 ∷ []) (wl 570 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp 443 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (S1 ∷ CS14⁻ ∷ []) (X4 ∷ CS14 ∷ X4 ∷ []) (wl 571 (lit c4))

-- F4-S3-CS2 @02132031: 15 steps
lem-F4-S3-CS2-at02132031 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-CS2-at02132031 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 0 (q56 c4) ∷
   rw⁻ 1 (q57 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q58 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 1 (q59 c4) ∷
   rw 1 (q59 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ024 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CCZ024 ∷ []) (wp 478 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CK40 ∷ Toff213 ∷ []) (Toff213 ∷ CK40 ∷ []) (lem-comm-CK40-TOFF213 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp 479 c4)

-- F4-K2-CS2 @02132031: 17 steps
lem-F4-K2-CS2-at02132031 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS2-at02132031 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 0 (q60 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 2 (q61 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw⁻ 2 (q60 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q61 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q62 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ []) (wp 610 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (K0 ∷ CK40 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) (wp 611 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (K0 ∷ Toff213 ∷ []) (Toff213 ∷ K0 ∷ []) (c₁ (K) (K ↑ • CCZ • K ↑ • iI))
  q66 : Ws → Eqn
  q66 c4 = eqn (Toff213 ∷ CK40 ∷ []) (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (Toff213 ∷ S4 ∷ []) (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S))
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ024 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ []) (wp 612 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (CK40 ∷ X4 ∷ []) (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (wp 613 c4)

-- F4-CS2-K2 @02132031: 19 steps
lem-F4-CS2-K2-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K2-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q63 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 4 (q65 c4) ∷
   rw 5 (q66 c4) ∷
   rw 6 (q67 c4) ∷
   rw 3 (q68 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw 3 (q66 c4) ∷
   rw 4 (q67 c4) ∷
   rw 1 (q68 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q69 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = eqn (S1 ∷ CS14⁻ ∷ X4 ∷ []) (X4 ∷ CS14 ∷ []) (wl 711 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (S1 ∷ CS14⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S1 ∷ CS14⁻ ∷ []) (wp 604 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (S1 ∷ CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ S1 ∷ CS14⁻ ∷ []) (wl 712 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ024 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) (wp 605 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (CS14 ∷ X4 ∷ []) (X4 ∷ S1 ∷ CS14⁻ ∷ []) (wl 713 (lit c4))

-- F4-CS2-S3 @02132031: 15 steps
lem-F4-CS2-S3-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S3-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q70 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q71 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   rw 1 (q73 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (Sb2-0-3-1 ∷ []) ∷
   re 7 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q74 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = eqn (X4 ∷ S4 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ []) (wl 709 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp 599 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (ι ∷ []) (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl)
  q78 : Ws → Eqn
  q78 c4 = eqn (Toff213 ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff213 ∷ []) (wp 600 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (ι1 ∷ []) (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl)
  q80 : Ws → Eqn
  q80 c4 = eqn (CCZ024 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ024 ∷ []) (wp 601 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (S4 ∷ X4 ∷ []) (X4 ∷ ι ∷ S4⁻ ∷ []) (wl 710 (lit c4))

-- F4-CS2-I @02132031: 19 steps
lem-F4-CS2-I-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-I-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 2 (q75 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 2 (q76 c4) ∷
   rw 1 (q1 c4) ∷
   rw 5 (q77 c4) ∷
   rw 4 (q78 c4) ∷
   rw 4 (q79 c4) ∷
   rw 3 (q80 c4) ∷
   rw 3 (q77 c4) ∷
   rw 2 (q78 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (Sb2-0-3-1 ∷ []) ∷
   re 7 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q81 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = eqn (S0 ∷ CS04⁻ ∷ X4 ∷ []) (X4 ∷ CS04 ∷ []) (wp 602 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (S0 ∷ CS04⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S0 ∷ CS04⁻ ∷ []) (wp 421 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (S0 ∷ Toff213 ∷ []) (Toff213 ∷ S0 ∷ []) (c₁ (S) (K ↑ • CCZ • K ↑ • iI))
  q85 : Ws → Eqn
  q85 c4 = eqn (Toff213 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ024 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp 420 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (CS04 ∷ X4 ∷ []) (X4 ∷ S0 ∷ CS04⁻ ∷ []) (wp 603 c4)

-- F4-CS2-S2 @02132031: 17 steps
lem-F4-CS2-S2-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S2-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q82 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q83 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw 5 (q85 c4) ∷
   rw 3 (q86 c4) ∷
   rw⁻ 2 (q84 c4) ∷
   rw 3 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (Sb2-0-3-1 ∷ []) ∷
   re 7 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q87 c4) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = eqn (Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (X4 ∷ CCZ014 ∷ []) (wp 52 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl 206 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (Toff023 ∷ X4 ∷ []) (X4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (wl 314 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp 53 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (CX32 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (CCZ014 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ014 ∷ []) (wp 265 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) (wp 67 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (CCZ014 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ014 ∷ []) (wp 55 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (X4 ∷ CZ01 ∷ CZ01 ∷ []) (X4 ∷ []) (wl 208 (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) (wl 209 (lit c4))
  q100 : Ws → Eqn
  q100 c4 = eqn (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) (wp 60 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (CS13⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS13⁻ ∷ []) (wl 219 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (Toff324 ∷ []) (wl 1413 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ []) (wp 61 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) (wp 64 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (CCZ014 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ014 ∷ []) (wp 722 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) (wp 62 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ []) (wp 65 c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ Toff023 ∷ []) (wp 68 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (Toff024 ∷ CCZ014 ∷ []) (wp 71 c4)
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl 220 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) (wl 221 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (CX14 ∷ Toff023 ∷ []) (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ []) (wp 69 c4)
  q114 : Ws → Eqn
  q114 c4 = eqn (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) (wp 70 c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ []) (wp 72 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (CCZ124 ∷ []) (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) (wp 74 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) (wl 222 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) (wl 999 (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl 181 (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl 1000 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl 263 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (CX23 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ []) (wl 894 (lit c4))
  q123 : Ws → Eqn
  q123 c4 = eqn (CX23 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX23 ∷ Toff324 ∷ []) (wl 1001 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (CX20 ∷ CX23 ∷ Toff023 ∷ []) (Toff023 ∷ CX23 ∷ []) (wl 1002 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = eqn (Toff023 ∷ Toff324 ∷ []) (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp 805 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (CCZ014 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp 381 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4))
  q128 : Ws → Eqn
  q128 c4 = eqn (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp 806 c4)
  q129 : Ws → Eqn
  q129 c4 = eqn (CCZ014 ∷ CX32 ∷ []) (CX32 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX32 (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (CX20 ∷ Toff023 ∷ []) (Toff023 ∷ CX20 ∷ []) (wl 1003 (lit c4))
  q131 : Ws → Eqn
  q131 c4 = eqn (Toff023 ∷ CX14 ∷ []) (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4))
  q132 : Ws → Eqn
  q132 c4 = eqn (CCZ124 ∷ []) (CX20 ∷ CCZ124 ∷ CX20 ∷ []) (wp 380 c4)
  q133 : Ws → Eqn
  q133 c4 = eqn (CCZ124 ∷ CX23 ∷ CCZ124 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ []) (wl 1004 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (Toff324 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ Toff324 ∷ []) (wl 211 (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ []) (wl 896 (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (CS13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13 ∷ []) (wl 1005 (lit c4))
  q137 : Ws → Eqn
  q137 c4 = eqn (CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ []) (wl 900 (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13⁻ ∷ []) (wl 1006 (lit c4))

-- F4-CS2-CS2 @132132: 286 steps
lem-F4-CS2-CS2-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-CS2-at132132 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 4 (q90 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw 6 (q92 c4) ∷
   rw⁻ 10 (q93 c4) ∷
   rw 9 (q94 c4) ∷
   rw⁻ 8 (q95 c4) ∷
   rw 7 (q94 c4) ∷
   rw⁻ 6 (q96 c4) ∷
   rw⁻ 7 (q92 c4) ∷
   rw⁻ 5 (q97 c4) ∷
   rw⁻ 4 (q89 c4) ∷
   rw 5 (q98 c4) ∷
   rw 6 (q99 c4) ∷
   rw⁻ 5 (q91 c4) ∷
   rw⁻ 2 (q88 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 6 (q88 c4) ∷
   rw⁻ 5 (q100 c4) ∷
   rw 6 (q101 c4) ∷
   rw⁻ 7 (q100 c4) ∷
   rw 8 (q101 c4) ∷
   rw⁻ 5 (q88 c4) ∷
   rw 5 (q88 c4) ∷
   rw⁻ 4 (q102 c4) ∷
   rw⁻ 10 (q103 c4) ∷
   rw⁻ 9 (q104 c4) ∷
   rw 8 (q94 c4) ∷
   rw⁻ 7 (q105 c4) ∷
   rw 6 (q94 c4) ∷
   rw⁻ 5 (q106 c4) ∷
   rw⁻ 4 (q107 c4) ∷
   rw 5 (q102 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw⁻ 7 (q102 c4) ∷
   rw⁻ 13 (q103 c4) ∷
   rw⁻ 12 (q104 c4) ∷
   rw 11 (q94 c4) ∷
   rw⁻ 10 (q105 c4) ∷
   rw 9 (q94 c4) ∷
   rw⁻ 8 (q106 c4) ∷
   rw⁻ 7 (q107 c4) ∷
   rw 8 (q102 c4) ∷
   rw⁻ 6 (q109 c4) ∷
   rw⁻ 9 (q108 c4) ∷
   rw 8 (q110 c4) ∷
   rw 12 (q111 c4) ∷
   rw 11 (q112 c4) ∷
   rw 10 (q113 c4) ∷
   rw 9 (q112 c4) ∷
   rw 8 (q114 c4) ∷
   rw⁻ 9 (q110 c4) ∷
   rw⁻ 7 (q115 c4) ∷
   rw⁻ 8 (q116 c4) ∷
   rw⁻ 4 (q88 c4) ∷
   re 3 1 (CS13 ∷ []) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 3 (q93 c4) ∷
   rw 4 (q117 c4) ∷
   rw⁻ 5 (q93 c4) ∷
   rw 6 (q117 c4) ∷
   rw⁻ 3 (q88 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 2 (q102 c4) ∷
   rw⁻ 8 (q103 c4) ∷
   rw⁻ 7 (q104 c4) ∷
   rw 6 (q94 c4) ∷
   rw⁻ 5 (q105 c4) ∷
   rw 4 (q94 c4) ∷
   rw⁻ 3 (q106 c4) ∷
   rw⁻ 2 (q107 c4) ∷
   rw 3 (q102 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw⁻ 5 (q102 c4) ∷
   rw⁻ 11 (q103 c4) ∷
   rw⁻ 10 (q104 c4) ∷
   rw 9 (q94 c4) ∷
   rw⁻ 8 (q105 c4) ∷
   rw 7 (q94 c4) ∷
   rw⁻ 6 (q106 c4) ∷
   rw⁻ 5 (q107 c4) ∷
   rw 6 (q102 c4) ∷
   rw⁻ 4 (q109 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   rw 6 (q110 c4) ∷
   rw 10 (q111 c4) ∷
   rw 9 (q112 c4) ∷
   rw 8 (q113 c4) ∷
   rw 7 (q112 c4) ∷
   rw 6 (q114 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw⁻ 5 (q115 c4) ∷
   rw⁻ 6 (q116 c4) ∷
   rw⁻ 2 (q88 c4) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 0 (q89 c4) ∷
   rw 2 (q90 c4) ∷
   rw⁻ 1 (q91 c4) ∷
   rw 4 (q92 c4) ∷
   rw⁻ 8 (q93 c4) ∷
   rw 7 (q94 c4) ∷
   rw⁻ 6 (q95 c4) ∷
   rw 5 (q94 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw⁻ 5 (q92 c4) ∷
   rw⁻ 3 (q97 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 3 (q98 c4) ∷
   rw 4 (q99 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw⁻ 0 (q88 c4) ∷
   rw 3 (q88 c4) ∷
   rw 2 (q92 c4) ∷
   rw⁻ 6 (q93 c4) ∷
   rw 5 (q94 c4) ∷
   rw⁻ 4 (q95 c4) ∷
   rw 3 (q94 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   rw⁻ 3 (q92 c4) ∷
   rw 3 (q99 c4) ∷
   rw 4 (q92 c4) ∷
   rw⁻ 8 (q93 c4) ∷
   rw 7 (q94 c4) ∷
   rw⁻ 6 (q95 c4) ∷
   rw 5 (q94 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw⁻ 5 (q92 c4) ∷
   rw 5 (q99 c4) ∷
   rw⁻ 2 (q88 c4) ∷
   rw 3 (q118 c4) ∷
   rw 10 (q119 c4) ∷
   rw 3 (q120 c4) ∷
   rw 5 (q121 c4) ∷
   re 4 1 (Sb0-1-3-2 ∷ []) ∷
   re 6 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 2 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 3 (q122 c4) ∷
   re 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 4 1 (CS13 ∷ []) ∷
   re 6 1 (CS13⁻ ∷ []) ∷
   rw⁻ 3 (q123 c4) ∷
   rw 2 (q88 c4) ∷
   rw⁻ 5 (q124 c4) ∷
   rw 7 (q125 c4) ∷
   rw 4 (q126 c4) ∷
   rw 6 (q127 c4) ∷
   rw 7 (q128 c4) ∷
   rw⁻ 10 (q102 c4) ∷
   rw 9 (q107 c4) ∷
   rw 10 (q106 c4) ∷
   rw 11 (q129 c4) ∷
   rw 12 (q105 c4) ∷
   rw 13 (q129 c4) ∷
   rw 14 (q104 c4) ∷
   rw 15 (q103 c4) ∷
   rw 9 (q102 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw 5 (q110 c4) ∷
   rw⁻ 4 (q114 c4) ∷
   rw 5 (q131 c4) ∷
   rw⁻ 6 (q113 c4) ∷
   rw 7 (q131 c4) ∷
   rw⁻ 8 (q111 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   rw⁻ 5 (q124 c4) ∷
   rw 7 (q115 c4) ∷
   rw 9 (q110 c4) ∷
   rw⁻ 8 (q114 c4) ∷
   rw 9 (q131 c4) ∷
   rw⁻ 10 (q113 c4) ∷
   rw 11 (q131 c4) ∷
   rw⁻ 12 (q111 c4) ∷
   rw⁻ 8 (q110 c4) ∷
   rw 9 (q125 c4) ∷
   rw⁻ 3 (q132 c4) ∷
   rw⁻ 5 (q116 c4) ∷
   rw 3 (q133 c4) ∷
   rw 2 (q127 c4) ∷
   rw⁻ 4 (q102 c4) ∷
   rw 3 (q107 c4) ∷
   rw 4 (q106 c4) ∷
   rw 5 (q129 c4) ∷
   rw 6 (q105 c4) ∷
   rw 7 (q129 c4) ∷
   rw 8 (q104 c4) ∷
   rw 9 (q103 c4) ∷
   rw 3 (q102 c4) ∷
   rw⁻ 4 (q88 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 1 (q134 c4) ∷
   rw⁻ 4 (q135 c4) ∷
   re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q136 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 6 (q117 c4) ∷
   rw 5 (q93 c4) ∷
   rw⁻ 4 (q117 c4) ∷
   rw 3 (q93 c4) ∷
   rw⁻ 4 (q88 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 2 (q135 c4) ∷
   rw⁻ 5 (q122 c4) ∷
   re 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 6 1 (CS13 ∷ []) ∷
   re 8 1 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q123 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 7 (q124 c4) ∷
   rw 9 (q125 c4) ∷
   rw 6 (q126 c4) ∷
   rw 8 (q127 c4) ∷
   rw 9 (q128 c4) ∷
   rw⁻ 12 (q102 c4) ∷
   rw 11 (q107 c4) ∷
   rw 12 (q106 c4) ∷
   rw 13 (q129 c4) ∷
   rw 14 (q105 c4) ∷
   rw 15 (q129 c4) ∷
   rw 16 (q104 c4) ∷
   rw 17 (q103 c4) ∷
   rw 11 (q102 c4) ∷
   rw⁻ 5 (q130 c4) ∷
   rw 7 (q110 c4) ∷
   rw⁻ 6 (q114 c4) ∷
   rw 7 (q131 c4) ∷
   rw⁻ 8 (q113 c4) ∷
   rw 9 (q131 c4) ∷
   rw⁻ 10 (q111 c4) ∷
   rw⁻ 6 (q110 c4) ∷
   rw⁻ 7 (q124 c4) ∷
   rw 9 (q115 c4) ∷
   rw 11 (q110 c4) ∷
   rw⁻ 10 (q114 c4) ∷
   rw 11 (q131 c4) ∷
   rw⁻ 12 (q113 c4) ∷
   rw 13 (q131 c4) ∷
   rw⁻ 14 (q111 c4) ∷
   rw⁻ 10 (q110 c4) ∷
   rw 11 (q125 c4) ∷
   rw⁻ 5 (q132 c4) ∷
   rw⁻ 7 (q116 c4) ∷
   rw 5 (q133 c4) ∷
   rw 4 (q127 c4) ∷
   rw⁻ 6 (q102 c4) ∷
   rw 5 (q107 c4) ∷
   rw 6 (q106 c4) ∷
   rw 7 (q129 c4) ∷
   rw 8 (q105 c4) ∷
   rw 9 (q129 c4) ∷
   rw 10 (q104 c4) ∷
   rw 11 (q103 c4) ∷
   rw 5 (q102 c4) ∷
   rw⁻ 6 (q88 c4) ∷
   re 8 1 (Sb0-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 6 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 3 (q134 c4) ∷
   rw⁻ 6 (q137 c4) ∷
   re 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 7 1 (CS13 ∷ []) ∷
   re 9 1 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q138 c4) ∷
   rw 5 (q88 c4) ∷
   rw⁻ 8 (q101 c4) ∷
   rw 7 (q100 c4) ∷
   rw⁻ 6 (q101 c4) ∷
   rw 5 (q100 c4) ∷
   rw⁻ 6 (q88 c4) ∷
   re 8 1 (Sb0-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 6 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 4 (q137 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q139 : Ws → Eqn
  q139 c4 = eqn (CCZ014 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ014 ∷ []) (wp 407 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (Toff023 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff023 ∷ []) (wp 408 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (wl 558 (lit c4))

-- F4-I-CS2 @132132: 15 steps
lem-F4-I-CS2-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-CS2-at132132 c4 = derive (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 0 (q139 c4) ∷
   rw⁻ 1 (q140 c4) ∷
   rw⁻ 2 (q139 c4) ∷
   rw⁻ 3 (q140 c4) ∷
   rw⁻ 0 (q88 c4) ∷
   rw⁻ 1 (q141 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷
   rw 1 (q55 c4) ∷
   rw⁻ 1 (q55 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = eqn (CCZ014 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CCZ014 ∷ []) (wp 458 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff023 ∷ []) (wp 459 c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (wl 585 (lit c4))
  q145 : Ws → Eqn
  q145 c4 = eqn (S2 ∷ CS24⁻ ∷ []) (X4 ∷ CS24 ∷ X4 ∷ []) (wl 583 (lit c4))

-- F4-S3-CS2 @132132: 15 steps
lem-F4-S3-CS2-at132132 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-CS2-at132132 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 0 (q142 c4) ∷
   rw⁻ 1 (q143 c4) ∷
   rw⁻ 2 (q142 c4) ∷
   rw⁻ 3 (q143 c4) ∷
   rw⁻ 0 (q88 c4) ∷
   rw⁻ 1 (q144 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 1 (q145 c4) ∷
   rw 1 (q145 c4) ∷ []) Eq.refl

private
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ []) (wp 518 c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (CK41 ∷ Toff023 ∷ []) (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4))
  q148 : Ws → Eqn
  q148 c4 = eqn (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (wl 643 (lit c4))

-- F4-K2-CS2 @132132: 17 steps
lem-F4-K2-CS2-at132132 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS2-at132132 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 0 (q146 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw 2 (q147 c4) ∷
   rw⁻ 1 (q91 c4) ∷
   rw⁻ 2 (q146 c4) ∷
   rw⁻ 5 (q91 c4) ∷
   rw 4 (q147 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw⁻ 0 (q88 c4) ∷
   rw⁻ 1 (q148 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = eqn (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ []) (wl 720 (lit c4))
  q150 : Ws → Eqn
  q150 c4 = eqn (K1 ∷ CK41 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ []) (wl 734 (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) (wl 735 (lit c4))
  q152 : Ws → Eqn
  q152 c4 = eqn (Toff023 ∷ CK41 ∷ []) (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4))
  q153 : Ws → Eqn
  q153 c4 = eqn (Toff023 ∷ S4 ∷ []) (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S))
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) (wp 634 c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (CK41 ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (wl 723 (lit c4))

-- F4-CS2-K2 @132132: 19 steps
lem-F4-CS2-K2-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K2-at132132 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q149 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q150 c4) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 4 (q151 c4) ∷
   rw 5 (q152 c4) ∷
   rw 6 (q153 c4) ∷
   rw 3 (q154 c4) ∷
   rw⁻ 2 (q151 c4) ∷
   rw 3 (q152 c4) ∷
   rw 4 (q153 c4) ∷
   rw 1 (q154 c4) ∷
   rw⁻ 4 (q88 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q155 c4) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = eqn (S2 ∷ CS24⁻ ∷ X4 ∷ []) (X4 ∷ CS24 ∷ []) (wl 714 (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (S2 ∷ CS24⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S2 ∷ CS24⁻ ∷ []) (wl 732 (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ S2 ∷ CS24⁻ ∷ []) (wp 625 c4)
  q159 : Ws → Eqn
  q159 c4 = eqn (CCZ014 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) (wp 626 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (CS24 ∷ X4 ∷ []) (X4 ∷ S2 ∷ CS24⁻ ∷ []) (wl 716 (lit c4))

-- F4-CS2-S3 @132132: 15 steps
lem-F4-CS2-S3-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S3-at132132 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q156 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q157 c4) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 4 (q158 c4) ∷
   rw 3 (q159 c4) ∷
   rw⁻ 2 (q158 c4) ∷
   rw 1 (q159 c4) ∷
   rw⁻ 3 (q88 c4) ∷
   re 5 1 (Sb0-1-3-2 ∷ []) ∷
   re 7 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 3 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q160 c4) ∷ []) Eq.refl

private
  q161 : Ws → Eqn
  q161 c4 = eqn (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (wp 619 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (Toff023 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff023 ∷ []) (wp 620 c4)
  q163 : Ws → Eqn
  q163 c4 = eqn (CCZ014 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ014 ∷ []) (wp 621 c4)

-- F4-CS2-I @132132: 17 steps
lem-F4-CS2-I-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-I-at132132 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 2 (q75 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 6 (q77 c4) ∷
   rw 2 (q161 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q88 c4) ∷
   rw 4 (q162 c4) ∷
   rw 3 (q163 c4) ∷
   rw 2 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   rw⁻ 3 (q88 c4) ∷
   re 5 1 (Sb0-1-3-2 ∷ []) ∷
   re 7 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 3 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q81 c4) ∷ []) Eq.refl

private
  q164 : Ws → Eqn
  q164 c4 = eqn (S1 ∷ CS14⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S1 ∷ CS14⁻ ∷ []) (wl 573 (lit c4))
  q165 : Ws → Eqn
  q165 c4 = eqn (S1 ∷ Toff023 ∷ []) (Toff023 ∷ S1 ∷ []) (wl 572 (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (Toff023 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 (lit c4))
  q167 : Ws → Eqn
  q167 c4 = eqn (CCZ014 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ CCZ014 ∷ []) (wp 445 c4)

-- F4-CS2-S2 @132132: 17 steps
lem-F4-CS2-S2-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S2-at132132 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q70 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q164 c4) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 4 (q165 c4) ∷
   rw 5 (q166 c4) ∷
   rw 3 (q167 c4) ∷
   rw⁻ 2 (q165 c4) ∷
   rw 3 (q166 c4) ∷
   rw 1 (q167 c4) ∷
   rw⁻ 3 (q88 c4) ∷
   re 5 1 (Sb0-1-3-2 ∷ []) ∷
   re 7 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 3 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q74 c4) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = eqn (CCZ024 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CCZ024 ∷ []) (wp 419 c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (CS04 ∷ Toff213 ∷ []) (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4))
  q170 : Ws → Eqn
  q170 c4 = eqn (S0 ∷ CS04⁻ ∷ []) (X4 ∷ CS04 ∷ X4 ∷ []) (wp 257 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (CS04⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4))

-- F4-S2-CS2 @02132031: 18 steps
lem-F4-S2-CS2-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-CS2-at02132031 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 0 (q168 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 2 (q169 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw⁻ 2 (q170 c4) ∷
   rw⁻ 2 (q86 c4) ∷
   rw 4 (q171 c4) ∷
   rw 3 (q84 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q83 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷
   rw 1 (q170 c4) ∷ []) Eq.refl

private
  q172 : Ws → Eqn
  q172 c4 = eqn (CCZ014 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CCZ014 ∷ []) (wp 444 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (CS14 ∷ Toff023 ∷ []) (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (CS14⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4))

-- F4-S2-CS2 @132132: 18 steps
lem-F4-S2-CS2-at132132 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-CS2-at132132 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 0 (q172 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw 2 (q173 c4) ∷
   rw⁻ 1 (q91 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 2 (q167 c4) ∷
   rw 4 (q174 c4) ∷
   rw 3 (q165 c4) ∷
   rw⁻ 0 (q88 c4) ∷
   rw 1 (q164 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷
   rw 1 (q59 c4) ∷ []) Eq.refl

private
  q175 : Ws → Eqn
  q175 c4 = eqn (Bx2-4013 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (Bx2-4013 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp 19 c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) (lem-t-cP-at0214203143 c4)

-- box2 @0214203143: 11 steps
lem-box2-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0214203143 c4 = derive (Bx2-4013 ∷ Bx2-4013 ∷ []) []
  (rw 0 (q175 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 4 (q177 c4) ∷
   rw 5 (q178 c4) ∷
   rw⁻ 5 (q176 c4) ∷
   rw 5 (q175 c4) ∷
   rw 4 (q177 c4) ∷
   rw 3 (q119 c4) ∷
   rw 2 (q177 c4) ∷
   rw 1 (q119 c4) ∷
   rw 0 (q177 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = eqn (CCZ024 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CCZ024 ∷ []) (wp 1278 c4)
  q180 : Ws → Eqn
  q180 c4 = eqn (Toff213 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff213 ∷ []) (wl 1430 (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (wp 1279 c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ []) (ι ∷ S0⁻ ∷ []) (wl 1431 (lit c4))

-- F4-I-CS2 @0213243140: 15 steps
lem-F4-I-CS2-at0213243140 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-CS2-at0213243140 c4 = derive (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  (re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
   rw 3 (q176 c4) ∷
   rw⁻ 0 (q179 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw⁻ 2 (q179 c4) ∷
   rw⁻ 3 (q180 c4) ∷
   rw⁻ 0 (q176 c4) ∷
   rw⁻ 1 (q181 c4) ∷
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷
   rw 1 (q182 c4) ∷
   rw⁻ 1 (q182 c4) ∷ []) Eq.refl

private
  q183 : Ws → Eqn
  q183 c4 = eqn (CCZ024 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CCZ024 ∷ []) (wp 1280 c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (X0 ∷ Toff213 ∷ []) (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI))
  q185 : Ws → Eqn
  q185 c4 = eqn (S4 ∷ CS04⁻ ∷ []) (X0 ∷ CS04 ∷ X0 ∷ []) (wp 1281 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (CCZ024 ∷ S4 ∷ CS04⁻ ∷ []) (S4 ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp 1282 c4)
  q187 : Ws → Eqn
  q187 c4 = eqn (S4 ∷ CS04⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ S4 ∷ CS04⁻ ∷ []) (wp 1283 c4)

-- F4-S2-CS2 @0213243140: 18 steps
lem-F4-S2-CS2-at0213243140 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S2-CS2-at0213243140 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
   rw 3 (q176 c4) ∷
   rw⁻ 0 (q183 c4) ∷
   rw 3 (q184 c4) ∷
   rw 2 (q169 c4) ∷
   rw 1 (q184 c4) ∷
   rw⁻ 2 (q185 c4) ∷
   rw⁻ 2 (q186 c4) ∷
   rw 4 (q171 c4) ∷
   rw⁻ 3 (q67 c4) ∷
   rw⁻ 0 (q176 c4) ∷
   rw 1 (q187 c4) ∷
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷
   rw 1 (q185 c4) ∷ []) Eq.refl
