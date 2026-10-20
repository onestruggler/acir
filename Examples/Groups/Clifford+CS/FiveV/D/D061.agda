{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D061 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-box-tQ-at043043)
open import Examples.Groups.Clifford+CS.FiveV.D.D007 using (lem-box-tQ-at04233042)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-box-cP-at04203243)
open import Examples.Groups.Clifford+CS.FiveV.D.D016 using (lem-box-cP-at0310243142 ; lem-box-cP-at0314213240 ; lem-box-perm-1324-at0310213442)
open import Examples.Groups.Clifford+CS.FiveV.D.D017 using (lem-CSdu-box-3-at0310213442 ; lem-CSu-box-3-at0310213442 ; lem-box-cP-at02142140 ; lem-box-cP-at04122041 ; lem-box-cP-at0412213043 ; lem-box-cP-at0412233041 ; lem-box-cP-at04233042 ; lem-box-perm-3124-at0210213443 ; lem-box2-at0310213442)
open import Examples.Groups.Clifford+CS.FiveV.D.D023 using (lem-F0-R-at0410213243 ; lem-Ku-box-at0214203143 ; lem-box-perm-1324-at04122041 ; lem-box-perm-2314-at0214203143 ; lem-box-perm-3241-at04203243)
open import Examples.Groups.Clifford+CS.FiveV.D.D033 using (lem-CKdu-box-2-at0214203143 ; lem-F0-B-at0410213243 ; lem-box-perm-1243-at043043 ; lem-box-perm-1243-at0440 ; lem-box-perm-1342-at0440 ; lem-box-perm-1423-at04122041 ; lem-box-perm-1423-at04203243 ; lem-box-perm-1423-at04233042 ; lem-box-perm-4213-at04122041)
open import Examples.Groups.Clifford+CS.FiveV.D.D034 using (lem-S2-SBOX⟨0·2·43·1⟩-at0440)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CS03-CCZ124 ; lem-comm-CS13-CCZ024 ; lem-comm-CS23-CCZ014 ; lem-comm-CSd03-CCZ124 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CCZ024-CS13 ; lem-comm-CCZ024-CSd13 ; lem-comm-CS02-CCZ134 ; lem-comm-CSd02-CCZ134 ; lem-comm-CX40-TOFF312)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CK02-CCZ134 ; lem-comm-CX23-TOFF401 ; lem-comm-TOFF401-CX23)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CCZ124-CK03 ; lem-comm-CK03-CCZ124 ; lem-comm-CX41-TOFF203 ; lem-comm-CX41-TOFF302)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx4-2031 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (X0 ∷ CCZ024 ∷ []) (wp 1284 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CZ24 ∷ Toff413 ∷ []) (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) (wl 1498 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (X0 ∷ Toff413 ∷ []) (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑))
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
  q10 c4 = eqn (CCZ024 ∷ CZ24 ∷ []) (CZ24 ∷ CCZ024 ∷ []) (wp 1285 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X0 ∷ CZ24 ∷ CZ24 ∷ []) (X0 ∷ []) (wl 1433 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ123 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ123 ∷ []) (wl 1499 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CS13⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS13⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS13⁻ ∷ []) (wl 1500 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx4-2031 ∷ []) (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx4-2301 ∷ []) (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (Toff302 ∷ CCZ234 ∷ []) (wp 896 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ024 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp 1341 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (Toff302 ∷ []) (wl 1501 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (K3⁻ ∷ Toff401 ∷ []) (Toff401 ∷ K3⁻ ∷ []) (wp 1342 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS02 ∷ Toff401 ∷ []) (Toff401 ∷ CS02 ∷ []) (wp 1343 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CX23 ∷ Toff401 ∷ []) (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS03⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS03⁻ ∷ []) (wp 1344 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CS03 ∷ Toff401 ∷ []) (Toff401 ∷ CS03 ∷ []) (wp 1328 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (K3 ∷ Toff401 ∷ []) (Toff401 ∷ K3 ∷ []) (wp 1345 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ012 ∷ []) (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl 929 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ234 ∷ CS12 ∷ []) (CS12 ∷ CCZ234 ∷ []) (wl 415 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CX10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ234 ∷ []) (wp 765 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ234 ∷ CS02 ∷ []) (CS02 ∷ CCZ234 ∷ []) (wp 279 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) (wp 90 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Toff302 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff302 ∷ []) (wp 1346 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ012 ∷ []) (wp 359 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CS13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CS13 ∷ Toff413 ∷ []) (Toff413 ∷ CS13 ∷ []) (wl 1502 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx4-1023 ∷ []) (Bx4-2031 ∷ []) (lem-box-perm-3241-at04203243 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx4-2031 ∷ []) (Bx4-1023 ∷ []) (lem-box-perm-4213-at04122041 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx4-1023 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl 207 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp 53 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ014 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ []) (wp 54 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CS23⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ123 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ []) (wl 463 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ123 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ []) (Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ []) (wl 1503 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl 181 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ012 ∷ CS13 ∷ Toff302 ∷ []) (CS13 ∷ Toff302 ∷ CCZ012 ∷ []) (wl 1504 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl 341 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CX31 ∷ Toff103 ∷ X0 ∷ []) (X0 ∷ Toff103 ∷ []) (wl 1505 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CX31 ∷ Toff103 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX31 ∷ Toff103 ∷ []) (wl 1506 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CX31 ∷ Toff423 ∷ []) (Toff423 ∷ CX31 ∷ []) (wl 1507 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (Toff103 ∷ []) (wl 1508 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (K1 ∷ Toff423 ∷ []) (Toff423 ∷ K1 ∷ []) (c₂ (K ↑) (Toffᵗ))
  q54 : Ws → Eqn
  q54 c4 = eqn (CS03 ∷ Toff423 ∷ []) (Toff423 ∷ CS03 ∷ []) (wp 1347 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CX10 ∷ Toff423 ∷ []) (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ))
  q56 : Ws → Eqn
  q56 c4 = eqn (CS03⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS03⁻ ∷ []) (wp 1348 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CS13 ∷ Toff423 ∷ []) (Toff423 ∷ CS13 ∷ []) (wl 1509 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (K1⁻ ∷ Toff423 ∷ []) (Toff423 ∷ K1⁻ ∷ []) (c₂ ((K • iI) ↑) (Toffᵗ))
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ014 ∷ CX31 ∷ Toff103 ∷ []) (CX31 ∷ Toff103 ∷ CCZ014 ∷ []) (wp 1349 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Toff103 ∷ X0 ∷ []) (X0 ∷ CX31 ∷ Toff103 ∷ []) (wl 1510 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ []) (wl 1511 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (CS12 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS12 ∷ []) (wl 1512 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) (wl 461 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) (wp 67 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CS12⁻ ∷ X0 ∷ []) (X0 ∷ CS12⁻ ∷ []) (wl 1513 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CS12⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS12⁻ ∷ []) (wl 1514 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) (wl 460 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ014 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ014 ∷ []) (wp 265 c4)

-- F4-CS1-CS2 @0440: 248 steps
lem-F4-CS1-CS2-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-CS2-at0440 c4 = derive (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  (re 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q4 c4) ∷
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
   rw 5 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw 5 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw 7 (q13 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 5 (q15 c4) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 11 (q20 c4) ∷
   rw 10 (q21 c4) ∷
   rw 9 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw 7 (q22 c4) ∷
   rw 6 (q24 c4) ∷
   rw 5 (q25 c4) ∷
   rw 6 (q19 c4) ∷
   rw 8 (q26 c4) ∷
   rw⁻ 12 (q27 c4) ∷
   rw 11 (q28 c4) ∷
   rw⁻ 10 (q29 c4) ∷
   rw 9 (q28 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 9 (q26 c4) ∷
   rw 7 (q31 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw 7 (q32 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 13 (q20 c4) ∷
   rw 12 (q21 c4) ∷
   rw 11 (q22 c4) ∷
   rw 10 (q23 c4) ∷
   rw 9 (q22 c4) ∷
   rw 8 (q24 c4) ∷
   rw 7 (q25 c4) ∷
   rw 8 (q19 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   re 3 1 (CS13 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw 3 (q34 c4) ∷
   rw 4 (q35 c4) ∷
   rw 5 (q34 c4) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q15 c4) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 9 (q20 c4) ∷
   rw 8 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw 6 (q23 c4) ∷
   rw 5 (q22 c4) ∷
   rw 4 (q24 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q19 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 9 (q28 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw 7 (q28 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw 5 (q31 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 5 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 11 (q20 c4) ∷
   rw 10 (q21 c4) ∷
   rw 9 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw 7 (q22 c4) ∷
   rw 6 (q24 c4) ∷
   rw 5 (q25 c4) ∷
   rw 6 (q19 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw 1 (q36 c4) ∷
   rw 2 (q37 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
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
   rw 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 3 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw⁻ 6 (q40 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   rw 4 (q42 c4) ∷
   rw⁻ 3 (q41 c4) ∷
   rw 2 (q43 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   rw 3 (q44 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 8 (q40 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw 5 (q44 c4) ∷
   rw⁻ 2 (q38 c4) ∷
   rw 3 (q45 c4) ∷
   rw 10 (q46 c4) ∷
   rw 4 (q47 c4) ∷
   rw 6 (q48 c4) ∷
   re 4 1 (Sb4-1-3-2 ∷ []) ∷
   re 6 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 2 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 3 (q49 c4) ∷
   re 2 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 4 1 (CS13 ∷ []) ∷
   re 6 1 (CS13⁻ ∷ []) ∷
   rw⁻ 3 (q50 c4) ∷
   rw 2 (q38 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   rw⁻ 7 (q52 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw⁻ 7 (q54 c4) ∷
   rw⁻ 8 (q55 c4) ∷
   rw⁻ 9 (q56 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   rw⁻ 11 (q57 c4) ∷
   rw⁻ 12 (q58 c4) ∷
   rw 6 (q52 c4) ∷
   rw 4 (q59 c4) ∷
   rw⁻ 3 (q51 c4) ∷
   rw⁻ 5 (q52 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw⁻ 5 (q54 c4) ∷
   rw⁻ 6 (q55 c4) ∷
   rw⁻ 7 (q56 c4) ∷
   rw⁻ 8 (q55 c4) ∷
   rw⁻ 9 (q57 c4) ∷
   rw⁻ 10 (q58 c4) ∷
   rw 4 (q52 c4) ∷
   rw 2 (q59 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   re 6 1 (Sb4-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 4 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 1 (q60 c4) ∷
   rw⁻ 4 (q61 c4) ∷
   re 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q62 c4) ∷
   rw 3 (q38 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   rw 5 (q64 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   rw 3 (q64 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   re 6 1 (Sb4-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 4 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 2 (q61 c4) ∷
   rw⁻ 5 (q49 c4) ∷
   re 4 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 6 1 (CS13 ∷ []) ∷
   re 8 1 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q50 c4) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw⁻ 9 (q52 c4) ∷
   rw⁻ 8 (q53 c4) ∷
   rw⁻ 9 (q54 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   rw⁻ 11 (q56 c4) ∷
   rw⁻ 12 (q55 c4) ∷
   rw⁻ 13 (q57 c4) ∷
   rw⁻ 14 (q58 c4) ∷
   rw 8 (q52 c4) ∷
   rw 6 (q59 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   rw⁻ 7 (q52 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw⁻ 7 (q54 c4) ∷
   rw⁻ 8 (q55 c4) ∷
   rw⁻ 9 (q56 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   rw⁻ 11 (q57 c4) ∷
   rw⁻ 12 (q58 c4) ∷
   rw 6 (q52 c4) ∷
   rw 4 (q59 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   re 8 1 (Sb4-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 6 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 3 (q60 c4) ∷
   rw⁻ 6 (q65 c4) ∷
   re 5 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 7 1 (CS13 ∷ []) ∷
   re 9 1 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q66 c4) ∷
   rw 5 (q38 c4) ∷
   rw⁻ 8 (q67 c4) ∷
   rw 7 (q68 c4) ∷
   rw⁻ 6 (q67 c4) ∷
   rw 5 (q68 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   re 8 1 (Sb4-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 6 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 4 (q65 c4) ∷
   re 2 1 (Sb4-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 0 5 (Sb4-2-03-1 ∷ []) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (Bx4-1023 ∷ []) (Bx4-1302 ∷ []) (lem-box-perm-1423-at04203243 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (Bx4-1302 ∷ []) (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) (lem-box-cP-at04233042 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (X0 ∷ CCZ134 ∷ []) (CCZ134 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q72 : Ws → Eqn
  q72 c4 = eqn (CK02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CK02 ∷ []) (lem-comm-CK02-CCZ134 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (Toff402 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Toff402 ∷ []) (wp 1359 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (wl 1530 (lit c4))

-- F4-K2-CS1 @0440: 19 steps
lem-F4-K2-CS1-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-CS1-at0440 c4 = derive (X0 ∷ CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  (re 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q69 c4) ∷
   rw 3 (q70 c4) ∷
   rw 2 (q71 c4) ∷
   rw 1 (q72 c4) ∷
   rw 0 (q71 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   rw 4 (q71 c4) ∷
   rw 3 (q72 c4) ∷
   rw 2 (q71 c4) ∷
   rw⁻ 3 (q73 c4) ∷
   rw⁻ 0 (q70 c4) ∷
   rw⁻ 0 (q69 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   re 2 1 (Sb4-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 0 5 (Sb4-1-02-3 ∷ []) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (X0 ∷ CCZ014 ∷ []) (wp 1351 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (CZ14 ∷ Toff423 ∷ []) (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) (wl 1516 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (X0 ∷ Toff423 ∷ []) (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑))
  q78 : Ws → Eqn
  q78 c4 = eqn (CCZ014 ∷ CZ14 ∷ []) (CZ14 ∷ CCZ014 ∷ []) (wp 1352 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (X0 ∷ CZ14 ∷ CZ14 ∷ []) (X0 ∷ []) (wp 1353 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (CCZ014 ∷ Toff103 ∷ CCZ034 ∷ []) (Toff103 ∷ CCZ014 ∷ []) (wp 1364 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ034 ∷ CCZ023 ∷ []) (wp 1365 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl 307 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ014 ∷ CS02 ∷ []) (CS02 ∷ CCZ014 ∷ []) (wp 155 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (CX23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4))
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ014 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ014 ∷ []) (wp 156 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ014 ∷ CS03 ∷ []) (CS03 ∷ CCZ014 ∷ []) (wp 157 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ014 ∷ []) (wp 124 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (Toff103 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff103 ∷ []) (wp 1366 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ []) (wp 1367 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (CCZ123 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ []) (Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ []) (wl 1539 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (CCZ023 ∷ CS12 ∷ Toff103 ∷ []) (CS12 ∷ Toff103 ∷ CCZ023 ∷ []) (wl 1540 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ023 ∷ CCZ023 ∷ []) [] (wl 204 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (CX23 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ []) (wl 1520 (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (CX23 ∷ Toff302 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX23 ∷ Toff302 ∷ []) (wl 1541 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (Toff401 ∷ CX23 ∷ []) (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (CCZ234 ∷ CX23 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp 1368 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (CZ24 ∷ CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CZ24 ∷ []) (wp 1369 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ024 ∷ []) (wp 1370 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (CZ24 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (CZ24 ∷ CCZ024 ∷ []) (wp 1371 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (CCZ234 ∷ CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ []) (CX23 ∷ Toff302 ∷ CCZ234 ∷ []) (wp 1372 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (Toff302 ∷ X0 ∷ []) (X0 ∷ CX23 ∷ Toff302 ∷ []) (wl 1525 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (CS13 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ []) (wl 1526 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (CS13 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13 ∷ []) (wl 1542 (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (CCZ024 ∷ CS13 ∷ []) (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (CS13⁻ ∷ X0 ∷ []) (X0 ∷ CS13⁻ ∷ []) (wl 1528 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (CS13⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13⁻ ∷ []) (wl 1543 (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ024 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4))

-- F4-CS2-CS1 @0440: 254 steps
lem-F4-CS2-CS1-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-CS1-at0440 c4 = derive (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  (re 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q38 c4) ∷
   rw⁻ 2 (q75 c4) ∷
   rw 4 (q76 c4) ∷
   rw 3 (q77 c4) ∷
   rw 6 (q39 c4) ∷
   rw⁻ 10 (q40 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw 6 (q43 c4) ∷
   rw⁻ 7 (q39 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw⁻ 4 (q75 c4) ∷
   rw 5 (q79 c4) ∷
   rw 6 (q44 c4) ∷
   rw 5 (q77 c4) ∷
   rw⁻ 2 (q38 c4) ∷
   re 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 6 (q38 c4) ∷
   rw⁻ 5 (q68 c4) ∷
   rw 6 (q67 c4) ∷
   rw⁻ 7 (q68 c4) ∷
   rw 8 (q67 c4) ∷
   rw⁻ 5 (q38 c4) ∷
   rw 5 (q38 c4) ∷
   rw⁻ 4 (q80 c4) ∷
   rw 6 (q81 c4) ∷
   rw⁻ 5 (q52 c4) ∷
   rw 11 (q58 c4) ∷
   rw 10 (q57 c4) ∷
   rw 9 (q55 c4) ∷
   rw 8 (q56 c4) ∷
   rw 7 (q55 c4) ∷
   rw 6 (q54 c4) ∷
   rw 5 (q53 c4) ∷
   rw 6 (q52 c4) ∷
   rw 8 (q82 c4) ∷
   rw⁻ 12 (q83 c4) ∷
   rw 11 (q84 c4) ∷
   rw⁻ 10 (q85 c4) ∷
   rw 9 (q84 c4) ∷
   rw⁻ 8 (q86 c4) ∷
   rw⁻ 9 (q82 c4) ∷
   rw⁻ 7 (q87 c4) ∷
   rw⁻ 6 (q80 c4) ∷
   rw 7 (q88 c4) ∷
   rw 8 (q89 c4) ∷
   rw⁻ 7 (q52 c4) ∷
   rw 13 (q58 c4) ∷
   rw 12 (q57 c4) ∷
   rw 11 (q55 c4) ∷
   rw 10 (q56 c4) ∷
   rw 9 (q55 c4) ∷
   rw 8 (q54 c4) ∷
   rw 7 (q53 c4) ∷
   rw 8 (q52 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw 4 (q38 c4) ∷
   rw⁻ 3 (q64 c4) ∷
   rw 4 (q63 c4) ∷
   rw⁻ 5 (q64 c4) ∷
   rw 6 (q63 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 3 (q38 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw 4 (q81 c4) ∷
   rw⁻ 3 (q52 c4) ∷
   rw 9 (q58 c4) ∷
   rw 8 (q57 c4) ∷
   rw 7 (q55 c4) ∷
   rw 6 (q56 c4) ∷
   rw 5 (q55 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q53 c4) ∷
   rw 4 (q52 c4) ∷
   rw 6 (q82 c4) ∷
   rw⁻ 10 (q83 c4) ∷
   rw 9 (q84 c4) ∷
   rw⁻ 8 (q85 c4) ∷
   rw 7 (q84 c4) ∷
   rw⁻ 6 (q86 c4) ∷
   rw⁻ 7 (q82 c4) ∷
   rw⁻ 5 (q87 c4) ∷
   rw⁻ 4 (q80 c4) ∷
   rw 5 (q88 c4) ∷
   rw 6 (q89 c4) ∷
   rw⁻ 5 (q52 c4) ∷
   rw 11 (q58 c4) ∷
   rw 10 (q57 c4) ∷
   rw 9 (q55 c4) ∷
   rw 8 (q56 c4) ∷
   rw 7 (q55 c4) ∷
   rw 6 (q54 c4) ∷
   rw 5 (q53 c4) ∷
   rw 6 (q52 c4) ∷
   rw⁻ 2 (q38 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q36 c4) ∷
   rw 1 (q38 c4) ∷
   rw⁻ 0 (q75 c4) ∷
   rw 2 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 8 (q40 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw⁻ 3 (q78 c4) ∷
   rw⁻ 2 (q75 c4) ∷
   rw 3 (q79 c4) ∷
   rw 4 (q44 c4) ∷
   rw 3 (q77 c4) ∷
   rw⁻ 0 (q38 c4) ∷
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
   rw 3 (q90 c4) ∷
   rw 10 (q46 c4) ∷
   rw 4 (q91 c4) ∷
   rw 6 (q92 c4) ∷
   re 4 1 (Sb4-2-1-3 ∷ []) ∷
   re 6 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 2 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 3 (q93 c4) ∷
   re 2 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 4 1 (CS12 ∷ []) ∷
   re 6 1 (CS12⁻ ∷ []) ∷
   rw⁻ 3 (q94 c4) ∷
   rw 2 (q15 c4) ∷
   rw 2 (q16 c4) ∷
   rw 5 (q95 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw 8 (q95 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw 10 (q95 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw 6 (q19 c4) ∷
   rw 4 (q96 c4) ∷
   rw 3 (q95 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   rw 6 (q95 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 8 (q95 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw⁻ 10 (q20 c4) ∷
   rw 4 (q19 c4) ∷
   rw⁻ 5 (q97 c4) ∷
   rw⁻ 7 (q98 c4) ∷
   rw 5 (q99 c4) ∷
   rw 2 (q100 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   re 6 1 (Sb4-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 4 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 1 (q101 c4) ∷
   rw⁻ 4 (q102 c4) ∷
   re 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q103 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 3 (q104 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (Sb4-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 4 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 2 (q102 c4) ∷
   rw⁻ 5 (q93 c4) ∷
   re 4 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 6 1 (CS12 ∷ []) ∷
   re 8 1 (CS12⁻ ∷ []) ∷
   rw⁻ 5 (q94 c4) ∷
   rw 4 (q15 c4) ∷
   rw 4 (q16 c4) ∷
   rw 7 (q95 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw⁻ 9 (q24 c4) ∷
   rw 10 (q95 c4) ∷
   rw⁻ 11 (q23 c4) ∷
   rw 12 (q95 c4) ∷
   rw⁻ 13 (q21 c4) ∷
   rw⁻ 14 (q20 c4) ∷
   rw 8 (q19 c4) ∷
   rw 6 (q96 c4) ∷
   rw 5 (q95 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw 8 (q95 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw 10 (q95 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw 6 (q19 c4) ∷
   rw⁻ 7 (q97 c4) ∷
   rw⁻ 9 (q98 c4) ∷
   rw 7 (q99 c4) ∷
   rw 4 (q100 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   re 8 1 (Sb4-2-1-3 ∷ []) ∷
   re 10 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 6 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 3 (q101 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   re 5 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 7 1 (CS12 ∷ []) ∷
   re 9 1 (CS12⁻ ∷ []) ∷
   rw⁻ 6 (q106 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 7 (q107 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 5 (q107 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 8 1 (Sb4-2-1-3 ∷ []) ∷
   re 10 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 6 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 4 (q105 c4) ∷
   re 2 1 (Sb4-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 0 5 (Sb4-1-02-3 ∷ []) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (Bx4-2031 ∷ []) (Bx4-2103 ∷ []) (lem-box-perm-1423-at04122041 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (Bx4-2103 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at0412213043 c4)
  q110 : Ws → Eqn
  q110 c4 = eqn (X0 ∷ CCZ124 ∷ []) (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))
  q111 : Ws → Eqn
  q111 c4 = eqn (CK03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CK03 ∷ []) (lem-comm-CK03-CCZ124 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (Toff403 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff403 ∷ []) (wp 1384 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (wl 1572 (lit c4))

-- F4-K3-CS2 @0440: 19 steps
lem-F4-K3-CS2-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-CS2-at0440 c4 = derive (X0 ∷ CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  (re 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q108 c4) ∷
   rw 3 (q109 c4) ∷
   rw 2 (q110 c4) ∷
   rw 1 (q111 c4) ∷
   rw 0 (q110 c4) ∷
   rw⁻ 1 (q112 c4) ∷
   rw 4 (q110 c4) ∷
   rw 3 (q111 c4) ∷
   rw 2 (q110 c4) ∷
   rw⁻ 3 (q112 c4) ∷
   rw⁻ 0 (q109 c4) ∷
   rw⁻ 0 (q108 c4) ∷
   rw⁻ 1 (q113 c4) ∷
   re 2 1 (Sb4-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 0 5 (Sb4-2-03-1 ∷ []) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = eqn (K3 ∷ CK03 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ []) (wl 1574 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (K3 ∷ CK03 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ []) (wl 1575 (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ []) (Toff403 ∷ K3 ∷ CK03 ∷ S0 ∷ []) (wp 1393 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (CCZ124 ∷ K3 ∷ []) (K3 ∷ CCZ124 ∷ []) (wl 1576 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (CCZ124 ∷ CK03 ∷ []) (CK03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CK03 (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (S0 ∷ CCZ124 ∷ []) (CCZ124 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))
  q120 : Ws → Eqn
  q120 c4 = eqn (CK03 ∷ X0 ∷ []) (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ []) (wl 1577 (lit c4))

-- F4-CS2-K3 @0440: 21 steps
lem-F4-CS2-K3-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-K3-at0440 c4 = derive (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  (rw⁻ 2 (q114 c4) ∷
   re 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q115 c4) ∷
   rw 1 (q108 c4) ∷
   rw 1 (q109 c4) ∷
   rw⁻ 4 (q116 c4) ∷
   rw 3 (q117 c4) ∷
   rw 4 (q118 c4) ∷
   rw⁻ 5 (q119 c4) ∷
   rw⁻ 2 (q116 c4) ∷
   rw 1 (q117 c4) ∷
   rw 2 (q118 c4) ∷
   rw⁻ 3 (q119 c4) ∷
   rw⁻ 4 (q109 c4) ∷
   rw⁻ 4 (q108 c4) ∷
   re 6 1 (Sb4-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 4 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 0 (q120 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (Bx4-1230 ∷ []) (Bx4-1302 ∷ []) (lem-box-perm-1342-at0440 c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (Bx4-1302 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at04233042 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (Bx2-4130 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at02142140 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ024 ∷ []) (wp 827 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (CCZ024 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp 1197 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (CCZ034 ∷ []) (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) (wp 198 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (CCZ124 ∷ CS04 ∷ []) (CS04 ∷ CCZ124 ∷ []) (wp 384 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (CCZ124 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ []) (wl 651 (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (CS03⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (CS03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4))
  q131 : Ws → Eqn
  q131 c4 = eqn (CCZ024 ∷ CCZ034 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ024 ∷ []) (wp 1411 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (Toff413 ∷ CCZ124 ∷ []) (wl 1598 (lit c4))
  q133 : Ws → Eqn
  q133 c4 = eqn (CCZ123 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl 1150 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ []) (Toff413 ∷ []) (wl 1605 (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (Toff203 ∷ K4⁻ ∷ []) (K4⁻ ∷ Toff203 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K • iI))
  q136 : Ws → Eqn
  q136 c4 = eqn (CS34 ∷ Toff203 ∷ []) (Toff203 ∷ CS34 ∷ []) (wp 1199 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (CX41 ∷ Toff203 ∷ []) (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (CS13⁻ ∷ Toff203 ∷ []) (Toff203 ∷ CS13⁻ ∷ []) (wl 1606 (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (CS13 ∷ Toff203 ∷ []) (Toff203 ∷ CS13 ∷ []) (wl 1607 (lit c4))
  q140 : Ws → Eqn
  q140 c4 = eqn (Toff203 ∷ K4 ∷ []) (K4 ∷ Toff203 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K))
  q141 : Ws → Eqn
  q141 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl 289 (lit c4))
  q142 : Ws → Eqn
  q142 c4 = eqn (CCZ124 ∷ CS01 ∷ []) (CS01 ∷ CCZ124 ∷ []) (wp 919 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (CCZ124 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ []) (wl 280 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ123 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ123 ∷ []) (wl 770 (lit c4))
  q145 : Ws → Eqn
  q145 c4 = eqn (Toff413 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff413 ∷ []) (wl 1608 (lit c4))
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ013 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ013 ∷ []) (wl 1131 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) (wp 39 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp 32 c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp 21 c4)
  q150 : Ws → Eqn
  q150 c4 = eqn (CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ013 ∷ []) (wp 1412 c4)
  q151 : Ws → Eqn
  q151 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl 230 (lit c4))
  q152 : Ws → Eqn
  q152 c4 = eqn (Bx4-1302 ∷ []) (Bx4-1230 ∷ []) (lem-box-perm-1423-at04233042 c4)

-- box-box-2 @0440: 105 steps
lem-box-box-2-at0440 : Ws → ⟪ (Bx4-1230 ∷ Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ Bx4-1230 ∷ []) ⟫ʷ
lem-box-box-2-at0440 c4 = derive (Bx4-1230 ∷ Bx2-4130 ∷ []) (Bx2-4130 ∷ Bx4-1230 ∷ [])
  (rw 0 (q121 c4) ∷
   rw 0 (q122 c4) ∷
   rw 4 (q123 c4) ∷
   rw 3 (q124 c4) ∷
   rw 4 (q125 c4) ∷
   rw 6 (q126 c4) ∷
   rw⁻ 10 (q127 c4) ∷
   rw⁻ 9 (q128 c4) ∷
   rw 8 (q129 c4) ∷
   rw⁻ 7 (q128 c4) ∷
   rw 6 (q130 c4) ∷
   rw⁻ 7 (q126 c4) ∷
   rw 5 (q124 c4) ∷
   rw 6 (q131 c4) ∷
   rw⁻ 3 (q123 c4) ∷
   rw 3 (q123 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 4 (q133 c4) ∷
   rw⁻ 3 (q134 c4) ∷
   rw⁻ 9 (q135 c4) ∷
   rw 8 (q136 c4) ∷
   rw 7 (q137 c4) ∷
   rw 6 (q138 c4) ∷
   rw 5 (q137 c4) ∷
   rw 4 (q139 c4) ∷
   rw⁻ 3 (q140 c4) ∷
   rw 4 (q134 c4) ∷
   rw 6 (q141 c4) ∷
   rw⁻ 10 (q142 c4) ∷
   rw⁻ 9 (q143 c4) ∷
   rw 8 (q129 c4) ∷
   rw⁻ 7 (q143 c4) ∷
   rw 6 (q130 c4) ∷
   rw⁻ 7 (q141 c4) ∷
   rw 5 (q144 c4) ∷
   rw⁻ 4 (q132 c4) ∷
   rw 5 (q145 c4) ∷
   rw 6 (q146 c4) ∷
   rw⁻ 5 (q134 c4) ∷
   rw⁻ 11 (q135 c4) ∷
   rw 10 (q136 c4) ∷
   rw 9 (q137 c4) ∷
   rw 8 (q138 c4) ∷
   rw 7 (q137 c4) ∷
   rw 6 (q139 c4) ∷
   rw⁻ 5 (q140 c4) ∷
   rw 6 (q134 c4) ∷
   rw⁻ 2 (q123 c4) ∷
   rw 2 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   rw 2 (q125 c4) ∷
   rw 4 (q126 c4) ∷
   rw⁻ 8 (q127 c4) ∷
   rw⁻ 7 (q128 c4) ∷
   rw 6 (q129 c4) ∷
   rw⁻ 5 (q128 c4) ∷
   rw 4 (q130 c4) ∷
   rw⁻ 5 (q126 c4) ∷
   rw 3 (q124 c4) ∷
   rw 4 (q131 c4) ∷
   rw⁻ 1 (q123 c4) ∷
   rw 1 (q123 c4) ∷
   rw⁻ 0 (q132 c4) ∷
   rw 2 (q133 c4) ∷
   rw⁻ 1 (q134 c4) ∷
   rw⁻ 7 (q135 c4) ∷
   rw 6 (q136 c4) ∷
   rw 5 (q137 c4) ∷
   rw 4 (q138 c4) ∷
   rw 3 (q137 c4) ∷
   rw 2 (q139 c4) ∷
   rw⁻ 1 (q140 c4) ∷
   rw 2 (q134 c4) ∷
   rw 4 (q141 c4) ∷
   rw⁻ 8 (q142 c4) ∷
   rw⁻ 7 (q143 c4) ∷
   rw 6 (q129 c4) ∷
   rw⁻ 5 (q143 c4) ∷
   rw 4 (q130 c4) ∷
   rw⁻ 5 (q141 c4) ∷
   rw 3 (q144 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 3 (q145 c4) ∷
   rw 4 (q146 c4) ∷
   rw⁻ 3 (q134 c4) ∷
   rw⁻ 9 (q135 c4) ∷
   rw 8 (q136 c4) ∷
   rw 7 (q137 c4) ∷
   rw 6 (q138 c4) ∷
   rw 5 (q137 c4) ∷
   rw 4 (q139 c4) ∷
   rw⁻ 3 (q140 c4) ∷
   rw 4 (q134 c4) ∷
   rw⁻ 0 (q123 c4) ∷
   rw 2 (q141 c4) ∷
   rw⁻ 6 (q147 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q148 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q149 c4) ∷
   rw⁻ 3 (q141 c4) ∷
   rw 3 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw⁻ 1 (q122 c4) ∷
   rw 1 (q152 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = eqn (K2 ∷ CK02⁻ ∷ []) (X0 ∷ CK02 ∷ X0 ∷ []) (wl 1633 (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (CK02⁻ ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CK02⁻ ∷ []) (lem-CKdu-box-2-at0214203143 c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (K2 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ K2 ∷ []) (lem-Ku-box-at0214203143 c4)

-- XCKX-box-2 @0214203143: 4 steps
lem-XCKX-box-2-at0214203143 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-XCKX-box-2-at0214203143 c4 = derive (X0 ∷ CK02 ∷ X0 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  (rw⁻ 0 (q153 c4) ∷
   rw 1 (q154 c4) ∷
   rw 0 (q155 c4) ∷
   rw 1 (q153 c4) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = eqn (Bx2-4013 ∷ []) (Bx2-0143 ∷ []) (lem-box-perm-2314-at0214203143 c4)
  q157 : Ws → Eqn
  q157 c4 = eqn (CX23 ∷ CX23 ∷ []) [] (wl 806 (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (CX23 ∷ Bx2-0143 ∷ CX23 ∷ []) (Bx2-0143 ∷ Bx3-0142 ∷ []) (lem-F0-B-at0410213243 c4)
  q159 : Ws → Eqn
  q159 c4 = eqn (CX23 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Bx3-0142 ∷ CX23 ∷ []) (lem-F0-R-at0410213243 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (CS34⁻ ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CS34⁻ ∷ []) (lem-CSdu-box-3-at0310213442 c4)
  q161 : Ws → Eqn
  q161 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4)
  q163 : Ws → Eqn
  q163 c4 = eqn (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) (Toff301 ∷ CCZ034 ∷ []) (wp 388 c4)
  q164 : Ws → Eqn
  q164 c4 = eqn (CCZ014 ∷ []) (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp 1143 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) (wl 499 (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (CX40 ∷ Toff312 ∷ []) (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4))
  q167 : Ws → Eqn
  q167 c4 = eqn (CS01⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS01⁻ ∷ []) (wl 500 (lit c4))
  q168 : Ws → Eqn
  q168 c4 = eqn (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) (wl 501 (lit c4))
  q169 : Ws → Eqn
  q169 c4 = eqn (Toff301 ∷ Toff312 ∷ []) (Toff312 ∷ Toff301 ∷ []) (wl 525 (lit c4))
  q170 : Ws → Eqn
  q170 c4 = eqn (CCZ034 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp 1435 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (CS34 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CS34 ∷ []) (lem-CSu-box-3-at0310213442 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (Bx3-0142 ∷ Bx3-0142 ∷ []) [] (lem-box2-at0310213442 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (Bx2-0143 ∷ []) (Bx2-4013 ∷ []) (lem-box-perm-3124-at0210213443 c4)

-- CXuA-S @0410213243: 44 steps
lem-CXuA-S-at0410213243 : Ws → ⟪ (CX23 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ CX23 ∷ []) ⟫ʷ
lem-CXuA-S-at0410213243 c4 = derive (CX23 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ CX23 ∷ [])
  (re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 3 1 (CS34 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   rw 1 (q156 c4) ∷
   rw⁻ 2 (q157 c4) ∷
   rw 0 (q158 c4) ∷
   rw 2 (q159 c4) ∷
   rw 5 (q160 c4) ∷
   rw 5 (q161 c4) ∷
   rw 5 (q162 c4) ∷
   rw⁻ 4 (q163 c4) ∷
   rw 6 (q164 c4) ∷
   rw 10 (q165 c4) ∷
   rw 9 (q166 c4) ∷
   rw 8 (q167 c4) ∷
   rw 7 (q166 c4) ∷
   rw 6 (q168 c4) ∷
   rw⁻ 7 (q164 c4) ∷
   rw 5 (q169 c4) ∷
   rw⁻ 6 (q170 c4) ∷
   rw 7 (q169 c4) ∷
   rw⁻ 4 (q162 c4) ∷
   rw⁻ 4 (q161 c4) ∷
   rw 3 (q171 c4) ∷
   rw 3 (q161 c4) ∷
   rw 3 (q162 c4) ∷
   rw⁻ 2 (q163 c4) ∷
   rw 4 (q164 c4) ∷
   rw 8 (q165 c4) ∷
   rw 7 (q166 c4) ∷
   rw 6 (q167 c4) ∷
   rw 5 (q166 c4) ∷
   rw 4 (q168 c4) ∷
   rw⁻ 5 (q164 c4) ∷
   rw 3 (q169 c4) ∷
   rw⁻ 4 (q170 c4) ∷
   rw 5 (q169 c4) ∷
   rw⁻ 2 (q162 c4) ∷
   rw⁻ 2 (q161 c4) ∷
   rw 1 (q172 c4) ∷
   rw 0 (q173 c4) ∷
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷ []) Eq.refl

private
  q174 : Ws → Eqn
  q174 c4 = eqn (Bx4-1230 ∷ []) (Bx4-1203 ∷ []) (lem-box-perm-1243-at0440 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (Bx4-1203 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (Bx3-4120 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ034 ∷ []) (wp 103 c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (CCZ034 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp 1438 c4)
  q179 : Ws → Eqn
  q179 c4 = eqn (CCZ024 ∷ []) (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp 213 c4)
  q180 : Ws → Eqn
  q180 c4 = eqn (CCZ134 ∷ CS04 ∷ []) (CS04 ∷ CCZ134 ∷ []) (wp 1003 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (CCZ134 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ []) (wl 318 (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn (CS02⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (CS02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4))
  q184 : Ws → Eqn
  q184 c4 = eqn (CCZ024 ∷ CCZ034 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ034 ∷ []) (wp 1134 c4)
  q185 : Ws → Eqn
  q185 c4 = eqn (CCZ134 ∷ Toff412 ∷ CCZ123 ∷ []) (Toff412 ∷ CCZ134 ∷ []) (wl 1673 (lit c4))
  q186 : Ws → Eqn
  q186 c4 = eqn (CCZ123 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl 1241 (lit c4))
  q187 : Ws → Eqn
  q187 c4 = eqn (K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ []) (Toff412 ∷ []) (wl 1674 (lit c4))
  q188 : Ws → Eqn
  q188 c4 = eqn (Toff302 ∷ K4⁻ ∷ []) (K4⁻ ∷ Toff302 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K • iI))
  q189 : Ws → Eqn
  q189 c4 = eqn (CS24 ∷ Toff302 ∷ []) (Toff302 ∷ CS24 ∷ []) (wp 1006 c4)
  q190 : Ws → Eqn
  q190 c4 = eqn (CX41 ∷ Toff302 ∷ []) (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4))
  q191 : Ws → Eqn
  q191 c4 = eqn (CS12⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS12⁻ ∷ []) (wl 1675 (lit c4))
  q192 : Ws → Eqn
  q192 c4 = eqn (CS12 ∷ Toff302 ∷ []) (Toff302 ∷ CS12 ∷ []) (wl 1190 (lit c4))
  q193 : Ws → Eqn
  q193 c4 = eqn (Toff302 ∷ K4 ∷ []) (K4 ∷ Toff302 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K))
  q194 : Ws → Eqn
  q194 c4 = eqn (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl 155 (lit c4))
  q195 : Ws → Eqn
  q195 c4 = eqn (CCZ134 ∷ CS01 ∷ []) (CS01 ∷ CCZ134 ∷ []) (wp 261 c4)
  q196 : Ws → Eqn
  q196 c4 = eqn (CCZ134 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ []) (wl 679 (lit c4))
  q197 : Ws → Eqn
  q197 c4 = eqn (CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ123 ∷ []) (wl 618 (lit c4))
  q198 : Ws → Eqn
  q198 c4 = eqn (Toff412 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff412 ∷ []) (wl 1676 (lit c4))
  q199 : Ws → Eqn
  q199 c4 = eqn (CCZ012 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ012 ∷ []) (wl 1251 (lit c4))
  q200 : Ws → Eqn
  q200 c4 = eqn (CCZ034 ∷ CS01 ∷ []) (CS01 ∷ CCZ034 ∷ []) (wp 1 c4)
  q201 : Ws → Eqn
  q201 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
  q202 : Ws → Eqn
  q202 c4 = eqn (CCZ034 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ034 ∷ []) (wp 2 c4)
  q203 : Ws → Eqn
  q203 c4 = eqn (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) (wp 3 c4)
  q204 : Ws → Eqn
  q204 c4 = eqn (CCZ012 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ012 ∷ []) (wp 374 c4)
  q205 : Ws → Eqn
  q205 c4 = eqn (Bx4-1203 ∷ []) (Bx4-1230 ∷ []) (lem-box-perm-1243-at043043 c4)

-- box-box-3 @0440: 105 steps
lem-box-box-3-at0440 : Ws → ⟪ (Bx4-1230 ∷ Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ Bx4-1230 ∷ []) ⟫ʷ
lem-box-box-3-at0440 c4 = derive (Bx4-1230 ∷ Bx3-4120 ∷ []) (Bx3-4120 ∷ Bx4-1230 ∷ [])
  (rw 0 (q174 c4) ∷
   rw 0 (q175 c4) ∷
   rw 4 (q176 c4) ∷
   rw 3 (q177 c4) ∷
   rw 4 (q178 c4) ∷
   rw 6 (q177 c4) ∷
   rw 5 (q179 c4) ∷
   rw⁻ 9 (q180 c4) ∷
   rw⁻ 8 (q181 c4) ∷
   rw 7 (q182 c4) ∷
   rw⁻ 6 (q181 c4) ∷
   rw 5 (q183 c4) ∷
   rw⁻ 6 (q179 c4) ∷
   rw 6 (q184 c4) ∷
   rw⁻ 3 (q176 c4) ∷
   rw 3 (q176 c4) ∷
   rw⁻ 2 (q185 c4) ∷
   rw 4 (q186 c4) ∷
   rw⁻ 3 (q187 c4) ∷
   rw⁻ 9 (q188 c4) ∷
   rw 8 (q189 c4) ∷
   rw 7 (q190 c4) ∷
   rw 6 (q191 c4) ∷
   rw 5 (q190 c4) ∷
   rw 4 (q192 c4) ∷
   rw⁻ 3 (q193 c4) ∷
   rw 4 (q187 c4) ∷
   rw 6 (q194 c4) ∷
   rw⁻ 10 (q195 c4) ∷
   rw⁻ 9 (q196 c4) ∷
   rw 8 (q182 c4) ∷
   rw⁻ 7 (q196 c4) ∷
   rw 6 (q183 c4) ∷
   rw⁻ 7 (q194 c4) ∷
   rw 5 (q197 c4) ∷
   rw⁻ 4 (q185 c4) ∷
   rw 5 (q198 c4) ∷
   rw 6 (q199 c4) ∷
   rw⁻ 5 (q187 c4) ∷
   rw⁻ 11 (q188 c4) ∷
   rw 10 (q189 c4) ∷
   rw 9 (q190 c4) ∷
   rw 8 (q191 c4) ∷
   rw 7 (q190 c4) ∷
   rw 6 (q192 c4) ∷
   rw⁻ 5 (q193 c4) ∷
   rw 6 (q187 c4) ∷
   rw⁻ 2 (q176 c4) ∷
   rw 2 (q176 c4) ∷
   rw 1 (q177 c4) ∷
   rw 2 (q178 c4) ∷
   rw 4 (q177 c4) ∷
   rw 3 (q179 c4) ∷
   rw⁻ 7 (q180 c4) ∷
   rw⁻ 6 (q181 c4) ∷
   rw 5 (q182 c4) ∷
   rw⁻ 4 (q181 c4) ∷
   rw 3 (q183 c4) ∷
   rw⁻ 4 (q179 c4) ∷
   rw 4 (q184 c4) ∷
   rw⁻ 1 (q176 c4) ∷
   rw 1 (q176 c4) ∷
   rw⁻ 0 (q185 c4) ∷
   rw 2 (q186 c4) ∷
   rw⁻ 1 (q187 c4) ∷
   rw⁻ 7 (q188 c4) ∷
   rw 6 (q189 c4) ∷
   rw 5 (q190 c4) ∷
   rw 4 (q191 c4) ∷
   rw 3 (q190 c4) ∷
   rw 2 (q192 c4) ∷
   rw⁻ 1 (q193 c4) ∷
   rw 2 (q187 c4) ∷
   rw 4 (q194 c4) ∷
   rw⁻ 8 (q195 c4) ∷
   rw⁻ 7 (q196 c4) ∷
   rw 6 (q182 c4) ∷
   rw⁻ 5 (q196 c4) ∷
   rw 4 (q183 c4) ∷
   rw⁻ 5 (q194 c4) ∷
   rw 3 (q197 c4) ∷
   rw⁻ 2 (q185 c4) ∷
   rw 3 (q198 c4) ∷
   rw 4 (q199 c4) ∷
   rw⁻ 3 (q187 c4) ∷
   rw⁻ 9 (q188 c4) ∷
   rw 8 (q189 c4) ∷
   rw 7 (q190 c4) ∷
   rw 6 (q191 c4) ∷
   rw 5 (q190 c4) ∷
   rw 4 (q192 c4) ∷
   rw⁻ 3 (q193 c4) ∷
   rw 4 (q187 c4) ∷
   rw⁻ 0 (q176 c4) ∷
   rw 2 (q194 c4) ∷
   rw⁻ 6 (q200 c4) ∷
   rw 5 (q201 c4) ∷
   rw⁻ 4 (q202 c4) ∷
   rw 3 (q201 c4) ∷
   rw⁻ 2 (q203 c4) ∷
   rw⁻ 3 (q194 c4) ∷
   rw 3 (q204 c4) ∷
   rw 4 (q48 c4) ∷
   rw⁻ 1 (q175 c4) ∷
   rw 1 (q205 c4) ∷ []) Eq.refl

private
  q206 : Ws → Eqn
  q206 c4 = eqn (Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ []) (CCZ023 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩-at0440 c4)
  q207 : Ws → Eqn
  q207 c4 = eqn (CK03 ∷ CCZ023 ∷ CK03 ∷ S0 ∷ []) (Toff302 ∷ []) (wl 1706 (lit c4))

-- L-CX01-2 @0440: 2 steps
lem-L-CX01-2-at0440 : Ws → ⟪ (CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
lem-L-CX01-2-at0440 c4 = derive (CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ []) (Toff302 ∷ [])
  (rw 1 (q206 c4) ∷
   rw 0 (q207 c4) ∷ []) Eq.refl

private
  q208 : Ws → Eqn
  q208 c4 = eqn (CK02 ∷ CCZ023 ∷ CK02 ∷ S0 ∷ []) (Toff203 ∷ []) (wl 1707 (lit c4))

-- L-CX10-2 @0440: 2 steps
lem-L-CX10-2-at0440 : Ws → ⟪ (CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
lem-L-CX10-2-at0440 c4 = derive (CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ []) (Toff203 ∷ [])
  (rw 1 (q206 c4) ∷
   rw 0 (q208 c4) ∷ []) Eq.refl
