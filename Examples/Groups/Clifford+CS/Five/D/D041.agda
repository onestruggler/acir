{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD041 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D041 (Sᴰ : SD041) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ014-CX23)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CCZ014-CS23 ; lem-comm-CCZ014-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CX14)

-- The lemmas of other derivation modules (DSig).
private
  lem-box-cP-at243243 : Ws → St 856
  lem-box-cP-at243243 = pickᴰ 0 Sᴰ
  lem-box2-at243243 : Ws → St 1083
  lem-box2-at243243 = pickᴰ 1 Sᴰ
  lem-box-perm-1423-at243243 : Ws → St 1289
  lem-box-perm-1423-at243243 = pickᴰ 2 Sᴰ
  lem-S2-SBOX⟨0·1·42·3⟩ : Ws → St 1313
  lem-S2-SBOX⟨0·1·42·3⟩ = pickᴰ 3 Sᴰ
  lem-S2-SBOX⟨0·2·43·1⟩ : Ws → St 1314
  lem-S2-SBOX⟨0·2·43·1⟩ = pickᴰ 4 Sᴰ
  lem-CKc-box-at233442 : Ws → St 1325
  lem-CKc-box-at233442 = pickᴰ 5 Sᴰ
  lem-box-perm-1342-at233442 : Ws → St 1328
  lem-box-perm-1342-at233442 = pickᴰ 6 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Toff023 ∷ Toff324 ∷ []) (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp 805 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp 806 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) (wl 217 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ []) (wp 65 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) (wp 64 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) (wp 63 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) (wp 62 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ []) (wp 61 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ []) (wp 72 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl 220 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) (wp 70 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Toff023 ∷ CX14 ∷ []) (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ []) (wp 69 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) (wl 221 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ124 ∷ []) (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) (wp 74 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) (wp 66 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) (wl 222 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp 53 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS13⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS13⁻ ∷ []) (wl 219 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) (wp 60 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Bx0-1342 ∷ CK42 ∷ []) (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) (lem-CKc-box-at233442 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1423 ∷ []) (lem-box-perm-1342-at233442 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ234 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ234 ∷ []) (wp 278 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl 274 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (S4 ∷ Toff023 ∷ []) (Toff023 ∷ S4 ∷ []) (wp 632 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ014 ∷ S4 ∷ []) (S4 ∷ CCZ014 ∷ []) (wp 633 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) (wl 209 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl 207 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ014 ∷ CS23 ∷ []) (CS23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CS23 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ014 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ []) (wp 54 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ014 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CSd23 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx0-1423 ∷ Bx0-1423 ∷ []) [] (lem-box2-at243243 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl 1000 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl 263 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ []) (CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ []) (wl 1292 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl 181 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ123 ∷ []) (wl 508 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ []) (S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ []) (wl 1293 (lit c4))

-- nf-rel-268@1: 473 steps
lem-nf-rel-268at1 : Ws → ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ []) ⟫ʷ
lem-nf-rel-268at1 c4 = derive (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ [])
  (rw 2 (q1 c4) ∷
   rw 5 (q2 c4) ∷
   rw 8 (q1 c4) ∷
   re 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 2 1 (CS13 ∷ []) ∷
   re 4 1 (CS13⁻ ∷ []) ∷
   re 10 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 12 1 (CS13 ∷ []) ∷
   re 14 1 (CS13⁻ ∷ []) ∷
   rw 10 (q3 c4) ∷
   rw 13 (q4 c4) ∷
   rw 12 (q5 c4) ∷
   rw⁻ 15 (q6 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q12 c4) ∷
   rw 14 (q6 c4) ∷
   rw 11 (q13 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 13 (q16 c4) ∷
   rw⁻ 14 (q17 c4) ∷
   rw 15 (q16 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw 13 (q4 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw 10 (q20 c4) ∷
   rw⁻ 12 (q6 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q9 c4) ∷
   rw 16 (q11 c4) ∷
   rw 17 (q12 c4) ∷
   rw 11 (q6 c4) ∷
   rw⁻ 12 (q3 c4) ∷
   rw 12 (q3 c4) ∷
   rw⁻ 15 (q21 c4) ∷
   rw 14 (q22 c4) ∷
   rw⁻ 13 (q21 c4) ∷
   rw 12 (q22 c4) ∷
   rw⁻ 13 (q3 c4) ∷
   rw 13 (q3 c4) ∷
   rw 16 (q4 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 18 (q6 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q8 c4) ∷
   rw 19 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw 21 (q9 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q12 c4) ∷
   rw 17 (q6 c4) ∷
   rw 14 (q13 c4) ∷
   rw 16 (q14 c4) ∷
   rw⁻ 15 (q15 c4) ∷
   rw 16 (q16 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 19 (q18 c4) ∷
   rw⁻ 15 (q14 c4) ∷
   rw 16 (q4 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw 13 (q20 c4) ∷
   rw⁻ 15 (q6 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q12 c4) ∷
   rw 14 (q6 c4) ∷
   rw⁻ 15 (q3 c4) ∷
   rw 15 (q3 c4) ∷
   rw⁻ 18 (q23 c4) ∷
   rw 17 (q24 c4) ∷
   rw⁻ 16 (q23 c4) ∷
   rw 15 (q24 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   rw 16 (q25 c4) ∷
   rw 16 (q26 c4) ∷
   rw 19 (q27 c4) ∷
   rw 19 (q3 c4) ∷
   rw⁻ 22 (q28 c4) ∷
   rw 22 (q29 c4) ∷
   rw 21 (q8 c4) ∷
   rw 22 (q9 c4) ∷
   rw 23 (q10 c4) ∷
   rw 24 (q9 c4) ∷
   rw 25 (q11 c4) ∷
   rw⁻ 21 (q29 c4) ∷
   rw⁻ 20 (q28 c4) ∷
   rw 20 (q29 c4) ∷
   rw 19 (q8 c4) ∷
   rw 20 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q9 c4) ∷
   rw 23 (q11 c4) ∷
   rw⁻ 19 (q29 c4) ∷
   rw⁻ 20 (q3 c4) ∷
   rw 20 (q25 c4) ∷
   rw 20 (q26 c4) ∷
   rw 23 (q27 c4) ∷
   rw 23 (q3 c4) ∷
   rw⁻ 26 (q30 c4) ∷
   rw 25 (q31 c4) ∷
   rw⁻ 24 (q30 c4) ∷
   rw 23 (q31 c4) ∷
   rw⁻ 24 (q3 c4) ∷
   rw 0 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q11 c4) ∷
   rw 10 (q12 c4) ∷
   rw 4 (q6 c4) ∷
   rw 1 (q13 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 6 (q18 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw 0 (q20 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q9 c4) ∷
   rw 6 (q11 c4) ∷
   rw 7 (q12 c4) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw 4 (q22 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 3 (q3 c4) ∷
   rw 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q12 c4) ∷
   rw 7 (q6 c4) ∷
   rw 4 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 8 (q16 c4) ∷
   rw⁻ 9 (q18 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q11 c4) ∷
   rw 10 (q12 c4) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   rw 7 (q24 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   rw 5 (q24 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   rw 6 (q25 c4) ∷
   rw 6 (q26 c4) ∷
   rw 9 (q27 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 12 (q28 c4) ∷
   rw 12 (q29 c4) ∷
   rw 11 (q8 c4) ∷
   rw 12 (q9 c4) ∷
   rw 13 (q10 c4) ∷
   rw 14 (q9 c4) ∷
   rw 15 (q11 c4) ∷
   rw⁻ 11 (q29 c4) ∷
   rw⁻ 10 (q28 c4) ∷
   rw 10 (q29 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw 12 (q9 c4) ∷
   rw 13 (q11 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw 10 (q25 c4) ∷
   rw 10 (q26 c4) ∷
   rw 13 (q27 c4) ∷
   rw 13 (q3 c4) ∷
   rw⁻ 16 (q30 c4) ∷
   rw 15 (q31 c4) ∷
   rw⁻ 14 (q30 c4) ∷
   rw 13 (q31 c4) ∷
   rw⁻ 14 (q3 c4) ∷
   rw 14 (q3 c4) ∷
   rw 18 (q14 c4) ∷
   rw⁻ 17 (q15 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 19 (q17 c4) ∷
   rw 20 (q16 c4) ∷
   rw⁻ 21 (q18 c4) ∷
   rw⁻ 17 (q14 c4) ∷
   rw 16 (q20 c4) ∷
   rw 16 (q14 c4) ∷
   rw⁻ 15 (q15 c4) ∷
   rw 16 (q16 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 19 (q18 c4) ∷
   rw⁻ 15 (q14 c4) ∷
   rw 14 (q20 c4) ∷
   rw⁻ 15 (q3 c4) ∷
   rw 15 (q3 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 20 (q17 c4) ∷
   rw 21 (q16 c4) ∷
   rw⁻ 22 (q18 c4) ∷
   rw⁻ 18 (q14 c4) ∷
   rw 17 (q20 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw 17 (q16 c4) ∷
   rw⁻ 18 (q17 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 20 (q18 c4) ∷
   rw⁻ 16 (q14 c4) ∷
   rw 15 (q20 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   rw 16 (q3 c4) ∷
   rw 19 (q4 c4) ∷
   rw 18 (q5 c4) ∷
   rw⁻ 21 (q6 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q8 c4) ∷
   rw 22 (q9 c4) ∷
   rw 23 (q10 c4) ∷
   rw 24 (q9 c4) ∷
   rw 25 (q11 c4) ∷
   rw 26 (q12 c4) ∷
   rw 20 (q6 c4) ∷
   rw 17 (q13 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 20 (q17 c4) ∷
   rw 21 (q16 c4) ∷
   rw⁻ 22 (q18 c4) ∷
   rw⁻ 18 (q14 c4) ∷
   rw 19 (q4 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw 16 (q20 c4) ∷
   rw⁻ 18 (q6 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q8 c4) ∷
   rw 19 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw 21 (q9 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q12 c4) ∷
   rw 17 (q6 c4) ∷
   rw⁻ 18 (q3 c4) ∷
   rw 18 (q3 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw 20 (q22 c4) ∷
   rw⁻ 19 (q21 c4) ∷
   rw 18 (q22 c4) ∷
   rw⁻ 19 (q3 c4) ∷
   rw 19 (q3 c4) ∷
   rw 23 (q14 c4) ∷
   rw⁻ 22 (q15 c4) ∷
   rw 23 (q16 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw 25 (q16 c4) ∷
   rw⁻ 26 (q18 c4) ∷
   rw⁻ 22 (q14 c4) ∷
   rw 21 (q20 c4) ∷
   rw 21 (q14 c4) ∷
   rw⁻ 20 (q15 c4) ∷
   rw 21 (q16 c4) ∷
   rw⁻ 22 (q17 c4) ∷
   rw 23 (q16 c4) ∷
   rw⁻ 24 (q18 c4) ∷
   rw⁻ 20 (q14 c4) ∷
   rw 19 (q20 c4) ∷
   rw⁻ 20 (q3 c4) ∷
   rw 20 (q3 c4) ∷
   rw 23 (q4 c4) ∷
   rw 22 (q5 c4) ∷
   rw⁻ 25 (q6 c4) ∷
   rw 24 (q7 c4) ∷
   rw 25 (q8 c4) ∷
   rw 26 (q9 c4) ∷
   rw 27 (q10 c4) ∷
   rw 28 (q9 c4) ∷
   rw 29 (q11 c4) ∷
   rw 30 (q12 c4) ∷
   rw 24 (q6 c4) ∷
   rw 21 (q13 c4) ∷
   rw 23 (q14 c4) ∷
   rw⁻ 22 (q15 c4) ∷
   rw 23 (q16 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw 25 (q16 c4) ∷
   rw⁻ 26 (q18 c4) ∷
   rw⁻ 22 (q14 c4) ∷
   rw 23 (q4 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw 20 (q20 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw 21 (q7 c4) ∷
   rw 22 (q8 c4) ∷
   rw 23 (q9 c4) ∷
   rw 24 (q10 c4) ∷
   rw 25 (q9 c4) ∷
   rw 26 (q11 c4) ∷
   rw 27 (q12 c4) ∷
   rw 21 (q6 c4) ∷
   rw⁻ 22 (q3 c4) ∷
   rw 22 (q3 c4) ∷
   rw⁻ 25 (q23 c4) ∷
   rw 24 (q24 c4) ∷
   rw⁻ 23 (q23 c4) ∷
   rw 22 (q24 c4) ∷
   rw⁻ 23 (q3 c4) ∷
   rw 23 (q3 c4) ∷
   rw⁻ 26 (q32 c4) ∷
   rw 26 (q33 c4) ∷
   rw 25 (q34 c4) ∷
   rw 26 (q35 c4) ∷
   rw 27 (q36 c4) ∷
   rw 28 (q35 c4) ∷
   rw 29 (q22 c4) ∷
   rw⁻ 25 (q33 c4) ∷
   rw⁻ 24 (q32 c4) ∷
   rw 24 (q33 c4) ∷
   rw 23 (q34 c4) ∷
   rw 24 (q35 c4) ∷
   rw 25 (q36 c4) ∷
   rw 26 (q35 c4) ∷
   rw 27 (q22 c4) ∷
   rw⁻ 23 (q33 c4) ∷
   rw⁻ 24 (q3 c4) ∷
   rw 24 (q25 c4) ∷
   rw 24 (q26 c4) ∷
   rw 27 (q27 c4) ∷
   rw 27 (q3 c4) ∷
   rw⁻ 30 (q32 c4) ∷
   rw 30 (q33 c4) ∷
   rw 29 (q34 c4) ∷
   rw 30 (q35 c4) ∷
   rw 31 (q36 c4) ∷
   rw 32 (q35 c4) ∷
   rw 33 (q22 c4) ∷
   rw⁻ 29 (q33 c4) ∷
   rw⁻ 28 (q32 c4) ∷
   rw 28 (q33 c4) ∷
   rw 27 (q34 c4) ∷
   rw 28 (q35 c4) ∷
   rw 29 (q36 c4) ∷
   rw 30 (q35 c4) ∷
   rw 31 (q22 c4) ∷
   rw⁻ 27 (q33 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw 28 (q3 c4) ∷
   rw⁻ 31 (q28 c4) ∷
   rw 31 (q29 c4) ∷
   rw 30 (q8 c4) ∷
   rw 31 (q9 c4) ∷
   rw 32 (q10 c4) ∷
   rw 33 (q9 c4) ∷
   rw 34 (q11 c4) ∷
   rw⁻ 30 (q29 c4) ∷
   rw⁻ 29 (q28 c4) ∷
   rw 29 (q29 c4) ∷
   rw 28 (q8 c4) ∷
   rw 29 (q9 c4) ∷
   rw 30 (q10 c4) ∷
   rw 31 (q9 c4) ∷
   rw 32 (q11 c4) ∷
   rw⁻ 28 (q29 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw 29 (q3 c4) ∷
   rw⁻ 32 (q32 c4) ∷
   rw 32 (q33 c4) ∷
   rw 31 (q34 c4) ∷
   rw 32 (q35 c4) ∷
   rw 33 (q36 c4) ∷
   rw 34 (q35 c4) ∷
   rw 35 (q22 c4) ∷
   rw⁻ 31 (q33 c4) ∷
   rw⁻ 30 (q32 c4) ∷
   rw 30 (q33 c4) ∷
   rw 29 (q34 c4) ∷
   rw 30 (q35 c4) ∷
   rw 31 (q36 c4) ∷
   rw 32 (q35 c4) ∷
   rw 33 (q22 c4) ∷
   rw⁻ 29 (q33 c4) ∷
   rw⁻ 30 (q3 c4) ∷
   rw 30 (q25 c4) ∷
   rw 30 (q26 c4) ∷
   rw 33 (q27 c4) ∷
   rw 33 (q3 c4) ∷
   rw⁻ 36 (q32 c4) ∷
   rw 36 (q33 c4) ∷
   rw 35 (q34 c4) ∷
   rw 36 (q35 c4) ∷
   rw 37 (q36 c4) ∷
   rw 38 (q35 c4) ∷
   rw 39 (q22 c4) ∷
   rw⁻ 35 (q33 c4) ∷
   rw⁻ 34 (q32 c4) ∷
   rw 34 (q33 c4) ∷
   rw 33 (q34 c4) ∷
   rw 34 (q35 c4) ∷
   rw 35 (q36 c4) ∷
   rw 36 (q35 c4) ∷
   rw 37 (q22 c4) ∷
   rw⁻ 33 (q33 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw 34 (q3 c4) ∷
   rw⁻ 37 (q30 c4) ∷
   rw 36 (q31 c4) ∷
   rw⁻ 35 (q30 c4) ∷
   rw 34 (q31 c4) ∷
   rw⁻ 35 (q3 c4) ∷
   rw 35 (q37 c4) ∷
   rw 0 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 4 (q40 c4) ∷
   rw 29 (q41 c4) ∷
   rw 5 (q42 c4) ∷
   rw 6 (q41 c4) ∷
   rw 7 (q43 c4) ∷
   rw 17 (q41 c4) ∷
   rw 8 (q39 c4) ∷
   rw 8 (q38 c4) ∷
   rw 10 (q39 c4) ∷
   rw 15 (q41 c4) ∷
   rw 16 (q41 c4) ∷ []) Eq.refl
