{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D071 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0382 ; wl0383 ; wl0384 ; wl0385 ; wl0393 ; wl0424 ; wl0425 ; wl0426 ; wl0427 ; wl0428 ; wl0429 ; wl0430 ; wl0431 ; wl0456 ; wl0457 ; wl0458 ; wl0459 ; wl0465 ; wl0466 ; wl0467 ; wp0130 ; wp0146 ; wp0147 ; wp0148 ; wp0149 ; wp0150 ; wp0165 ; wp0169 ; wp0170)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Toff314 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ Toff314 ∷ []) (wl0456 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CS03⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CS03⁻ ∷ []) (wp0165 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Toff204 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ Toff204 ∷ []) (wp0169 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ123 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0465 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CS03 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CS03 ∷ []) (wl0458 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ []) (wl0457 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS03⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CS03⁻ ∷ []) (wl0459 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Toff204 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ Toff204 ∷ []) (wp0170 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ123 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CCZ123 ∷ []) (wl0466 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CK10⁻ ∷ []) (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ []) (wl0424 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0426 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ []) (wp0147 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01⁻ ∷ []) (wl0427 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS01⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ []) (wl0425 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01⁻ ∷ []) (wp0146 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0150 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0149 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (K0⁻ ∷ X1 ∷ []) (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X))
  q24 : Ws → Eqn
  q24 c4 = eqn (K0⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (CCZ ↑))
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS01⁻ ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ []) (wp0148 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS01⁻ ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01⁻ ∷ []) (wl0428 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0429 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01⁻ ∷ []) (wl0430 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wl0431 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (S1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1 ∷ []) (wl0385 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ []) (wl0383 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (S1 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1 ∷ []) (wl0384 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ []) (wl0382 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ []) (wp0130 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (X1 ∷ ι⁻ ∷ []) (ι⁻ ∷ X1 ∷ []) (zc⁻)
  q38 : Ws → Eqn
  q38 c4 = eqn (Sb2-0-41-3 ∷ ι⁻ ∷ []) (ι⁻ ∷ Sb2-0-41-3 ∷ []) (zc⁻)
  q39 : Ws → Eqn
  q39 c4 = eqn (CK10⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CK10⁻ ∷ []) (wl0467 (lit c4))

-- F1 CS-K0 part26: 374 steps
lem-F1-CS-K0-part26 : Ws → ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ CS03 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ
lem-F1-CS-K0-part26 c4 = derive (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ CS03 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  (re 12 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 13 (q1 c4) ∷
   re 17 1 (CS03⁻ ∷ []) ∷
   rw⁻ 14 (q2 c4) ∷
   re 14 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q1 c4) ∷
   rw 19 (q3 c4) ∷
   rw 19 (q4 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw⁻ 17 (q6 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw⁻ 19 (q6 c4) ∷
   rw⁻ 16 (q4 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   re 12 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 12 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 12 1 (CS03 ∷ []) ∷
   rw⁻ 9 (q7 c4) ∷
   re 9 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 10 (q8 c4) ∷
   re 14 1 (CS03⁻ ∷ []) ∷
   rw⁻ 11 (q9 c4) ∷
   re 11 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 12 (q8 c4) ∷
   rw 16 (q3 c4) ∷
   rw 16 (q4 c4) ∷
   rw⁻ 13 (q10 c4) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 15 (q10 c4) ∷
   rw⁻ 16 (q11 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw⁻ 13 (q3 c4) ∷
   re 9 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 31 (q12 c4) ∷
   re 29 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q13 c4) ∷
   rw⁻ 33 (q13 c4) ∷
   rw⁻ 36 (q13 c4) ∷
   rw⁻ 39 (q13 c4) ∷
   re 41 1 (CS03⁻ ∷ []) ∷
   rw⁻ 40 (q14 c4) ∷
   re 42 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 37 (q15 c4) ∷
   re 35 1 (CS03 ∷ []) ∷
   rw⁻ 34 (q16 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q15 c4) ∷
   rw 29 (q4 c4) ∷
   rw⁻ 30 (q13 c4) ∷
   rw⁻ 33 (q13 c4) ∷
   rw⁻ 36 (q13 c4) ∷
   rw⁻ 37 (q17 c4) ∷
   rw⁻ 34 (q18 c4) ∷
   rw⁻ 31 (q17 c4) ∷
   rw⁻ 28 (q18 c4) ∷
   rw 31 (q13 c4) ∷
   rw 32 (q13 c4) ∷
   rw 33 (q13 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw 31 (q13 c4) ∷
   rw 32 (q13 c4) ∷
   rw 33 (q13 c4) ∷
   rw 34 (q13 c4) ∷
   re 30 5 (Sb2-0-41-3 ∷ []) ∷
   re 30 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q13 c4) ∷
   rw⁻ 34 (q13 c4) ∷
   rw⁻ 37 (q13 c4) ∷
   rw⁻ 40 (q13 c4) ∷
   re 36 1 (CS03 ∷ []) ∷
   re 42 1 (CS03⁻ ∷ []) ∷
   rw⁻ 35 (q19 c4) ∷
   re 39 1 (Sb2-0-3-1 ∷ []) ∷
   re 45 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q20 c4) ∷
   rw 30 (q21 c4) ∷
   rw 30 (q22 c4) ∷
   rw⁻ 31 (q13 c4) ∷
   rw⁻ 34 (q13 c4) ∷
   rw⁻ 37 (q13 c4) ∷
   rw⁻ 40 (q23 c4) ∷
   rw⁻ 39 (q24 c4) ∷
   rw⁻ 38 (q23 c4) ∷
   rw 40 (q25 c4) ∷
   rw⁻ 41 (q13 c4) ∷
   rw⁻ 44 (q13 c4) ∷
   rw⁻ 47 (q13 c4) ∷
   rw⁻ 50 (q13 c4) ∷
   rw⁻ 51 (q26 c4) ∷
   rw⁻ 48 (q27 c4) ∷
   rw⁻ 45 (q28 c4) ∷
   rw⁻ 42 (q27 c4) ∷
   rw⁻ 39 (q29 c4) ∷
   rw 42 (q13 c4) ∷
   rw 43 (q13 c4) ∷
   rw 44 (q13 c4) ∷
   rw 45 (q13 c4) ∷
   rw⁻ 41 (q25 c4) ∷
   rw⁻ 42 (q23 c4) ∷
   rw⁻ 41 (q24 c4) ∷
   rw⁻ 40 (q23 c4) ∷
   rw⁻ 35 (q30 c4) ∷
   rw⁻ 34 (q23 c4) ∷
   rw⁻ 33 (q24 c4) ∷
   rw⁻ 32 (q23 c4) ∷
   rw 34 (q25 c4) ∷
   rw⁻ 35 (q13 c4) ∷
   rw⁻ 38 (q13 c4) ∷
   rw⁻ 41 (q13 c4) ∷
   rw⁻ 44 (q13 c4) ∷
   rw⁻ 45 (q26 c4) ∷
   rw⁻ 42 (q27 c4) ∷
   rw⁻ 39 (q28 c4) ∷
   rw⁻ 36 (q27 c4) ∷
   rw⁻ 33 (q29 c4) ∷
   rw 36 (q13 c4) ∷
   rw 37 (q13 c4) ∷
   rw 38 (q13 c4) ∷
   rw 39 (q13 c4) ∷
   rw⁻ 35 (q25 c4) ∷
   rw⁻ 36 (q23 c4) ∷
   rw⁻ 35 (q24 c4) ∷
   rw⁻ 34 (q23 c4) ∷
   rw⁻ 29 (q30 c4) ∷
   rw 34 (q13 c4) ∷
   rw 35 (q13 c4) ∷
   rw 36 (q13 c4) ∷
   rw⁻ 33 (q22 c4) ∷
   rw 33 (q31 c4) ∷
   rw 34 (q13 c4) ∷
   rw 35 (q13 c4) ∷
   rw 36 (q13 c4) ∷
   rw 37 (q13 c4) ∷
   re 33 5 (Sb2-0-41-3 ∷ []) ∷
   re 33 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 34 (q13 c4) ∷
   rw⁻ 37 (q13 c4) ∷
   rw⁻ 40 (q13 c4) ∷
   rw⁻ 43 (q13 c4) ∷
   re 45 1 (CS03⁻ ∷ []) ∷
   rw⁻ 44 (q14 c4) ∷
   re 46 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 41 (q15 c4) ∷
   re 39 1 (CS03 ∷ []) ∷
   rw⁻ 38 (q16 c4) ∷
   re 40 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 35 (q15 c4) ∷
   rw 33 (q4 c4) ∷
   rw⁻ 34 (q13 c4) ∷
   rw⁻ 37 (q13 c4) ∷
   rw⁻ 40 (q13 c4) ∷
   rw⁻ 41 (q17 c4) ∷
   rw⁻ 38 (q18 c4) ∷
   rw⁻ 35 (q17 c4) ∷
   rw⁻ 32 (q18 c4) ∷
   rw 35 (q13 c4) ∷
   rw 36 (q13 c4) ∷
   rw 37 (q13 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw 35 (q13 c4) ∷
   rw 36 (q13 c4) ∷
   rw 37 (q13 c4) ∷
   rw 38 (q13 c4) ∷
   re 34 5 (Sb2-0-41-3 ∷ []) ∷
   re 34 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 35 (q13 c4) ∷
   rw⁻ 38 (q13 c4) ∷
   rw⁻ 41 (q13 c4) ∷
   rw⁻ 44 (q13 c4) ∷
   re 46 1 (CS03⁻ ∷ []) ∷
   rw⁻ 45 (q32 c4) ∷
   re 47 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 42 (q33 c4) ∷
   re 40 1 (CS03 ∷ []) ∷
   rw⁻ 39 (q34 c4) ∷
   re 41 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 36 (q33 c4) ∷
   rw 34 (q4 c4) ∷
   rw⁻ 35 (q13 c4) ∷
   rw⁻ 38 (q13 c4) ∷
   rw⁻ 41 (q13 c4) ∷
   rw⁻ 42 (q35 c4) ∷
   rw⁻ 39 (q36 c4) ∷
   rw⁻ 36 (q35 c4) ∷
   rw⁻ 33 (q36 c4) ∷
   rw 36 (q13 c4) ∷
   rw 37 (q13 c4) ∷
   rw 38 (q13 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw 36 (q13 c4) ∷
   rw 37 (q13 c4) ∷
   rw 38 (q13 c4) ∷
   rw 39 (q13 c4) ∷
   re 35 5 (Sb2-0-41-3 ∷ []) ∷
   rw 36 (q37 c4) ∷
   rw 35 (q38 c4) ∷
   rw 34 (q37 c4) ∷
   rw⁻ 28 (q12 c4) ∷
   rw⁻ 25 (q39 c4) ∷
   rw 25 (q12 c4) ∷
   re 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q13 c4) ∷
   rw⁻ 27 (q13 c4) ∷
   rw⁻ 30 (q13 c4) ∷
   rw⁻ 33 (q13 c4) ∷
   re 35 1 (CS03⁻ ∷ []) ∷
   rw⁻ 34 (q14 c4) ∷
   re 36 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q15 c4) ∷
   re 29 1 (CS03 ∷ []) ∷
   rw⁻ 28 (q16 c4) ∷
   re 30 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q15 c4) ∷
   rw 23 (q4 c4) ∷
   rw⁻ 24 (q13 c4) ∷
   rw⁻ 27 (q13 c4) ∷
   rw⁻ 30 (q13 c4) ∷
   rw⁻ 31 (q17 c4) ∷
   rw⁻ 28 (q18 c4) ∷
   rw⁻ 25 (q17 c4) ∷
   rw⁻ 22 (q18 c4) ∷
   rw 25 (q13 c4) ∷
   rw 26 (q13 c4) ∷
   rw 27 (q13 c4) ∷
   rw⁻ 24 (q4 c4) ∷
   rw 25 (q13 c4) ∷
   rw 26 (q13 c4) ∷
   rw 27 (q13 c4) ∷
   rw 28 (q13 c4) ∷
   re 24 5 (Sb2-0-41-3 ∷ []) ∷
   re 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q13 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 31 (q13 c4) ∷
   rw⁻ 34 (q13 c4) ∷
   re 30 1 (CS03 ∷ []) ∷
   re 36 1 (CS03⁻ ∷ []) ∷
   rw⁻ 29 (q19 c4) ∷
   re 33 1 (Sb2-0-3-1 ∷ []) ∷
   re 39 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q20 c4) ∷
   rw 24 (q21 c4) ∷
   rw 24 (q22 c4) ∷
   rw⁻ 25 (q13 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 31 (q13 c4) ∷
   rw⁻ 34 (q23 c4) ∷
   rw⁻ 33 (q24 c4) ∷
   rw⁻ 32 (q23 c4) ∷
   rw 34 (q25 c4) ∷
   rw⁻ 35 (q13 c4) ∷
   rw⁻ 38 (q13 c4) ∷
   rw⁻ 41 (q13 c4) ∷
   rw⁻ 44 (q13 c4) ∷
   rw⁻ 45 (q26 c4) ∷
   rw⁻ 42 (q27 c4) ∷
   rw⁻ 39 (q28 c4) ∷
   rw⁻ 36 (q27 c4) ∷
   rw⁻ 33 (q29 c4) ∷
   rw 36 (q13 c4) ∷
   rw 37 (q13 c4) ∷
   rw 38 (q13 c4) ∷
   rw 39 (q13 c4) ∷
   rw⁻ 35 (q25 c4) ∷
   rw⁻ 36 (q23 c4) ∷
   rw⁻ 35 (q24 c4) ∷
   rw⁻ 34 (q23 c4) ∷
   rw⁻ 29 (q30 c4) ∷
   rw⁻ 28 (q23 c4) ∷
   rw⁻ 27 (q24 c4) ∷
   rw⁻ 26 (q23 c4) ∷
   rw 28 (q25 c4) ∷
   rw⁻ 29 (q13 c4) ∷
   rw⁻ 32 (q13 c4) ∷
   rw⁻ 35 (q13 c4) ∷
   rw⁻ 38 (q13 c4) ∷
   rw⁻ 39 (q26 c4) ∷
   rw⁻ 36 (q27 c4) ∷
   rw⁻ 33 (q28 c4) ∷
   rw⁻ 30 (q27 c4) ∷
   rw⁻ 27 (q29 c4) ∷
   rw 30 (q13 c4) ∷
   rw 31 (q13 c4) ∷
   rw 32 (q13 c4) ∷
   rw 33 (q13 c4) ∷
   rw⁻ 29 (q25 c4) ∷
   rw⁻ 30 (q23 c4) ∷
   rw⁻ 29 (q24 c4) ∷
   rw⁻ 28 (q23 c4) ∷
   rw⁻ 23 (q30 c4) ∷
   rw 28 (q13 c4) ∷
   rw 29 (q13 c4) ∷
   rw 30 (q13 c4) ∷
   rw⁻ 27 (q22 c4) ∷
   rw 27 (q31 c4) ∷
   rw 28 (q13 c4) ∷
   rw 29 (q13 c4) ∷
   rw 30 (q13 c4) ∷
   rw 31 (q13 c4) ∷
   re 27 5 (Sb2-0-41-3 ∷ []) ∷
   re 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 31 (q13 c4) ∷
   rw⁻ 34 (q13 c4) ∷
   rw⁻ 37 (q13 c4) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   rw⁻ 38 (q14 c4) ∷
   re 40 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 35 (q15 c4) ∷
   re 33 1 (CS03 ∷ []) ∷
   rw⁻ 32 (q16 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 29 (q15 c4) ∷
   rw 27 (q4 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 31 (q13 c4) ∷
   rw⁻ 34 (q13 c4) ∷
   rw⁻ 35 (q17 c4) ∷
   rw⁻ 32 (q18 c4) ∷
   rw⁻ 29 (q17 c4) ∷
   rw⁻ 26 (q18 c4) ∷
   rw 29 (q13 c4) ∷
   rw 30 (q13 c4) ∷
   rw 31 (q13 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw 29 (q13 c4) ∷
   rw 30 (q13 c4) ∷
   rw 31 (q13 c4) ∷
   rw 32 (q13 c4) ∷
   re 28 5 (Sb2-0-41-3 ∷ []) ∷
   re 28 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 29 (q13 c4) ∷
   rw⁻ 32 (q13 c4) ∷
   rw⁻ 35 (q13 c4) ∷
   rw⁻ 38 (q13 c4) ∷
   re 40 1 (CS03⁻ ∷ []) ∷
   rw⁻ 39 (q32 c4) ∷
   re 41 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 36 (q33 c4) ∷
   re 34 1 (CS03 ∷ []) ∷
   rw⁻ 33 (q34 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q33 c4) ∷
   rw 28 (q4 c4) ∷
   rw⁻ 29 (q13 c4) ∷
   rw⁻ 32 (q13 c4) ∷
   rw⁻ 35 (q13 c4) ∷
   rw⁻ 36 (q35 c4) ∷
   rw⁻ 33 (q36 c4) ∷
   rw⁻ 30 (q35 c4) ∷
   rw⁻ 27 (q36 c4) ∷
   rw 30 (q13 c4) ∷
   rw 31 (q13 c4) ∷
   rw 32 (q13 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw 30 (q13 c4) ∷
   rw 31 (q13 c4) ∷
   rw 32 (q13 c4) ∷
   rw 33 (q13 c4) ∷
   re 29 5 (Sb2-0-41-3 ∷ []) ∷
   rw 30 (q37 c4) ∷
   rw 29 (q38 c4) ∷
   rw 28 (q37 c4) ∷
   rw⁻ 22 (q12 c4) ∷
   rw⁻ 19 (q39 c4) ∷
   rw 19 (q12 c4) ∷
   re 17 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 18 (q13 c4) ∷
   rw⁻ 21 (q13 c4) ∷
   rw⁻ 24 (q13 c4) ∷
   rw⁻ 27 (q13 c4) ∷
   re 29 1 (CS03⁻ ∷ []) ∷
   rw⁻ 28 (q14 c4) ∷
   re 30 1 (Sb⁻2-0-3-1 ∷ []) ∷ []) Eq.refl
