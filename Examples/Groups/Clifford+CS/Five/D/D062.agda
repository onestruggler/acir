{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D062 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0388 ; wl0389 ; wl0390 ; wl0391 ; wl0392 ; wl0393 ; wl0394 ; wl0395 ; wl0396 ; wl0397 ; wl0398 ; wl0399 ; wl0400 ; wl0420 ; wp0134 ; wp0135 ; wp0136 ; wp0137 ; wp0138 ; wp0139)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CS01 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) (wl0391 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) (wp0135 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CS01 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ []) (wl0390 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CS01 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) (wl0389 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) (wp0134 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CK10 ∷ []) (ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ []) (wl0388 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CK10 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ []) (wl0420 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (X1 ∷ ι ∷ []) (ι ∷ X1 ∷ []) (zc)
  q11 : Ws → Eqn
  q11 c4 = eqn (Sb2-0-41-3 ∷ ι ∷ []) (ι ∷ Sb2-0-41-3 ∷ []) (zc)
  q12 : Ws → Eqn
  q12 c4 = eqn (S1⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1⁻ ∷ []) (wl0400 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ []) (wl0398 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (S1⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1⁻ ∷ []) (wl0399 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (S1⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ []) (wl0397 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (S1⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1⁻ ∷ []) (wp0139 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (wp0138 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (wp0137 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (K0 ∷ X1 ∷ []) (X1 ∷ K0 ∷ []) (c₁ (K) (X))
  q22 : Ws → Eqn
  q22 c4 = eqn (K0 ∷ CCZ234 ∷ []) (CCZ234 ∷ K0 ∷ []) (c₁ (K) (CCZ ↑))
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS01 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ []) (wp0136 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS01 ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) (wl0395 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS01 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01 ∷ []) (wl0396 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ []) (wl0394 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (wl0392 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)

-- F1 CS-K0 part17: 368 steps
lem-F1-CS-K0-part17 : Ws → ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ
lem-F1-CS-K0-part17 c4 = derive (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  (rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   re 31 5 (Sb2-0-41-3 ∷ []) ∷
   re 31 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   re 43 1 (CS03⁻ ∷ []) ∷
   rw⁻ 42 (q2 c4) ∷
   re 44 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 39 (q3 c4) ∷
   re 37 1 (CS03 ∷ []) ∷
   rw⁻ 36 (q4 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 33 (q3 c4) ∷
   rw 31 (q5 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw⁻ 39 (q6 c4) ∷
   rw⁻ 36 (q7 c4) ∷
   rw⁻ 33 (q6 c4) ∷
   rw⁻ 30 (q7 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   re 32 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 24 (q8 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw 21 (q8 c4) ∷
   rw 20 (q10 c4) ∷
   rw 19 (q11 c4) ∷
   rw 18 (q10 c4) ∷
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   re 32 1 (CS03⁻ ∷ []) ∷
   rw⁻ 31 (q12 c4) ∷
   re 33 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 28 (q13 c4) ∷
   re 26 1 (CS03 ∷ []) ∷
   rw⁻ 25 (q14 c4) ∷
   re 27 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 22 (q13 c4) ∷
   rw 20 (q5 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 28 (q15 c4) ∷
   rw⁻ 25 (q16 c4) ∷
   rw⁻ 22 (q15 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   re 21 5 (Sb2-0-41-3 ∷ []) ∷
   re 21 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   re 33 1 (CS03⁻ ∷ []) ∷
   rw⁻ 32 (q2 c4) ∷
   re 34 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 29 (q3 c4) ∷
   re 27 1 (CS03 ∷ []) ∷
   rw⁻ 26 (q4 c4) ∷
   re 28 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q3 c4) ∷
   rw 21 (q5 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 29 (q6 c4) ∷
   rw⁻ 26 (q7 c4) ∷
   rw⁻ 23 (q6 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   re 22 5 (Sb2-0-41-3 ∷ []) ∷
   re 22 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   re 28 1 (CS03 ∷ []) ∷
   re 34 1 (CS03⁻ ∷ []) ∷
   rw⁻ 27 (q17 c4) ∷
   re 31 1 (Sb2-0-3-1 ∷ []) ∷
   re 37 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q18 c4) ∷
   rw 22 (q19 c4) ∷
   rw 22 (q20 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q21 c4) ∷
   rw⁻ 31 (q22 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw 32 (q23 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw⁻ 43 (q24 c4) ∷
   rw⁻ 40 (q25 c4) ∷
   rw⁻ 37 (q26 c4) ∷
   rw⁻ 34 (q25 c4) ∷
   rw⁻ 31 (q27 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   rw⁻ 33 (q23 c4) ∷
   rw⁻ 34 (q21 c4) ∷
   rw⁻ 33 (q22 c4) ∷
   rw⁻ 32 (q21 c4) ∷
   rw⁻ 27 (q28 c4) ∷
   rw⁻ 26 (q21 c4) ∷
   rw⁻ 25 (q22 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw 26 (q23 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 37 (q24 c4) ∷
   rw⁻ 34 (q25 c4) ∷
   rw⁻ 31 (q26 c4) ∷
   rw⁻ 28 (q25 c4) ∷
   rw⁻ 25 (q27 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw⁻ 27 (q23 c4) ∷
   rw⁻ 28 (q21 c4) ∷
   rw⁻ 27 (q22 c4) ∷
   rw⁻ 26 (q21 c4) ∷
   rw⁻ 21 (q28 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw⁻ 25 (q20 c4) ∷
   rw 25 (q29 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   re 25 5 (Sb2-0-41-3 ∷ []) ∷
   re 25 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   re 37 1 (CS03⁻ ∷ []) ∷
   rw⁻ 36 (q2 c4) ∷
   re 38 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 33 (q3 c4) ∷
   re 31 1 (CS03 ∷ []) ∷
   rw⁻ 30 (q4 c4) ∷
   re 32 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 27 (q3 c4) ∷
   rw 25 (q5 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 33 (q6 c4) ∷
   rw⁻ 30 (q7 c4) ∷
   rw⁻ 27 (q6 c4) ∷
   rw⁻ 24 (q7 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   re 26 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 18 (q8 c4) ∷
   rw⁻ 15 (q9 c4) ∷
   rw 15 (q8 c4) ∷
   rw 14 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 12 (q10 c4) ∷
   re 14 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   re 26 1 (CS03⁻ ∷ []) ∷
   rw⁻ 25 (q12 c4) ∷
   re 27 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 22 (q13 c4) ∷
   re 20 1 (CS03 ∷ []) ∷
   rw⁻ 19 (q14 c4) ∷
   re 21 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 16 (q13 c4) ∷
   rw 14 (q5 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 22 (q15 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   re 15 5 (Sb2-0-41-3 ∷ []) ∷
   re 15 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   re 27 1 (CS03⁻ ∷ []) ∷
   rw⁻ 26 (q2 c4) ∷
   re 28 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q3 c4) ∷
   re 21 1 (CS03 ∷ []) ∷
   rw⁻ 20 (q4 c4) ∷
   re 22 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 17 (q3 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 23 (q6 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   rw⁻ 17 (q6 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   re 16 5 (Sb2-0-41-3 ∷ []) ∷
   re 16 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 17 (q1 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   re 22 1 (CS03 ∷ []) ∷
   re 28 1 (CS03⁻ ∷ []) ∷
   rw⁻ 21 (q17 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   re 31 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 18 (q18 c4) ∷
   rw 16 (q19 c4) ∷
   rw 16 (q20 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q21 c4) ∷
   rw⁻ 25 (q22 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw 26 (q23 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 37 (q24 c4) ∷
   rw⁻ 34 (q25 c4) ∷
   rw⁻ 31 (q26 c4) ∷
   rw⁻ 28 (q25 c4) ∷
   rw⁻ 25 (q27 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw⁻ 27 (q23 c4) ∷
   rw⁻ 28 (q21 c4) ∷
   rw⁻ 27 (q22 c4) ∷
   rw⁻ 26 (q21 c4) ∷
   rw⁻ 21 (q28 c4) ∷
   rw⁻ 20 (q21 c4) ∷
   rw⁻ 19 (q22 c4) ∷
   rw⁻ 18 (q21 c4) ∷
   rw 20 (q23 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 31 (q24 c4) ∷
   rw⁻ 28 (q25 c4) ∷
   rw⁻ 25 (q26 c4) ∷
   rw⁻ 22 (q25 c4) ∷
   rw⁻ 19 (q27 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw⁻ 21 (q23 c4) ∷
   rw⁻ 22 (q21 c4) ∷
   rw⁻ 21 (q22 c4) ∷
   rw⁻ 20 (q21 c4) ∷
   rw⁻ 15 (q28 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw⁻ 19 (q20 c4) ∷
   rw 19 (q29 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   re 19 5 (Sb2-0-41-3 ∷ []) ∷
   re 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   re 31 1 (CS03⁻ ∷ []) ∷
   rw⁻ 30 (q2 c4) ∷
   re 32 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 27 (q3 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   rw⁻ 24 (q4 c4) ∷
   re 26 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 21 (q3 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 27 (q6 c4) ∷
   rw⁻ 24 (q7 c4) ∷
   rw⁻ 21 (q6 c4) ∷
   rw⁻ 18 (q7 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   re 20 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 12 (q8 c4) ∷ []) Eq.refl
