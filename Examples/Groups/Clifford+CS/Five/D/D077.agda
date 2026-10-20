{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D077 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0382 ; wl0383 ; wl0384 ; wl0385 ; wl0393 ; wl0424 ; wl0425 ; wl0426 ; wl0427 ; wl0428 ; wl0429 ; wl0430 ; wl0431 ; wl0467 ; wp0130 ; wp0146 ; wp0147 ; wp0148 ; wp0149 ; wp0150)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0426 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ []) (wp0147 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01⁻ ∷ []) (wl0427 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CS01⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ []) (wl0425 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01⁻ ∷ []) (wp0146 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (S1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1 ∷ []) (wl0385 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ []) (wl0383 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (S1 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1 ∷ []) (wl0384 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ []) (wl0382 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ []) (wp0130 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X1 ∷ ι⁻ ∷ []) (ι⁻ ∷ X1 ∷ []) (zc⁻)
  q14 : Ws → Eqn
  q14 c4 = eqn (Sb2-0-41-3 ∷ ι⁻ ∷ []) (ι⁻ ∷ Sb2-0-41-3 ∷ []) (zc⁻)
  q15 : Ws → Eqn
  q15 c4 = eqn (CK10⁻ ∷ []) (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ []) (wl0424 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CK10⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CK10⁻ ∷ []) (wl0467 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0150 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0149 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (K0⁻ ∷ X1 ∷ []) (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X))
  q22 : Ws → Eqn
  q22 c4 = eqn (K0⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (CCZ ↑))
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS01⁻ ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ []) (wp0148 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS01⁻ ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01⁻ ∷ []) (wl0428 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0429 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01⁻ ∷ []) (wl0430 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wl0431 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)

-- F1 CS-K0 part32: 368 steps
lem-F1-CS-K0-part32 : Ws → ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ ι⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ
lem-F1-CS-K0-part32 c4 = derive (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ ι⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  (rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw⁻ 45 (q1 c4) ∷
   re 47 1 (CS03⁻ ∷ []) ∷
   rw⁻ 46 (q2 c4) ∷
   re 48 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 43 (q3 c4) ∷
   re 41 1 (CS03 ∷ []) ∷
   rw⁻ 40 (q4 c4) ∷
   re 42 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 37 (q3 c4) ∷
   rw 35 (q5 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw⁻ 43 (q6 c4) ∷
   rw⁻ 40 (q7 c4) ∷
   rw⁻ 37 (q6 c4) ∷
   rw⁻ 34 (q7 c4) ∷
   rw 37 (q1 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   rw⁻ 36 (q5 c4) ∷
   rw 37 (q1 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   re 36 5 (Sb2-0-41-3 ∷ []) ∷
   re 36 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw⁻ 46 (q1 c4) ∷
   re 48 1 (CS03⁻ ∷ []) ∷
   rw⁻ 47 (q8 c4) ∷
   re 49 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 44 (q9 c4) ∷
   re 42 1 (CS03 ∷ []) ∷
   rw⁻ 41 (q10 c4) ∷
   re 43 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 38 (q9 c4) ∷
   rw 36 (q5 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw⁻ 44 (q11 c4) ∷
   rw⁻ 41 (q12 c4) ∷
   rw⁻ 38 (q11 c4) ∷
   rw⁻ 35 (q12 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw⁻ 37 (q5 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   re 37 5 (Sb2-0-41-3 ∷ []) ∷
   rw 38 (q13 c4) ∷
   rw 37 (q14 c4) ∷
   rw 36 (q13 c4) ∷
   rw⁻ 30 (q15 c4) ∷
   rw⁻ 27 (q16 c4) ∷
   rw 27 (q15 c4) ∷
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
   re 26 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   re 32 1 (CS03 ∷ []) ∷
   re 38 1 (CS03⁻ ∷ []) ∷
   rw⁻ 31 (q17 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ []) ∷
   re 41 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 28 (q18 c4) ∷
   rw 26 (q19 c4) ∷
   rw 26 (q20 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q21 c4) ∷
   rw⁻ 35 (q22 c4) ∷
   rw⁻ 34 (q21 c4) ∷
   rw 36 (q23 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw⁻ 46 (q1 c4) ∷
   rw⁻ 47 (q24 c4) ∷
   rw⁻ 44 (q25 c4) ∷
   rw⁻ 41 (q26 c4) ∷
   rw⁻ 38 (q25 c4) ∷
   rw⁻ 35 (q27 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   rw⁻ 37 (q23 c4) ∷
   rw⁻ 38 (q21 c4) ∷
   rw⁻ 37 (q22 c4) ∷
   rw⁻ 36 (q21 c4) ∷
   rw⁻ 31 (q28 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw⁻ 29 (q22 c4) ∷
   rw⁻ 28 (q21 c4) ∷
   rw 30 (q23 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 41 (q24 c4) ∷
   rw⁻ 38 (q25 c4) ∷
   rw⁻ 35 (q26 c4) ∷
   rw⁻ 32 (q25 c4) ∷
   rw⁻ 29 (q27 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw⁻ 31 (q23 c4) ∷
   rw⁻ 32 (q21 c4) ∷
   rw⁻ 31 (q22 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw⁻ 25 (q28 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw⁻ 29 (q20 c4) ∷
   rw 29 (q29 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   re 29 5 (Sb2-0-41-3 ∷ []) ∷
   re 29 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   re 41 1 (CS03⁻ ∷ []) ∷
   rw⁻ 40 (q2 c4) ∷
   re 42 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 37 (q3 c4) ∷
   re 35 1 (CS03 ∷ []) ∷
   rw⁻ 34 (q4 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q3 c4) ∷
   rw 29 (q5 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 37 (q6 c4) ∷
   rw⁻ 34 (q7 c4) ∷
   rw⁻ 31 (q6 c4) ∷
   rw⁻ 28 (q7 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   re 30 5 (Sb2-0-41-3 ∷ []) ∷
   re 30 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   re 42 1 (CS03⁻ ∷ []) ∷
   rw⁻ 41 (q8 c4) ∷
   re 43 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 38 (q9 c4) ∷
   re 36 1 (CS03 ∷ []) ∷
   rw⁻ 35 (q10 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q9 c4) ∷
   rw 30 (q5 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 38 (q11 c4) ∷
   rw⁻ 35 (q12 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   re 31 5 (Sb2-0-41-3 ∷ []) ∷
   rw 32 (q13 c4) ∷
   rw 31 (q14 c4) ∷
   rw 30 (q13 c4) ∷
   rw⁻ 24 (q15 c4) ∷
   rw⁻ 21 (q16 c4) ∷
   rw 21 (q15 c4) ∷
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
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   re 26 1 (CS03 ∷ []) ∷
   re 32 1 (CS03⁻ ∷ []) ∷
   rw⁻ 25 (q17 c4) ∷
   re 29 1 (Sb2-0-3-1 ∷ []) ∷
   re 35 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 22 (q18 c4) ∷
   rw 20 (q19 c4) ∷
   rw 20 (q20 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw⁻ 29 (q22 c4) ∷
   rw⁻ 28 (q21 c4) ∷
   rw 30 (q23 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 41 (q24 c4) ∷
   rw⁻ 38 (q25 c4) ∷
   rw⁻ 35 (q26 c4) ∷
   rw⁻ 32 (q25 c4) ∷
   rw⁻ 29 (q27 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw⁻ 31 (q23 c4) ∷
   rw⁻ 32 (q21 c4) ∷
   rw⁻ 31 (q22 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw⁻ 25 (q28 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 23 (q22 c4) ∷
   rw⁻ 22 (q21 c4) ∷
   rw 24 (q23 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 35 (q24 c4) ∷
   rw⁻ 32 (q25 c4) ∷
   rw⁻ 29 (q26 c4) ∷
   rw⁻ 26 (q25 c4) ∷
   rw⁻ 23 (q27 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw⁻ 25 (q23 c4) ∷
   rw⁻ 26 (q21 c4) ∷
   rw⁻ 25 (q22 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 19 (q28 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw⁻ 23 (q20 c4) ∷
   rw 23 (q29 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   re 23 5 (Sb2-0-41-3 ∷ []) ∷
   re 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   re 35 1 (CS03⁻ ∷ []) ∷
   rw⁻ 34 (q2 c4) ∷
   re 36 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q3 c4) ∷
   re 29 1 (CS03 ∷ []) ∷
   rw⁻ 28 (q4 c4) ∷
   re 30 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q3 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 31 (q6 c4) ∷
   rw⁻ 28 (q7 c4) ∷
   rw⁻ 25 (q6 c4) ∷
   rw⁻ 22 (q7 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   re 24 5 (Sb2-0-41-3 ∷ []) ∷
   re 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   re 36 1 (CS03⁻ ∷ []) ∷
   rw⁻ 35 (q8 c4) ∷
   re 37 1 (Sb⁻2-0-3-1 ∷ []) ∷ []) Eq.refl
