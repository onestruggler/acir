{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D108 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0503 ; wl0509 ; wl0513 ; wl0514 ; wl0528 ; wl0529 ; wl0530 ; wl0531 ; wl0576 ; wl0577 ; wp0192 ; wp0200 ; wp0201 ; wp0202 ; wp0203 ; wp0204 ; wp0205 ; wp0238 ; wp0239 ; wp0240 ; wp0241 ; wp0242 ; wp0243)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 ; lem-beta-T-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-X1-beta-at0210243143 ; lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04233240 ; lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04233240 ; lem-auto-CSd01-∣-BOX⟨2·0134⟩-at143143 ; lem-auto-S0-∣-BOX⟨1·0234⟩-at12243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) (wl0514 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (X0 ∷ CCZ234 ∷ []) (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑))
  q7 : Ws → Eqn
  q7 c4 = eqn (CK01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ))
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Toff314 ∷ CS03 ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) (wp0192 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CS03⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS03⁻ ∷ []) (wl0513 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (X0 ∷ Bx2-0413 ∷ X0 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ []) (lem-X1-beta-at0210243143 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ134 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ134 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04233240 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ []) (wp0205 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ134 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ134 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04233240 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl0503 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ []) (wp0202 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Sb2-0-41-3 ∷ Toff314 ∷ []) (Toff314 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03 ∷ []) (wl0531 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0204 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS03⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ []) (wl0529 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) (wp0201 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS04⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS04⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩-at143143 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ134 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CCZ134 ∷ []) (wp0238 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Toff314 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ []) (wp0239 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CS03 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CS03 ∷ []) (wp0240 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CS03⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CS03⁻ ∷ []) (wp0241 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (S0 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·0234⟩-at12243143 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ134 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CCZ134 ∷ []) (wp0242 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff314 ∷ []) (wp0243 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CS03 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CS03 ∷ []) (wl0576 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS03⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CS03⁻ ∷ []) (wl0577 (lit c4))

-- F1 CS-K1 [rhs shape] part17: 421 steps
lem-F1-CS-K1-rhs-shape-part17 : Ws → ⟪ (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-rhs-shape-part17 c4 = derive (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 31 (q1 c4) ∷
   rw 32 (q2 c4) ∷
   rw 33 (q2 c4) ∷
   rw 34 (q2 c4) ∷
   rw 35 (q2 c4) ∷
   re 31 5 (Sb2-0-41-3 ∷ []) ∷
   re 29 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 25 5 (Sb2-0-41-3 ∷ []) ∷
   re 25 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 25 (q3 c4) ∷
   rw 25 (q4 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw 25 (q6 c4) ∷
   rw 24 (q7 c4) ∷
   rw 23 (q6 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 27 (q6 c4) ∷
   rw 26 (q7 c4) ∷
   rw 25 (q6 c4) ∷
   rw⁻ 22 (q4 c4) ∷
   rw 22 (q8 c4) ∷
   re 27 1 (CS03 ∷ []) ∷
   rw⁻ 23 (q9 c4) ∷
   re 24 1 (Sb2-0-3-1 ∷ []) ∷
   re 29 1 (CS03⁻ ∷ []) ∷
   rw⁻ 26 (q10 c4) ∷
   re 26 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 22 5 (Sb2-0-41-3 ∷ []) ∷
   re 22 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q2 c4) ∷
   rw 21 (q11 c4) ∷
   rw 21 (q12 c4) ∷
   rw 20 (q13 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw 19 (q11 c4) ∷
   rw 19 (q12 c4) ∷
   rw 23 (q14 c4) ∷
   rw 20 (q14 c4) ∷
   rw 21 (q15 c4) ∷
   rw 22 (q14 c4) ∷
   rw 23 (q16 c4) ∷
   rw⁻ 22 (q17 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 20 (q17 c4) ∷
   re 24 1 (CS03 ∷ []) ∷
   re 22 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   re 34 1 (CS03⁻ ∷ []) ∷
   rw⁻ 33 (q19 c4) ∷
   re 35 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 28 1 (CS03 ∷ []) ∷
   rw⁻ 24 (q20 c4) ∷
   re 29 1 (Sb2-0-3-1 ∷ []) ∷
   rw 22 (q1 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw⁻ 27 (q22 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 21 (q22 c4) ∷
   rw 24 (q2 c4) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q2 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw 24 (q2 c4) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q2 c4) ∷
   rw 27 (q2 c4) ∷
   re 23 5 (Sb2-0-41-3 ∷ []) ∷
   re 21 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q17 c4) ∷
   rw 23 (q18 c4) ∷
   rw⁻ 22 (q17 c4) ∷
   re 26 1 (CS03⁻ ∷ []) ∷
   re 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   re 36 1 (CS03⁻ ∷ []) ∷
   rw⁻ 35 (q23 c4) ∷
   re 37 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 30 1 (CS03 ∷ []) ∷
   rw⁻ 26 (q24 c4) ∷
   re 31 1 (Sb2-0-3-1 ∷ []) ∷
   rw 24 (q1 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 32 (q25 c4) ∷
   rw⁻ 29 (q26 c4) ∷
   rw⁻ 26 (q25 c4) ∷
   rw⁻ 23 (q26 c4) ∷
   rw 26 (q2 c4) ∷
   rw 27 (q2 c4) ∷
   rw 28 (q2 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw 26 (q2 c4) ∷
   rw 27 (q2 c4) ∷
   rw 28 (q2 c4) ∷
   rw 29 (q2 c4) ∷
   re 25 5 (Sb2-0-41-3 ∷ []) ∷
   re 23 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 19 5 (Sb2-0-41-3 ∷ []) ∷
   re 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 19 (q3 c4) ∷
   rw 19 (q4 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw 19 (q6 c4) ∷
   rw 18 (q7 c4) ∷
   rw 17 (q6 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw 21 (q6 c4) ∷
   rw 20 (q7 c4) ∷
   rw 19 (q6 c4) ∷
   rw⁻ 16 (q4 c4) ∷
   rw 16 (q8 c4) ∷
   re 21 1 (CS03 ∷ []) ∷
   rw⁻ 17 (q9 c4) ∷
   re 18 1 (Sb2-0-3-1 ∷ []) ∷
   re 23 1 (CS03⁻ ∷ []) ∷
   rw⁻ 20 (q10 c4) ∷
   re 20 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 16 5 (Sb2-0-41-3 ∷ []) ∷
   re 16 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 17 (q2 c4) ∷
   rw 15 (q11 c4) ∷
   rw 15 (q12 c4) ∷
   rw 14 (q13 c4) ∷
   rw⁻ 15 (q2 c4) ∷
   rw 13 (q11 c4) ∷
   rw 13 (q12 c4) ∷
   rw 17 (q14 c4) ∷
   rw 14 (q14 c4) ∷
   rw 15 (q15 c4) ∷
   rw 16 (q14 c4) ∷
   rw 17 (q16 c4) ∷
   rw⁻ 16 (q17 c4) ∷
   rw 15 (q18 c4) ∷
   rw⁻ 14 (q17 c4) ∷
   re 18 1 (CS03 ∷ []) ∷
   re 16 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 17 (q2 c4) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   re 28 1 (CS03⁻ ∷ []) ∷
   rw⁻ 27 (q19 c4) ∷
   re 29 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 22 1 (CS03 ∷ []) ∷
   rw⁻ 18 (q20 c4) ∷
   re 23 1 (Sb2-0-3-1 ∷ []) ∷
   rw 16 (q1 c4) ∷
   rw⁻ 17 (q2 c4) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 21 (q22 c4) ∷
   rw⁻ 18 (q21 c4) ∷
   rw⁻ 15 (q22 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   re 17 5 (Sb2-0-41-3 ∷ []) ∷
   re 15 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 18 (q17 c4) ∷
   rw 17 (q18 c4) ∷
   rw⁻ 16 (q17 c4) ∷
   re 20 1 (CS03⁻ ∷ []) ∷
   re 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   re 30 1 (CS03⁻ ∷ []) ∷
   rw⁻ 29 (q23 c4) ∷
   re 31 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 24 1 (CS03 ∷ []) ∷
   rw⁻ 20 (q24 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   rw 18 (q1 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 26 (q25 c4) ∷
   rw⁻ 23 (q26 c4) ∷
   rw⁻ 20 (q25 c4) ∷
   rw⁻ 17 (q26 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   re 19 5 (Sb2-0-41-3 ∷ []) ∷
   re 17 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 13 5 (Sb2-0-41-3 ∷ []) ∷
   re 13 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 14 (q2 c4) ∷
   rw 12 (q11 c4) ∷
   rw 12 (q12 c4) ∷
   rw 11 (q27 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw 10 (q11 c4) ∷
   rw 10 (q12 c4) ∷
   rw 14 (q14 c4) ∷
   rw 11 (q28 c4) ∷
   rw 14 (q16 c4) ∷
   rw⁻ 11 (q29 c4) ∷
   re 15 1 (CS03 ∷ []) ∷
   rw⁻ 12 (q30 c4) ∷
   re 12 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 13 (q29 c4) ∷
   re 17 1 (CS03⁻ ∷ []) ∷
   rw⁻ 14 (q31 c4) ∷
   re 14 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 10 5 (Sb2-0-41-3 ∷ []) ∷
   re 10 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 11 (q2 c4) ∷
   rw 9 (q11 c4) ∷
   rw 9 (q12 c4) ∷
   rw 8 (q32 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   rw 7 (q11 c4) ∷
   rw 7 (q12 c4) ∷
   rw 11 (q14 c4) ∷
   rw 8 (q33 c4) ∷
   rw 11 (q16 c4) ∷
   rw⁻ 8 (q34 c4) ∷
   re 12 1 (CS03 ∷ []) ∷
   rw⁻ 9 (q35 c4) ∷
   re 9 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 10 (q34 c4) ∷
   re 14 1 (CS03⁻ ∷ []) ∷
   rw⁻ 11 (q36 c4) ∷
   re 11 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 7 5 (Sb2-0-41-3 ∷ []) ∷
   re 29 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q2 c4) ∷
   rw 28 (q11 c4) ∷
   rw 28 (q12 c4) ∷
   rw 27 (q13 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw 26 (q11 c4) ∷
   rw 26 (q12 c4) ∷
   rw 30 (q14 c4) ∷
   rw 27 (q14 c4) ∷
   rw 28 (q15 c4) ∷
   rw 29 (q14 c4) ∷
   rw 30 (q16 c4) ∷
   rw⁻ 29 (q17 c4) ∷
   rw 28 (q18 c4) ∷
   rw⁻ 27 (q17 c4) ∷
   re 31 1 (CS03 ∷ []) ∷
   re 29 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q2 c4) ∷
   rw⁻ 33 (q2 c4) ∷
   rw⁻ 36 (q2 c4) ∷
   rw⁻ 39 (q2 c4) ∷
   re 41 1 (CS03⁻ ∷ []) ∷
   rw⁻ 40 (q19 c4) ∷
   re 42 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 35 1 (CS03 ∷ []) ∷
   rw⁻ 31 (q20 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ []) ∷
   rw 29 (q1 c4) ∷
   rw⁻ 30 (q2 c4) ∷
   rw⁻ 33 (q2 c4) ∷
   rw⁻ 36 (q2 c4) ∷
   rw⁻ 37 (q21 c4) ∷
   rw⁻ 34 (q22 c4) ∷
   rw⁻ 31 (q21 c4) ∷
   rw⁻ 28 (q22 c4) ∷
   rw 31 (q2 c4) ∷
   rw 32 (q2 c4) ∷
   rw 33 (q2 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw 31 (q2 c4) ∷
   rw 32 (q2 c4) ∷
   rw 33 (q2 c4) ∷
   rw 34 (q2 c4) ∷
   re 30 5 (Sb2-0-41-3 ∷ []) ∷
   re 28 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q17 c4) ∷
   rw 30 (q18 c4) ∷
   rw⁻ 29 (q17 c4) ∷
   re 33 1 (CS03⁻ ∷ []) ∷
   re 31 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   rw⁻ 38 (q2 c4) ∷
   rw⁻ 41 (q2 c4) ∷
   re 43 1 (CS03⁻ ∷ []) ∷
   rw⁻ 42 (q23 c4) ∷
   re 44 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 37 1 (CS03 ∷ []) ∷
   rw⁻ 33 (q24 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ []) ∷
   rw 31 (q1 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   rw⁻ 38 (q2 c4) ∷
   rw⁻ 39 (q25 c4) ∷
   rw⁻ 36 (q26 c4) ∷
   rw⁻ 33 (q25 c4) ∷
   rw⁻ 30 (q26 c4) ∷
   rw 33 (q2 c4) ∷
   rw 34 (q2 c4) ∷
   rw 35 (q2 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw 33 (q2 c4) ∷
   rw 34 (q2 c4) ∷
   rw 35 (q2 c4) ∷
   rw 36 (q2 c4) ∷
   re 32 5 (Sb2-0-41-3 ∷ []) ∷
   re 30 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 26 5 (Sb2-0-41-3 ∷ []) ∷
   re 26 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 26 (q3 c4) ∷
   rw 26 (q4 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw 26 (q6 c4) ∷
   rw 25 (q7 c4) ∷
   rw 24 (q6 c4) ∷
   rw⁻ 25 (q5 c4) ∷
   rw 28 (q6 c4) ∷
   rw 27 (q7 c4) ∷
   rw 26 (q6 c4) ∷
   rw⁻ 23 (q4 c4) ∷
   rw 23 (q8 c4) ∷
   re 28 1 (CS03 ∷ []) ∷
   rw⁻ 24 (q9 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   re 30 1 (CS03⁻ ∷ []) ∷
   rw⁻ 27 (q10 c4) ∷
   re 27 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 23 5 (Sb2-0-41-3 ∷ []) ∷
   re 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q2 c4) ∷
   rw 22 (q11 c4) ∷
   rw 22 (q12 c4) ∷
   rw 21 (q13 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw 20 (q11 c4) ∷
   rw 20 (q12 c4) ∷
   rw 24 (q14 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q15 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q16 c4) ∷
   rw⁻ 23 (q17 c4) ∷
   rw 22 (q18 c4) ∷
   rw⁻ 21 (q17 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   re 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 30 (q2 c4) ∷
   rw⁻ 33 (q2 c4) ∷
   re 35 1 (CS03⁻ ∷ []) ∷
   rw⁻ 34 (q19 c4) ∷
   re 36 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 29 1 (CS03 ∷ []) ∷
   rw⁻ 25 (q20 c4) ∷
   re 30 1 (Sb2-0-3-1 ∷ []) ∷
   rw 23 (q1 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 30 (q2 c4) ∷
   rw⁻ 31 (q21 c4) ∷
   rw⁻ 28 (q22 c4) ∷
   rw⁻ 25 (q21 c4) ∷
   rw⁻ 22 (q22 c4) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q2 c4) ∷
   rw 27 (q2 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q2 c4) ∷
   rw 27 (q2 c4) ∷
   rw 28 (q2 c4) ∷
   re 24 5 (Sb2-0-41-3 ∷ []) ∷
   re 22 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q17 c4) ∷
   rw 24 (q18 c4) ∷
   rw⁻ 23 (q17 c4) ∷
   re 27 1 (CS03⁻ ∷ []) ∷
   re 25 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   re 37 1 (CS03⁻ ∷ []) ∷
   rw⁻ 36 (q23 c4) ∷
   re 38 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 31 1 (CS03 ∷ []) ∷
   rw⁻ 27 (q24 c4) ∷
   re 32 1 (Sb2-0-3-1 ∷ []) ∷
   rw 25 (q1 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 33 (q25 c4) ∷
   rw⁻ 30 (q26 c4) ∷
   rw⁻ 27 (q25 c4) ∷
   rw⁻ 24 (q26 c4) ∷
   rw 27 (q2 c4) ∷
   rw 28 (q2 c4) ∷
   rw 29 (q2 c4) ∷
   rw⁻ 26 (q1 c4) ∷ []) Eq.refl
