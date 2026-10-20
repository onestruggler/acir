{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D092 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0393 ; wl0433 ; wl0503 ; wl0509 ; wl0515 ; wl0516 ; wl0517 ; wl0518 ; wl0519 ; wl0520 ; wl0521 ; wl0522 ; wl0523 ; wl0524 ; wl0525 ; wl0526 ; wl0527 ; wl0528 ; wl0529 ; wl0530 ; wl0531 ; wp0182 ; wp0193 ; wp0194 ; wp0195 ; wp0196 ; wp0197 ; wp0198 ; wp0199 ; wp0200 ; wp0201 ; wp0202 ; wp0203 ; wp0204 ; wp0205)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 ; lem-beta-T-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-X1-beta-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 ; lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CS04⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS04⁻ ∷ []) (wp0193 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (wl0515 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CK01 ∷ []) (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (wl0516 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CS01 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CS01 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CS01 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ []) (wl0518 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CS01 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ []) (wl0519 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0520 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (X0 ∷ K1 ∷ []) (K1 ∷ X0 ∷ []) (c₁ (X) (K))
  q15 : Ws → Eqn
  q15 c4 = eqn (K1 ∷ CCZ234 ∷ []) (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ))
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS01 ∷ []) (wl0521 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS01 ∷ X0 ∷ CX43 ∷ X0 ∷ []) (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS01 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ []) (wl0523 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS01 ∷ X0 ∷ CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ []) (wp0196 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wp0197 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0524 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) (wp0198 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (S0⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) (wl0525 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (S0⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) (wp0199 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (S0⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0⁻ ∷ []) (wl0526 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (S0⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0⁻ ∷ []) (wl0527 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (X0 ∷ ι ∷ []) (ι ∷ X0 ∷ []) zc
  q30 : Ws → Eqn
  q30 c4 = eqn (Sb2-0-41-3 ∷ ι ∷ []) (ι ∷ Sb2-0-41-3 ∷ []) zc
  q31 : Ws → Eqn
  q31 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) (wp0201 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CS03⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ []) (wl0529 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ []) (wp0202 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Toff314 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Toff314 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0204 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03 ∷ []) (wl0531 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (X0 ∷ Bx2-0413 ∷ X0 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ []) (lem-X1-beta-at0210243143 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ []) (wp0205 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Sb2-0-41-3 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl0503 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CS04⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ []) (wp0182 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))

-- F1 CS-K1 [rhs shape] part1: 500 steps
lem-F1-CS-K1-rhs-shape-part1 : Ws → ⟪ (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-rhs-shape-part1 c4 = derive (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (re 21 5 (Sb2-0-41-3 ∷ []) ∷
   rw 17 (q1 c4) ∷
   rw 16 (q2 c4) ∷
   rw 24 (q3 c4) ∷
   re 32 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw⁻ 42 (q4 c4) ∷
   rw 32 (q5 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw 30 (q6 c4) ∷
   rw 33 (q7 c4) ∷
   rw 36 (q6 c4) ∷
   rw 39 (q7 c4) ∷
   rw 32 (q4 c4) ∷
   rw 33 (q4 c4) ∷
   rw 34 (q4 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw 33 (q8 c4) ∷
   re 38 1 (CS03 ∷ []) ∷
   rw 36 (q9 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ []) ∷
   rw 39 (q8 c4) ∷
   re 44 1 (CS03⁻ ∷ []) ∷
   rw 42 (q10 c4) ∷
   re 43 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 32 (q4 c4) ∷
   rw 33 (q4 c4) ∷
   rw 34 (q4 c4) ∷
   rw 35 (q4 c4) ∷
   re 31 5 (Sb2-0-41-3 ∷ []) ∷
   re 31 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw⁻ 41 (q4 c4) ∷
   rw 31 (q11 c4) ∷
   rw 31 (q12 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw 27 (q13 c4) ∷
   rw⁻ 32 (q14 c4) ∷
   rw 33 (q15 c4) ∷
   rw⁻ 34 (q14 c4) ∷
   rw 33 (q16 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 37 (q4 c4) ∷
   rw⁻ 40 (q4 c4) ∷
   rw⁻ 43 (q4 c4) ∷
   rw 31 (q17 c4) ∷
   rw 34 (q18 c4) ∷
   rw 37 (q19 c4) ∷
   rw 40 (q18 c4) ∷
   rw 43 (q20 c4) ∷
   rw 33 (q4 c4) ∷
   rw 34 (q4 c4) ∷
   rw 35 (q4 c4) ∷
   rw 36 (q4 c4) ∷
   rw⁻ 32 (q16 c4) ∷
   rw⁻ 30 (q14 c4) ∷
   rw 31 (q15 c4) ∷
   rw⁻ 32 (q14 c4) ∷
   rw 33 (q13 c4) ∷
   rw⁻ 38 (q14 c4) ∷
   rw 39 (q15 c4) ∷
   rw⁻ 40 (q14 c4) ∷
   rw 39 (q16 c4) ∷
   rw⁻ 40 (q4 c4) ∷
   rw⁻ 43 (q4 c4) ∷
   rw⁻ 46 (q4 c4) ∷
   rw⁻ 49 (q4 c4) ∷
   rw 37 (q17 c4) ∷
   rw 40 (q18 c4) ∷
   rw 43 (q19 c4) ∷
   rw 46 (q18 c4) ∷
   rw 49 (q20 c4) ∷
   rw 39 (q4 c4) ∷
   rw 40 (q4 c4) ∷
   rw 41 (q4 c4) ∷
   rw 42 (q4 c4) ∷
   rw⁻ 38 (q16 c4) ∷
   rw⁻ 36 (q14 c4) ∷
   rw 37 (q15 c4) ∷
   rw⁻ 38 (q14 c4) ∷
   rw 29 (q4 c4) ∷
   rw 30 (q4 c4) ∷
   rw 31 (q4 c4) ∷
   rw⁻ 28 (q12 c4) ∷
   rw 28 (q21 c4) ∷
   re 37 1 (CS03 ∷ []) ∷
   rw 30 (q22 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ []) ∷
   re 43 1 (CS03⁻ ∷ []) ∷
   rw 39 (q23 c4) ∷
   re 40 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 29 (q4 c4) ∷
   rw 30 (q4 c4) ∷
   rw 31 (q4 c4) ∷
   rw 32 (q4 c4) ∷
   re 28 5 (Sb2-0-41-3 ∷ []) ∷
   re 28 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw 28 (q5 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw 26 (q6 c4) ∷
   rw 29 (q7 c4) ∷
   rw 32 (q6 c4) ∷
   rw 35 (q7 c4) ∷
   rw 28 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   rw 30 (q4 c4) ∷
   rw⁻ 27 (q5 c4) ∷
   rw 29 (q8 c4) ∷
   re 34 1 (CS03 ∷ []) ∷
   rw 32 (q9 c4) ∷
   re 33 1 (Sb2-0-3-1 ∷ []) ∷
   rw 35 (q8 c4) ∷
   re 40 1 (CS03⁻ ∷ []) ∷
   rw 38 (q10 c4) ∷
   re 39 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 28 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   rw 30 (q4 c4) ∷
   rw 31 (q4 c4) ∷
   re 27 5 (Sb2-0-41-3 ∷ []) ∷
   re 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 37 (q4 c4) ∷
   rw 27 (q5 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw 25 (q24 c4) ∷
   rw 28 (q25 c4) ∷
   rw 31 (q24 c4) ∷
   rw 34 (q25 c4) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   rw 28 (q26 c4) ∷
   re 33 1 (CS03 ∷ []) ∷
   rw 31 (q27 c4) ∷
   re 32 1 (Sb2-0-3-1 ∷ []) ∷
   rw 34 (q26 c4) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   rw 37 (q28 c4) ∷
   re 38 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   rw 30 (q4 c4) ∷
   re 26 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 24 (q29 c4) ∷
   rw⁻ 25 (q30 c4) ∷
   rw⁻ 26 (q29 c4) ∷
   rw⁻ 27 (q3 c4) ∷
   re 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 27 1 (CS03⁻ ∷ []) ∷
   re 29 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw 29 (q5 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw 27 (q31 c4) ∷
   rw 30 (q32 c4) ∷
   rw 33 (q31 c4) ∷
   rw 36 (q32 c4) ∷
   rw 29 (q4 c4) ∷
   rw 30 (q4 c4) ∷
   rw 31 (q4 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   re 35 1 (CS03 ∷ []) ∷
   rw 30 (q33 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ []) ∷
   re 41 1 (CS03⁻ ∷ []) ∷
   rw 39 (q34 c4) ∷
   re 40 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 29 (q4 c4) ∷
   rw 30 (q4 c4) ∷
   rw 31 (q4 c4) ∷
   rw 32 (q4 c4) ∷
   re 28 5 (Sb2-0-41-3 ∷ []) ∷
   re 30 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 26 (q35 c4) ∷
   rw 27 (q36 c4) ∷
   rw 28 (q35 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   re 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 37 (q4 c4) ∷
   rw 27 (q5 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw 25 (q37 c4) ∷
   rw 28 (q38 c4) ∷
   rw 31 (q37 c4) ∷
   rw 34 (q38 c4) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   re 33 1 (CS03 ∷ []) ∷
   rw 28 (q39 c4) ∷
   re 32 1 (Sb2-0-3-1 ∷ []) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   rw 37 (q40 c4) ∷
   re 38 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   rw 30 (q4 c4) ∷
   re 26 5 (Sb2-0-41-3 ∷ []) ∷
   re 28 1 (Sb2-0-3-1 ∷ []) ∷
   rw 24 (q35 c4) ∷
   rw 25 (q36 c4) ∷
   rw 26 (q35 c4) ∷
   rw⁻ 23 (q4 c4) ∷
   rw 24 (q41 c4) ∷
   rw 25 (q42 c4) ∷
   rw⁻ 26 (q4 c4) ∷
   rw 27 (q41 c4) ∷
   rw⁻ 23 (q43 c4) ∷
   rw⁻ 26 (q43 c4) ∷
   rw 25 (q44 c4) ∷
   rw⁻ 24 (q43 c4) ∷
   rw 23 (q45 c4) ∷
   re 26 5 (Sb2-0-41-3 ∷ []) ∷
   rw 22 (q3 c4) ∷
   re 30 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 37 (q4 c4) ∷
   rw⁻ 40 (q4 c4) ∷
   rw 30 (q5 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 37 (q4 c4) ∷
   rw 28 (q6 c4) ∷
   rw 31 (q7 c4) ∷
   rw 34 (q6 c4) ∷
   rw 37 (q7 c4) ∷
   rw 30 (q4 c4) ∷
   rw 31 (q4 c4) ∷
   rw 32 (q4 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw 31 (q8 c4) ∷
   re 36 1 (CS03 ∷ []) ∷
   rw 34 (q9 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ []) ∷
   rw 37 (q8 c4) ∷
   re 42 1 (CS03⁻ ∷ []) ∷
   rw 40 (q10 c4) ∷
   re 41 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 30 (q4 c4) ∷
   rw 31 (q4 c4) ∷
   rw 32 (q4 c4) ∷
   rw 33 (q4 c4) ∷
   re 29 5 (Sb2-0-41-3 ∷ []) ∷
   re 29 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw 29 (q11 c4) ∷
   rw 29 (q12 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw 25 (q13 c4) ∷
   rw⁻ 30 (q14 c4) ∷
   rw 31 (q15 c4) ∷
   rw⁻ 32 (q14 c4) ∷
   rw 31 (q16 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw⁻ 41 (q4 c4) ∷
   rw 29 (q17 c4) ∷
   rw 32 (q18 c4) ∷
   rw 35 (q19 c4) ∷
   rw 38 (q18 c4) ∷
   rw 41 (q20 c4) ∷
   rw 31 (q4 c4) ∷
   rw 32 (q4 c4) ∷
   rw 33 (q4 c4) ∷
   rw 34 (q4 c4) ∷
   rw⁻ 30 (q16 c4) ∷
   rw⁻ 28 (q14 c4) ∷
   rw 29 (q15 c4) ∷
   rw⁻ 30 (q14 c4) ∷
   rw 31 (q13 c4) ∷
   rw⁻ 36 (q14 c4) ∷
   rw 37 (q15 c4) ∷
   rw⁻ 38 (q14 c4) ∷
   rw 37 (q16 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw⁻ 41 (q4 c4) ∷
   rw⁻ 44 (q4 c4) ∷
   rw⁻ 47 (q4 c4) ∷
   rw 35 (q17 c4) ∷
   rw 38 (q18 c4) ∷
   rw 41 (q19 c4) ∷
   rw 44 (q18 c4) ∷
   rw 47 (q20 c4) ∷
   rw 37 (q4 c4) ∷
   rw 38 (q4 c4) ∷
   rw 39 (q4 c4) ∷
   rw 40 (q4 c4) ∷
   rw⁻ 36 (q16 c4) ∷
   rw⁻ 34 (q14 c4) ∷
   rw 35 (q15 c4) ∷
   rw⁻ 36 (q14 c4) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw 26 (q21 c4) ∷
   re 35 1 (CS03 ∷ []) ∷
   rw 28 (q22 c4) ∷
   re 32 1 (Sb2-0-3-1 ∷ []) ∷
   re 41 1 (CS03⁻ ∷ []) ∷
   rw 37 (q23 c4) ∷
   re 38 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   rw 30 (q4 c4) ∷
   re 26 5 (Sb2-0-41-3 ∷ []) ∷
   re 26 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 27 (q4 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw 26 (q5 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw 24 (q6 c4) ∷
   rw 27 (q7 c4) ∷
   rw 30 (q6 c4) ∷
   rw 33 (q7 c4) ∷
   rw 26 (q4 c4) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   rw⁻ 25 (q5 c4) ∷
   rw 27 (q8 c4) ∷
   re 32 1 (CS03 ∷ []) ∷
   rw 30 (q9 c4) ∷
   re 31 1 (Sb2-0-3-1 ∷ []) ∷
   rw 33 (q8 c4) ∷
   re 38 1 (CS03⁻ ∷ []) ∷
   rw 36 (q10 c4) ∷
   re 37 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 26 (q4 c4) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   re 25 5 (Sb2-0-41-3 ∷ []) ∷
   re 25 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q4 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw 25 (q5 c4) ∷
   rw⁻ 26 (q4 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw 23 (q24 c4) ∷
   rw 26 (q25 c4) ∷
   rw 29 (q24 c4) ∷
   rw 32 (q25 c4) ∷
   rw 25 (q4 c4) ∷
   rw 26 (q4 c4) ∷
   rw 27 (q4 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 26 (q26 c4) ∷
   re 31 1 (CS03 ∷ []) ∷
   rw 29 (q27 c4) ∷
   re 30 1 (Sb2-0-3-1 ∷ []) ∷
   rw 32 (q26 c4) ∷
   re 37 1 (CS03⁻ ∷ []) ∷
   rw 35 (q28 c4) ∷
   re 36 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 25 (q4 c4) ∷
   rw 26 (q4 c4) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   re 24 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 22 (q29 c4) ∷
   rw⁻ 23 (q30 c4) ∷
   rw⁻ 24 (q29 c4) ∷
   rw⁻ 25 (q3 c4) ∷
   re 21 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 25 1 (CS03⁻ ∷ []) ∷
   re 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 37 (q4 c4) ∷
   rw 27 (q5 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw 25 (q31 c4) ∷
   rw 28 (q32 c4) ∷
   rw 31 (q31 c4) ∷
   rw 34 (q32 c4) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   re 33 1 (CS03 ∷ []) ∷
   rw 28 (q33 c4) ∷
   re 32 1 (Sb2-0-3-1 ∷ []) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   rw 37 (q34 c4) ∷
   re 38 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   rw 30 (q4 c4) ∷
   re 26 5 (Sb2-0-41-3 ∷ []) ∷
   re 28 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 24 (q35 c4) ∷
   rw 25 (q36 c4) ∷
   rw 26 (q35 c4) ∷
   re 23 1 (CS03 ∷ []) ∷
   re 25 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q4 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw 25 (q5 c4) ∷
   rw⁻ 26 (q4 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw 23 (q37 c4) ∷
   rw 26 (q38 c4) ∷
   rw 29 (q37 c4) ∷
   rw 32 (q38 c4) ∷
   rw 25 (q4 c4) ∷
   rw 26 (q4 c4) ∷
   rw 27 (q4 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   re 31 1 (CS03 ∷ []) ∷
   rw 26 (q39 c4) ∷
   re 30 1 (Sb2-0-3-1 ∷ []) ∷
   re 37 1 (CS03⁻ ∷ []) ∷
   rw 35 (q40 c4) ∷
   re 36 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 25 (q4 c4) ∷
   rw 26 (q4 c4) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   re 24 5 (Sb2-0-41-3 ∷ []) ∷
   re 26 1 (Sb2-0-3-1 ∷ []) ∷
   rw 22 (q35 c4) ∷
   rw 23 (q36 c4) ∷
   rw 24 (q35 c4) ∷
   rw⁻ 21 (q4 c4) ∷
   rw 22 (q41 c4) ∷
   rw 23 (q42 c4) ∷
   rw⁻ 24 (q4 c4) ∷
   rw 25 (q41 c4) ∷
   rw⁻ 21 (q43 c4) ∷
   rw⁻ 24 (q43 c4) ∷
   rw 23 (q44 c4) ∷
   rw⁻ 22 (q43 c4) ∷
   rw 21 (q45 c4) ∷
   re 24 5 (Sb2-0-41-3 ∷ []) ∷
   re 22 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q4 c4) ∷
   rw⁻ 26 (q4 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw 22 (q5 c4) ∷
   rw⁻ 23 (q4 c4) ∷
   rw⁻ 26 (q4 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw 20 (q46 c4) ∷
   rw 25 (q47 c4) ∷ []) Eq.refl
