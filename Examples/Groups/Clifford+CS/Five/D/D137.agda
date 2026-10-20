{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D137 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0393 ; wl0503 ; wl0509 ; wl0513 ; wl0514 ; wl0516 ; wl0517 ; wl0518 ; wl0519 ; wl0520 ; wl0521 ; wl0522 ; wl0523 ; wl0524 ; wl0525 ; wl0526 ; wl0527 ; wl0528 ; wl0529 ; wl0530 ; wl0531 ; wl0532 ; wl0576 ; wl0577 ; wp0192 ; wp0194 ; wp0195 ; wp0196 ; wp0197 ; wp0198 ; wp0199 ; wp0200 ; wp0201 ; wp0202 ; wp0203 ; wp0204 ; wp0205 ; wp0238 ; wp0239 ; wp0240 ; wp0241 ; wp0242 ; wp0243)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 ; lem-beta-T-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-X1-beta-at0210243143 ; lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04233240 ; lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04233240 ; lem-auto-CSd01-∣-BOX⟨2·0134⟩-at143143 ; lem-auto-S0-∣-BOX⟨1·0234⟩-at12243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) (wl0514 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (X0 ∷ CCZ234 ∷ []) (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑))
  q6 : Ws → Eqn
  q6 c4 = eqn (CK01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ))
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Toff314 ∷ CS03 ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) (wp0192 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CS03⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS03⁻ ∷ []) (wl0513 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (X0 ∷ Bx2-0413 ∷ X0 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ []) (lem-X1-beta-at0210243143 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ134 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ134 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04233240 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ []) (wp0205 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ134 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ134 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04233240 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl0503 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ []) (wp0202 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Sb2-0-41-3 ∷ Toff314 ∷ []) (Toff314 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03 ∷ []) (wl0531 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0204 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
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
  q37 : Ws → Eqn
  q37 c4 = eqn (CK01 ∷ []) (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (wl0516 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (X0 ∷ ι ∷ []) (ι ∷ X0 ∷ []) (zc)
  q39 : Ws → Eqn
  q39 c4 = eqn (Sb2-0-41-3 ∷ ι ∷ []) (ι ∷ Sb2-0-41-3 ∷ []) (zc)
  q40 : Ws → Eqn
  q40 c4 = eqn (S0⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0⁻ ∷ []) (wl0527 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (S0⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) (wp0199 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (S0⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0⁻ ∷ []) (wl0526 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (S0⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) (wl0525 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) (wp0198 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CS01 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ []) (wl0519 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CS01 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ []) (wl0518 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CS01 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CS01 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0524 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wp0197 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (X0 ∷ K1 ∷ []) (K1 ∷ X0 ∷ []) (c₁ (X) (K))
  q53 : Ws → Eqn
  q53 c4 = eqn (K1 ∷ CCZ234 ∷ []) (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ))
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CS01 ∷ X0 ∷ CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ []) (wp0196 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CS01 ∷ X0 ∷ CX43 ∷ X0 ∷ []) (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CS01 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ []) (wl0523 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS01 ∷ []) (wl0521 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0520 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (wl0532 (lit c4))

-- F1 CS-K1 part13: 392 steps
lem-F1-CS-K1-part13 : Ws → ⟪ (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ
lem-F1-CS-K1-part13 c4 = derive (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  (rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   re 21 5 (Sb2-0-41-3 ∷ []) ∷
   re 19 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 15 5 (Sb2-0-41-3 ∷ []) ∷
   re 15 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 15 (q2 c4) ∷
   rw 15 (q3 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw 15 (q5 c4) ∷
   rw 14 (q6 c4) ∷
   rw 13 (q5 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw 17 (q5 c4) ∷
   rw 16 (q6 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 12 (q3 c4) ∷
   rw 12 (q7 c4) ∷
   re 17 1 (CS03 ∷ []) ∷
   rw⁻ 13 (q8 c4) ∷
   re 14 1 (Sb2-0-3-1 ∷ []) ∷
   re 19 1 (CS03⁻ ∷ []) ∷
   rw⁻ 16 (q9 c4) ∷
   re 16 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 12 5 (Sb2-0-41-3 ∷ []) ∷
   re 12 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 13 (q1 c4) ∷
   rw 11 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 10 (q12 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw 9 (q10 c4) ∷
   rw 9 (q11 c4) ∷
   rw 13 (q13 c4) ∷
   rw 10 (q13 c4) ∷
   rw 11 (q14 c4) ∷
   rw 12 (q13 c4) ∷
   rw 13 (q15 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw 11 (q17 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   re 14 1 (CS03 ∷ []) ∷
   re 12 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 13 (q1 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   re 24 1 (CS03⁻ ∷ []) ∷
   rw⁻ 23 (q18 c4) ∷
   re 25 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 18 1 (CS03 ∷ []) ∷
   rw⁻ 14 (q19 c4) ∷
   re 19 1 (Sb2-0-3-1 ∷ []) ∷
   rw 12 (q20 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 20 (q21 c4) ∷
   rw⁻ 17 (q22 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw⁻ 11 (q22 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw⁻ 13 (q20 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   re 13 5 (Sb2-0-41-3 ∷ []) ∷
   re 11 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 14 (q16 c4) ∷
   rw 13 (q17 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   re 16 1 (CS03⁻ ∷ []) ∷
   re 14 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   re 26 1 (CS03⁻ ∷ []) ∷
   rw⁻ 25 (q23 c4) ∷
   re 27 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 20 1 (CS03 ∷ []) ∷
   rw⁻ 16 (q24 c4) ∷
   re 21 1 (Sb2-0-3-1 ∷ []) ∷
   rw 14 (q20 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 22 (q25 c4) ∷
   rw⁻ 19 (q26 c4) ∷
   rw⁻ 16 (q25 c4) ∷
   rw⁻ 13 (q26 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw⁻ 15 (q20 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   re 15 5 (Sb2-0-41-3 ∷ []) ∷
   re 13 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 9 5 (Sb2-0-41-3 ∷ []) ∷
   re 9 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   rw 8 (q10 c4) ∷
   rw 8 (q11 c4) ∷
   rw 7 (q27 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw 6 (q10 c4) ∷
   rw 6 (q11 c4) ∷
   rw 10 (q13 c4) ∷
   rw 7 (q28 c4) ∷
   rw 10 (q15 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   re 11 1 (CS03 ∷ []) ∷
   rw⁻ 8 (q30 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 9 (q29 c4) ∷
   re 13 1 (CS03⁻ ∷ []) ∷
   rw⁻ 10 (q31 c4) ∷
   re 10 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   re 6 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   rw 5 (q10 c4) ∷
   rw 5 (q11 c4) ∷
   rw 4 (q32 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 3 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 7 (q13 c4) ∷
   rw 4 (q33 c4) ∷
   rw 7 (q15 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   re 8 1 (CS03 ∷ []) ∷
   rw⁻ 5 (q35 c4) ∷
   re 5 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 6 (q34 c4) ∷
   re 10 1 (CS03⁻ ∷ []) ∷
   rw⁻ 7 (q36 c4) ∷
   re 7 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   rw 25 (q37 c4) ∷
   rw 24 (q38 c4) ∷
   rw 23 (q39 c4) ∷
   rw 22 (q38 c4) ∷
   re 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   re 36 1 (CS03⁻ ∷ []) ∷
   rw⁻ 35 (q40 c4) ∷
   re 37 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q41 c4) ∷
   re 30 1 (CS03 ∷ []) ∷
   rw⁻ 29 (q42 c4) ∷
   re 31 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q41 c4) ∷
   rw 24 (q20 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 32 (q43 c4) ∷
   rw⁻ 29 (q44 c4) ∷
   rw⁻ 26 (q43 c4) ∷
   rw⁻ 23 (q44 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw⁻ 25 (q20 c4) ∷
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
   rw⁻ 36 (q45 c4) ∷
   re 38 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 33 (q46 c4) ∷
   re 31 1 (CS03 ∷ []) ∷
   rw⁻ 30 (q47 c4) ∷
   re 32 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 27 (q46 c4) ∷
   rw 25 (q20 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 33 (q48 c4) ∷
   rw⁻ 30 (q49 c4) ∷
   rw⁻ 27 (q48 c4) ∷
   rw⁻ 24 (q49 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw⁻ 26 (q20 c4) ∷
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
   re 38 1 (CS03⁻ ∷ []) ∷
   rw⁻ 37 (q50 c4) ∷
   re 41 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 32 1 (CS03 ∷ []) ∷
   rw⁻ 28 (q51 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ []) ∷
   rw 26 (q2 c4) ∷
   rw 26 (q3 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw 36 (q52 c4) ∷
   rw⁻ 35 (q53 c4) ∷
   rw 34 (q52 c4) ∷
   rw 36 (q54 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw⁻ 46 (q1 c4) ∷
   rw⁻ 47 (q55 c4) ∷
   rw⁻ 44 (q56 c4) ∷
   rw⁻ 41 (q57 c4) ∷
   rw⁻ 38 (q56 c4) ∷
   rw⁻ 35 (q58 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   rw⁻ 37 (q54 c4) ∷
   rw 38 (q52 c4) ∷
   rw⁻ 37 (q53 c4) ∷
   rw 36 (q52 c4) ∷
   rw⁻ 31 (q59 c4) ∷
   rw 30 (q52 c4) ∷
   rw⁻ 29 (q53 c4) ∷
   rw 28 (q52 c4) ∷
   rw 30 (q54 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 41 (q55 c4) ∷
   rw⁻ 38 (q56 c4) ∷
   rw⁻ 35 (q57 c4) ∷
   rw⁻ 32 (q56 c4) ∷
   rw⁻ 29 (q58 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw⁻ 31 (q54 c4) ∷
   rw 32 (q52 c4) ∷
   rw⁻ 31 (q53 c4) ∷
   rw 30 (q52 c4) ∷
   rw⁻ 25 (q59 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw 29 (q7 c4) ∷
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
   rw⁻ 40 (q45 c4) ∷
   re 42 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 37 (q46 c4) ∷
   re 35 1 (CS03 ∷ []) ∷
   rw⁻ 34 (q47 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q46 c4) ∷
   rw 29 (q20 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 37 (q48 c4) ∷
   rw⁻ 34 (q49 c4) ∷
   rw⁻ 31 (q48 c4) ∷
   rw⁻ 28 (q49 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw⁻ 30 (q20 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   re 30 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 22 (q37 c4) ∷
   rw⁻ 19 (q60 c4) ∷
   rw 19 (q37 c4) ∷
   rw 18 (q38 c4) ∷
   rw 17 (q39 c4) ∷
   rw 16 (q38 c4) ∷
   re 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   re 30 1 (CS03⁻ ∷ []) ∷
   rw⁻ 29 (q40 c4) ∷
   re 31 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q41 c4) ∷
   re 24 1 (CS03 ∷ []) ∷
   rw⁻ 23 (q42 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q41 c4) ∷
   rw 18 (q20 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 26 (q43 c4) ∷
   rw⁻ 23 (q44 c4) ∷
   rw⁻ 20 (q43 c4) ∷
   rw⁻ 17 (q44 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw⁻ 19 (q20 c4) ∷
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
   rw⁻ 30 (q45 c4) ∷
   re 32 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 27 (q46 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   rw⁻ 24 (q47 c4) ∷
   re 26 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 21 (q46 c4) ∷
   rw 19 (q20 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 27 (q48 c4) ∷
   rw⁻ 24 (q49 c4) ∷
   rw⁻ 21 (q48 c4) ∷
   rw⁻ 18 (q49 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw⁻ 20 (q20 c4) ∷
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
   re 32 1 (CS03⁻ ∷ []) ∷
   rw⁻ 31 (q50 c4) ∷
   re 35 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 26 1 (CS03 ∷ []) ∷
   rw⁻ 22 (q51 c4) ∷
   re 29 1 (Sb2-0-3-1 ∷ []) ∷
   rw 20 (q2 c4) ∷
   rw 20 (q3 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷ []) Eq.refl
