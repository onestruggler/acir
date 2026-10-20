{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D091 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0393 ; wl0433 ; wl0503 ; wl0505 ; wl0506 ; wl0507 ; wl0508 ; wl0509 ; wl0510 ; wl0511 ; wl0512 ; wl0513 ; wl0514 ; wl0515 ; wl0516 ; wl0517 ; wl0518 ; wl0519 ; wl0520 ; wl0521 ; wl0522 ; wl0523 ; wl0524 ; wl0525 ; wl0526 ; wl0527 ; wl0528 ; wl0529 ; wl0530 ; wl0531 ; wl0532 ; wp0178 ; wp0179 ; wp0180 ; wp0181 ; wp0182 ; wp0183 ; wp0184 ; wp0185 ; wp0186 ; wp0187 ; wp0188 ; wp0189 ; wp0190 ; wp0191 ; wp0192 ; wp0193 ; wp0194 ; wp0195 ; wp0196 ; wp0197 ; wp0198 ; wp0199 ; wp0200 ; wp0201 ; wp0202 ; wp0203 ; wp0204 ; wp0205)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 ; lem-beta-T-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-F5-CS01-at0440 ; lem-SBtgt-at0440 ; lem-X1-beta-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 ; lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CK41⁻ ∷ CK41 ∷ []) [] (wl0505 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CK41 ∷ CK41 ∷ []) (S4⁻ ∷ []) (wl0506 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CK41 ∷ []) (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (wp0178 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (ι1 ∷ []) (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl)
  q5 : Ws → Eqn
  q5 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (ι ∷ []) (wl0507 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CS04⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (S4⁻ ∷ []) (wp0179 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (CS14 ∷ []) (lem-F5-CS01-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Sb2-4-01-3 ∷ []) (Sb2-0-41-3 ∷ []) (lem-SBtgt-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (K1 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (wl0508 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CS04⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0180 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (S0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ []) (wp0181 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CS04⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ []) (wp0182 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CS04⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS04⁻ ∷ []) (wp0183 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CS04⁻ ∷ X0 ∷ CX13 ∷ X0 ∷ []) (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CS04⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0185 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CS04⁻ ∷ X0 ∷ CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ []) (wp0186 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS04⁻ ∷ []) (wp0187 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS04⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS04⁻ ∷ []) (wp0188 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CS04⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0189 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) (wp0190 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) (wl0510 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) (wp0191 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (S0 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0 ∷ []) (wl0511 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0 ∷ []) (wl0512 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CS03⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS03⁻ ∷ []) (wl0513 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Toff314 ∷ CS03 ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) (wp0192 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (X0 ∷ CCZ234 ∷ []) (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑))
  q33 : Ws → Eqn
  q33 c4 = eqn (CK01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ))
  q34 : Ws → Eqn
  q34 c4 = eqn (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) (wl0514 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CS04⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS04⁻ ∷ []) (wp0193 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (wl0515 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CK01 ∷ []) (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (wl0516 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS01 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS01 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CS01 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ []) (wl0518 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS01 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ []) (wl0519 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0520 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (X0 ∷ K1 ∷ []) (K1 ∷ X0 ∷ []) (c₁ (X) (K))
  q46 : Ws → Eqn
  q46 c4 = eqn (K1 ∷ CCZ234 ∷ []) (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS01 ∷ []) (wl0521 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CS01 ∷ X0 ∷ CX43 ∷ X0 ∷ []) (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CS01 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ []) (wl0523 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS01 ∷ X0 ∷ CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ []) (wp0196 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wp0197 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0524 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) (wp0198 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (S0⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) (wl0525 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (S0⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) (wp0199 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (S0⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0⁻ ∷ []) (wl0526 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (S0⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0⁻ ∷ []) (wl0527 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (X0 ∷ ι ∷ []) (ι ∷ X0 ∷ []) zc
  q60 : Ws → Eqn
  q60 c4 = eqn (Sb2-0-41-3 ∷ ι ∷ []) (ι ∷ Sb2-0-41-3 ∷ []) zc
  q61 : Ws → Eqn
  q61 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) (wp0201 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CS03⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ []) (wl0529 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ []) (wp0202 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Toff314 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Toff314 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0204 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03 ∷ []) (wl0531 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (X0 ∷ Bx2-0413 ∷ X0 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ []) (lem-X1-beta-at0210243143 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ []) (wp0205 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (Sb2-0-41-3 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl0503 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (wl0532 (lit c4))

-- F1 CS-K1 [rhs shape] part0: 500 steps
lem-F1-CS-K1-rhs-shape-part0 : Ws → ⟪ (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-rhs-shape-part0 c4 = derive (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 3 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q9 c4) ∷
   rw⁻ 17 (q7 c4) ∷
   rw 18 (q8 c4) ∷
   rw 20 (q8 c4) ∷
   rw 21 (q9 c4) ∷
   rw⁻ 25 (q7 c4) ∷
   rw 26 (q8 c4) ∷
   rw 28 (q8 c4) ∷
   rw 5 (q10 c4) ∷
   rw 4 (q11 c4) ∷
   re 10 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 11 (q12 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw⁻ 17 (q12 c4) ∷
   rw⁻ 20 (q12 c4) ∷
   rw 10 (q13 c4) ∷
   rw⁻ 11 (q12 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw⁻ 17 (q12 c4) ∷
   rw 8 (q14 c4) ∷
   rw 13 (q15 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw⁻ 17 (q12 c4) ∷
   rw⁻ 20 (q12 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw 11 (q16 c4) ∷
   rw 14 (q17 c4) ∷
   rw 17 (q18 c4) ∷
   rw 20 (q17 c4) ∷
   rw 23 (q19 c4) ∷
   rw 13 (q12 c4) ∷
   rw 14 (q12 c4) ∷
   rw 15 (q12 c4) ∷
   rw 16 (q12 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 14 (q14 c4) ∷
   rw 19 (q15 c4) ∷
   rw⁻ 20 (q12 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw 17 (q16 c4) ∷
   rw 20 (q17 c4) ∷
   rw 23 (q18 c4) ∷
   rw 26 (q17 c4) ∷
   rw 29 (q19 c4) ∷
   rw 19 (q12 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q12 c4) ∷
   rw 22 (q12 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw 10 (q12 c4) ∷
   rw 11 (q12 c4) ∷
   rw 12 (q12 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 11 (q20 c4) ∷
   re 16 1 (CS03 ∷ []) ∷
   rw 14 (q21 c4) ∷
   re 15 1 (Sb2-0-3-1 ∷ []) ∷
   rw 17 (q20 c4) ∷
   re 22 1 (CS03⁻ ∷ []) ∷
   rw 20 (q22 c4) ∷
   re 21 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 10 (q12 c4) ∷
   rw 11 (q12 c4) ∷
   rw 12 (q12 c4) ∷
   rw 13 (q12 c4) ∷
   re 9 5 (Sb2-0-41-3 ∷ []) ∷
   re 9 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 13 (q12 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw⁻ 19 (q12 c4) ∷
   rw 9 (q13 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 13 (q12 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw 7 (q23 c4) ∷
   rw 10 (q24 c4) ∷
   rw 13 (q23 c4) ∷
   rw 16 (q24 c4) ∷
   rw 9 (q12 c4) ∷
   rw 10 (q12 c4) ∷
   rw 11 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 10 (q25 c4) ∷
   re 15 1 (CS03 ∷ []) ∷
   rw 13 (q26 c4) ∷
   re 14 1 (Sb2-0-3-1 ∷ []) ∷
   rw 16 (q25 c4) ∷
   re 21 1 (CS03⁻ ∷ []) ∷
   rw 19 (q27 c4) ∷
   re 20 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 9 (q12 c4) ∷
   rw 10 (q12 c4) ∷
   rw 11 (q12 c4) ∷
   rw 12 (q12 c4) ∷
   re 8 5 (Sb2-0-41-3 ∷ []) ∷
   re 12 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 16 1 (CS03⁻ ∷ []) ∷
   rw 16 (q28 c4) ∷
   re 19 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 14 1 (CS03 ∷ []) ∷
   rw 13 (q29 c4) ∷
   re 17 1 (Sb2-0-3-1 ∷ []) ∷
   rw 12 (q30 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw⁻ 16 (q33 c4) ∷
   rw⁻ 17 (q32 c4) ∷
   rw 14 (q34 c4) ∷
   rw⁻ 13 (q32 c4) ∷
   rw⁻ 14 (q33 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw 12 (q34 c4) ∷
   rw⁻ 15 (q31 c4) ∷
   rw 15 (q35 c4) ∷
   re 15 5 (Sb2-0-41-3 ∷ []) ∷
   rw 11 (q36 c4) ∷
   rw 10 (q37 c4) ∷
   rw 16 (q38 c4) ∷
   re 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q12 c4) ∷
   rw⁻ 28 (q12 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 34 (q12 c4) ∷
   rw 24 (q13 c4) ∷
   rw⁻ 25 (q12 c4) ∷
   rw⁻ 28 (q12 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw 22 (q39 c4) ∷
   rw 25 (q40 c4) ∷
   rw 28 (q39 c4) ∷
   rw 31 (q40 c4) ∷
   rw 24 (q12 c4) ∷
   rw 25 (q12 c4) ∷
   rw 26 (q12 c4) ∷
   rw⁻ 23 (q13 c4) ∷
   rw 25 (q41 c4) ∷
   re 30 1 (CS03 ∷ []) ∷
   rw 28 (q42 c4) ∷
   re 29 1 (Sb2-0-3-1 ∷ []) ∷
   rw 31 (q41 c4) ∷
   re 36 1 (CS03⁻ ∷ []) ∷
   rw 34 (q43 c4) ∷
   re 35 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 24 (q12 c4) ∷
   rw 25 (q12 c4) ∷
   rw 26 (q12 c4) ∷
   rw 27 (q12 c4) ∷
   re 23 5 (Sb2-0-41-3 ∷ []) ∷
   re 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q12 c4) ∷
   rw⁻ 27 (q12 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw⁻ 33 (q12 c4) ∷
   rw 23 (q30 c4) ∷
   rw 23 (q31 c4) ∷
   rw⁻ 24 (q12 c4) ∷
   rw⁻ 27 (q12 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw 19 (q44 c4) ∷
   rw⁻ 24 (q45 c4) ∷
   rw 25 (q46 c4) ∷
   rw⁻ 26 (q45 c4) ∷
   rw 25 (q47 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 32 (q12 c4) ∷
   rw⁻ 35 (q12 c4) ∷
   rw 23 (q48 c4) ∷
   rw 26 (q49 c4) ∷
   rw 29 (q50 c4) ∷
   rw 32 (q49 c4) ∷
   rw 35 (q51 c4) ∷
   rw 25 (q12 c4) ∷
   rw 26 (q12 c4) ∷
   rw 27 (q12 c4) ∷
   rw 28 (q12 c4) ∷
   rw⁻ 24 (q47 c4) ∷
   rw⁻ 22 (q45 c4) ∷
   rw 23 (q46 c4) ∷
   rw⁻ 24 (q45 c4) ∷
   rw 25 (q44 c4) ∷
   rw⁻ 30 (q45 c4) ∷
   rw 31 (q46 c4) ∷
   rw⁻ 32 (q45 c4) ∷
   rw 31 (q47 c4) ∷
   rw⁻ 32 (q12 c4) ∷
   rw⁻ 35 (q12 c4) ∷
   rw⁻ 38 (q12 c4) ∷
   rw⁻ 41 (q12 c4) ∷
   rw 29 (q48 c4) ∷
   rw 32 (q49 c4) ∷
   rw 35 (q50 c4) ∷
   rw 38 (q49 c4) ∷
   rw 41 (q51 c4) ∷
   rw 31 (q12 c4) ∷
   rw 32 (q12 c4) ∷
   rw 33 (q12 c4) ∷
   rw 34 (q12 c4) ∷
   rw⁻ 30 (q47 c4) ∷
   rw⁻ 28 (q45 c4) ∷
   rw 29 (q46 c4) ∷
   rw⁻ 30 (q45 c4) ∷
   rw 21 (q12 c4) ∷
   rw 22 (q12 c4) ∷
   rw 23 (q12 c4) ∷
   rw⁻ 20 (q31 c4) ∷
   rw 20 (q35 c4) ∷
   re 29 1 (CS03 ∷ []) ∷
   rw 22 (q52 c4) ∷
   re 26 1 (Sb2-0-3-1 ∷ []) ∷
   re 35 1 (CS03⁻ ∷ []) ∷
   rw 31 (q53 c4) ∷
   re 32 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 21 (q12 c4) ∷
   rw 22 (q12 c4) ∷
   rw 23 (q12 c4) ∷
   rw 24 (q12 c4) ∷
   re 20 5 (Sb2-0-41-3 ∷ []) ∷
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 21 (q12 c4) ∷
   rw⁻ 24 (q12 c4) ∷
   rw⁻ 27 (q12 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw 20 (q13 c4) ∷
   rw⁻ 21 (q12 c4) ∷
   rw⁻ 24 (q12 c4) ∷
   rw⁻ 27 (q12 c4) ∷
   rw 18 (q39 c4) ∷
   rw 21 (q40 c4) ∷
   rw 24 (q39 c4) ∷
   rw 27 (q40 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q12 c4) ∷
   rw 22 (q12 c4) ∷
   rw⁻ 19 (q13 c4) ∷
   rw 21 (q41 c4) ∷
   re 26 1 (CS03 ∷ []) ∷
   rw 24 (q42 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   rw 27 (q41 c4) ∷
   re 32 1 (CS03⁻ ∷ []) ∷
   rw 30 (q43 c4) ∷
   re 31 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q12 c4) ∷
   rw 22 (q12 c4) ∷
   rw 23 (q12 c4) ∷
   re 19 5 (Sb2-0-41-3 ∷ []) ∷
   re 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q12 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw 19 (q13 c4) ∷
   rw⁻ 20 (q12 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw 17 (q54 c4) ∷
   rw 20 (q55 c4) ∷
   rw 23 (q54 c4) ∷
   rw 26 (q55 c4) ∷
   rw 19 (q12 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q12 c4) ∷
   rw⁻ 18 (q13 c4) ∷
   rw 20 (q56 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   rw 23 (q57 c4) ∷
   re 24 1 (Sb2-0-3-1 ∷ []) ∷
   rw 26 (q56 c4) ∷
   re 31 1 (CS03⁻ ∷ []) ∷
   rw 29 (q58 c4) ∷
   re 30 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 19 (q12 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q12 c4) ∷
   rw 22 (q12 c4) ∷
   re 18 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 16 (q59 c4) ∷
   rw⁻ 17 (q60 c4) ∷
   rw⁻ 18 (q59 c4) ∷
   rw⁻ 19 (q38 c4) ∷
   re 15 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 19 1 (CS03⁻ ∷ []) ∷
   re 21 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 22 (q12 c4) ∷
   rw⁻ 25 (q12 c4) ∷
   rw⁻ 28 (q12 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw 21 (q13 c4) ∷
   rw⁻ 22 (q12 c4) ∷
   rw⁻ 25 (q12 c4) ∷
   rw⁻ 28 (q12 c4) ∷
   rw 19 (q61 c4) ∷
   rw 22 (q62 c4) ∷
   rw 25 (q61 c4) ∷
   rw 28 (q62 c4) ∷
   rw 21 (q12 c4) ∷
   rw 22 (q12 c4) ∷
   rw 23 (q12 c4) ∷
   rw⁻ 20 (q13 c4) ∷
   re 27 1 (CS03 ∷ []) ∷
   rw 22 (q63 c4) ∷
   re 26 1 (Sb2-0-3-1 ∷ []) ∷
   re 33 1 (CS03⁻ ∷ []) ∷
   rw 31 (q64 c4) ∷
   re 32 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 21 (q12 c4) ∷
   rw 22 (q12 c4) ∷
   rw 23 (q12 c4) ∷
   rw 24 (q12 c4) ∷
   re 20 5 (Sb2-0-41-3 ∷ []) ∷
   re 22 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 18 (q65 c4) ∷
   rw 19 (q66 c4) ∷
   rw 20 (q65 c4) ∷
   re 17 1 (CS03 ∷ []) ∷
   re 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q12 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw 19 (q13 c4) ∷
   rw⁻ 20 (q12 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw 17 (q67 c4) ∷
   rw 20 (q68 c4) ∷
   rw 23 (q67 c4) ∷
   rw 26 (q68 c4) ∷
   rw 19 (q12 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q12 c4) ∷
   rw⁻ 18 (q13 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   rw 20 (q69 c4) ∷
   re 24 1 (Sb2-0-3-1 ∷ []) ∷
   re 31 1 (CS03⁻ ∷ []) ∷
   rw 29 (q70 c4) ∷
   re 30 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 19 (q12 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q12 c4) ∷
   rw 22 (q12 c4) ∷
   re 18 5 (Sb2-0-41-3 ∷ []) ∷
   re 20 1 (Sb2-0-3-1 ∷ []) ∷
   rw 16 (q65 c4) ∷
   rw 17 (q66 c4) ∷
   rw 18 (q65 c4) ∷
   rw⁻ 15 (q12 c4) ∷
   rw 16 (q71 c4) ∷
   rw 17 (q72 c4) ∷
   rw⁻ 18 (q12 c4) ∷
   rw 19 (q71 c4) ∷
   rw⁻ 15 (q73 c4) ∷
   rw⁻ 18 (q73 c4) ∷
   rw 17 (q74 c4) ∷
   rw⁻ 16 (q73 c4) ∷
   rw 15 (q75 c4) ∷
   re 18 5 (Sb2-0-41-3 ∷ []) ∷
   re 16 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 17 (q12 c4) ∷
   rw⁻ 20 (q12 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw 16 (q13 c4) ∷
   rw⁻ 17 (q12 c4) ∷
   rw⁻ 20 (q12 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw 14 (q14 c4) ∷
   rw 19 (q15 c4) ∷
   rw⁻ 20 (q12 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw 17 (q16 c4) ∷
   rw 20 (q17 c4) ∷
   rw 23 (q18 c4) ∷
   rw 26 (q17 c4) ∷
   rw 29 (q19 c4) ∷
   rw 19 (q12 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q12 c4) ∷
   rw 22 (q12 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw 20 (q14 c4) ∷
   rw 25 (q15 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 32 (q12 c4) ∷
   rw⁻ 35 (q12 c4) ∷
   rw 23 (q16 c4) ∷
   rw 26 (q17 c4) ∷
   rw 29 (q18 c4) ∷
   rw 32 (q17 c4) ∷
   rw 35 (q19 c4) ∷
   rw 25 (q12 c4) ∷
   rw 26 (q12 c4) ∷
   rw 27 (q12 c4) ∷
   rw 28 (q12 c4) ∷
   rw⁻ 24 (q15 c4) ∷
   rw 16 (q12 c4) ∷
   rw 17 (q12 c4) ∷
   rw 18 (q12 c4) ∷
   rw⁻ 15 (q13 c4) ∷
   rw 17 (q20 c4) ∷
   re 22 1 (CS03 ∷ []) ∷
   rw 20 (q21 c4) ∷
   re 21 1 (Sb2-0-3-1 ∷ []) ∷
   rw 23 (q20 c4) ∷
   re 28 1 (CS03⁻ ∷ []) ∷
   rw 26 (q22 c4) ∷
   re 27 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 16 (q12 c4) ∷
   rw 17 (q12 c4) ∷
   rw 18 (q12 c4) ∷
   rw 19 (q12 c4) ∷
   re 15 5 (Sb2-0-41-3 ∷ []) ∷
   re 15 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 16 (q12 c4) ∷
   rw⁻ 19 (q12 c4) ∷
   rw⁻ 22 (q12 c4) ∷
   rw⁻ 25 (q12 c4) ∷
   rw 15 (q13 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw⁻ 19 (q12 c4) ∷
   rw⁻ 22 (q12 c4) ∷
   rw 13 (q23 c4) ∷
   rw 16 (q24 c4) ∷
   rw 19 (q23 c4) ∷
   rw 22 (q24 c4) ∷
   rw 15 (q12 c4) ∷
   rw 16 (q12 c4) ∷
   rw 17 (q12 c4) ∷
   rw⁻ 14 (q13 c4) ∷
   rw 16 (q25 c4) ∷
   re 21 1 (CS03 ∷ []) ∷
   rw 19 (q26 c4) ∷
   re 20 1 (Sb2-0-3-1 ∷ []) ∷
   rw 22 (q25 c4) ∷
   re 27 1 (CS03⁻ ∷ []) ∷
   rw 25 (q27 c4) ∷
   re 26 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 15 (q12 c4) ∷
   rw 16 (q12 c4) ∷
   rw 17 (q12 c4) ∷
   rw 18 (q12 c4) ∷
   re 14 5 (Sb2-0-41-3 ∷ []) ∷
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 24 1 (CS03⁻ ∷ []) ∷
   rw 24 (q28 c4) ∷
   re 27 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 22 1 (CS03 ∷ []) ∷
   rw 21 (q29 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   rw 20 (q30 c4) ∷
   rw 20 (q31 c4) ∷
   rw⁻ 23 (q32 c4) ∷
   rw⁻ 24 (q33 c4) ∷
   rw⁻ 25 (q32 c4) ∷
   rw 22 (q34 c4) ∷
   rw⁻ 21 (q32 c4) ∷
   rw⁻ 22 (q33 c4) ∷
   rw⁻ 23 (q32 c4) ∷
   rw 20 (q34 c4) ∷
   rw⁻ 23 (q31 c4) ∷
   rw 23 (q35 c4) ∷
   re 23 5 (Sb2-0-41-3 ∷ []) ∷
   rw 19 (q76 c4) ∷
   re 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 22 1 (CS03⁻ ∷ []) ∷
   rw 22 (q28 c4) ∷
   re 25 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 20 1 (CS03 ∷ []) ∷
   rw 19 (q29 c4) ∷
   re 23 1 (Sb2-0-3-1 ∷ []) ∷
   rw 18 (q30 c4) ∷
   rw 18 (q31 c4) ∷
   rw⁻ 21 (q32 c4) ∷
   rw⁻ 22 (q33 c4) ∷
   rw⁻ 23 (q32 c4) ∷
   rw 20 (q34 c4) ∷
   rw⁻ 19 (q32 c4) ∷
   rw⁻ 20 (q33 c4) ∷
   rw⁻ 21 (q32 c4) ∷
   rw 18 (q34 c4) ∷
   rw⁻ 21 (q31 c4) ∷
   rw 21 (q35 c4) ∷ []) Eq.refl
