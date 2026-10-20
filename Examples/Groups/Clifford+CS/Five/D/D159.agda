{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D159 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0393 ; wl0503 ; wl0509 ; wl0516 ; wl0517 ; wl0518 ; wl0519 ; wl0520 ; wl0521 ; wl0522 ; wl0523 ; wl0524 ; wl0525 ; wl0526 ; wl0527 ; wl0528 ; wl0529 ; wl0530 ; wl0531 ; wl0548 ; wl0551 ; wl0558 ; wl0563 ; wl0571 ; wl0572 ; wl0579 ; wl0580 ; wl0581 ; wl0583 ; wp0194 ; wp0195 ; wp0196 ; wp0197 ; wp0198 ; wp0199 ; wp0200 ; wp0201 ; wp0202 ; wp0203 ; wp0204 ; wp0205 ; wp0247 ; wp0258 ; wp0259)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-auto-CCZ012-∣-CCZ314-at122331)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-X1-beta-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 ; lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 ; lem-beta-T-at03103441 ; lem-sym23-at03103441 ; lem-sym34-at0310243241)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CX20-CCZ134)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X0 ∷ K2⁻ ∷ []) (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑))
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl0581 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (X0 ∷ CS23 ∷ []) (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑))
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ134 ∷ CS23 ∷ []) (CS23 ∷ CCZ134 ∷ []) (wl0558 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CX20 ∷ X0 ∷ []) (X0 ∷ CX20 ∷ []) (wl0583 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CX20 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ X0 ∷ CS03⁻ ∷ []) (wp0247 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CS03 ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ X0 ∷ CS03 ∷ []) (wp0258 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X0 ∷ K2 ∷ []) (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑))
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ134 ∷ K2 ∷ []) (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl0563 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (K2 ∷ K2⁻ ∷ []) [] (wl0579 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ023 ∷ []) (K2⁻ ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ []) (wl0580 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ124 ∷ []) (K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ X0 ∷ CCZ124 ∷ X0 ∷ X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ []) (wp0259 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at122331 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Toff203 ∷ X0 ∷ CS02 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ X0 ∷ Toff203 ∷ []) (wl0572 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Toff203 ∷ X0 ∷ CS02⁻ ∷ X0 ∷ []) (X0 ∷ CS02⁻ ∷ X0 ∷ Toff203 ∷ []) (wl0571 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ []) (wp0202 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Toff314 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Toff314 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) (wp0201 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CS03⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ []) (wl0529 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0204 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03 ∷ []) (wl0531 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (X0 ∷ Bx2-0413 ∷ X0 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ []) (lem-X1-beta-at0210243143 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ []) (wp0205 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (Sb2-0-41-3 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl0503 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CK01 ∷ []) (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (wl0516 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CS01 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CS01 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CS01 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ []) (wl0518 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CS01 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ []) (wl0519 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0520 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (X0 ∷ K1 ∷ []) (K1 ∷ X0 ∷ []) (c₁ (X) (K))
  q54 : Ws → Eqn
  q54 c4 = eqn (K1 ∷ CCZ234 ∷ []) (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ))
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS01 ∷ []) (wl0521 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CS01 ∷ X0 ∷ CX43 ∷ X0 ∷ []) (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CS01 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ []) (wl0523 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CS01 ∷ X0 ∷ CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ []) (wp0196 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wp0197 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0524 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) (wp0198 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (S0⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) (wl0525 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (S0⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) (wp0199 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (S0⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0⁻ ∷ []) (wl0526 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (S0⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0⁻ ∷ []) (wl0527 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (X0 ∷ ι ∷ []) (ι ∷ X0 ∷ []) zc
  q69 : Ws → Eqn
  q69 c4 = eqn (Sb2-0-41-3 ∷ ι ∷ []) (ι ∷ Sb2-0-41-3 ∷ []) zc

-- F1 CS-K1 part35: 500 steps
lem-F1-CS-K1-part35 : Ws → ⟪ (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CCZ023 ∷ X0 ∷ CCZ134 ∷ K2⁻ ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-part35 c4 = derive (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CCZ023 ∷ X0 ∷ CCZ134 ∷ K2⁻ ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 26 (q1 c4) ∷
   rw 23 (q2 c4) ∷
   rw⁻ 27 (q3 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw 26 (q5 c4) ∷
   rw 27 (q6 c4) ∷
   rw 28 (q5 c4) ∷
   rw 25 (q7 c4) ∷
   rw 24 (q5 c4) ∷
   rw 25 (q6 c4) ∷
   rw 26 (q5 c4) ∷
   rw 23 (q8 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 24 (q9 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q11 c4) ∷
   rw 17 (q11 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw 14 (q13 c4) ∷
   rw 14 (q14 c4) ∷
   rw 16 (q15 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 21 (q11 c4) ∷
   rw⁻ 24 (q11 c4) ∷
   rw⁻ 16 (q17 c4) ∷
   rw⁻ 21 (q17 c4) ∷
   rw⁻ 32 (q17 c4) ∷
   rw⁻ 17 (q18 c4) ∷
   rw⁻ 18 (q19 c4) ∷
   rw 17 (q20 c4) ∷
   rw 17 (q19 c4) ∷
   rw 28 (q18 c4) ∷
   rw 16 (q17 c4) ∷
   rw 25 (q17 c4) ∷
   rw 28 (q17 c4) ∷
   rw 18 (q11 c4) ∷
   rw 19 (q11 c4) ∷
   rw 17 (q16 c4) ∷
   rw 19 (q15 c4) ∷
   re 21 1 (CS02 ∷ []) ∷
   rw 19 (q21 c4) ∷
   re 20 1 (Sb3-0-2-1 ∷ []) ∷
   rw⁻ 22 (q15 c4) ∷
   rw⁻ 26 (q16 c4) ∷
   rw⁻ 27 (q11 c4) ∷
   rw⁻ 30 (q11 c4) ∷
   rw⁻ 22 (q17 c4) ∷
   rw⁻ 27 (q17 c4) ∷
   rw⁻ 38 (q17 c4) ∷
   rw⁻ 23 (q18 c4) ∷
   rw⁻ 24 (q19 c4) ∷
   rw 23 (q20 c4) ∷
   rw 23 (q19 c4) ∷
   rw 34 (q18 c4) ∷
   rw 22 (q17 c4) ∷
   rw 31 (q17 c4) ∷
   rw 34 (q17 c4) ∷
   rw 24 (q11 c4) ∷
   rw 25 (q11 c4) ∷
   rw 23 (q16 c4) ∷
   rw 25 (q15 c4) ∷
   re 27 1 (CS02⁻ ∷ []) ∷
   rw 25 (q22 c4) ∷
   re 26 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q11 c4) ∷
   rw 17 (q11 c4) ∷
   rw 18 (q11 c4) ∷
   re 14 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 14 (q23 c4) ∷
   rw⁻ 16 (q24 c4) ∷
   rw 16 (q25 c4) ∷
   rw 16 (q26 c4) ∷
   rw⁻ 16 (q27 c4) ∷
   rw 12 (q28 c4) ∷
   rw 13 (q29 c4) ∷
   rw 14 (q28 c4) ∷
   re 11 1 (CS03⁻ ∷ []) ∷
   re 13 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw⁻ 23 (q11 c4) ∷
   rw 13 (q30 c4) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw 11 (q31 c4) ∷
   rw 14 (q32 c4) ∷
   rw 17 (q31 c4) ∷
   rw 20 (q32 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q11 c4) ∷
   rw 15 (q11 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   re 19 1 (CS03 ∷ []) ∷
   rw 14 (q33 c4) ∷
   re 18 1 (Sb2-0-3-1 ∷ []) ∷
   re 25 1 (CS03⁻ ∷ []) ∷
   rw 23 (q34 c4) ∷
   re 24 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q11 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q11 c4) ∷
   re 12 5 (Sb2-0-41-3 ∷ []) ∷
   re 14 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 10 (q28 c4) ∷
   rw 11 (q29 c4) ∷
   rw 12 (q28 c4) ∷
   re 9 1 (CS03 ∷ []) ∷
   re 11 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 12 (q11 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw⁻ 21 (q11 c4) ∷
   rw 11 (q30 c4) ∷
   rw⁻ 12 (q11 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw 9 (q35 c4) ∷
   rw 12 (q36 c4) ∷
   rw 15 (q35 c4) ∷
   rw 18 (q36 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q11 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   re 17 1 (CS03 ∷ []) ∷
   rw 12 (q37 c4) ∷
   re 16 1 (Sb2-0-3-1 ∷ []) ∷
   re 23 1 (CS03⁻ ∷ []) ∷
   rw 21 (q38 c4) ∷
   re 22 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q11 c4) ∷
   re 10 5 (Sb2-0-41-3 ∷ []) ∷
   re 12 1 (Sb2-0-3-1 ∷ []) ∷
   re 12 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 8 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 12 1 (CS03⁻ ∷ []) ∷
   re 14 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q11 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw⁻ 21 (q11 c4) ∷
   rw⁻ 24 (q11 c4) ∷
   rw 14 (q30 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw⁻ 21 (q11 c4) ∷
   rw 12 (q31 c4) ∷
   rw 15 (q32 c4) ∷
   rw 18 (q31 c4) ∷
   rw 21 (q32 c4) ∷
   rw 14 (q11 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q11 c4) ∷
   rw⁻ 13 (q30 c4) ∷
   re 20 1 (CS03 ∷ []) ∷
   rw 15 (q33 c4) ∷
   re 19 1 (Sb2-0-3-1 ∷ []) ∷
   re 26 1 (CS03⁻ ∷ []) ∷
   rw 24 (q34 c4) ∷
   re 25 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 14 (q11 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q11 c4) ∷
   rw 17 (q11 c4) ∷
   re 13 5 (Sb2-0-41-3 ∷ []) ∷
   re 15 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 11 (q28 c4) ∷
   rw 12 (q29 c4) ∷
   rw 13 (q28 c4) ∷
   re 10 1 (CS03 ∷ []) ∷
   re 12 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 13 (q11 c4) ∷
   rw⁻ 16 (q11 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   rw⁻ 22 (q11 c4) ∷
   rw 12 (q30 c4) ∷
   rw⁻ 13 (q11 c4) ∷
   rw⁻ 16 (q11 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   rw 10 (q35 c4) ∷
   rw 13 (q36 c4) ∷
   rw 16 (q35 c4) ∷
   rw 19 (q36 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q11 c4) ∷
   rw⁻ 11 (q30 c4) ∷
   re 18 1 (CS03 ∷ []) ∷
   rw 13 (q37 c4) ∷
   re 17 1 (Sb2-0-3-1 ∷ []) ∷
   re 24 1 (CS03⁻ ∷ []) ∷
   rw 22 (q38 c4) ∷
   re 23 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q11 c4) ∷
   rw 15 (q11 c4) ∷
   re 11 5 (Sb2-0-41-3 ∷ []) ∷
   re 13 1 (Sb2-0-3-1 ∷ []) ∷
   rw 9 (q28 c4) ∷
   rw 10 (q29 c4) ∷
   rw 11 (q28 c4) ∷
   rw⁻ 8 (q11 c4) ∷
   rw 9 (q39 c4) ∷
   rw 10 (q40 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw 12 (q39 c4) ∷
   rw⁻ 8 (q41 c4) ∷
   rw⁻ 11 (q41 c4) ∷
   rw 10 (q42 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   rw 8 (q43 c4) ∷
   re 11 5 (Sb2-0-41-3 ∷ []) ∷
   re 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 11 1 (CS03⁻ ∷ []) ∷
   re 13 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw⁻ 23 (q11 c4) ∷
   rw 13 (q30 c4) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw 11 (q31 c4) ∷
   rw 14 (q32 c4) ∷
   rw 17 (q31 c4) ∷
   rw 20 (q32 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q11 c4) ∷
   rw 15 (q11 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   re 19 1 (CS03 ∷ []) ∷
   rw 14 (q33 c4) ∷
   re 18 1 (Sb2-0-3-1 ∷ []) ∷
   re 25 1 (CS03⁻ ∷ []) ∷
   rw 23 (q34 c4) ∷
   re 24 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q11 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q11 c4) ∷
   re 12 5 (Sb2-0-41-3 ∷ []) ∷
   re 14 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 10 (q28 c4) ∷
   rw 11 (q29 c4) ∷
   rw 12 (q28 c4) ∷
   re 9 1 (CS03 ∷ []) ∷
   re 11 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 12 (q11 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw⁻ 21 (q11 c4) ∷
   rw 11 (q30 c4) ∷
   rw⁻ 12 (q11 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw 9 (q35 c4) ∷
   rw 12 (q36 c4) ∷
   rw 15 (q35 c4) ∷
   rw 18 (q36 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q11 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   re 17 1 (CS03 ∷ []) ∷
   rw 12 (q37 c4) ∷
   re 16 1 (Sb2-0-3-1 ∷ []) ∷
   re 23 1 (CS03⁻ ∷ []) ∷
   rw 21 (q38 c4) ∷
   re 22 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q11 c4) ∷
   re 10 5 (Sb2-0-41-3 ∷ []) ∷
   re 12 1 (Sb2-0-3-1 ∷ []) ∷
   rw 8 (q28 c4) ∷
   rw 9 (q29 c4) ∷
   rw 10 (q28 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw 8 (q39 c4) ∷
   rw 9 (q40 c4) ∷
   rw⁻ 10 (q11 c4) ∷
   rw 11 (q39 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw⁻ 10 (q41 c4) ∷
   rw 9 (q42 c4) ∷
   rw⁻ 8 (q41 c4) ∷
   rw 7 (q43 c4) ∷
   re 10 5 (Sb2-0-41-3 ∷ []) ∷
   rw 6 (q44 c4) ∷
   re 14 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q11 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw⁻ 21 (q11 c4) ∷
   rw⁻ 24 (q11 c4) ∷
   rw 14 (q30 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw⁻ 21 (q11 c4) ∷
   rw 12 (q45 c4) ∷
   rw 15 (q46 c4) ∷
   rw 18 (q45 c4) ∷
   rw 21 (q46 c4) ∷
   rw 14 (q11 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q11 c4) ∷
   rw⁻ 13 (q30 c4) ∷
   rw 15 (q47 c4) ∷
   re 20 1 (CS03 ∷ []) ∷
   rw 18 (q48 c4) ∷
   re 19 1 (Sb2-0-3-1 ∷ []) ∷
   rw 21 (q47 c4) ∷
   re 26 1 (CS03⁻ ∷ []) ∷
   rw 24 (q49 c4) ∷
   re 25 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 14 (q11 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q11 c4) ∷
   rw 17 (q11 c4) ∷
   re 13 5 (Sb2-0-41-3 ∷ []) ∷
   re 13 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw⁻ 23 (q11 c4) ∷
   rw 13 (q50 c4) ∷
   rw 13 (q51 c4) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw 9 (q52 c4) ∷
   rw⁻ 14 (q53 c4) ∷
   rw 15 (q54 c4) ∷
   rw⁻ 16 (q53 c4) ∷
   rw 15 (q55 c4) ∷
   rw⁻ 16 (q11 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   rw⁻ 22 (q11 c4) ∷
   rw⁻ 25 (q11 c4) ∷
   rw 13 (q56 c4) ∷
   rw 16 (q57 c4) ∷
   rw 19 (q58 c4) ∷
   rw 22 (q57 c4) ∷
   rw 25 (q59 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q11 c4) ∷
   rw 17 (q11 c4) ∷
   rw 18 (q11 c4) ∷
   rw⁻ 14 (q55 c4) ∷
   rw⁻ 12 (q53 c4) ∷
   rw 13 (q54 c4) ∷
   rw⁻ 14 (q53 c4) ∷
   rw 15 (q52 c4) ∷
   rw⁻ 20 (q53 c4) ∷
   rw 21 (q54 c4) ∷
   rw⁻ 22 (q53 c4) ∷
   rw 21 (q55 c4) ∷
   rw⁻ 22 (q11 c4) ∷
   rw⁻ 25 (q11 c4) ∷
   rw⁻ 28 (q11 c4) ∷
   rw⁻ 31 (q11 c4) ∷
   rw 19 (q56 c4) ∷
   rw 22 (q57 c4) ∷
   rw 25 (q58 c4) ∷
   rw 28 (q57 c4) ∷
   rw 31 (q59 c4) ∷
   rw 21 (q11 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q11 c4) ∷
   rw 24 (q11 c4) ∷
   rw⁻ 20 (q55 c4) ∷
   rw⁻ 18 (q53 c4) ∷
   rw 19 (q54 c4) ∷
   rw⁻ 20 (q53 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q11 c4) ∷
   rw⁻ 10 (q51 c4) ∷
   rw 10 (q60 c4) ∷
   re 19 1 (CS03 ∷ []) ∷
   rw 12 (q61 c4) ∷
   re 16 1 (Sb2-0-3-1 ∷ []) ∷
   re 25 1 (CS03⁻ ∷ []) ∷
   rw 21 (q62 c4) ∷
   re 22 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q11 c4) ∷
   re 10 5 (Sb2-0-41-3 ∷ []) ∷
   re 10 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 11 (q11 c4) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw 10 (q30 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw 8 (q45 c4) ∷
   rw 11 (q46 c4) ∷
   rw 14 (q45 c4) ∷
   rw 17 (q46 c4) ∷
   rw 10 (q11 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q11 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw 11 (q47 c4) ∷
   re 16 1 (CS03 ∷ []) ∷
   rw 14 (q48 c4) ∷
   re 15 1 (Sb2-0-3-1 ∷ []) ∷
   rw 17 (q47 c4) ∷
   re 22 1 (CS03⁻ ∷ []) ∷
   rw 20 (q49 c4) ∷
   re 21 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 10 (q11 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q11 c4) ∷
   re 9 5 (Sb2-0-41-3 ∷ []) ∷
   re 9 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 10 (q11 c4) ∷
   rw⁻ 13 (q11 c4) ∷
   rw⁻ 16 (q11 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   rw 9 (q30 c4) ∷
   rw⁻ 10 (q11 c4) ∷
   rw⁻ 13 (q11 c4) ∷
   rw⁻ 16 (q11 c4) ∷
   rw 7 (q63 c4) ∷
   rw 10 (q64 c4) ∷
   rw 13 (q63 c4) ∷
   rw 16 (q64 c4) ∷
   rw 9 (q11 c4) ∷
   rw 10 (q11 c4) ∷
   rw 11 (q11 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw 10 (q65 c4) ∷
   re 15 1 (CS03 ∷ []) ∷
   rw 13 (q66 c4) ∷
   re 14 1 (Sb2-0-3-1 ∷ []) ∷
   rw 16 (q65 c4) ∷
   re 21 1 (CS03⁻ ∷ []) ∷
   rw 19 (q67 c4) ∷
   re 20 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 9 (q11 c4) ∷
   rw 10 (q11 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q11 c4) ∷
   re 8 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 6 (q68 c4) ∷
   rw⁻ 7 (q69 c4) ∷
   rw⁻ 8 (q68 c4) ∷
   rw⁻ 9 (q44 c4) ∷
   re 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 9 1 (CS03⁻ ∷ []) ∷
   re 11 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 12 (q11 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw⁻ 21 (q11 c4) ∷
   rw 11 (q30 c4) ∷
   rw⁻ 12 (q11 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw 9 (q31 c4) ∷
   rw 12 (q32 c4) ∷
   rw 15 (q31 c4) ∷
   rw 18 (q32 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q11 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   re 17 1 (CS03 ∷ []) ∷
   rw 12 (q33 c4) ∷
   re 16 1 (Sb2-0-3-1 ∷ []) ∷
   re 23 1 (CS03⁻ ∷ []) ∷
   rw 21 (q34 c4) ∷
   re 22 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q11 c4) ∷
   re 10 5 (Sb2-0-41-3 ∷ []) ∷
   re 12 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 8 (q28 c4) ∷
   rw 9 (q29 c4) ∷
   rw 10 (q28 c4) ∷ []) Eq.refl
