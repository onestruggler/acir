{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D132 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0404 ; wl0509 ; wl0528 ; wl0530 ; wl0544 ; wl0545 ; wl0546 ; wl0547 ; wl0548 ; wl0549 ; wl0550 ; wl0551 ; wl0552 ; wl0553 ; wl0554 ; wl0555 ; wl0558 ; wl0559 ; wl0560 ; wl0561 ; wl0562 ; wl0563 ; wl0564 ; wl0565 ; wl0566 ; wl0567 ; wl0568 ; wl0569 ; wl0570 ; wl0571 ; wl0572 ; wp0200 ; wp0202 ; wp0203 ; wp0212 ; wp0213 ; wp0214 ; wp0215 ; wp0216 ; wp0220 ; wp0221 ; wp0222 ; wp0223 ; wp0224 ; wp0225)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0d)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-BOXd-BOX-at0310243142 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 ; lem-beta-T-at03103441 ; lem-sym23-at0310243241 ; lem-sym23-at03103441 ; lem-sym34-at0310243142 ; lem-sym34-at0310243241)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X0 ∷ K2⁻ ∷ []) (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑))
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ134 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (X0 ∷ K2 ∷ []) (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑))
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ134 ∷ K2 ∷ []) (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (X0 ∷ CS23 ∷ []) (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ134 ∷ CS23 ∷ []) (CS23 ∷ CCZ134 ∷ []) (wl0558 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (wl0559 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx⁻3-0412 ∷ []) (Bx3-0412 ∷ []) (lem-BOXd-BOX-at0310243142 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (K2⁻ ∷ K2 ∷ []) [] (wl0550 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0549 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ []) (X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (wl0561 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (K2 ∷ CS23 ∷ K2⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (wl0562 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl0563 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ []) (X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0564 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0565 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wp0220 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (K2 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ K2 ∷ []) (wp0221 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CX03 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ CX03 ∷ []) (wp0222 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (K2⁻ ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ K2⁻ ∷ []) (wp0223 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS12⁻ ∷ X0 ∷ []) (X0 ∷ CS12⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0566 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0567 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ []) (X0 ∷ K2 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0568 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (K2 ∷ CS23⁻ ∷ K2⁻ ∷ X0 ∷ []) (X0 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ []) (wl0569 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (K2 ∷ CS23⁻ ∷ K2⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ []) (wl0570 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ []) (X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) (wp0224 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Toff203 ∷ X0 ∷ CS02⁻ ∷ X0 ∷ []) (X0 ∷ CS02⁻ ∷ X0 ∷ Toff203 ∷ []) (wl0571 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Toff203 ∷ X0 ∷ CS02 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ X0 ∷ Toff203 ∷ []) (wl0572 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (Sb⁻2-0-41-3 ∷ []) (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ124 ∷ X0 ∷ []) (X0 ∷ CCZ124 ∷ []) (wp0225 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Sb⁻2-0-41-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0210243143 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CS03 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ CS03 ∷ []) (wl0544 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Toff314 ∷ CS03⁻ ∷ Toff314 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (wp0212 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Toff201 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ Toff201 ∷ []) (wl0545 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (X0 ∷ CCZ234 ∷ []) (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑))
  q47 : Ws → Eqn
  q47 c4 = eqn (CK01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CK01⁻ ∷ []) (c₂ (S • CK₀₁) (CCZ))
  q48 : Ws → Eqn
  q48 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0213 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CS03 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS03 ∷ []) (wl0546 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ []) (wp0202 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Sb⁻2-0-41-3 ∷ Toff314 ∷ []) (Toff314 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) (wp0214 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CS03⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS03⁻ ∷ []) (wl0547 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (CS02 ∷ X0 ∷ CS34 ∷ X0 ∷ []) (X0 ∷ CS34 ∷ X0 ∷ CS02 ∷ []) (wp0215 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CS02 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ CS02 ∷ []) (wp0216 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CS02 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) (X0 ∷ CS13⁻ ∷ X0 ∷ CS02 ∷ []) (wl0552 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CS02 ∷ X0 ∷ CS13 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ X0 ∷ CS02 ∷ []) (wl0553 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) (wl0555 (lit c4))

-- F1 CS-K1 part8: 333 steps
lem-F1-CS-K1-part8 : Ws → ⟪ (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ
lem-F1-CS-K1-part8 c4 = derive (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  (rw 74 (q1 c4) ∷
   rw 73 (q2 c4) ∷
   rw 72 (q1 c4) ∷
   rw 75 (q3 c4) ∷
   rw 74 (q4 c4) ∷
   rw 73 (q3 c4) ∷
   rw 76 (q5 c4) ∷
   rw 75 (q6 c4) ∷
   rw 74 (q5 c4) ∷
   rw 77 (q1 c4) ∷
   rw 76 (q2 c4) ∷
   rw 75 (q1 c4) ∷
   rw⁻ 61 (q7 c4) ∷
   rw 75 (q8 c4) ∷
   rw 76 (q8 c4) ∷
   rw 77 (q8 c4) ∷
   rw⁻ 74 (q9 c4) ∷
   rw 74 (q10 c4) ∷
   rw 74 (q11 c4) ∷
   rw⁻ 74 (q12 c4) ∷
   rw 60 (q13 c4) ∷
   rw 61 (q13 c4) ∷
   rw 62 (q13 c4) ∷
   rw 63 (q13 c4) ∷
   rw⁻ 59 (q14 c4) ∷
   rw 58 (q15 c4) ∷
   rw⁻ 58 (q15 c4) ∷
   rw 59 (q16 c4) ∷
   rw⁻ 60 (q13 c4) ∷
   rw⁻ 63 (q13 c4) ∷
   rw⁻ 66 (q13 c4) ∷
   rw⁻ 69 (q13 c4) ∷
   rw⁻ 57 (q17 c4) ∷
   rw⁻ 56 (q18 c4) ∷
   rw⁻ 55 (q17 c4) ∷
   rw⁻ 59 (q19 c4) ∷
   rw⁻ 60 (q8 c4) ∷
   rw⁻ 63 (q8 c4) ∷
   rw⁻ 64 (q20 c4) ∷
   rw 62 (q21 c4) ∷
   rw⁻ 63 (q8 c4) ∷
   rw⁻ 66 (q8 c4) ∷
   rw⁻ 69 (q8 c4) ∷
   rw⁻ 72 (q8 c4) ∷
   rw⁻ 73 (q22 c4) ∷
   rw⁻ 70 (q23 c4) ∷
   rw⁻ 71 (q24 c4) ∷
   rw⁻ 72 (q25 c4) ∷
   rw⁻ 67 (q26 c4) ∷
   rw⁻ 64 (q23 c4) ∷
   rw⁻ 65 (q24 c4) ∷
   rw⁻ 66 (q25 c4) ∷
   rw⁻ 61 (q27 c4) ∷
   rw 66 (q8 c4) ∷
   rw 67 (q8 c4) ∷
   rw 68 (q8 c4) ∷
   rw 69 (q8 c4) ∷
   rw⁻ 65 (q21 c4) ∷
   rw⁻ 58 (q28 c4) ∷
   rw 63 (q8 c4) ∷
   rw 64 (q8 c4) ∷
   rw 62 (q19 c4) ∷
   rw⁻ 63 (q29 c4) ∷
   rw⁻ 62 (q30 c4) ∷
   rw⁻ 61 (q29 c4) ∷
   rw⁻ 65 (q19 c4) ∷
   rw⁻ 66 (q8 c4) ∷
   rw⁻ 69 (q8 c4) ∷
   rw⁻ 70 (q20 c4) ∷
   rw 68 (q21 c4) ∷
   rw⁻ 69 (q8 c4) ∷
   rw⁻ 72 (q8 c4) ∷
   rw⁻ 75 (q8 c4) ∷
   rw⁻ 78 (q8 c4) ∷
   rw⁻ 79 (q22 c4) ∷
   rw⁻ 76 (q23 c4) ∷
   rw⁻ 77 (q24 c4) ∷
   rw⁻ 78 (q25 c4) ∷
   rw⁻ 73 (q26 c4) ∷
   rw⁻ 70 (q23 c4) ∷
   rw⁻ 71 (q24 c4) ∷
   rw⁻ 72 (q25 c4) ∷
   rw⁻ 67 (q27 c4) ∷
   rw 72 (q8 c4) ∷
   rw 73 (q8 c4) ∷
   rw 74 (q8 c4) ∷
   rw 75 (q8 c4) ∷
   rw⁻ 71 (q21 c4) ∷
   rw⁻ 64 (q28 c4) ∷
   rw 69 (q8 c4) ∷
   rw 70 (q8 c4) ∷
   rw 68 (q19 c4) ∷
   rw⁻ 67 (q31 c4) ∷
   rw 57 (q13 c4) ∷
   rw 58 (q13 c4) ∷
   rw 59 (q13 c4) ∷
   rw 60 (q13 c4) ∷
   rw⁻ 56 (q16 c4) ∷
   rw 55 (q15 c4) ∷
   re 53 1 (CS02⁻ ∷ []) ∷
   rw⁻ 52 (q32 c4) ∷
   re 54 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 52 (q15 c4) ∷
   rw 53 (q16 c4) ∷
   rw⁻ 54 (q13 c4) ∷
   rw⁻ 57 (q13 c4) ∷
   rw⁻ 60 (q13 c4) ∷
   rw⁻ 63 (q13 c4) ∷
   rw⁻ 51 (q17 c4) ∷
   rw⁻ 50 (q18 c4) ∷
   rw⁻ 49 (q17 c4) ∷
   rw⁻ 53 (q19 c4) ∷
   rw⁻ 54 (q8 c4) ∷
   rw⁻ 57 (q8 c4) ∷
   rw⁻ 58 (q20 c4) ∷
   rw 56 (q21 c4) ∷
   rw⁻ 57 (q8 c4) ∷
   rw⁻ 60 (q8 c4) ∷
   rw⁻ 63 (q8 c4) ∷
   rw⁻ 66 (q8 c4) ∷
   rw⁻ 67 (q22 c4) ∷
   rw⁻ 64 (q23 c4) ∷
   rw⁻ 65 (q24 c4) ∷
   rw⁻ 66 (q25 c4) ∷
   rw⁻ 61 (q26 c4) ∷
   rw⁻ 58 (q23 c4) ∷
   rw⁻ 59 (q24 c4) ∷
   rw⁻ 60 (q25 c4) ∷
   rw⁻ 55 (q27 c4) ∷
   rw 60 (q8 c4) ∷
   rw 61 (q8 c4) ∷
   rw 62 (q8 c4) ∷
   rw 63 (q8 c4) ∷
   rw⁻ 59 (q21 c4) ∷
   rw⁻ 52 (q28 c4) ∷
   rw 57 (q8 c4) ∷
   rw 58 (q8 c4) ∷
   rw 56 (q19 c4) ∷
   rw⁻ 57 (q29 c4) ∷
   rw⁻ 56 (q30 c4) ∷
   rw⁻ 55 (q29 c4) ∷
   rw⁻ 59 (q19 c4) ∷
   rw⁻ 60 (q8 c4) ∷
   rw⁻ 63 (q8 c4) ∷
   rw⁻ 64 (q20 c4) ∷
   rw 62 (q21 c4) ∷
   rw⁻ 63 (q8 c4) ∷
   rw⁻ 66 (q8 c4) ∷
   rw⁻ 69 (q8 c4) ∷
   rw⁻ 72 (q8 c4) ∷
   rw⁻ 73 (q22 c4) ∷
   rw⁻ 70 (q23 c4) ∷
   rw⁻ 71 (q24 c4) ∷
   rw⁻ 72 (q25 c4) ∷
   rw⁻ 67 (q26 c4) ∷
   rw⁻ 64 (q23 c4) ∷
   rw⁻ 65 (q24 c4) ∷
   rw⁻ 66 (q25 c4) ∷
   rw⁻ 61 (q27 c4) ∷
   rw 66 (q8 c4) ∷
   rw 67 (q8 c4) ∷
   rw 68 (q8 c4) ∷
   rw 69 (q8 c4) ∷
   rw⁻ 65 (q21 c4) ∷
   rw⁻ 58 (q28 c4) ∷
   rw 63 (q8 c4) ∷
   rw 64 (q8 c4) ∷
   rw 62 (q19 c4) ∷
   rw⁻ 61 (q31 c4) ∷
   rw 51 (q13 c4) ∷
   rw 52 (q13 c4) ∷
   rw 53 (q13 c4) ∷
   rw 54 (q13 c4) ∷
   rw⁻ 50 (q16 c4) ∷
   rw 49 (q15 c4) ∷
   re 47 1 (CS02 ∷ []) ∷
   rw⁻ 46 (q33 c4) ∷
   re 48 1 (Sb3-0-2-1 ∷ []) ∷
   rw 49 (q8 c4) ∷
   rw 50 (q8 c4) ∷
   rw 51 (q8 c4) ∷
   rw 52 (q8 c4) ∷
   re 48 5 (Sb⁻3-0-41-2 ∷ []) ∷
   rw⁻ 48 (q34 c4) ∷
   rw⁻ 49 (q35 c4) ∷
   rw 48 (q36 c4) ∷
   rw⁻ 47 (q35 c4) ∷
   rw⁻ 44 (q37 c4) ∷
   rw 44 (q38 c4) ∷
   rw 44 (q39 c4) ∷
   rw⁻ 44 (q40 c4) ∷
   re 40 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 40 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 40 1 (CS03 ∷ []) ∷
   rw⁻ 37 (q41 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ []) ∷
   re 42 1 (CS03⁻ ∷ []) ∷
   rw⁻ 38 (q42 c4) ∷
   re 39 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 44 (q40 c4) ∷
   rw 44 (q43 c4) ∷
   rw 44 (q44 c4) ∷
   rw⁻ 41 (q45 c4) ∷
   rw 44 (q46 c4) ∷
   rw 43 (q47 c4) ∷
   rw 42 (q46 c4) ∷
   rw⁻ 43 (q45 c4) ∷
   rw 46 (q46 c4) ∷
   rw 45 (q47 c4) ∷
   rw 44 (q46 c4) ∷
   rw⁻ 41 (q44 c4) ∷
   rw 41 (q48 c4) ∷
   rw⁻ 41 (q40 c4) ∷
   re 37 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 37 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 37 1 (CS03 ∷ []) ∷
   re 35 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 36 (q8 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw⁻ 42 (q8 c4) ∷
   rw⁻ 45 (q8 c4) ∷
   rw 47 (q40 c4) ∷
   rw 47 (q49 c4) ∷
   rw⁻ 48 (q8 c4) ∷
   rw⁻ 51 (q8 c4) ∷
   rw⁻ 54 (q8 c4) ∷
   rw⁻ 55 (q50 c4) ∷
   rw⁻ 52 (q51 c4) ∷
   rw⁻ 49 (q50 c4) ∷
   rw⁻ 46 (q51 c4) ∷
   rw 49 (q8 c4) ∷
   rw 50 (q8 c4) ∷
   rw 51 (q8 c4) ∷
   rw⁻ 48 (q49 c4) ∷
   rw⁻ 48 (q40 c4) ∷
   re 41 1 (CS03⁻ ∷ []) ∷
   rw⁻ 37 (q52 c4) ∷
   re 42 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 35 1 (CS03 ∷ []) ∷
   rw⁻ 34 (q53 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ []) ∷
   rw 37 (q8 c4) ∷
   rw 38 (q8 c4) ∷
   rw 39 (q8 c4) ∷
   rw 40 (q8 c4) ∷
   re 36 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 34 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 37 (q54 c4) ∷
   rw 36 (q55 c4) ∷
   rw⁻ 35 (q54 c4) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   re 37 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 41 (q8 c4) ∷
   rw⁻ 44 (q8 c4) ∷
   rw⁻ 47 (q8 c4) ∷
   rw 49 (q40 c4) ∷
   rw 49 (q49 c4) ∷
   rw⁻ 50 (q8 c4) ∷
   rw⁻ 53 (q8 c4) ∷
   rw⁻ 56 (q8 c4) ∷
   rw⁻ 57 (q56 c4) ∷
   rw⁻ 54 (q57 c4) ∷
   rw⁻ 51 (q56 c4) ∷
   rw⁻ 48 (q57 c4) ∷
   rw 51 (q8 c4) ∷
   rw 52 (q8 c4) ∷
   rw 53 (q8 c4) ∷
   rw⁻ 50 (q49 c4) ∷
   rw⁻ 50 (q40 c4) ∷
   re 43 1 (CS03⁻ ∷ []) ∷
   rw⁻ 39 (q58 c4) ∷
   re 44 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 37 1 (CS03 ∷ []) ∷
   rw⁻ 36 (q59 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ []) ∷
   rw 39 (q8 c4) ∷
   rw 40 (q8 c4) ∷
   rw 41 (q8 c4) ∷
   rw 42 (q8 c4) ∷
   re 38 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 36 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 39 (q54 c4) ∷
   rw 38 (q55 c4) ∷
   rw⁻ 37 (q54 c4) ∷
   rw 41 (q40 c4) ∷
   rw 41 (q60 c4) ∷
   rw 41 (q61 c4) ∷
   rw 41 (q37 c4) ∷
   rw 39 (q34 c4) ∷
   re 39 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) ∷
   rw⁻ 40 (q8 c4) ∷
   rw⁻ 43 (q8 c4) ∷
   rw⁻ 46 (q8 c4) ∷
   rw⁻ 49 (q8 c4) ∷
   rw⁻ 53 (q15 c4) ∷
   rw 54 (q14 c4) ∷
   rw⁻ 55 (q13 c4) ∷
   rw⁻ 58 (q13 c4) ∷
   rw⁻ 61 (q13 c4) ∷
   rw⁻ 64 (q13 c4) ∷
   rw 51 (q12 c4) ∷
   rw 51 (q62 c4) ∷
   rw 51 (q63 c4) ∷
   rw 51 (q9 c4) ∷
   rw⁻ 52 (q8 c4) ∷
   rw⁻ 55 (q8 c4) ∷
   rw⁻ 58 (q8 c4) ∷
   rw 61 (q3 c4) ∷
   rw 60 (q4 c4) ∷
   rw 59 (q3 c4) ∷
   rw 61 (q64 c4) ∷
   rw⁻ 62 (q8 c4) ∷
   rw⁻ 65 (q8 c4) ∷
   rw⁻ 68 (q8 c4) ∷
   rw⁻ 71 (q8 c4) ∷
   rw⁻ 72 (q65 c4) ∷
   rw⁻ 69 (q66 c4) ∷
   rw⁻ 66 (q67 c4) ∷
   rw⁻ 63 (q66 c4) ∷
   rw⁻ 60 (q68 c4) ∷
   rw 63 (q8 c4) ∷
   rw 64 (q8 c4) ∷
   rw 65 (q8 c4) ∷
   rw 66 (q8 c4) ∷
   rw⁻ 62 (q64 c4) ∷
   rw 63 (q1 c4) ∷
   rw 62 (q2 c4) ∷
   rw 61 (q1 c4) ∷
   rw⁻ 56 (q69 c4) ∷
   rw 55 (q3 c4) ∷
   rw 54 (q4 c4) ∷
   rw 53 (q3 c4) ∷ []) Eq.refl
