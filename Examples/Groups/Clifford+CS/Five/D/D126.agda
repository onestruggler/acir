{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D126 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0393 ; wl0404 ; wl0433 ; wl0509 ; wl0510 ; wl0511 ; wl0512 ; wl0528 ; wl0530 ; wl0533 ; wl0534 ; wl0535 ; wl0536 ; wl0537 ; wl0538 ; wl0539 ; wl0540 ; wl0541 ; wl0542 ; wl0543 ; wl0544 ; wl0545 ; wl0546 ; wl0547 ; wl0548 ; wl0549 ; wl0550 ; wl0551 ; wl0552 ; wl0553 ; wl0554 ; wl0555 ; wp0182 ; wp0183 ; wp0184 ; wp0185 ; wp0186 ; wp0187 ; wp0188 ; wp0189 ; wp0190 ; wp0191 ; wp0200 ; wp0202 ; wp0203 ; wp0206 ; wp0207 ; wp0208 ; wp0209 ; wp0210 ; wp0211 ; wp0212 ; wp0213 ; wp0214 ; wp0215 ; wp0216)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0d)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-BOXd-BOX-at0310243142 ; lem-F5d-CS01-at0440 ; lem-SBtgtd-at0440 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 ; lem-beta-T-at03103441 ; lem-sym23-at0310243241 ; lem-sym34-at0310243142)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CS04⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS04⁻ ∷ []) (wp0183 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CS04⁻ ∷ X0 ∷ CX13 ∷ X0 ∷ []) (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CS04⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0185 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CS04⁻ ∷ X0 ∷ CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ []) (wp0186 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CS04⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ []) (wp0182 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS04⁻ ∷ []) (wp0187 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CS04⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS04⁻ ∷ []) (wp0188 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CS04⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0189 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) (wp0190 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) (wl0510 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) (wp0191 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (S0 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0 ∷ []) (wl0511 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0 ∷ []) (wl0512 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CK41⁻ ∷ []) (CS14⁻ ∷ K1⁻ ∷ CS14⁻ ∷ K1⁻ ∷ CS14⁻ ∷ S4 ∷ ι1⁻ ∷ []) (wp0206 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (ι1⁻ ∷ []) (ι⁻ ∷ []) (uₛ ((iI • iI • iI) ↑) (iI • iI • iI) Eq.refl)
  q19 : Ws → Eqn
  q19 c4 = eqn (CS14⁻ ∷ []) (Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ []) (lem-F5d-CS01-at0440 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Sb⁻2-4-01-3 ∷ []) (Sb⁻2-0-41-3 ∷ []) (lem-SBtgtd-at0440 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (K1⁻ ∷ []) (wl0533 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (S4 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (wp0207 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ []) (ι⁻ ∷ []) (wl0534 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CK01⁻ ∷ []) (CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ []) (wl0535 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS01⁻ ∷ []) (wl0536 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS01⁻ ∷ []) (wp0208 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS01⁻ ∷ []) (wp0209 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS01⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS01⁻ ∷ []) (wl0537 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CS01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS01⁻ ∷ []) (wl0538 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (X0 ∷ K1⁻ ∷ []) (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI))
  q34 : Ws → Eqn
  q34 c4 = eqn (K1⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ K1⁻ ∷ []) (c₂ ((K • iI) ↑) (CCZ))
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS01⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ []) (wp0210 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (X0 ∷ CX43 ∷ X0 ∷ CS01⁻ ∷ []) (wl0539 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CS01⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS01⁻ ∷ []) (wl0540 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS01⁻ ∷ []) (wl0541 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) (wl0542 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) (wp0211 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) (wl0543 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (X0 ∷ ι⁻ ∷ []) (ι⁻ ∷ X0 ∷ []) (zc⁻)
  q45 : Ws → Eqn
  q45 c4 = eqn (Sb⁻2-0-41-3 ∷ ι⁻ ∷ []) (ι⁻ ∷ Sb⁻2-0-41-3 ∷ []) (zc⁻)
  q46 : Ws → Eqn
  q46 c4 = eqn (CS03 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ CS03 ∷ []) (wl0544 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (Toff314 ∷ CS03⁻ ∷ Toff314 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (wp0212 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (Toff201 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ Toff201 ∷ []) (wl0545 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (X0 ∷ CCZ234 ∷ []) (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑))
  q50 : Ws → Eqn
  q50 c4 = eqn (CK01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CK01⁻ ∷ []) (c₂ (S • CK₀₁) (CCZ))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0213 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CS03 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS03 ∷ []) (wl0546 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ []) (wp0202 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (Sb⁻2-0-41-3 ∷ Toff314 ∷ []) (Toff314 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) (wp0214 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (CS03⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS03⁻ ∷ []) (wl0547 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Sb⁻2-0-41-3 ∷ []) (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0549 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (K2⁻ ∷ K2 ∷ []) [] (wl0550 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (Bx⁻3-0412 ∷ []) (Bx3-0412 ∷ []) (lem-BOXd-BOX-at0310243142 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (X0 ∷ K2 ∷ []) (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑))
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ134 ∷ K2 ∷ []) (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (CS02 ∷ X0 ∷ CS34 ∷ X0 ∷ []) (X0 ∷ CS34 ∷ X0 ∷ CS02 ∷ []) (wp0215 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (CS02 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ CS02 ∷ []) (wp0216 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (CS02 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) (X0 ∷ CS13⁻ ∷ X0 ∷ CS02 ∷ []) (wl0552 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (CS02 ∷ X0 ∷ CS13 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ X0 ∷ CS02 ∷ []) (wl0553 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (X0 ∷ K2⁻ ∷ []) (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑))
  q80 : Ws → Eqn
  q80 c4 = eqn (CCZ134 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4))
  q81 : Ws → Eqn
  q81 c4 = eqn (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) (wl0555 (lit c4))

-- F1 CS-K1 part2: 404 steps
lem-F1-CS-K1-part2 : Ws → ⟪ (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ K2 ∷ X0 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ
lem-F1-CS-K1-part2 c4 = derive (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ K2 ∷ X0 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  (rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw 23 (q2 c4) ∷
   rw 26 (q3 c4) ∷
   rw 29 (q4 c4) ∷
   rw 32 (q3 c4) ∷
   rw 35 (q5 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw⁻ 24 (q6 c4) ∷
   rw 26 (q7 c4) ∷
   rw 31 (q6 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   rw 29 (q2 c4) ∷
   rw 32 (q3 c4) ∷
   rw 35 (q4 c4) ∷
   rw 38 (q3 c4) ∷
   rw 41 (q5 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw⁻ 30 (q6 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw 23 (q9 c4) ∷
   re 28 1 (CS03 ∷ []) ∷
   rw 26 (q10 c4) ∷
   re 27 1 (Sb2-0-3-1 ∷ []) ∷
   rw 29 (q9 c4) ∷
   re 34 1 (CS03⁻ ∷ []) ∷
   rw 32 (q11 c4) ∷
   re 33 1 (Sb⁻2-0-3-1 ∷ []) ∷
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
   rw 21 (q8 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw 19 (q12 c4) ∷
   rw 22 (q13 c4) ∷
   rw 25 (q12 c4) ∷
   rw 28 (q13 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw 22 (q14 c4) ∷
   re 27 1 (CS03 ∷ []) ∷
   rw 25 (q15 c4) ∷
   re 26 1 (Sb2-0-3-1 ∷ []) ∷
   rw 28 (q14 c4) ∷
   re 33 1 (CS03⁻ ∷ []) ∷
   rw 31 (q16 c4) ∷
   re 32 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   re 20 5 (Sb2-0-41-3 ∷ []) ∷
   rw 30 (q17 c4) ∷
   rw 36 (q18 c4) ∷
   rw 30 (q19 c4) ∷
   rw 30 (q20 c4) ∷
   rw 32 (q20 c4) ∷
   rw⁻ 34 (q21 c4) ∷
   rw 38 (q19 c4) ∷
   rw 38 (q20 c4) ∷
   rw 40 (q20 c4) ∷
   rw⁻ 42 (q21 c4) ∷
   rw 46 (q19 c4) ∷
   rw 46 (q20 c4) ∷
   rw 48 (q20 c4) ∷
   rw 50 (q22 c4) ∷
   rw⁻ 54 (q23 c4) ∷
   rw 34 (q24 c4) ∷
   re 32 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw 44 (q25 c4) ∷
   rw 44 (q8 c4) ∷
   rw⁻ 45 (q1 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw⁻ 52 (q26 c4) ∷
   rw⁻ 49 (q27 c4) ∷
   rw⁻ 46 (q26 c4) ∷
   rw⁻ 43 (q27 c4) ∷
   rw 46 (q1 c4) ∷
   rw 47 (q1 c4) ∷
   rw 48 (q1 c4) ∷
   rw⁻ 45 (q8 c4) ∷
   rw⁻ 45 (q25 c4) ∷
   rw⁻ 40 (q28 c4) ∷
   re 38 1 (CS03⁻ ∷ []) ∷
   rw⁻ 37 (q29 c4) ∷
   re 39 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 34 (q28 c4) ∷
   re 32 1 (CS03 ∷ []) ∷
   rw⁻ 31 (q30 c4) ∷
   re 33 1 (Sb2-0-3-1 ∷ []) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   re 33 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 33 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw 45 (q25 c4) ∷
   rw 45 (q31 c4) ∷
   rw 45 (q32 c4) ∷
   rw⁻ 46 (q1 c4) ∷
   rw⁻ 49 (q1 c4) ∷
   rw⁻ 52 (q1 c4) ∷
   rw 55 (q33 c4) ∷
   rw⁻ 54 (q34 c4) ∷
   rw 53 (q33 c4) ∷
   rw 55 (q35 c4) ∷
   rw⁻ 56 (q1 c4) ∷
   rw⁻ 59 (q1 c4) ∷
   rw⁻ 62 (q1 c4) ∷
   rw⁻ 65 (q1 c4) ∷
   rw⁻ 66 (q36 c4) ∷
   rw⁻ 63 (q37 c4) ∷
   rw⁻ 60 (q38 c4) ∷
   rw⁻ 57 (q37 c4) ∷
   rw⁻ 54 (q39 c4) ∷
   rw 57 (q1 c4) ∷
   rw 58 (q1 c4) ∷
   rw 59 (q1 c4) ∷
   rw 60 (q1 c4) ∷
   rw⁻ 56 (q35 c4) ∷
   rw 57 (q33 c4) ∷
   rw⁻ 56 (q34 c4) ∷
   rw 55 (q33 c4) ∷
   rw⁻ 50 (q40 c4) ∷
   rw 49 (q33 c4) ∷
   rw⁻ 48 (q34 c4) ∷
   rw 47 (q33 c4) ∷
   rw 49 (q35 c4) ∷
   rw⁻ 50 (q1 c4) ∷
   rw⁻ 53 (q1 c4) ∷
   rw⁻ 56 (q1 c4) ∷
   rw⁻ 59 (q1 c4) ∷
   rw⁻ 60 (q36 c4) ∷
   rw⁻ 57 (q37 c4) ∷
   rw⁻ 54 (q38 c4) ∷
   rw⁻ 51 (q37 c4) ∷
   rw⁻ 48 (q39 c4) ∷
   rw 51 (q1 c4) ∷
   rw 52 (q1 c4) ∷
   rw 53 (q1 c4) ∷
   rw 54 (q1 c4) ∷
   rw⁻ 50 (q35 c4) ∷
   rw 51 (q33 c4) ∷
   rw⁻ 50 (q34 c4) ∷
   rw 49 (q33 c4) ∷
   rw⁻ 44 (q40 c4) ∷
   rw 49 (q1 c4) ∷
   rw 50 (q1 c4) ∷
   rw 51 (q1 c4) ∷
   rw⁻ 48 (q32 c4) ∷
   rw 48 (q41 c4) ∷
   rw⁻ 48 (q25 c4) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   rw⁻ 35 (q42 c4) ∷
   re 42 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 33 1 (CS03 ∷ []) ∷
   rw⁻ 32 (q43 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ []) ∷
   rw 37 (q1 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   re 36 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 36 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw⁻ 46 (q1 c4) ∷
   rw 48 (q25 c4) ∷
   rw 48 (q8 c4) ∷
   rw⁻ 49 (q1 c4) ∷
   rw⁻ 52 (q1 c4) ∷
   rw⁻ 55 (q1 c4) ∷
   rw⁻ 56 (q26 c4) ∷
   rw⁻ 53 (q27 c4) ∷
   rw⁻ 50 (q26 c4) ∷
   rw⁻ 47 (q27 c4) ∷
   rw 50 (q1 c4) ∷
   rw 51 (q1 c4) ∷
   rw 52 (q1 c4) ∷
   rw⁻ 49 (q8 c4) ∷
   rw⁻ 49 (q25 c4) ∷
   rw⁻ 44 (q28 c4) ∷
   re 42 1 (CS03⁻ ∷ []) ∷
   rw⁻ 41 (q29 c4) ∷
   re 43 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 38 (q28 c4) ∷
   re 36 1 (CS03 ∷ []) ∷
   rw⁻ 35 (q30 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ []) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   re 37 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 37 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 38 (q1 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   rw⁻ 44 (q1 c4) ∷
   rw⁻ 47 (q1 c4) ∷
   rw 49 (q25 c4) ∷
   rw 49 (q8 c4) ∷
   rw⁻ 50 (q1 c4) ∷
   rw⁻ 53 (q1 c4) ∷
   rw⁻ 56 (q1 c4) ∷
   rw⁻ 57 (q13 c4) ∷
   rw⁻ 54 (q12 c4) ∷
   rw⁻ 51 (q13 c4) ∷
   rw⁻ 48 (q12 c4) ∷
   rw 51 (q1 c4) ∷
   rw 52 (q1 c4) ∷
   rw 53 (q1 c4) ∷
   rw⁻ 50 (q8 c4) ∷
   rw⁻ 50 (q25 c4) ∷
   rw⁻ 45 (q14 c4) ∷
   re 43 1 (CS03⁻ ∷ []) ∷
   rw⁻ 42 (q16 c4) ∷
   re 44 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 39 (q14 c4) ∷
   re 37 1 (CS03 ∷ []) ∷
   rw⁻ 36 (q15 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ []) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   rw 42 (q1 c4) ∷
   re 38 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 39 (q44 c4) ∷
   rw 38 (q45 c4) ∷
   rw 37 (q44 c4) ∷
   rw⁻ 31 (q24 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 38 1 (CS03 ∷ []) ∷
   rw⁻ 35 (q46 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ []) ∷
   re 40 1 (CS03⁻ ∷ []) ∷
   rw⁻ 36 (q47 c4) ∷
   re 37 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 42 (q25 c4) ∷
   rw 42 (q31 c4) ∷
   rw 42 (q32 c4) ∷
   rw⁻ 39 (q48 c4) ∷
   rw 42 (q49 c4) ∷
   rw 41 (q50 c4) ∷
   rw 40 (q49 c4) ∷
   rw⁻ 41 (q48 c4) ∷
   rw 44 (q49 c4) ∷
   rw 43 (q50 c4) ∷
   rw 42 (q49 c4) ∷
   rw⁻ 39 (q32 c4) ∷
   rw 39 (q41 c4) ∷
   rw⁻ 39 (q25 c4) ∷
   re 35 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 35 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 35 1 (CS03 ∷ []) ∷
   re 33 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw 45 (q25 c4) ∷
   rw 45 (q8 c4) ∷
   rw⁻ 46 (q1 c4) ∷
   rw⁻ 49 (q1 c4) ∷
   rw⁻ 52 (q1 c4) ∷
   rw⁻ 53 (q51 c4) ∷
   rw⁻ 50 (q52 c4) ∷
   rw⁻ 47 (q51 c4) ∷
   rw⁻ 44 (q52 c4) ∷
   rw 47 (q1 c4) ∷
   rw 48 (q1 c4) ∷
   rw 49 (q1 c4) ∷
   rw⁻ 46 (q8 c4) ∷
   rw⁻ 46 (q25 c4) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   rw⁻ 35 (q53 c4) ∷
   re 40 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 33 1 (CS03 ∷ []) ∷
   rw⁻ 32 (q54 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ []) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   rw 38 (q1 c4) ∷
   re 34 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 32 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 35 (q55 c4) ∷
   rw 34 (q56 c4) ∷
   rw⁻ 33 (q55 c4) ∷
   re 37 1 (CS03⁻ ∷ []) ∷
   re 35 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw⁻ 45 (q1 c4) ∷
   rw 47 (q25 c4) ∷
   rw 47 (q8 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw⁻ 54 (q1 c4) ∷
   rw⁻ 55 (q57 c4) ∷
   rw⁻ 52 (q58 c4) ∷
   rw⁻ 49 (q57 c4) ∷
   rw⁻ 46 (q58 c4) ∷
   rw 49 (q1 c4) ∷
   rw 50 (q1 c4) ∷
   rw 51 (q1 c4) ∷
   rw⁻ 48 (q8 c4) ∷
   rw⁻ 48 (q25 c4) ∷
   re 41 1 (CS03⁻ ∷ []) ∷
   rw⁻ 37 (q59 c4) ∷
   re 42 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 35 1 (CS03 ∷ []) ∷
   rw⁻ 34 (q60 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ []) ∷
   rw 37 (q1 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   re 36 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 34 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 37 (q55 c4) ∷
   rw 36 (q56 c4) ∷
   rw⁻ 35 (q55 c4) ∷
   rw 39 (q25 c4) ∷
   rw 39 (q61 c4) ∷
   rw 39 (q62 c4) ∷
   rw 39 (q63 c4) ∷
   rw 37 (q64 c4) ∷
   re 37 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) ∷
   rw⁻ 38 (q1 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   rw⁻ 44 (q1 c4) ∷
   rw⁻ 47 (q1 c4) ∷
   rw⁻ 51 (q65 c4) ∷
   rw 52 (q66 c4) ∷
   rw⁻ 53 (q67 c4) ∷
   rw⁻ 56 (q67 c4) ∷
   rw⁻ 59 (q67 c4) ∷
   rw⁻ 62 (q67 c4) ∷
   rw 49 (q68 c4) ∷
   rw 49 (q69 c4) ∷
   rw 49 (q70 c4) ∷
   rw 49 (q71 c4) ∷
   rw⁻ 50 (q1 c4) ∷
   rw⁻ 53 (q1 c4) ∷
   rw⁻ 56 (q1 c4) ∷
   rw 59 (q72 c4) ∷
   rw 58 (q73 c4) ∷
   rw 57 (q72 c4) ∷
   rw 59 (q74 c4) ∷
   rw⁻ 60 (q1 c4) ∷
   rw⁻ 63 (q1 c4) ∷
   rw⁻ 66 (q1 c4) ∷
   rw⁻ 69 (q1 c4) ∷
   rw⁻ 70 (q75 c4) ∷
   rw⁻ 67 (q76 c4) ∷
   rw⁻ 64 (q77 c4) ∷
   rw⁻ 61 (q76 c4) ∷
   rw⁻ 58 (q78 c4) ∷
   rw 61 (q1 c4) ∷
   rw 62 (q1 c4) ∷
   rw 63 (q1 c4) ∷
   rw 64 (q1 c4) ∷
   rw⁻ 60 (q74 c4) ∷
   rw 61 (q79 c4) ∷
   rw 60 (q80 c4) ∷
   rw 59 (q79 c4) ∷
   rw⁻ 54 (q81 c4) ∷
   rw 53 (q72 c4) ∷ []) Eq.refl
