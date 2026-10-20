{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D097 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0404 ; wl0509 ; wl0510 ; wl0511 ; wl0512 ; wl0528 ; wl0530 ; wl0535 ; wl0544 ; wl0545 ; wl0546 ; wl0547 ; wl0548 ; wl0549 ; wl0550 ; wl0551 ; wl0552 ; wl0553 ; wl0554 ; wl0555 ; wl0556 ; wl0557 ; wl0558 ; wl0559 ; wl0560 ; wl0561 ; wl0562 ; wl0563 ; wl0564 ; wl0565 ; wp0190 ; wp0191 ; wp0200 ; wp0202 ; wp0203 ; wp0212 ; wp0213 ; wp0214 ; wp0215 ; wp0216 ; wp0217 ; wp0218 ; wp0219)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0d)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-BOXd-BOX-at0310243142 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 ; lem-beta-T-at03103441 ; lem-sym23-at0310243241 ; lem-sym23-at03103441 ; lem-sym34-at0310243142 ; lem-sym34-at0310243241)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) (wl0510 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) (wp0190 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) (wp0191 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0 ∷ []) (wl0512 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (S0 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0 ∷ []) (wl0511 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (X0 ∷ ι⁻ ∷ []) (ι⁻ ∷ X0 ∷ []) (zc⁻)
  q10 : Ws → Eqn
  q10 c4 = eqn (Sb⁻2-0-41-3 ∷ ι⁻ ∷ []) (ι⁻ ∷ Sb⁻2-0-41-3 ∷ []) (zc⁻)
  q11 : Ws → Eqn
  q11 c4 = eqn (CK01⁻ ∷ []) (CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ []) (wl0535 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CS03 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ CS03 ∷ []) (wl0544 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Toff314 ∷ CS03⁻ ∷ Toff314 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (wp0212 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Toff201 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ Toff201 ∷ []) (wl0545 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (X0 ∷ CCZ234 ∷ []) (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑))
  q18 : Ws → Eqn
  q18 c4 = eqn (CK01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CK01⁻ ∷ []) (c₂ (S • CK₀₁) (CCZ))
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0213 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS03 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS03 ∷ []) (wl0546 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ []) (wp0202 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Sb⁻2-0-41-3 ∷ Toff314 ∷ []) (Toff314 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) (wp0214 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS03⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS03⁻ ∷ []) (wl0547 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Sb⁻2-0-41-3 ∷ []) (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0549 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (K2⁻ ∷ K2 ∷ []) [] (wl0550 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx⁻3-0412 ∷ []) (Bx3-0412 ∷ []) (lem-BOXd-BOX-at0310243142 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (X0 ∷ K2 ∷ []) (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑))
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ134 ∷ K2 ∷ []) (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CS02 ∷ X0 ∷ CS34 ∷ X0 ∷ []) (X0 ∷ CS34 ∷ X0 ∷ CS02 ∷ []) (wp0215 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CS02 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ CS02 ∷ []) (wp0216 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CS02 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) (X0 ∷ CS13⁻ ∷ X0 ∷ CS02 ∷ []) (wl0552 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CS02 ∷ X0 ∷ CS13 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ X0 ∷ CS02 ∷ []) (wl0553 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (X0 ∷ K2⁻ ∷ []) (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑))
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ134 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) (wl0555 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CX30 ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ X0 ∷ CX30 ∷ []) (wp0217 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CS02⁻ ∷ X0 ∷ CS34 ∷ X0 ∷ []) (X0 ∷ CS34 ∷ X0 ∷ CS02⁻ ∷ []) (wp0218 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CS02⁻ ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ CS02⁻ ∷ []) (wp0219 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CS02⁻ ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) (X0 ∷ CS13⁻ ∷ X0 ∷ CS02⁻ ∷ []) (wl0556 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CS02⁻ ∷ X0 ∷ CS13 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ X0 ∷ CS02⁻ ∷ []) (wl0557 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (X0 ∷ CS23 ∷ []) (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑))
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ134 ∷ CS23 ∷ []) (CS23 ∷ CCZ134 ∷ []) (wl0558 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (wl0559 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ []) (X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (wl0561 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (K2 ∷ CS23 ∷ K2⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (wl0562 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl0563 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ []) (X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0564 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0565 (lit c4))

-- F1 CS-K1 [rhs shape] part6: 333 steps
lem-F1-CS-K1-rhs-shape-part6 : Ws → ⟪ (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ X0 ∷ CS12 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS12⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-rhs-shape-part6 c4 = derive (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ X0 ∷ CS12 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS12⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw 43 (q1 c4) ∷
   re 39 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 39 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw⁻ 46 (q1 c4) ∷
   rw⁻ 49 (q1 c4) ∷
   rw 51 (q2 c4) ∷
   rw 51 (q3 c4) ∷
   rw⁻ 52 (q1 c4) ∷
   rw⁻ 55 (q1 c4) ∷
   rw⁻ 58 (q1 c4) ∷
   rw⁻ 59 (q4 c4) ∷
   rw⁻ 56 (q5 c4) ∷
   rw⁻ 53 (q4 c4) ∷
   rw⁻ 50 (q5 c4) ∷
   rw 53 (q1 c4) ∷
   rw 54 (q1 c4) ∷
   rw 55 (q1 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw⁻ 52 (q2 c4) ∷
   rw⁻ 47 (q6 c4) ∷
   re 45 1 (CS03⁻ ∷ []) ∷
   rw⁻ 44 (q7 c4) ∷
   re 46 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 41 (q6 c4) ∷
   re 39 1 (CS03 ∷ []) ∷
   rw⁻ 38 (q8 c4) ∷
   re 40 1 (Sb2-0-3-1 ∷ []) ∷
   rw 41 (q1 c4) ∷
   rw 42 (q1 c4) ∷
   rw 43 (q1 c4) ∷
   rw 44 (q1 c4) ∷
   re 40 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 41 (q9 c4) ∷
   rw 40 (q10 c4) ∷
   rw 39 (q9 c4) ∷
   rw⁻ 33 (q11 c4) ∷
   re 46 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 46 1 (CS03 ∷ []) ∷
   rw⁻ 43 (q12 c4) ∷
   re 43 1 (Sb2-0-3-1 ∷ []) ∷
   re 48 1 (CS03⁻ ∷ []) ∷
   rw⁻ 44 (q13 c4) ∷
   re 45 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 50 (q2 c4) ∷
   rw 50 (q14 c4) ∷
   rw 50 (q15 c4) ∷
   rw⁻ 47 (q16 c4) ∷
   rw 50 (q17 c4) ∷
   rw 49 (q18 c4) ∷
   rw 48 (q17 c4) ∷
   rw⁻ 49 (q16 c4) ∷
   rw 52 (q17 c4) ∷
   rw 51 (q18 c4) ∷
   rw 50 (q17 c4) ∷
   rw⁻ 47 (q15 c4) ∷
   rw 47 (q19 c4) ∷
   rw⁻ 47 (q2 c4) ∷
   re 43 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 43 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 43 1 (CS03 ∷ []) ∷
   re 41 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 42 (q1 c4) ∷
   rw⁻ 45 (q1 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw 53 (q2 c4) ∷
   rw 53 (q3 c4) ∷
   rw⁻ 54 (q1 c4) ∷
   rw⁻ 57 (q1 c4) ∷
   rw⁻ 60 (q1 c4) ∷
   rw⁻ 61 (q20 c4) ∷
   rw⁻ 58 (q21 c4) ∷
   rw⁻ 55 (q20 c4) ∷
   rw⁻ 52 (q21 c4) ∷
   rw 55 (q1 c4) ∷
   rw 56 (q1 c4) ∷
   rw 57 (q1 c4) ∷
   rw⁻ 54 (q3 c4) ∷
   rw⁻ 54 (q2 c4) ∷
   re 47 1 (CS03⁻ ∷ []) ∷
   rw⁻ 43 (q22 c4) ∷
   re 48 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 41 1 (CS03 ∷ []) ∷
   rw⁻ 40 (q23 c4) ∷
   re 42 1 (Sb2-0-3-1 ∷ []) ∷
   rw 43 (q1 c4) ∷
   rw 44 (q1 c4) ∷
   rw 45 (q1 c4) ∷
   rw 46 (q1 c4) ∷
   re 42 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 40 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 43 (q24 c4) ∷
   rw 42 (q25 c4) ∷
   rw⁻ 41 (q24 c4) ∷
   re 45 1 (CS03⁻ ∷ []) ∷
   re 43 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 44 (q1 c4) ∷
   rw⁻ 47 (q1 c4) ∷
   rw⁻ 50 (q1 c4) ∷
   rw⁻ 53 (q1 c4) ∷
   rw 55 (q2 c4) ∷
   rw 55 (q3 c4) ∷
   rw⁻ 56 (q1 c4) ∷
   rw⁻ 59 (q1 c4) ∷
   rw⁻ 62 (q1 c4) ∷
   rw⁻ 63 (q26 c4) ∷
   rw⁻ 60 (q27 c4) ∷
   rw⁻ 57 (q26 c4) ∷
   rw⁻ 54 (q27 c4) ∷
   rw 57 (q1 c4) ∷
   rw 58 (q1 c4) ∷
   rw 59 (q1 c4) ∷
   rw⁻ 56 (q3 c4) ∷
   rw⁻ 56 (q2 c4) ∷
   re 49 1 (CS03⁻ ∷ []) ∷
   rw⁻ 45 (q28 c4) ∷
   re 50 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 43 1 (CS03 ∷ []) ∷
   rw⁻ 42 (q29 c4) ∷
   re 44 1 (Sb2-0-3-1 ∷ []) ∷
   rw 45 (q1 c4) ∷
   rw 46 (q1 c4) ∷
   rw 47 (q1 c4) ∷
   rw 48 (q1 c4) ∷
   re 44 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 42 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 45 (q24 c4) ∷
   rw 44 (q25 c4) ∷
   rw⁻ 43 (q24 c4) ∷
   rw 47 (q2 c4) ∷
   rw 47 (q30 c4) ∷
   rw 47 (q31 c4) ∷
   rw 47 (q32 c4) ∷
   rw 45 (q33 c4) ∷
   re 45 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) ∷
   rw⁻ 46 (q1 c4) ∷
   rw⁻ 49 (q1 c4) ∷
   rw⁻ 52 (q1 c4) ∷
   rw⁻ 55 (q1 c4) ∷
   rw⁻ 59 (q34 c4) ∷
   rw 60 (q35 c4) ∷
   rw⁻ 61 (q36 c4) ∷
   rw⁻ 64 (q36 c4) ∷
   rw⁻ 67 (q36 c4) ∷
   rw⁻ 70 (q36 c4) ∷
   rw 57 (q37 c4) ∷
   rw 57 (q38 c4) ∷
   rw 57 (q39 c4) ∷
   rw 57 (q40 c4) ∷
   rw⁻ 58 (q1 c4) ∷
   rw⁻ 61 (q1 c4) ∷
   rw⁻ 64 (q1 c4) ∷
   rw 67 (q41 c4) ∷
   rw 66 (q42 c4) ∷
   rw 65 (q41 c4) ∷
   rw 67 (q43 c4) ∷
   rw⁻ 68 (q1 c4) ∷
   rw⁻ 71 (q1 c4) ∷
   rw⁻ 74 (q1 c4) ∷
   rw⁻ 77 (q1 c4) ∷
   rw⁻ 78 (q44 c4) ∷
   rw⁻ 75 (q45 c4) ∷
   rw⁻ 72 (q46 c4) ∷
   rw⁻ 69 (q45 c4) ∷
   rw⁻ 66 (q47 c4) ∷
   rw 69 (q1 c4) ∷
   rw 70 (q1 c4) ∷
   rw 71 (q1 c4) ∷
   rw 72 (q1 c4) ∷
   rw⁻ 68 (q43 c4) ∷
   rw 69 (q48 c4) ∷
   rw 68 (q49 c4) ∷
   rw 67 (q48 c4) ∷
   rw⁻ 62 (q50 c4) ∷
   rw 61 (q41 c4) ∷
   rw 60 (q42 c4) ∷
   rw 59 (q41 c4) ∷
   rw 61 (q43 c4) ∷
   rw⁻ 62 (q1 c4) ∷
   rw⁻ 65 (q1 c4) ∷
   rw⁻ 68 (q1 c4) ∷
   rw⁻ 71 (q1 c4) ∷
   rw⁻ 72 (q44 c4) ∷
   rw⁻ 69 (q45 c4) ∷
   rw⁻ 66 (q46 c4) ∷
   rw⁻ 63 (q45 c4) ∷
   rw⁻ 60 (q47 c4) ∷
   rw 63 (q1 c4) ∷
   rw 64 (q1 c4) ∷
   rw 65 (q1 c4) ∷
   rw 66 (q1 c4) ∷
   rw⁻ 62 (q43 c4) ∷
   rw 63 (q48 c4) ∷
   rw 62 (q49 c4) ∷
   rw 61 (q48 c4) ∷
   rw⁻ 56 (q50 c4) ∷
   rw 61 (q1 c4) ∷
   rw 62 (q1 c4) ∷
   rw 63 (q1 c4) ∷
   rw⁻ 60 (q40 c4) ∷
   rw 60 (q51 c4) ∷
   rw 60 (q52 c4) ∷
   rw⁻ 60 (q37 c4) ∷
   rw 60 (q37 c4) ∷
   rw 60 (q38 c4) ∷
   rw 60 (q39 c4) ∷
   rw 60 (q40 c4) ∷
   rw⁻ 61 (q1 c4) ∷
   rw⁻ 64 (q1 c4) ∷
   rw⁻ 67 (q1 c4) ∷
   rw 70 (q41 c4) ∷
   rw 69 (q42 c4) ∷
   rw 68 (q41 c4) ∷
   rw⁻ 69 (q53 c4) ∷
   rw 72 (q48 c4) ∷
   rw 71 (q49 c4) ∷
   rw 70 (q48 c4) ∷
   rw 73 (q41 c4) ∷
   rw 72 (q42 c4) ∷
   rw 71 (q41 c4) ∷
   rw 73 (q43 c4) ∷
   rw⁻ 74 (q1 c4) ∷
   rw⁻ 77 (q1 c4) ∷
   rw⁻ 80 (q1 c4) ∷
   rw⁻ 83 (q1 c4) ∷
   rw⁻ 84 (q54 c4) ∷
   rw⁻ 81 (q55 c4) ∷
   rw⁻ 78 (q56 c4) ∷
   rw⁻ 75 (q55 c4) ∷
   rw⁻ 72 (q57 c4) ∷
   rw 75 (q1 c4) ∷
   rw 76 (q1 c4) ∷
   rw 77 (q1 c4) ∷
   rw 78 (q1 c4) ∷
   rw⁻ 74 (q43 c4) ∷
   rw 75 (q48 c4) ∷
   rw 74 (q49 c4) ∷
   rw 73 (q48 c4) ∷
   rw 76 (q41 c4) ∷
   rw 75 (q42 c4) ∷
   rw 74 (q41 c4) ∷
   rw⁻ 75 (q53 c4) ∷
   rw 78 (q48 c4) ∷
   rw 77 (q49 c4) ∷
   rw 76 (q48 c4) ∷
   rw 79 (q41 c4) ∷
   rw 78 (q42 c4) ∷
   rw 77 (q41 c4) ∷
   rw 80 (q58 c4) ∷
   rw 79 (q59 c4) ∷
   rw 78 (q58 c4) ∷
   rw 81 (q48 c4) ∷
   rw 80 (q49 c4) ∷
   rw 79 (q48 c4) ∷
   rw⁻ 65 (q60 c4) ∷
   rw 64 (q41 c4) ∷
   rw 63 (q42 c4) ∷
   rw 62 (q41 c4) ∷
   rw⁻ 63 (q53 c4) ∷
   rw 66 (q48 c4) ∷
   rw 65 (q49 c4) ∷
   rw 64 (q48 c4) ∷
   rw 67 (q41 c4) ∷
   rw 66 (q42 c4) ∷
   rw 65 (q41 c4) ∷
   rw 67 (q43 c4) ∷
   rw⁻ 68 (q1 c4) ∷
   rw⁻ 71 (q1 c4) ∷
   rw⁻ 74 (q1 c4) ∷
   rw⁻ 77 (q1 c4) ∷
   rw⁻ 78 (q54 c4) ∷
   rw⁻ 75 (q55 c4) ∷
   rw⁻ 72 (q56 c4) ∷
   rw⁻ 69 (q55 c4) ∷
   rw⁻ 66 (q57 c4) ∷
   rw 69 (q1 c4) ∷
   rw 70 (q1 c4) ∷
   rw 71 (q1 c4) ∷
   rw 72 (q1 c4) ∷
   rw⁻ 68 (q43 c4) ∷
   rw 69 (q48 c4) ∷
   rw 68 (q49 c4) ∷
   rw 67 (q48 c4) ∷
   rw 70 (q41 c4) ∷
   rw 69 (q42 c4) ∷
   rw 68 (q41 c4) ∷
   rw⁻ 69 (q53 c4) ∷
   rw 72 (q48 c4) ∷
   rw 71 (q49 c4) ∷
   rw 70 (q48 c4) ∷
   rw 73 (q41 c4) ∷
   rw 72 (q42 c4) ∷
   rw 71 (q41 c4) ∷
   rw 74 (q58 c4) ∷
   rw 73 (q59 c4) ∷
   rw 72 (q58 c4) ∷
   rw 75 (q48 c4) ∷
   rw 74 (q49 c4) ∷
   rw 73 (q48 c4) ∷
   rw⁻ 59 (q60 c4) ∷
   rw 73 (q1 c4) ∷
   rw 74 (q1 c4) ∷
   rw 75 (q1 c4) ∷
   rw⁻ 72 (q40 c4) ∷
   rw 72 (q51 c4) ∷
   rw 72 (q52 c4) ∷
   rw⁻ 72 (q37 c4) ∷
   rw 58 (q36 c4) ∷
   rw 59 (q36 c4) ∷
   rw 60 (q36 c4) ∷
   rw 61 (q36 c4) ∷
   rw⁻ 57 (q35 c4) ∷
   rw 56 (q34 c4) ∷
   rw⁻ 56 (q34 c4) ∷
   rw 57 (q61 c4) ∷
   rw⁻ 58 (q36 c4) ∷
   rw⁻ 61 (q36 c4) ∷
   rw⁻ 64 (q36 c4) ∷
   rw⁻ 67 (q36 c4) ∷
   rw⁻ 55 (q62 c4) ∷
   rw⁻ 54 (q63 c4) ∷
   rw⁻ 53 (q62 c4) ∷
   rw⁻ 57 (q64 c4) ∷
   rw⁻ 58 (q1 c4) ∷
   rw⁻ 61 (q1 c4) ∷
   rw⁻ 62 (q65 c4) ∷
   rw 60 (q66 c4) ∷
   rw⁻ 61 (q1 c4) ∷
   rw⁻ 64 (q1 c4) ∷
   rw⁻ 67 (q1 c4) ∷
   rw⁻ 70 (q1 c4) ∷ []) Eq.refl
