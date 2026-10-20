{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D128 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0404 ; wl0509 ; wl0548 ; wl0549 ; wl0550 ; wl0551 ; wl0552 ; wl0553 ; wl0554 ; wl0555 ; wl0556 ; wl0557 ; wl0558 ; wl0559 ; wl0560 ; wl0561 ; wl0562 ; wl0563 ; wl0564 ; wl0565 ; wl0566 ; wl0567 ; wl0568 ; wl0569 ; wl0570 ; wl0571 ; wp0215 ; wp0216 ; wp0217 ; wp0218 ; wp0219 ; wp0220 ; wp0221 ; wp0222 ; wp0223 ; wp0224 ; wp0225)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0d)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-BOXd-BOX-at0310243142 ; lem-beta-T-at03103441 ; lem-sym23-at0310243241 ; lem-sym23-at03103441 ; lem-sym34-at0310243142 ; lem-sym34-at0310243241)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CCZ124 ∷ X0 ∷ []) (X0 ∷ CCZ124 ∷ []) (wp0225 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb⁻2-0-41-3 ∷ []) (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0549 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (K2⁻ ∷ K2 ∷ []) [] (wl0550 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx⁻3-0412 ∷ []) (Bx3-0412 ∷ []) (lem-BOXd-BOX-at0310243142 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X0 ∷ K2 ∷ []) (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑))
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ134 ∷ K2 ∷ []) (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS02 ∷ X0 ∷ CS34 ∷ X0 ∷ []) (X0 ∷ CS34 ∷ X0 ∷ CS02 ∷ []) (wp0215 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CS02 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ CS02 ∷ []) (wp0216 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS02 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) (X0 ∷ CS13⁻ ∷ X0 ∷ CS02 ∷ []) (wl0552 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS02 ∷ X0 ∷ CS13 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ X0 ∷ CS02 ∷ []) (wl0553 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (X0 ∷ K2⁻ ∷ []) (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑))
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ134 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) (wl0555 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CX30 ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ X0 ∷ CX30 ∷ []) (wp0217 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CS02⁻ ∷ X0 ∷ CS34 ∷ X0 ∷ []) (X0 ∷ CS34 ∷ X0 ∷ CS02⁻ ∷ []) (wp0218 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS02⁻ ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ CS02⁻ ∷ []) (wp0219 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CS02⁻ ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) (X0 ∷ CS13⁻ ∷ X0 ∷ CS02⁻ ∷ []) (wl0556 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS02⁻ ∷ X0 ∷ CS13 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ X0 ∷ CS02⁻ ∷ []) (wl0557 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (X0 ∷ CS23 ∷ []) (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ134 ∷ CS23 ∷ []) (CS23 ∷ CCZ134 ∷ []) (wl0558 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (wl0559 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ []) (X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (wl0561 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (K2 ∷ CS23 ∷ K2⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (wl0562 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl0563 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ []) (X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0564 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0565 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wp0220 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (K2 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ K2 ∷ []) (wp0221 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CX03 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ CX03 ∷ []) (wp0222 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (K2⁻ ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ K2⁻ ∷ []) (wp0223 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS12⁻ ∷ X0 ∷ []) (X0 ∷ CS12⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0566 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0567 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ []) (X0 ∷ K2 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0568 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (K2 ∷ CS23⁻ ∷ K2⁻ ∷ X0 ∷ []) (X0 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ []) (wl0569 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (K2 ∷ CS23⁻ ∷ K2⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ []) (wl0570 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ []) (X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) (wp0224 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Toff203 ∷ X0 ∷ CS02⁻ ∷ X0 ∷ []) (X0 ∷ CS02⁻ ∷ X0 ∷ Toff203 ∷ []) (wl0571 (lit c4))

-- F1 CS-K1 part4: 297 steps
lem-F1-CS-K1-part4 : Ws → ⟪ (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ X0 ∷ CCZ124 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ X0 ∷ K2 ∷ CCZ124 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ
lem-F1-CS-K1-part4 c4 = derive (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ X0 ∷ CCZ124 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ X0 ∷ K2 ∷ CCZ124 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  (rw⁻ 37 (q1 c4) ∷
   rw 39 (q2 c4) ∷
   re 39 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) ∷
   rw⁻ 40 (q3 c4) ∷
   rw⁻ 43 (q3 c4) ∷
   rw⁻ 46 (q3 c4) ∷
   rw⁻ 49 (q3 c4) ∷
   rw⁻ 53 (q4 c4) ∷
   rw 54 (q5 c4) ∷
   rw⁻ 55 (q6 c4) ∷
   rw⁻ 58 (q6 c4) ∷
   rw⁻ 61 (q6 c4) ∷
   rw⁻ 64 (q6 c4) ∷
   rw 51 (q7 c4) ∷
   rw 51 (q8 c4) ∷
   rw 51 (q9 c4) ∷
   rw 51 (q10 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw⁻ 55 (q3 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw 61 (q11 c4) ∷
   rw 60 (q12 c4) ∷
   rw 59 (q11 c4) ∷
   rw 61 (q13 c4) ∷
   rw⁻ 62 (q3 c4) ∷
   rw⁻ 65 (q3 c4) ∷
   rw⁻ 68 (q3 c4) ∷
   rw⁻ 71 (q3 c4) ∷
   rw⁻ 72 (q14 c4) ∷
   rw⁻ 69 (q15 c4) ∷
   rw⁻ 66 (q16 c4) ∷
   rw⁻ 63 (q15 c4) ∷
   rw⁻ 60 (q17 c4) ∷
   rw 63 (q3 c4) ∷
   rw 64 (q3 c4) ∷
   rw 65 (q3 c4) ∷
   rw 66 (q3 c4) ∷
   rw⁻ 62 (q13 c4) ∷
   rw 63 (q18 c4) ∷
   rw 62 (q19 c4) ∷
   rw 61 (q18 c4) ∷
   rw⁻ 56 (q20 c4) ∷
   rw 55 (q11 c4) ∷
   rw 54 (q12 c4) ∷
   rw 53 (q11 c4) ∷
   rw 55 (q13 c4) ∷
   rw⁻ 56 (q3 c4) ∷
   rw⁻ 59 (q3 c4) ∷
   rw⁻ 62 (q3 c4) ∷
   rw⁻ 65 (q3 c4) ∷
   rw⁻ 66 (q14 c4) ∷
   rw⁻ 63 (q15 c4) ∷
   rw⁻ 60 (q16 c4) ∷
   rw⁻ 57 (q15 c4) ∷
   rw⁻ 54 (q17 c4) ∷
   rw 57 (q3 c4) ∷
   rw 58 (q3 c4) ∷
   rw 59 (q3 c4) ∷
   rw 60 (q3 c4) ∷
   rw⁻ 56 (q13 c4) ∷
   rw 57 (q18 c4) ∷
   rw 56 (q19 c4) ∷
   rw 55 (q18 c4) ∷
   rw⁻ 50 (q20 c4) ∷
   rw 55 (q3 c4) ∷
   rw 56 (q3 c4) ∷
   rw 57 (q3 c4) ∷
   rw⁻ 54 (q10 c4) ∷
   rw 54 (q21 c4) ∷
   rw 54 (q22 c4) ∷
   rw⁻ 54 (q7 c4) ∷
   rw 54 (q7 c4) ∷
   rw 54 (q8 c4) ∷
   rw 54 (q9 c4) ∷
   rw 54 (q10 c4) ∷
   rw⁻ 55 (q3 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw 64 (q11 c4) ∷
   rw 63 (q12 c4) ∷
   rw 62 (q11 c4) ∷
   rw⁻ 63 (q23 c4) ∷
   rw 66 (q18 c4) ∷
   rw 65 (q19 c4) ∷
   rw 64 (q18 c4) ∷
   rw 67 (q11 c4) ∷
   rw 66 (q12 c4) ∷
   rw 65 (q11 c4) ∷
   rw 67 (q13 c4) ∷
   rw⁻ 68 (q3 c4) ∷
   rw⁻ 71 (q3 c4) ∷
   rw⁻ 74 (q3 c4) ∷
   rw⁻ 77 (q3 c4) ∷
   rw⁻ 78 (q24 c4) ∷
   rw⁻ 75 (q25 c4) ∷
   rw⁻ 72 (q26 c4) ∷
   rw⁻ 69 (q25 c4) ∷
   rw⁻ 66 (q27 c4) ∷
   rw 69 (q3 c4) ∷
   rw 70 (q3 c4) ∷
   rw 71 (q3 c4) ∷
   rw 72 (q3 c4) ∷
   rw⁻ 68 (q13 c4) ∷
   rw 69 (q18 c4) ∷
   rw 68 (q19 c4) ∷
   rw 67 (q18 c4) ∷
   rw 70 (q11 c4) ∷
   rw 69 (q12 c4) ∷
   rw 68 (q11 c4) ∷
   rw⁻ 69 (q23 c4) ∷
   rw 72 (q18 c4) ∷
   rw 71 (q19 c4) ∷
   rw 70 (q18 c4) ∷
   rw 73 (q11 c4) ∷
   rw 72 (q12 c4) ∷
   rw 71 (q11 c4) ∷
   rw 74 (q28 c4) ∷
   rw 73 (q29 c4) ∷
   rw 72 (q28 c4) ∷
   rw 75 (q18 c4) ∷
   rw 74 (q19 c4) ∷
   rw 73 (q18 c4) ∷
   rw⁻ 59 (q30 c4) ∷
   rw 58 (q11 c4) ∷
   rw 57 (q12 c4) ∷
   rw 56 (q11 c4) ∷
   rw⁻ 57 (q23 c4) ∷
   rw 60 (q18 c4) ∷
   rw 59 (q19 c4) ∷
   rw 58 (q18 c4) ∷
   rw 61 (q11 c4) ∷
   rw 60 (q12 c4) ∷
   rw 59 (q11 c4) ∷
   rw 61 (q13 c4) ∷
   rw⁻ 62 (q3 c4) ∷
   rw⁻ 65 (q3 c4) ∷
   rw⁻ 68 (q3 c4) ∷
   rw⁻ 71 (q3 c4) ∷
   rw⁻ 72 (q24 c4) ∷
   rw⁻ 69 (q25 c4) ∷
   rw⁻ 66 (q26 c4) ∷
   rw⁻ 63 (q25 c4) ∷
   rw⁻ 60 (q27 c4) ∷
   rw 63 (q3 c4) ∷
   rw 64 (q3 c4) ∷
   rw 65 (q3 c4) ∷
   rw 66 (q3 c4) ∷
   rw⁻ 62 (q13 c4) ∷
   rw 63 (q18 c4) ∷
   rw 62 (q19 c4) ∷
   rw 61 (q18 c4) ∷
   rw 64 (q11 c4) ∷
   rw 63 (q12 c4) ∷
   rw 62 (q11 c4) ∷
   rw⁻ 63 (q23 c4) ∷
   rw 66 (q18 c4) ∷
   rw 65 (q19 c4) ∷
   rw 64 (q18 c4) ∷
   rw 67 (q11 c4) ∷
   rw 66 (q12 c4) ∷
   rw 65 (q11 c4) ∷
   rw 68 (q28 c4) ∷
   rw 67 (q29 c4) ∷
   rw 66 (q28 c4) ∷
   rw 69 (q18 c4) ∷
   rw 68 (q19 c4) ∷
   rw 67 (q18 c4) ∷
   rw⁻ 53 (q30 c4) ∷
   rw 67 (q3 c4) ∷
   rw 68 (q3 c4) ∷
   rw 69 (q3 c4) ∷
   rw⁻ 66 (q10 c4) ∷
   rw 66 (q21 c4) ∷
   rw 66 (q22 c4) ∷
   rw⁻ 66 (q7 c4) ∷
   rw 52 (q6 c4) ∷
   rw 53 (q6 c4) ∷
   rw 54 (q6 c4) ∷
   rw 55 (q6 c4) ∷
   rw⁻ 51 (q5 c4) ∷
   rw 50 (q4 c4) ∷
   rw⁻ 50 (q4 c4) ∷
   rw 51 (q31 c4) ∷
   rw⁻ 52 (q6 c4) ∷
   rw⁻ 55 (q6 c4) ∷
   rw⁻ 58 (q6 c4) ∷
   rw⁻ 61 (q6 c4) ∷
   rw⁻ 49 (q32 c4) ∷
   rw⁻ 48 (q33 c4) ∷
   rw⁻ 47 (q32 c4) ∷
   rw⁻ 51 (q34 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw⁻ 55 (q3 c4) ∷
   rw⁻ 56 (q35 c4) ∷
   rw 54 (q36 c4) ∷
   rw⁻ 55 (q3 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw⁻ 64 (q3 c4) ∷
   rw⁻ 65 (q37 c4) ∷
   rw⁻ 62 (q38 c4) ∷
   rw⁻ 63 (q39 c4) ∷
   rw⁻ 64 (q40 c4) ∷
   rw⁻ 59 (q41 c4) ∷
   rw⁻ 56 (q38 c4) ∷
   rw⁻ 57 (q39 c4) ∷
   rw⁻ 58 (q40 c4) ∷
   rw⁻ 53 (q42 c4) ∷
   rw 58 (q3 c4) ∷
   rw 59 (q3 c4) ∷
   rw 60 (q3 c4) ∷
   rw 61 (q3 c4) ∷
   rw⁻ 57 (q36 c4) ∷
   rw⁻ 50 (q43 c4) ∷
   rw 55 (q3 c4) ∷
   rw 56 (q3 c4) ∷
   rw 54 (q34 c4) ∷
   rw⁻ 55 (q44 c4) ∷
   rw⁻ 54 (q45 c4) ∷
   rw⁻ 53 (q44 c4) ∷
   rw⁻ 57 (q34 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw⁻ 62 (q35 c4) ∷
   rw 60 (q36 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw⁻ 64 (q3 c4) ∷
   rw⁻ 67 (q3 c4) ∷
   rw⁻ 70 (q3 c4) ∷
   rw⁻ 71 (q37 c4) ∷
   rw⁻ 68 (q38 c4) ∷
   rw⁻ 69 (q39 c4) ∷
   rw⁻ 70 (q40 c4) ∷
   rw⁻ 65 (q41 c4) ∷
   rw⁻ 62 (q38 c4) ∷
   rw⁻ 63 (q39 c4) ∷
   rw⁻ 64 (q40 c4) ∷
   rw⁻ 59 (q42 c4) ∷
   rw 64 (q3 c4) ∷
   rw 65 (q3 c4) ∷
   rw 66 (q3 c4) ∷
   rw 67 (q3 c4) ∷
   rw⁻ 63 (q36 c4) ∷
   rw⁻ 56 (q43 c4) ∷
   rw 61 (q3 c4) ∷
   rw 62 (q3 c4) ∷
   rw 60 (q34 c4) ∷
   rw⁻ 59 (q46 c4) ∷
   rw 49 (q6 c4) ∷
   rw 50 (q6 c4) ∷
   rw 51 (q6 c4) ∷
   rw 52 (q6 c4) ∷
   rw⁻ 48 (q31 c4) ∷
   rw 47 (q4 c4) ∷
   re 45 1 (CS02⁻ ∷ []) ∷
   rw⁻ 44 (q47 c4) ∷
   re 46 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 44 (q4 c4) ∷
   rw 45 (q31 c4) ∷
   rw⁻ 46 (q6 c4) ∷
   rw⁻ 49 (q6 c4) ∷
   rw⁻ 52 (q6 c4) ∷
   rw⁻ 55 (q6 c4) ∷
   rw⁻ 43 (q32 c4) ∷
   rw⁻ 42 (q33 c4) ∷
   rw⁻ 41 (q32 c4) ∷
   rw⁻ 45 (q34 c4) ∷
   rw⁻ 46 (q3 c4) ∷
   rw⁻ 49 (q3 c4) ∷
   rw⁻ 50 (q35 c4) ∷
   rw 48 (q36 c4) ∷
   rw⁻ 49 (q3 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw⁻ 55 (q3 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 59 (q37 c4) ∷
   rw⁻ 56 (q38 c4) ∷
   rw⁻ 57 (q39 c4) ∷
   rw⁻ 58 (q40 c4) ∷
   rw⁻ 53 (q41 c4) ∷
   rw⁻ 50 (q38 c4) ∷
   rw⁻ 51 (q39 c4) ∷
   rw⁻ 52 (q40 c4) ∷
   rw⁻ 47 (q42 c4) ∷
   rw 52 (q3 c4) ∷
   rw 53 (q3 c4) ∷
   rw 54 (q3 c4) ∷
   rw 55 (q3 c4) ∷
   rw⁻ 51 (q36 c4) ∷
   rw⁻ 44 (q43 c4) ∷
   rw 49 (q3 c4) ∷
   rw 50 (q3 c4) ∷
   rw 48 (q34 c4) ∷
   rw⁻ 49 (q44 c4) ∷
   rw⁻ 48 (q45 c4) ∷
   rw⁻ 47 (q44 c4) ∷
   rw⁻ 51 (q34 c4) ∷ []) Eq.refl
