{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D096 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0393 ; wl0509 ; wl0510 ; wl0511 ; wl0512 ; wl0535 ; wl0536 ; wl0537 ; wl0538 ; wl0539 ; wl0540 ; wl0541 ; wl0542 ; wl0543 ; wl0548 ; wl0550 ; wl0560 ; wl0563 ; wl0564 ; wl0565 ; wl0566 ; wl0567 ; wl0568 ; wl0572 ; wl0573 ; wp0190 ; wp0191 ; wp0208 ; wp0209 ; wp0210 ; wp0211 ; wp0220 ; wp0221 ; wp0222 ; wp0223 ; wp0224 ; wp0225)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0d)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0210243143)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ []) (X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0564 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0565 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wp0220 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (K2 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ K2 ∷ []) (wp0221 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CX03 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ CX03 ∷ []) (wp0222 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (K2⁻ ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ K2⁻ ∷ []) (wp0223 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS12⁻ ∷ X0 ∷ []) (X0 ∷ CS12⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0566 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0567 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ []) (X0 ∷ K2 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0568 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl0563 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ []) (X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) (wp0224 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (K2⁻ ∷ K2 ∷ []) [] (wl0550 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Toff203 ∷ X0 ∷ CS02 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ X0 ∷ Toff203 ∷ []) (wl0572 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sb⁻2-0-41-3 ∷ []) (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ124 ∷ X0 ∷ []) (X0 ∷ CCZ124 ∷ []) (wp0225 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Sb⁻2-0-41-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0210243143 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CK01⁻ ∷ []) (CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ []) (wl0535 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
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
  q44 c4 = eqn (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) (wl0510 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) (wp0190 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) (wp0191 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0 ∷ []) (wl0512 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (S0 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0 ∷ []) (wl0511 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (X0 ∷ ι⁻ ∷ []) (ι⁻ ∷ X0 ∷ []) (zc⁻)
  q50 : Ws → Eqn
  q50 c4 = eqn (Sb⁻2-0-41-3 ∷ ι⁻ ∷ []) (ι⁻ ∷ Sb⁻2-0-41-3 ∷ []) (zc⁻)
  q51 : Ws → Eqn
  q51 c4 = eqn (CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ []) (wl0573 (lit c4))

-- F1 CS-K1 [rhs shape] part5: 359 steps
lem-F1-CS-K1-rhs-shape-part5 : Ws → ⟪ (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ X0 ∷ K2 ∷ CCZ124 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-rhs-shape-part5 c4 = derive (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ X0 ∷ K2 ∷ CCZ124 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 52 (q1 c4) ∷
   rw⁻ 55 (q1 c4) ∷
   rw⁻ 56 (q2 c4) ∷
   rw 54 (q3 c4) ∷
   rw⁻ 55 (q1 c4) ∷
   rw⁻ 58 (q1 c4) ∷
   rw⁻ 61 (q1 c4) ∷
   rw⁻ 64 (q1 c4) ∷
   rw⁻ 65 (q4 c4) ∷
   rw⁻ 62 (q5 c4) ∷
   rw⁻ 63 (q6 c4) ∷
   rw⁻ 64 (q7 c4) ∷
   rw⁻ 59 (q8 c4) ∷
   rw⁻ 56 (q5 c4) ∷
   rw⁻ 57 (q6 c4) ∷
   rw⁻ 58 (q7 c4) ∷
   rw⁻ 53 (q9 c4) ∷
   rw 58 (q1 c4) ∷
   rw 59 (q1 c4) ∷
   rw 60 (q1 c4) ∷
   rw 61 (q1 c4) ∷
   rw⁻ 57 (q3 c4) ∷
   rw⁻ 50 (q10 c4) ∷
   rw 55 (q1 c4) ∷
   rw 56 (q1 c4) ∷
   rw 54 (q11 c4) ∷
   rw⁻ 53 (q12 c4) ∷
   rw 43 (q13 c4) ∷
   rw 44 (q13 c4) ∷
   rw 45 (q13 c4) ∷
   rw 46 (q13 c4) ∷
   rw⁻ 42 (q14 c4) ∷
   rw 41 (q15 c4) ∷
   re 39 1 (CS02 ∷ []) ∷
   rw⁻ 38 (q16 c4) ∷
   re 40 1 (Sb3-0-2-1 ∷ []) ∷
   rw 41 (q1 c4) ∷
   rw 42 (q1 c4) ∷
   rw 43 (q1 c4) ∷
   rw 44 (q1 c4) ∷
   re 40 5 (Sb⁻3-0-41-2 ∷ []) ∷
   rw⁻ 40 (q17 c4) ∷
   rw⁻ 41 (q18 c4) ∷
   rw 40 (q19 c4) ∷
   rw⁻ 39 (q18 c4) ∷
   rw⁻ 36 (q20 c4) ∷
   rw 36 (q21 c4) ∷
   rw 36 (q22 c4) ∷
   rw⁻ 36 (q23 c4) ∷
   re 32 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 42 (q24 c4) ∷
   re 40 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 41 (q1 c4) ∷
   rw⁻ 44 (q1 c4) ∷
   rw⁻ 47 (q1 c4) ∷
   rw⁻ 50 (q1 c4) ∷
   rw 52 (q23 c4) ∷
   rw 52 (q25 c4) ∷
   rw⁻ 53 (q1 c4) ∷
   rw⁻ 56 (q1 c4) ∷
   rw⁻ 59 (q1 c4) ∷
   rw⁻ 60 (q26 c4) ∷
   rw⁻ 57 (q27 c4) ∷
   rw⁻ 54 (q26 c4) ∷
   rw⁻ 51 (q27 c4) ∷
   rw 54 (q1 c4) ∷
   rw 55 (q1 c4) ∷
   rw 56 (q1 c4) ∷
   rw⁻ 53 (q25 c4) ∷
   rw⁻ 53 (q23 c4) ∷
   rw⁻ 48 (q28 c4) ∷
   re 46 1 (CS03⁻ ∷ []) ∷
   rw⁻ 45 (q29 c4) ∷
   re 47 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 42 (q28 c4) ∷
   re 40 1 (CS03 ∷ []) ∷
   rw⁻ 39 (q30 c4) ∷
   re 41 1 (Sb2-0-3-1 ∷ []) ∷
   rw 42 (q1 c4) ∷
   rw 43 (q1 c4) ∷
   rw 44 (q1 c4) ∷
   rw 45 (q1 c4) ∷
   re 41 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 41 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 42 (q1 c4) ∷
   rw⁻ 45 (q1 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw 53 (q23 c4) ∷
   rw 53 (q31 c4) ∷
   rw 53 (q32 c4) ∷
   rw⁻ 54 (q1 c4) ∷
   rw⁻ 57 (q1 c4) ∷
   rw⁻ 60 (q1 c4) ∷
   rw 63 (q33 c4) ∷
   rw⁻ 62 (q34 c4) ∷
   rw 61 (q33 c4) ∷
   rw 63 (q35 c4) ∷
   rw⁻ 64 (q1 c4) ∷
   rw⁻ 67 (q1 c4) ∷
   rw⁻ 70 (q1 c4) ∷
   rw⁻ 73 (q1 c4) ∷
   rw⁻ 74 (q36 c4) ∷
   rw⁻ 71 (q37 c4) ∷
   rw⁻ 68 (q38 c4) ∷
   rw⁻ 65 (q37 c4) ∷
   rw⁻ 62 (q39 c4) ∷
   rw 65 (q1 c4) ∷
   rw 66 (q1 c4) ∷
   rw 67 (q1 c4) ∷
   rw 68 (q1 c4) ∷
   rw⁻ 64 (q35 c4) ∷
   rw 65 (q33 c4) ∷
   rw⁻ 64 (q34 c4) ∷
   rw 63 (q33 c4) ∷
   rw⁻ 58 (q40 c4) ∷
   rw 57 (q33 c4) ∷
   rw⁻ 56 (q34 c4) ∷
   rw 55 (q33 c4) ∷
   rw 57 (q35 c4) ∷
   rw⁻ 58 (q1 c4) ∷
   rw⁻ 61 (q1 c4) ∷
   rw⁻ 64 (q1 c4) ∷
   rw⁻ 67 (q1 c4) ∷
   rw⁻ 68 (q36 c4) ∷
   rw⁻ 65 (q37 c4) ∷
   rw⁻ 62 (q38 c4) ∷
   rw⁻ 59 (q37 c4) ∷
   rw⁻ 56 (q39 c4) ∷
   rw 59 (q1 c4) ∷
   rw 60 (q1 c4) ∷
   rw 61 (q1 c4) ∷
   rw 62 (q1 c4) ∷
   rw⁻ 58 (q35 c4) ∷
   rw 59 (q33 c4) ∷
   rw⁻ 58 (q34 c4) ∷
   rw 57 (q33 c4) ∷
   rw⁻ 52 (q40 c4) ∷
   rw 57 (q1 c4) ∷
   rw 58 (q1 c4) ∷
   rw 59 (q1 c4) ∷
   rw⁻ 56 (q32 c4) ∷
   rw 56 (q41 c4) ∷
   rw⁻ 56 (q23 c4) ∷
   re 47 1 (CS03⁻ ∷ []) ∷
   rw⁻ 43 (q42 c4) ∷
   re 50 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 41 1 (CS03 ∷ []) ∷
   rw⁻ 40 (q43 c4) ∷
   re 44 1 (Sb2-0-3-1 ∷ []) ∷
   rw 45 (q1 c4) ∷
   rw 46 (q1 c4) ∷
   rw 47 (q1 c4) ∷
   rw 48 (q1 c4) ∷
   re 44 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 44 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 45 (q1 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw⁻ 54 (q1 c4) ∷
   rw 56 (q23 c4) ∷
   rw 56 (q25 c4) ∷
   rw⁻ 57 (q1 c4) ∷
   rw⁻ 60 (q1 c4) ∷
   rw⁻ 63 (q1 c4) ∷
   rw⁻ 64 (q26 c4) ∷
   rw⁻ 61 (q27 c4) ∷
   rw⁻ 58 (q26 c4) ∷
   rw⁻ 55 (q27 c4) ∷
   rw 58 (q1 c4) ∷
   rw 59 (q1 c4) ∷
   rw 60 (q1 c4) ∷
   rw⁻ 57 (q25 c4) ∷
   rw⁻ 57 (q23 c4) ∷
   rw⁻ 52 (q28 c4) ∷
   re 50 1 (CS03⁻ ∷ []) ∷
   rw⁻ 49 (q29 c4) ∷
   re 51 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 46 (q28 c4) ∷
   re 44 1 (CS03 ∷ []) ∷
   rw⁻ 43 (q30 c4) ∷
   re 45 1 (Sb2-0-3-1 ∷ []) ∷
   rw 46 (q1 c4) ∷
   rw 47 (q1 c4) ∷
   rw 48 (q1 c4) ∷
   rw 49 (q1 c4) ∷
   re 45 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 45 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 46 (q1 c4) ∷
   rw⁻ 49 (q1 c4) ∷
   rw⁻ 52 (q1 c4) ∷
   rw⁻ 55 (q1 c4) ∷
   rw 57 (q23 c4) ∷
   rw 57 (q25 c4) ∷
   rw⁻ 58 (q1 c4) ∷
   rw⁻ 61 (q1 c4) ∷
   rw⁻ 64 (q1 c4) ∷
   rw⁻ 65 (q44 c4) ∷
   rw⁻ 62 (q45 c4) ∷
   rw⁻ 59 (q44 c4) ∷
   rw⁻ 56 (q45 c4) ∷
   rw 59 (q1 c4) ∷
   rw 60 (q1 c4) ∷
   rw 61 (q1 c4) ∷
   rw⁻ 58 (q25 c4) ∷
   rw⁻ 58 (q23 c4) ∷
   rw⁻ 53 (q46 c4) ∷
   re 51 1 (CS03⁻ ∷ []) ∷
   rw⁻ 50 (q47 c4) ∷
   re 52 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 47 (q46 c4) ∷
   re 45 1 (CS03 ∷ []) ∷
   rw⁻ 44 (q48 c4) ∷
   re 46 1 (Sb2-0-3-1 ∷ []) ∷
   rw 47 (q1 c4) ∷
   rw 48 (q1 c4) ∷
   rw 49 (q1 c4) ∷
   rw 50 (q1 c4) ∷
   re 46 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 47 (q49 c4) ∷
   rw 46 (q50 c4) ∷
   rw 45 (q49 c4) ∷
   rw⁻ 39 (q24 c4) ∷
   rw⁻ 36 (q51 c4) ∷
   rw 36 (q24 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   rw⁻ 44 (q1 c4) ∷
   rw 46 (q23 c4) ∷
   rw 46 (q25 c4) ∷
   rw⁻ 47 (q1 c4) ∷
   rw⁻ 50 (q1 c4) ∷
   rw⁻ 53 (q1 c4) ∷
   rw⁻ 54 (q26 c4) ∷
   rw⁻ 51 (q27 c4) ∷
   rw⁻ 48 (q26 c4) ∷
   rw⁻ 45 (q27 c4) ∷
   rw 48 (q1 c4) ∷
   rw 49 (q1 c4) ∷
   rw 50 (q1 c4) ∷
   rw⁻ 47 (q25 c4) ∷
   rw⁻ 47 (q23 c4) ∷
   rw⁻ 42 (q28 c4) ∷
   re 40 1 (CS03⁻ ∷ []) ∷
   rw⁻ 39 (q29 c4) ∷
   re 41 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 36 (q28 c4) ∷
   re 34 1 (CS03 ∷ []) ∷
   rw⁻ 33 (q30 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ []) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   re 35 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 35 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw⁻ 45 (q1 c4) ∷
   rw 47 (q23 c4) ∷
   rw 47 (q31 c4) ∷
   rw 47 (q32 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw⁻ 54 (q1 c4) ∷
   rw 57 (q33 c4) ∷
   rw⁻ 56 (q34 c4) ∷
   rw 55 (q33 c4) ∷
   rw 57 (q35 c4) ∷
   rw⁻ 58 (q1 c4) ∷
   rw⁻ 61 (q1 c4) ∷
   rw⁻ 64 (q1 c4) ∷
   rw⁻ 67 (q1 c4) ∷
   rw⁻ 68 (q36 c4) ∷
   rw⁻ 65 (q37 c4) ∷
   rw⁻ 62 (q38 c4) ∷
   rw⁻ 59 (q37 c4) ∷
   rw⁻ 56 (q39 c4) ∷
   rw 59 (q1 c4) ∷
   rw 60 (q1 c4) ∷
   rw 61 (q1 c4) ∷
   rw 62 (q1 c4) ∷
   rw⁻ 58 (q35 c4) ∷
   rw 59 (q33 c4) ∷
   rw⁻ 58 (q34 c4) ∷
   rw 57 (q33 c4) ∷
   rw⁻ 52 (q40 c4) ∷
   rw 51 (q33 c4) ∷
   rw⁻ 50 (q34 c4) ∷
   rw 49 (q33 c4) ∷
   rw 51 (q35 c4) ∷
   rw⁻ 52 (q1 c4) ∷
   rw⁻ 55 (q1 c4) ∷
   rw⁻ 58 (q1 c4) ∷
   rw⁻ 61 (q1 c4) ∷
   rw⁻ 62 (q36 c4) ∷
   rw⁻ 59 (q37 c4) ∷
   rw⁻ 56 (q38 c4) ∷
   rw⁻ 53 (q37 c4) ∷
   rw⁻ 50 (q39 c4) ∷
   rw 53 (q1 c4) ∷
   rw 54 (q1 c4) ∷
   rw 55 (q1 c4) ∷
   rw 56 (q1 c4) ∷
   rw⁻ 52 (q35 c4) ∷
   rw 53 (q33 c4) ∷
   rw⁻ 52 (q34 c4) ∷
   rw 51 (q33 c4) ∷
   rw⁻ 46 (q40 c4) ∷
   rw 51 (q1 c4) ∷
   rw 52 (q1 c4) ∷
   rw 53 (q1 c4) ∷
   rw⁻ 50 (q32 c4) ∷
   rw 50 (q41 c4) ∷
   rw⁻ 50 (q23 c4) ∷
   re 41 1 (CS03⁻ ∷ []) ∷
   rw⁻ 37 (q42 c4) ∷
   re 44 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 35 1 (CS03 ∷ []) ∷
   rw⁻ 34 (q43 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ []) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   rw 42 (q1 c4) ∷
   re 38 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 38 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw⁻ 45 (q1 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw 50 (q23 c4) ∷
   rw 50 (q25 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw⁻ 54 (q1 c4) ∷
   rw⁻ 57 (q1 c4) ∷
   rw⁻ 58 (q26 c4) ∷
   rw⁻ 55 (q27 c4) ∷
   rw⁻ 52 (q26 c4) ∷
   rw⁻ 49 (q27 c4) ∷
   rw 52 (q1 c4) ∷
   rw 53 (q1 c4) ∷
   rw 54 (q1 c4) ∷
   rw⁻ 51 (q25 c4) ∷
   rw⁻ 51 (q23 c4) ∷
   rw⁻ 46 (q28 c4) ∷
   re 44 1 (CS03⁻ ∷ []) ∷
   rw⁻ 43 (q29 c4) ∷
   re 45 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 40 (q28 c4) ∷
   re 38 1 (CS03 ∷ []) ∷
   rw⁻ 37 (q30 c4) ∷
   re 39 1 (Sb2-0-3-1 ∷ []) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   rw 42 (q1 c4) ∷ []) Eq.refl
