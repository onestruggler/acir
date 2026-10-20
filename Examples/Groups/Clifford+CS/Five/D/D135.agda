{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D135 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0433 ; wl0509 ; wl0510 ; wl0511 ; wl0512 ; wl0515 ; wl0525 ; wl0526 ; wl0527 ; wl0548 ; wl0550 ; wl0560 ; wl0563 ; wl0564 ; wl0565 ; wl0566 ; wl0567 ; wl0568 ; wl0572 ; wl0574 ; wp0190 ; wp0191 ; wp0198 ; wp0199 ; wp0220 ; wp0221 ; wp0222 ; wp0223 ; wp0224 ; wp0225 ; wp0226 ; wp0227 ; wp0228 ; wp0229 ; wp0230 ; wp0231 ; wp0232 ; wp0233 ; wp0234 ; wp0235 ; wp0236)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0d)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0210243143)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ []) (X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) (wl0564 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0565 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
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
  q24 c4 = eqn (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (wp0226 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS04 ∷ X0 ∷ CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ X0 ∷ CS04 ∷ []) (wp0227 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CS04 ∷ X0 ∷ CX13 ∷ X0 ∷ []) (X0 ∷ CX13 ∷ X0 ∷ CS04 ∷ []) (wp0228 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS04 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS04 ∷ []) (wp0229 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CS04 ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS04 ∷ []) (wp0230 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CS04 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS04 ∷ []) (wp0231 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CS04 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS04 ∷ []) (wp0232 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CS04 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS04 ∷ []) (wp0233 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CS04 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS04 ∷ []) (wp0234 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CS04 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ CS04 ∷ []) (wp0235 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (S0⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ S0⁻ ∷ []) (wp0236 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (S0⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) (wl0525 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) (wp0198 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (S0⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) (wp0199 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (S0⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0⁻ ∷ []) (wl0527 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (S0⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0⁻ ∷ []) (wl0526 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (S0⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ S0⁻ ∷ []) (wl0574 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0 ∷ []) (wl0512 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) (wp0191 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (S0 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0 ∷ []) (wl0511 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) (wl0510 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) (wp0190 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (wl0515 (lit c4))

-- F1 CS-K1 part11: 381 steps
lem-F1-CS-K1-part11 : Ws → ⟪ (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ X0 ∷ CCZ124 ∷ X0 ∷ X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ
lem-F1-CS-K1-part11 c4 = derive (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ X0 ∷ CCZ124 ∷ X0 ∷ X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  (rw⁻ 58 (q1 c4) ∷
   rw 56 (q2 c4) ∷
   rw⁻ 57 (q3 c4) ∷
   rw⁻ 60 (q3 c4) ∷
   rw⁻ 63 (q3 c4) ∷
   rw⁻ 66 (q3 c4) ∷
   rw⁻ 67 (q4 c4) ∷
   rw⁻ 64 (q5 c4) ∷
   rw⁻ 65 (q6 c4) ∷
   rw⁻ 66 (q7 c4) ∷
   rw⁻ 61 (q8 c4) ∷
   rw⁻ 58 (q5 c4) ∷
   rw⁻ 59 (q6 c4) ∷
   rw⁻ 60 (q7 c4) ∷
   rw⁻ 55 (q9 c4) ∷
   rw 60 (q3 c4) ∷
   rw 61 (q3 c4) ∷
   rw 62 (q3 c4) ∷
   rw 63 (q3 c4) ∷
   rw⁻ 59 (q2 c4) ∷
   rw⁻ 52 (q10 c4) ∷
   rw 57 (q3 c4) ∷
   rw 58 (q3 c4) ∷
   rw 56 (q11 c4) ∷
   rw⁻ 55 (q12 c4) ∷
   rw 45 (q13 c4) ∷
   rw 46 (q13 c4) ∷
   rw 47 (q13 c4) ∷
   rw 48 (q13 c4) ∷
   rw⁻ 44 (q14 c4) ∷
   rw 43 (q15 c4) ∷
   re 41 1 (CS02 ∷ []) ∷
   rw⁻ 40 (q16 c4) ∷
   re 42 1 (Sb3-0-2-1 ∷ []) ∷
   rw 43 (q3 c4) ∷
   rw 44 (q3 c4) ∷
   rw 45 (q3 c4) ∷
   rw 46 (q3 c4) ∷
   re 42 5 (Sb⁻3-0-41-2 ∷ []) ∷
   rw⁻ 42 (q17 c4) ∷
   rw⁻ 43 (q18 c4) ∷
   rw 42 (q19 c4) ∷
   rw⁻ 41 (q18 c4) ∷
   rw⁻ 38 (q20 c4) ∷
   rw 38 (q21 c4) ∷
   rw 38 (q22 c4) ∷
   rw⁻ 38 (q23 c4) ∷
   re 34 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 50 (q24 c4) ∷
   re 48 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 49 (q3 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw⁻ 55 (q3 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw 60 (q23 c4) ∷
   rw 60 (q25 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw⁻ 64 (q3 c4) ∷
   rw⁻ 67 (q3 c4) ∷
   rw 69 (q26 c4) ∷
   rw⁻ 70 (q3 c4) ∷
   rw⁻ 73 (q3 c4) ∷
   rw⁻ 76 (q3 c4) ∷
   rw⁻ 79 (q3 c4) ∷
   rw⁻ 80 (q27 c4) ∷
   rw⁻ 77 (q28 c4) ∷
   rw⁻ 74 (q29 c4) ∷
   rw⁻ 71 (q28 c4) ∷
   rw⁻ 68 (q30 c4) ∷
   rw 71 (q3 c4) ∷
   rw 72 (q3 c4) ∷
   rw 73 (q3 c4) ∷
   rw 74 (q3 c4) ∷
   rw⁻ 70 (q26 c4) ∷
   rw⁻ 65 (q31 c4) ∷
   rw 63 (q26 c4) ∷
   rw⁻ 64 (q3 c4) ∷
   rw⁻ 67 (q3 c4) ∷
   rw⁻ 70 (q3 c4) ∷
   rw⁻ 73 (q3 c4) ∷
   rw⁻ 74 (q27 c4) ∷
   rw⁻ 71 (q28 c4) ∷
   rw⁻ 68 (q29 c4) ∷
   rw⁻ 65 (q28 c4) ∷
   rw⁻ 62 (q30 c4) ∷
   rw 65 (q3 c4) ∷
   rw 66 (q3 c4) ∷
   rw 67 (q3 c4) ∷
   rw 68 (q3 c4) ∷
   rw⁻ 64 (q26 c4) ∷
   rw⁻ 59 (q31 c4) ∷
   rw 62 (q3 c4) ∷
   rw 63 (q3 c4) ∷
   rw 64 (q3 c4) ∷
   rw⁻ 61 (q25 c4) ∷
   rw⁻ 61 (q23 c4) ∷
   rw⁻ 56 (q32 c4) ∷
   re 54 1 (CS03⁻ ∷ []) ∷
   rw⁻ 53 (q33 c4) ∷
   re 55 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 50 (q32 c4) ∷
   re 48 1 (CS03 ∷ []) ∷
   rw⁻ 47 (q34 c4) ∷
   re 49 1 (Sb2-0-3-1 ∷ []) ∷
   rw 50 (q3 c4) ∷
   rw 51 (q3 c4) ∷
   rw 52 (q3 c4) ∷
   rw 53 (q3 c4) ∷
   re 49 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 44 (q35 c4) ∷
   re 42 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 43 (q3 c4) ∷
   rw⁻ 46 (q3 c4) ∷
   rw⁻ 49 (q3 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw 54 (q23 c4) ∷
   rw 54 (q25 c4) ∷
   rw⁻ 55 (q3 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw 63 (q26 c4) ∷
   rw⁻ 64 (q3 c4) ∷
   rw⁻ 67 (q3 c4) ∷
   rw⁻ 70 (q3 c4) ∷
   rw⁻ 73 (q3 c4) ∷
   rw⁻ 74 (q27 c4) ∷
   rw⁻ 71 (q28 c4) ∷
   rw⁻ 68 (q29 c4) ∷
   rw⁻ 65 (q28 c4) ∷
   rw⁻ 62 (q30 c4) ∷
   rw 65 (q3 c4) ∷
   rw 66 (q3 c4) ∷
   rw 67 (q3 c4) ∷
   rw 68 (q3 c4) ∷
   rw⁻ 64 (q26 c4) ∷
   rw⁻ 59 (q31 c4) ∷
   rw 57 (q26 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw⁻ 64 (q3 c4) ∷
   rw⁻ 67 (q3 c4) ∷
   rw⁻ 68 (q27 c4) ∷
   rw⁻ 65 (q28 c4) ∷
   rw⁻ 62 (q29 c4) ∷
   rw⁻ 59 (q28 c4) ∷
   rw⁻ 56 (q30 c4) ∷
   rw 59 (q3 c4) ∷
   rw 60 (q3 c4) ∷
   rw 61 (q3 c4) ∷
   rw 62 (q3 c4) ∷
   rw⁻ 58 (q26 c4) ∷
   rw⁻ 53 (q31 c4) ∷
   rw 56 (q3 c4) ∷
   rw 57 (q3 c4) ∷
   rw 58 (q3 c4) ∷
   rw⁻ 55 (q25 c4) ∷
   rw⁻ 55 (q23 c4) ∷
   rw⁻ 50 (q32 c4) ∷
   re 48 1 (CS03⁻ ∷ []) ∷
   rw⁻ 47 (q33 c4) ∷
   re 49 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 44 (q32 c4) ∷
   re 42 1 (CS03 ∷ []) ∷
   rw⁻ 41 (q34 c4) ∷
   re 43 1 (Sb2-0-3-1 ∷ []) ∷
   rw 44 (q3 c4) ∷
   rw 45 (q3 c4) ∷
   rw 46 (q3 c4) ∷
   rw 47 (q3 c4) ∷
   re 43 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 38 (q35 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 37 (q3 c4) ∷
   rw⁻ 40 (q3 c4) ∷
   rw⁻ 43 (q3 c4) ∷
   rw⁻ 46 (q3 c4) ∷
   rw 48 (q23 c4) ∷
   rw 48 (q25 c4) ∷
   rw⁻ 49 (q3 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw⁻ 55 (q3 c4) ∷
   rw 57 (q26 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw⁻ 64 (q3 c4) ∷
   rw⁻ 67 (q3 c4) ∷
   rw⁻ 68 (q27 c4) ∷
   rw⁻ 65 (q28 c4) ∷
   rw⁻ 62 (q29 c4) ∷
   rw⁻ 59 (q28 c4) ∷
   rw⁻ 56 (q30 c4) ∷
   rw 59 (q3 c4) ∷
   rw 60 (q3 c4) ∷
   rw 61 (q3 c4) ∷
   rw 62 (q3 c4) ∷
   rw⁻ 58 (q26 c4) ∷
   rw⁻ 53 (q31 c4) ∷
   rw 51 (q26 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw⁻ 55 (q3 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw⁻ 62 (q27 c4) ∷
   rw⁻ 59 (q28 c4) ∷
   rw⁻ 56 (q29 c4) ∷
   rw⁻ 53 (q28 c4) ∷
   rw⁻ 50 (q30 c4) ∷
   rw 53 (q3 c4) ∷
   rw 54 (q3 c4) ∷
   rw 55 (q3 c4) ∷
   rw 56 (q3 c4) ∷
   rw⁻ 52 (q26 c4) ∷
   rw⁻ 47 (q31 c4) ∷
   rw 50 (q3 c4) ∷
   rw 51 (q3 c4) ∷
   rw 52 (q3 c4) ∷
   rw⁻ 49 (q25 c4) ∷
   rw⁻ 49 (q23 c4) ∷
   rw⁻ 44 (q32 c4) ∷
   re 42 1 (CS03⁻ ∷ []) ∷
   rw⁻ 41 (q33 c4) ∷
   re 43 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 38 (q32 c4) ∷
   re 36 1 (CS03 ∷ []) ∷
   rw⁻ 35 (q34 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ []) ∷
   rw 38 (q3 c4) ∷
   rw 39 (q3 c4) ∷
   rw 40 (q3 c4) ∷
   rw 41 (q3 c4) ∷
   re 37 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 51 (q36 c4) ∷
   re 49 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 50 (q3 c4) ∷
   rw⁻ 53 (q3 c4) ∷
   rw⁻ 56 (q3 c4) ∷
   rw⁻ 59 (q3 c4) ∷
   rw 61 (q23 c4) ∷
   rw 61 (q25 c4) ∷
   rw⁻ 62 (q3 c4) ∷
   rw⁻ 65 (q3 c4) ∷
   rw⁻ 68 (q3 c4) ∷
   rw⁻ 69 (q37 c4) ∷
   rw⁻ 66 (q38 c4) ∷
   rw⁻ 63 (q37 c4) ∷
   rw⁻ 60 (q38 c4) ∷
   rw 63 (q3 c4) ∷
   rw 64 (q3 c4) ∷
   rw 65 (q3 c4) ∷
   rw⁻ 62 (q25 c4) ∷
   rw⁻ 62 (q23 c4) ∷
   rw⁻ 57 (q39 c4) ∷
   re 55 1 (CS03⁻ ∷ []) ∷
   rw⁻ 54 (q40 c4) ∷
   re 56 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 51 (q39 c4) ∷
   re 49 1 (CS03 ∷ []) ∷
   rw⁻ 48 (q41 c4) ∷
   re 50 1 (Sb2-0-3-1 ∷ []) ∷
   rw 51 (q3 c4) ∷
   rw 52 (q3 c4) ∷
   rw 53 (q3 c4) ∷
   rw 54 (q3 c4) ∷
   re 50 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 45 (q42 c4) ∷
   re 43 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 44 (q3 c4) ∷
   rw⁻ 47 (q3 c4) ∷
   rw⁻ 50 (q3 c4) ∷
   rw⁻ 53 (q3 c4) ∷
   rw 55 (q23 c4) ∷
   rw 55 (q25 c4) ∷
   rw⁻ 56 (q3 c4) ∷
   rw⁻ 59 (q3 c4) ∷
   rw⁻ 62 (q3 c4) ∷
   rw⁻ 63 (q37 c4) ∷
   rw⁻ 60 (q38 c4) ∷
   rw⁻ 57 (q37 c4) ∷
   rw⁻ 54 (q38 c4) ∷
   rw 57 (q3 c4) ∷
   rw 58 (q3 c4) ∷
   rw 59 (q3 c4) ∷
   rw⁻ 56 (q25 c4) ∷
   rw⁻ 56 (q23 c4) ∷
   rw⁻ 51 (q39 c4) ∷
   re 49 1 (CS03⁻ ∷ []) ∷
   rw⁻ 48 (q40 c4) ∷
   re 50 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 45 (q39 c4) ∷
   re 43 1 (CS03 ∷ []) ∷
   rw⁻ 42 (q41 c4) ∷
   re 44 1 (Sb2-0-3-1 ∷ []) ∷
   rw 45 (q3 c4) ∷
   rw 46 (q3 c4) ∷
   rw 47 (q3 c4) ∷
   rw 48 (q3 c4) ∷
   re 44 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 39 (q42 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 38 (q3 c4) ∷
   rw⁻ 41 (q3 c4) ∷
   rw⁻ 44 (q3 c4) ∷
   rw⁻ 47 (q3 c4) ∷
   rw 49 (q23 c4) ∷
   rw 49 (q25 c4) ∷
   rw⁻ 50 (q3 c4) ∷
   rw⁻ 53 (q3 c4) ∷
   rw⁻ 56 (q3 c4) ∷
   rw⁻ 57 (q37 c4) ∷
   rw⁻ 54 (q38 c4) ∷
   rw⁻ 51 (q37 c4) ∷
   rw⁻ 48 (q38 c4) ∷
   rw 51 (q3 c4) ∷
   rw 52 (q3 c4) ∷
   rw 53 (q3 c4) ∷
   rw⁻ 50 (q25 c4) ∷
   rw⁻ 50 (q23 c4) ∷
   rw⁻ 45 (q39 c4) ∷
   re 43 1 (CS03⁻ ∷ []) ∷
   rw⁻ 42 (q40 c4) ∷
   re 44 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 39 (q39 c4) ∷
   re 37 1 (CS03 ∷ []) ∷
   rw⁻ 36 (q41 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ []) ∷
   rw 39 (q3 c4) ∷
   rw 40 (q3 c4) ∷
   rw 41 (q3 c4) ∷
   rw 42 (q3 c4) ∷
   re 38 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 21 (q3 c4) ∷
   rw⁻ 24 (q3 c4) ∷
   rw⁻ 27 (q3 c4) ∷
   rw⁻ 30 (q3 c4) ∷
   re 32 1 (CS03⁻ ∷ []) ∷
   rw⁻ 31 (q43 c4) ∷
   re 33 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 28 (q44 c4) ∷
   re 26 1 (CS03 ∷ []) ∷
   rw⁻ 25 (q45 c4) ∷
   re 27 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 22 (q44 c4) ∷
   rw 20 (q25 c4) ∷
   rw⁻ 21 (q3 c4) ∷
   rw⁻ 24 (q3 c4) ∷
   rw⁻ 27 (q3 c4) ∷
   rw⁻ 28 (q46 c4) ∷
   rw⁻ 25 (q47 c4) ∷
   rw⁻ 22 (q46 c4) ∷
   rw⁻ 19 (q47 c4) ∷
   rw 22 (q3 c4) ∷
   rw 23 (q3 c4) ∷
   rw 24 (q3 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw 22 (q3 c4) ∷
   rw 23 (q3 c4) ∷
   rw 24 (q3 c4) ∷
   rw 25 (q3 c4) ∷
   re 21 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 16 (q48 c4) ∷
   re 14 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q3 c4) ∷
   rw⁻ 18 (q3 c4) ∷
   rw⁻ 21 (q3 c4) ∷
   rw⁻ 24 (q3 c4) ∷
   re 26 1 (CS03⁻ ∷ []) ∷
   rw⁻ 25 (q43 c4) ∷
   re 27 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 22 (q44 c4) ∷
   re 20 1 (CS03 ∷ []) ∷
   rw⁻ 19 (q45 c4) ∷
   re 21 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 16 (q44 c4) ∷
   rw 14 (q25 c4) ∷
   rw⁻ 15 (q3 c4) ∷
   rw⁻ 18 (q3 c4) ∷
   rw⁻ 21 (q3 c4) ∷
   rw⁻ 22 (q46 c4) ∷
   rw⁻ 19 (q47 c4) ∷
   rw⁻ 16 (q46 c4) ∷ []) Eq.refl
