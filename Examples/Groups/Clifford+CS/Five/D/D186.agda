{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D186 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0190 ; wl0247 ; wl0248 ; wl0249 ; wl0250 ; wl0260 ; wl0283 ; wl0548 ; wl0560 ; wl0724 ; wl0725 ; wl0726 ; wl0727 ; wl0728 ; wl0743 ; wl0744 ; wl0745 ; wl0746 ; wl0747 ; wl0748 ; wl0749 ; wl0750 ; wl0751 ; wl0752 ; wl0753 ; wl0754 ; wl0755 ; wl0885 ; wl0886 ; wl0887 ; wl0888 ; wp0034 ; wp0059 ; wp0365 ; wp0366 ; wp0387 ; wp0388 ; wp0389 ; wp0390 ; wp0391 ; wp0392 ; wp0393 ; wp0461 ; wp0462 ; wp0463 ; wp0464 ; wp0465)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F5-CS01)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-F4-iIᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-F4-CS01ᵖ0∣iIᵖ1 ; lem-F4-K1ᵖ0∣CS01ᵖ1 ; lem-F4-S0ᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-F4-CS01ᵖ0∣CS01ᵖ1 ; lem-F4-CS01ᵖ0∣K1ᵖ1 ; lem-F4-CS01ᵖ0∣S0ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D184 using (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D185 using (lem-F2-CS01∣CS23-part0)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (wp0365 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (wp0366 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) (wl0726 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) (wl0727 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ X4 ∷ CS14 ∷ []) (wl0728 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (K1⁻ ∷ X4 ∷ []) (X4 ∷ K1⁻ ∷ []) (c₂ ((K • iI) ↑) (X ↑ ↑))
  q10 : Ws → Eqn
  q10 c4 = eqn (K1⁻ ∷ Toff203 ∷ []) (Toff203 ∷ K1⁻ ∷ []) (wl0746 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (wl0744 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (wp0387 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (wp0388 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (wl0748 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (K1 ∷ X4 ∷ []) (X4 ∷ K1 ∷ []) (c₂ (K ↑) (X ↑ ↑))
  q22 : Ws → Eqn
  q22 c4 = eqn (K1 ∷ Toff203 ∷ []) (Toff203 ∷ K1 ∷ []) (wl0724 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ []) (wp0391 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ []) (wl0749 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (wp0392 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (wp0393 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ []) (wl0750 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (wl0751 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ []) (wl0752 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ []) (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))
  q31 : Ws → Eqn
  q31 c4 = eqn (CS13 ∷ Toff203 ∷ []) (Toff203 ∷ CS13 ∷ []) (wl0753 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (wl0747 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (wp0389 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (wp0390 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (K1⁻ ∷ K1 ∷ []) [] (wl0260 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ []) (wl0743 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ []) (wl0754 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (Sb⁻2-0-41-3 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (wl0745 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (X4 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ []) (wl0725 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ []) (wl0755 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (Sb⁻2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ []) (lem-F5-CS01 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp0034 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp0059 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] (wl0247 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl0248 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CS03⁻ ∷ CS03 ∷ []) [] (wl0249 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CS03 ∷ CS03⁻ ∷ []) [] (wl0250 (lit c4))

-- F2 CS01|CS23 part1: 475 steps
lem-F2-CS01∣CS23-part1 : Ws → ⟪ (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F2-CS01∣CS23-part1 c4 = derive (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 26 (q3 c4) ∷
   rw⁻ 23 (q4 c4) ∷
   rw⁻ 20 (q3 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw⁻ 19 (q6 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 16 (q8 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw⁻ 16 (q10 c4) ∷
   rw⁻ 15 (q9 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw 17 (q12 c4) ∷
   rw 17 (q13 c4) ∷
   rw⁻ 17 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   re 8 1 (CS03⁻ ∷ []) ∷
   rw⁻ 7 (q16 c4) ∷
   re 11 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q15 c4) ∷
   re 2 1 (CS03 ∷ []) ∷
   rw⁻ 1 (q17 c4) ∷
   re 5 1 (Sb2-0-3-1 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   re 5 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 5 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw 17 (q14 c4) ∷
   rw 17 (q18 c4) ∷
   rw 17 (q19 c4) ∷
   rw 17 (q11 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 25 (q20 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 23 (q22 c4) ∷
   rw⁻ 22 (q21 c4) ∷
   rw⁻ 23 (q23 c4) ∷
   rw⁻ 26 (q9 c4) ∷
   rw⁻ 25 (q10 c4) ∷
   rw⁻ 24 (q9 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw⁻ 26 (q22 c4) ∷
   rw⁻ 25 (q21 c4) ∷
   rw⁻ 27 (q8 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 32 (q24 c4) ∷
   rw 30 (q6 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 41 (q25 c4) ∷
   rw⁻ 38 (q26 c4) ∷
   rw⁻ 35 (q27 c4) ∷
   rw⁻ 32 (q26 c4) ∷
   rw⁻ 29 (q28 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw⁻ 31 (q6 c4) ∷
   rw⁻ 26 (q29 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 28 (q8 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw⁻ 28 (q10 c4) ∷
   rw⁻ 27 (q9 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw⁻ 29 (q22 c4) ∷
   rw⁻ 28 (q21 c4) ∷
   rw⁻ 29 (q23 c4) ∷
   rw⁻ 32 (q9 c4) ∷
   rw⁻ 31 (q10 c4) ∷
   rw⁻ 30 (q9 c4) ∷
   rw⁻ 33 (q21 c4) ∷
   rw⁻ 32 (q22 c4) ∷
   rw⁻ 31 (q21 c4) ∷
   rw⁻ 34 (q30 c4) ∷
   rw⁻ 33 (q31 c4) ∷
   rw⁻ 32 (q30 c4) ∷
   rw⁻ 35 (q9 c4) ∷
   rw⁻ 34 (q10 c4) ∷
   rw⁻ 33 (q9 c4) ∷
   rw⁻ 19 (q20 c4) ∷
   rw⁻ 18 (q21 c4) ∷
   rw⁻ 17 (q22 c4) ∷
   rw⁻ 16 (q21 c4) ∷
   rw⁻ 17 (q23 c4) ∷
   rw⁻ 20 (q9 c4) ∷
   rw⁻ 19 (q10 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw⁻ 20 (q22 c4) ∷
   rw⁻ 19 (q21 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 26 (q24 c4) ∷
   rw 24 (q6 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 35 (q25 c4) ∷
   rw⁻ 32 (q26 c4) ∷
   rw⁻ 29 (q27 c4) ∷
   rw⁻ 26 (q26 c4) ∷
   rw⁻ 23 (q28 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw⁻ 25 (q6 c4) ∷
   rw⁻ 20 (q29 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 22 (q8 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw⁻ 22 (q10 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 23 (q22 c4) ∷
   rw⁻ 22 (q21 c4) ∷
   rw⁻ 23 (q23 c4) ∷
   rw⁻ 26 (q9 c4) ∷
   rw⁻ 25 (q10 c4) ∷
   rw⁻ 24 (q9 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw⁻ 26 (q22 c4) ∷
   rw⁻ 25 (q21 c4) ∷
   rw⁻ 28 (q30 c4) ∷
   rw⁻ 27 (q31 c4) ∷
   rw⁻ 26 (q30 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw⁻ 28 (q10 c4) ∷
   rw⁻ 27 (q9 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw⁻ 29 (q11 c4) ∷
   rw 29 (q12 c4) ∷
   rw 29 (q13 c4) ∷
   rw⁻ 29 (q14 c4) ∷
   rw⁻ 13 (q32 c4) ∷
   re 11 1 (CS03⁻ ∷ []) ∷
   rw⁻ 10 (q33 c4) ∷
   re 23 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 7 (q32 c4) ∷
   re 5 1 (CS03 ∷ []) ∷
   rw⁻ 4 (q34 c4) ∷
   re 17 1 (Sb2-0-3-1 ∷ []) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   re 17 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 3 (q35 c4) ∷
   rw 4 (q35 c4) ∷
   rw 5 (q35 c4) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 2 (q36 c4) ∷
   rw 1 (q37 c4) ∷
   re 5 1 (CS12 ∷ []) ∷
   rw⁻ 4 (q38 c4) ∷
   re 4 1 (Sb0-2-1-3 ∷ []) ∷
   rw 3 (q39 c4) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q38 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 6 (q37 c4) ∷
   rw 7 (q36 c4) ∷
   rw⁻ 8 (q35 c4) ∷
   rw⁻ 11 (q35 c4) ∷
   rw⁻ 14 (q35 c4) ∷
   rw⁻ 17 (q35 c4) ∷
   re 4 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw 16 (q14 c4) ∷
   rw 16 (q18 c4) ∷
   rw 16 (q19 c4) ∷
   rw 16 (q11 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 24 (q40 c4) ∷
   rw⁻ 23 (q21 c4) ∷
   rw⁻ 22 (q22 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 28 (q41 c4) ∷
   rw 26 (q6 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 37 (q2 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw⁻ 25 (q5 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw⁻ 27 (q6 c4) ∷
   rw⁻ 22 (q7 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 24 (q8 c4) ∷
   rw⁻ 25 (q9 c4) ∷
   rw⁻ 24 (q10 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw⁻ 18 (q40 c4) ∷
   rw⁻ 17 (q21 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw⁻ 15 (q21 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 22 (q41 c4) ∷
   rw 20 (q6 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw⁻ 25 (q4 c4) ∷
   rw⁻ 22 (q3 c4) ∷
   rw⁻ 19 (q5 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw⁻ 21 (q6 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 18 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q10 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   rw 19 (q12 c4) ∷
   rw 19 (q13 c4) ∷
   rw⁻ 19 (q14 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   re 10 1 (CS03⁻ ∷ []) ∷
   rw⁻ 9 (q16 c4) ∷
   re 13 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 6 (q15 c4) ∷
   re 4 1 (CS03 ∷ []) ∷
   rw⁻ 3 (q17 c4) ∷
   re 7 1 (Sb2-0-3-1 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   re 7 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 7 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw 19 (q14 c4) ∷
   rw 19 (q18 c4) ∷
   rw 19 (q19 c4) ∷
   rw 19 (q11 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 27 (q20 c4) ∷
   rw⁻ 26 (q21 c4) ∷
   rw⁻ 25 (q22 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 25 (q23 c4) ∷
   rw⁻ 28 (q9 c4) ∷
   rw⁻ 27 (q10 c4) ∷
   rw⁻ 26 (q9 c4) ∷
   rw⁻ 29 (q21 c4) ∷
   rw⁻ 28 (q22 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw⁻ 29 (q8 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 34 (q24 c4) ∷
   rw 32 (q6 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw⁻ 43 (q25 c4) ∷
   rw⁻ 40 (q26 c4) ∷
   rw⁻ 37 (q27 c4) ∷
   rw⁻ 34 (q26 c4) ∷
   rw⁻ 31 (q28 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   rw⁻ 33 (q6 c4) ∷
   rw⁻ 28 (q29 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 30 (q8 c4) ∷
   rw⁻ 31 (q9 c4) ∷
   rw⁻ 30 (q10 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw⁻ 32 (q21 c4) ∷
   rw⁻ 31 (q22 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw⁻ 31 (q23 c4) ∷
   rw⁻ 34 (q9 c4) ∷
   rw⁻ 33 (q10 c4) ∷
   rw⁻ 32 (q9 c4) ∷
   rw⁻ 35 (q21 c4) ∷
   rw⁻ 34 (q22 c4) ∷
   rw⁻ 33 (q21 c4) ∷
   rw⁻ 36 (q30 c4) ∷
   rw⁻ 35 (q31 c4) ∷
   rw⁻ 34 (q30 c4) ∷
   rw⁻ 37 (q9 c4) ∷
   rw⁻ 36 (q10 c4) ∷
   rw⁻ 35 (q9 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 20 (q21 c4) ∷
   rw⁻ 19 (q22 c4) ∷
   rw⁻ 18 (q21 c4) ∷
   rw⁻ 19 (q23 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 21 (q10 c4) ∷
   rw⁻ 20 (q9 c4) ∷
   rw⁻ 23 (q21 c4) ∷
   rw⁻ 22 (q22 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 28 (q24 c4) ∷
   rw 26 (q6 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 37 (q25 c4) ∷
   rw⁻ 34 (q26 c4) ∷
   rw⁻ 31 (q27 c4) ∷
   rw⁻ 28 (q26 c4) ∷
   rw⁻ 25 (q28 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw⁻ 27 (q6 c4) ∷
   rw⁻ 22 (q29 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 24 (q8 c4) ∷
   rw⁻ 25 (q9 c4) ∷
   rw⁻ 24 (q10 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw⁻ 26 (q21 c4) ∷
   rw⁻ 25 (q22 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 25 (q23 c4) ∷
   rw⁻ 28 (q9 c4) ∷
   rw⁻ 27 (q10 c4) ∷
   rw⁻ 26 (q9 c4) ∷
   rw⁻ 29 (q21 c4) ∷
   rw⁻ 28 (q22 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw⁻ 30 (q30 c4) ∷
   rw⁻ 29 (q31 c4) ∷
   rw⁻ 28 (q30 c4) ∷
   rw⁻ 31 (q9 c4) ∷
   rw⁻ 30 (q10 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw⁻ 31 (q11 c4) ∷
   rw 31 (q12 c4) ∷
   rw 31 (q13 c4) ∷
   rw⁻ 31 (q14 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   re 13 1 (CS03⁻ ∷ []) ∷
   rw⁻ 12 (q33 c4) ∷
   re 25 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 9 (q32 c4) ∷
   re 7 1 (CS03 ∷ []) ∷
   rw⁻ 6 (q34 c4) ∷
   re 19 1 (Sb2-0-3-1 ∷ []) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   re 19 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 5 (q35 c4) ∷
   rw 6 (q35 c4) ∷
   rw 7 (q35 c4) ∷
   rw 8 (q35 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 3 (q37 c4) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 6 (q42 c4) ∷
   re 6 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw 5 (q43 c4) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q42 c4) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 4 (q44 c4) ∷
   rw 3 (q1 c4) ∷
   re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 2 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 7 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 6 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   rw 11 (q45 c4) ∷
   rw 10 (q46 c4) ∷
   re 9 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 9 1 (CZ03 ∷ []) ∷
   re 12 1 (CZ03 ∷ []) ∷
   re 15 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 17 1 (CZ03 ∷ []) ∷
   re 20 1 (CZ03 ∷ []) ∷
   rw 9 (q47 c4) ∷
   rw 8 (q46 c4) ∷
   rw 7 (q45 c4) ∷
   re 6 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 6 1 (CZ03 ∷ []) ∷
   re 9 1 (CZ03 ∷ []) ∷
   re 12 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 14 1 (CZ03 ∷ []) ∷
   re 17 1 (CZ03 ∷ []) ∷
   rw 6 (q47 c4) ∷
   rw 5 (q48 c4) ∷
   re 4 1 (CS03⁻ ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   rw 4 (q49 c4) ∷
   rw 3 (q48 c4) ∷
   re 2 1 (CS03 ∷ []) ∷
   re 3 1 (CS03⁻ ∷ []) ∷
   rw 2 (q50 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = eqn (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (lem-F2-CS01∣CS23-part0 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) (lem-F2-CS01∣CS23-part1 c4)

-- F2 CS01|CS23: 2 steps
lem-F2-CS01∣CS23 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F2-CS01∣CS23 c4 = derive (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ [])
  (rw 0 (q51 c4) ∷
   rw 0 (q52 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = eqn (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl0886 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (wp0462 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS01ᵖ1 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣iIᵖ1 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4))

-- split4[CS01 CS01 CS01 CS01 CS01 CS01 S0 iI S0 S0 S0 CS01 K1 CS01 K1 CS01]: 136 steps
lem-split4CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 : Ws → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-split4CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 c4 = derive (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 15 (q44 c4) ∷
   rw 14 (q53 c4) ∷
   rw⁻ 13 (q44 c4) ∷
   rw 12 (q53 c4) ∷
   rw⁻ 11 (q44 c4) ∷
   rw 10 (q54 c4) ∷
   rw 9 (q54 c4) ∷
   rw 8 (q54 c4) ∷
   rw⁻ 7 (q55 c4) ∷
   rw 6 (q54 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw⁻ 1 (q44 c4) ∷
   rw⁻ 0 (q44 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   rw⁻ 7 (q56 c4) ∷
   rw⁻ 6 (q56 c4) ∷
   rw⁻ 11 (q56 c4) ∷
   rw⁻ 10 (q56 c4) ∷
   rw⁻ 9 (q56 c4) ∷
   rw⁻ 15 (q56 c4) ∷
   rw⁻ 14 (q56 c4) ∷
   rw⁻ 13 (q56 c4) ∷
   rw⁻ 12 (q56 c4) ∷
   rw⁻ 19 (q56 c4) ∷
   rw⁻ 18 (q56 c4) ∷
   rw⁻ 17 (q56 c4) ∷
   rw⁻ 16 (q56 c4) ∷
   rw⁻ 15 (q56 c4) ∷
   rw⁻ 23 (q57 c4) ∷
   rw⁻ 22 (q57 c4) ∷
   rw⁻ 21 (q57 c4) ∷
   rw⁻ 20 (q57 c4) ∷
   rw⁻ 19 (q57 c4) ∷
   rw⁻ 18 (q57 c4) ∷
   rw 27 (q58 c4) ∷
   rw⁻ 26 (q59 c4) ∷
   rw⁻ 25 (q59 c4) ∷
   rw⁻ 24 (q59 c4) ∷
   rw⁻ 23 (q59 c4) ∷
   rw⁻ 22 (q59 c4) ∷
   rw⁻ 21 (q59 c4) ∷
   rw 31 (q60 c4) ∷
   rw 30 (q61 c4) ∷
   rw⁻ 29 (q57 c4) ∷
   rw⁻ 28 (q57 c4) ∷
   rw⁻ 27 (q57 c4) ∷
   rw⁻ 26 (q57 c4) ∷
   rw⁻ 25 (q57 c4) ∷
   rw⁻ 24 (q57 c4) ∷
   rw 35 (q61 c4) ∷
   rw 34 (q60 c4) ∷
   rw 33 (q61 c4) ∷
   rw⁻ 32 (q57 c4) ∷
   rw⁻ 31 (q57 c4) ∷
   rw⁻ 30 (q57 c4) ∷
   rw⁻ 29 (q57 c4) ∷
   rw⁻ 28 (q57 c4) ∷
   rw⁻ 27 (q57 c4) ∷
   rw 39 (q61 c4) ∷
   rw 38 (q61 c4) ∷
   rw 37 (q60 c4) ∷
   rw 36 (q61 c4) ∷
   rw⁻ 35 (q57 c4) ∷
   rw⁻ 34 (q57 c4) ∷
   rw⁻ 33 (q57 c4) ∷
   rw⁻ 32 (q57 c4) ∷
   rw⁻ 31 (q57 c4) ∷
   rw⁻ 30 (q57 c4) ∷
   rw⁻ 43 (q62 c4) ∷
   rw⁻ 42 (q62 c4) ∷
   rw⁻ 41 (q62 c4) ∷
   rw⁻ 40 (q63 c4) ∷
   rw⁻ 39 (q62 c4) ∷
   rw⁻ 38 (q56 c4) ∷
   rw⁻ 37 (q56 c4) ∷
   rw⁻ 36 (q56 c4) ∷
   rw⁻ 35 (q56 c4) ∷
   rw⁻ 34 (q56 c4) ∷
   rw⁻ 33 (q56 c4) ∷
   rw⁻ 47 (q64 c4) ∷
   rw 46 (q65 c4) ∷
   rw 45 (q65 c4) ∷
   rw 44 (q65 c4) ∷
   rw 43 (q66 c4) ∷
   rw 42 (q65 c4) ∷
   rw⁻ 41 (q64 c4) ∷
   rw⁻ 40 (q64 c4) ∷
   rw⁻ 39 (q64 c4) ∷
   rw⁻ 38 (q64 c4) ∷
   rw⁻ 37 (q64 c4) ∷
   rw⁻ 36 (q64 c4) ∷
   rw⁻ 51 (q67 c4) ∷
   rw⁻ 50 (q56 c4) ∷
   rw⁻ 49 (q62 c4) ∷
   rw⁻ 48 (q62 c4) ∷
   rw⁻ 47 (q62 c4) ∷
   rw⁻ 46 (q63 c4) ∷
   rw⁻ 45 (q62 c4) ∷
   rw⁻ 44 (q56 c4) ∷
   rw⁻ 43 (q56 c4) ∷
   rw⁻ 42 (q56 c4) ∷
   rw⁻ 41 (q56 c4) ∷
   rw⁻ 40 (q56 c4) ∷
   rw⁻ 39 (q56 c4) ∷
   rw⁻ 55 (q64 c4) ∷
   rw 54 (q68 c4) ∷
   rw⁻ 53 (q64 c4) ∷
   rw 52 (q65 c4) ∷
   rw 51 (q65 c4) ∷
   rw 50 (q65 c4) ∷
   rw 49 (q66 c4) ∷
   rw 48 (q65 c4) ∷
   rw⁻ 47 (q64 c4) ∷
   rw⁻ 46 (q64 c4) ∷
   rw⁻ 45 (q64 c4) ∷
   rw⁻ 44 (q64 c4) ∷
   rw⁻ 43 (q64 c4) ∷
   rw⁻ 42 (q64 c4) ∷
   rw⁻ 59 (q67 c4) ∷
   rw⁻ 58 (q56 c4) ∷
   rw⁻ 57 (q67 c4) ∷
   rw⁻ 56 (q56 c4) ∷
   rw⁻ 55 (q62 c4) ∷
   rw⁻ 54 (q62 c4) ∷
   rw⁻ 53 (q62 c4) ∷
   rw⁻ 52 (q63 c4) ∷
   rw⁻ 51 (q62 c4) ∷
   rw⁻ 50 (q56 c4) ∷
   rw⁻ 49 (q56 c4) ∷
   rw⁻ 48 (q56 c4) ∷
   rw⁻ 47 (q56 c4) ∷
   rw⁻ 46 (q56 c4) ∷
   rw⁻ 45 (q56 c4) ∷ []) Eq.refl
