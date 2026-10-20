{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D185 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0189 ; wl0190 ; wl0211 ; wl0247 ; wl0248 ; wl0249 ; wl0250 ; wl0260 ; wl0283 ; wl0433 ; wl0548 ; wl0560 ; wl0724 ; wl0725 ; wl0726 ; wl0727 ; wl0728 ; wl0733 ; wl0734 ; wl0743 ; wl0745 ; wl0746 ; wp0034 ; wp0059 ; wp0296 ; wp0343 ; wp0344 ; wp0345 ; wp0346 ; wp0365 ; wp0366 ; wp0373 ; wp0374 ; wp0375 ; wp0376 ; wp0377 ; wp0378 ; wp0379 ; wp0380 ; wp0381 ; wp0382 ; wp0383 ; wp0384)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0d)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-beta-T-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F5-CS01)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-BOXd-BOX-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-beta-T-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D184 using (lem-AX-SB-at3443 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0210243143)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CS03 ∷ CS03⁻ ∷ []) [] (wl0250 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl0248 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CS03⁻ ∷ CS03 ∷ []) [] (wl0249 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] (wl0247 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp0034 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp0059 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ []) (lem-F5-CS01 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CS01 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS01 ∷ []) (lem-AX-SB-at3443 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ []) (wp0373 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0374 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (K0⁻ ∷ K0 ∷ []) [] (wl0189 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ []) (c₁ (K) (X ↑ ↑ ↑))
  q17 : Ws → Eqn
  q17 c4 = eqn (K0 ∷ CCZ123 ∷ []) (CCZ123 ∷ K0 ∷ []) (c₁ (K) (CCZ))
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ []) (wp0343 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ []) (wp0344 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ []) (wp0345 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS04 ∷ []) (wp0346 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X ↑ ↑ ↑))
  q24 : Ws → Eqn
  q24 c4 = eqn (K0⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ K0⁻ ∷ []) (c₁ (K • iI) (CCZ))
  q25 : Ws → Eqn
  q25 c4 = eqn (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (wp0377 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (wp0376 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (wp0375 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Sb⁻2-0-41-3 ∷ []) (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx⁻3-0412 ∷ []) (Bx3-0412 ∷ []) (lem-BOXd-BOX-at0310243142 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ []) (wl0733 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0211 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ []) (wp0380 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ []) (wp0381 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS04⁻ ∷ []) (wp0382 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS04⁻ ∷ []) (wp0383 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ []) (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ123 ∷ CS02 ∷ []) (CS02 ∷ CCZ123 ∷ []) (wl0734 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (wp0384 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (wp0379 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (wp0378 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) (wp0296 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (Sb⁻2-0-41-3 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0210243143 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ []) (wl0743 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (K1⁻ ∷ K1 ∷ []) [] (wl0260 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (wl0745 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (K1 ∷ X4 ∷ []) (X4 ∷ K1 ∷ []) (c₂ (K ↑) (X ↑ ↑))
  q52 : Ws → Eqn
  q52 c4 = eqn (K1 ∷ Toff203 ∷ []) (Toff203 ∷ K1 ∷ []) (wl0724 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (X4 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ []) (wl0725 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (wp0365 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (wp0366 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) (wl0726 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) (wl0727 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ X4 ∷ CS14 ∷ []) (wl0728 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (K1⁻ ∷ X4 ∷ []) (X4 ∷ K1⁻ ∷ []) (c₂ ((K • iI) ↑) (X ↑ ↑))
  q62 : Ws → Eqn
  q62 c4 = eqn (K1⁻ ∷ Toff203 ∷ []) (Toff203 ∷ K1⁻ ∷ []) (wl0746 (lit c4))

-- F2 CS01|CS23 part0: 500 steps
lem-F2-CS01∣CS23-part0 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) ⟫ʷ
lem-F2-CS01∣CS23-part0 c4 = derive (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   re 1 1 (Sb2-0-3-1 ∷ []) ∷
   re 2 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   re 3 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   re 5 1 (Bx⁻2-03 ∷ []) ∷
   re 8 1 (Bx⁻2-03 ∷ []) ∷
   re 5 6 (Bx⁻0-213 ∷ []) ∷
   re 8 1 (Bx2-03 ∷ []) ∷
   re 11 1 (Bx2-03 ∷ []) ∷
   re 6 6 (Bx0-213 ∷ []) ∷
   rw⁻ 6 (q6 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   re 8 1 (Bx⁻2-03 ∷ []) ∷
   re 11 1 (Bx⁻2-03 ∷ []) ∷
   re 8 6 (Bx⁻0-213 ∷ []) ∷
   re 11 1 (Bx2-03 ∷ []) ∷
   re 14 1 (Bx2-03 ∷ []) ∷
   re 9 6 (Bx0-213 ∷ []) ∷
   rw⁻ 9 (q7 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   re 5 6 (Bx⁻2-0413 ∷ []) ∷
   re 6 6 (Bx2-0413 ∷ []) ∷
   re 1 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 2 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 3 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw 3 (q10 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw⁻ 14 (q13 c4) ∷
   re 1 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw 13 (q14 c4) ∷
   rw 13 (q15 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q16 c4) ∷
   rw⁻ 22 (q17 c4) ∷
   rw⁻ 21 (q16 c4) ∷
   rw 23 (q18 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 34 (q19 c4) ∷
   rw⁻ 31 (q20 c4) ∷
   rw⁻ 28 (q21 c4) ∷
   rw⁻ 25 (q20 c4) ∷
   rw⁻ 22 (q22 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw⁻ 24 (q18 c4) ∷
   rw⁻ 25 (q23 c4) ∷
   rw⁻ 24 (q24 c4) ∷
   rw⁻ 23 (q23 c4) ∷
   rw⁻ 18 (q25 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw⁻ 16 (q17 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   rw 17 (q18 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 28 (q19 c4) ∷
   rw⁻ 25 (q20 c4) ∷
   rw⁻ 22 (q21 c4) ∷
   rw⁻ 19 (q20 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw⁻ 18 (q18 c4) ∷
   rw⁻ 19 (q23 c4) ∷
   rw⁻ 18 (q24 c4) ∷
   rw⁻ 17 (q23 c4) ∷
   rw⁻ 12 (q25 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw⁻ 16 (q14 c4) ∷
   rw⁻ 9 (q26 c4) ∷
   re 1 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q27 c4) ∷
   re 4 1 (Sb2-0-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   re 4 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 4 (q28 c4) ∷
   re 4 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw 16 (q29 c4) ∷
   rw 16 (q30 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q16 c4) ∷
   rw⁻ 25 (q17 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw⁻ 25 (q31 c4) ∷
   rw⁻ 28 (q23 c4) ∷
   rw⁻ 27 (q24 c4) ∷
   rw⁻ 26 (q23 c4) ∷
   rw⁻ 29 (q16 c4) ∷
   rw⁻ 28 (q17 c4) ∷
   rw⁻ 27 (q16 c4) ∷
   rw 29 (q32 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 40 (q33 c4) ∷
   rw⁻ 37 (q34 c4) ∷
   rw⁻ 34 (q35 c4) ∷
   rw⁻ 31 (q34 c4) ∷
   rw⁻ 28 (q36 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw⁻ 30 (q32 c4) ∷
   rw⁻ 31 (q23 c4) ∷
   rw⁻ 30 (q24 c4) ∷
   rw⁻ 29 (q23 c4) ∷
   rw⁻ 32 (q16 c4) ∷
   rw⁻ 31 (q17 c4) ∷
   rw⁻ 30 (q16 c4) ∷
   rw⁻ 31 (q31 c4) ∷
   rw⁻ 34 (q23 c4) ∷
   rw⁻ 33 (q24 c4) ∷
   rw⁻ 32 (q23 c4) ∷
   rw⁻ 35 (q16 c4) ∷
   rw⁻ 34 (q17 c4) ∷
   rw⁻ 33 (q16 c4) ∷
   rw⁻ 36 (q37 c4) ∷
   rw 35 (q38 c4) ∷
   rw⁻ 34 (q37 c4) ∷
   rw⁻ 37 (q23 c4) ∷
   rw⁻ 36 (q24 c4) ∷
   rw⁻ 35 (q23 c4) ∷
   rw⁻ 21 (q39 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 19 (q17 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 19 (q31 c4) ∷
   rw⁻ 22 (q23 c4) ∷
   rw⁻ 21 (q24 c4) ∷
   rw⁻ 20 (q23 c4) ∷
   rw⁻ 23 (q16 c4) ∷
   rw⁻ 22 (q17 c4) ∷
   rw⁻ 21 (q16 c4) ∷
   rw 23 (q32 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 34 (q33 c4) ∷
   rw⁻ 31 (q34 c4) ∷
   rw⁻ 28 (q35 c4) ∷
   rw⁻ 25 (q34 c4) ∷
   rw⁻ 22 (q36 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw⁻ 24 (q32 c4) ∷
   rw⁻ 25 (q23 c4) ∷
   rw⁻ 24 (q24 c4) ∷
   rw⁻ 23 (q23 c4) ∷
   rw⁻ 26 (q16 c4) ∷
   rw⁻ 25 (q17 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw⁻ 25 (q31 c4) ∷
   rw⁻ 28 (q23 c4) ∷
   rw⁻ 27 (q24 c4) ∷
   rw⁻ 26 (q23 c4) ∷
   rw⁻ 29 (q16 c4) ∷
   rw⁻ 28 (q17 c4) ∷
   rw⁻ 27 (q16 c4) ∷
   rw⁻ 30 (q37 c4) ∷
   rw 29 (q38 c4) ∷
   rw⁻ 28 (q37 c4) ∷
   rw⁻ 31 (q23 c4) ∷
   rw⁻ 30 (q24 c4) ∷
   rw⁻ 29 (q23 c4) ∷
   rw⁻ 15 (q39 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw⁻ 28 (q30 c4) ∷
   rw⁻ 28 (q29 c4) ∷
   rw⁻ 12 (q40 c4) ∷
   re 4 1 (CS02 ∷ []) ∷
   re 10 1 (CS02⁻ ∷ []) ∷
   rw⁻ 3 (q41 c4) ∷
   re 16 1 (Sb3-0-2-1 ∷ []) ∷
   re 22 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   re 16 5 (Sb⁻3-0-41-2 ∷ []) ∷
   rw⁻ 16 (q28 c4) ∷
   rw 2 (q13 c4) ∷
   rw 3 (q13 c4) ∷
   rw 4 (q13 c4) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw 0 (q11 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   rw 2 (q43 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw⁻ 13 (q13 c4) ∷
   rw⁻ 16 (q13 c4) ∷
   re 3 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw 15 (q14 c4) ∷
   rw 15 (q15 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q16 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw⁻ 23 (q16 c4) ∷
   rw 25 (q18 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 36 (q19 c4) ∷
   rw⁻ 33 (q20 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw⁻ 27 (q20 c4) ∷
   rw⁻ 24 (q22 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw⁻ 26 (q18 c4) ∷
   rw⁻ 27 (q23 c4) ∷
   rw⁻ 26 (q24 c4) ∷
   rw⁻ 25 (q23 c4) ∷
   rw⁻ 20 (q25 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw⁻ 18 (q17 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw 19 (q18 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw⁻ 27 (q20 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 18 (q22 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw⁻ 20 (q18 c4) ∷
   rw⁻ 21 (q23 c4) ∷
   rw⁻ 20 (q24 c4) ∷
   rw⁻ 19 (q23 c4) ∷
   rw⁻ 14 (q25 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw⁻ 18 (q14 c4) ∷
   rw⁻ 11 (q26 c4) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 9 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q27 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 12 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   re 6 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 6 (q28 c4) ∷
   re 6 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw 18 (q29 c4) ∷
   rw 18 (q30 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   rw⁻ 27 (q17 c4) ∷
   rw⁻ 26 (q16 c4) ∷
   rw⁻ 27 (q31 c4) ∷
   rw⁻ 30 (q23 c4) ∷
   rw⁻ 29 (q24 c4) ∷
   rw⁻ 28 (q23 c4) ∷
   rw⁻ 31 (q16 c4) ∷
   rw⁻ 30 (q17 c4) ∷
   rw⁻ 29 (q16 c4) ∷
   rw 31 (q32 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   rw⁻ 42 (q33 c4) ∷
   rw⁻ 39 (q34 c4) ∷
   rw⁻ 36 (q35 c4) ∷
   rw⁻ 33 (q34 c4) ∷
   rw⁻ 30 (q36 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   rw⁻ 32 (q32 c4) ∷
   rw⁻ 33 (q23 c4) ∷
   rw⁻ 32 (q24 c4) ∷
   rw⁻ 31 (q23 c4) ∷
   rw⁻ 34 (q16 c4) ∷
   rw⁻ 33 (q17 c4) ∷
   rw⁻ 32 (q16 c4) ∷
   rw⁻ 33 (q31 c4) ∷
   rw⁻ 36 (q23 c4) ∷
   rw⁻ 35 (q24 c4) ∷
   rw⁻ 34 (q23 c4) ∷
   rw⁻ 37 (q16 c4) ∷
   rw⁻ 36 (q17 c4) ∷
   rw⁻ 35 (q16 c4) ∷
   rw⁻ 38 (q37 c4) ∷
   rw 37 (q38 c4) ∷
   rw⁻ 36 (q37 c4) ∷
   rw⁻ 39 (q23 c4) ∷
   rw⁻ 38 (q24 c4) ∷
   rw⁻ 37 (q23 c4) ∷
   rw⁻ 23 (q39 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 21 (q17 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 21 (q31 c4) ∷
   rw⁻ 24 (q23 c4) ∷
   rw⁻ 23 (q24 c4) ∷
   rw⁻ 22 (q23 c4) ∷
   rw⁻ 25 (q16 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw⁻ 23 (q16 c4) ∷
   rw 25 (q32 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 36 (q33 c4) ∷
   rw⁻ 33 (q34 c4) ∷
   rw⁻ 30 (q35 c4) ∷
   rw⁻ 27 (q34 c4) ∷
   rw⁻ 24 (q36 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw⁻ 26 (q32 c4) ∷
   rw⁻ 27 (q23 c4) ∷
   rw⁻ 26 (q24 c4) ∷
   rw⁻ 25 (q23 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   rw⁻ 27 (q17 c4) ∷
   rw⁻ 26 (q16 c4) ∷
   rw⁻ 27 (q31 c4) ∷
   rw⁻ 30 (q23 c4) ∷
   rw⁻ 29 (q24 c4) ∷
   rw⁻ 28 (q23 c4) ∷
   rw⁻ 31 (q16 c4) ∷
   rw⁻ 30 (q17 c4) ∷
   rw⁻ 29 (q16 c4) ∷
   rw⁻ 32 (q37 c4) ∷
   rw 31 (q38 c4) ∷
   rw⁻ 30 (q37 c4) ∷
   rw⁻ 33 (q23 c4) ∷
   rw⁻ 32 (q24 c4) ∷
   rw⁻ 31 (q23 c4) ∷
   rw⁻ 17 (q39 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw⁻ 30 (q30 c4) ∷
   rw⁻ 30 (q29 c4) ∷
   rw⁻ 14 (q40 c4) ∷
   re 6 1 (CS02 ∷ []) ∷
   re 12 1 (CS02⁻ ∷ []) ∷
   rw⁻ 5 (q41 c4) ∷
   re 18 1 (Sb3-0-2-1 ∷ []) ∷
   re 24 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   re 18 5 (Sb⁻3-0-41-2 ∷ []) ∷
   rw⁻ 18 (q28 c4) ∷
   rw 4 (q13 c4) ∷
   rw 5 (q13 c4) ∷
   rw 6 (q13 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw 2 (q11 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   rw⁻ 0 (q10 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw 5 (q45 c4) ∷
   rw⁻ 6 (q46 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   rw⁻ 12 (q46 c4) ∷
   rw⁻ 15 (q46 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw 14 (q14 c4) ∷
   rw 14 (q47 c4) ∷
   rw 14 (q48 c4) ∷
   rw 14 (q49 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 22 (q50 c4) ∷
   rw⁻ 21 (q51 c4) ∷
   rw⁻ 20 (q52 c4) ∷
   rw⁻ 19 (q51 c4) ∷
   rw⁻ 21 (q53 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 26 (q54 c4) ∷
   rw 24 (q55 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 35 (q56 c4) ∷
   rw⁻ 32 (q57 c4) ∷
   rw⁻ 29 (q58 c4) ∷
   rw⁻ 26 (q57 c4) ∷
   rw⁻ 23 (q59 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw⁻ 25 (q55 c4) ∷
   rw⁻ 20 (q60 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 22 (q53 c4) ∷
   rw⁻ 23 (q61 c4) ∷
   rw⁻ 22 (q62 c4) ∷
   rw⁻ 21 (q61 c4) ∷
   rw⁻ 16 (q50 c4) ∷
   rw⁻ 15 (q51 c4) ∷
   rw⁻ 14 (q52 c4) ∷
   rw⁻ 13 (q51 c4) ∷
   rw⁻ 15 (q53 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 20 (q54 c4) ∷
   rw 18 (q55 c4) ∷ []) Eq.refl
