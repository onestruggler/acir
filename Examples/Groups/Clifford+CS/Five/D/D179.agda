{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D179 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0035 ; wl0037 ; wl0100 ; wl0103 ; wl0138 ; wl0183 ; wl0212 ; wl0283 ; wl0296 ; wl0333 ; wl0351 ; wl0357 ; wl0358 ; wl0550 ; wl0563 ; wl0616 ; wl0779 ; wl0780 ; wl0781 ; wl0782 ; wl0783 ; wl0787 ; wl0788 ; wl0789 ; wl0790 ; wl0791 ; wl0792 ; wl0793 ; wl0794 ; wl0795 ; wl0796 ; wl0797 ; wl0798 ; wl0799 ; wl0800 ; wl0801 ; wl0802 ; wl0803 ; wl0804 ; wl0805 ; wl0806 ; wl0807 ; wl0808 ; wl0809 ; wl0810 ; wl0811 ; wl0812 ; wl0813 ; wl0814 ; wl0815 ; wl0816 ; wp0055 ; wp0269 ; wp0285 ; wp0351 ; wp0352 ; wp0411 ; wp0412 ; wp0413 ; wp0414 ; wp0415 ; wp0416 ; wp0417 ; wp0418)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-beta-T-at13243142 ; lem-beta-inv-at243243 ; lem-sym12 ; lem-sym12-at0314203142 ; lem-sym12-at1221 ; lem-sym12-at14213243 ; lem-sym23-at1221 ; lem-sym23-at14213243 ; lem-sym34 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-Cz-beta-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 ; lem-sym12-at243243 ; lem-sym23-at122331 ; lem-sym23-at243243 ; lem-sym23-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-SBsym-at0113203442 ; lem-X1-beta-at14213243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at233442 ; lem-sym23-at233442 ; lem-sym23-at2442 ; lem-sym34-at243243 ; lem-sym34-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D164 using (lem-T-beta-at2332 ; lem-sym23-at0312203441 ; lem-sym23-at0312243041)
open import Examples.Groups.Clifford+CS.Five.D.D166 using (lem-T312-beta-at1441 ; lem-sym23-at143143 ; lem-sym34-at143143 ; lem-sym34-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-T312-beta-at133441 ; lem-auto-BOX⟨0·1234⟩-∣-CSd21 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.D175 using (lem-beta-T-at133441)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-X1-beta-at0314203142 ; lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 ; lem-c124-beta-at0312203441)
open import Examples.Groups.Clifford+CS.Five.D.D178 using (lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩-at3443 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at243243)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOX⟨0·2314⟩ ; lem-nat-2-CSd12 ; lem-nat-2-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-1-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-SBOX⟨2·1·40·3⟩ ; lem-nat-1-SBOX⟨3·1·40·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-SBOX⟨2·0·41·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-BOX⟨0·3421⟩ ; lem-nat-2-BOX⟨0·2431⟩ ; lem-nat-2-BOX⟨0·3241⟩ ; lem-nat-3-BOX⟨0·2341⟩ ; lem-nat-3-BOX⟨0·2431⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 ; lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 ; lem-nat-1-SBOX⟨3·2·40·1⟩ ; lem-nat-2-BOX⟨0·2341⟩ ; lem-nat-2-BOX⟨0·3421⟩ ; lem-nat-2-SBOX⟨2·1·40·3⟩ ; lem-nat-2-SBOX⟨3·1·40·2⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx3-0412 ∷ []) (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ Bx3-4012 ∷ X4 ∷ []) (CCZ012 ∷ Bx3-4012 ∷ []) (lem-X1-beta-at0314203142 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx3-4012 ∷ []) (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ012 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Sb0-1-42-3 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at243243 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ []) (wl0787 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ012 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩-at3443 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl0183 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl0563 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0788 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (K2⁻ ∷ K2 ∷ []) [] (wl0550 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (wl0789 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (wl0790 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (wl0791 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1432 ∷ []) (lem-sym34-at243243 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx0-1432 ∷ []) (Bx0-1342 ∷ []) (lem-sym23-at2442 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx0-1342 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (wp0412 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (X ↑))
  q22 : Ws → Eqn
  q22 c4 = eqn (K2 ∷ Toff013 ∷ []) (Toff013 ∷ K2 ∷ []) (wl0779 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) (wl0780 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ []) (wl0781 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (wp0411 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (wl0782 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ []) (wp0351 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (wp0352 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ X4 ∷ CS24 ∷ []) (wl0783 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (K2⁻ ∷ X4 ∷ []) (X4 ∷ K2⁻ ∷ []) (c₃ ((K • iI) ↑ ↑) (X ↑))
  q32 : Ws → Eqn
  q32 c4 = eqn (K2⁻ ∷ Toff013 ∷ []) (Toff013 ∷ K2⁻ ∷ []) (wl0792 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1432 ∷ []) (lem-sym23-at233442 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx0-1432 ∷ []) (Bx0-1423 ∷ []) (lem-sym34-at2442 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (wl0793 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (wl0794 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (wl0795 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (wp0413 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (X4 ∷ Toff013 ∷ X4 ∷ CX14 ∷ []) (wp0414 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ []) (wl0796 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (wp0415 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (wl0797 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ []) (wp0416 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) (wp0417 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ []) (wl0798 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ []) (c₃ (CS ↑) (X ↑))
  q47 : Ws → Eqn
  q47 c4 = eqn (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) (wl0799 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ []) (wl0800 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (Sb0-1-42-3 ∷ Sb3-0-2-1 ∷ []) (Sb3-0-2-1 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at243243 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CS02⁻ ∷ X4 ∷ []) (X4 ∷ CS02⁻ ∷ []) (wl0801 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (Sb0-1-42-3 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at243243 c4)

-- F4 CS12^0|CS01^1: 510 steps
lem-F4-CS12ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣CS01ᵖ1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 3 (q1 c4) ∷
   re 3 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q6 c4) ∷
   rw 4 (q8 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 3 (q8 c4) ∷
   rw 4 (q10 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw⁻ 15 (q13 c4) ∷
   re 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   re 14 1 (CS13⁻ ∷ []) ∷
   rw⁻ 13 (q14 c4) ∷
   re 17 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 10 (q15 c4) ∷
   re 8 1 (CS13 ∷ []) ∷
   rw⁻ 7 (q16 c4) ∷
   re 11 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 2 (q17 c4) ∷
   rw 2 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   rw⁻ 10 (q20 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw⁻ 8 (q22 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   rw⁻ 13 (q2 c4) ∷
   rw⁻ 14 (q24 c4) ∷
   rw 12 (q25 c4) ∷
   rw⁻ 13 (q2 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 23 (q26 c4) ∷
   rw⁻ 20 (q27 c4) ∷
   rw⁻ 17 (q28 c4) ∷
   rw⁻ 14 (q27 c4) ∷
   rw⁻ 11 (q29 c4) ∷
   rw 14 (q2 c4) ∷
   rw 15 (q2 c4) ∷
   rw 16 (q2 c4) ∷
   rw 17 (q2 c4) ∷
   rw⁻ 13 (q25 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw 11 (q2 c4) ∷
   rw 12 (q2 c4) ∷
   rw 10 (q23 c4) ∷
   rw⁻ 11 (q31 c4) ∷
   rw⁻ 10 (q32 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q21 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 8 (q24 c4) ∷
   rw 6 (q25 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   rw⁻ 13 (q2 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw⁻ 17 (q26 c4) ∷
   rw⁻ 14 (q27 c4) ∷
   rw⁻ 11 (q28 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw 8 (q2 c4) ∷
   rw 9 (q2 c4) ∷
   rw 10 (q2 c4) ∷
   rw 11 (q2 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 5 (q2 c4) ∷
   rw 6 (q2 c4) ∷
   rw 4 (q23 c4) ∷
   rw⁻ 5 (q31 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q2 c4) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 5 (q33 c4) ∷
   rw 5 (q34 c4) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q2 c4) ∷
   rw 8 (q2 c4) ∷
   rw 9 (q2 c4) ∷
   re 5 5 (Sb0-1-42-3 ∷ []) ∷
   re 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw⁻ 15 (q2 c4) ∷
   re 17 1 (CS13⁻ ∷ []) ∷
   rw⁻ 16 (q35 c4) ∷
   re 29 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 13 (q36 c4) ∷
   re 11 1 (CS13 ∷ []) ∷
   rw⁻ 10 (q37 c4) ∷
   re 23 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 7 (q36 c4) ∷
   rw 5 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   rw 5 (q19 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw⁻ 13 (q38 c4) ∷
   rw⁻ 12 (q21 c4) ∷
   rw⁻ 11 (q22 c4) ∷
   rw⁻ 10 (q21 c4) ∷
   rw⁻ 11 (q39 c4) ∷
   rw⁻ 14 (q31 c4) ∷
   rw⁻ 13 (q32 c4) ∷
   rw⁻ 12 (q31 c4) ∷
   rw⁻ 15 (q21 c4) ∷
   rw⁻ 14 (q22 c4) ∷
   rw⁻ 13 (q21 c4) ∷
   rw⁻ 15 (q23 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 20 (q40 c4) ∷
   rw 18 (q25 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 29 (q41 c4) ∷
   rw⁻ 26 (q42 c4) ∷
   rw⁻ 23 (q43 c4) ∷
   rw⁻ 20 (q42 c4) ∷
   rw⁻ 17 (q44 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw⁻ 19 (q25 c4) ∷
   rw⁻ 14 (q45 c4) ∷
   rw 17 (q2 c4) ∷
   rw 18 (q2 c4) ∷
   rw 16 (q23 c4) ∷
   rw⁻ 17 (q31 c4) ∷
   rw⁻ 16 (q32 c4) ∷
   rw⁻ 15 (q31 c4) ∷
   rw⁻ 18 (q21 c4) ∷
   rw⁻ 17 (q22 c4) ∷
   rw⁻ 16 (q21 c4) ∷
   rw⁻ 17 (q39 c4) ∷
   rw⁻ 20 (q31 c4) ∷
   rw⁻ 19 (q32 c4) ∷
   rw⁻ 18 (q31 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw⁻ 20 (q22 c4) ∷
   rw⁻ 19 (q21 c4) ∷
   rw⁻ 22 (q46 c4) ∷
   rw⁻ 21 (q47 c4) ∷
   rw⁻ 20 (q46 c4) ∷
   rw⁻ 23 (q31 c4) ∷
   rw⁻ 22 (q32 c4) ∷
   rw⁻ 21 (q31 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw⁻ 5 (q22 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw⁻ 6 (q31 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw⁻ 8 (q22 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   rw⁻ 13 (q2 c4) ∷
   rw⁻ 14 (q40 c4) ∷
   rw 12 (q25 c4) ∷
   rw⁻ 13 (q2 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 23 (q41 c4) ∷
   rw⁻ 20 (q42 c4) ∷
   rw⁻ 17 (q43 c4) ∷
   rw⁻ 14 (q42 c4) ∷
   rw⁻ 11 (q44 c4) ∷
   rw 14 (q2 c4) ∷
   rw 15 (q2 c4) ∷
   rw 16 (q2 c4) ∷
   rw 17 (q2 c4) ∷
   rw⁻ 13 (q25 c4) ∷
   rw⁻ 8 (q45 c4) ∷
   rw 11 (q2 c4) ∷
   rw 12 (q2 c4) ∷
   rw 10 (q23 c4) ∷
   rw⁻ 11 (q31 c4) ∷
   rw⁻ 10 (q32 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 12 (q21 c4) ∷
   rw⁻ 11 (q22 c4) ∷
   rw⁻ 10 (q21 c4) ∷
   rw⁻ 11 (q39 c4) ∷
   rw⁻ 14 (q31 c4) ∷
   rw⁻ 13 (q32 c4) ∷
   rw⁻ 12 (q31 c4) ∷
   rw⁻ 15 (q21 c4) ∷
   rw⁻ 14 (q22 c4) ∷
   rw⁻ 13 (q21 c4) ∷
   rw⁻ 16 (q46 c4) ∷
   rw⁻ 15 (q47 c4) ∷
   rw⁻ 14 (q46 c4) ∷
   rw⁻ 17 (q31 c4) ∷
   rw⁻ 16 (q32 c4) ∷
   rw⁻ 15 (q31 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw 17 (q33 c4) ∷
   rw 17 (q34 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   re 17 5 (Sb0-1-42-3 ∷ []) ∷
   rw 3 (q13 c4) ∷
   rw 4 (q13 c4) ∷
   rw 5 (q13 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw 1 (q11 c4) ∷
   re 5 1 (CS02 ∷ []) ∷
   rw⁻ 4 (q48 c4) ∷
   re 4 1 (Sb3-0-2-1 ∷ []) ∷
   rw 3 (q49 c4) ∷
   re 3 1 (CS02 ∷ []) ∷
   rw⁻ 2 (q48 c4) ∷
   re 2 1 (Sb3-0-2-1 ∷ []) ∷
   rw⁻ 6 (q11 c4) ∷
   rw 7 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw⁻ 14 (q13 c4) ∷
   rw⁻ 17 (q13 c4) ∷
   re 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   rw⁻ 14 (q2 c4) ∷
   re 16 1 (CS13⁻ ∷ []) ∷
   rw⁻ 15 (q14 c4) ∷
   re 19 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 12 (q15 c4) ∷
   re 10 1 (CS13 ∷ []) ∷
   rw⁻ 9 (q16 c4) ∷
   re 13 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 4 (q17 c4) ∷
   rw 4 (q18 c4) ∷
   rw 4 (q19 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw⁻ 10 (q22 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw⁻ 11 (q23 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw⁻ 15 (q2 c4) ∷
   rw⁻ 16 (q24 c4) ∷
   rw 14 (q25 c4) ∷
   rw⁻ 15 (q2 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 25 (q26 c4) ∷
   rw⁻ 22 (q27 c4) ∷
   rw⁻ 19 (q28 c4) ∷
   rw⁻ 16 (q27 c4) ∷
   rw⁻ 13 (q29 c4) ∷
   rw 16 (q2 c4) ∷
   rw 17 (q2 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw⁻ 15 (q25 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   rw 13 (q2 c4) ∷
   rw 14 (q2 c4) ∷
   rw 12 (q23 c4) ∷
   rw⁻ 13 (q31 c4) ∷
   rw⁻ 12 (q32 c4) ∷
   rw⁻ 11 (q31 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw⁻ 4 (q22 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   rw⁻ 10 (q24 c4) ∷
   rw 8 (q25 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw⁻ 15 (q2 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 19 (q26 c4) ∷
   rw⁻ 16 (q27 c4) ∷
   rw⁻ 13 (q28 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 10 (q2 c4) ∷
   rw 11 (q2 c4) ∷
   rw 12 (q2 c4) ∷
   rw 13 (q2 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw 7 (q2 c4) ∷
   rw 8 (q2 c4) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   rw⁻ 5 (q31 c4) ∷
   rw 8 (q2 c4) ∷
   rw 9 (q2 c4) ∷
   rw 10 (q2 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 7 (q33 c4) ∷
   rw 7 (q34 c4) ∷
   rw 8 (q2 c4) ∷
   rw 9 (q2 c4) ∷
   rw 10 (q2 c4) ∷
   rw 11 (q2 c4) ∷
   re 7 5 (Sb0-1-42-3 ∷ []) ∷
   re 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 8 (q2 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   rw⁻ 14 (q2 c4) ∷
   rw⁻ 17 (q2 c4) ∷
   re 19 1 (CS13⁻ ∷ []) ∷
   rw⁻ 18 (q35 c4) ∷
   re 31 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 15 (q36 c4) ∷
   re 13 1 (CS13 ∷ []) ∷
   rw⁻ 12 (q37 c4) ∷
   re 25 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 9 (q36 c4) ∷
   rw 7 (q17 c4) ∷
   rw 7 (q18 c4) ∷
   rw 7 (q19 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   rw⁻ 14 (q2 c4) ∷
   rw⁻ 15 (q38 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw⁻ 13 (q22 c4) ∷
   rw⁻ 12 (q21 c4) ∷
   rw⁻ 13 (q39 c4) ∷
   rw⁻ 16 (q31 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw⁻ 14 (q31 c4) ∷
   rw⁻ 17 (q21 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw⁻ 15 (q21 c4) ∷
   rw⁻ 17 (q23 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 22 (q40 c4) ∷
   rw 20 (q25 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 30 (q2 c4) ∷
   rw⁻ 31 (q41 c4) ∷
   rw⁻ 28 (q42 c4) ∷
   rw⁻ 25 (q43 c4) ∷
   rw⁻ 22 (q42 c4) ∷
   rw⁻ 19 (q44 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw 24 (q2 c4) ∷
   rw 25 (q2 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw⁻ 16 (q45 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw 18 (q23 c4) ∷
   rw⁻ 19 (q31 c4) ∷
   rw⁻ 18 (q32 c4) ∷
   rw⁻ 17 (q31 c4) ∷
   rw⁻ 20 (q21 c4) ∷
   rw⁻ 19 (q22 c4) ∷
   rw⁻ 18 (q21 c4) ∷
   rw⁻ 19 (q39 c4) ∷
   rw⁻ 22 (q31 c4) ∷
   rw⁻ 21 (q32 c4) ∷
   rw⁻ 20 (q31 c4) ∷
   rw⁻ 23 (q21 c4) ∷
   rw⁻ 22 (q22 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw⁻ 24 (q46 c4) ∷
   rw⁻ 23 (q47 c4) ∷
   rw⁻ 22 (q46 c4) ∷
   rw⁻ 25 (q31 c4) ∷
   rw⁻ 24 (q32 c4) ∷
   rw⁻ 23 (q31 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw⁻ 7 (q39 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw⁻ 9 (q32 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw⁻ 10 (q22 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw⁻ 11 (q23 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw⁻ 15 (q2 c4) ∷
   rw⁻ 16 (q40 c4) ∷
   rw 14 (q25 c4) ∷
   rw⁻ 15 (q2 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 25 (q41 c4) ∷
   rw⁻ 22 (q42 c4) ∷
   rw⁻ 19 (q43 c4) ∷
   rw⁻ 16 (q42 c4) ∷
   rw⁻ 13 (q44 c4) ∷
   rw 16 (q2 c4) ∷
   rw 17 (q2 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw⁻ 15 (q25 c4) ∷
   rw⁻ 10 (q45 c4) ∷
   rw 13 (q2 c4) ∷
   rw 14 (q2 c4) ∷
   rw 12 (q23 c4) ∷
   rw⁻ 13 (q31 c4) ∷
   rw⁻ 12 (q32 c4) ∷
   rw⁻ 11 (q31 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw⁻ 13 (q22 c4) ∷
   rw⁻ 12 (q21 c4) ∷
   rw⁻ 13 (q39 c4) ∷
   rw⁻ 16 (q31 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw⁻ 14 (q31 c4) ∷
   rw⁻ 17 (q21 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw⁻ 15 (q21 c4) ∷
   rw⁻ 18 (q46 c4) ∷
   rw⁻ 17 (q47 c4) ∷
   rw⁻ 16 (q46 c4) ∷
   rw⁻ 19 (q31 c4) ∷
   rw⁻ 18 (q32 c4) ∷
   rw⁻ 17 (q31 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw 19 (q33 c4) ∷
   rw 19 (q34 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   re 19 5 (Sb0-1-42-3 ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw 6 (q13 c4) ∷
   rw 7 (q13 c4) ∷
   rw 8 (q13 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw 3 (q11 c4) ∷
   re 7 1 (CS02⁻ ∷ []) ∷
   rw⁻ 6 (q50 c4) ∷
   re 6 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw 5 (q51 c4) ∷
   re 5 1 (CS02⁻ ∷ []) ∷
   rw⁻ 4 (q50 c4) ∷
   re 4 1 (Sb⁻3-0-2-1 ∷ []) ∷
   re 0 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (Bx0-1423 ∷ []) (Bx0-4123 ∷ []) (lem-sym12-at243243 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (X4 ∷ Bx0-4123 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx0-4123 ∷ []) (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ []) (X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (wl0802 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (Bx0-1423 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (Bx0-1423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (Bx0-1423 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (Toff324 ∷ Toff324 ∷ []) [] (wl0616 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (Bx0-4123 ∷ []) (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx0-4213 ∷ []) (Bx0-4231 ∷ []) (lem-sym34-at143143 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (Toff324 ∷ Bx0-4231 ∷ Toff324 ∷ []) (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx0-4231 ∷ []) (Bx0-4213 ∷ []) (lem-sym34-at1441 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Bx0-4213 ∷ []) (Bx0-4123 ∷ []) (lem-sym23-at143143 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (Bx0-1423 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Bx0-1423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ124 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ []) (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ []) (wl0803 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ124 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ []) (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ []) (wl0804 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl0351 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Bx0-1423 ∷ Bx0-1423 ∷ []) [] (lem-beta-inv-at243243 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS12 ∷ []) (wl0805 (lit c4))

-- F5 CS12: 38 steps
lem-F5-CS12 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-F5-CS12 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 1 (q52 c4) ∷
   rw 0 (q53 c4) ∷
   rw 1 (q54 c4) ∷
   re 8 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 10 1 (CS13 ∷ []) ∷
   re 12 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw 3 (q58 c4) ∷
   rw⁻ 4 (q59 c4) ∷
   rw 6 (q52 c4) ∷
   rw 6 (q60 c4) ∷
   rw 6 (q61 c4) ∷
   rw 5 (q62 c4) ∷
   rw 5 (q63 c4) ∷
   rw 5 (q64 c4) ∷
   rw 5 (q54 c4) ∷
   rw 5 (q65 c4) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 7 (q59 c4) ∷
   rw 9 (q52 c4) ∷
   rw 9 (q60 c4) ∷
   rw 9 (q61 c4) ∷
   rw 8 (q62 c4) ∷
   rw 8 (q63 c4) ∷
   rw 8 (q64 c4) ∷
   rw 8 (q54 c4) ∷
   rw 8 (q65 c4) ∷
   rw⁻ 1 (q67 c4) ∷
   rw⁻ 2 (q68 c4) ∷
   rw 1 (q69 c4) ∷
   rw 7 (q70 c4) ∷
   rw 0 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl0035 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (CS02 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS02 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (Sw01 ∷ Sb1-0-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wl0138 (lit c4))

-- auto CS01 | SBOX(2;0;31;4) @0112203443: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0112203443 : Ws → ⟪ (CS12 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0112203443 c4 = derive (CS12 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS12 ∷ [])
  (rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   rw 2 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw 0 (q76 c4) ∷
   rw⁻ 1 (q77 c4) ∷
   rw 2 (q72 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ []) (lem-F5-CS12 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp0055 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (Toff014 ∷ Toff014 ∷ []) [] (wp0269 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ []) [] (wl0806 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (CS13 ∷ CS13⁻ ∷ []) [] (wl0807 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (CS13⁻ ∷ CS13 ∷ []) [] (wl0808 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (CS12 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS12 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0112203443 c4)

-- F4 CS12^0|CS12^1: 63 steps
lem-F4-CS12ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣CS12ᵖ1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 0 (q78 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   re 5 1 (Bx0-13 ∷ []) ∷
   re 8 1 (Bx0-13 ∷ []) ∷
   re 3 6 (Bx1-023 ∷ []) ∷
   re 4 1 (Bx⁻0-13 ∷ []) ∷
   re 7 1 (Bx⁻0-13 ∷ []) ∷
   re 4 6 (Bx⁻1-023 ∷ []) ∷
   rw⁻ 4 (q80 c4) ∷
   rw⁻ 5 (q79 c4) ∷
   rw⁻ 6 (q81 c4) ∷
   re 8 1 (Bx0-13 ∷ []) ∷
   re 11 1 (Bx0-13 ∷ []) ∷
   re 6 6 (Bx1-023 ∷ []) ∷
   re 7 1 (Bx⁻0-13 ∷ []) ∷
   re 10 1 (Bx⁻0-13 ∷ []) ∷
   re 7 6 (Bx⁻1-023 ∷ []) ∷
   re 1 6 (Bx0-1423 ∷ []) ∷
   re 2 6 (Bx⁻0-1423 ∷ []) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   re 3 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q59 c4) ∷
   rw⁻ 5 (q83 c4) ∷
   re 5 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 1 5 (Sb0-1-42-3 ∷ []) ∷
   re 2 5 (Sb⁻0-1-42-3 ∷ []) ∷
   rw 0 (q84 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   re 5 1 (Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) ∷
   re 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 8 1 (CS13⁻ ∷ []) ∷
   re 9 1 (CS13 ∷ []) ∷
   rw 8 (q83 c4) ∷
   rw 7 (q59 c4) ∷
   re 6 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 6 (q82 c4) ∷
   rw 5 (q59 c4) ∷
   re 5 1 (Bx⁻1-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) ∷
   re 4 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) ∷
   re 9 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   re 11 1 (CZ13 ∷ []) ∷
   re 14 1 (CZ13 ∷ []) ∷
   re 15 1 (Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-13 ∷ Toff102 ∷ CCZ012 ∷ []) ∷
   re 15 1 (CZ13 ∷ []) ∷
   re 18 1 (CZ13 ∷ []) ∷
   rw 9 (q81 c4) ∷
   rw 8 (q79 c4) ∷
   rw 7 (q80 c4) ∷
   re 6 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   re 8 1 (CZ13 ∷ []) ∷
   re 11 1 (CZ13 ∷ []) ∷
   re 12 1 (Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-13 ∷ Toff102 ∷ CCZ012 ∷ []) ∷
   re 12 1 (CZ13 ∷ []) ∷
   re 15 1 (CZ13 ∷ []) ∷
   rw 6 (q81 c4) ∷
   rw 5 (q80 c4) ∷
   rw 4 (q79 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (Sw12 ∷ Bx0-3421 ∷ []) (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (Bx0-3412 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-beta-T-at13243142 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (Sw12 ∷ Toff034 ∷ []) (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 (lit c4))

-- beta-T @13243241: 8 steps
lem-beta-T-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-beta-T-at13243241 c4 = derive (Bx0-3421 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 1 (q87 c4) ∷
   rw 0 (q88 c4) ∷
   rw⁻ 1 (q89 c4) ∷
   rw 2 (q88 c4) ∷
   rw⁻ 3 (q89 c4) ∷
   rw 4 (q85 c4) ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = eqn (Bx0-3421 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-beta-T-at13243241 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (Sb⁻0-1-2-3 ∷ Toff034 ∷ []) (Toff034 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ012 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ012 ∷ []) (wl0809 (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(0;3421): 10 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ : Ws → ⟪ (Sb⁻0-1-2-3 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ c4 = derive (Sb⁻0-1-2-3 ∷ Bx0-3421 ∷ []) (Bx0-3421 ∷ Sb⁻0-1-2-3 ∷ [])
  (rw 1 (q90 c4) ∷
   rw 0 (q91 c4) ∷
   re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 1 (q92 c4) ∷
   re 2 1 (Sb⁻0-1-2-3 ∷ []) ∷
   rw 2 (q91 c4) ∷
   re 3 1 (CS12⁻ ∷ []) ∷
   rw⁻ 3 (q92 c4) ∷
   re 4 1 (Sb⁻0-1-2-3 ∷ []) ∷
   rw⁻ 0 (q90 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = eqn (Sb0-1-2-3 ∷ Toff034 ∷ []) (Toff034 ∷ Sb0-1-2-3 ∷ []) (lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (CCZ012 ∷ CS12 ∷ []) (CS12 ∷ CCZ012 ∷ []) (wl0810 (lit c4))

-- auto SBOX(0;1;2;3) | BOX(0;3421): 10 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ : Ws → ⟪ (Sb0-1-2-3 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ c4 = derive (Sb0-1-2-3 ∷ Bx0-3421 ∷ []) (Bx0-3421 ∷ Sb0-1-2-3 ∷ [])
  (rw 1 (q90 c4) ∷
   rw 0 (q93 c4) ∷
   re 1 1 (CS12 ∷ []) ∷
   rw⁻ 1 (q94 c4) ∷
   re 2 1 (Sb0-1-2-3 ∷ []) ∷
   rw 2 (q93 c4) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw⁻ 3 (q94 c4) ∷
   re 4 1 (Sb0-1-2-3 ∷ []) ∷
   rw⁻ 0 (q90 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw12 ∷ Bx0-2314 ∷ []) (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (Toff013 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Toff013 ∷ []) (lem-T-beta-at2332 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (Sw12 ∷ Bx0-1324 ∷ []) (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 (lit c4))

-- T-beta @122331: 7 steps
lem-T-beta-at122331 : Ws → ⟪ (Toff023 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ Toff023 ∷ []) ⟫ʷ
lem-T-beta-at122331 c4 = derive (Toff023 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ Toff023 ∷ [])
  (rw⁻ 0 (q85 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 0 (q98 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q85 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (Toff023 ∷ []) (Toff023 ∷ []) (wl0811 (lit c4))
  q101 : Ws → Eqn
  q101 c4 = eqn (Bx0-1234 ∷ []) (Bx0-2134 ∷ []) (lem-sym12 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2314 ∷ []) (lem-sym23-at1221 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (Toff023 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ Toff023 ∷ []) (lem-T-beta-at122331 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2134 ∷ []) (lem-sym23-at122331 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (Bx0-2134 ∷ []) (Bx0-1234 ∷ []) (lem-sym12-at1221 c4)

-- auto BOX(0;1234) | TOFF032: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF032 : Ws → ⟪ (Bx0-1234 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF032 c4 = derive (Bx0-1234 ∷ Toff023 ∷ []) (Toff023 ∷ Bx0-1234 ∷ [])
  (rw 1 (q100 c4) ∷
   rw 0 (q101 c4) ∷
   rw 0 (q102 c4) ∷
   rw⁻ 0 (q103 c4) ∷
   rw 1 (q104 c4) ∷
   rw 1 (q105 c4) ∷
   rw 0 (q100 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ014 ∷ []) (CCZ014 ∷ []) (wp0285 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1243 ∷ []) (lem-sym34 c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1423 ∷ []) (lem-sym23-at3443 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (CCZ014 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ []) (lem-Cz-beta-at243243 c4)
  q110 : Ws → Eqn
  q110 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1243 ∷ []) (lem-sym23-at243243 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1234 ∷ []) (lem-sym34-at3443 c4)

-- auto BOX(0;1234) | CCZ041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ041 : Ws → ⟪ (Bx0-1234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ041 c4 = derive (Bx0-1234 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx0-1234 ∷ [])
  (rw 1 (q106 c4) ∷
   rw 0 (q107 c4) ∷
   rw 0 (q108 c4) ∷
   rw⁻ 0 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw 1 (q111 c4) ∷
   rw 0 (q106 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (Bx0-3241 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at133441 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (Bx0-1234 ∷ Toff023 ∷ []) (Toff023 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF032 c4)
  q114 : Ws → Eqn
  q114 c4 = eqn (Bx0-1234 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ041 c4)

-- auto BOX(0;1234) | BOX(0;3241): 6 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·3241⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·3241⟩ c4 = derive (Bx0-1234 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Bx0-1234 ∷ [])
  (rw 1 (q112 c4) ∷
   rw 0 (q113 c4) ∷
   rw 1 (q114 c4) ∷
   rw 2 (q113 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 0 (q112 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw23 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ (lit c4))
  q117 : Ws → Eqn
  q117 c4 = eqn (Sw23 ∷ Bx0-2431 ∷ []) (Bx0-3421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2431⟩ (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (Sb⁻0-1-2-3 ∷ Bx0-3421 ∷ []) (Bx0-3421 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (Sw23 ∷ Bx0-3421 ∷ []) (Bx0-2431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3421⟩ (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(0;3421) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 : Ws → ⟪ (Sb⁻0-1-3-2 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 c4 = derive (Sb⁻0-1-3-2 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ Sb⁻0-1-3-2 ∷ [])
  (rw⁻ 0 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 0 (q119 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q115 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (Sw34 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ (lit c4))
  q123 : Ws → Eqn
  q123 c4 = eqn (Sw34 ∷ Bx0-2341 ∷ []) (Bx0-2431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2341⟩ (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (Sb⁻0-1-3-2 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (Sw34 ∷ Bx0-2431 ∷ []) (Bx0-2341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2431⟩ (lit c4))
  q126 : Ws → Eqn
  q126 c4 = eqn (Sw34 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(0;3421) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 : Ws → ⟪ (Sb⁻0-1-4-2 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 c4 = derive (Sb⁻0-1-4-2 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ Sb⁻0-1-4-2 ∷ [])
  (rw⁻ 0 (q121 c4) ∷
   rw 1 (q122 c4) ∷
   rw 2 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   rw 0 (q125 c4) ∷
   rw 1 (q126 c4) ∷
   rw 2 (q121 c4) ∷ []) Eq.refl

private
  q127 : Ws → Eqn
  q127 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ (lit c4))
  q128 : Ws → Eqn
  q128 c4 = eqn (Sw23 ∷ Bx0-3241 ∷ []) (Bx0-2341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3241⟩ (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (Sb⁻0-1-4-2 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (Sw23 ∷ Bx0-2341 ∷ []) (Bx0-3241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2341⟩ (lit c4))
  q131 : Ws → Eqn
  q131 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(0;3421) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 : Ws → ⟪ (Sb⁻0-1-4-3 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 c4 = derive (Sb⁻0-1-4-3 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Sb⁻0-1-4-3 ∷ [])
  (rw⁻ 0 (q115 c4) ∷
   rw 1 (q127 c4) ∷
   rw 2 (q128 c4) ∷
   rw 1 (q129 c4) ∷
   rw 0 (q130 c4) ∷
   rw 1 (q131 c4) ∷
   rw 2 (q115 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = eqn (Sw23 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ (lit c4))
  q133 : Ws → Eqn
  q133 c4 = eqn (Sb0-1-2-3 ∷ Bx0-3421 ∷ []) (Bx0-3421 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (Sw23 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(0;3421) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 : Ws → ⟪ (Sb0-1-3-2 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 c4 = derive (Sb0-1-3-2 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ Sb0-1-3-2 ∷ [])
  (rw⁻ 0 (q115 c4) ∷
   rw 1 (q132 c4) ∷
   rw 2 (q117 c4) ∷
   rw 1 (q133 c4) ∷
   rw 0 (q119 c4) ∷
   rw 1 (q134 c4) ∷
   rw 2 (q115 c4) ∷ []) Eq.refl

private
  q135 : Ws → Eqn
  q135 c4 = eqn (Sw34 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (Sb0-1-3-2 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (Sw34 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(0;3421) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 : Ws → ⟪ (Sb0-1-4-2 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 c4 = derive (Sb0-1-4-2 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ Sb0-1-4-2 ∷ [])
  (rw⁻ 0 (q121 c4) ∷
   rw 1 (q135 c4) ∷
   rw 2 (q123 c4) ∷
   rw 1 (q136 c4) ∷
   rw 0 (q125 c4) ∷
   rw 1 (q137 c4) ∷
   rw 2 (q121 c4) ∷ []) Eq.refl

private
  q138 : Ws → Eqn
  q138 c4 = eqn (Sw23 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (Sb0-1-4-2 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (Sw23 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(0;3421) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 : Ws → ⟪ (Sb0-1-4-3 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 c4 = derive (Sb0-1-4-3 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Sb0-1-4-3 ∷ [])
  (rw⁻ 0 (q115 c4) ∷
   rw 1 (q138 c4) ∷
   rw 2 (q128 c4) ∷
   rw 1 (q139 c4) ∷
   rw 0 (q130 c4) ∷
   rw 1 (q140 c4) ∷
   rw 2 (q115 c4) ∷ []) Eq.refl

private
  q141 : Ws → Eqn
  q141 c4 = eqn (Sb⁻0-1-4-3 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (Toff423 ∷ Toff423 ∷ []) [] (wl0296 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (Toff423 ∷ []) (Toff423 ∷ []) (wl0812 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (Toff423 ∷ Bx0-3241 ∷ Toff423 ∷ []) (Bx0-3241 ∷ CCZ123 ∷ []) (lem-T312-beta-at133441 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (Sb0-1-4-3 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (Bx0-1234 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·3241⟩ c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (CCZ123 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (wl0357 (lit c4))
  q148 : Ws → Eqn
  q148 c4 = eqn (CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (wl0358 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0212 (lit c4))

-- auto SBOX(0;1;23;4) | BOX(0;3241): 22 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩ c4 = derive (Sb0-1-23-4 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   rw 4 (q141 c4) ∷
   rw⁻ 5 (q142 c4) ∷
   rw 3 (q143 c4) ∷
   rw 5 (q143 c4) ∷
   rw 3 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw⁻ 3 (q142 c4) ∷
   rw 1 (q143 c4) ∷
   rw 3 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q146 c4) ∷
   re 7 1 (CS14⁻ ∷ []) ∷
   rw 5 (q147 c4) ∷
   re 6 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14 ∷ []) ∷
   re 6 1 (CS14⁻ ∷ []) ∷
   rw 2 (q148 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw 6 (q149 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = eqn (CCZ012 ∷ []) (CCZ012 ∷ []) (wl0813 (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (Bx3-2401 ∷ []) (Bx3-2041 ∷ []) (lem-sym23-at0312243041 c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (CCZ012 ∷ Bx3-2041 ∷ []) (Bx3-2041 ∷ CCZ012 ∷ []) (lem-c124-beta-at0312203441 c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (Bx3-2041 ∷ []) (Bx3-2401 ∷ []) (lem-sym23-at0312203441 c4)

-- auto CCZ012 | BOX(3;2401): 5 steps
lem-auto-CCZ012-∣-BOX⟨3·2401⟩ : Ws → ⟪ (CCZ012 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·2401⟩ c4 = derive (CCZ012 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ CCZ012 ∷ [])
  (rw 0 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 0 (q152 c4) ∷
   rw 0 (q153 c4) ∷
   rw 1 (q150 c4) ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ012 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·2401⟩ c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (CCZ012 ∷ Toff104 ∷ CS12 ∷ Toff104 ∷ []) (Toff104 ∷ CS12 ∷ Toff104 ∷ CCZ012 ∷ []) (wp0418 c4)

-- auto CCZ012 | SBOX(3;2;40;1): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩ : Ws → ⟪ (CCZ012 ∷ Sb3-2-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-2-40-1 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩ c4 = derive (CCZ012 ∷ Sb3-2-40-1 ∷ []) (Sb3-2-40-1 ∷ CCZ012 ∷ [])
  (re 1 1 (Bx3-2401 ∷ Toff104 ∷ Sb3-2-1-0 ∷ Toff104 ∷ Sb⁻3-2-1-0 ∷ []) ∷
   rw 0 (q154 c4) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw 1 (q155 c4) ∷
   re 2 1 (Sb3-2-1-0 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 4 (q92 c4) ∷
   re 4 1 (Sb⁻3-2-1-0 ∷ []) ∷
   re 0 5 (Sb3-2-40-1 ∷ []) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = eqn (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4)
  q157 : Ws → Eqn
  q157 c4 = eqn (Sb0-1-32-4 ∷ CS13 ∷ []) (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOX(0;3;1;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩ c4 = derive (Sb0-1-23-4 ∷ Sb0-3-1-4 ∷ []) (Sb0-3-1-4 ∷ Sb0-1-23-4 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw 0 (q156 c4) ∷
   rw 0 (q157 c4) ∷
   rw⁻ 1 (q156 c4) ∷
   re 0 1 (Sb0-3-1-4 ∷ []) ∷ []) Eq.refl

private
  q158 : Ws → Eqn
  q158 c4 = eqn (CS12⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS12⁻ ∷ []) (wl0814 (lit c4))
  q159 : Ws → Eqn
  q159 c4 = eqn (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) (wl0815 (lit c4))
  q160 : Ws → Eqn
  q160 c4 = eqn (CS12⁻ ∷ CS14 ∷ []) (CS14 ∷ CS12⁻ ∷ []) (wl0816 (lit c4))
  q161 : Ws → Eqn
  q161 c4 = eqn (Bx0-1234 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21 c4)

-- auto SBOX(0;1;23;4) | CSd21: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21 : Ws → ⟪ (Sb0-1-23-4 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21 c4 = derive (Sb0-1-23-4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q158 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 3 (q159 c4) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 2 (q160 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q159 c4) ∷
   rw 0 (q161 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q162 : Ws → Eqn
  q162 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (Sw23 ∷ CS13⁻ ∷ []) (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 (lit c4))
  q164 : Ws → Eqn
  q164 c4 = eqn (Sb0-1-23-4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (Sw23 ∷ CS12⁻ ∷ []) (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CSd21 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21-at2332 c4 = derive (Sb0-1-32-4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q115 c4) ∷
   rw 1 (q162 c4) ∷
   rw 2 (q163 c4) ∷
   rw 1 (q164 c4) ∷
   rw 0 (q165 c4) ∷
   rw 1 (q166 c4) ∷
   rw 2 (q115 c4) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = eqn (Sb0-1-32-4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOXd(0;3;1;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩ c4 = derive (Sb0-1-23-4 ∷ Sb⁻0-3-1-4 ∷ []) (Sb⁻0-3-1-4 ∷ Sb0-1-23-4 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw 0 (q156 c4) ∷
   rw 0 (q167 c4) ∷
   rw⁻ 1 (q156 c4) ∷
   re 0 1 (Sb⁻0-3-1-4 ∷ []) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = eqn (Sb0-1-23-4 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩ c4)

-- auto SBOX(0;1;23;4) | BOX(0;3241) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q115 c4) ∷
   rw 1 (q162 c4) ∷
   rw 2 (q130 c4) ∷
   rw 1 (q168 c4) ∷
   rw 0 (q128 c4) ∷
   rw 1 (q166 c4) ∷
   rw 2 (q115 c4) ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = eqn (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4))
  q170 : Ws → Eqn
  q170 c4 = eqn (Sb0-1-32-4 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at2332 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | BOX(0;3241) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q121 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q125 c4) ∷
   rw 1 (q170 c4) ∷
   rw 0 (q123 c4) ∷
   rw 1 (q171 c4) ∷
   rw 2 (q121 c4) ∷ []) Eq.refl

private
  q172 : Ws → Eqn
  q172 c4 = eqn (Sw12 ∷ Sb3-1-40-2 ∷ []) (Sb3-2-40-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·1·40·2⟩ (lit c4))
  q173 : Ws → Eqn
  q173 c4 = eqn (CCZ012 ∷ Sb3-2-40-1 ∷ []) (Sb3-2-40-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩ c4)
  q174 : Ws → Eqn
  q174 c4 = eqn (Sw12 ∷ Sb3-2-40-1 ∷ []) (Sb3-1-40-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·2·40·1⟩ (lit c4))

-- auto CCZ012 | SBOX(3;2;40;1) @1221: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at1221 : Ws → ⟪ (CCZ012 ∷ Sb3-1-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-40-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at1221 c4 = derive (CCZ012 ∷ Sb3-1-40-2 ∷ []) (Sb3-1-40-2 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q85 c4) ∷
   rw⁻ 1 (q89 c4) ∷
   rw 2 (q172 c4) ∷
   rw 1 (q173 c4) ∷
   rw 0 (q174 c4) ∷
   rw⁻ 1 (q89 c4) ∷
   rw 2 (q85 c4) ∷ []) Eq.refl

private
  q175 : Ws → Eqn
  q175 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4))
  q176 : Ws → Eqn
  q176 c4 = eqn (Sw23 ∷ Sb2-1-40-3 ∷ []) (Sb3-1-40-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·40·3⟩ (lit c4))
  q177 : Ws → Eqn
  q177 c4 = eqn (CCZ012 ∷ Sb3-1-40-2 ∷ []) (Sb3-1-40-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at1221 c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (Sw23 ∷ Sb3-1-40-2 ∷ []) (Sb2-1-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·40·2⟩ (lit c4))
  q179 : Ws → Eqn
  q179 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4))

-- auto CCZ012 | SBOX(3;2;40;1) @132132: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at132132 : Ws → ⟪ (CCZ013 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at132132 c4 = derive (CCZ013 ∷ Sb2-1-40-3 ∷ []) (Sb2-1-40-3 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q115 c4) ∷
   rw 1 (q175 c4) ∷
   rw 2 (q176 c4) ∷
   rw 1 (q177 c4) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q179 c4) ∷
   rw 2 (q115 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = eqn (CCZ013 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ013 ∷ []) (wl0100 (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (Sw01 ∷ Sb2-0-41-3 ∷ []) (Sb2-1-40-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·41·3⟩ (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn (CCZ013 ∷ Sb2-1-40-3 ∷ []) (Sb2-1-40-3 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at132132 c4)
  q183 : Ws → Eqn
  q183 c4 = eqn (Sw01 ∷ Sb2-1-40-3 ∷ []) (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ (lit c4))

-- auto CCZ012 | SBOX(3;2;40;1) @01132032: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at01132032 : Ws → ⟪ (CCZ013 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at01132032 c4 = derive (CCZ013 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw 2 (q181 c4) ∷
   rw 1 (q182 c4) ∷
   rw 0 (q183 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw 2 (q72 c4) ∷ []) Eq.refl

private
  q184 : Ws → Eqn
  q184 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4))
  q185 : Ws → Eqn
  q185 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4))
  q186 : Ws → Eqn
  q186 c4 = eqn (CCZ013 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at01132032 c4)
  q187 : Ws → Eqn
  q187 c4 = eqn (Sw12 ∷ Sb2-0-41-3 ∷ []) (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4))
  q188 : Ws → Eqn
  q188 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4))

-- auto CCZ012 | SBOX(3;2;40;1) @02132031: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132031 : Ws → ⟪ (CCZ023 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132031 c4 = derive (CCZ023 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q85 c4) ∷
   rw 1 (q184 c4) ∷
   rw 2 (q185 c4) ∷
   rw 1 (q186 c4) ∷
   rw 0 (q187 c4) ∷
   rw 1 (q188 c4) ∷
   rw 2 (q85 c4) ∷ []) Eq.refl

private
  q189 : Ws → Eqn
  q189 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 (lit c4))
  q190 : Ws → Eqn
  q190 c4 = eqn (CCZ023 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132031 c4)
  q191 : Ws → Eqn
  q191 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 (lit c4))

-- auto CCZ012 | SBOX(3;2;40;1) @02132130: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132130 : Ws → ⟪ (CCZ123 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132130 c4 = derive (CCZ123 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q189 c4) ∷
   rw 2 (q74 c4) ∷
   rw 1 (q190 c4) ∷
   rw 0 (q76 c4) ∷
   rw⁻ 1 (q191 c4) ∷
   rw 2 (q72 c4) ∷ []) Eq.refl
