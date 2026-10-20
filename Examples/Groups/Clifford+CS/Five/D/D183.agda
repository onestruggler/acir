{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D183 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0096 ; wl0103 ; wl0212 ; wl0214 ; wl0227 ; wl0283 ; wl0296 ; wl0341 ; wl0357 ; wl0358 ; wl0402 ; wl0602 ; wl0813 ; wl0848 ; wl0849 ; wl0850 ; wl0851 ; wl0852 ; wl0859 ; wl0860 ; wl0861 ; wl0862 ; wl0863 ; wl0864 ; wl0865 ; wl0866 ; wl0867 ; wl0868 ; wl0869 ; wl0870 ; wl0871 ; wl0872 ; wl0873 ; wp0440 ; wp0448 ; wp0449 ; wp0450 ; wp0451 ; wp0452 ; wp0453 ; wp0454 ; wp0455 ; wp0456)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at12243143 ; lem-sym12-at14213243 ; lem-sym23)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-Cz-beta-at2332 ; lem-sym12-at243243 ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym23-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-SBsym-at0113203442 ; lem-T312-beta-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-sym23-at0310243241 ; lem-sym23-at03103441)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-beta-T-at12213443 ; lem-sym23-at12233441 ; lem-sym23-at122441 ; lem-sym34-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D174 using (lem-beta-T-at143143)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-auto-BOX⟨0·1234⟩-∣-TOFF042 ; lem-c124-beta-at03103441)
open import Examples.Groups.Clifford+CS.Five.D.D181 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at122441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D182 using (lem-F4-CS23ᵖ0∣CS01ᵖ1-part0)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ013 ; lem-nat-2-BOX⟨0·2413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-SBOX⟨0·2·43·1⟩ ; lem-nat-0-SBOX⟨1·2·43·0⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨0·4213⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨3·0421⟩ ; lem-nat-0-BOX⟨3·1420⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-BOX⟨0·4123⟩ ; lem-nat-2-BOX⟨0·4213⟩ ; lem-nat-2-BOX⟨0·4312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-0-BOX⟨3·0241⟩ ; lem-nat-0-BOX⟨3·1240⟩ ; lem-nat-1-SBOX⟨0·1·3·2⟩ ; lem-nat-1-SBOX⟨0·2·3·1⟩ ; lem-nat-1-SBOX⟨2·1·43·0⟩ ; lem-nat-1-SBOXd⟨0·1·3·2⟩ ; lem-nat-1-SBOXd⟨0·2·3·1⟩ ; lem-nat-2-SBOX⟨2·1·43·0⟩ ; lem-nat-2-SBOX⟨3·1·42·0⟩ ; lem-nat-3-BOX⟨0·3412⟩ ; lem-nat-3-BOX⟨0·4312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-1-SBOX⟨1·2·43·0⟩ ; lem-nat-2-SBOX⟨0·2·3·1⟩ ; lem-nat-2-SBOX⟨0·3·2·1⟩ ; lem-nat-2-SBOX⟨0·4·2·1⟩ ; lem-nat-2-SBOX⟨0·4·3·1⟩ ; lem-nat-2-SBOXd⟨0·2·3·1⟩ ; lem-nat-2-SBOXd⟨0·3·2·1⟩ ; lem-nat-2-SBOXd⟨0·4·2·1⟩ ; lem-nat-2-SBOXd⟨0·4·3·1⟩ ; lem-nat-3-SBOX⟨0·3·2·1⟩ ; lem-nat-3-SBOX⟨0·4·2·1⟩ ; lem-nat-3-SBOXd⟨0·3·2·1⟩ ; lem-nat-3-SBOXd⟨0·4·2·1⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) (wl0863 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) (wl0864 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) (wl0865 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2413 ∷ []) (lem-sym34-at122441 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx0-2143 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) (wp0449 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (K3 ∷ X4 ∷ []) (X4 ∷ K3 ∷ []) (c₄ (K ↑ ↑ ↑) (X))
  q10 : Ws → Eqn
  q10 c4 = eqn (Toff012 ∷ K3 ∷ []) (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K))
  q11 : Ws → Eqn
  q11 c4 = eqn (CX14 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (X4 ∷ Toff012 ∷ X4 ∷ CX14 ∷ []) (wp0450 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (K3⁻ ∷ X4 ∷ []) (X4 ∷ K3⁻ ∷ []) (c₄ ((K • iI) ↑ ↑ ↑) (X))
  q13 : Ws → Eqn
  q13 c4 = eqn (Toff012 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI))
  q14 : Ws → Eqn
  q14 c4 = eqn (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wl0341 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ []) (wl0866 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ []) (wp0451 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ []) (wl0867 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS34⁻ ∷ []) (wl0868 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ []) (wl0869 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ []) (wl0870 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ []) (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS13 ∷ Toff012 ∷ []) (Toff012 ∷ CS13 ∷ []) (wl0214 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (K3⁻ ∷ K3 ∷ []) [] (wl0859 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0227 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ []) (wp0452 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Sb0-2-43-1 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at122441 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (wl0860 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (wl0861 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (wl0862 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (wp0448 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ []) (wl0848 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ []) (wp0440 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) (wl0849 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ []) (wl0850 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (wl0851 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ X4 ∷ CS34 ∷ []) (wl0852 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ []) (wp0453 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (Sb0-2-43-1 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at122441 c4)

-- F4 CS23^0|CS01^1 part1: 392 steps
lem-F4-CS23ᵖ0∣CS01ᵖ1-part1 : Ws → ⟪ (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣CS01ᵖ1-part1 c4 = derive (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   re 17 1 (CS12⁻ ∷ []) ∷
   rw⁻ 16 (q2 c4) ∷
   re 29 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 13 (q3 c4) ∷
   re 11 1 (CS12 ∷ []) ∷
   rw⁻ 10 (q4 c4) ∷
   re 23 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 7 (q3 c4) ∷
   rw 5 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 13 (q8 c4) ∷
   rw⁻ 12 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw 13 (q13 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw⁻ 15 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw⁻ 13 (q9 c4) ∷
   rw⁻ 15 (q14 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 20 (q15 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 29 (q17 c4) ∷
   rw⁻ 26 (q18 c4) ∷
   rw⁻ 23 (q19 c4) ∷
   rw⁻ 20 (q18 c4) ∷
   rw⁻ 17 (q20 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 16 (q14 c4) ∷
   rw⁻ 17 (q12 c4) ∷
   rw 16 (q13 c4) ∷
   rw⁻ 15 (q12 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 20 (q12 c4) ∷
   rw 19 (q13 c4) ∷
   rw⁻ 18 (q12 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 22 (q22 c4) ∷
   rw⁻ 21 (q23 c4) ∷
   rw⁻ 20 (q22 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw 22 (q13 c4) ∷
   rw⁻ 21 (q12 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw 5 (q10 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw 8 (q10 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw⁻ 14 (q15 c4) ∷
   rw 12 (q16 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 23 (q17 c4) ∷
   rw⁻ 20 (q18 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw⁻ 14 (q18 c4) ∷
   rw⁻ 11 (q20 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 10 (q14 c4) ∷
   rw⁻ 11 (q12 c4) ∷
   rw 10 (q13 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 12 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw 13 (q13 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw⁻ 15 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw⁻ 13 (q9 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw⁻ 15 (q23 c4) ∷
   rw⁻ 14 (q22 c4) ∷
   rw⁻ 17 (q12 c4) ∷
   rw 16 (q13 c4) ∷
   rw⁻ 15 (q12 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw⁻ 17 (q7 c4) ∷
   rw 17 (q24 c4) ∷
   rw 17 (q25 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   re 17 5 (Sb0-2-43-1 ∷ []) ∷
   rw 3 (q26 c4) ∷
   rw 4 (q26 c4) ∷
   rw 5 (q26 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   rw 1 (q28 c4) ∷
   re 5 1 (CS03 ∷ []) ∷
   rw⁻ 4 (q29 c4) ∷
   re 4 1 (Sb2-0-3-1 ∷ []) ∷
   rw 3 (q30 c4) ∷
   re 3 1 (CS03 ∷ []) ∷
   rw⁻ 2 (q29 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 7 (q27 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 11 (q26 c4) ∷
   rw⁻ 14 (q26 c4) ∷
   rw⁻ 17 (q26 c4) ∷
   re 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   re 16 1 (CS12⁻ ∷ []) ∷
   rw⁻ 15 (q31 c4) ∷
   re 19 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 12 (q32 c4) ∷
   re 10 1 (CS12 ∷ []) ∷
   rw⁻ 9 (q33 c4) ∷
   re 13 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 6 (q32 c4) ∷
   rw 4 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 12 (q34 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw⁻ 11 (q14 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 16 (q35 c4) ∷
   rw 14 (q16 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 25 (q36 c4) ∷
   rw⁻ 22 (q37 c4) ∷
   rw⁻ 19 (q38 c4) ∷
   rw⁻ 16 (q37 c4) ∷
   rw⁻ 13 (q39 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   rw⁻ 10 (q40 c4) ∷
   rw 13 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 12 (q14 c4) ∷
   rw⁻ 13 (q12 c4) ∷
   rw 12 (q13 c4) ∷
   rw⁻ 11 (q12 c4) ∷
   rw⁻ 6 (q34 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 10 (q35 c4) ∷
   rw 8 (q16 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 19 (q36 c4) ∷
   rw⁻ 16 (q37 c4) ∷
   rw⁻ 13 (q38 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 7 (q39 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   rw 7 (q24 c4) ∷
   rw 7 (q25 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   re 7 5 (Sb0-2-43-1 ∷ []) ∷
   re 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   re 19 1 (CS12⁻ ∷ []) ∷
   rw⁻ 18 (q2 c4) ∷
   re 31 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 15 (q3 c4) ∷
   re 13 1 (CS12 ∷ []) ∷
   rw⁻ 12 (q4 c4) ∷
   re 25 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 9 (q3 c4) ∷
   rw 7 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   rw 13 (q10 c4) ∷
   rw⁻ 12 (q9 c4) ∷
   rw⁻ 13 (q11 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw 15 (q13 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw 16 (q10 c4) ∷
   rw⁻ 15 (q9 c4) ∷
   rw⁻ 17 (q14 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 22 (q15 c4) ∷
   rw 20 (q16 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 31 (q17 c4) ∷
   rw⁻ 28 (q18 c4) ∷
   rw⁻ 25 (q19 c4) ∷
   rw⁻ 22 (q18 c4) ∷
   rw⁻ 19 (q20 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw⁻ 21 (q16 c4) ∷
   rw⁻ 16 (q21 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 18 (q14 c4) ∷
   rw⁻ 19 (q12 c4) ∷
   rw 18 (q13 c4) ∷
   rw⁻ 17 (q12 c4) ∷
   rw⁻ 20 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   rw⁻ 22 (q12 c4) ∷
   rw 21 (q13 c4) ∷
   rw⁻ 20 (q12 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw 22 (q10 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 24 (q22 c4) ∷
   rw⁻ 23 (q23 c4) ∷
   rw⁻ 22 (q22 c4) ∷
   rw⁻ 25 (q12 c4) ∷
   rw 24 (q13 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw 9 (q13 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw⁻ 11 (q14 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw 14 (q16 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 25 (q17 c4) ∷
   rw⁻ 22 (q18 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 13 (q20 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   rw⁻ 10 (q21 c4) ∷
   rw 13 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 12 (q14 c4) ∷
   rw⁻ 13 (q12 c4) ∷
   rw 12 (q13 c4) ∷
   rw⁻ 11 (q12 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   rw 13 (q10 c4) ∷
   rw⁻ 12 (q9 c4) ∷
   rw⁻ 13 (q11 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw 15 (q13 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw 16 (q10 c4) ∷
   rw⁻ 15 (q9 c4) ∷
   rw⁻ 18 (q22 c4) ∷
   rw⁻ 17 (q23 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw⁻ 19 (q12 c4) ∷
   rw 18 (q13 c4) ∷
   rw⁻ 17 (q12 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw⁻ 19 (q7 c4) ∷
   rw 19 (q24 c4) ∷
   rw 19 (q25 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   re 19 5 (Sb0-2-43-1 ∷ []) ∷
   rw 5 (q26 c4) ∷
   rw 6 (q26 c4) ∷
   rw 7 (q26 c4) ∷
   rw 8 (q26 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   rw 3 (q28 c4) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 6 (q41 c4) ∷
   re 6 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 5 (q42 c4) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 4 (q41 c4) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (lem-F4-CS23ᵖ0∣CS01ᵖ1-part0 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣CS01ᵖ1-part1 c4)

-- F4 CS23^0|CS01^1: 2 steps
lem-F4-CS23ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣CS01ᵖ1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q43 c4) ∷
   rw 0 (q44 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx0-2413 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at12243143 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CS12⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS12⁻ ∷ []) (wp0454 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ013 ∷ []) (wl0871 (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(0;2413): 14 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ : Ws → ⟪ (Sb⁻0-1-2-3 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ c4 = derive (Sb⁻0-1-2-3 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Sb⁻0-1-2-3 ∷ [])
  (rw 1 (q45 c4) ∷
   re 0 1 (CS12⁻ ∷ []) ∷
   rw 0 (q46 c4) ∷
   re 1 1 (Sb⁻0-1-2-3 ∷ []) ∷
   re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 1 (q47 c4) ∷
   re 2 1 (Sb⁻0-1-2-3 ∷ []) ∷
   re 2 1 (CS12⁻ ∷ []) ∷
   rw 2 (q46 c4) ∷
   re 3 1 (Sb⁻0-1-2-3 ∷ []) ∷
   re 3 1 (CS12⁻ ∷ []) ∷
   rw⁻ 3 (q47 c4) ∷
   re 4 1 (Sb⁻0-1-2-3 ∷ []) ∷
   rw⁻ 0 (q45 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = eqn (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) (wp0455 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ []) (wl0872 (lit c4))

-- auto SBOX(0;1;2;3) | BOX(0;2413): 14 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ : Ws → ⟪ (Sb0-1-2-3 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ c4 = derive (Sb0-1-2-3 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Sb0-1-2-3 ∷ [])
  (rw 1 (q45 c4) ∷
   re 0 1 (CS12 ∷ []) ∷
   rw 0 (q48 c4) ∷
   re 1 1 (Sb0-1-2-3 ∷ []) ∷
   re 1 1 (CS12 ∷ []) ∷
   rw⁻ 1 (q49 c4) ∷
   re 2 1 (Sb0-1-2-3 ∷ []) ∷
   re 2 1 (CS12 ∷ []) ∷
   rw 2 (q48 c4) ∷
   re 3 1 (Sb0-1-2-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw⁻ 3 (q49 c4) ∷
   re 4 1 (Sb0-1-2-3 ∷ []) ∷
   rw⁻ 0 (q45 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1324 ∷ []) (lem-sym23 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ013 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ013 ∷ []) (lem-Cz-beta-at2332 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1234 ∷ []) (lem-sym23-at2332 c4)

-- auto BOX(0;1234) | CCZ013: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ013 : Ws → ⟪ (Bx0-1234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ013 c4 = derive (Bx0-1234 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx0-1234 ∷ [])
  (rw 0 (q50 c4) ∷
   rw⁻ 0 (q51 c4) ∷
   rw 1 (q52 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = eqn (Bx0-4213 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at143143 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx0-1234 ∷ Toff024 ∷ []) (Toff024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF042 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Bx0-1234 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ013 c4)

-- auto BOX(0;1234) | BOX(0;4213): 6 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·4213⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·4213⟩ c4 = derive (Bx0-1234 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Bx0-1234 ∷ [])
  (rw 1 (q53 c4) ∷
   rw 0 (q54 c4) ∷
   rw 1 (q55 c4) ∷
   rw 2 (q54 c4) ∷
   rw 3 (q55 c4) ∷
   rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (Sw23 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (Sw23 ∷ Bx0-3412 ∷ []) (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (Sb⁻0-1-2-3 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Sw23 ∷ Bx0-2413 ∷ []) (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(0;2413) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 : Ws → ⟪ (Sb⁻0-1-3-2 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 c4 = derive (Sb⁻0-1-3-2 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Sb⁻0-1-3-2 ∷ [])
  (rw⁻ 0 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 2 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q56 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (Sw34 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (Sw34 ∷ Bx0-4312 ∷ []) (Bx0-3412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4312⟩ (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (Sb⁻0-1-3-2 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Sw34 ∷ Bx0-3412 ∷ []) (Bx0-4312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3412⟩ (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (Sw34 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(0;2413) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 : Ws → ⟪ (Sb⁻0-1-4-2 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 c4 = derive (Sb⁻0-1-4-2 ∷ Bx0-4312 ∷ []) (Bx0-4312 ∷ Sb⁻0-1-4-2 ∷ [])
  (rw⁻ 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 0 (q66 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q62 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (Sw23 ∷ Bx0-4213 ∷ []) (Bx0-4312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4213⟩ (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Sb⁻0-1-4-2 ∷ Bx0-4312 ∷ []) (Bx0-4312 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (Sw23 ∷ Bx0-4312 ∷ []) (Bx0-4213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4312⟩ (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(0;2413) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 : Ws → ⟪ (Sb⁻0-1-4-3 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 c4 = derive (Sb⁻0-1-4-3 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Sb⁻0-1-4-3 ∷ [])
  (rw⁻ 0 (q56 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   rw 0 (q71 c4) ∷
   rw 1 (q72 c4) ∷
   rw 2 (q56 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (Sw12 ∷ Bx0-4213 ∷ []) (Bx0-4123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4213⟩ (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (Bx0-4123 ∷ []) (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (Sw12 ∷ Bx0-1423 ∷ []) (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4))

-- sym12 @143143: 5 steps
lem-sym12-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-sym12-at143143 c4 = derive (Bx0-4213 ∷ []) (Bx0-2413 ∷ [])
  (rw⁻ 0 (q73 c4) ∷
   rw 1 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw 0 (q76 c4) ∷
   rw 1 (q73 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (Sw12 ∷ Bx0-2413 ∷ []) (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (Bx0-1423 ∷ []) (Bx0-4123 ∷ []) (lem-sym12-at243243 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (Sw12 ∷ Bx0-4123 ∷ []) (Bx0-4213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4123⟩ (lit c4))

-- sym12 @12243143: 5 steps
lem-sym12-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym12-at12243143 c4 = derive (Bx0-2413 ∷ []) (Bx0-4213 ∷ [])
  (rw⁻ 0 (q73 c4) ∷
   rw 1 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 0 (q79 c4) ∷
   rw 1 (q73 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (Sw23 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ (lit c4))
  q81 : Ws → Eqn
  q81 c4 = eqn (Sb0-1-2-3 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (Sw23 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(0;2413) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 : Ws → ⟪ (Sb0-1-3-2 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 c4 = derive (Sb0-1-3-2 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Sb0-1-3-2 ∷ [])
  (rw⁻ 0 (q56 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q58 c4) ∷
   rw 1 (q81 c4) ∷
   rw 0 (q60 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q56 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = eqn (Sw34 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (Sb0-1-3-2 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (Sw34 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(0;2413) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 : Ws → ⟪ (Sb0-1-4-2 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 c4 = derive (Sb0-1-4-2 ∷ Bx0-4312 ∷ []) (Bx0-4312 ∷ Sb0-1-4-2 ∷ [])
  (rw⁻ 0 (q62 c4) ∷
   rw 1 (q83 c4) ∷
   rw 2 (q64 c4) ∷
   rw 1 (q84 c4) ∷
   rw 0 (q66 c4) ∷
   rw 1 (q85 c4) ∷
   rw 2 (q62 c4) ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = eqn (Sw23 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (Sb0-1-4-2 ∷ Bx0-4312 ∷ []) (Bx0-4312 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (Sw23 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(0;2413) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 : Ws → ⟪ (Sb0-1-4-3 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 c4 = derive (Sb0-1-4-3 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Sb0-1-4-3 ∷ [])
  (rw⁻ 0 (q56 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q69 c4) ∷
   rw 1 (q87 c4) ∷
   rw 0 (q71 c4) ∷
   rw 1 (q88 c4) ∷
   rw 2 (q56 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = eqn (Sb⁻0-1-4-3 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (Toff423 ∷ Toff423 ∷ []) [] (wl0296 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (Bx0-4213 ∷ []) (Bx0-2413 ∷ []) (lem-sym12-at143143 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2341 ∷ []) (lem-sym23-at122441 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (Toff423 ∷ Bx0-2341 ∷ Toff423 ∷ []) (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (Bx0-2341 ∷ []) (Bx0-2431 ∷ []) (lem-sym23-at12233441 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (Bx0-2413 ∷ []) (Bx0-4213 ∷ []) (lem-sym12-at12243143 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (Sb0-1-4-3 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (Bx0-1234 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·4213⟩ c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (CCZ123 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (wl0357 (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (wl0358 (lit c4))
  q100 : Ws → Eqn
  q100 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0212 (lit c4))

-- auto SBOX(0;1;23;4) | BOX(0;4213): 30 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩ c4 = derive (Sb0-1-23-4 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   rw 4 (q89 c4) ∷
   rw⁻ 5 (q90 c4) ∷
   rw 4 (q91 c4) ∷
   rw 4 (q25 c4) ∷
   rw 4 (q92 c4) ∷
   rw 3 (q93 c4) ∷
   rw 3 (q94 c4) ∷
   rw 3 (q5 c4) ∷
   rw 3 (q95 c4) ∷
   rw 2 (q96 c4) ∷
   rw⁻ 3 (q90 c4) ∷
   rw 2 (q91 c4) ∷
   rw 2 (q25 c4) ∷
   rw 2 (q92 c4) ∷
   rw 1 (q93 c4) ∷
   rw 1 (q94 c4) ∷
   rw 1 (q5 c4) ∷
   rw 1 (q95 c4) ∷
   rw 0 (q97 c4) ∷
   re 7 1 (CS14⁻ ∷ []) ∷
   rw 5 (q98 c4) ∷
   re 6 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14 ∷ []) ∷
   re 6 1 (CS14⁻ ∷ []) ∷
   rw 2 (q99 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw 6 (q100 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (Sw01 ∷ Bx3-1420 ∷ []) (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Sw01 ∷ Bx3-0241 ∷ []) (Bx3-1240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0241⟩ (lit c4))

-- sym23 @03243240: 5 steps
lem-sym23-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-sym23-at03243240 c4 = derive (Bx3-1420 ∷ []) (Bx3-1240 ∷ [])
  (rw⁻ 0 (q101 c4) ∷
   rw 1 (q102 c4) ∷
   rw 1 (q103 c4) ∷
   rw 0 (q104 c4) ∷
   rw 1 (q101 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0096 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (Sw01 ∷ Bx3-1240 ∷ []) (Bx3-0241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1240⟩ (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ012 ∷ Bx3-0241 ∷ []) (Bx3-0241 ∷ CCZ012 ∷ []) (lem-c124-beta-at03103441 c4)

-- c124-beta @033440: 7 steps
lem-c124-beta-at033440 : Ws → ⟪ (CCZ012 ∷ Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at033440 c4 = derive (CCZ012 ∷ Bx3-1240 ∷ []) (Bx3-1240 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q101 c4) ∷
   rw⁻ 1 (q105 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q107 c4) ∷
   rw 0 (q104 c4) ∷
   rw⁻ 1 (q105 c4) ∷
   rw 2 (q101 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (Sw01 ∷ Bx3-0421 ∷ []) (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ (lit c4))

-- sym23 @033440: 5 steps
lem-sym23-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym23-at033440 c4 = derive (Bx3-1240 ∷ []) (Bx3-1420 ∷ [])
  (rw⁻ 0 (q101 c4) ∷
   rw 1 (q106 c4) ∷
   rw 1 (q108 c4) ∷
   rw 0 (q109 c4) ∷
   rw 1 (q101 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ012 ∷ []) (CCZ012 ∷ []) (wl0813 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (Bx3-1420 ∷ []) (Bx3-1240 ∷ []) (lem-sym23-at03243240 c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (CCZ012 ∷ Bx3-1240 ∷ []) (Bx3-1240 ∷ CCZ012 ∷ []) (lem-c124-beta-at033440 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (Bx3-1240 ∷ []) (Bx3-1420 ∷ []) (lem-sym23-at033440 c4)

-- auto CCZ012 | BOX(3;1420): 5 steps
lem-auto-CCZ012-∣-BOX⟨3·1420⟩ : Ws → ⟪ (CCZ012 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·1420⟩ c4 = derive (CCZ012 ∷ Bx3-1420 ∷ []) (Bx3-1420 ∷ CCZ012 ∷ [])
  (rw 0 (q110 c4) ∷
   rw 1 (q111 c4) ∷
   rw 0 (q112 c4) ∷
   rw 0 (q113 c4) ∷
   rw 1 (q110 c4) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = eqn (CCZ012 ∷ Bx3-1420 ∷ []) (Bx3-1420 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·1420⟩ c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (CCZ012 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ []) (Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ012 ∷ []) (wp0456 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (CCZ012 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ012 ∷ []) (wl0873 (lit c4))

-- auto CCZ012 | SBOX(3;1;42;0): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩ : Ws → ⟪ (CCZ012 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩ c4 = derive (CCZ012 ∷ Sb3-1-42-0 ∷ []) (Sb3-1-42-0 ∷ CCZ012 ∷ [])
  (re 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   rw 0 (q114 c4) ∷
   re 3 1 (CS01 ∷ []) ∷
   rw 1 (q115 c4) ∷
   re 2 1 (Sb3-1-0-2 ∷ []) ∷
   re 5 1 (CS01⁻ ∷ []) ∷
   rw 4 (q116 c4) ∷
   re 4 1 (Sb⁻3-1-0-2 ∷ []) ∷
   re 0 5 (Sb3-1-42-0 ∷ []) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4)
  q118 : Ws → Eqn
  q118 c4 = eqn (Sb0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-1 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩ c4 = derive (Sb0-1-23-4 ∷ Sb0-4-3-1 ∷ []) (Sb0-4-3-1 ∷ Sb0-1-23-4 ∷ [])
  (re 1 1 (CS34 ∷ []) ∷
   rw 0 (q117 c4) ∷
   rw 0 (q118 c4) ∷
   rw⁻ 1 (q117 c4) ∷
   re 0 1 (Sb0-4-3-1 ∷ []) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = eqn (Sb0-1-32-4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-1 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩ c4 = derive (Sb0-1-23-4 ∷ Sb⁻0-4-3-1 ∷ []) (Sb⁻0-4-3-1 ∷ Sb0-1-23-4 ∷ [])
  (re 1 1 (CS34⁻ ∷ []) ∷
   rw 0 (q117 c4) ∷
   rw 0 (q119 c4) ∷
   rw⁻ 1 (q117 c4) ∷
   re 0 1 (Sb⁻0-4-3-1 ∷ []) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (Sb0-1-23-4 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩ c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | BOX(0;4213) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Bx0-4312 ∷ []) (Bx0-4312 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q56 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q71 c4) ∷
   rw 1 (q121 c4) ∷
   rw 0 (q69 c4) ∷
   rw 1 (q122 c4) ∷
   rw 2 (q56 c4) ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = eqn (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (Sb0-1-32-4 ∷ Bx0-4312 ∷ []) (Bx0-4312 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2332 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | BOX(0;4213) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q62 c4) ∷
   rw 1 (q123 c4) ∷
   rw 2 (q66 c4) ∷
   rw 1 (q124 c4) ∷
   rw 0 (q64 c4) ∷
   rw 1 (q125 c4) ∷
   rw 2 (q62 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4))
  q127 : Ws → Eqn
  q127 c4 = eqn (Sb0-1-42-3 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at243243 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (Sw23 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | BOX(0;4213) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2442 c4 = derive (Sb0-1-43-2 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q56 c4) ∷
   rw 1 (q126 c4) ∷
   rw 2 (q60 c4) ∷
   rw 1 (q127 c4) ∷
   rw 0 (q58 c4) ∷
   rw 1 (q128 c4) ∷
   rw 2 (q56 c4) ∷ []) Eq.refl

private
  q129 : Ws → Eqn
  q129 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (Sb0-1-43-2 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2442 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (Sw12 ∷ Sb0-1-43-2 ∷ []) (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4))

-- auto SBOX(0;1;23;4) | BOX(0;4213) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at122441 c4 = derive (Sb0-2-43-1 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q73 c4) ∷
   rw 1 (q129 c4) ∷
   rw 2 (q76 c4) ∷
   rw 1 (q130 c4) ∷
   rw 0 (q77 c4) ∷
   rw 1 (q131 c4) ∷
   rw 2 (q73 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4))
  q133 : Ws → Eqn
  q133 c4 = eqn (Sw23 ∷ Sb2-1-43-0 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·43·0⟩ (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (CCZ012 ∷ Sb3-1-42-0 ∷ []) (Sb3-1-42-0 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩ c4)
  q135 : Ws → Eqn
  q135 c4 = eqn (Sw23 ∷ Sb3-1-42-0 ∷ []) (Sb2-1-43-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·42·0⟩ (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4))

-- auto CCZ012 | SBOX(3;1;42;0) @2332: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at2332 : Ws → ⟪ (CCZ013 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at2332 c4 = derive (CCZ013 ∷ Sb2-1-43-0 ∷ []) (Sb2-1-43-0 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q56 c4) ∷
   rw 1 (q132 c4) ∷
   rw 2 (q133 c4) ∷
   rw 1 (q134 c4) ∷
   rw 0 (q135 c4) ∷
   rw 1 (q136 c4) ∷
   rw 2 (q56 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (Sw12 ∷ Sb1-2-43-0 ∷ []) (Sb2-1-43-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·43·0⟩ (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (CCZ013 ∷ Sb2-1-43-0 ∷ []) (Sb2-1-43-0 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at2332 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (Sw12 ∷ Sb2-1-43-0 ∷ []) (Sb1-2-43-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·43·0⟩ (lit c4))
  q141 : Ws → Eqn
  q141 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4))

-- auto CCZ012 | SBOX(3;1;42;0) @122331: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at122331 : Ws → ⟪ (CCZ023 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at122331 c4 = derive (CCZ023 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q73 c4) ∷
   rw 1 (q137 c4) ∷
   rw 2 (q138 c4) ∷
   rw 1 (q139 c4) ∷
   rw 0 (q140 c4) ∷
   rw 1 (q141 c4) ∷
   rw 2 (q73 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ023 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at122331 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (Sw01 ∷ Sb1-2-43-0 ∷ []) (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4))
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 (lit c4))

-- auto CCZ012 | SBOX(3;1;42;0) @01122330: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at01122330 : Ws → ⟪ (CCZ123 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at01122330 c4 = derive (CCZ123 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q101 c4) ∷
   rw⁻ 1 (q142 c4) ∷
   rw 2 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q145 c4) ∷
   rw⁻ 1 (q146 c4) ∷
   rw 2 (q101 c4) ∷ []) Eq.refl

private
  q147 : Ws → Eqn
  q147 c4 = eqn (Sw23 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·4·2·1⟩ (lit c4))
  q148 : Ws → Eqn
  q148 c4 = eqn (Sb0-1-23-4 ∷ Sb0-4-3-1 ∷ []) (Sb0-4-3-1 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩ c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (Sw23 ∷ Sb0-4-3-1 ∷ []) (Sb0-4-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·4·3·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-2-1 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q56 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw 0 (q149 c4) ∷
   rw 1 (q122 c4) ∷
   rw 2 (q56 c4) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = eqn (Sw34 ∷ Sb0-3-2-1 ∷ []) (Sb0-4-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·3·2·1⟩ (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (Sb0-1-32-4 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-2-1 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2332 c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (Sw34 ∷ Sb0-4-2-1 ∷ []) (Sb0-3-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·4·2·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-2-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Sb0-3-2-1 ∷ []) (Sb0-3-2-1 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q62 c4) ∷
   rw 1 (q123 c4) ∷
   rw 2 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 0 (q152 c4) ∷
   rw 1 (q125 c4) ∷
   rw 2 (q62 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = eqn (Sw23 ∷ Sb0-2-3-1 ∷ []) (Sb0-3-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·2·3·1⟩ (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (Sb0-1-42-3 ∷ Sb0-3-2-1 ∷ []) (Sb0-3-2-1 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at243243 c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (Sw23 ∷ Sb0-3-2-1 ∷ []) (Sb0-2-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·2·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2442 c4 = derive (Sb0-1-43-2 ∷ Sb0-2-3-1 ∷ []) (Sb0-2-3-1 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q56 c4) ∷
   rw 1 (q126 c4) ∷
   rw 2 (q153 c4) ∷
   rw 1 (q154 c4) ∷
   rw 0 (q155 c4) ∷
   rw 1 (q128 c4) ∷
   rw 2 (q56 c4) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = eqn (Sw12 ∷ Sb0-1-3-2 ∷ []) (Sb0-2-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·3·2⟩ (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (Sb0-1-43-2 ∷ Sb0-2-3-1 ∷ []) (Sb0-2-3-1 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2442 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (Sw12 ∷ Sb0-2-3-1 ∷ []) (Sb0-1-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·3·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at122441 c4 = derive (Sb0-2-43-1 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q73 c4) ∷
   rw 1 (q129 c4) ∷
   rw 2 (q156 c4) ∷
   rw 1 (q157 c4) ∷
   rw 0 (q158 c4) ∷
   rw 1 (q131 c4) ∷
   rw 2 (q73 c4) ∷ []) Eq.refl

private
  q159 : Ws → Eqn
  q159 c4 = eqn (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·4·2·1⟩ (lit c4))
  q160 : Ws → Eqn
  q160 c4 = eqn (Sb0-1-23-4 ∷ Sb⁻0-4-3-1 ∷ []) (Sb⁻0-4-3-1 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩ c4)
  q161 : Ws → Eqn
  q161 c4 = eqn (Sw23 ∷ Sb⁻0-4-3-1 ∷ []) (Sb⁻0-4-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·4·3·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb⁻0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-2-1 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-4-2-1 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q56 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q159 c4) ∷
   rw 1 (q160 c4) ∷
   rw 0 (q161 c4) ∷
   rw 1 (q122 c4) ∷
   rw 2 (q56 c4) ∷ []) Eq.refl

private
  q162 : Ws → Eqn
  q162 c4 = eqn (Sw34 ∷ Sb⁻0-3-2-1 ∷ []) (Sb⁻0-4-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·3·2·1⟩ (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (Sb0-1-32-4 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-4-2-1 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2332 c4)
  q164 : Ws → Eqn
  q164 c4 = eqn (Sw34 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-3-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·4·2·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb⁻0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-2-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Sb⁻0-3-2-1 ∷ []) (Sb⁻0-3-2-1 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q62 c4) ∷
   rw 1 (q123 c4) ∷
   rw 2 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   rw 0 (q164 c4) ∷
   rw 1 (q125 c4) ∷
   rw 2 (q62 c4) ∷ []) Eq.refl

private
  q165 : Ws → Eqn
  q165 c4 = eqn (Sw23 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-3-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·2·3·1⟩ (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (Sb0-1-42-3 ∷ Sb⁻0-3-2-1 ∷ []) (Sb⁻0-3-2-1 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at243243 c4)
  q167 : Ws → Eqn
  q167 c4 = eqn (Sw23 ∷ Sb⁻0-3-2-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·3·2·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2442 c4 = derive (Sb0-1-43-2 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q56 c4) ∷
   rw 1 (q126 c4) ∷
   rw 2 (q165 c4) ∷
   rw 1 (q166 c4) ∷
   rw 0 (q167 c4) ∷
   rw 1 (q128 c4) ∷
   rw 2 (q56 c4) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = eqn (Sw12 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-2-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·3·2⟩ (lit c4))
  q169 : Ws → Eqn
  q169 c4 = eqn (Sb0-1-43-2 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2442 c4)
  q170 : Ws → Eqn
  q170 c4 = eqn (Sw12 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-1-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·3·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at122441 c4 = derive (Sb0-2-43-1 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q73 c4) ∷
   rw 1 (q129 c4) ∷
   rw 2 (q168 c4) ∷
   rw 1 (q169 c4) ∷
   rw 0 (q170 c4) ∷
   rw 1 (q131 c4) ∷
   rw 2 (q73 c4) ∷ []) Eq.refl
