{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D184 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0021 ; wl0024 ; wl0025 ; wl0103 ; wl0111 ; wl0187 ; wl0212 ; wl0225 ; wl0226 ; wl0265 ; wl0270 ; wl0271 ; wl0272 ; wl0273 ; wl0283 ; wl0298 ; wl0325 ; wl0326 ; wl0341 ; wl0364 ; wl0602 ; wl0627 ; wl0653 ; wl0661 ; wl0741 ; wl0742 ; wl0848 ; wl0849 ; wl0850 ; wl0851 ; wl0852 ; wl0859 ; wl0860 ; wl0861 ; wl0862 ; wl0866 ; wl0867 ; wl0868 ; wl0869 ; wl0870 ; wl0874 ; wl0875 ; wl0876 ; wl0877 ; wl0878 ; wl0879 ; wl0880 ; wl0881 ; wl0882 ; wl0883 ; wl0884 ; wp0034 ; wp0268 ; wp0370 ; wp0371 ; wp0372 ; wp0440 ; wp0448 ; wp0451 ; wp0457 ; wp0458 ; wp0459 ; wp0460)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-CS12-beta ; lem-CS20-beta-ci ; lem-beta-T-at2332 ; lem-sym12-at14213243 ; lem-sym34 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-AX-SB ; lem-BOXd-BOX-at2332 ; lem-CS12-beta-at243243 ; lem-sym12-at243243 ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym23-at243243 ; lem-sym23-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-X1-beta-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-SBsymd-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02)
open import Examples.Groups.Clifford+CS.Five.D.D166 using (lem-T312-beta-at14233142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 ; lem-beta-inv-at122441 ; lem-sym12-at122441 ; lem-sym12-at1441 ; lem-sym23-at14233241 ; lem-sym23-at1441 ; lem-sym34-at14233142 ; lem-sym34-at14233241)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-X1-beta-at1441 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 ; lem-beta-T-at12213443 ; lem-sym34-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2442 ; lem-auto-BOX⟨0·1234⟩-∣-CS13-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D180 using (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D183 using (lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at01122330 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at122441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at122441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ013 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-2-CS12 ; lem-nat-2-CS13)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-3-SBOX⟨1·0·2·4⟩ ; lem-nat-3-SBOXd⟨1·0·2·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨0·2431⟩ ; lem-nat-1-SBOX⟨0·1·2·3⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·1·3⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-1-SBOXd⟨0·1·2·3⟩ ; lem-nat-1-SBOXd⟨0·2·1·3⟩ ; lem-nat-2-SBOX⟨1·0·3·4⟩ ; lem-nat-2-SBOXd⟨1·0·3·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-SBOXd⟨0·1·42·3⟩ ; lem-nat-0-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨1·0·2·4⟩ ; lem-nat-2-SBOXd⟨1·0·2·4⟩ ; lem-nat-3-SBOX⟨1·0·2·3⟩ ; lem-nat-3-SBOXd⟨0·1·32·4⟩ ; lem-nat-3-SBOXd⟨0·1·42·3⟩ ; lem-nat-3-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-SBOX⟨0·1·2·3⟩ ; lem-nat-0-SBOXd⟨0·1·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-SBOX⟨1·0·2·3⟩ ; lem-nat-0-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-comm-CCZ024-CSd13 ; lem-nat-3-SBOX⟨0·2·34·1⟩ ; lem-nat-3-SBOX⟨0·2·43·1⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx0-1423 ∷ []) (Bx0-4123 ∷ []) (lem-sym12-at243243 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ Bx0-4123 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx0-4123 ∷ []) (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ123 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Sb0-2-43-1 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at122441 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ123 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at01122330 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0212 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ []) (wl0364 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0225 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (K3⁻ ∷ K3 ∷ []) [] (wl0859 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (wl0860 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (wl0861 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (wl0862 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2413 ∷ []) (lem-sym34-at122441 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx0-2143 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (wp0448 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (K3 ∷ X4 ∷ []) (X4 ∷ K3 ∷ []) (c₄ (K ↑ ↑ ↑) (X))
  q21 : Ws → Eqn
  q21 c4 = eqn (Toff012 ∷ K3 ∷ []) (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K))
  q22 : Ws → Eqn
  q22 c4 = eqn (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wl0341 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ []) (wl0848 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ []) (wp0440 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) (wl0849 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ []) (wl0850 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (wl0851 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ X4 ∷ CS34 ∷ []) (wl0852 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (K3⁻ ∷ X4 ∷ []) (X4 ∷ K3⁻ ∷ []) (c₄ ((K • iI) ↑ ↑ ↑) (X))
  q31 : Ws → Eqn
  q31 c4 = eqn (Toff012 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI))
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (wl0874 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (wl0875 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (wl0876 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (wp0457 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ []) (wp0458 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ []) (wl0866 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ []) (wp0451 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ []) (wl0867 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS34⁻ ∷ []) (wl0868 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ []) (wl0869 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ []) (wl0870 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ []) (c₄ (CS ↑ ↑) (X))
  q46 : Ws → Eqn
  q46 c4 = eqn (CS23 ∷ Toff012 ∷ []) (Toff012 ∷ CS23 ∷ []) (wl0226 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ []) (wl0741 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Sb0-2-43-1 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at122441 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ []) (wl0742 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (Sb0-2-43-1 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at122441 c4)

-- F4 CS23^0|CS12^1: 508 steps
lem-F4-CS23ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣CS12ᵖ1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 3 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 0 (q5 c4) ∷
   rw 4 (q7 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw⁻ 15 (q12 c4) ∷
   re 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   re 14 1 (CS12⁻ ∷ []) ∷
   rw⁻ 13 (q13 c4) ∷
   re 17 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 10 (q14 c4) ∷
   re 8 1 (CS12 ∷ []) ∷
   rw⁻ 7 (q15 c4) ∷
   re 11 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 2 (q16 c4) ∷
   rw 2 (q17 c4) ∷
   rw 2 (q18 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   rw 8 (q21 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw⁻ 14 (q23 c4) ∷
   rw 12 (q24 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 23 (q25 c4) ∷
   rw⁻ 20 (q26 c4) ∷
   rw⁻ 17 (q27 c4) ∷
   rw⁻ 14 (q26 c4) ∷
   rw⁻ 11 (q28 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw⁻ 13 (q24 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 10 (q22 c4) ∷
   rw⁻ 11 (q30 c4) ∷
   rw 10 (q31 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 1 (q20 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   rw 6 (q24 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 17 (q25 c4) ∷
   rw⁻ 14 (q26 c4) ∷
   rw⁻ 11 (q27 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 4 (q22 c4) ∷
   rw⁻ 5 (q30 c4) ∷
   rw 4 (q31 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw 5 (q32 c4) ∷
   rw 5 (q33 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   re 5 5 (Sb0-2-43-1 ∷ []) ∷
   re 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   re 17 1 (CS12⁻ ∷ []) ∷
   rw⁻ 16 (q34 c4) ∷
   re 29 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 13 (q35 c4) ∷
   re 11 1 (CS12 ∷ []) ∷
   rw⁻ 10 (q36 c4) ∷
   re 23 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 7 (q35 c4) ∷
   rw 5 (q16 c4) ∷
   rw 5 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 13 (q37 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw 11 (q21 c4) ∷
   rw⁻ 10 (q20 c4) ∷
   rw⁻ 11 (q38 c4) ∷
   rw⁻ 14 (q30 c4) ∷
   rw 13 (q31 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw⁻ 15 (q20 c4) ∷
   rw 14 (q21 c4) ∷
   rw⁻ 13 (q20 c4) ∷
   rw⁻ 15 (q22 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 20 (q39 c4) ∷
   rw 18 (q24 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 29 (q40 c4) ∷
   rw⁻ 26 (q41 c4) ∷
   rw⁻ 23 (q42 c4) ∷
   rw⁻ 20 (q41 c4) ∷
   rw⁻ 17 (q43 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw⁻ 19 (q24 c4) ∷
   rw⁻ 14 (q44 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 16 (q22 c4) ∷
   rw⁻ 17 (q30 c4) ∷
   rw 16 (q31 c4) ∷
   rw⁻ 15 (q30 c4) ∷
   rw⁻ 18 (q20 c4) ∷
   rw 17 (q21 c4) ∷
   rw⁻ 16 (q20 c4) ∷
   rw⁻ 17 (q38 c4) ∷
   rw⁻ 20 (q30 c4) ∷
   rw 19 (q31 c4) ∷
   rw⁻ 18 (q30 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw 20 (q21 c4) ∷
   rw⁻ 19 (q20 c4) ∷
   rw⁻ 22 (q45 c4) ∷
   rw⁻ 21 (q46 c4) ∷
   rw⁻ 20 (q45 c4) ∷
   rw⁻ 23 (q30 c4) ∷
   rw 22 (q31 c4) ∷
   rw⁻ 21 (q30 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw⁻ 5 (q38 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw 7 (q31 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   rw 8 (q21 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw⁻ 14 (q39 c4) ∷
   rw 12 (q24 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 23 (q40 c4) ∷
   rw⁻ 20 (q41 c4) ∷
   rw⁻ 17 (q42 c4) ∷
   rw⁻ 14 (q41 c4) ∷
   rw⁻ 11 (q43 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw⁻ 13 (q24 c4) ∷
   rw⁻ 8 (q44 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 10 (q22 c4) ∷
   rw⁻ 11 (q30 c4) ∷
   rw 10 (q31 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw 11 (q21 c4) ∷
   rw⁻ 10 (q20 c4) ∷
   rw⁻ 11 (q38 c4) ∷
   rw⁻ 14 (q30 c4) ∷
   rw 13 (q31 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw⁻ 15 (q20 c4) ∷
   rw 14 (q21 c4) ∷
   rw⁻ 13 (q20 c4) ∷
   rw⁻ 16 (q45 c4) ∷
   rw⁻ 15 (q46 c4) ∷
   rw⁻ 14 (q45 c4) ∷
   rw⁻ 17 (q30 c4) ∷
   rw 16 (q31 c4) ∷
   rw⁻ 15 (q30 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw⁻ 17 (q18 c4) ∷
   rw 17 (q32 c4) ∷
   rw 17 (q33 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   re 17 5 (Sb0-2-43-1 ∷ []) ∷
   rw 3 (q12 c4) ∷
   rw 4 (q12 c4) ∷
   rw 5 (q12 c4) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 1 (q10 c4) ∷
   re 5 1 (CS13 ∷ []) ∷
   rw⁻ 4 (q47 c4) ∷
   re 4 1 (Sb0-1-3-2 ∷ []) ∷
   rw 3 (q48 c4) ∷
   re 3 1 (CS13 ∷ []) ∷
   rw⁻ 2 (q47 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 6 (q10 c4) ∷
   rw 7 (q11 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw⁻ 11 (q12 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw⁻ 17 (q12 c4) ∷
   re 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   re 16 1 (CS12⁻ ∷ []) ∷
   rw⁻ 15 (q13 c4) ∷
   re 19 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 12 (q14 c4) ∷
   re 10 1 (CS12 ∷ []) ∷
   rw⁻ 9 (q15 c4) ∷
   re 13 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 4 (q16 c4) ∷
   rw 4 (q17 c4) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw⁻ 11 (q20 c4) ∷
   rw 10 (q21 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   rw⁻ 11 (q22 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 16 (q23 c4) ∷
   rw 14 (q24 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 25 (q25 c4) ∷
   rw⁻ 22 (q26 c4) ∷
   rw⁻ 19 (q27 c4) ∷
   rw⁻ 16 (q26 c4) ∷
   rw⁻ 13 (q28 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw⁻ 15 (q24 c4) ∷
   rw⁻ 10 (q29 c4) ∷
   rw 13 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 12 (q22 c4) ∷
   rw⁻ 13 (q30 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 11 (q30 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw⁻ 5 (q22 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw 8 (q24 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 19 (q25 c4) ∷
   rw⁻ 16 (q26 c4) ∷
   rw⁻ 13 (q27 c4) ∷
   rw⁻ 10 (q26 c4) ∷
   rw⁻ 7 (q28 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw⁻ 9 (q24 c4) ∷
   rw⁻ 4 (q29 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 6 (q22 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw 6 (q31 c4) ∷
   rw⁻ 5 (q30 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw 7 (q32 c4) ∷
   rw 7 (q33 c4) ∷
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
   rw⁻ 18 (q34 c4) ∷
   re 31 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 15 (q35 c4) ∷
   re 13 1 (CS12 ∷ []) ∷
   rw⁻ 12 (q36 c4) ∷
   re 25 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 9 (q35 c4) ∷
   rw 7 (q16 c4) ∷
   rw 7 (q17 c4) ∷
   rw 7 (q18 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 15 (q37 c4) ∷
   rw⁻ 14 (q20 c4) ∷
   rw 13 (q21 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw⁻ 13 (q38 c4) ∷
   rw⁻ 16 (q30 c4) ∷
   rw 15 (q31 c4) ∷
   rw⁻ 14 (q30 c4) ∷
   rw⁻ 17 (q20 c4) ∷
   rw 16 (q21 c4) ∷
   rw⁻ 15 (q20 c4) ∷
   rw⁻ 17 (q22 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 22 (q39 c4) ∷
   rw 20 (q24 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 31 (q40 c4) ∷
   rw⁻ 28 (q41 c4) ∷
   rw⁻ 25 (q42 c4) ∷
   rw⁻ 22 (q41 c4) ∷
   rw⁻ 19 (q43 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw⁻ 21 (q24 c4) ∷
   rw⁻ 16 (q44 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 18 (q22 c4) ∷
   rw⁻ 19 (q30 c4) ∷
   rw 18 (q31 c4) ∷
   rw⁻ 17 (q30 c4) ∷
   rw⁻ 20 (q20 c4) ∷
   rw 19 (q21 c4) ∷
   rw⁻ 18 (q20 c4) ∷
   rw⁻ 19 (q38 c4) ∷
   rw⁻ 22 (q30 c4) ∷
   rw 21 (q31 c4) ∷
   rw⁻ 20 (q30 c4) ∷
   rw⁻ 23 (q20 c4) ∷
   rw 22 (q21 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 24 (q45 c4) ∷
   rw⁻ 23 (q46 c4) ∷
   rw⁻ 22 (q45 c4) ∷
   rw⁻ 25 (q30 c4) ∷
   rw 24 (q31 c4) ∷
   rw⁻ 23 (q30 c4) ∷
   rw⁻ 9 (q37 c4) ∷
   rw⁻ 8 (q20 c4) ∷
   rw 7 (q21 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   rw 9 (q31 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 11 (q20 c4) ∷
   rw 10 (q21 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   rw⁻ 11 (q22 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 16 (q39 c4) ∷
   rw 14 (q24 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 25 (q40 c4) ∷
   rw⁻ 22 (q41 c4) ∷
   rw⁻ 19 (q42 c4) ∷
   rw⁻ 16 (q41 c4) ∷
   rw⁻ 13 (q43 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw⁻ 15 (q24 c4) ∷
   rw⁻ 10 (q44 c4) ∷
   rw 13 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 12 (q22 c4) ∷
   rw⁻ 13 (q30 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 11 (q30 c4) ∷
   rw⁻ 14 (q20 c4) ∷
   rw 13 (q21 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw⁻ 13 (q38 c4) ∷
   rw⁻ 16 (q30 c4) ∷
   rw 15 (q31 c4) ∷
   rw⁻ 14 (q30 c4) ∷
   rw⁻ 17 (q20 c4) ∷
   rw 16 (q21 c4) ∷
   rw⁻ 15 (q20 c4) ∷
   rw⁻ 18 (q45 c4) ∷
   rw⁻ 17 (q46 c4) ∷
   rw⁻ 16 (q45 c4) ∷
   rw⁻ 19 (q30 c4) ∷
   rw 18 (q31 c4) ∷
   rw⁻ 17 (q30 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw⁻ 19 (q18 c4) ∷
   rw 19 (q32 c4) ∷
   rw 19 (q33 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   re 19 5 (Sb0-2-43-1 ∷ []) ∷
   rw 5 (q12 c4) ∷
   rw 6 (q12 c4) ∷
   rw 7 (q12 c4) ∷
   rw 8 (q12 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   rw 3 (q10 c4) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q49 c4) ∷
   re 6 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw 5 (q50 c4) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q49 c4) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Sw12 ∷ Bx0-2431 ∷ []) (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx0-1432 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at2442 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (Sw12 ∷ Bx0-1432 ∷ []) (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4))

-- auto BOX(0;1234) | CS13 @122441: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at122441 : Ws → ⟪ (Bx0-2431 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at122441 c4 = derive (Bx0-2431 ∷ CS23 ∷ []) (CS23 ∷ Bx0-2431 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 2 (q53 c4) ∷
   rw 1 (q54 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (Bx0-1432 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2442 c4)

-- auto BOX(0;1234) | CCZ134 @122441: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at122441 : Ws → ⟪ (Bx0-2431 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at122441 c4 = derive (Bx0-2431 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-2431 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw 1 (q58 c4) ∷
   rw⁻ 0 (q57 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx0-2431 ∷ []) (Bx0-4231 ∷ []) (lem-sym12-at122441 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (X4 ∷ Bx0-4231 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx0-4231 ∷ []) (Bx0-2431 ∷ []) (lem-sym12-at1441 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ []) (X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (wl0877 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx0-2431 ∷ CS23 ∷ []) (CS23 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at122441 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Bx0-2431 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at122441 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (Bx0-2431 ∷ CS12 ∷ []) (CS12 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Toff134 ∷ Toff134 ∷ []) [] (wl0627 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (Bx0-4231 ∷ []) (Bx0-4321 ∷ []) (lem-sym23-at1441 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Bx0-4321 ∷ []) (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (Toff134 ∷ Bx0-4312 ∷ Toff134 ∷ []) (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (Bx0-4312 ∷ []) (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (Bx0-4321 ∷ []) (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (Bx0-2431 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (Bx0-2431 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ234 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ []) (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ []) (wl0878 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ234 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ []) (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CCZ234 ∷ []) (wl0879 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl0265 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (Bx0-2431 ∷ Bx0-2431 ∷ []) [] (lem-beta-inv-at122441 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS23 ∷ []) (wl0880 (lit c4))

-- F5 CS23: 38 steps
lem-F5-CS23 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-F5-CS23 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   re 8 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 10 1 (CS12 ∷ []) ∷
   re 12 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   rw 6 (q59 c4) ∷
   rw 6 (q67 c4) ∷
   rw 6 (q68 c4) ∷
   rw 5 (q69 c4) ∷
   rw 5 (q70 c4) ∷
   rw 5 (q71 c4) ∷
   rw 5 (q61 c4) ∷
   rw 5 (q72 c4) ∷
   rw 6 (q73 c4) ∷
   rw⁻ 7 (q66 c4) ∷
   rw 9 (q59 c4) ∷
   rw 9 (q67 c4) ∷
   rw 9 (q68 c4) ∷
   rw 8 (q69 c4) ∷
   rw 8 (q70 c4) ∷
   rw 8 (q71 c4) ∷
   rw 8 (q61 c4) ∷
   rw 8 (q72 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   rw⁻ 2 (q75 c4) ∷
   rw 1 (q76 c4) ∷
   rw 7 (q77 c4) ∷
   rw 0 (q78 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (CS13 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS13 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0113203442 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (Sw12 ∷ Sb0-1-43-2 ∷ []) (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4))

-- auto CS01 | SBOX(2;0;31;4) @0213203441: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0213203441 : Ws → ⟪ (CS23 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS23 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0213203441 c4 = derive (CS23 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS23 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 0 (q81 c4) ∷
   rw⁻ 1 (q55 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ []) (lem-F5-CS23 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp0034 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (Toff024 ∷ Toff024 ∷ []) [] (wp0268 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ []) [] (wl0881 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CS12 ∷ CS12⁻ ∷ []) [] (wl0882 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (CS12⁻ ∷ CS12 ∷ []) [] (wl0187 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (CS23 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS23 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0213203441 c4)

-- F4 CS23^0|CS23^1: 63 steps
lem-F4-CS23ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣CS23ᵖ1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q82 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw⁻ 2 (q84 c4) ∷
   rw⁻ 3 (q85 c4) ∷
   re 5 1 (Bx0-21 ∷ []) ∷
   re 8 1 (Bx0-21 ∷ []) ∷
   re 3 6 (Bx2-031 ∷ []) ∷
   re 4 1 (Bx⁻0-21 ∷ []) ∷
   re 7 1 (Bx⁻0-21 ∷ []) ∷
   re 4 6 (Bx⁻2-031 ∷ []) ∷
   rw⁻ 4 (q84 c4) ∷
   rw⁻ 5 (q83 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   re 8 1 (Bx0-21 ∷ []) ∷
   re 11 1 (Bx0-21 ∷ []) ∷
   re 6 6 (Bx2-031 ∷ []) ∷
   re 7 1 (Bx⁻0-21 ∷ []) ∷
   re 10 1 (Bx⁻0-21 ∷ []) ∷
   re 7 6 (Bx⁻2-031 ∷ []) ∷
   re 1 6 (Bx0-2431 ∷ []) ∷
   re 2 6 (Bx⁻0-2431 ∷ []) ∷
   rw⁻ 2 (q66 c4) ∷
   rw⁻ 3 (q86 c4) ∷
   re 3 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q66 c4) ∷
   rw⁻ 5 (q87 c4) ∷
   re 5 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 6 1 (Sb0-2-1-3 ∷ []) ∷
   re 1 5 (Sb0-2-43-1 ∷ []) ∷
   re 2 5 (Sb⁻0-2-43-1 ∷ []) ∷
   rw 0 (q88 c4) ∷
   rw⁻ 1 (q82 c4) ∷
   re 5 1 (Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ Toff134 ∷ Bx⁻0-2431 ∷ []) ∷
   re 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 8 1 (CS12⁻ ∷ []) ∷
   re 9 1 (CS12 ∷ []) ∷
   rw 8 (q87 c4) ∷
   rw 7 (q66 c4) ∷
   re 6 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 6 (q86 c4) ∷
   rw 5 (q66 c4) ∷
   re 5 1 (Bx⁻2-031 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ []) ∷
   re 4 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) ∷
   re 9 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   re 11 1 (CZ12 ∷ []) ∷
   re 14 1 (CZ12 ∷ []) ∷
   re 15 1 (Bx⁻0-21 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-21 ∷ Toff203 ∷ CCZ023 ∷ []) ∷
   re 15 1 (CZ12 ∷ []) ∷
   re 18 1 (CZ12 ∷ []) ∷
   rw 9 (q85 c4) ∷
   rw 8 (q83 c4) ∷
   rw 7 (q84 c4) ∷
   re 6 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   re 8 1 (CZ12 ∷ []) ∷
   re 11 1 (CZ12 ∷ []) ∷
   re 12 1 (Bx⁻0-21 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-21 ∷ Toff203 ∷ CCZ023 ∷ []) ∷
   re 12 1 (CZ12 ∷ []) ∷
   re 15 1 (CZ12 ∷ []) ∷
   rw 6 (q85 c4) ∷
   rw 5 (q84 c4) ∷
   rw 4 (q83 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = eqn (Bx⁻0-1234 ∷ []) (Bx0-1234 ∷ []) (lem-BOXd-BOX c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (CS12 ∷ []) (CS12 ∷ []) (wl0270 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (CS12 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4)

-- auto BOXd(0;1234) | CS21: 5 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS21 : Ws → ⟪ (Bx⁻0-1234 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS21 c4 = derive (Bx⁻0-1234 ∷ CS12 ∷ []) (CS12 ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw⁻ 0 (q91 c4) ∷
   rw 0 (q90 c4) ∷
   rw⁻ 1 (q89 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = eqn (Bx⁻0-1234 ∷ CS12 ∷ []) (CS12 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS21 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) (wl0272 (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (CS12 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS12 ∷ []) (wl0271 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (CS12 ∷ CS14 ∷ []) (CS14 ∷ CS12 ∷ []) (wl0273 (lit c4))

-- auto SBOXd(0;1;23;4) | CS21: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21 c4 = derive (Sb⁻0-1-23-4 ∷ CS12 ∷ []) (CS12 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 4 (q92 c4) ∷
   rw⁻ 3 (q93 c4) ∷
   re 2 1 (CS14⁻ ∷ []) ∷
   rw⁻ 2 (q94 c4) ∷
   re 3 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q93 c4) ∷
   re 0 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q95 c4) ∷
   re 1 1 (Sb0-1-4-3 ∷ []) ∷
   re 1 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (Sw23 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Sw23 ∷ CS13 ∷ []) (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (Sb⁻0-1-23-4 ∷ CS12 ∷ []) (CS12 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4))
  q101 : Ws → Eqn
  q101 c4 = eqn (Sw23 ∷ Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | CS21 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CS13 ∷ []) (CS13 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q98 c4) ∷
   rw 1 (q99 c4) ∷
   rw 0 (q100 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q96 c4) ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = eqn (CS14 ∷ []) (CS14 ∷ []) (wl0298 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1243 ∷ []) (lem-sym34 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1423 ∷ []) (lem-sym23-at3443 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (CS14 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14 ∷ []) (lem-CS12-beta-at243243 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1243 ∷ []) (lem-sym23-at243243 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1234 ∷ []) (lem-sym34-at3443 c4)

-- auto BOXd(0;1234) | CS41: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS41 : Ws → ⟪ (Bx⁻0-1234 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS41 c4 = derive (Bx⁻0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q89 c4) ∷
   rw 1 (q102 c4) ∷
   rw 0 (q103 c4) ∷
   rw 0 (q104 c4) ∷
   rw⁻ 0 (q105 c4) ∷
   rw 1 (q106 c4) ∷
   rw 1 (q107 c4) ∷
   rw 0 (q102 c4) ∷
   rw⁻ 1 (q89 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (Bx⁻0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS41 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (CS14 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS14 ∷ []) (wl0325 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CS14 ∷ CS14 ∷ []) (CS14 ∷ CS14 ∷ []) (wl0326 (lit c4))

-- auto SBOXd(0;1;23;4) | CS41: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41 c4 = derive (Sb⁻0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 4 (q108 c4) ∷
   re 2 1 (CS14⁻ ∷ []) ∷
   rw⁻ 1 (q109 c4) ∷
   re 3 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 0 1 (CS14 ∷ []) ∷
   rw 0 (q110 c4) ∷
   re 1 1 (Sb0-1-4-3 ∷ []) ∷
   re 1 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (Sb⁻0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41 c4)

-- auto SBOXd(0;1;23;4) | CS41 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw⁻ 2 (q111 c4) ∷
   rw 1 (q112 c4) ∷
   rw⁻ 0 (q111 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q96 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0653 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (Sb⁻0-1-32-4 ∷ CS13 ∷ []) (CS13 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (Bx⁻0-1324 ∷ []) (Bx0-1324 ∷ []) (lem-BOXd-BOX-at2332 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (Bx0-1324 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4)
  q118 : Ws → Eqn
  q118 c4 = eqn (CCZ024 ∷ CX43 ∷ []) (CX43 ∷ CCZ024 ∷ []) (wp0459 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (CCZ024 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff013 ∷ []) (Toff013 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (wp0460 c4)
  q121 : Ws → Eqn
  q121 c4 = eqn (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (wl0883 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (CS14 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0884 (lit c4))
  q123 : Ws → Eqn
  q123 c4 = eqn (Sb⁻0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41-at2332 c4)

-- auto SBOXd(0;1;23;4) | CCZ143: 26 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143 c4 = derive (Sb⁻0-1-23-4 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb⁻0-1-23-4 ∷ [])
  (rw 1 (q113 c4) ∷
   rw 0 (q114 c4) ∷
   rw 0 (q115 c4) ∷
   re 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) ∷
   rw 5 (q116 c4) ∷
   rw 5 (q117 c4) ∷
   rw 8 (q118 c4) ∷
   rw 9 (q119 c4) ∷
   rw 10 (q118 c4) ∷
   rw⁻ 7 (q120 c4) ∷
   rw 6 (q118 c4) ∷
   rw 7 (q119 c4) ∷
   rw 8 (q118 c4) ∷
   rw⁻ 5 (q120 c4) ∷
   rw⁻ 8 (q117 c4) ∷
   rw⁻ 8 (q116 c4) ∷
   re 3 1 (CS14⁻ ∷ []) ∷
   rw⁻ 2 (q121 c4) ∷
   re 6 1 (Sb⁻0-1-4-2 ∷ []) ∷
   re 1 1 (CS14 ∷ []) ∷
   rw 1 (q122 c4) ∷
   re 4 1 (Sb0-1-4-2 ∷ []) ∷
   re 4 5 (Sb⁻0-1-32-4 ∷ []) ∷
   rw 4 (q123 c4) ∷
   rw⁻ 5 (q114 c4) ∷
   rw⁻ 0 (q113 c4) ∷ []) Eq.refl

private
  q124 : Ws → Eqn
  q124 c4 = eqn (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = eqn (Sb⁻0-1-23-4 ∷ CS02 ∷ []) (CS02 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4))

-- auto SBOXd(0;1;23;4) | CS02 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q124 c4) ∷
   rw 1 (q125 c4) ∷
   rw 0 (q126 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q96 c4) ∷ []) Eq.refl

private
  q127 : Ws → Eqn
  q127 c4 = eqn (Sb⁻0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02-at2332 c4)

-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4): 5 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ : Ws → ⟪ (Sb⁻0-1-23-4 ∷ Sb1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ c4 = derive (Sb⁻0-1-23-4 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw 0 (q114 c4) ∷
   rw 0 (q127 c4) ∷
   rw⁻ 1 (q114 c4) ∷
   re 0 1 (Sb1-0-3-4 ∷ []) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (CS02⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CS20-beta-ci c4)

-- auto BOXd(0;1234) | CSd02: 3 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd02 : Ws → ⟪ (Bx⁻0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd02 c4 = derive (Bx⁻0-1234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q89 c4) ∷
   rw⁻ 0 (q128 c4) ∷
   rw⁻ 1 (q89 c4) ∷ []) Eq.refl

private
  q129 : Ws → Eqn
  q129 c4 = eqn (Bx⁻0-1234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd02 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (CS02⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS02⁻ ∷ []) (wp0371 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (CS02⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS02⁻ ∷ []) (wp0370 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (CS02⁻ ∷ CS14 ∷ []) (CS14 ∷ CS02⁻ ∷ []) (wp0372 c4)

-- auto SBOXd(0;1;23;4) | CSd02: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02 c4 = derive (Sb⁻0-1-23-4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Sb⁻0-1-23-4 ∷ [])
  (re 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 4 (q129 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   re 2 1 (CS14⁻ ∷ []) ∷
   rw⁻ 2 (q131 c4) ∷
   re 3 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q130 c4) ∷
   re 0 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q132 c4) ∷
   re 1 1 (Sb0-1-4-3 ∷ []) ∷
   re 1 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = eqn (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (Sb⁻0-1-23-4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02 c4)
  q135 : Ws → Eqn
  q135 c4 = eqn (Sw23 ∷ CS02⁻ ∷ []) (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4))

-- auto SBOXd(0;1;23;4) | CSd02 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q133 c4) ∷
   rw 1 (q134 c4) ∷
   rw 0 (q135 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q96 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = eqn (Sb⁻0-1-32-4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02-at2332 c4)

-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4): 5 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ : Ws → ⟪ (Sb⁻0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ c4 = derive (Sb⁻0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q114 c4) ∷
   rw 0 (q136 c4) ∷
   rw⁻ 1 (q114 c4) ∷
   re 0 1 (Sb⁻1-0-3-4 ∷ []) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q139 : Ws → Eqn
  q139 c4 = eqn (Sw34 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-34-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·43·1⟩ (lit c4))
  q140 : Ws → Eqn
  q140 c4 = eqn (CS01 ∷ Sb0-2-34-1 ∷ []) (Sb0-2-34-1 ∷ CS01 ∷ []) (lem-AX-SB c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (Sw34 ∷ Sb0-2-34-1 ∷ []) (Sb0-2-43-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·34·1⟩ (lit c4))

-- AX-SB @3443: 7 steps
lem-AX-SB-at3443 : Ws → ⟪ (CS01 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS01 ∷ []) ⟫ʷ
lem-AX-SB-at3443 c4 = derive (CS01 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS01 ∷ [])
  (rw⁻ 0 (q137 c4) ∷
   rw⁻ 1 (q138 c4) ∷
   rw 2 (q139 c4) ∷
   rw 1 (q140 c4) ∷
   rw 0 (q141 c4) ∷
   rw⁻ 1 (q138 c4) ∷
   rw 2 (q137 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (Sb⁻0-1-23-4 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143 c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4))

-- auto SBOXd(0;1;23;4) | CCZ143 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q142 c4) ∷
   rw 1 (q143 c4) ∷
   rw 0 (q144 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q96 c4) ∷ []) Eq.refl

private
  q145 : Ws → Eqn
  q145 c4 = eqn (Sw34 ∷ Sb⁻0-1-42-3 ∷ []) (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4))
  q146 : Ws → Eqn
  q146 c4 = eqn (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (Sb⁻0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at2332 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (Sw34 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | CCZ143 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at243243 c4 = derive (Sb⁻0-1-42-3 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb⁻0-1-42-3 ∷ [])
  (rw⁻ 0 (q137 c4) ∷
   rw 1 (q145 c4) ∷
   rw 2 (q146 c4) ∷
   rw 1 (q147 c4) ∷
   rw 0 (q148 c4) ∷
   rw 1 (q149 c4) ∷
   rw 2 (q137 c4) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (Sw01 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4))
  q152 : Ws → Eqn
  q152 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 (lit c4))
  q153 : Ws → Eqn
  q153 c4 = eqn (Sb⁻0-1-42-3 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at243243 c4)
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 (lit c4))
  q155 : Ws → Eqn
  q155 c4 = eqn (Sw01 ∷ Sb⁻0-1-42-3 ∷ []) (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | CCZ143 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0110243243 c4 = derive (Sb⁻1-0-42-3 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb⁻1-0-42-3 ∷ [])
  (rw⁻ 0 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw⁻ 2 (q152 c4) ∷
   rw 1 (q153 c4) ∷
   rw⁻ 0 (q154 c4) ∷
   rw 1 (q155 c4) ∷
   rw 2 (q150 c4) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = eqn (Sw12 ∷ Sb⁻2-0-41-3 ∷ []) (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (Sb⁻1-0-42-3 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0110243243 c4)
  q159 : Ws → Eqn
  q159 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4))
  q160 : Ws → Eqn
  q160 c4 = eqn (Sw12 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | CCZ143 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0210243143 c4 = derive (Sb⁻2-0-41-3 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb⁻2-0-41-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q156 c4) ∷
   rw 2 (q157 c4) ∷
   rw 1 (q158 c4) ∷
   rw 0 (q159 c4) ∷
   rw 1 (q160 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q161 : Ws → Eqn
  q161 c4 = eqn (Sw23 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·4⟩ (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (Sb⁻0-1-23-4 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ c4)
  q163 : Ws → Eqn
  q163 c4 = eqn (Sw23 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·4⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ Sb1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q161 c4) ∷
   rw 1 (q162 c4) ∷
   rw 0 (q163 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q96 c4) ∷ []) Eq.refl

private
  q164 : Ws → Eqn
  q164 c4 = eqn (Sw34 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·3⟩ (lit c4))
  q165 : Ws → Eqn
  q165 c4 = eqn (Sb⁻0-1-32-4 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (Sw34 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·4⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4 = derive (Sb⁻0-1-42-3 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ [])
  (rw⁻ 0 (q137 c4) ∷
   rw 1 (q145 c4) ∷
   rw 2 (q164 c4) ∷
   rw 1 (q165 c4) ∷
   rw 0 (q166 c4) ∷
   rw 1 (q149 c4) ∷
   rw 2 (q137 c4) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = eqn (Sw01 ∷ Sb0-1-2-3 ∷ []) (Sb1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·3⟩ (lit c4))
  q168 : Ws → Eqn
  q168 c4 = eqn (Sb⁻0-1-42-3 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (Sw01 ∷ Sb1-0-2-3 ∷ []) (Sb0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·2·3⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 c4 = derive (Sb⁻1-0-42-3 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ [])
  (rw⁻ 0 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 2 (q167 c4) ∷
   rw 1 (q168 c4) ∷
   rw 0 (q169 c4) ∷
   rw 1 (q155 c4) ∷
   rw 2 (q150 c4) ∷ []) Eq.refl

private
  q170 : Ws → Eqn
  q170 c4 = eqn (Sw12 ∷ Sb0-2-1-3 ∷ []) (Sb0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·1·3⟩ (lit c4))
  q171 : Ws → Eqn
  q171 c4 = eqn (Sb⁻1-0-42-3 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (Sw12 ∷ Sb0-1-2-3 ∷ []) (Sb0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·2·3⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 c4 = derive (Sb⁻2-0-41-3 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q156 c4) ∷
   rw 2 (q170 c4) ∷
   rw 1 (q171 c4) ∷
   rw 0 (q172 c4) ∷
   rw 1 (q160 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q173 : Ws → Eqn
  q173 c4 = eqn (Sw23 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·4⟩ (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (Sb⁻0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (Sw23 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·4⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q173 c4) ∷
   rw 1 (q174 c4) ∷
   rw 0 (q175 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q96 c4) ∷ []) Eq.refl

private
  q176 : Ws → Eqn
  q176 c4 = eqn (Sw34 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·3⟩ (lit c4))
  q177 : Ws → Eqn
  q177 c4 = eqn (Sb⁻0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (Sw34 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·4⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4 = derive (Sb⁻0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ [])
  (rw⁻ 0 (q137 c4) ∷
   rw 1 (q145 c4) ∷
   rw 2 (q176 c4) ∷
   rw 1 (q177 c4) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q149 c4) ∷
   rw 2 (q137 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = eqn (Sw01 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·3⟩ (lit c4))
  q180 : Ws → Eqn
  q180 c4 = eqn (Sb⁻0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (Sw01 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·2·3⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 c4 = derive (Sb⁻1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ [])
  (rw⁻ 0 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 2 (q179 c4) ∷
   rw 1 (q180 c4) ∷
   rw 0 (q181 c4) ∷
   rw 1 (q155 c4) ∷
   rw 2 (q150 c4) ∷ []) Eq.refl

private
  q182 : Ws → Eqn
  q182 c4 = eqn (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·1·3⟩ (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (Sb⁻1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (Sw12 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·2·3⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 c4 = derive (Sb⁻2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q156 c4) ∷
   rw 2 (q182 c4) ∷
   rw 1 (q183 c4) ∷
   rw 0 (q184 c4) ∷
   rw 1 (q160 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl
