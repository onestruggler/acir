{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D089 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0009 ; wl0011 ; wl0012 ; wl0015 ; wl0016 ; wl0018 ; wl0027 ; wl0028 ; wl0050 ; wl0051 ; wl0086 ; wl0335 ; wl0336 ; wl0342 ; wl0353 ; wl0354 ; wl0355 ; wl0379 ; wl0380 ; wl0381 ; wl0382 ; wl0383 ; wl0384 ; wl0385 ; wl0401 ; wl0402 ; wl0403 ; wl0404 ; wl0405 ; wl0406 ; wl0407 ; wl0408 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0454 ; wl0455 ; wl0487 ; wl0488 ; wl0489 ; wl0490 ; wl0491 ; wl0492 ; wl0493 ; wl0494 ; wl0495 ; wl0496 ; wl0497 ; wl0498 ; wl0499 ; wl0500 ; wp0024 ; wp0060 ; wp0098 ; wp0099 ; wp0100 ; wp0115 ; wp0116 ; wp0117 ; wp0118 ; wp0119 ; wp0120 ; wp0127 ; wp0128 ; wp0129 ; wp0130 ; wp0140 ; wp0141 ; wp0173 ; wp0174)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-CS20-beta-c ; lem-F0 ; lem-T-beta ; lem-beta-T-at132132 ; lem-beta-T-at2332 ; lem-sym12-at132132 ; lem-sym23 ; lem-sym23-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at2332 ; lem-CSd12-beta-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 ; lem-beta-T-at0210243143 ; lem-sym12-at0210243143 ; lem-sym12-at2332 ; lem-sym12-at233442 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym23-at2332 ; lem-sym34-at13213442 ; lem-sym34-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-SBsym-at0113203442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-CS12-beta-at13243142 ; lem-CS20-beta-c-at2332 ; lem-SBsymd-at0113203442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS43 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-X1-beta-at02203443 ; lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 ; lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 ; lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at2332 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at2332 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at2332 ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym12-at0210213443 ; lem-sym12-at02203443 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D044 using (lem-F1-CS-K0-rhs-shape)
open import Examples.Groups.Clifford+CS.Five.D.D045 using (lem-F1-CS-K0-part0)
open import Examples.Groups.Clifford+CS.Five.D.D046 using (lem-F1-CS-K0-part1)
open import Examples.Groups.Clifford+CS.Five.D.D047 using (lem-F1-CS-K0-part2)
open import Examples.Groups.Clifford+CS.Five.D.D048 using (lem-F1-CS-K0-part3)
open import Examples.Groups.Clifford+CS.Five.D.D049 using (lem-F1-CS-K0-part4)
open import Examples.Groups.Clifford+CS.Five.D.D050 using (lem-F1-CS-K0-part5)
open import Examples.Groups.Clifford+CS.Five.D.D051 using (lem-F1-CS-K0-part6)
open import Examples.Groups.Clifford+CS.Five.D.D052 using (lem-F1-CS-K0-part7)
open import Examples.Groups.Clifford+CS.Five.D.D053 using (lem-F1-CS-K0-part8)
open import Examples.Groups.Clifford+CS.Five.D.D054 using (lem-F1-CS-K0-part9)
open import Examples.Groups.Clifford+CS.Five.D.D055 using (lem-F1-CS-K0-part10)
open import Examples.Groups.Clifford+CS.Five.D.D056 using (lem-F1-CS-K0-part11)
open import Examples.Groups.Clifford+CS.Five.D.D057 using (lem-F1-CS-K0-part12)
open import Examples.Groups.Clifford+CS.Five.D.D058 using (lem-F1-CS-K0-part13)
open import Examples.Groups.Clifford+CS.Five.D.D059 using (lem-F1-CS-K0-part14)
open import Examples.Groups.Clifford+CS.Five.D.D060 using (lem-F1-CS-K0-part15)
open import Examples.Groups.Clifford+CS.Five.D.D061 using (lem-F1-CS-K0-part16)
open import Examples.Groups.Clifford+CS.Five.D.D062 using (lem-F1-CS-K0-part17)
open import Examples.Groups.Clifford+CS.Five.D.D063 using (lem-F1-CS-K0-part18)
open import Examples.Groups.Clifford+CS.Five.D.D064 using (lem-F1-CS-K0-part19)
open import Examples.Groups.Clifford+CS.Five.D.D065 using (lem-F1-CS-K0-part20)
open import Examples.Groups.Clifford+CS.Five.D.D066 using (lem-F1-CS-K0-part21)
open import Examples.Groups.Clifford+CS.Five.D.D067 using (lem-F1-CS-K0-part22)
open import Examples.Groups.Clifford+CS.Five.D.D068 using (lem-F1-CS-K0-part23)
open import Examples.Groups.Clifford+CS.Five.D.D069 using (lem-F1-CS-K0-part24)
open import Examples.Groups.Clifford+CS.Five.D.D070 using (lem-F1-CS-K0-part25)
open import Examples.Groups.Clifford+CS.Five.D.D071 using (lem-F1-CS-K0-part26)
open import Examples.Groups.Clifford+CS.Five.D.D072 using (lem-F1-CS-K0-part27)
open import Examples.Groups.Clifford+CS.Five.D.D073 using (lem-F1-CS-K0-part28)
open import Examples.Groups.Clifford+CS.Five.D.D074 using (lem-F1-CS-K0-part29)
open import Examples.Groups.Clifford+CS.Five.D.D075 using (lem-F1-CS-K0-part30)
open import Examples.Groups.Clifford+CS.Five.D.D076 using (lem-F1-CS-K0-part31)
open import Examples.Groups.Clifford+CS.Five.D.D077 using (lem-F1-CS-K0-part32)
open import Examples.Groups.Clifford+CS.Five.D.D078 using (lem-F1-CS-K0-part33)
open import Examples.Groups.Clifford+CS.Five.D.D079 using (lem-F1-CS-K0-part34)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-F1-CS-K0-part35)
open import Examples.Groups.Clifford+CS.Five.D.D081 using (lem-F1-CS-K0-part36)
open import Examples.Groups.Clifford+CS.Five.D.D082 using (lem-F1-CS-K0-part37)
open import Examples.Groups.Clifford+CS.Five.D.D083 using (lem-F1-CS-K0-part38)
open import Examples.Groups.Clifford+CS.Five.D.D084 using (lem-F1-CS-K0-part39)
open import Examples.Groups.Clifford+CS.Five.D.D085 using (lem-F1-CS-K0-part40)
open import Examples.Groups.Clifford+CS.Five.D.D086 using (lem-F1-CS-K0-part41)
open import Examples.Groups.Clifford+CS.Five.D.D087 using (lem-F1-CS-K0-part42)
open import Examples.Groups.Clifford+CS.Five.D.D088 using (lem-F1-CS-K0-part43)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ024 ; lem-nat-2-BOX⟨0·3412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-2-BOX⟨0·2413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-3-BOX⟨0·4123⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-TOFF013 ; lem-nat-2-BOX⟨2·4013⟩ ; lem-nat-3-BOX⟨0·3124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-2-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-2-CS02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-CS03 ; lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CX41-TOFF203)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CCZ014-CX23 ; lem-comm-TOFF013-CSd24 ; lem-nat-0-SBOX⟨1·4·20·3⟩ ; lem-nat-0-SBOX⟨2·1·40·3⟩ ; lem-nat-0-SBOX⟨3·0·41·2⟩ ; lem-nat-0-SBOX⟨3·4·21·0⟩ ; lem-nat-1-BOX⟨0·3214⟩ ; lem-nat-1-SBOX⟨0·4·21·3⟩ ; lem-nat-1-SBOX⟨1·2·40·3⟩ ; lem-nat-1-SBOX⟨2·4·30·1⟩ ; lem-nat-1-SBOX⟨3·1·40·2⟩ ; lem-nat-1-SBOX⟨3·4·12·0⟩ ; lem-nat-2-SBOX⟨1·3·40·2⟩ ; lem-nat-2-SBOX⟨1·4·30·2⟩ ; lem-nat-2-SBOX⟨3·2·40·1⟩ ; lem-nat-2-SBOX⟨3·4·20·1⟩ ; lem-nat-3-SBOX⟨0·3·4·2⟩ ; lem-nat-3-SBOX⟨0·4·3·2⟩ ; lem-nat-3-SBOX⟨1·4·30·2⟩ ; lem-nat-3-SBOX⟨2·3·40·1⟩ ; lem-nat-3-SBOXd⟨0·3·4·2⟩ ; lem-nat-3-SBOXd⟨0·4·3·2⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS14⁻ ∷ []) (wp0127 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CS14⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS14⁻ ∷ []) (wl0380 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CS14⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS14⁻ ∷ []) (wl0381 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CS14⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS14⁻ ∷ []) (wp0128 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CS14⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS14⁻ ∷ []) (wp0129 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ []) (wp0130 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ []) (wl0382 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ []) (wl0383 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (S1 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1 ∷ []) (wl0384 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (S1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1 ∷ []) (wl0385 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ []) (wl0401 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (K3⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) (wl0405 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) (wl0406 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CX41 ∷ Toff203 ∷ []) (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0140 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0141 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) (wl0455 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) (wl0454 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) (wl0418 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (K3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) (wl0419 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx2-0143 ∷ []) (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (X1 ∷ Bx2-1043 ∷ X1 ∷ []) (CCZ034 ∷ Bx2-1043 ∷ []) (lem-X1-beta-at02203443 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ034 ∷ X1 ∷ []) (X1 ∷ CCZ034 ∷ []) (wp0060 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (Sb2-0-41-3 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ034 ∷ CCZ034 ∷ []) [] (wp0024 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape c4)

-- F1 CS-K0 part44: 264 steps
lem-F1-CS-K0-part44 : Ws → ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-part44 c4 = derive (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ [])
  (rw 2 (q1 c4) ∷
   rw 5 (q2 c4) ∷
   rw 8 (q1 c4) ∷
   rw 11 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw 5 (q3 c4) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   re 10 1 (CS03 ∷ []) ∷
   rw 8 (q6 c4) ∷
   re 9 1 (Sb2-0-3-1 ∷ []) ∷
   rw 11 (q5 c4) ∷
   re 16 1 (CS03⁻ ∷ []) ∷
   rw 14 (q7 c4) ∷
   re 15 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw 5 (q3 c4) ∷
   rw 6 (q3 c4) ∷
   rw 7 (q3 c4) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw⁻ 13 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw 1 (q8 c4) ∷
   rw 4 (q9 c4) ∷
   rw 7 (q8 c4) ∷
   rw 10 (q9 c4) ∷
   rw 3 (q3 c4) ∷
   rw 4 (q3 c4) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw 4 (q10 c4) ∷
   re 9 1 (CS03 ∷ []) ∷
   rw 7 (q11 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   rw 10 (q10 c4) ∷
   re 15 1 (CS03⁻ ∷ []) ∷
   rw 13 (q12 c4) ∷
   re 14 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 3 (q3 c4) ∷
   rw 4 (q3 c4) ∷
   rw 5 (q3 c4) ∷
   rw 6 (q3 c4) ∷
   re 2 5 (Sb2-0-41-3 ∷ []) ∷
   re 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 4 1 (CS03⁻ ∷ []) ∷
   rw 4 (q13 c4) ∷
   re 5 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 5 (q14 c4) ∷
   re 6 1 (CS03⁻ ∷ []) ∷
   rw 6 (q13 c4) ∷
   re 7 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q15 c4) ∷
   rw 5 (q16 c4) ∷
   rw 6 (q17 c4) ∷
   rw 7 (q16 c4) ∷
   rw 4 (q18 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q20 c4) ∷
   rw 10 (q19 c4) ∷
   re 9 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 10 (q3 c4) ∷
   rw⁻ 13 (q3 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   rw⁻ 19 (q3 c4) ∷
   rw 9 (q21 c4) ∷
   rw 9 (q22 c4) ∷
   rw 9 (q23 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw⁻ 13 (q3 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   rw 7 (q24 c4) ∷
   rw 8 (q25 c4) ∷
   rw 9 (q24 c4) ∷
   rw 6 (q26 c4) ∷
   rw 5 (q24 c4) ∷
   rw 6 (q25 c4) ∷
   rw 7 (q24 c4) ∷
   rw 8 (q27 c4) ∷
   rw 13 (q24 c4) ∷
   rw 14 (q25 c4) ∷
   rw 15 (q24 c4) ∷
   rw 12 (q26 c4) ∷
   rw 11 (q24 c4) ∷
   rw 12 (q25 c4) ∷
   rw 13 (q24 c4) ∷
   rw 14 (q27 c4) ∷
   rw 7 (q3 c4) ∷
   rw 8 (q3 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   rw 6 (q28 c4) ∷
   rw 6 (q29 c4) ∷
   re 15 1 (CS03 ∷ []) ∷
   rw 8 (q30 c4) ∷
   re 12 1 (Sb2-0-3-1 ∷ []) ∷
   re 21 1 (CS03⁻ ∷ []) ∷
   rw 17 (q31 c4) ∷
   re 18 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw 8 (q3 c4) ∷
   rw 9 (q3 c4) ∷
   rw 10 (q3 c4) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   re 6 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 7 (q3 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw⁻ 13 (q3 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   rw 6 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw⁻ 13 (q3 c4) ∷
   rw 4 (q34 c4) ∷
   rw 7 (q35 c4) ∷
   rw 10 (q34 c4) ∷
   rw 13 (q35 c4) ∷
   rw 6 (q3 c4) ∷
   rw 7 (q3 c4) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 5 (q33 c4) ∷
   rw 5 (q36 c4) ∷
   rw 7 (q37 c4) ∷
   re 12 1 (CS03 ∷ []) ∷
   rw 10 (q38 c4) ∷
   re 11 1 (Sb2-0-3-1 ∷ []) ∷
   rw 13 (q37 c4) ∷
   re 18 1 (CS03⁻ ∷ []) ∷
   rw 16 (q39 c4) ∷
   re 17 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw 7 (q3 c4) ∷
   rw 8 (q3 c4) ∷
   rw 9 (q3 c4) ∷
   re 5 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 7 (q18 c4) ∷
   rw 3 (q40 c4) ∷
   rw 4 (q41 c4) ∷
   rw 5 (q40 c4) ∷
   rw 6 (q15 c4) ∷
   re 2 1 (CS03 ∷ []) ∷
   rw 2 (q42 c4) ∷
   re 3 1 (Sb2-0-3-1 ∷ []) ∷
   rw 3 (q43 c4) ∷
   re 4 1 (CS03 ∷ []) ∷
   rw 4 (q42 c4) ∷
   re 5 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 1 (q15 c4) ∷
   rw 3 (q16 c4) ∷
   rw 4 (q17 c4) ∷
   rw 5 (q16 c4) ∷
   rw 2 (q18 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q20 c4) ∷
   rw 8 (q19 c4) ∷
   re 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw⁻ 14 (q3 c4) ∷
   rw⁻ 17 (q3 c4) ∷
   rw 7 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw 7 (q23 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw⁻ 14 (q3 c4) ∷
   rw 5 (q24 c4) ∷
   rw 6 (q25 c4) ∷
   rw 7 (q24 c4) ∷
   rw 4 (q26 c4) ∷
   rw 3 (q24 c4) ∷
   rw 4 (q25 c4) ∷
   rw 5 (q24 c4) ∷
   rw 6 (q27 c4) ∷
   rw 11 (q24 c4) ∷
   rw 12 (q25 c4) ∷
   rw 13 (q24 c4) ∷
   rw 10 (q26 c4) ∷
   rw 9 (q24 c4) ∷
   rw 10 (q25 c4) ∷
   rw 11 (q24 c4) ∷
   rw 12 (q27 c4) ∷
   rw 5 (q3 c4) ∷
   rw 6 (q3 c4) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   rw 4 (q28 c4) ∷
   rw 4 (q29 c4) ∷
   re 13 1 (CS03 ∷ []) ∷
   rw 6 (q30 c4) ∷
   re 10 1 (Sb2-0-3-1 ∷ []) ∷
   re 19 1 (CS03⁻ ∷ []) ∷
   rw 15 (q31 c4) ∷
   re 16 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw 6 (q3 c4) ∷
   rw 7 (q3 c4) ∷
   rw 8 (q3 c4) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   re 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw⁻ 14 (q3 c4) ∷
   rw 4 (q32 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw 2 (q34 c4) ∷
   rw 5 (q35 c4) ∷
   rw 8 (q34 c4) ∷
   rw 11 (q35 c4) ∷
   rw 4 (q3 c4) ∷
   rw 5 (q3 c4) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw 3 (q36 c4) ∷
   rw 5 (q37 c4) ∷
   re 10 1 (CS03 ∷ []) ∷
   rw 8 (q38 c4) ∷
   re 9 1 (Sb2-0-3-1 ∷ []) ∷
   rw 11 (q37 c4) ∷
   re 16 1 (CS03⁻ ∷ []) ∷
   rw 14 (q39 c4) ∷
   re 15 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw 5 (q3 c4) ∷
   rw 6 (q3 c4) ∷
   rw 7 (q3 c4) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 5 (q18 c4) ∷
   rw 1 (q40 c4) ∷
   rw 2 (q41 c4) ∷
   rw 3 (q40 c4) ∷
   rw 4 (q15 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   rw 2 (q32 c4) ∷
   rw 2 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q46 c4) ∷
   rw 2 (q36 c4) ∷
   rw 2 (q47 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 5 (q32 c4) ∷
   rw 5 (q44 c4) ∷
   rw 4 (q45 c4) ∷
   rw 5 (q46 c4) ∷
   rw 5 (q36 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw 2 (q49 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   rw 0 (q50 c4) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part0 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part1 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part2 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ K2 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part3 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ K2 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ K3 ∷ X1 ∷ CZ13 ∷ K3⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part4 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ K3 ∷ X1 ∷ CZ13 ∷ K3⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part5 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx2-0341 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part6 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx2-0341 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part7 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part8 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part9 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part10 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0431 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part11 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0431 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ X1 ∷ CS03 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part12 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ X1 ∷ CS03 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part13 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0431 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part14 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0431 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ Sb2-0-41-3 ∷ CCZ034 ∷ X1 ∷ CCZ034 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part15 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ Sb2-0-41-3 ∷ CCZ034 ∷ X1 ∷ CCZ034 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part16 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part17 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part18 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part19 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part20 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part21 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part22 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part23 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part24 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ CS03 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part25 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ CS03 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part26 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Bx2-0413 ∷ CS23 ∷ X1 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part27 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Bx2-0413 ∷ CS23 ∷ X1 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0341 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part28 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0341 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ X1 ∷ CS23⁻ ∷ Bx2-0413 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part29 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ X1 ∷ CS23⁻ ∷ Bx2-0413 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Bx2-0143 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part30 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Bx2-0143 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part31 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ ι⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part32 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ ι⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part33 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CCZ134 ∷ X1 ∷ K3⁻ ∷ Sb2-0-41-3 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part34 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CCZ134 ∷ X1 ∷ K3⁻ ∷ Sb2-0-41-3 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part35 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (lem-F1-CS-K0-part36 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-part37 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-part38 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-part39 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Bx2-0143 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-part40 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Bx2-0143 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-part41 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-part42 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-part43 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-part44 c4)

-- F1 CS-K0: 45 steps
lem-F1-CS-K0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0 c4 = derive (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ [])
  (rw 0 (q52 c4) ∷
   rw 0 (q53 c4) ∷
   rw 0 (q54 c4) ∷
   rw 0 (q55 c4) ∷
   rw 0 (q56 c4) ∷
   rw 0 (q57 c4) ∷
   rw 0 (q58 c4) ∷
   rw 0 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 0 (q61 c4) ∷
   rw 0 (q62 c4) ∷
   rw 0 (q63 c4) ∷
   rw 0 (q64 c4) ∷
   rw 0 (q65 c4) ∷
   rw 0 (q66 c4) ∷
   rw 0 (q67 c4) ∷
   rw 0 (q68 c4) ∷
   rw 0 (q69 c4) ∷
   rw 0 (q70 c4) ∷
   rw 0 (q71 c4) ∷
   rw 0 (q72 c4) ∷
   rw 0 (q73 c4) ∷
   rw 0 (q74 c4) ∷
   rw 0 (q75 c4) ∷
   rw 0 (q76 c4) ∷
   rw 0 (q77 c4) ∷
   rw 0 (q78 c4) ∷
   rw 0 (q79 c4) ∷
   rw 0 (q80 c4) ∷
   rw 0 (q81 c4) ∷
   rw 0 (q82 c4) ∷
   rw 0 (q83 c4) ∷
   rw 0 (q84 c4) ∷
   rw 0 (q85 c4) ∷
   rw 0 (q86 c4) ∷
   rw 0 (q87 c4) ∷
   rw 0 (q88 c4) ∷
   rw 0 (q89 c4) ∷
   rw 0 (q90 c4) ∷
   rw 0 (q91 c4) ∷
   rw 0 (q92 c4) ∷
   rw 0 (q93 c4) ∷
   rw 0 (q94 c4) ∷
   rw 0 (q95 c4) ∷
   rw 0 (q96 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = eqn (Bx0-3124 ∷ []) (Bx0-1324 ∷ []) (lem-sym12-at132132 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1234 ∷ []) (lem-sym23-at2332 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ []) (lem-T-beta c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1324 ∷ []) (lem-sym23 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (Bx0-1324 ∷ []) (Bx0-3124 ∷ []) (lem-sym12-at2332 c4)

-- auto TOFF012 | BOX(0;3124): 5 steps
lem-auto-TOFF012-∣-BOX⟨0·3124⟩ : Ws → ⟪ (Toff012 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3124⟩ c4 = derive (Toff012 ∷ Bx0-3124 ∷ []) (Bx0-3124 ∷ Toff012 ∷ [])
  (rw 1 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 0 (q99 c4) ∷
   rw 0 (q100 c4) ∷
   rw 0 (q101 c4) ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = eqn (Toff012 ∷ Sb0-3-4-2 ∷ []) (Sb0-3-4-2 ∷ Toff012 ∷ []) (c₃ (Toff) (CS))

-- auto TOFF012 | SBOX(0;3;4;2): 1 steps
lem-auto-TOFF012-∣-SBOX⟨0·3·4·2⟩ : Ws → ⟪ (Toff012 ∷ Sb0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-2 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨0·3·4·2⟩ c4 = derive (Toff012 ∷ Sb0-3-4-2 ∷ []) (Sb0-3-4-2 ∷ Toff012 ∷ [])
  (rw 0 (q102 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = eqn (Toff012 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-3-4-2 ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS))

-- auto TOFF012 | SBOXd(0;3;4;2): 1 steps
lem-auto-TOFF012-∣-SBOXd⟨0·3·4·2⟩ : Ws → ⟪ (Toff012 ∷ Sb⁻0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-2 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOXd⟨0·3·4·2⟩ c4 = derive (Toff012 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-3-4-2 ∷ Toff012 ∷ [])
  (rw 0 (q103 c4) ∷ []) Eq.refl

private
  q104 : Ws → Eqn
  q104 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (Sw01 ∷ Sb2-1-40-3 ∷ []) (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (Sw01 ∷ Sb3-0-41-2 ∷ []) (Sb3-1-40-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·41·2⟩ (lit c4))

-- F0 @0110: 5 steps
lem-F0-at0110 : Ws → ⟪ (Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-40-2 ∷ []) ⟫ʷ
lem-F0-at0110 c4 = derive (Sb2-1-40-3 ∷ []) (Sb3-1-40-2 ∷ [])
  (rw⁻ 0 (q104 c4) ∷
   rw 1 (q105 c4) ∷
   rw 1 (q106 c4) ∷
   rw 0 (q107 c4) ∷
   rw 1 (q104 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (Sw12 ∷ Sb1-2-40-3 ∷ []) (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (Sb2-1-40-3 ∷ []) (Sb3-1-40-2 ∷ []) (lem-F0-at0110 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (Sw12 ∷ Sb3-1-40-2 ∷ []) (Sb3-2-40-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·1·40·2⟩ (lit c4))

-- F0 @021021: 5 steps
lem-F0-at021021 : Ws → ⟪ (Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-2-40-1 ∷ []) ⟫ʷ
lem-F0-at021021 c4 = derive (Sb1-2-40-3 ∷ []) (Sb3-2-40-1 ∷ [])
  (rw⁻ 0 (q108 c4) ∷
   rw 1 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw 0 (q111 c4) ∷
   rw 1 (q108 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (Sw23 ∷ Sb1-3-40-2 ∷ []) (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (Sb1-2-40-3 ∷ []) (Sb3-2-40-1 ∷ []) (lem-F0-at021021 c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (Sw23 ∷ Sb3-2-40-1 ∷ []) (Sb2-3-40-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·2·40·1⟩ (lit c4))

-- F0 @03102132: 5 steps
lem-F0-at03102132 : Ws → ⟪ (Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ []) ⟫ʷ
lem-F0-at03102132 c4 = derive (Sb1-3-40-2 ∷ []) (Sb2-3-40-1 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw 1 (q113 c4) ∷
   rw 1 (q114 c4) ∷
   rw 0 (q115 c4) ∷
   rw 1 (q112 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q117 : Ws → Eqn
  q117 c4 = eqn (Sw34 ∷ Sb1-4-30-2 ∷ []) (Sb1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·30·2⟩ (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (Sb1-3-40-2 ∷ []) (Sb2-3-40-1 ∷ []) (lem-F0-at03102132 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (Sw34 ∷ Sb2-3-40-1 ∷ []) (Sb2-4-30-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·3·40·1⟩ (lit c4))

-- F0 @0410213243: 5 steps
lem-F0-at0410213243 : Ws → ⟪ (Sb1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-30-1 ∷ []) ⟫ʷ
lem-F0-at0410213243 c4 = derive (Sb1-4-30-2 ∷ []) (Sb2-4-30-1 ∷ [])
  (rw⁻ 0 (q116 c4) ∷
   rw 1 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 0 (q119 c4) ∷
   rw 1 (q116 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw12 ∷ Sb2-4-30-1 ∷ []) (Sb1-4-30-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·30·1⟩ (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (Sb1-4-30-2 ∷ []) (Sb2-4-30-1 ∷ []) (lem-F0-at0410213243 c4)

-- F0 @04103143: 5 steps
lem-F0-at04103143 : Ws → ⟪ (Sb2-4-30-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-30-2 ∷ []) ⟫ʷ
lem-F0-at04103143 c4 = derive (Sb2-4-30-1 ∷ []) (Sb1-4-30-2 ∷ [])
  (rw⁻ 0 (q108 c4) ∷
   rw 1 (q120 c4) ∷
   rw 1 (q121 c4) ∷
   rw 0 (q120 c4) ∷
   rw 1 (q108 c4) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = eqn (Sw23 ∷ Sb3-4-20-1 ∷ []) (Sb2-4-30-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·20·1⟩ (lit c4))
  q123 : Ws → Eqn
  q123 c4 = eqn (Sb2-4-30-1 ∷ []) (Sb1-4-30-2 ∷ []) (lem-F0-at04103143 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (Sw23 ∷ Sb1-4-30-2 ∷ []) (Sb1-4-20-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·30·2⟩ (lit c4))

-- F0 @0410233142: 5 steps
lem-F0-at0410233142 : Ws → ⟪ (Sb3-4-20-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-20-3 ∷ []) ⟫ʷ
lem-F0-at0410233142 c4 = derive (Sb3-4-20-1 ∷ []) (Sb1-4-20-3 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw 1 (q122 c4) ∷
   rw 1 (q123 c4) ∷
   rw 0 (q124 c4) ∷
   rw 1 (q112 c4) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = eqn (Sw01 ∷ Sb3-4-21-0 ∷ []) (Sb3-4-20-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·21·0⟩ (lit c4))
  q126 : Ws → Eqn
  q126 c4 = eqn (Sb3-4-20-1 ∷ []) (Sb1-4-20-3 ∷ []) (lem-F0-at0410233142 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (Sw01 ∷ Sb1-4-20-3 ∷ []) (Sb0-4-21-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·4·20·3⟩ (lit c4))

-- F0 @04233042: 5 steps
lem-F0-at04233042 : Ws → ⟪ (Sb3-4-21-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-21-3 ∷ []) ⟫ʷ
lem-F0-at04233042 c4 = derive (Sb3-4-21-0 ∷ []) (Sb0-4-21-3 ∷ [])
  (rw⁻ 0 (q104 c4) ∷
   rw 1 (q125 c4) ∷
   rw 1 (q126 c4) ∷
   rw 0 (q127 c4) ∷
   rw 1 (q104 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (Sw12 ∷ Sb3-4-12-0 ∷ []) (Sb3-4-21-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·12·0⟩ (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (Sb3-4-21-0 ∷ []) (Sb0-4-21-3 ∷ []) (lem-F0-at04233042 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (Sw12 ∷ Sb0-4-21-3 ∷ []) (Sb0-4-12-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·4·21·3⟩ (lit c4))

-- F0 @0412233041: 5 steps
lem-F0-at0412233041 : Ws → ⟪ (Sb3-4-12-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-12-3 ∷ []) ⟫ʷ
lem-F0-at0412233041 c4 = derive (Sb3-4-12-0 ∷ []) (Sb0-4-12-3 ∷ [])
  (rw⁻ 0 (q108 c4) ∷
   rw 1 (q128 c4) ∷
   rw 1 (q129 c4) ∷
   rw 0 (q130 c4) ∷
   rw 1 (q108 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = eqn (Toff012 ∷ Sw34 ∷ []) (Sw34 ∷ Toff012 ∷ []) (c₃ (Toff) (Swap))
  q132 : Ws → Eqn
  q132 c4 = eqn (Sw34 ∷ Bx0-4123 ∷ []) (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ (lit c4))
  q133 : Ws → Eqn
  q133 c4 = eqn (Toff012 ∷ Bx0-3124 ∷ []) (Bx0-3124 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3124⟩ c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (Sw34 ∷ Bx0-3124 ∷ []) (Bx0-4123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3124⟩ (lit c4))

-- auto TOFF012 | BOX(0;3124) @3443: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at3443 : Ws → ⟪ (Toff012 ∷ Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at3443 c4 = derive (Toff012 ∷ Bx0-4123 ∷ []) (Bx0-4123 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q116 c4) ∷
   rw⁻ 1 (q131 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q133 c4) ∷
   rw 0 (q134 c4) ∷
   rw⁻ 1 (q131 c4) ∷
   rw 2 (q116 c4) ∷ []) Eq.refl

private
  q135 : Ws → Eqn
  q135 c4 = eqn (Sw34 ∷ Sb0-4-3-2 ∷ []) (Sb0-3-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·4·3·2⟩ (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (Toff012 ∷ Sb0-3-4-2 ∷ []) (Sb0-3-4-2 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨0·3·4·2⟩ c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (Sw34 ∷ Sb0-3-4-2 ∷ []) (Sb0-4-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·3·4·2⟩ (lit c4))

-- auto TOFF012 | SBOX(0;3;4;2) @3443: 7 steps
lem-auto-TOFF012-∣-SBOX⟨0·3·4·2⟩-at3443 : Ws → ⟪ (Toff012 ∷ Sb0-4-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-2 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨0·3·4·2⟩-at3443 c4 = derive (Toff012 ∷ Sb0-4-3-2 ∷ []) (Sb0-4-3-2 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q116 c4) ∷
   rw⁻ 1 (q131 c4) ∷
   rw 2 (q135 c4) ∷
   rw 1 (q136 c4) ∷
   rw 0 (q137 c4) ∷
   rw⁻ 1 (q131 c4) ∷
   rw 2 (q116 c4) ∷ []) Eq.refl

private
  q138 : Ws → Eqn
  q138 c4 = eqn (Sw34 ∷ Sb⁻0-4-3-2 ∷ []) (Sb⁻0-3-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·4·3·2⟩ (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (Toff012 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-3-4-2 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-SBOXd⟨0·3·4·2⟩ c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (Sw34 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-4-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·3·4·2⟩ (lit c4))

-- auto TOFF012 | SBOXd(0;3;4;2) @3443: 7 steps
lem-auto-TOFF012-∣-SBOXd⟨0·3·4·2⟩-at3443 : Ws → ⟪ (Toff012 ∷ Sb⁻0-4-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-2 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOXd⟨0·3·4·2⟩-at3443 c4 = derive (Toff012 ∷ Sb⁻0-4-3-2 ∷ []) (Sb⁻0-4-3-2 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q116 c4) ∷
   rw⁻ 1 (q131 c4) ∷
   rw 2 (q138 c4) ∷
   rw 1 (q139 c4) ∷
   rw 0 (q140 c4) ∷
   rw⁻ 1 (q131 c4) ∷
   rw 2 (q116 c4) ∷ []) Eq.refl

private
  q141 : Ws → Eqn
  q141 c4 = eqn (Sb3-4-12-0 ∷ []) (Sb0-4-12-3 ∷ []) (lem-F0-at0412233041 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (Toff012 ∷ Bx0-4123 ∷ []) (Bx0-4123 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3124⟩-at3443 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (Toff012 ∷ Toff312 ∷ []) (Toff312 ∷ Toff012 ∷ []) (wl0487 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (Toff012 ∷ Sb0-4-3-2 ∷ []) (Sb0-4-3-2 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨0·3·4·2⟩-at3443 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (Toff012 ∷ Sb⁻0-4-3-2 ∷ []) (Sb⁻0-4-3-2 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-SBOXd⟨0·3·4·2⟩-at3443 c4)

-- auto TOFF012 | SBOX(3;4;12;0): 9 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩ : Ws → ⟪ (Toff012 ∷ Sb3-4-12-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-12-0 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩ c4 = derive (Toff012 ∷ Sb3-4-12-0 ∷ []) (Sb3-4-12-0 ∷ Toff012 ∷ [])
  (rw 1 (q141 c4) ∷
   re 1 1 (Bx0-4123 ∷ Toff312 ∷ Sb0-4-3-2 ∷ Toff312 ∷ Sb⁻0-4-3-2 ∷ []) ∷
   rw 0 (q142 c4) ∷
   rw 1 (q143 c4) ∷
   rw 2 (q144 c4) ∷
   rw 3 (q143 c4) ∷
   rw 4 (q145 c4) ∷
   re 0 5 (Sb0-4-12-3 ∷ []) ∷
   rw⁻ 0 (q141 c4) ∷ []) Eq.refl

private
  q146 : Ws → Eqn
  q146 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 (lit c4))
  q148 : Ws → Eqn
  q148 c4 = eqn (Sb0-1-23-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34 c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 (lit c4))
  q150 : Ws → Eqn
  q150 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CS34 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-at2332 c4 = derive (Sb0-1-32-4 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw 1 (q146 c4) ∷
   rw⁻ 2 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw⁻ 0 (q149 c4) ∷
   rw 1 (q150 c4) ∷
   rw 2 (q112 c4) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = eqn (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (Sb0-1-32-4 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-at2332 c4)

-- auto SBOX(0;1;23;4) | CS24 CS24: 6 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-CS24 : Ws → ⟪ (Sb0-1-23-4 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS24 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-CS24 c4 = derive (Sb0-1-23-4 ∷ CS24 ∷ CS24 ∷ []) (CS24 ∷ CS24 ∷ Sb0-1-23-4 ∷ [])
  (rw 0 (q151 c4) ∷
   rw 0 (q152 c4) ∷
   rw⁻ 1 (q151 c4) ∷
   rw 1 (q151 c4) ∷
   rw 1 (q152 c4) ∷
   rw⁻ 2 (q151 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = eqn (Sb0-1-23-4 ∷ CS24 ∷ CS24 ∷ []) (CS24 ∷ CS24 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-CS24 c4)

-- auto SBOX(0;1;23;4) | CS24 CS24 @2332: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-CS24-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS34 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-CS24-at2332 c4 = derive (Sb0-1-32-4 ∷ CS34 ∷ CS34 ∷ []) (CS34 ∷ CS34 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw 1 (q146 c4) ∷
   rw⁻ 2 (q149 c4) ∷
   rw⁻ 3 (q149 c4) ∷
   rw 1 (q153 c4) ∷
   rw⁻ 0 (q147 c4) ∷
   rw⁻ 1 (q147 c4) ∷
   rw 2 (q150 c4) ∷
   rw 3 (q112 c4) ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = eqn (CS34 ∷ CS34 ∷ []) (CZ34 ∷ []) (wl0488 (lit c4))
  q155 : Ws → Eqn
  q155 c4 = eqn (Sb0-1-32-4 ∷ CS34 ∷ CS34 ∷ []) (CS34 ∷ CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-CS24-at2332 c4)

-- auto SBOX(0;1;23;4) | CZ34: 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ34 : Ws → ⟪ (Sb0-1-23-4 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CZ34 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ34 c4 = derive (Sb0-1-23-4 ∷ CZ34 ∷ []) (CZ34 ∷ Sb0-1-23-4 ∷ [])
  (rw⁻ 1 (q154 c4) ∷
   rw 0 (q151 c4) ∷
   rw 0 (q155 c4) ∷
   rw⁻ 2 (q151 c4) ∷
   rw 0 (q154 c4) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = eqn (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) (wl0028 (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (Sb0-1-23-4 ∷ CZ34 ∷ []) (CZ34 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ34 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) (wl0027 (lit c4))

-- auto SBOX(0;1;23;4) | CZ34 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ34-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ34-at2332 c4 = derive (Sb0-1-32-4 ∷ CZ24 ∷ []) (CZ24 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw 1 (q146 c4) ∷
   rw⁻ 2 (q156 c4) ∷
   rw 1 (q157 c4) ∷
   rw⁻ 0 (q158 c4) ∷
   rw 1 (q150 c4) ∷
   rw 2 (q112 c4) ∷ []) Eq.refl

private
  q159 : Ws → Eqn
  q159 c4 = eqn (CX24 ∷ []) (K4 ∷ CZ24 ∷ K4⁻ ∷ []) (wl0489 (lit c4))
  q160 : Ws → Eqn
  q160 c4 = eqn (Sb0-1-32-4 ∷ K4 ∷ []) (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4)
  q161 : Ws → Eqn
  q161 c4 = eqn (Sb0-1-32-4 ∷ CZ24 ∷ []) (CZ24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ34-at2332 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (Sb0-1-32-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4)

-- auto SBOX(0;1;23;4) | CX24: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX24 : Ws → ⟪ (Sb0-1-23-4 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX24 c4 = derive (Sb0-1-23-4 ∷ CX24 ∷ []) (CX24 ∷ Sb0-1-23-4 ∷ [])
  (rw 1 (q159 c4) ∷
   rw 0 (q151 c4) ∷
   rw 0 (q160 c4) ∷
   rw 1 (q161 c4) ∷
   rw 2 (q162 c4) ∷
   rw⁻ 3 (q151 c4) ∷
   rw⁻ 0 (q159 c4) ∷ []) Eq.refl

private
  q163 : Ws → Eqn
  q163 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 (lit c4))
  q164 : Ws → Eqn
  q164 c4 = eqn (Sw12 ∷ Bx0-2413 ∷ []) (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4))
  q165 : Ws → Eqn
  q165 c4 = eqn (CS14⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14⁻ ∷ []) (lem-CSd12-beta-at243243 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (Sw12 ∷ Bx0-1423 ∷ []) (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4))
  q167 : Ws → Eqn
  q167 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 (lit c4))

-- CSd12-beta @12243143: 7 steps
lem-CSd12-beta-at12243143 : Ws → ⟪ (CS24⁻ ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at12243143 c4 = derive (CS24⁻ ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CS24⁻ ∷ [])
  (rw⁻ 0 (q108 c4) ∷
   rw⁻ 1 (q163 c4) ∷
   rw 2 (q164 c4) ∷
   rw 1 (q165 c4) ∷
   rw 0 (q166 c4) ∷
   rw⁻ 1 (q167 c4) ∷
   rw 2 (q108 c4) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 (lit c4))
  q169 : Ws → Eqn
  q169 c4 = eqn (Sw23 ∷ Bx0-3412 ∷ []) (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4))
  q170 : Ws → Eqn
  q170 c4 = eqn (CS24⁻ ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CS24⁻ ∷ []) (lem-CSd12-beta-at12243143 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (Sw23 ∷ Bx0-2413 ∷ []) (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4))
  q172 : Ws → Eqn
  q172 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 (lit c4))

-- CSd12-beta @13243142: 7 steps
lem-CSd12-beta-at13243142 : Ws → ⟪ (CS34⁻ ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CS34⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at13243142 c4 = derive (CS34⁻ ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CS34⁻ ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw⁻ 1 (q168 c4) ∷
   rw 2 (q169 c4) ∷
   rw 1 (q170 c4) ∷
   rw 0 (q171 c4) ∷
   rw⁻ 1 (q172 c4) ∷
   rw 2 (q112 c4) ∷ []) Eq.refl

private
  q173 : Ws → Eqn
  q173 c4 = eqn (CS34⁻ ∷ []) (CS34⁻ ∷ []) (wl0490 (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1342 ∷ []) (lem-sym34-at2332 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (Bx0-1342 ∷ []) (Bx0-3142 ∷ []) (lem-sym12-at233442 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (CS34⁻ ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CS34⁻ ∷ []) (lem-CSd12-beta-at13243142 c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (Bx0-3412 ∷ []) (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4)
  q179 : Ws → Eqn
  q179 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4)

-- auto BOX(0;1234) | CSd43: 11 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd43 : Ws → ⟪ (Bx0-1234 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd43 c4 = derive (Bx0-1234 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Bx0-1234 ∷ [])
  (rw 1 (q173 c4) ∷
   rw 0 (q100 c4) ∷
   rw 0 (q174 c4) ∷
   rw 0 (q175 c4) ∷
   rw 0 (q176 c4) ∷
   rw⁻ 0 (q177 c4) ∷
   rw 1 (q178 c4) ∷
   rw 1 (q179 c4) ∷
   rw 1 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 0 (q173 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = eqn (CS14⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS14⁻ ∷ []) (wl0491 (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (CS34⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS34⁻ ∷ []) (wl0492 (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn (Bx0-1234 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43 c4)

-- auto SBOX(0;1;23;4) | CSd43: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd43 : Ws → ⟪ (Sb0-1-23-4 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd43 c4 = derive (Sb0-1-23-4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw 4 (q180 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 1 (q181 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw 0 (q182 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q183 : Ws → Eqn
  q183 c4 = eqn (Sb0-1-23-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS43 c4)

-- auto SBOX(0;1;23;4) | CS43 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS43-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS43-at2332 c4 = derive (Sb0-1-32-4 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw 1 (q146 c4) ∷
   rw⁻ 2 (q147 c4) ∷
   rw 1 (q183 c4) ∷
   rw⁻ 0 (q149 c4) ∷
   rw 1 (q150 c4) ∷
   rw 2 (q112 c4) ∷ []) Eq.refl

private
  q184 : Ws → Eqn
  q184 c4 = eqn (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) (wl0050 (lit c4))
  q185 : Ws → Eqn
  q185 c4 = eqn (Sb0-1-23-4 ∷ CX24 ∷ []) (CX24 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX24 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) (wl0051 (lit c4))

-- auto SBOX(0;1;23;4) | CX24 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX24-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX24-at2332 c4 = derive (Sb0-1-32-4 ∷ CX34 ∷ []) (CX34 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw 1 (q146 c4) ∷
   rw⁻ 2 (q184 c4) ∷
   rw 1 (q185 c4) ∷
   rw⁻ 0 (q186 c4) ∷
   rw 1 (q150 c4) ∷
   rw 2 (q112 c4) ∷ []) Eq.refl

private
  q187 : Ws → Eqn
  q187 c4 = eqn (Sb0-1-23-4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd43 c4)

-- auto SBOX(0;1;23;4) | CSd43 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd43-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd43-at2332 c4 = derive (Sb0-1-32-4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw 1 (q146 c4) ∷
   rw⁻ 2 (q172 c4) ∷
   rw 1 (q187 c4) ∷
   rw⁻ 0 (q168 c4) ∷
   rw 1 (q150 c4) ∷
   rw 2 (q112 c4) ∷ []) Eq.refl

private
  q188 : Ws → Eqn
  q188 c4 = eqn (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0493 (lit c4))
  q189 : Ws → Eqn
  q189 c4 = eqn (Sb0-1-32-4 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS43-at2332 c4)
  q190 : Ws → Eqn
  q190 c4 = eqn (Sb0-1-32-4 ∷ CX34 ∷ []) (CX34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX24-at2332 c4)
  q191 : Ws → Eqn
  q191 c4 = eqn (Sb0-1-32-4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd43-at2332 c4)
  q192 : Ws → Eqn
  q192 c4 = eqn (Sb0-1-32-4 ∷ CS23 ∷ []) (CS23 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 c4)

-- auto SBOX(0;1;23;4) | CCZ234: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234 : Ws → ⟪ (Sb0-1-23-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234 c4 = derive (Sb0-1-23-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-23-4 ∷ [])
  (rw 1 (q188 c4) ∷
   rw 0 (q151 c4) ∷
   rw 0 (q189 c4) ∷
   rw 1 (q190 c4) ∷
   rw 2 (q191 c4) ∷
   rw 3 (q190 c4) ∷
   rw 4 (q192 c4) ∷
   rw⁻ 5 (q151 c4) ∷
   rw⁻ 0 (q188 c4) ∷ []) Eq.refl

private
  q193 : Ws → Eqn
  q193 c4 = eqn (Bx⁻0-1234 ∷ []) (Bx0-1234 ∷ []) (lem-BOXd-BOX c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (CS34 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CS34 ∷ []) (lem-CS12-beta-at13243142 c4)

-- auto BOXd(0;1234) | CS34: 11 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS34 : Ws → ⟪ (Bx⁻0-1234 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS34 c4 = derive (Bx⁻0-1234 ∷ CS34 ∷ []) (CS34 ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q193 c4) ∷
   rw 0 (q100 c4) ∷
   rw 0 (q174 c4) ∷
   rw 0 (q175 c4) ∷
   rw 0 (q176 c4) ∷
   rw⁻ 0 (q194 c4) ∷
   rw 1 (q178 c4) ∷
   rw 1 (q179 c4) ∷
   rw 1 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw⁻ 1 (q193 c4) ∷ []) Eq.refl

private
  q195 : Ws → Eqn
  q195 c4 = eqn (Bx⁻0-1234 ∷ CS34 ∷ []) (CS34 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS34 c4)
  q196 : Ws → Eqn
  q196 c4 = eqn (CS34 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS34 ∷ []) (wl0494 (lit c4))
  q197 : Ws → Eqn
  q197 c4 = eqn (CS14 ∷ CS34 ∷ []) (CS34 ∷ CS14 ∷ []) (wl0495 (lit c4))

-- auto SBOXd(0;1;23;4) | CS34: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS34 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS34 c4 = derive (Sb⁻0-1-23-4 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 4 (q195 c4) ∷
   re 2 1 (CS14⁻ ∷ []) ∷
   rw⁻ 1 (q196 c4) ∷
   re 3 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 0 1 (CS14 ∷ []) ∷
   rw 0 (q197 c4) ∷
   re 1 1 (Sb0-1-4-3 ∷ []) ∷
   re 1 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q198 : Ws → Eqn
  q198 c4 = eqn (Sw23 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4))
  q199 : Ws → Eqn
  q199 c4 = eqn (Sb⁻0-1-23-4 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS34 c4)
  q200 : Ws → Eqn
  q200 c4 = eqn (Sw23 ∷ Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | CS34 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS34-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS34-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CS24 ∷ []) (CS24 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw 1 (q198 c4) ∷
   rw⁻ 2 (q147 c4) ∷
   rw 1 (q199 c4) ∷
   rw⁻ 0 (q149 c4) ∷
   rw 1 (q200 c4) ∷
   rw 2 (q112 c4) ∷ []) Eq.refl

private
  q201 : Ws → Eqn
  q201 c4 = eqn (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0336 (lit c4))
  q202 : Ws → Eqn
  q202 c4 = eqn (Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4)
  q203 : Ws → Eqn
  q203 c4 = eqn (Sb⁻0-1-32-4 ∷ CS24 ∷ []) (CS24 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS34-at2332 c4)
  q204 : Ws → Eqn
  q204 c4 = eqn (Bx⁻0-1324 ∷ []) (Bx0-1324 ∷ []) (lem-BOXd-BOX-at2332 c4)
  q205 : Ws → Eqn
  q205 c4 = eqn (Bx0-1324 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4)
  q206 : Ws → Eqn
  q206 c4 = eqn (CCZ024 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ024 ∷ []) (wp0173 c4)
  q207 : Ws → Eqn
  q207 c4 = eqn (CX32 ∷ Toff013 ∷ []) (Toff013 ∷ CX32 ∷ []) (wl0496 (lit c4))
  q208 : Ws → Eqn
  q208 c4 = eqn (Toff013 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4))
  q209 : Ws → Eqn
  q209 c4 = eqn (CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ []) (Toff423 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (wl0497 (lit c4))
  q210 : Ws → Eqn
  q210 c4 = eqn (CS14⁻ ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14⁻ ∷ []) (wl0498 (lit c4))
  q211 : Ws → Eqn
  q211 c4 = eqn (CS14 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14 ∷ []) (wl0499 (lit c4))
  q212 : Ws → Eqn
  q212 c4 = eqn (Sb⁻0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at2332 c4)

-- auto SBOXd(0;1;23;4) | CCZ432: 28 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ432 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ432 c4 = derive (Sb⁻0-1-23-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb⁻0-1-23-4 ∷ [])
  (rw 1 (q201 c4) ∷
   rw 0 (q202 c4) ∷
   rw 0 (q203 c4) ∷
   re 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) ∷
   rw 5 (q204 c4) ∷
   rw 5 (q205 c4) ∷
   rw 8 (q206 c4) ∷
   rw⁻ 7 (q207 c4) ∷
   rw 8 (q208 c4) ∷
   rw⁻ 9 (q207 c4) ∷
   rw 6 (q206 c4) ∷
   rw⁻ 5 (q207 c4) ∷
   rw 6 (q208 c4) ∷
   rw⁻ 7 (q207 c4) ∷
   rw⁻ 8 (q205 c4) ∷
   rw⁻ 8 (q204 c4) ∷
   rw⁻ 4 (q209 c4) ∷
   re 3 1 (CS14⁻ ∷ []) ∷
   rw 3 (q210 c4) ∷
   re 6 1 (Sb⁻0-1-4-2 ∷ []) ∷
   rw⁻ 2 (q209 c4) ∷
   re 1 1 (CS14 ∷ []) ∷
   rw 1 (q211 c4) ∷
   re 4 1 (Sb0-1-4-2 ∷ []) ∷
   re 4 5 (Sb⁻0-1-32-4 ∷ []) ∷
   rw 4 (q212 c4) ∷
   rw⁻ 5 (q202 c4) ∷
   rw⁻ 0 (q201 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = eqn (CCZ234 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ234 ∷ []) (wl0086 (lit c4))
  q214 : Ws → Eqn
  q214 c4 = eqn (Sb⁻0-1-23-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ432 c4)

-- auto SBOXd(0;1;23;4) | CCZ432 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ432-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ432-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw 1 (q198 c4) ∷
   rw⁻ 2 (q213 c4) ∷
   rw 1 (q214 c4) ∷
   rw⁻ 0 (q213 c4) ∷
   rw 1 (q200 c4) ∷
   rw 2 (q112 c4) ∷ []) Eq.refl

private
  q215 : Ws → Eqn
  q215 c4 = eqn (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) (wl0335 (lit c4))
  q216 : Ws → Eqn
  q216 c4 = eqn (Sb⁻0-1-32-4 ∷ K4 ∷ []) (K4 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at2332 c4)
  q217 : Ws → Eqn
  q217 c4 = eqn (Sb⁻0-1-32-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ432-at2332 c4)
  q218 : Ws → Eqn
  q218 c4 = eqn (Sb⁻0-1-32-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at2332 c4)

-- auto SBOXd(0;1;23;4) | TOFF423: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423 c4 = derive (Sb⁻0-1-23-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb⁻0-1-23-4 ∷ [])
  (rw⁻ 1 (q215 c4) ∷
   rw 0 (q202 c4) ∷
   rw 0 (q216 c4) ∷
   rw 1 (q217 c4) ∷
   rw 2 (q218 c4) ∷
   rw⁻ 3 (q202 c4) ∷
   rw 0 (q215 c4) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = eqn (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4)

-- auto BOXd(0;1234) | CS02: 3 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS02 : Ws → ⟪ (Bx⁻0-1234 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS02 c4 = derive (Bx⁻0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q193 c4) ∷
   rw⁻ 0 (q219 c4) ∷
   rw⁻ 1 (q193 c4) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = eqn (Bx⁻0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS02 c4)
  q221 : Ws → Eqn
  q221 c4 = eqn (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ []) (wp0098 c4)
  q222 : Ws → Eqn
  q222 c4 = eqn (CS02 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS02 ∷ []) (wp0099 c4)
  q223 : Ws → Eqn
  q223 c4 = eqn (CS02 ∷ CS14 ∷ []) (CS14 ∷ CS02 ∷ []) (wp0100 c4)

-- auto SBOXd(0;1;23;4) | CS02: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02 c4 = derive (Sb⁻0-1-23-4 ∷ CS02 ∷ []) (CS02 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 4 (q220 c4) ∷
   rw⁻ 3 (q221 c4) ∷
   re 2 1 (CS14⁻ ∷ []) ∷
   rw⁻ 2 (q222 c4) ∷
   re 3 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q221 c4) ∷
   re 0 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q223 c4) ∷
   re 1 1 (Sb0-1-4-3 ∷ []) ∷
   re 1 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = eqn (CS03 ∷ []) (CS03 ∷ []) (wl0342 (lit c4))
  q225 : Ws → Eqn
  q225 c4 = eqn (CS03 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS03 ∷ []) (lem-CS20-beta-c-at2332 c4)

-- auto BOXd(0;1234) | CS30: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS30 : Ws → ⟪ (Bx⁻0-1234 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS30 c4 = derive (Bx⁻0-1234 ∷ CS03 ∷ []) (CS03 ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q193 c4) ∷
   rw 1 (q224 c4) ∷
   rw 0 (q100 c4) ∷
   rw⁻ 0 (q225 c4) ∷
   rw 1 (q98 c4) ∷
   rw 0 (q224 c4) ∷
   rw⁻ 1 (q193 c4) ∷ []) Eq.refl

private
  q226 : Ws → Eqn
  q226 c4 = eqn (Bx⁻0-1234 ∷ CS03 ∷ []) (CS03 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS30 c4)
  q227 : Ws → Eqn
  q227 c4 = eqn (CS03 ∷ Toff423 ∷ []) (Toff423 ∷ CS03 ∷ []) (wp0116 c4)
  q228 : Ws → Eqn
  q228 c4 = eqn (CS03 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03 ∷ []) (wp0115 c4)
  q229 : Ws → Eqn
  q229 c4 = eqn (CS03 ∷ CS14 ∷ []) (CS14 ∷ CS03 ∷ []) (wp0117 c4)

-- auto SBOXd(0;1;23;4) | CS30: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS30 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS30 c4 = derive (Sb⁻0-1-23-4 ∷ CS03 ∷ []) (CS03 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 4 (q226 c4) ∷
   rw⁻ 3 (q227 c4) ∷
   re 2 1 (CS14⁻ ∷ []) ∷
   rw⁻ 2 (q228 c4) ∷
   re 3 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q227 c4) ∷
   re 0 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q229 c4) ∷
   re 1 1 (Sb0-1-4-3 ∷ []) ∷
   re 1 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q230 : Ws → Eqn
  q230 c4 = eqn (Sw12 ∷ Bx0-3214 ∷ []) (Bx0-3124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3214⟩ (lit c4))
  q231 : Ws → Eqn
  q231 c4 = eqn (Bx0-3124 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at132132 c4)
  q232 : Ws → Eqn
  q232 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 (lit c4))
  q233 : Ws → Eqn
  q233 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4))

-- beta-T @1331: 8 steps
lem-beta-T-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at1331 c4 = derive (Bx0-3214 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q108 c4) ∷
   rw 1 (q230 c4) ∷
   rw 1 (q231 c4) ∷
   rw 0 (q232 c4) ∷
   rw 1 (q233 c4) ∷
   rw 2 (q232 c4) ∷
   rw 3 (q233 c4) ∷
   rw 4 (q108 c4) ∷ []) Eq.refl

private
  q234 : Ws → Eqn
  q234 c4 = eqn (Bx0-3124 ∷ []) (Bx0-3214 ∷ []) (lem-sym23-at132132 c4)

-- sym23 @1331: 5 steps
lem-sym23-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym23-at1331 c4 = derive (Bx0-3214 ∷ []) (Bx0-3124 ∷ [])
  (rw⁻ 0 (q108 c4) ∷
   rw 1 (q230 c4) ∷
   rw 1 (q234 c4) ∷
   rw 0 (q230 c4) ∷
   rw 1 (q108 c4) ∷ []) Eq.refl

private
  q235 : Ws → Eqn
  q235 c4 = eqn (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4))
  q236 : Ws → Eqn
  q236 c4 = eqn (Sb⁻0-1-23-4 ∷ CS03 ∷ []) (CS03 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS30 c4)
  q237 : Ws → Eqn
  q237 c4 = eqn (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4))

-- auto SBOXd(0;1;23;4) | CS30 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS30-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS30-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CS02 ∷ []) (CS02 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw 1 (q198 c4) ∷
   rw 2 (q235 c4) ∷
   rw 1 (q236 c4) ∷
   rw 0 (q237 c4) ∷
   rw 1 (q200 c4) ∷
   rw 2 (q112 c4) ∷ []) Eq.refl

private
  q238 : Ws → Eqn
  q238 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4))
  q239 : Ws → Eqn
  q239 c4 = eqn (Sb⁻0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332 c4)
  q240 : Ws → Eqn
  q240 c4 = eqn (Bx0-3214 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at1331 c4)
  q241 : Ws → Eqn
  q241 c4 = eqn (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4))
  q242 : Ws → Eqn
  q242 c4 = eqn (CCZ014 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ014 ∷ []) (wp0174 c4)
  q243 : Ws → Eqn
  q243 c4 = eqn (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff023 ∷ []) (Toff023 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (wl0500 (lit c4))
  q244 : Ws → Eqn
  q244 c4 = eqn (Bx0-3214 ∷ []) (Bx0-3124 ∷ []) (lem-sym23-at1331 c4)
  q245 : Ws → Eqn
  q245 c4 = eqn (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) (Toff423 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (wp0119 c4)
  q246 : Ws → Eqn
  q246 c4 = eqn (CS14⁻ ∷ CX23 ∷ []) (CX23 ∷ CS14⁻ ∷ []) (wl0354 (lit c4))
  q247 : Ws → Eqn
  q247 c4 = eqn (CS03⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03⁻ ∷ []) (wp0118 c4)
  q248 : Ws → Eqn
  q248 c4 = eqn (CS14 ∷ CX23 ∷ []) (CX23 ∷ CS14 ∷ []) (wl0355 (lit c4))
  q249 : Ws → Eqn
  q249 c4 = eqn (CS03⁻ ∷ CS14 ∷ []) (CS14 ∷ CS03⁻ ∷ []) (wp0120 c4)
  q250 : Ws → Eqn
  q250 c4 = eqn (Sb⁻0-1-32-4 ∷ CS02 ∷ []) (CS02 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS30-at2332 c4)

-- auto SBOXd(0;1;23;4) | CCZ023: 44 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023 c4 = derive (Sb⁻0-1-23-4 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb⁻0-1-23-4 ∷ [])
  (rw 1 (q238 c4) ∷
   rw 0 (q202 c4) ∷
   rw 0 (q239 c4) ∷
   re 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) ∷
   rw 5 (q204 c4) ∷
   rw 5 (q101 c4) ∷
   rw 5 (q234 c4) ∷
   rw 5 (q240 c4) ∷
   rw 8 (q241 c4) ∷
   rw 9 (q242 c4) ∷
   rw 10 (q241 c4) ∷
   rw⁻ 7 (q243 c4) ∷
   rw 6 (q241 c4) ∷
   rw 7 (q242 c4) ∷
   rw 8 (q241 c4) ∷
   rw⁻ 5 (q243 c4) ∷
   rw⁻ 8 (q240 c4) ∷
   rw 8 (q244 c4) ∷
   rw 8 (q97 c4) ∷
   rw⁻ 8 (q204 c4) ∷
   rw⁻ 4 (q245 c4) ∷
   re 3 1 (CS14⁻ ∷ []) ∷
   rw 3 (q246 c4) ∷
   re 4 1 (Sb⁻0-1-4-2 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q247 c4) ∷
   re 5 1 (Sb⁻0-1-4-2 ∷ []) ∷
   re 5 1 (CS14⁻ ∷ []) ∷
   rw 5 (q246 c4) ∷
   re 6 1 (Sb⁻0-1-4-2 ∷ []) ∷
   rw⁻ 2 (q245 c4) ∷
   re 1 1 (CS14 ∷ []) ∷
   rw 1 (q248 c4) ∷
   re 2 1 (Sb0-1-4-2 ∷ []) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 2 (q249 c4) ∷
   re 3 1 (Sb0-1-4-2 ∷ []) ∷
   re 3 1 (CS14 ∷ []) ∷
   rw 3 (q248 c4) ∷
   re 4 1 (Sb0-1-4-2 ∷ []) ∷
   re 4 5 (Sb⁻0-1-32-4 ∷ []) ∷
   rw 4 (q250 c4) ∷
   rw⁻ 5 (q202 c4) ∷
   rw⁻ 0 (q238 c4) ∷ []) Eq.refl

private
  q251 : Ws → Eqn
  q251 c4 = eqn (Sw23 ∷ Bx3-0412 ∷ []) (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4))
  q252 : Ws → Eqn
  q252 c4 = eqn (Bx2-0413 ∷ []) (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4)
  q253 : Ws → Eqn
  q253 c4 = eqn (Sw23 ∷ Bx2-4013 ∷ []) (Bx3-4012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4013⟩ (lit c4))

-- sym12 @0310243142: 5 steps
lem-sym12-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym12-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-4012 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw 1 (q251 c4) ∷
   rw 1 (q252 c4) ∷
   rw 0 (q253 c4) ∷
   rw 1 (q112 c4) ∷ []) Eq.refl
