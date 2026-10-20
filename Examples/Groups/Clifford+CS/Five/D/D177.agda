{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D177 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0037 ; wl0044 ; wl0047 ; wl0057 ; wl0058 ; wl0085 ; wl0091 ; wl0096 ; wl0097 ; wl0099 ; wl0113 ; wl0119 ; wl0120 ; wl0190 ; wl0260 ; wl0283 ; wl0353 ; wl0548 ; wl0560 ; wl0724 ; wl0725 ; wl0726 ; wl0727 ; wl0728 ; wl0743 ; wl0744 ; wl0745 ; wl0746 ; wl0747 ; wl0748 ; wl0749 ; wl0750 ; wl0751 ; wl0752 ; wl0753 ; wl0754 ; wl0755 ; wl0756 ; wl0757 ; wl0758 ; wl0759 ; wl0760 ; wl0761 ; wl0762 ; wl0763 ; wl0764 ; wl0765 ; wl0766 ; wl0767 ; wl0768 ; wp0348 ; wp0349 ; wp0365 ; wp0366 ; wp0387 ; wp0388 ; wp0389 ; wp0390 ; wp0391 ; wp0392 ; wp0393 ; wp0394 ; wp0395 ; wp0396 ; wp0397 ; wp0398 ; wp0399 ; wp0400 ; wp0401 ; wp0402 ; wp0403 ; wp0404 ; wp0405 ; wp0406)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-T-beta ; lem-beta-T-at243243 ; lem-c124-beta-at0310213442 ; lem-sym12 ; lem-sym12-at1221 ; lem-sym23 ; lem-sym34-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at233442 ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym23-at2332 ; lem-sym34-at12213443 ; lem-sym34-at2332 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F0-at132132 ; lem-X1-beta-at0214203143 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 ; lem-sym12-at13213442)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 ; lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-auto-CCZ012-∣-CCZ342-at04103143)
open import Examples.Groups.Clifford+CS.Five.D.D164 using (lem-T-beta-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D170 using (lem-auto-CCZ012-∣-TOFF342)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at3443 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D175 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D176 using (lem-F4-CS01ᵖ0∣CS23ᵖ1-part0)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-TOFF201)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-TOFF403 ; lem-nat-2-BOX⟨3·4012⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF413 ; lem-nat-2-BOX⟨2·4013⟩ ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-TOFF401 ; lem-nat-2-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-2-CS12 ; lem-nat-2-CS13)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-CS02 ; lem-nat-2-SBOX⟨1·0·2·3⟩ ; lem-nat-2-SBOX⟨1·0·43·2⟩ ; lem-nat-2-SBOXd⟨1·0·2·3⟩ ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·3142⟩ ; lem-nat-0-BOX⟨1·3042⟩ ; lem-nat-1-BOX⟨1·3042⟩ ; lem-nat-1-BOX⟨2·3041⟩ ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨3·0142⟩ ; lem-nat-1-BOX⟨3·0241⟩ ; lem-nat-2-SBOX⟨1·0·3·2⟩ ; lem-nat-2-SBOX⟨1·0·42·3⟩ ; lem-nat-2-SBOXd⟨1·0·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨4·0123⟩ ; lem-nat-0-BOX⟨4·1023⟩ ; lem-nat-1-BOX⟨4·0123⟩ ; lem-nat-1-BOX⟨4·0213⟩ ; lem-nat-1-BOX⟨4·1032⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨3·0142⟩ ; lem-nat-0-BOX⟨3·1042⟩ ; lem-nat-0-SBOX⟨0·1·43·2⟩ ; lem-nat-1-BOX⟨3·1042⟩ ; lem-nat-1-BOX⟨3·2041⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-0-SBOX⟨2·0·43·1⟩ ; lem-nat-1-BOX⟨4·2031⟩ ; lem-nat-1-SBOX⟨2·1·43·0⟩ ; lem-nat-2-BOX⟨2·3041⟩ ; lem-nat-2-BOX⟨3·2041⟩ ; lem-nat-2-BOX⟨4·1023⟩ ; lem-nat-2-BOX⟨4·1032⟩ ; lem-nat-3-BOX⟨3·2041⟩ ; lem-nat-3-BOX⟨4·2031⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (wp0389 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (wl0747 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (wp0390 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (wl0748 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (K1 ∷ X4 ∷ []) (X4 ∷ K1 ∷ []) (c₂ (K ↑) (X ↑ ↑))
  q10 : Ws → Eqn
  q10 c4 = eqn (K1 ∷ Toff203 ∷ []) (Toff203 ∷ K1 ∷ []) (wl0724 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ []) (wp0391 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (K1⁻ ∷ X4 ∷ []) (X4 ∷ K1⁻ ∷ []) (c₂ ((K • iI) ↑) (X ↑ ↑))
  q13 : Ws → Eqn
  q13 c4 = eqn (K1⁻ ∷ Toff203 ∷ []) (Toff203 ∷ K1⁻ ∷ []) (wl0746 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ []) (wl0749 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (wp0392 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (wp0393 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ []) (wl0750 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (wl0751 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ []) (wl0752 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ []) (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS13 ∷ Toff203 ∷ []) (Toff203 ∷ CS13 ∷ []) (wl0753 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (K1⁻ ∷ K1 ∷ []) [] (wl0260 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ []) (wl0743 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ []) (wl0754 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (Sb2-0-41-3 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (wp0387 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (wl0744 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (wp0388 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (wl0745 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (X4 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ []) (wl0725 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (wp0365 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (wp0366 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) (wl0726 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) (wl0727 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ X4 ∷ CS14 ∷ []) (wl0728 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ []) (wl0755 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Sb2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 c4)

-- F4 CS01^0|CS23^1 part1: 392 steps
lem-F4-CS01ᵖ0∣CS23ᵖ1-part1 : Ws → ⟪ (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣CS23ᵖ1-part1 c4 = derive (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   re 17 1 (CS03⁻ ∷ []) ∷
   rw⁻ 16 (q2 c4) ∷
   re 29 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 13 (q3 c4) ∷
   re 11 1 (CS03 ∷ []) ∷
   rw⁻ 10 (q4 c4) ∷
   re 23 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 7 (q3 c4) ∷
   rw 5 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 13 (q8 c4) ∷
   rw⁻ 12 (q9 c4) ∷
   rw⁻ 11 (q10 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw⁻ 13 (q13 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw⁻ 15 (q9 c4) ∷
   rw⁻ 14 (q10 c4) ∷
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
   rw⁻ 16 (q13 c4) ∷
   rw⁻ 15 (q12 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 17 (q10 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 20 (q12 c4) ∷
   rw⁻ 19 (q13 c4) ∷
   rw⁻ 18 (q12 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 20 (q10 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 22 (q22 c4) ∷
   rw⁻ 21 (q23 c4) ∷
   rw⁻ 20 (q22 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 22 (q13 c4) ∷
   rw⁻ 21 (q12 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw⁻ 8 (q10 c4) ∷
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
   rw⁻ 10 (q13 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 12 (q9 c4) ∷
   rw⁻ 11 (q10 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw⁻ 13 (q13 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw⁻ 15 (q9 c4) ∷
   rw⁻ 14 (q10 c4) ∷
   rw⁻ 13 (q9 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw⁻ 15 (q23 c4) ∷
   rw⁻ 14 (q22 c4) ∷
   rw⁻ 17 (q12 c4) ∷
   rw⁻ 16 (q13 c4) ∷
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
   re 17 5 (Sb2-0-41-3 ∷ []) ∷
   rw 3 (q26 c4) ∷
   rw 4 (q26 c4) ∷
   rw 5 (q26 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   rw 1 (q28 c4) ∷
   re 5 1 (CS12 ∷ []) ∷
   rw⁻ 4 (q29 c4) ∷
   re 4 1 (Sb0-2-1-3 ∷ []) ∷
   rw 3 (q30 c4) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q29 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 7 (q27 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 11 (q26 c4) ∷
   rw⁻ 14 (q26 c4) ∷
   rw⁻ 17 (q26 c4) ∷
   re 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   re 16 1 (CS03⁻ ∷ []) ∷
   rw⁻ 15 (q31 c4) ∷
   re 19 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 12 (q32 c4) ∷
   re 10 1 (CS03 ∷ []) ∷
   rw⁻ 9 (q33 c4) ∷
   re 13 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 6 (q32 c4) ∷
   rw 4 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 12 (q34 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw⁻ 10 (q10 c4) ∷
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
   rw⁻ 12 (q13 c4) ∷
   rw⁻ 11 (q12 c4) ∷
   rw⁻ 6 (q34 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw⁻ 4 (q10 c4) ∷
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
   rw⁻ 6 (q13 c4) ∷
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
   re 7 5 (Sb2-0-41-3 ∷ []) ∷
   re 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   re 19 1 (CS03⁻ ∷ []) ∷
   rw⁻ 18 (q2 c4) ∷
   re 31 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q3 c4) ∷
   re 13 1 (CS03 ∷ []) ∷
   rw⁻ 12 (q4 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 9 (q3 c4) ∷
   rw 7 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   rw⁻ 13 (q10 c4) ∷
   rw⁻ 12 (q9 c4) ∷
   rw⁻ 13 (q11 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw⁻ 15 (q13 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw⁻ 16 (q10 c4) ∷
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
   rw⁻ 18 (q13 c4) ∷
   rw⁻ 17 (q12 c4) ∷
   rw⁻ 20 (q9 c4) ∷
   rw⁻ 19 (q10 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   rw⁻ 22 (q12 c4) ∷
   rw⁻ 21 (q13 c4) ∷
   rw⁻ 20 (q12 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw⁻ 22 (q10 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 24 (q22 c4) ∷
   rw⁻ 23 (q23 c4) ∷
   rw⁻ 22 (q22 c4) ∷
   rw⁻ 25 (q12 c4) ∷
   rw⁻ 24 (q13 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw⁻ 10 (q10 c4) ∷
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
   rw⁻ 12 (q13 c4) ∷
   rw⁻ 11 (q12 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   rw⁻ 13 (q10 c4) ∷
   rw⁻ 12 (q9 c4) ∷
   rw⁻ 13 (q11 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw⁻ 15 (q13 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw⁻ 16 (q10 c4) ∷
   rw⁻ 15 (q9 c4) ∷
   rw⁻ 18 (q22 c4) ∷
   rw⁻ 17 (q23 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw⁻ 19 (q12 c4) ∷
   rw⁻ 18 (q13 c4) ∷
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
   re 19 5 (Sb2-0-41-3 ∷ []) ∷
   rw 5 (q26 c4) ∷
   rw 6 (q26 c4) ∷
   rw 7 (q26 c4) ∷
   rw 8 (q26 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   rw 3 (q28 c4) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 6 (q41 c4) ∷
   re 6 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw 5 (q42 c4) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q41 c4) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (lem-F4-CS01ᵖ0∣CS23ᵖ1-part0 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS23ᵖ1-part1 c4)

-- F4 CS01^0|CS23^1: 2 steps
lem-F4-CS01ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣CS23ᵖ1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q43 c4) ∷
   rw 0 (q44 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CS01 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at3443 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (Sw12 ∷ Sb2-0-41-3 ∷ []) (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4))

-- auto CS01 | SBOX(2;0;31;4) @12213443: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 : Ws → ⟪ (CS02 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 c4 = derive (CS02 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS02 ∷ [])
  (rw⁻ 0 (q45 c4) ∷
   rw 1 (q46 c4) ∷
   rw 2 (q47 c4) ∷
   rw 1 (q48 c4) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q50 c4) ∷
   rw 2 (q45 c4) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Sw12 ∷ Bx3-0241 ∷ []) (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ012 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Sw12 ∷ Bx3-0142 ∷ []) (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ (lit c4))

-- c124-beta @03103441: 7 steps
lem-c124-beta-at03103441 : Ws → ⟪ (CCZ012 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at03103441 c4 = derive (CCZ012 ∷ Bx3-0241 ∷ []) (Bx3-0241 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q45 c4) ∷
   rw⁻ 1 (q51 c4) ∷
   rw 2 (q52 c4) ∷
   rw 1 (q53 c4) ∷
   rw 0 (q54 c4) ∷
   rw⁻ 1 (q51 c4) ∷
   rw 2 (q45 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q57 : Ws → Eqn
  q57 c4 = eqn (Sw23 ∷ Bx3-4012 ∷ []) (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (X4 ∷ Bx2-4013 ∷ X4 ∷ []) (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (Sw23 ∷ Bx2-4013 ∷ []) (Bx3-4012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4013⟩ (lit c4))

-- X1-beta @0314203142: 8 steps
lem-X1-beta-at0314203142 : Ws → ⟪ (X4 ∷ Bx3-4012 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx3-4012 ∷ []) ⟫ʷ
lem-X1-beta-at0314203142 c4 = derive (X4 ∷ Bx3-4012 ∷ X4 ∷ []) (CCZ012 ∷ Bx3-4012 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw 3 (q56 c4) ∷
   rw 1 (q58 c4) ∷
   rw 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q55 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = eqn (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q63 : Ws → Eqn
  q63 c4 = eqn (Sb0-1-42-3 ∷ K0 ∷ []) (K0 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Sw23 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | K0 @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2442 c4 = derive (Sb0-1-43-2 ∷ K0 ∷ []) (K0 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q61 c4) ∷
   rw⁻ 2 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw⁻ 0 (q62 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q55 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0057 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (Sb0-1-42-3 ∷ K3 ∷ []) (K3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0058 (lit c4))

-- auto SBOX(0;1;23;4) | K4 @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2442 c4 = derive (Sb0-1-43-2 ∷ K2 ∷ []) (K2 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q61 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw 1 (q66 c4) ∷
   rw⁻ 0 (q67 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q55 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (Bx0-3142 ∷ []) (Bx0-1342 ∷ []) (lem-sym12-at13213442 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1324 ∷ []) (lem-sym34-at233442 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1234 ∷ []) (lem-sym23-at2332 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ []) (lem-T-beta c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1324 ∷ []) (lem-sym23 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1342 ∷ []) (lem-sym34-at2332 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (Bx0-1342 ∷ []) (Bx0-3142 ∷ []) (lem-sym12-at233442 c4)

-- auto TOFF012 | BOX(0;3142): 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩ : Ws → ⟪ (Toff012 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩ c4 = derive (Toff012 ∷ Bx0-3142 ∷ []) (Bx0-3142 ∷ Toff012 ∷ [])
  (rw 1 (q68 c4) ∷
   rw 1 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   rw 0 (q71 c4) ∷
   rw 0 (q72 c4) ∷
   rw 0 (q73 c4) ∷
   rw 0 (q74 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) (wl0113 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at04103143 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4))

-- auto CCZ012 | CCZ342 @0410233142: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0410233142 : Ws → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0410233142 c4 = derive (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q75 c4) ∷
   rw⁻ 2 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   rw⁻ 0 (q76 c4) ∷
   rw 1 (q78 c4) ∷
   rw 2 (q55 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) (wl0097 (lit c4))
  q81 : Ws → Eqn
  q81 c4 = eqn (Sw01 ∷ Bx1-3042 ∷ []) (Bx0-3142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3042⟩ (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (Toff012 ∷ Bx0-3142 ∷ []) (Bx0-3142 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩ c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (Sw01 ∷ Bx0-3142 ∷ []) (Bx1-3042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3142⟩ (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4))

-- auto TOFF012 | BOX(0;3142) @0110: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0110 : Ws → ⟪ (Toff102 ∷ Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0110 c4 = derive (Toff102 ∷ Bx1-3042 ∷ []) (Bx1-3042 ∷ Toff102 ∷ [])
  (rw⁻ 0 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q79 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) (wl0044 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (Sw12 ∷ Bx2-3041 ∷ []) (Bx1-3042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3041⟩ (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (Toff102 ∷ Bx1-3042 ∷ []) (Bx1-3042 ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0110 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (Sw12 ∷ Bx1-3042 ∷ []) (Bx2-3041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3042⟩ (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4))

-- auto TOFF012 | BOX(0;3142) @021021: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at021021 : Ws → ⟪ (Toff201 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at021021 c4 = derive (Toff201 ∷ Bx2-3041 ∷ []) (Bx2-3041 ∷ Toff201 ∷ [])
  (rw⁻ 0 (q45 c4) ∷
   rw 1 (q85 c4) ∷
   rw 2 (q86 c4) ∷
   rw 1 (q87 c4) ∷
   rw 0 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 2 (q45 c4) ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = eqn (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (Sw23 ∷ Bx3-2041 ∷ []) (Bx2-3041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·2041⟩ (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (Toff201 ∷ Bx2-3041 ∷ []) (Bx2-3041 ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at021021 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (Sw23 ∷ Bx2-3041 ∷ []) (Bx3-2041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·3041⟩ (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4))

-- auto TOFF012 | BOX(0;3142) @03102132: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at03102132 : Ws → ⟪ (Toff301 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at03102132 c4 = derive (Toff301 ∷ Bx3-2041 ∷ []) (Bx3-2041 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   rw 0 (q93 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q55 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw34 ∷ Toff401 ∷ []) (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (Sw34 ∷ Bx4-2031 ∷ []) (Bx3-2041 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·2031⟩ (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Toff301 ∷ Bx3-2041 ∷ []) (Bx3-2041 ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at03102132 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (Sw34 ∷ Bx3-2041 ∷ []) (Bx4-2031 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·2041⟩ (lit c4))
  q100 : Ws → Eqn
  q100 c4 = eqn (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 (lit c4))

-- auto TOFF012 | BOX(0;3142) @0410213243: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410213243 : Ws → ⟪ (Toff401 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ Toff401 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410213243 c4 = derive (Toff401 ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ Toff401 ∷ [])
  (rw⁻ 0 (q95 c4) ∷
   rw 1 (q96 c4) ∷
   rw 2 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q95 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (Sw12 ∷ Bx4-1032 ∷ []) (Bx4-2031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·1032⟩ (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (Toff401 ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ Toff401 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410213243 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Sw12 ∷ Bx4-2031 ∷ []) (Bx4-1032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2031⟩ (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 (lit c4))

-- auto TOFF012 | BOX(0;3142) @04103143: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04103143 : Ws → ⟪ (Toff402 ∷ Bx4-1032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ Toff402 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04103143 c4 = derive (Toff402 ∷ Bx4-1032 ∷ []) (Bx4-1032 ∷ Toff402 ∷ [])
  (rw⁻ 0 (q45 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q102 c4) ∷
   rw 1 (q103 c4) ∷
   rw 0 (q104 c4) ∷
   rw 1 (q105 c4) ∷
   rw 2 (q45 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (Sw23 ∷ Bx4-1023 ∷ []) (Bx4-1032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1023⟩ (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (Toff402 ∷ Bx4-1032 ∷ []) (Bx4-1032 ∷ Toff402 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04103143 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (Sw23 ∷ Bx4-1032 ∷ []) (Bx4-1023 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1032⟩ (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (Sw23 ∷ Toff402 ∷ []) (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 (lit c4))

-- auto TOFF012 | BOX(0;3142) @0410233142: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410233142 : Ws → ⟪ (Toff403 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Toff403 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410233142 c4 = derive (Toff403 ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ Toff403 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q106 c4) ∷
   rw 2 (q107 c4) ∷
   rw 1 (q108 c4) ∷
   rw 0 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw 2 (q55 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = eqn (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (Sw01 ∷ Bx4-0123 ∷ []) (Bx4-1023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0123⟩ (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (Toff403 ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ Toff403 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410233142 c4)
  q114 : Ws → Eqn
  q114 c4 = eqn (Sw01 ∷ Bx4-1023 ∷ []) (Bx4-0123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1023⟩ (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 (lit c4))

-- auto TOFF012 | BOX(0;3142) @04233042: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04233042 : Ws → ⟪ (Toff413 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Toff413 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04233042 c4 = derive (Toff413 ∷ Bx4-0123 ∷ []) (Bx4-0123 ∷ Toff413 ∷ [])
  (rw⁻ 0 (q79 c4) ∷
   rw 1 (q111 c4) ∷
   rw 2 (q112 c4) ∷
   rw 1 (q113 c4) ∷
   rw 0 (q114 c4) ∷
   rw 1 (q115 c4) ∷
   rw 2 (q79 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl0091 (lit c4))
  q117 : Ws → Eqn
  q117 c4 = eqn (Sw12 ∷ Bx4-0213 ∷ []) (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (Toff413 ∷ Bx4-0123 ∷ []) (Bx4-0123 ∷ Toff413 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04233042 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (Sw12 ∷ Bx4-0123 ∷ []) (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) (wl0085 (lit c4))

-- auto TOFF012 | BOX(0;3142) @0412233041: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233041 : Ws → ⟪ (Toff423 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233041 c4 = derive (Toff423 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Toff423 ∷ [])
  (rw⁻ 0 (q45 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 0 (q119 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q45 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q122 : Ws → Eqn
  q122 c4 = eqn (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) (wl0120 (lit c4))
  q123 : Ws → Eqn
  q123 c4 = eqn (CCZ012 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF342 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) (wl0119 (lit c4))

-- auto CCZ012 | TOFF342 @3443: 7 steps
lem-auto-CCZ012-∣-TOFF342-at3443 : Ws → ⟪ (CCZ012 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at3443 c4 = derive (CCZ012 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q95 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw 2 (q122 c4) ∷
   rw 1 (q123 c4) ∷
   rw 0 (q124 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw 2 (q95 c4) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = eqn (Sw23 ∷ Bx0-1432 ∷ []) (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4))
  q126 : Ws → Eqn
  q126 c4 = eqn (Sw23 ∷ CS13 ∷ []) (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4))
  q127 : Ws → Eqn
  q127 c4 = eqn (Bx0-1423 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (Sw23 ∷ Bx0-1423 ∷ []) (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4))

-- auto BOX(0;1234) | CS13 @2442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at2442 : Ws → ⟪ (Bx0-1432 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at2442 c4 = derive (Bx0-1432 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1432 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q125 c4) ∷
   rw 2 (q126 c4) ∷
   rw 1 (q127 c4) ∷
   rw 0 (q128 c4) ∷
   rw 1 (q129 c4) ∷
   rw 2 (q55 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = eqn (Bx0-1423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 c4)

-- auto BOX(0;1234) | CCZ134 @2442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2442 : Ws → ⟪ (Bx0-1432 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2442 c4 = derive (Bx0-1432 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1432 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q125 c4) ∷
   rw⁻ 2 (q76 c4) ∷
   rw 1 (q130 c4) ∷
   rw⁻ 0 (q76 c4) ∷
   rw 1 (q129 c4) ∷
   rw 2 (q55 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = eqn (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4))
  q132 : Ws → Eqn
  q132 c4 = eqn (Sw23 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4))
  q133 : Ws → Eqn
  q133 c4 = eqn (CS02 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS02 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (Sw23 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4))

-- auto CS01 | SBOX(2;0;31;4) @13213442: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at13213442 : Ws → ⟪ (CS03 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at13213442 c4 = derive (CS03 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CS03 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q131 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q133 c4) ∷
   rw 0 (q134 c4) ∷
   rw 1 (q135 c4) ∷
   rw 2 (q55 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = eqn (Sb0-1-42-3 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 c4)

-- auto SBOX(0;1;23;4) | CCZ143 @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2442 c4 = derive (Sb0-1-43-2 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q61 c4) ∷
   rw⁻ 2 (q76 c4) ∷
   rw 1 (q136 c4) ∷
   rw⁻ 0 (q76 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q55 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = eqn (Sw23 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·2⟩ (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (Sb0-1-42-3 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4)
  q139 : Ws → Eqn
  q139 c4 = eqn (Sw23 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 c4 = derive (Sb0-1-43-2 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-3-2 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q137 c4) ∷
   rw 1 (q138 c4) ∷
   rw 0 (q139 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q55 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = eqn (Sw23 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·2⟩ (lit c4))
  q141 : Ws → Eqn
  q141 c4 = eqn (Sb0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (Sw23 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442 c4 = derive (Sb0-1-43-2 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q140 c4) ∷
   rw 1 (q141 c4) ∷
   rw 0 (q142 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q55 c4) ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = eqn (Sw01 ∷ Sb0-1-43-2 ∷ []) (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (Sb1-0-43-2 ∷ []) (Sb2-0-43-1 ∷ []) (lem-F0-at132132 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (Sw01 ∷ Sb2-0-43-1 ∷ []) (Sb2-1-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·43·1⟩ (lit c4))

-- F0 @01132032: 5 steps
lem-F0-at01132032 : Ws → ⟪ (Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ []) ⟫ʷ
lem-F0-at01132032 c4 = derive (Sb0-1-43-2 ∷ []) (Sb2-1-43-0 ∷ [])
  (rw⁻ 0 (q79 c4) ∷
   rw 1 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q145 c4) ∷
   rw 1 (q79 c4) ∷ []) Eq.refl

private
  q146 : Ws → Eqn
  q146 c4 = eqn (Toff024 ∷ []) (Toff024 ∷ []) (wp0394 c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (Bx0-1234 ∷ []) (Bx0-2134 ∷ []) (lem-sym12 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2143 ∷ []) (lem-sym34-at1221 c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4)
  q150 : Ws → Eqn
  q150 c4 = eqn (Toff024 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Toff024 ∷ []) (lem-T-beta-at12243143 c4)
  q151 : Ws → Eqn
  q151 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (Bx0-2134 ∷ []) (Bx0-1234 ∷ []) (lem-sym12-at1221 c4)

-- auto BOX(0;1234) | TOFF042: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF042 : Ws → ⟪ (Bx0-1234 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF042 c4 = derive (Bx0-1234 ∷ Toff024 ∷ []) (Toff024 ∷ Bx0-1234 ∷ [])
  (rw 1 (q146 c4) ∷
   rw 0 (q147 c4) ∷
   rw 0 (q148 c4) ∷
   rw 0 (q149 c4) ∷
   rw⁻ 0 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 1 (q152 c4) ∷
   rw 1 (q153 c4) ∷
   rw 0 (q146 c4) ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0096 (lit c4))
  q155 : Ws → Eqn
  q155 c4 = eqn (Sw01 ∷ Bx3-1042 ∷ []) (Bx3-0142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1042⟩ (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (Sw01 ∷ Bx3-0142 ∷ []) (Bx3-1042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0142⟩ (lit c4))

-- c124-beta @03203442: 7 steps
lem-c124-beta-at03203442 : Ws → ⟪ (CCZ012 ∷ Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at03203442 c4 = derive (CCZ012 ∷ Bx3-1042 ∷ []) (Bx3-1042 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q79 c4) ∷
   rw⁻ 1 (q154 c4) ∷
   rw 2 (q155 c4) ∷
   rw 1 (q53 c4) ∷
   rw 0 (q156 c4) ∷
   rw⁻ 1 (q154 c4) ∷
   rw 2 (q79 c4) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = eqn (Sw12 ∷ Bx3-2041 ∷ []) (Bx3-1042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2041⟩ (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (CCZ012 ∷ Bx3-1042 ∷ []) (Bx3-1042 ∷ CCZ012 ∷ []) (lem-c124-beta-at03203442 c4)
  q159 : Ws → Eqn
  q159 c4 = eqn (Sw12 ∷ Bx3-1042 ∷ []) (Bx3-2041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1042⟩ (lit c4))

-- c124-beta @0312203441: 7 steps
lem-c124-beta-at0312203441 : Ws → ⟪ (CCZ012 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at0312203441 c4 = derive (CCZ012 ∷ Bx3-2041 ∷ []) (Bx3-2041 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q45 c4) ∷
   rw⁻ 1 (q51 c4) ∷
   rw 2 (q157 c4) ∷
   rw 1 (q158 c4) ∷
   rw 0 (q159 c4) ∷
   rw⁻ 1 (q51 c4) ∷
   rw 2 (q45 c4) ∷ []) Eq.refl

private
  q160 : Ws → Eqn
  q160 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4))
  q161 : Ws → Eqn
  q161 c4 = eqn (Sb0-1-43-2 ∷ []) (Sb2-1-43-0 ∷ []) (lem-F0-at01132032 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (Sw12 ∷ Sb2-1-43-0 ∷ []) (Sb1-2-43-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·43·0⟩ (lit c4))

-- F0 @02132031: 5 steps
lem-F0-at02132031 : Ws → ⟪ (Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ []) ⟫ʷ
lem-F0-at02132031 c4 = derive (Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ [])
  (rw⁻ 0 (q45 c4) ∷
   rw 1 (q160 c4) ∷
   rw 1 (q161 c4) ∷
   rw 0 (q162 c4) ∷
   rw 1 (q45 c4) ∷ []) Eq.refl

private
  q163 : Ws → Eqn
  q163 c4 = eqn (S4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ S4 ∷ []) (wl0756 (lit c4))
  q164 : Ws → Eqn
  q164 c4 = eqn (S4 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ S4 ∷ []) (wl0757 (lit c4))
  q165 : Ws → Eqn
  q165 c4 = eqn (S4 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ S4 ∷ []) (wl0758 (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4)
  q167 : Ws → Eqn
  q167 c4 = eqn (S4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ S4 ∷ []) (wp0395 c4)
  q168 : Ws → Eqn
  q168 c4 = eqn (S4 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ S4 ∷ []) (wp0396 c4)

-- F4 CS12^0|iI^1: 30 steps
lem-F4-CS12ᵖ0∣iIᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣iIᵖ1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 13 1 (CS13⁻ ∷ []) ∷
   rw⁻ 12 (q163 c4) ∷
   re 14 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 9 (q164 c4) ∷
   re 7 1 (CS13 ∷ []) ∷
   rw⁻ 6 (q165 c4) ∷
   re 8 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q164 c4) ∷
   rw 1 (q166 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 9 (q167 c4) ∷
   rw⁻ 6 (q168 c4) ∷
   rw⁻ 3 (q167 c4) ∷
   rw⁻ 0 (q168 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 2 (q166 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   re 2 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = eqn (CS04 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ []) (wp0397 c4)
  q170 : Ws → Eqn
  q170 c4 = eqn (CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ CS04 ∷ []) (wp0398 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (CS04 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS04 ∷ []) (wp0399 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ []) (wp0400 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ []) (wp0401 c4)

-- F4 CS12^0|S0^1: 30 steps
lem-F4-CS12ᵖ0∣S0ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣S0ᵖ1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 13 1 (CS13⁻ ∷ []) ∷
   rw⁻ 12 (q169 c4) ∷
   re 14 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 9 (q170 c4) ∷
   re 7 1 (CS13 ∷ []) ∷
   rw⁻ 6 (q171 c4) ∷
   re 8 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q170 c4) ∷
   rw 1 (q166 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 9 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw⁻ 3 (q172 c4) ∷
   rw⁻ 0 (q173 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 2 (q166 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   re 2 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q174 : Ws → Eqn
  q174 c4 = eqn (CS14 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ CS14 ∷ []) (wl0759 (lit c4))
  q175 : Ws → Eqn
  q175 c4 = eqn (CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ CS14 ∷ []) (wl0760 (lit c4))
  q176 : Ws → Eqn
  q176 c4 = eqn (CS14 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS14 ∷ []) (wl0761 (lit c4))
  q177 : Ws → Eqn
  q177 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4))
  q178 : Ws → Eqn
  q178 c4 = eqn (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ []) (wl0762 (lit c4))
  q179 : Ws → Eqn
  q179 c4 = eqn (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ []) (wp0348 c4)
  q180 : Ws → Eqn
  q180 c4 = eqn (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (wp0349 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ []) (wp0402 c4)

-- F4 CS12^0|S1^1: 58 steps
lem-F4-CS12ᵖ0∣S1ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣S1ᵖ1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 13 1 (CS13⁻ ∷ []) ∷
   rw⁻ 12 (q174 c4) ∷
   re 14 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 9 (q175 c4) ∷
   re 7 1 (CS13 ∷ []) ∷
   rw⁻ 6 (q176 c4) ∷
   re 8 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q175 c4) ∷
   rw 1 (q166 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw 10 (q177 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 21 (q36 c4) ∷
   rw⁻ 18 (q178 c4) ∷
   rw⁻ 15 (q179 c4) ∷
   rw⁻ 12 (q178 c4) ∷
   rw⁻ 9 (q180 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw⁻ 11 (q177 c4) ∷
   rw⁻ 6 (q181 c4) ∷
   rw 4 (q177 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 15 (q36 c4) ∷
   rw⁻ 12 (q178 c4) ∷
   rw⁻ 9 (q179 c4) ∷
   rw⁻ 6 (q178 c4) ∷
   rw⁻ 3 (q180 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 5 (q177 c4) ∷
   rw⁻ 0 (q181 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 2 (q166 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   re 2 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q182 : Ws → Eqn
  q182 c4 = eqn (CS24 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ []) (wl0763 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ CS24 ∷ []) (wl0764 (lit c4))
  q184 : Ws → Eqn
  q184 c4 = eqn (CS24 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS24 ∷ []) (wl0765 (lit c4))
  q185 : Ws → Eqn
  q185 c4 = eqn (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ []) (wp0403 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS24 ∷ []) (wp0404 c4)

-- F4 CS12^0|S2^1: 30 steps
lem-F4-CS12ᵖ0∣S2ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣S2ᵖ1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 13 1 (CS13⁻ ∷ []) ∷
   rw⁻ 12 (q182 c4) ∷
   re 14 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 9 (q183 c4) ∷
   re 7 1 (CS13 ∷ []) ∷
   rw⁻ 6 (q184 c4) ∷
   re 8 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q183 c4) ∷
   rw 1 (q166 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 9 (q185 c4) ∷
   rw⁻ 6 (q186 c4) ∷
   rw⁻ 3 (q185 c4) ∷
   rw⁻ 0 (q186 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 2 (q166 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   re 2 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q187 : Ws → Eqn
  q187 c4 = eqn (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ []) (wl0766 (lit c4))
  q188 : Ws → Eqn
  q188 c4 = eqn (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ []) (wl0767 (lit c4))
  q189 : Ws → Eqn
  q189 c4 = eqn (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS34 ∷ []) (wl0768 (lit c4))
  q190 : Ws → Eqn
  q190 c4 = eqn (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ []) (wp0405 c4)
  q191 : Ws → Eqn
  q191 c4 = eqn (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ []) (wp0406 c4)

-- F4 CS12^0|S3^1: 30 steps
lem-F4-CS12ᵖ0∣S3ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣S3ᵖ1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 13 1 (CS13⁻ ∷ []) ∷
   rw⁻ 12 (q187 c4) ∷
   re 14 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 9 (q188 c4) ∷
   re 7 1 (CS13 ∷ []) ∷
   rw⁻ 6 (q189 c4) ∷
   re 8 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q188 c4) ∷
   rw 1 (q166 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 9 (q190 c4) ∷
   rw⁻ 6 (q191 c4) ∷
   rw⁻ 3 (q190 c4) ∷
   rw⁻ 0 (q191 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 2 (q166 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   re 2 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl
