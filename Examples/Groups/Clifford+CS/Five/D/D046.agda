{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D046 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0380 ; wl0381 ; wl0382 ; wl0383 ; wl0384 ; wl0385 ; wl0386 ; wl0387 ; wl0388 ; wl0389 ; wl0390 ; wl0391 ; wl0392 ; wl0393 ; wl0394 ; wl0395 ; wl0396 ; wl0397 ; wl0398 ; wl0399 ; wl0400 ; wl0401 ; wl0402 ; wl0403 ; wl0404 ; wl0405 ; wl0406 ; wl0407 ; wl0408 ; wl0409 ; wl0410 ; wl0411 ; wl0412 ; wl0413 ; wl0414 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0420 ; wp0024 ; wp0060 ; wp0127 ; wp0128 ; wp0129 ; wp0130 ; wp0131 ; wp0132 ; wp0133 ; wp0134 ; wp0135 ; wp0136 ; wp0137 ; wp0138 ; wp0139 ; wp0140 ; wp0141 ; wp0142 ; wp0143 ; wp0144)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-X1-beta-at02203443 ; lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 ; lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 ; lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym12-at0210213443 ; lem-sym12-at02203443 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CX41-TOFF203)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CS13 ∷ X1 ∷ K2 ∷ X1 ∷ []) (X1 ∷ K2 ∷ X1 ∷ CS13 ∷ []) (wl0409 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS13 ∷ []) (wl0410 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CS13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CS13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CS13 ∷ []) (wl0411 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CS13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ []) (wl0412 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ []) (X1 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ []) (wl0413 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (Toff204 ∷ []) (wp0142 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CS13 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ []) (wl0414 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) (wl0418 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (K3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx2-0143 ∷ []) (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (X1 ∷ Bx2-1043 ∷ X1 ∷ []) (CCZ034 ∷ Bx2-1043 ∷ []) (lem-X1-beta-at02203443 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ034 ∷ X1 ∷ []) (X1 ∷ CCZ034 ∷ []) (wp0060 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Sb2-0-41-3 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ034 ∷ CCZ034 ∷ []) [] (wp0024 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS14⁻ ∷ []) (wp0127 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS14⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS14⁻ ∷ []) (wl0380 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CS14⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS14⁻ ∷ []) (wl0381 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CS14⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS14⁻ ∷ []) (wp0128 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CS14⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS14⁻ ∷ []) (wp0129 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ []) (wp0130 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ []) (wl0382 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ []) (wl0383 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (S1 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1 ∷ []) (wl0384 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (S1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1 ∷ []) (wl0385 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0131 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Toff314 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff314 ∷ []) (wp0132 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (X1 ∷ CCZ234 ∷ []) (CCZ234 ∷ X1 ∷ []) (c₂ (X ↑) (CCZ))
  q42 : Ws → Eqn
  q42 c4 = eqn (CK10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK10 ∷ []) (c₂ (CK₁₀) (CCZ))
  q43 : Ws → Eqn
  q43 c4 = eqn (Toff201 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff201 ∷ []) (wl0386 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CK10 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ []) (wl0420 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS14⁻ ∷ []) (wp0133 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (S1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ S1 ∷ []) (wl0387 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CK10 ∷ []) (ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ []) (wl0388 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) (wp0134 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CS01 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) (wl0389 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) (wp0135 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CS01 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ []) (wl0390 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CS01 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) (wl0391 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (wl0392 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (K0 ∷ X1 ∷ []) (X1 ∷ K0 ∷ []) (c₁ (K) (X))
  q55 : Ws → Eqn
  q55 c4 = eqn (K0 ∷ CCZ234 ∷ []) (CCZ234 ∷ K0 ∷ []) (c₁ (K) (CCZ ↑))
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ []) (wl0394 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CS01 ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) (wl0395 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CS01 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01 ∷ []) (wl0396 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CS01 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ []) (wp0136 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (wp0137 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (wp0138 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (S1⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1⁻ ∷ []) (wp0139 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (S1⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ []) (wl0397 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ []) (wl0398 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (S1⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1⁻ ∷ []) (wl0399 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (S1⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1⁻ ∷ []) (wl0400 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (X1 ∷ ι ∷ []) (ι ∷ X1 ∷ []) zc
  q69 : Ws → Eqn
  q69 c4 = eqn (Sb2-0-41-3 ∷ ι ∷ []) (ι ∷ Sb2-0-41-3 ∷ []) zc
  q70 : Ws → Eqn
  q70 c4 = eqn (CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ []) (wl0401 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (K3⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) (wl0405 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) (wl0406 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (CX41 ∷ Toff203 ∷ []) (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4))
  q81 : Ws → Eqn
  q81 c4 = eqn (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0140 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0141 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) (wl0419 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4)

-- F1 CS-K0 part1: 500 steps
lem-F1-CS-K0-part1 : Ws → ⟪ (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ
lem-F1-CS-K0-part1 c4 = derive (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ CS04 ∷ [])
  (rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw 23 (q2 c4) ∷
   rw 28 (q3 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw 26 (q4 c4) ∷
   rw 29 (q5 c4) ∷
   rw 32 (q6 c4) ∷
   rw 35 (q5 c4) ∷
   rw 38 (q7 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw⁻ 27 (q3 c4) ∷
   rw 29 (q8 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 24 (q9 c4) ∷
   rw 26 (q10 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw 20 (q12 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   rw 23 (q13 c4) ∷
   re 24 1 (Sb2-0-3-1 ∷ []) ∷
   rw 26 (q12 c4) ∷
   re 31 1 (CS03⁻ ∷ []) ∷
   rw 29 (q14 c4) ∷
   re 30 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   re 18 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 20 (q15 c4) ∷
   rw 16 (q16 c4) ∷
   rw 17 (q17 c4) ∷
   rw 18 (q16 c4) ∷
   rw 19 (q18 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw 17 (q19 c4) ∷
   rw 17 (q20 c4) ∷
   rw 16 (q21 c4) ∷
   rw 17 (q22 c4) ∷
   rw 17 (q23 c4) ∷
   rw 17 (q24 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw 20 (q19 c4) ∷
   rw 20 (q20 c4) ∷
   rw 19 (q21 c4) ∷
   rw 20 (q22 c4) ∷
   rw 20 (q23 c4) ∷
   rw⁻ 15 (q25 c4) ∷
   rw⁻ 18 (q25 c4) ∷
   rw 17 (q26 c4) ∷
   rw⁻ 16 (q25 c4) ∷
   rw 15 (q27 c4) ∷
   re 18 5 (Sb2-0-41-3 ∷ []) ∷
   re 16 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 17 (q1 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw 16 (q11 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw 14 (q28 c4) ∷
   rw 17 (q29 c4) ∷
   rw 20 (q28 c4) ∷
   rw 23 (q29 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw 17 (q30 c4) ∷
   re 22 1 (CS03 ∷ []) ∷
   rw 20 (q31 c4) ∷
   re 21 1 (Sb2-0-3-1 ∷ []) ∷
   rw 23 (q30 c4) ∷
   re 28 1 (CS03⁻ ∷ []) ∷
   rw 26 (q32 c4) ∷
   re 27 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   re 15 5 (Sb2-0-41-3 ∷ []) ∷
   re 15 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw 15 (q11 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw 13 (q33 c4) ∷
   rw 16 (q34 c4) ∷
   rw 19 (q33 c4) ∷
   rw 22 (q34 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw⁻ 14 (q11 c4) ∷
   rw 16 (q35 c4) ∷
   re 21 1 (CS03 ∷ []) ∷
   rw 19 (q36 c4) ∷
   re 20 1 (Sb2-0-3-1 ∷ []) ∷
   rw 22 (q35 c4) ∷
   re 27 1 (CS03⁻ ∷ []) ∷
   rw 25 (q37 c4) ∷
   re 26 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   re 14 5 (Sb2-0-41-3 ∷ []) ∷
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 22 1 (CS03 ∷ []) ∷
   re 24 1 (CS03⁻ ∷ []) ∷
   rw 22 (q38 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   re 27 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 21 (q39 c4) ∷
   rw 20 (q19 c4) ∷
   rw 20 (q40 c4) ∷
   rw⁻ 23 (q41 c4) ∷
   rw⁻ 24 (q42 c4) ∷
   rw⁻ 25 (q41 c4) ∷
   rw 22 (q43 c4) ∷
   rw⁻ 21 (q41 c4) ∷
   rw⁻ 22 (q42 c4) ∷
   rw⁻ 23 (q41 c4) ∷
   rw 20 (q43 c4) ∷
   rw⁻ 23 (q40 c4) ∷
   rw 23 (q23 c4) ∷
   re 23 5 (Sb2-0-41-3 ∷ []) ∷
   rw 19 (q44 c4) ∷
   re 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 20 1 (CS03 ∷ []) ∷
   re 22 1 (CS03⁻ ∷ []) ∷
   rw 20 (q38 c4) ∷
   re 23 1 (Sb2-0-3-1 ∷ []) ∷
   re 25 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 19 (q39 c4) ∷
   rw 18 (q19 c4) ∷
   rw 18 (q40 c4) ∷
   rw⁻ 21 (q41 c4) ∷
   rw⁻ 22 (q42 c4) ∷
   rw⁻ 23 (q41 c4) ∷
   rw 20 (q43 c4) ∷
   rw⁻ 19 (q41 c4) ∷
   rw⁻ 20 (q42 c4) ∷
   rw⁻ 21 (q41 c4) ∷
   rw 18 (q43 c4) ∷
   rw⁻ 21 (q40 c4) ∷
   rw 21 (q23 c4) ∷
   re 21 5 (Sb2-0-41-3 ∷ []) ∷
   rw 17 (q45 c4) ∷
   rw 16 (q46 c4) ∷
   rw 24 (q47 c4) ∷
   re 32 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw 32 (q11 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw 30 (q48 c4) ∷
   rw 33 (q49 c4) ∷
   rw 36 (q48 c4) ∷
   rw 39 (q49 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw⁻ 31 (q11 c4) ∷
   rw 33 (q50 c4) ∷
   re 38 1 (CS03 ∷ []) ∷
   rw 36 (q51 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ []) ∷
   rw 39 (q50 c4) ∷
   re 44 1 (CS03⁻ ∷ []) ∷
   rw 42 (q52 c4) ∷
   re 43 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   re 31 5 (Sb2-0-41-3 ∷ []) ∷
   re 31 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   rw 31 (q19 c4) ∷
   rw 31 (q40 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw 27 (q53 c4) ∷
   rw 32 (q54 c4) ∷
   rw 33 (q55 c4) ∷
   rw 34 (q54 c4) ∷
   rw 33 (q56 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw 31 (q57 c4) ∷
   rw 34 (q58 c4) ∷
   rw 37 (q59 c4) ∷
   rw 40 (q58 c4) ∷
   rw 43 (q60 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   rw⁻ 32 (q56 c4) ∷
   rw 30 (q54 c4) ∷
   rw 31 (q55 c4) ∷
   rw 32 (q54 c4) ∷
   rw 33 (q53 c4) ∷
   rw 38 (q54 c4) ∷
   rw 39 (q55 c4) ∷
   rw 40 (q54 c4) ∷
   rw 39 (q56 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw⁻ 46 (q1 c4) ∷
   rw⁻ 49 (q1 c4) ∷
   rw 37 (q57 c4) ∷
   rw 40 (q58 c4) ∷
   rw 43 (q59 c4) ∷
   rw 46 (q58 c4) ∷
   rw 49 (q60 c4) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   rw 42 (q1 c4) ∷
   rw⁻ 38 (q56 c4) ∷
   rw 36 (q54 c4) ∷
   rw 37 (q55 c4) ∷
   rw 38 (q54 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw⁻ 28 (q40 c4) ∷
   rw 28 (q23 c4) ∷
   rw 30 (q61 c4) ∷
   re 37 1 (CS03 ∷ []) ∷
   re 43 1 (CS03⁻ ∷ []) ∷
   rw 33 (q62 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ []) ∷
   re 40 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   re 28 5 (Sb2-0-41-3 ∷ []) ∷
   re 28 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw 28 (q11 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw 26 (q48 c4) ∷
   rw 29 (q49 c4) ∷
   rw 32 (q48 c4) ∷
   rw 35 (q49 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw⁻ 27 (q11 c4) ∷
   rw 29 (q50 c4) ∷
   re 34 1 (CS03 ∷ []) ∷
   rw 32 (q51 c4) ∷
   re 33 1 (Sb2-0-3-1 ∷ []) ∷
   rw 35 (q50 c4) ∷
   re 40 1 (CS03⁻ ∷ []) ∷
   rw 38 (q52 c4) ∷
   re 39 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   re 27 5 (Sb2-0-41-3 ∷ []) ∷
   re 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw 27 (q11 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw 25 (q63 c4) ∷
   rw 28 (q64 c4) ∷
   rw 31 (q63 c4) ∷
   rw 34 (q64 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw⁻ 26 (q11 c4) ∷
   rw 28 (q65 c4) ∷
   re 33 1 (CS03 ∷ []) ∷
   rw 31 (q66 c4) ∷
   re 32 1 (Sb2-0-3-1 ∷ []) ∷
   rw 34 (q65 c4) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   rw 37 (q67 c4) ∷
   re 38 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   re 26 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 24 (q68 c4) ∷
   rw⁻ 25 (q69 c4) ∷
   rw⁻ 26 (q68 c4) ∷
   rw⁻ 27 (q47 c4) ∷
   re 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 27 1 (CS03⁻ ∷ []) ∷
   rw 27 (q70 c4) ∷
   re 28 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 28 (q71 c4) ∷
   re 29 1 (CS03⁻ ∷ []) ∷
   rw 29 (q70 c4) ∷
   re 30 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q18 c4) ∷
   rw 28 (q72 c4) ∷
   rw 29 (q73 c4) ∷
   rw 30 (q72 c4) ∷
   rw 27 (q15 c4) ∷
   rw 31 (q74 c4) ∷
   rw 32 (q75 c4) ∷
   rw 33 (q74 c4) ∷
   re 32 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw 32 (q76 c4) ∷
   rw 32 (q77 c4) ∷
   rw 32 (q78 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw 30 (q79 c4) ∷
   rw 31 (q80 c4) ∷
   rw 32 (q79 c4) ∷
   rw 29 (q81 c4) ∷
   rw 28 (q79 c4) ∷
   rw 29 (q80 c4) ∷
   rw 30 (q79 c4) ∷
   rw 31 (q82 c4) ∷
   rw 36 (q79 c4) ∷
   rw 37 (q80 c4) ∷
   rw 38 (q79 c4) ∷
   rw 35 (q81 c4) ∷
   rw 34 (q79 c4) ∷
   rw 35 (q80 c4) ∷
   rw 36 (q79 c4) ∷
   rw 37 (q82 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw⁻ 29 (q78 c4) ∷
   rw 29 (q83 c4) ∷
   rw 29 (q84 c4) ∷
   re 38 1 (CS03 ∷ []) ∷
   rw 31 (q85 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ []) ∷
   re 44 1 (CS03⁻ ∷ []) ∷
   rw 40 (q86 c4) ∷
   re 41 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   re 29 5 (Sb2-0-41-3 ∷ []) ∷
   re 29 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw 29 (q11 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw 27 (q2 c4) ∷
   rw 32 (q3 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw 30 (q4 c4) ∷
   rw 33 (q5 c4) ∷
   rw 36 (q6 c4) ∷
   rw 39 (q5 c4) ∷
   rw 42 (q7 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw⁻ 31 (q3 c4) ∷
   rw 33 (q8 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 28 (q9 c4) ∷
   rw 30 (q10 c4) ∷
   rw⁻ 35 (q9 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw 33 (q2 c4) ∷
   rw 38 (q3 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw⁻ 45 (q1 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw 36 (q4 c4) ∷
   rw 39 (q5 c4) ∷
   rw 42 (q6 c4) ∷
   rw 45 (q5 c4) ∷
   rw 48 (q7 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   rw⁻ 37 (q3 c4) ∷
   rw 39 (q8 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   rw 34 (q9 c4) ∷
   rw 36 (q10 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw⁻ 28 (q11 c4) ∷
   rw 30 (q12 c4) ∷
   re 35 1 (CS03 ∷ []) ∷
   rw 33 (q13 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ []) ∷
   rw 36 (q12 c4) ∷
   re 41 1 (CS03⁻ ∷ []) ∷
   rw 39 (q14 c4) ∷
   re 40 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   re 28 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 30 (q15 c4) ∷
   rw 26 (q16 c4) ∷
   rw 27 (q17 c4) ∷
   rw 28 (q16 c4) ∷
   rw 29 (q18 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   rw 25 (q87 c4) ∷
   re 26 1 (Sb2-0-3-1 ∷ []) ∷
   rw 26 (q88 c4) ∷
   re 27 1 (CS03 ∷ []) ∷
   rw 27 (q87 c4) ∷
   re 28 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q18 c4) ∷
   rw 26 (q72 c4) ∷
   rw 27 (q73 c4) ∷
   rw 28 (q72 c4) ∷
   rw 25 (q15 c4) ∷
   rw 29 (q74 c4) ∷
   rw 30 (q75 c4) ∷
   rw 31 (q74 c4) ∷
   re 30 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw 30 (q76 c4) ∷
   rw 30 (q77 c4) ∷
   rw 30 (q78 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw 28 (q79 c4) ∷
   rw 29 (q80 c4) ∷
   rw 30 (q79 c4) ∷ []) Eq.refl
