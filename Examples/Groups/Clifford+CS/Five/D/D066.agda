{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D066 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0386 ; wl0401 ; wl0402 ; wl0403 ; wl0404 ; wl0405 ; wl0406 ; wl0407 ; wl0408 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0454 ; wl0455 ; wl0456 ; wl0457 ; wl0458 ; wl0459 ; wp0024 ; wp0060 ; wp0131 ; wp0132 ; wp0140 ; wp0141 ; wp0163 ; wp0164 ; wp0165 ; wp0166)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-X1-beta-at02203443 ; lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233241 ; lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233241 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym12-at0210213443 ; lem-sym12-at02203443 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-CSd01-∣-BOX⟨2·3104⟩-at01143043 ; lem-auto-S0-∣-BOX⟨1·2304⟩-at0112203443 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-TOFF203-CX41)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) (wl0406 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) (wl0405 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sb2-0-41-3 ∷ CS34 ∷ []) (CS34 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sb2-0-41-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ []) (wl0401 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Toff201 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff201 ∷ []) (wl0386 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (X1 ∷ CCZ234 ∷ []) (CCZ234 ∷ X1 ∷ []) (c₂ (X ↑) (CCZ))
  q18 : Ws → Eqn
  q18 c4 = eqn (CK10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK10 ∷ []) (c₂ (CK₁₀) (CCZ))
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Toff314 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff314 ∷ []) (wp0132 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0131 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx2-0143 ∷ []) (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (X1 ∷ Bx2-1043 ∷ X1 ∷ []) (CCZ034 ∷ Bx2-1043 ∷ []) (lem-X1-beta-at02203443 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ034 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233241 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ034 ∷ X1 ∷ []) (X1 ∷ CCZ034 ∷ []) (wp0060 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ034 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233241 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ034 ∷ CCZ034 ∷ []) [] (wp0024 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) (wl0418 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sb2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) (wl0454 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) (wl0455 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0141 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0140 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Toff203 ∷ CX41 ∷ []) (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) (wl0419 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CS14⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS14⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·3104⟩-at01143043 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ034 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CCZ034 ∷ []) (wp0163 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (Toff314 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ Toff314 ∷ []) (wl0456 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CS03 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CS03 ∷ []) (wp0164 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CS03⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CS03⁻ ∷ []) (wp0165 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (S1 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ S1 ∷ []) (lem-auto-S0-∣-BOX⟨1·2304⟩-at0112203443 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ034 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CCZ034 ∷ []) (wp0166 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ []) (wl0457 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CS03 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CS03 ∷ []) (wl0458 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CS03⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CS03⁻ ∷ []) (wl0459 (lit c4))

-- F1 CS-K0 part21: 394 steps
lem-F1-CS-K0-part21 : Ws → ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ
lem-F1-CS-K0-part21 c4 = derive (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  (rw⁻ 27 (q1 c4) ∷
   rw 30 (q2 c4) ∷
   rw 31 (q2 c4) ∷
   rw 32 (q2 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw 29 (q4 c4) ∷
   rw 29 (q5 c4) ∷
   rw 30 (q2 c4) ∷
   rw 31 (q2 c4) ∷
   rw 32 (q2 c4) ∷
   rw 33 (q2 c4) ∷
   re 29 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 30 (q6 c4) ∷
   rw 29 (q7 c4) ∷
   rw⁻ 28 (q6 c4) ∷
   rw⁻ 24 (q8 c4) ∷
   rw⁻ 27 (q9 c4) ∷
   rw 26 (q10 c4) ∷
   rw⁻ 25 (q9 c4) ∷
   rw 23 (q11 c4) ∷
   re 27 1 (CS03⁻ ∷ []) ∷
   rw⁻ 26 (q12 c4) ∷
   re 26 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 25 (q13 c4) ∷
   re 25 1 (CS03⁻ ∷ []) ∷
   rw⁻ 24 (q12 c4) ∷
   re 24 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 20 5 (Sb2-0-41-3 ∷ []) ∷
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 20 (q14 c4) ∷
   rw 20 (q15 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw 20 (q17 c4) ∷
   rw 19 (q18 c4) ∷
   rw 18 (q17 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw 22 (q17 c4) ∷
   rw 21 (q18 c4) ∷
   rw 20 (q17 c4) ∷
   rw⁻ 17 (q15 c4) ∷
   rw 17 (q19 c4) ∷
   rw⁻ 18 (q20 c4) ∷
   re 22 1 (CS03 ∷ []) ∷
   re 24 1 (CS03⁻ ∷ []) ∷
   rw⁻ 19 (q21 c4) ∷
   re 19 1 (Sb2-0-3-1 ∷ []) ∷
   re 21 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 17 5 (Sb2-0-41-3 ∷ []) ∷
   re 17 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 18 (q2 c4) ∷
   rw 17 (q14 c4) ∷
   rw 17 (q22 c4) ∷
   rw 16 (q23 c4) ∷
   rw 17 (q24 c4) ∷
   rw 17 (q19 c4) ∷
   rw 16 (q25 c4) ∷
   rw 15 (q26 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw 15 (q14 c4) ∷
   rw 15 (q22 c4) ∷
   rw 14 (q23 c4) ∷
   rw 15 (q24 c4) ∷
   rw 15 (q19 c4) ∷
   rw 14 (q25 c4) ∷
   rw 18 (q27 c4) ∷
   rw 15 (q27 c4) ∷
   rw 16 (q28 c4) ∷
   rw 17 (q27 c4) ∷
   rw 18 (q29 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw⁻ 17 (q30 c4) ∷
   rw 16 (q31 c4) ∷
   rw⁻ 15 (q30 c4) ∷
   rw 19 (q8 c4) ∷
   re 17 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   re 29 1 (CS03⁻ ∷ []) ∷
   rw⁻ 28 (q32 c4) ∷
   re 30 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q33 c4) ∷
   re 23 1 (CS03 ∷ []) ∷
   rw⁻ 22 (q34 c4) ∷
   re 24 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 19 (q33 c4) ∷
   rw 17 (q14 c4) ∷
   rw 17 (q15 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 25 (q35 c4) ∷
   rw⁻ 22 (q36 c4) ∷
   rw⁻ 19 (q35 c4) ∷
   rw⁻ 16 (q36 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw 18 (q19 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   re 18 5 (Sb2-0-41-3 ∷ []) ∷
   re 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   re 30 1 (CS03⁻ ∷ []) ∷
   rw⁻ 29 (q37 c4) ∷
   re 33 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 24 1 (CS03 ∷ []) ∷
   rw⁻ 20 (q38 c4) ∷
   re 27 1 (Sb2-0-3-1 ∷ []) ∷
   rw 18 (q39 c4) ∷
   rw 18 (q40 c4) ∷
   rw 18 (q3 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 26 (q41 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw 24 (q42 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 24 (q43 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw 26 (q42 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 20 (q41 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw 18 (q42 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw⁻ 18 (q43 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw 20 (q42 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw 24 (q2 c4) ∷
   rw⁻ 21 (q3 c4) ∷
   rw 21 (q4 c4) ∷
   rw 21 (q5 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw 24 (q2 c4) ∷
   rw 25 (q2 c4) ∷
   re 21 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 22 (q6 c4) ∷
   rw 21 (q7 c4) ∷
   rw⁻ 20 (q6 c4) ∷
   rw⁻ 16 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw 15 (q11 c4) ∷
   re 19 1 (CS03 ∷ []) ∷
   rw⁻ 18 (q44 c4) ∷
   re 18 1 (Sb2-0-3-1 ∷ []) ∷
   rw 17 (q45 c4) ∷
   re 17 1 (CS03 ∷ []) ∷
   rw⁻ 16 (q44 c4) ∷
   re 16 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q11 c4) ∷
   rw⁻ 19 (q30 c4) ∷
   rw 18 (q31 c4) ∷
   rw⁻ 17 (q30 c4) ∷
   rw 21 (q8 c4) ∷
   re 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   re 31 1 (CS03⁻ ∷ []) ∷
   rw⁻ 30 (q32 c4) ∷
   re 32 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 27 (q33 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   rw⁻ 24 (q34 c4) ∷
   re 26 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 21 (q33 c4) ∷
   rw 19 (q14 c4) ∷
   rw 19 (q15 c4) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 27 (q35 c4) ∷
   rw⁻ 24 (q36 c4) ∷
   rw⁻ 21 (q35 c4) ∷
   rw⁻ 18 (q36 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw⁻ 20 (q15 c4) ∷
   rw 20 (q19 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw 24 (q2 c4) ∷
   re 20 5 (Sb2-0-41-3 ∷ []) ∷
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 30 (q2 c4) ∷
   re 32 1 (CS03⁻ ∷ []) ∷
   rw⁻ 31 (q37 c4) ∷
   re 35 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 26 1 (CS03 ∷ []) ∷
   rw⁻ 22 (q38 c4) ∷
   re 29 1 (Sb2-0-3-1 ∷ []) ∷
   rw 20 (q39 c4) ∷
   rw 20 (q40 c4) ∷
   rw 20 (q3 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 28 (q41 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw 26 (q42 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 26 (q43 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw 28 (q42 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 22 (q41 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw 20 (q42 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 20 (q43 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw 22 (q42 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw 24 (q2 c4) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q2 c4) ∷
   rw⁻ 23 (q3 c4) ∷
   rw 23 (q4 c4) ∷
   rw 23 (q5 c4) ∷
   rw 24 (q2 c4) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q2 c4) ∷
   rw 27 (q2 c4) ∷
   re 23 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 24 (q6 c4) ∷
   rw 23 (q7 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw 17 (q11 c4) ∷
   re 21 1 (CS03⁻ ∷ []) ∷
   rw⁻ 20 (q12 c4) ∷
   re 20 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 19 (q13 c4) ∷
   re 19 1 (CS03⁻ ∷ []) ∷
   rw⁻ 18 (q12 c4) ∷
   re 18 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 14 5 (Sb2-0-41-3 ∷ []) ∷
   re 14 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q2 c4) ∷
   rw 14 (q14 c4) ∷
   rw 14 (q22 c4) ∷
   rw 13 (q23 c4) ∷
   rw 14 (q24 c4) ∷
   rw 14 (q19 c4) ∷
   rw 13 (q25 c4) ∷
   rw 12 (q46 c4) ∷
   rw⁻ 13 (q2 c4) ∷
   rw 12 (q14 c4) ∷
   rw 12 (q22 c4) ∷
   rw 11 (q23 c4) ∷
   rw 12 (q24 c4) ∷
   rw 12 (q19 c4) ∷
   rw 11 (q25 c4) ∷
   rw 15 (q27 c4) ∷
   rw 12 (q47 c4) ∷
   rw 15 (q29 c4) ∷
   rw⁻ 12 (q48 c4) ∷
   re 16 1 (CS03 ∷ []) ∷
   rw⁻ 13 (q49 c4) ∷
   re 13 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 14 (q48 c4) ∷
   re 18 1 (CS03⁻ ∷ []) ∷
   rw⁻ 15 (q50 c4) ∷
   re 15 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 11 5 (Sb2-0-41-3 ∷ []) ∷
   re 11 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 12 (q2 c4) ∷
   rw 11 (q14 c4) ∷
   rw 11 (q22 c4) ∷
   rw 10 (q23 c4) ∷
   rw 11 (q24 c4) ∷
   rw 11 (q19 c4) ∷
   rw 10 (q25 c4) ∷
   rw 9 (q51 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   rw 9 (q14 c4) ∷
   rw 9 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw 9 (q24 c4) ∷
   rw 9 (q19 c4) ∷
   rw 8 (q25 c4) ∷
   rw 12 (q27 c4) ∷
   rw 9 (q52 c4) ∷
   rw 12 (q29 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   re 13 1 (CS03 ∷ []) ∷
   rw⁻ 10 (q54 c4) ∷
   re 10 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 11 (q53 c4) ∷
   re 15 1 (CS03⁻ ∷ []) ∷
   rw⁻ 12 (q55 c4) ∷
   re 12 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 8 5 (Sb2-0-41-3 ∷ []) ∷
   re 30 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 30 1 (CS03 ∷ []) ∷
   rw⁻ 29 (q44 c4) ∷
   re 29 1 (Sb2-0-3-1 ∷ []) ∷
   rw 28 (q45 c4) ∷
   re 28 1 (CS03 ∷ []) ∷
   rw⁻ 27 (q44 c4) ∷
   re 27 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q11 c4) ∷
   rw⁻ 30 (q30 c4) ∷
   rw 29 (q31 c4) ∷
   rw⁻ 28 (q30 c4) ∷
   rw 32 (q8 c4) ∷
   re 30 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 37 (q2 c4) ∷
   rw⁻ 40 (q2 c4) ∷
   re 42 1 (CS03⁻ ∷ []) ∷
   rw⁻ 41 (q32 c4) ∷
   re 43 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 38 (q33 c4) ∷
   re 36 1 (CS03 ∷ []) ∷
   rw⁻ 35 (q34 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q33 c4) ∷
   rw 30 (q14 c4) ∷
   rw 30 (q15 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 37 (q2 c4) ∷
   rw⁻ 38 (q35 c4) ∷
   rw⁻ 35 (q36 c4) ∷
   rw⁻ 32 (q35 c4) ∷
   rw⁻ 29 (q36 c4) ∷
   rw 32 (q2 c4) ∷
   rw 33 (q2 c4) ∷
   rw 34 (q2 c4) ∷
   rw⁻ 31 (q15 c4) ∷
   rw 31 (q19 c4) ∷
   rw 32 (q2 c4) ∷
   rw 33 (q2 c4) ∷
   rw 34 (q2 c4) ∷
   rw 35 (q2 c4) ∷
   re 31 5 (Sb2-0-41-3 ∷ []) ∷
   re 31 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   rw⁻ 38 (q2 c4) ∷
   rw⁻ 41 (q2 c4) ∷
   re 43 1 (CS03⁻ ∷ []) ∷
   rw⁻ 42 (q37 c4) ∷
   re 46 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 37 1 (CS03 ∷ []) ∷
   rw⁻ 33 (q38 c4) ∷
   re 40 1 (Sb2-0-3-1 ∷ []) ∷
   rw 31 (q39 c4) ∷
   rw 31 (q40 c4) ∷
   rw 31 (q3 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   rw⁻ 38 (q2 c4) ∷
   rw⁻ 39 (q41 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw 37 (q42 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 37 (q43 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw 39 (q42 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw⁻ 33 (q41 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw 31 (q42 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 31 (q43 c4) ∷
   rw⁻ 34 (q1 c4) ∷ []) Eq.refl
