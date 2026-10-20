{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D078 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0382 ; wl0383 ; wl0384 ; wl0401 ; wl0402 ; wl0403 ; wl0404 ; wl0405 ; wl0406 ; wl0407 ; wl0408 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0424 ; wl0433 ; wl0434 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0444 ; wl0445 ; wl0454 ; wl0455 ; wl0461 ; wl0462 ; wl0463 ; wl0464 ; wl0468 ; wp0130 ; wp0140 ; wp0141 ; wp0143 ; wp0155 ; wp0168 ; wp0171)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym34-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym12-at021021 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-beta-T-at022330 ; lem-sym12-at02203443 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441 ; lem-sym34-at0220)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-BOX⟨0·1234⟩-∣-CS40-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-TOFF203-CX41)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ []) (wl0383 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (S1 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1 ∷ []) (wl0384 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ []) (wl0382 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ []) (wp0130 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (X1 ∷ ι⁻ ∷ []) (ι⁻ ∷ X1 ∷ []) (zc⁻)
  q8 : Ws → Eqn
  q8 c4 = eqn (Sb2-0-41-3 ∷ ι⁻ ∷ []) (ι⁻ ∷ Sb2-0-41-3 ∷ []) (zc⁻)
  q9 : Ws → Eqn
  q9 c4 = eqn (CK10⁻ ∷ []) (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ []) (wl0424 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CK10⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CK10⁻ ∷ []) (wp0171 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CK10⁻ ∷ []) (wl0468 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) (wl0419 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) (wl0418 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Sb2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) (wl0454 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) (wl0455 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0141 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0140 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) (wl0406 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Toff203 ∷ CX41 ∷ []) (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) (wl0405 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Sb2-0-41-3 ∷ CS34 ∷ []) (CS34 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Sb2-0-41-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ []) (wl0401 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ []) (wp0155 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Sb2-0-41-3 ∷ Toff204 ∷ []) (Toff204 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at0210243143 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ123 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0444 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) (wl0443 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ123 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ []) (wl0445 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ []) (wl0434 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (Bx2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS40-at0210243143 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym12-at021021 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1304 ∷ []) (lem-sym23-at0220 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CX13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Bx2-1304 ∷ []) (Bx2-1034 ∷ []) (lem-sym23-at022330 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1043 ∷ []) (lem-sym34-at0220 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ []) (wl0440 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (Bx2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4))

-- F1 CS-K0 part33: 357 steps
lem-F1-CS-K0-part33 : Ws → ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ ι⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ
lem-F1-CS-K0-part33 c4 = derive (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ ι⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  (rw⁻ 32 (q1 c4) ∷
   re 30 1 (CS03 ∷ []) ∷
   rw⁻ 29 (q2 c4) ∷
   re 31 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q1 c4) ∷
   rw 24 (q3 c4) ∷
   rw⁻ 25 (q4 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 29 (q6 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   rw⁻ 23 (q6 c4) ∷
   rw 26 (q4 c4) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   rw⁻ 25 (q3 c4) ∷
   rw 26 (q4 c4) ∷
   rw 27 (q4 c4) ∷
   rw 28 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   re 25 5 (Sb2-0-41-3 ∷ []) ∷
   rw 26 (q7 c4) ∷
   rw 25 (q8 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 15 (q10 c4) ∷
   rw⁻ 12 (q11 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 34 1 (CS03 ∷ []) ∷
   rw⁻ 33 (q12 c4) ∷
   re 33 1 (Sb2-0-3-1 ∷ []) ∷
   rw 32 (q13 c4) ∷
   re 32 1 (CS03 ∷ []) ∷
   rw⁻ 31 (q12 c4) ∷
   re 31 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 35 (q14 c4) ∷
   rw⁻ 34 (q15 c4) ∷
   rw 33 (q16 c4) ∷
   rw⁻ 32 (q15 c4) ∷
   rw 36 (q17 c4) ∷
   re 34 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 35 (q4 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw⁻ 41 (q4 c4) ∷
   rw⁻ 44 (q4 c4) ∷
   re 46 1 (CS03⁻ ∷ []) ∷
   rw⁻ 45 (q18 c4) ∷
   re 47 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 42 (q19 c4) ∷
   re 40 1 (CS03 ∷ []) ∷
   rw⁻ 39 (q20 c4) ∷
   re 41 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 36 (q19 c4) ∷
   rw 34 (q21 c4) ∷
   rw 34 (q22 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw⁻ 41 (q4 c4) ∷
   rw⁻ 42 (q23 c4) ∷
   rw⁻ 39 (q24 c4) ∷
   rw⁻ 36 (q23 c4) ∷
   rw⁻ 33 (q24 c4) ∷
   rw 36 (q4 c4) ∷
   rw 37 (q4 c4) ∷
   rw 38 (q4 c4) ∷
   rw⁻ 35 (q22 c4) ∷
   rw 35 (q25 c4) ∷
   rw 36 (q4 c4) ∷
   rw 37 (q4 c4) ∷
   rw 38 (q4 c4) ∷
   rw 39 (q4 c4) ∷
   re 35 5 (Sb2-0-41-3 ∷ []) ∷
   re 35 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 36 (q4 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw⁻ 42 (q4 c4) ∷
   rw⁻ 45 (q4 c4) ∷
   re 47 1 (CS03⁻ ∷ []) ∷
   rw⁻ 46 (q26 c4) ∷
   re 50 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 41 1 (CS03 ∷ []) ∷
   rw⁻ 37 (q27 c4) ∷
   re 44 1 (Sb2-0-3-1 ∷ []) ∷
   rw 35 (q28 c4) ∷
   rw 35 (q29 c4) ∷
   rw 35 (q30 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw⁻ 42 (q4 c4) ∷
   rw⁻ 43 (q31 c4) ∷
   rw⁻ 42 (q32 c4) ∷
   rw 41 (q33 c4) ∷
   rw⁻ 40 (q32 c4) ∷
   rw⁻ 41 (q34 c4) ∷
   rw⁻ 44 (q32 c4) ∷
   rw 43 (q33 c4) ∷
   rw⁻ 42 (q32 c4) ∷
   rw⁻ 37 (q31 c4) ∷
   rw⁻ 36 (q32 c4) ∷
   rw 35 (q33 c4) ∷
   rw⁻ 34 (q32 c4) ∷
   rw⁻ 35 (q34 c4) ∷
   rw⁻ 38 (q32 c4) ∷
   rw 37 (q33 c4) ∷
   rw⁻ 36 (q32 c4) ∷
   rw 39 (q4 c4) ∷
   rw 40 (q4 c4) ∷
   rw 41 (q4 c4) ∷
   rw⁻ 38 (q30 c4) ∷
   rw 38 (q35 c4) ∷
   rw 38 (q36 c4) ∷
   rw 39 (q4 c4) ∷
   rw 40 (q4 c4) ∷
   rw 41 (q4 c4) ∷
   rw 42 (q4 c4) ∷
   re 38 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 39 (q37 c4) ∷
   rw 38 (q38 c4) ∷
   rw⁻ 37 (q37 c4) ∷
   rw⁻ 33 (q17 c4) ∷
   rw⁻ 36 (q39 c4) ∷
   rw 35 (q40 c4) ∷
   rw⁻ 34 (q39 c4) ∷
   rw 32 (q14 c4) ∷
   re 36 1 (CS03⁻ ∷ []) ∷
   rw⁻ 35 (q41 c4) ∷
   re 35 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 34 (q42 c4) ∷
   re 34 1 (CS03⁻ ∷ []) ∷
   rw⁻ 33 (q41 c4) ∷
   re 33 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 37 (q14 c4) ∷
   rw⁻ 36 (q15 c4) ∷
   rw 35 (q16 c4) ∷
   rw⁻ 34 (q15 c4) ∷
   rw 38 (q17 c4) ∷
   re 36 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 37 (q4 c4) ∷
   rw⁻ 40 (q4 c4) ∷
   rw⁻ 43 (q4 c4) ∷
   rw⁻ 46 (q4 c4) ∷
   re 48 1 (CS03⁻ ∷ []) ∷
   rw⁻ 47 (q18 c4) ∷
   re 49 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 44 (q19 c4) ∷
   re 42 1 (CS03 ∷ []) ∷
   rw⁻ 41 (q20 c4) ∷
   re 43 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 38 (q19 c4) ∷
   rw 36 (q21 c4) ∷
   rw 36 (q22 c4) ∷
   rw⁻ 37 (q4 c4) ∷
   rw⁻ 40 (q4 c4) ∷
   rw⁻ 43 (q4 c4) ∷
   rw⁻ 44 (q23 c4) ∷
   rw⁻ 41 (q24 c4) ∷
   rw⁻ 38 (q23 c4) ∷
   rw⁻ 35 (q24 c4) ∷
   rw 38 (q4 c4) ∷
   rw 39 (q4 c4) ∷
   rw 40 (q4 c4) ∷
   rw⁻ 37 (q22 c4) ∷
   rw 37 (q25 c4) ∷
   rw 38 (q4 c4) ∷
   rw 39 (q4 c4) ∷
   rw 40 (q4 c4) ∷
   rw 41 (q4 c4) ∷
   re 37 5 (Sb2-0-41-3 ∷ []) ∷
   re 37 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 38 (q4 c4) ∷
   rw⁻ 41 (q4 c4) ∷
   rw⁻ 44 (q4 c4) ∷
   rw⁻ 47 (q4 c4) ∷
   re 49 1 (CS03⁻ ∷ []) ∷
   rw⁻ 48 (q26 c4) ∷
   re 52 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 43 1 (CS03 ∷ []) ∷
   rw⁻ 39 (q27 c4) ∷
   re 46 1 (Sb2-0-3-1 ∷ []) ∷
   rw 37 (q28 c4) ∷
   rw 37 (q29 c4) ∷
   rw 37 (q30 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw⁻ 41 (q4 c4) ∷
   rw⁻ 44 (q4 c4) ∷
   rw⁻ 45 (q31 c4) ∷
   rw⁻ 44 (q32 c4) ∷
   rw 43 (q33 c4) ∷
   rw⁻ 42 (q32 c4) ∷
   rw⁻ 43 (q34 c4) ∷
   rw⁻ 46 (q32 c4) ∷
   rw 45 (q33 c4) ∷
   rw⁻ 44 (q32 c4) ∷
   rw⁻ 39 (q31 c4) ∷
   rw⁻ 38 (q32 c4) ∷
   rw 37 (q33 c4) ∷
   rw⁻ 36 (q32 c4) ∷
   rw⁻ 37 (q34 c4) ∷
   rw⁻ 40 (q32 c4) ∷
   rw 39 (q33 c4) ∷
   rw⁻ 38 (q32 c4) ∷
   rw 41 (q4 c4) ∷
   rw 42 (q4 c4) ∷
   rw 43 (q4 c4) ∷
   rw⁻ 40 (q30 c4) ∷
   rw 40 (q35 c4) ∷
   rw 40 (q36 c4) ∷
   rw 41 (q4 c4) ∷
   rw 42 (q4 c4) ∷
   rw 43 (q4 c4) ∷
   rw 44 (q4 c4) ∷
   re 40 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 41 (q37 c4) ∷
   rw 40 (q38 c4) ∷
   rw⁻ 39 (q37 c4) ∷
   rw⁻ 35 (q17 c4) ∷
   rw⁻ 38 (q39 c4) ∷
   rw 37 (q40 c4) ∷
   rw⁻ 36 (q39 c4) ∷
   rw 34 (q14 c4) ∷
   rw 38 (q43 c4) ∷
   rw 38 (q3 c4) ∷
   rw⁻ 37 (q44 c4) ∷
   rw 36 (q45 c4) ∷
   rw⁻ 35 (q44 c4) ∷
   re 37 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 38 (q4 c4) ∷
   rw⁻ 41 (q4 c4) ∷
   rw⁻ 44 (q4 c4) ∷
   rw⁻ 47 (q4 c4) ∷
   re 49 1 (CS03⁻ ∷ []) ∷
   rw⁻ 48 (q46 c4) ∷
   re 50 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 45 (q47 c4) ∷
   re 43 1 (CS03 ∷ []) ∷
   rw⁻ 42 (q48 c4) ∷
   re 44 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 39 (q47 c4) ∷
   rw 39 (q49 c4) ∷
   rw⁻ 38 (q50 c4) ∷
   rw 37 (q51 c4) ∷
   rw⁻ 36 (q50 c4) ∷
   rw 38 (q21 c4) ∷
   rw 38 (q52 c4) ∷
   rw 38 (q53 c4) ∷
   rw 38 (q54 c4) ∷
   rw 38 (q55 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw⁻ 42 (q4 c4) ∷
   rw⁻ 45 (q4 c4) ∷
   rw 47 (q56 c4) ∷
   rw⁻ 48 (q4 c4) ∷
   rw⁻ 51 (q4 c4) ∷
   rw⁻ 54 (q4 c4) ∷
   rw⁻ 57 (q4 c4) ∷
   rw⁻ 58 (q57 c4) ∷
   rw⁻ 55 (q58 c4) ∷
   rw⁻ 52 (q59 c4) ∷
   rw⁻ 49 (q58 c4) ∷
   rw⁻ 46 (q60 c4) ∷
   rw 49 (q4 c4) ∷
   rw 50 (q4 c4) ∷
   rw 51 (q4 c4) ∷
   rw 52 (q4 c4) ∷
   rw⁻ 48 (q56 c4) ∷
   rw⁻ 43 (q61 c4) ∷
   rw 41 (q56 c4) ∷
   rw⁻ 42 (q4 c4) ∷
   rw⁻ 45 (q4 c4) ∷
   rw⁻ 48 (q4 c4) ∷
   rw⁻ 51 (q4 c4) ∷
   rw⁻ 52 (q57 c4) ∷
   rw⁻ 49 (q58 c4) ∷
   rw⁻ 46 (q59 c4) ∷
   rw⁻ 43 (q58 c4) ∷
   rw⁻ 40 (q60 c4) ∷
   rw 43 (q4 c4) ∷
   rw 44 (q4 c4) ∷
   rw 45 (q4 c4) ∷
   rw 46 (q4 c4) ∷
   rw⁻ 42 (q56 c4) ∷
   rw⁻ 37 (q61 c4) ∷
   rw 40 (q4 c4) ∷
   rw 41 (q4 c4) ∷
   rw 42 (q4 c4) ∷
   rw⁻ 39 (q55 c4) ∷
   rw 39 (q62 c4) ∷
   rw 39 (q63 c4) ∷
   rw 39 (q64 c4) ∷
   rw 39 (q25 c4) ∷
   rw⁻ 40 (q65 c4) ∷
   rw 39 (q66 c4) ∷
   rw⁻ 38 (q65 c4) ∷
   rw 40 (q21 c4) ∷
   rw 40 (q52 c4) ∷
   rw 40 (q53 c4) ∷
   rw 40 (q54 c4) ∷
   rw 40 (q55 c4) ∷
   rw⁻ 41 (q4 c4) ∷
   rw⁻ 44 (q4 c4) ∷
   rw⁻ 47 (q4 c4) ∷
   rw 49 (q56 c4) ∷
   rw⁻ 50 (q4 c4) ∷
   rw⁻ 53 (q4 c4) ∷
   rw⁻ 56 (q4 c4) ∷
   rw⁻ 59 (q4 c4) ∷
   rw⁻ 60 (q57 c4) ∷
   rw⁻ 57 (q58 c4) ∷
   rw⁻ 54 (q59 c4) ∷
   rw⁻ 51 (q58 c4) ∷
   rw⁻ 48 (q60 c4) ∷
   rw 51 (q4 c4) ∷
   rw 52 (q4 c4) ∷
   rw 53 (q4 c4) ∷
   rw 54 (q4 c4) ∷
   rw⁻ 50 (q56 c4) ∷
   rw⁻ 45 (q61 c4) ∷
   rw 43 (q56 c4) ∷
   rw⁻ 44 (q4 c4) ∷
   rw⁻ 47 (q4 c4) ∷
   rw⁻ 50 (q4 c4) ∷
   rw⁻ 53 (q4 c4) ∷
   rw⁻ 54 (q57 c4) ∷
   rw⁻ 51 (q58 c4) ∷
   rw⁻ 48 (q59 c4) ∷
   rw⁻ 45 (q58 c4) ∷
   rw⁻ 42 (q60 c4) ∷
   rw 45 (q4 c4) ∷
   rw 46 (q4 c4) ∷
   rw 47 (q4 c4) ∷
   rw 48 (q4 c4) ∷
   rw⁻ 44 (q56 c4) ∷
   rw⁻ 39 (q61 c4) ∷
   rw 42 (q4 c4) ∷
   rw 43 (q4 c4) ∷
   rw 44 (q4 c4) ∷
   rw⁻ 41 (q55 c4) ∷
   rw 41 (q62 c4) ∷
   rw 41 (q63 c4) ∷
   rw 41 (q64 c4) ∷
   rw 41 (q25 c4) ∷
   rw 41 (q21 c4) ∷
   rw 41 (q22 c4) ∷
   rw⁻ 42 (q4 c4) ∷
   rw⁻ 45 (q4 c4) ∷
   rw⁻ 48 (q4 c4) ∷
   rw⁻ 49 (q67 c4) ∷
   rw⁻ 46 (q68 c4) ∷
   rw⁻ 43 (q67 c4) ∷
   rw⁻ 40 (q68 c4) ∷
   rw 43 (q4 c4) ∷
   rw 44 (q4 c4) ∷
   rw 45 (q4 c4) ∷
   rw⁻ 42 (q22 c4) ∷
   rw 42 (q25 c4) ∷
   rw⁻ 36 (q49 c4) ∷ []) Eq.refl
