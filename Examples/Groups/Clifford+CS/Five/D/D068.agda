{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D068 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0386 ; wl0401 ; wl0402 ; wl0403 ; wl0404 ; wl0405 ; wl0406 ; wl0407 ; wl0408 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0433 ; wl0434 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0444 ; wl0445 ; wl0454 ; wl0455 ; wl0461 ; wl0462 ; wl0463 ; wl0464 ; wp0131 ; wp0132 ; wp0140 ; wp0141 ; wp0143 ; wp0155 ; wp0168)
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
  q1 c4 = eqn (CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CX13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx2-1304 ∷ []) (Bx2-1034 ∷ []) (lem-sym23-at022330 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1043 ∷ []) (lem-sym34-at0220 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0131 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Toff314 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff314 ∷ []) (wp0132 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Toff201 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff201 ∷ []) (wl0386 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (X1 ∷ CCZ234 ∷ []) (CCZ234 ∷ X1 ∷ []) (c₂ (X ↑) (CCZ))
  q24 : Ws → Eqn
  q24 c4 = eqn (CK10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK10 ∷ []) (c₂ (CK₁₀) (CCZ))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) (wl0419 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) (wl0418 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Sb2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) (wl0454 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) (wl0455 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0141 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0140 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) (wl0406 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (Toff203 ∷ CX41 ∷ []) (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) (wl0405 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Sb2-0-41-3 ∷ CS34 ∷ []) (CS34 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (Sb2-0-41-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ []) (wl0401 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ []) (wp0155 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Sb2-0-41-3 ∷ Toff204 ∷ []) (Toff204 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at0210243143 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ123 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0444 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) (wl0443 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ123 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ []) (wl0445 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ []) (wl0434 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS40-at0210243143 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym12-at021021 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1304 ∷ []) (lem-sym23-at0220 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ []) (wl0440 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (Bx2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143 c4)

-- F1 CS-K0 part23: 360 steps
lem-F1-CS-K0-part23 : Ws → ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ
lem-F1-CS-K0-part23 c4 = derive (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  (rw⁻ 46 (q1 c4) ∷
   rw 49 (q2 c4) ∷
   rw 50 (q2 c4) ∷
   rw 51 (q2 c4) ∷
   rw 52 (q2 c4) ∷
   rw⁻ 48 (q3 c4) ∷
   rw⁻ 43 (q4 c4) ∷
   rw 41 (q3 c4) ∷
   rw⁻ 42 (q2 c4) ∷
   rw⁻ 45 (q2 c4) ∷
   rw⁻ 48 (q2 c4) ∷
   rw⁻ 51 (q2 c4) ∷
   rw⁻ 52 (q5 c4) ∷
   rw⁻ 49 (q6 c4) ∷
   rw⁻ 46 (q7 c4) ∷
   rw⁻ 43 (q6 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw 43 (q2 c4) ∷
   rw 44 (q2 c4) ∷
   rw 45 (q2 c4) ∷
   rw 46 (q2 c4) ∷
   rw⁻ 42 (q3 c4) ∷
   rw⁻ 37 (q4 c4) ∷
   rw 40 (q2 c4) ∷
   rw 41 (q2 c4) ∷
   rw 42 (q2 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw 39 (q9 c4) ∷
   rw 39 (q10 c4) ∷
   rw 39 (q11 c4) ∷
   rw 39 (q12 c4) ∷
   rw 39 (q13 c4) ∷
   rw 39 (q14 c4) ∷
   rw⁻ 40 (q2 c4) ∷
   rw⁻ 43 (q2 c4) ∷
   rw⁻ 46 (q2 c4) ∷
   rw⁻ 47 (q15 c4) ∷
   rw⁻ 44 (q16 c4) ∷
   rw⁻ 41 (q15 c4) ∷
   rw⁻ 38 (q16 c4) ∷
   rw 41 (q2 c4) ∷
   rw 42 (q2 c4) ∷
   rw 43 (q2 c4) ∷
   rw⁻ 40 (q14 c4) ∷
   rw 40 (q12 c4) ∷
   rw⁻ 34 (q17 c4) ∷
   rw 37 (q2 c4) ∷
   rw 38 (q2 c4) ∷
   rw 39 (q2 c4) ∷
   rw 40 (q2 c4) ∷
   re 36 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 31 (q18 c4) ∷
   rw⁻ 31 (q19 c4) ∷
   re 27 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 27 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 27 1 (CS03 ∷ []) ∷
   re 29 1 (CS03⁻ ∷ []) ∷
   rw⁻ 24 (q20 c4) ∷
   re 24 1 (Sb2-0-3-1 ∷ []) ∷
   re 26 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 27 (q21 c4) ∷
   rw 31 (q19 c4) ∷
   rw 31 (q13 c4) ∷
   rw 31 (q14 c4) ∷
   rw⁻ 28 (q22 c4) ∷
   rw 31 (q23 c4) ∷
   rw 30 (q24 c4) ∷
   rw 29 (q23 c4) ∷
   rw⁻ 30 (q22 c4) ∷
   rw 33 (q23 c4) ∷
   rw 32 (q24 c4) ∷
   rw 31 (q23 c4) ∷
   rw⁻ 28 (q14 c4) ∷
   rw 28 (q12 c4) ∷
   rw⁻ 28 (q19 c4) ∷
   re 24 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 24 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 24 1 (CS03 ∷ []) ∷
   rw⁻ 23 (q25 c4) ∷
   re 23 1 (Sb2-0-3-1 ∷ []) ∷
   rw 22 (q26 c4) ∷
   re 22 1 (CS03 ∷ []) ∷
   rw⁻ 21 (q25 c4) ∷
   re 21 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q27 c4) ∷
   rw⁻ 24 (q28 c4) ∷
   rw 23 (q29 c4) ∷
   rw⁻ 22 (q28 c4) ∷
   rw 26 (q30 c4) ∷
   re 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   re 36 1 (CS03⁻ ∷ []) ∷
   rw⁻ 35 (q31 c4) ∷
   re 37 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q32 c4) ∷
   re 30 1 (CS03 ∷ []) ∷
   rw⁻ 29 (q33 c4) ∷
   re 31 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q32 c4) ∷
   rw 24 (q13 c4) ∷
   rw 24 (q14 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 32 (q34 c4) ∷
   rw⁻ 29 (q35 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw⁻ 23 (q35 c4) ∷
   rw 26 (q2 c4) ∷
   rw 27 (q2 c4) ∷
   rw 28 (q2 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw 25 (q12 c4) ∷
   rw 26 (q2 c4) ∷
   rw 27 (q2 c4) ∷
   rw 28 (q2 c4) ∷
   rw 29 (q2 c4) ∷
   re 25 5 (Sb2-0-41-3 ∷ []) ∷
   re 25 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   re 37 1 (CS03⁻ ∷ []) ∷
   rw⁻ 36 (q36 c4) ∷
   re 40 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 31 1 (CS03 ∷ []) ∷
   rw⁻ 27 (q37 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ []) ∷
   rw 25 (q38 c4) ∷
   rw 25 (q39 c4) ∷
   rw 25 (q40 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 33 (q41 c4) ∷
   rw⁻ 32 (q42 c4) ∷
   rw 31 (q43 c4) ∷
   rw⁻ 30 (q42 c4) ∷
   rw⁻ 31 (q44 c4) ∷
   rw⁻ 34 (q42 c4) ∷
   rw 33 (q43 c4) ∷
   rw⁻ 32 (q42 c4) ∷
   rw⁻ 27 (q41 c4) ∷
   rw⁻ 26 (q42 c4) ∷
   rw 25 (q43 c4) ∷
   rw⁻ 24 (q42 c4) ∷
   rw⁻ 25 (q44 c4) ∷
   rw⁻ 28 (q42 c4) ∷
   rw 27 (q43 c4) ∷
   rw⁻ 26 (q42 c4) ∷
   rw 29 (q2 c4) ∷
   rw 30 (q2 c4) ∷
   rw 31 (q2 c4) ∷
   rw⁻ 28 (q40 c4) ∷
   rw 28 (q45 c4) ∷
   rw 28 (q46 c4) ∷
   rw 29 (q2 c4) ∷
   rw 30 (q2 c4) ∷
   rw 31 (q2 c4) ∷
   rw 32 (q2 c4) ∷
   re 28 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 29 (q47 c4) ∷
   rw 28 (q48 c4) ∷
   rw⁻ 27 (q47 c4) ∷
   rw⁻ 23 (q30 c4) ∷
   rw⁻ 26 (q49 c4) ∷
   rw 25 (q50 c4) ∷
   rw⁻ 24 (q49 c4) ∷
   rw 22 (q27 c4) ∷
   re 26 1 (CS03⁻ ∷ []) ∷
   rw⁻ 25 (q51 c4) ∷
   re 25 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 24 (q52 c4) ∷
   re 24 1 (CS03⁻ ∷ []) ∷
   rw⁻ 23 (q51 c4) ∷
   re 23 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 27 (q27 c4) ∷
   rw⁻ 26 (q28 c4) ∷
   rw 25 (q29 c4) ∷
   rw⁻ 24 (q28 c4) ∷
   rw 28 (q30 c4) ∷
   re 26 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 30 (q2 c4) ∷
   rw⁻ 33 (q2 c4) ∷
   rw⁻ 36 (q2 c4) ∷
   re 38 1 (CS03⁻ ∷ []) ∷
   rw⁻ 37 (q31 c4) ∷
   re 39 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 34 (q32 c4) ∷
   re 32 1 (CS03 ∷ []) ∷
   rw⁻ 31 (q33 c4) ∷
   re 33 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 28 (q32 c4) ∷
   rw 26 (q13 c4) ∷
   rw 26 (q14 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 30 (q2 c4) ∷
   rw⁻ 33 (q2 c4) ∷
   rw⁻ 34 (q34 c4) ∷
   rw⁻ 31 (q35 c4) ∷
   rw⁻ 28 (q34 c4) ∷
   rw⁻ 25 (q35 c4) ∷
   rw 28 (q2 c4) ∷
   rw 29 (q2 c4) ∷
   rw 30 (q2 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw 27 (q12 c4) ∷
   rw 28 (q2 c4) ∷
   rw 29 (q2 c4) ∷
   rw 30 (q2 c4) ∷
   rw 31 (q2 c4) ∷
   re 27 5 (Sb2-0-41-3 ∷ []) ∷
   re 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 37 (q2 c4) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   rw⁻ 38 (q36 c4) ∷
   re 42 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 33 1 (CS03 ∷ []) ∷
   rw⁻ 29 (q37 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ []) ∷
   rw 27 (q38 c4) ∷
   rw 27 (q39 c4) ∷
   rw 27 (q40 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 35 (q41 c4) ∷
   rw⁻ 34 (q42 c4) ∷
   rw 33 (q43 c4) ∷
   rw⁻ 32 (q42 c4) ∷
   rw⁻ 33 (q44 c4) ∷
   rw⁻ 36 (q42 c4) ∷
   rw 35 (q43 c4) ∷
   rw⁻ 34 (q42 c4) ∷
   rw⁻ 29 (q41 c4) ∷
   rw⁻ 28 (q42 c4) ∷
   rw 27 (q43 c4) ∷
   rw⁻ 26 (q42 c4) ∷
   rw⁻ 27 (q44 c4) ∷
   rw⁻ 30 (q42 c4) ∷
   rw 29 (q43 c4) ∷
   rw⁻ 28 (q42 c4) ∷
   rw 31 (q2 c4) ∷
   rw 32 (q2 c4) ∷
   rw 33 (q2 c4) ∷
   rw⁻ 30 (q40 c4) ∷
   rw 30 (q45 c4) ∷
   rw 30 (q46 c4) ∷
   rw 31 (q2 c4) ∷
   rw 32 (q2 c4) ∷
   rw 33 (q2 c4) ∷
   rw 34 (q2 c4) ∷
   re 30 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 31 (q47 c4) ∷
   rw 30 (q48 c4) ∷
   rw⁻ 29 (q47 c4) ∷
   rw⁻ 25 (q30 c4) ∷
   rw⁻ 28 (q49 c4) ∷
   rw 27 (q50 c4) ∷
   rw⁻ 26 (q49 c4) ∷
   rw 24 (q27 c4) ∷
   rw 28 (q19 c4) ∷
   rw 28 (q18 c4) ∷
   rw⁻ 27 (q53 c4) ∷
   rw 26 (q54 c4) ∷
   rw⁻ 25 (q53 c4) ∷
   re 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 37 (q2 c4) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   rw⁻ 38 (q55 c4) ∷
   re 40 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 35 (q56 c4) ∷
   re 33 1 (CS03 ∷ []) ∷
   rw⁻ 32 (q57 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 29 (q56 c4) ∷
   rw 29 (q17 c4) ∷
   rw⁻ 28 (q58 c4) ∷
   rw 27 (q59 c4) ∷
   rw⁻ 26 (q58 c4) ∷
   rw 28 (q13 c4) ∷
   rw 28 (q60 c4) ∷
   rw 28 (q61 c4) ∷
   rw 28 (q62 c4) ∷
   rw 28 (q8 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   rw 37 (q3 c4) ∷
   rw⁻ 38 (q2 c4) ∷
   rw⁻ 41 (q2 c4) ∷
   rw⁻ 44 (q2 c4) ∷
   rw⁻ 47 (q2 c4) ∷
   rw⁻ 48 (q5 c4) ∷
   rw⁻ 45 (q6 c4) ∷
   rw⁻ 42 (q7 c4) ∷
   rw⁻ 39 (q6 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw 39 (q2 c4) ∷
   rw 40 (q2 c4) ∷
   rw 41 (q2 c4) ∷
   rw 42 (q2 c4) ∷
   rw⁻ 38 (q3 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw 31 (q3 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   rw⁻ 38 (q2 c4) ∷
   rw⁻ 41 (q2 c4) ∷
   rw⁻ 42 (q5 c4) ∷
   rw⁻ 39 (q6 c4) ∷
   rw⁻ 36 (q7 c4) ∷
   rw⁻ 33 (q6 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw 33 (q2 c4) ∷
   rw 34 (q2 c4) ∷
   rw 35 (q2 c4) ∷
   rw 36 (q2 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw 30 (q2 c4) ∷
   rw 31 (q2 c4) ∷
   rw 32 (q2 c4) ∷
   rw⁻ 29 (q8 c4) ∷
   rw 29 (q9 c4) ∷
   rw 29 (q10 c4) ∷
   rw 29 (q11 c4) ∷
   rw 29 (q12 c4) ∷
   rw⁻ 30 (q63 c4) ∷
   rw 29 (q64 c4) ∷
   rw⁻ 28 (q63 c4) ∷
   rw 30 (q13 c4) ∷
   rw 30 (q60 c4) ∷
   rw 30 (q61 c4) ∷
   rw 30 (q62 c4) ∷
   rw 30 (q8 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 37 (q2 c4) ∷
   rw 39 (q3 c4) ∷
   rw⁻ 40 (q2 c4) ∷
   rw⁻ 43 (q2 c4) ∷
   rw⁻ 46 (q2 c4) ∷
   rw⁻ 49 (q2 c4) ∷
   rw⁻ 50 (q5 c4) ∷
   rw⁻ 47 (q6 c4) ∷
   rw⁻ 44 (q7 c4) ∷
   rw⁻ 41 (q6 c4) ∷
   rw⁻ 38 (q1 c4) ∷ []) Eq.refl
