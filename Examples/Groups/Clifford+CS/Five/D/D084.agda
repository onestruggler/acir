{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D084 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0382 ; wl0383 ; wl0384 ; wl0385 ; wl0393 ; wl0402 ; wl0403 ; wl0404 ; wl0405 ; wl0406 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0424 ; wl0425 ; wl0426 ; wl0427 ; wl0428 ; wl0429 ; wl0430 ; wl0431 ; wl0433 ; wl0434 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0444 ; wl0445 ; wl0461 ; wl0462 ; wl0463 ; wl0464 ; wp0130 ; wp0143 ; wp0146 ; wp0147 ; wp0148 ; wp0149 ; wp0150 ; wp0155 ; wp0168)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym34-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym12-at021021 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 ; lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-beta-T-at022330 ; lem-sym12-at02203443 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at0220)
open import Examples.Groups.Clifford+CS.Five.D.D044 using (lem-auto-CS01-∣-BOX⟨1·2340⟩-at0312203441 ; lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0312203441 ; lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CX41-TOFF203)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) (wl0418 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (K3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) (wl0419 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CK10⁻ ∷ []) (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ []) (wl0424 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (X1 ∷ ι⁻ ∷ []) (ι⁻ ∷ X1 ∷ []) zc⁻
  q15 : Ws → Eqn
  q15 c4 = eqn (Sb2-0-41-3 ∷ ι⁻ ∷ []) (ι⁻ ∷ Sb2-0-41-3 ∷ []) zc⁻
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ []) (wp0130 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ []) (wl0382 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ []) (wl0383 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (S1 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1 ∷ []) (wl0384 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (S1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1 ∷ []) (wl0385 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01⁻ ∷ []) (wp0146 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS01⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ []) (wl0425 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ []) (wp0147 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01⁻ ∷ []) (wl0427 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0426 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wl0431 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (K0⁻ ∷ X1 ∷ []) (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X))
  q30 : Ws → Eqn
  q30 c4 = eqn (K0⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (CCZ ↑))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01⁻ ∷ []) (wl0430 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CS01⁻ ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01⁻ ∷ []) (wl0428 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0429 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CS01⁻ ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ []) (wp0148 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0149 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0150 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym12-at021021 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1304 ∷ []) (lem-sym23-at0220 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CX13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Bx2-1304 ∷ []) (Bx2-1034 ∷ []) (lem-sym23-at022330 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1043 ∷ []) (lem-sym34-at0220 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ []) (wl0440 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CS23⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS23⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0312203441 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ []) (wl0434 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CS23 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS23 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2340⟩-at0312203441 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) (wl0443 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ123 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ []) (wl0445 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CCZ123 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0444 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ []) (wp0155 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Toff204 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Toff204 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (K3⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) (wl0405 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) (wl0406 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (CX41 ∷ Toff203 ∷ []) (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4))

-- F1 CS-K0 part39: 500 steps
lem-F1-CS-K0-part39 : Ws → ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-part39 c4 = derive (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw 16 (q3 c4) ∷
   rw 18 (q4 c4) ∷
   re 23 1 (CS03 ∷ []) ∷
   rw 21 (q5 c4) ∷
   re 22 1 (Sb2-0-3-1 ∷ []) ∷
   rw 24 (q4 c4) ∷
   re 29 1 (CS03⁻ ∷ []) ∷
   rw 27 (q6 c4) ∷
   re 28 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   re 16 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 18 (q7 c4) ∷
   rw 14 (q8 c4) ∷
   rw 15 (q9 c4) ∷
   rw 16 (q8 c4) ∷
   rw 17 (q10 c4) ∷
   re 13 1 (CS03 ∷ []) ∷
   rw 13 (q11 c4) ∷
   re 14 1 (Sb2-0-3-1 ∷ []) ∷
   rw 14 (q12 c4) ∷
   re 15 1 (CS03 ∷ []) ∷
   rw 15 (q11 c4) ∷
   re 16 1 (Sb2-0-3-1 ∷ []) ∷
   re 16 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 12 (q13 c4) ∷
   rw⁻ 18 (q14 c4) ∷
   rw⁻ 19 (q15 c4) ∷
   rw⁻ 20 (q14 c4) ∷
   re 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw 17 (q17 c4) ∷
   rw 20 (q18 c4) ∷
   rw 23 (q17 c4) ∷
   rw 26 (q18 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw 20 (q19 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   rw 23 (q20 c4) ∷
   re 24 1 (Sb2-0-3-1 ∷ []) ∷
   rw 26 (q19 c4) ∷
   re 31 1 (CS03⁻ ∷ []) ∷
   rw 29 (q21 c4) ∷
   re 30 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   re 18 5 (Sb2-0-41-3 ∷ []) ∷
   re 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw 16 (q22 c4) ∷
   rw 19 (q23 c4) ∷
   rw 22 (q22 c4) ∷
   rw 25 (q23 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw 19 (q24 c4) ∷
   re 24 1 (CS03 ∷ []) ∷
   rw 22 (q25 c4) ∷
   re 23 1 (Sb2-0-3-1 ∷ []) ∷
   rw 25 (q24 c4) ∷
   re 30 1 (CS03⁻ ∷ []) ∷
   rw 28 (q26 c4) ∷
   re 29 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   re 17 5 (Sb2-0-41-3 ∷ []) ∷
   re 17 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw 17 (q27 c4) ∷
   rw 17 (q2 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw 13 (q28 c4) ∷
   rw 18 (q29 c4) ∷
   rw 19 (q30 c4) ∷
   rw 20 (q29 c4) ∷
   rw 19 (q31 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw 17 (q32 c4) ∷
   rw 20 (q33 c4) ∷
   rw 23 (q34 c4) ∷
   rw 26 (q33 c4) ∷
   rw 29 (q35 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw⁻ 18 (q31 c4) ∷
   rw 16 (q29 c4) ∷
   rw 17 (q30 c4) ∷
   rw 18 (q29 c4) ∷
   rw 19 (q28 c4) ∷
   rw 24 (q29 c4) ∷
   rw 25 (q30 c4) ∷
   rw 26 (q29 c4) ∷
   rw 25 (q31 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw 23 (q32 c4) ∷
   rw 26 (q33 c4) ∷
   rw 29 (q34 c4) ∷
   rw 32 (q33 c4) ∷
   rw 35 (q35 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw⁻ 24 (q31 c4) ∷
   rw 22 (q29 c4) ∷
   rw 23 (q30 c4) ∷
   rw 24 (q29 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw⁻ 14 (q2 c4) ∷
   rw 14 (q3 c4) ∷
   rw 16 (q36 c4) ∷
   re 23 1 (CS03 ∷ []) ∷
   re 29 1 (CS03⁻ ∷ []) ∷
   rw 19 (q37 c4) ∷
   re 20 1 (Sb2-0-3-1 ∷ []) ∷
   re 26 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   re 14 5 (Sb2-0-41-3 ∷ []) ∷
   re 14 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw 14 (q16 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw 12 (q22 c4) ∷
   rw 15 (q23 c4) ∷
   rw 18 (q22 c4) ∷
   rw 21 (q23 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw 15 (q24 c4) ∷
   re 20 1 (CS03 ∷ []) ∷
   rw 18 (q25 c4) ∷
   re 19 1 (Sb2-0-3-1 ∷ []) ∷
   rw 21 (q24 c4) ∷
   re 26 1 (CS03⁻ ∷ []) ∷
   rw 24 (q26 c4) ∷
   re 25 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   re 13 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 15 (q13 c4) ∷
   re 11 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw 15 (q38 c4) ∷
   rw 15 (q16 c4) ∷
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw 18 (q39 c4) ∷
   rw 24 (q27 c4) ∷
   rw 24 (q2 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw 22 (q40 c4) ∷
   rw 25 (q41 c4) ∷
   rw 28 (q40 c4) ∷
   rw 31 (q41 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw 23 (q3 c4) ∷
   rw 23 (q27 c4) ∷
   rw 23 (q42 c4) ∷
   rw 23 (q43 c4) ∷
   rw 23 (q44 c4) ∷
   rw 23 (q45 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw 21 (q46 c4) ∷
   rw 26 (q47 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw 24 (q48 c4) ∷
   rw 27 (q49 c4) ∷
   rw 30 (q50 c4) ∷
   rw 33 (q49 c4) ∷
   rw 36 (q51 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw⁻ 25 (q47 c4) ∷
   rw 27 (q46 c4) ∷
   rw 32 (q47 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw 30 (q48 c4) ∷
   rw 33 (q49 c4) ∷
   rw 36 (q50 c4) ∷
   rw 39 (q49 c4) ∷
   rw 42 (q51 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw⁻ 31 (q47 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw⁻ 22 (q45 c4) ∷
   rw 22 (q52 c4) ∷
   rw 22 (q53 c4) ∷
   rw 22 (q54 c4) ∷
   rw 22 (q3 c4) ∷
   rw 20 (q55 c4) ∷
   rw 21 (q56 c4) ∷
   rw 22 (q55 c4) ∷
   rw 21 (q27 c4) ∷
   rw 21 (q42 c4) ∷
   rw 21 (q43 c4) ∷
   rw 21 (q44 c4) ∷
   rw 21 (q45 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw 19 (q46 c4) ∷
   rw 24 (q47 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw 22 (q48 c4) ∷
   rw 25 (q49 c4) ∷
   rw 28 (q50 c4) ∷
   rw 31 (q49 c4) ∷
   rw 34 (q51 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw⁻ 23 (q47 c4) ∷
   rw 25 (q46 c4) ∷
   rw 30 (q47 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw 28 (q48 c4) ∷
   rw 31 (q49 c4) ∷
   rw 34 (q50 c4) ∷
   rw 37 (q49 c4) ∷
   rw 40 (q51 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw⁻ 29 (q47 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw⁻ 20 (q45 c4) ∷
   rw 20 (q52 c4) ∷
   rw 20 (q53 c4) ∷
   rw 20 (q54 c4) ∷
   rw 20 (q3 c4) ∷
   rw 18 (q57 c4) ∷
   rw 19 (q58 c4) ∷
   rw 20 (q57 c4) ∷
   rw⁻ 21 (q39 c4) ∷
   rw 21 (q59 c4) ∷
   re 26 1 (CS03 ∷ []) ∷
   rw 24 (q60 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   rw 27 (q59 c4) ∷
   re 32 1 (CS03⁻ ∷ []) ∷
   rw 30 (q61 c4) ∷
   re 31 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   re 19 5 (Sb2-0-41-3 ∷ []) ∷
   rw 17 (q62 c4) ∷
   rw 18 (q63 c4) ∷
   rw 19 (q62 c4) ∷
   re 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw 16 (q39 c4) ∷
   rw 22 (q27 c4) ∷
   rw 22 (q2 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw 20 (q40 c4) ∷
   rw 23 (q41 c4) ∷
   rw 26 (q40 c4) ∷
   rw 29 (q41 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw 21 (q3 c4) ∷
   rw 21 (q27 c4) ∷
   rw 21 (q42 c4) ∷
   rw 21 (q43 c4) ∷
   rw 21 (q44 c4) ∷
   rw 21 (q45 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw 19 (q46 c4) ∷
   rw 24 (q47 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw 22 (q48 c4) ∷
   rw 25 (q49 c4) ∷
   rw 28 (q50 c4) ∷
   rw 31 (q49 c4) ∷
   rw 34 (q51 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw⁻ 23 (q47 c4) ∷
   rw 25 (q46 c4) ∷
   rw 30 (q47 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw 28 (q48 c4) ∷
   rw 31 (q49 c4) ∷
   rw 34 (q50 c4) ∷
   rw 37 (q49 c4) ∷
   rw 40 (q51 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw⁻ 29 (q47 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw⁻ 20 (q45 c4) ∷
   rw 20 (q52 c4) ∷
   rw 20 (q53 c4) ∷
   rw 20 (q54 c4) ∷
   rw 20 (q3 c4) ∷
   rw 18 (q55 c4) ∷
   rw 19 (q56 c4) ∷
   rw 20 (q55 c4) ∷
   rw 19 (q27 c4) ∷
   rw 19 (q42 c4) ∷
   rw 19 (q43 c4) ∷
   rw 19 (q44 c4) ∷
   rw 19 (q45 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw 17 (q46 c4) ∷
   rw 22 (q47 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw 20 (q48 c4) ∷
   rw 23 (q49 c4) ∷
   rw 26 (q50 c4) ∷
   rw 29 (q49 c4) ∷
   rw 32 (q51 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw⁻ 21 (q47 c4) ∷
   rw 23 (q46 c4) ∷
   rw 28 (q47 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw 26 (q48 c4) ∷
   rw 29 (q49 c4) ∷
   rw 32 (q50 c4) ∷
   rw 35 (q49 c4) ∷
   rw 38 (q51 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw⁻ 27 (q47 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw⁻ 18 (q45 c4) ∷
   rw 18 (q52 c4) ∷
   rw 18 (q53 c4) ∷
   rw 18 (q54 c4) ∷
   rw 18 (q3 c4) ∷
   rw 16 (q57 c4) ∷
   rw 17 (q58 c4) ∷
   rw 18 (q57 c4) ∷
   rw⁻ 19 (q39 c4) ∷
   rw 19 (q59 c4) ∷
   re 24 1 (CS03 ∷ []) ∷
   rw 22 (q60 c4) ∷
   re 23 1 (Sb2-0-3-1 ∷ []) ∷
   rw 25 (q59 c4) ∷
   re 30 1 (CS03⁻ ∷ []) ∷
   rw 28 (q61 c4) ∷
   re 29 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   re 17 5 (Sb2-0-41-3 ∷ []) ∷
   rw 15 (q62 c4) ∷
   rw 16 (q63 c4) ∷
   rw 17 (q62 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 18 (q38 c4) ∷
   rw⁻ 14 (q10 c4) ∷
   rw 16 (q64 c4) ∷
   rw 17 (q65 c4) ∷
   rw 18 (q64 c4) ∷
   rw 15 (q7 c4) ∷
   rw 19 (q66 c4) ∷
   rw 20 (q67 c4) ∷
   rw 21 (q66 c4) ∷
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw 20 (q68 c4) ∷
   rw 20 (q69 c4) ∷
   rw 20 (q70 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw 18 (q71 c4) ∷
   rw 19 (q72 c4) ∷ []) Eq.refl
