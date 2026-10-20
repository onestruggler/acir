{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D009 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0380 ; wl0381 ; wl0382 ; wl0383 ; wl0384 ; wl0385 ; wl0393 ; wl0402 ; wl0404 ; wl0409 ; wl0410 ; wl0411 ; wl0412 ; wl0413 ; wl0414 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0421 ; wl0422 ; wl0423 ; wl0424 ; wl0425 ; wl0426 ; wl0427 ; wl0428 ; wl0429 ; wl0430 ; wl0431 ; wl0432 ; wp0024 ; wp0060 ; wp0114 ; wp0127 ; wp0128 ; wp0129 ; wp0130 ; wp0142 ; wp0143 ; wp0144 ; wp0145 ; wp0146 ; wp0147 ; wp0148 ; wp0149 ; wp0150 ; wp0151 ; wp0152)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-F5d-CS01-at1441 ; lem-SBsymd-at1441 ; lem-X1-beta-at02203443 ; lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 ; lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 ; lem-beta-T-at0210213443 ; lem-sym12-at0210213443 ; lem-sym12-at02203443)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (Toff204 ∷ []) (wp0142 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CS13 ∷ X1 ∷ K2 ∷ X1 ∷ []) (X1 ∷ K2 ∷ X1 ∷ CS13 ∷ []) (wl0409 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS13 ∷ []) (wl0410 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CS13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CS13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CS13 ∷ []) (wl0411 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CS13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ []) (wl0412 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ []) (X1 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ []) (wl0413 (lit c4))
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
  q38 c4 = eqn (CK40⁻ ∷ []) (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ S4 ∷ ι⁻ ∷ []) (wp0145 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CS04⁻ ∷ []) (CS04⁻ ∷ []) (wp0114 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS04⁻ ∷ []) (Sb⁻2-0-14-3 ∷ X1 ∷ Sb⁻2-0-14-3 ∷ X1 ∷ []) (lem-F5d-CS01-at1441 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Sb⁻2-0-14-3 ∷ []) (Sb⁻2-0-41-3 ∷ []) (lem-SBsymd-at1441 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (K0⁻ ∷ []) (wl0421 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (S4 ∷ []) (X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ []) (wl0422 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ []) (ι⁻ ∷ []) (wl0423 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CK10⁻ ∷ []) (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ []) (wl0424 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CS01⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ []) (wl0425 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01⁻ ∷ []) (wp0146 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ []) (wp0147 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0426 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01⁻ ∷ []) (wl0427 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (K0⁻ ∷ X1 ∷ []) (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X))
  q54 : Ws → Eqn
  q54 c4 = eqn (K0⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (CCZ ↑))
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CS01⁻ ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ []) (wp0148 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CS01⁻ ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01⁻ ∷ []) (wl0428 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0429 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01⁻ ∷ []) (wl0430 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wl0431 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0149 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0150 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (X1 ∷ ι⁻ ∷ []) (ι⁻ ∷ X1 ∷ []) (zc⁻)
  q64 : Ws → Eqn
  q64 c4 = eqn (Sb⁻2-0-41-3 ∷ ι⁻ ∷ []) (ι⁻ ∷ Sb⁻2-0-41-3 ∷ []) (zc⁻)
  q65 : Ws → Eqn
  q65 c4 = eqn (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0151 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Toff314 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ Toff314 ∷ []) (wp0152 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (Toff201 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ Toff201 ∷ []) (wl0432 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (X1 ∷ CCZ234 ∷ []) (CCZ234 ∷ X1 ∷ []) (c₂ (X ↑) (CCZ))
  q69 : Ws → Eqn
  q69 c4 = eqn (CK10⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CK10⁻ ∷ []) (c₂ (S ↑ • CK₁₀) (CCZ))
  q70 : Ws → Eqn
  q70 c4 = eqn (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) (wl0419 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (Sb⁻2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (Sb⁻2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 c4)

-- F1 CS-K0 [rhs shape] part3: 421 steps
lem-F1-CS-K0-rhs-shape-part3 : Ws → ⟪ (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ K2 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-rhs-shape-part3 c4 = derive (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ K2 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 25 (q1 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw 23 (q3 c4) ∷
   rw 28 (q4 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   rw⁻ 38 (q2 c4) ∷
   rw 26 (q5 c4) ∷
   rw 29 (q6 c4) ∷
   rw 32 (q7 c4) ∷
   rw 35 (q6 c4) ∷
   rw 38 (q8 c4) ∷
   rw 28 (q2 c4) ∷
   rw 29 (q2 c4) ∷
   rw 30 (q2 c4) ∷
   rw 31 (q2 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw 29 (q9 c4) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q2 c4) ∷
   rw 24 (q1 c4) ∷
   rw 26 (q10 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   rw 29 (q3 c4) ∷
   rw 34 (q4 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   rw⁻ 38 (q2 c4) ∷
   rw⁻ 41 (q2 c4) ∷
   rw⁻ 44 (q2 c4) ∷
   rw 32 (q5 c4) ∷
   rw 35 (q6 c4) ∷
   rw 38 (q7 c4) ∷
   rw 41 (q6 c4) ∷
   rw 44 (q8 c4) ∷
   rw 34 (q2 c4) ∷
   rw 35 (q2 c4) ∷
   rw 36 (q2 c4) ∷
   rw 37 (q2 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw 35 (q9 c4) ∷
   rw 31 (q2 c4) ∷
   rw 32 (q2 c4) ∷
   rw 30 (q1 c4) ∷
   rw 32 (q10 c4) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q2 c4) ∷
   rw 27 (q2 c4) ∷
   rw⁻ 24 (q11 c4) ∷
   rw 26 (q12 c4) ∷
   re 31 1 (CS03 ∷ []) ∷
   rw 29 (q13 c4) ∷
   re 30 1 (Sb2-0-3-1 ∷ []) ∷
   rw 32 (q12 c4) ∷
   re 37 1 (CS03⁻ ∷ []) ∷
   rw 35 (q14 c4) ∷
   re 36 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q2 c4) ∷
   rw 27 (q2 c4) ∷
   rw 28 (q2 c4) ∷
   re 24 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 26 (q15 c4) ∷
   rw 22 (q16 c4) ∷
   rw 23 (q17 c4) ∷
   rw 24 (q16 c4) ∷
   rw 25 (q18 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw 23 (q19 c4) ∷
   rw 23 (q20 c4) ∷
   rw 22 (q21 c4) ∷
   rw 23 (q22 c4) ∷
   rw 23 (q23 c4) ∷
   rw 23 (q24 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw 26 (q19 c4) ∷
   rw 26 (q20 c4) ∷
   rw 25 (q21 c4) ∷
   rw 26 (q22 c4) ∷
   rw 26 (q23 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw⁻ 24 (q25 c4) ∷
   rw 23 (q26 c4) ∷
   rw⁻ 22 (q25 c4) ∷
   rw 21 (q27 c4) ∷
   re 24 5 (Sb2-0-41-3 ∷ []) ∷
   re 22 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw 22 (q11 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw 20 (q28 c4) ∷
   rw 23 (q29 c4) ∷
   rw 26 (q28 c4) ∷
   rw 29 (q29 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw 24 (q2 c4) ∷
   rw⁻ 21 (q11 c4) ∷
   rw 23 (q30 c4) ∷
   re 28 1 (CS03 ∷ []) ∷
   rw 26 (q31 c4) ∷
   re 27 1 (Sb2-0-3-1 ∷ []) ∷
   rw 29 (q30 c4) ∷
   re 34 1 (CS03⁻ ∷ []) ∷
   rw 32 (q32 c4) ∷
   re 33 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw 24 (q2 c4) ∷
   rw 25 (q2 c4) ∷
   re 21 5 (Sb2-0-41-3 ∷ []) ∷
   re 21 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw 21 (q11 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw 19 (q33 c4) ∷
   rw 22 (q34 c4) ∷
   rw 25 (q33 c4) ∷
   rw 28 (q34 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw 22 (q35 c4) ∷
   re 27 1 (CS03 ∷ []) ∷
   rw 25 (q36 c4) ∷
   re 26 1 (Sb2-0-3-1 ∷ []) ∷
   rw 28 (q35 c4) ∷
   re 33 1 (CS03⁻ ∷ []) ∷
   rw 31 (q37 c4) ∷
   re 32 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw 24 (q2 c4) ∷
   re 20 5 (Sb2-0-41-3 ∷ []) ∷
   rw 30 (q38 c4) ∷
   rw 30 (q39 c4) ∷
   rw 30 (q40 c4) ∷
   rw 30 (q41 c4) ∷
   rw 32 (q41 c4) ∷
   rw⁻ 34 (q42 c4) ∷
   rw 38 (q39 c4) ∷
   rw 38 (q40 c4) ∷
   rw 38 (q41 c4) ∷
   rw 40 (q41 c4) ∷
   rw⁻ 42 (q42 c4) ∷
   rw 46 (q39 c4) ∷
   rw 46 (q40 c4) ∷
   rw 46 (q41 c4) ∷
   rw 48 (q41 c4) ∷
   rw 50 (q43 c4) ∷
   rw⁻ 54 (q44 c4) ∷
   rw 34 (q45 c4) ∷
   re 32 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 33 (q2 c4) ∷
   rw⁻ 36 (q2 c4) ∷
   rw⁻ 39 (q2 c4) ∷
   rw⁻ 42 (q2 c4) ∷
   rw 44 (q46 c4) ∷
   rw 44 (q11 c4) ∷
   rw⁻ 45 (q2 c4) ∷
   rw⁻ 48 (q2 c4) ∷
   rw⁻ 51 (q2 c4) ∷
   rw⁻ 52 (q47 c4) ∷
   rw⁻ 49 (q48 c4) ∷
   rw⁻ 46 (q47 c4) ∷
   rw⁻ 43 (q48 c4) ∷
   rw 46 (q2 c4) ∷
   rw 47 (q2 c4) ∷
   rw 48 (q2 c4) ∷
   rw⁻ 45 (q11 c4) ∷
   rw⁻ 45 (q46 c4) ∷
   rw⁻ 40 (q49 c4) ∷
   re 38 1 (CS03⁻ ∷ []) ∷
   rw⁻ 37 (q50 c4) ∷
   re 39 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 34 (q49 c4) ∷
   re 32 1 (CS03 ∷ []) ∷
   rw⁻ 31 (q51 c4) ∷
   re 33 1 (Sb2-0-3-1 ∷ []) ∷
   rw 34 (q2 c4) ∷
   rw 35 (q2 c4) ∷
   rw 36 (q2 c4) ∷
   rw 37 (q2 c4) ∷
   re 33 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 33 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 37 (q2 c4) ∷
   rw⁻ 40 (q2 c4) ∷
   rw⁻ 43 (q2 c4) ∷
   rw 45 (q46 c4) ∷
   rw 45 (q19 c4) ∷
   rw 45 (q52 c4) ∷
   rw⁻ 46 (q2 c4) ∷
   rw⁻ 49 (q2 c4) ∷
   rw⁻ 52 (q2 c4) ∷
   rw⁻ 55 (q53 c4) ∷
   rw⁻ 54 (q54 c4) ∷
   rw⁻ 53 (q53 c4) ∷
   rw 55 (q55 c4) ∷
   rw⁻ 56 (q2 c4) ∷
   rw⁻ 59 (q2 c4) ∷
   rw⁻ 62 (q2 c4) ∷
   rw⁻ 65 (q2 c4) ∷
   rw⁻ 66 (q56 c4) ∷
   rw⁻ 63 (q57 c4) ∷
   rw⁻ 60 (q58 c4) ∷
   rw⁻ 57 (q57 c4) ∷
   rw⁻ 54 (q59 c4) ∷
   rw 57 (q2 c4) ∷
   rw 58 (q2 c4) ∷
   rw 59 (q2 c4) ∷
   rw 60 (q2 c4) ∷
   rw⁻ 56 (q55 c4) ∷
   rw⁻ 57 (q53 c4) ∷
   rw⁻ 56 (q54 c4) ∷
   rw⁻ 55 (q53 c4) ∷
   rw⁻ 50 (q60 c4) ∷
   rw⁻ 49 (q53 c4) ∷
   rw⁻ 48 (q54 c4) ∷
   rw⁻ 47 (q53 c4) ∷
   rw 49 (q55 c4) ∷
   rw⁻ 50 (q2 c4) ∷
   rw⁻ 53 (q2 c4) ∷
   rw⁻ 56 (q2 c4) ∷
   rw⁻ 59 (q2 c4) ∷
   rw⁻ 60 (q56 c4) ∷
   rw⁻ 57 (q57 c4) ∷
   rw⁻ 54 (q58 c4) ∷
   rw⁻ 51 (q57 c4) ∷
   rw⁻ 48 (q59 c4) ∷
   rw 51 (q2 c4) ∷
   rw 52 (q2 c4) ∷
   rw 53 (q2 c4) ∷
   rw 54 (q2 c4) ∷
   rw⁻ 50 (q55 c4) ∷
   rw⁻ 51 (q53 c4) ∷
   rw⁻ 50 (q54 c4) ∷
   rw⁻ 49 (q53 c4) ∷
   rw⁻ 44 (q60 c4) ∷
   rw 49 (q2 c4) ∷
   rw 50 (q2 c4) ∷
   rw 51 (q2 c4) ∷
   rw⁻ 48 (q52 c4) ∷
   rw 48 (q23 c4) ∷
   rw⁻ 48 (q46 c4) ∷
   rw⁻ 41 (q61 c4) ∷
   re 33 1 (CS03 ∷ []) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   rw⁻ 32 (q62 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ []) ∷
   re 42 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 37 (q2 c4) ∷
   rw 38 (q2 c4) ∷
   rw 39 (q2 c4) ∷
   rw 40 (q2 c4) ∷
   re 36 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 36 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 37 (q2 c4) ∷
   rw⁻ 40 (q2 c4) ∷
   rw⁻ 43 (q2 c4) ∷
   rw⁻ 46 (q2 c4) ∷
   rw 48 (q46 c4) ∷
   rw 48 (q11 c4) ∷
   rw⁻ 49 (q2 c4) ∷
   rw⁻ 52 (q2 c4) ∷
   rw⁻ 55 (q2 c4) ∷
   rw⁻ 56 (q47 c4) ∷
   rw⁻ 53 (q48 c4) ∷
   rw⁻ 50 (q47 c4) ∷
   rw⁻ 47 (q48 c4) ∷
   rw 50 (q2 c4) ∷
   rw 51 (q2 c4) ∷
   rw 52 (q2 c4) ∷
   rw⁻ 49 (q11 c4) ∷
   rw⁻ 49 (q46 c4) ∷
   rw⁻ 44 (q49 c4) ∷
   re 42 1 (CS03⁻ ∷ []) ∷
   rw⁻ 41 (q50 c4) ∷
   re 43 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 38 (q49 c4) ∷
   re 36 1 (CS03 ∷ []) ∷
   rw⁻ 35 (q51 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ []) ∷
   rw 38 (q2 c4) ∷
   rw 39 (q2 c4) ∷
   rw 40 (q2 c4) ∷
   rw 41 (q2 c4) ∷
   re 37 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 37 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 38 (q2 c4) ∷
   rw⁻ 41 (q2 c4) ∷
   rw⁻ 44 (q2 c4) ∷
   rw⁻ 47 (q2 c4) ∷
   rw 49 (q46 c4) ∷
   rw 49 (q11 c4) ∷
   rw⁻ 50 (q2 c4) ∷
   rw⁻ 53 (q2 c4) ∷
   rw⁻ 56 (q2 c4) ∷
   rw⁻ 57 (q34 c4) ∷
   rw⁻ 54 (q33 c4) ∷
   rw⁻ 51 (q34 c4) ∷
   rw⁻ 48 (q33 c4) ∷
   rw 51 (q2 c4) ∷
   rw 52 (q2 c4) ∷
   rw 53 (q2 c4) ∷
   rw⁻ 50 (q11 c4) ∷
   rw⁻ 50 (q46 c4) ∷
   rw⁻ 45 (q35 c4) ∷
   re 43 1 (CS03⁻ ∷ []) ∷
   rw⁻ 42 (q37 c4) ∷
   re 44 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 39 (q35 c4) ∷
   re 37 1 (CS03 ∷ []) ∷
   rw⁻ 36 (q36 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ []) ∷
   rw 39 (q2 c4) ∷
   rw 40 (q2 c4) ∷
   rw 41 (q2 c4) ∷
   rw 42 (q2 c4) ∷
   re 38 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 39 (q63 c4) ∷
   rw 38 (q64 c4) ∷
   rw 37 (q63 c4) ∷
   rw⁻ 31 (q45 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 38 1 (CS03 ∷ []) ∷
   re 40 1 (CS03⁻ ∷ []) ∷
   rw⁻ 35 (q65 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ []) ∷
   re 37 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 38 (q66 c4) ∷
   rw 42 (q46 c4) ∷
   rw 42 (q19 c4) ∷
   rw 42 (q52 c4) ∷
   rw⁻ 39 (q67 c4) ∷
   rw 42 (q68 c4) ∷
   rw 41 (q69 c4) ∷
   rw 40 (q68 c4) ∷
   rw⁻ 41 (q67 c4) ∷
   rw 44 (q68 c4) ∷
   rw 43 (q69 c4) ∷
   rw 42 (q68 c4) ∷
   rw⁻ 39 (q52 c4) ∷
   rw 39 (q23 c4) ∷
   rw⁻ 39 (q46 c4) ∷
   re 35 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 35 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 35 1 (CS03 ∷ []) ∷
   rw⁻ 34 (q70 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ []) ∷
   rw 33 (q71 c4) ∷
   re 33 1 (CS03 ∷ []) ∷
   rw⁻ 32 (q70 c4) ∷
   re 32 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 36 (q18 c4) ∷
   rw⁻ 35 (q16 c4) ∷
   rw 34 (q72 c4) ∷
   rw⁻ 33 (q16 c4) ∷
   rw 37 (q15 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 36 (q2 c4) ∷
   rw⁻ 39 (q2 c4) ∷
   rw⁻ 42 (q2 c4) ∷
   rw⁻ 45 (q2 c4) ∷
   rw 47 (q46 c4) ∷
   rw 47 (q11 c4) ∷
   rw⁻ 48 (q2 c4) ∷
   rw⁻ 51 (q2 c4) ∷
   rw⁻ 54 (q2 c4) ∷
   rw⁻ 55 (q10 c4) ∷
   rw⁻ 53 (q1 c4) ∷
   rw⁻ 54 (q2 c4) ∷
   rw⁻ 57 (q2 c4) ∷
   rw⁻ 58 (q9 c4) ∷
   rw 56 (q4 c4) ∷
   rw⁻ 57 (q2 c4) ∷
   rw⁻ 60 (q2 c4) ∷
   rw⁻ 63 (q2 c4) ∷
   rw⁻ 66 (q2 c4) ∷
   rw⁻ 67 (q8 c4) ∷
   rw⁻ 64 (q6 c4) ∷
   rw⁻ 61 (q7 c4) ∷
   rw⁻ 58 (q6 c4) ∷
   rw⁻ 55 (q5 c4) ∷
   rw 58 (q2 c4) ∷
   rw 59 (q2 c4) ∷
   rw 60 (q2 c4) ∷
   rw 61 (q2 c4) ∷
   rw⁻ 57 (q4 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw 55 (q2 c4) ∷
   rw 56 (q2 c4) ∷
   rw 54 (q1 c4) ∷
   rw⁻ 49 (q10 c4) ∷
   rw⁻ 47 (q1 c4) ∷
   rw⁻ 48 (q2 c4) ∷
   rw⁻ 51 (q2 c4) ∷
   rw⁻ 52 (q9 c4) ∷
   rw 50 (q4 c4) ∷
   rw⁻ 51 (q2 c4) ∷
   rw⁻ 54 (q2 c4) ∷
   rw⁻ 57 (q2 c4) ∷
   rw⁻ 60 (q2 c4) ∷
   rw⁻ 61 (q8 c4) ∷
   rw⁻ 58 (q6 c4) ∷
   rw⁻ 55 (q7 c4) ∷ []) Eq.refl
