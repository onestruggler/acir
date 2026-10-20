{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D175 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0103 ; wl0189 ; wl0211 ; wl0283 ; wl0305 ; wl0364 ; wl0433 ; wl0600 ; wl0717 ; wl0719 ; wl0730 ; wl0732 ; wl0733 ; wl0734 ; wl0735 ; wl0736 ; wl0737 ; wl0738 ; wl0739 ; wl0740 ; wl0741 ; wl0742 ; wp0296 ; wp0343 ; wp0344 ; wp0345 ; wp0346 ; wp0353 ; wp0356 ; wp0373 ; wp0374 ; wp0375 ; wp0376 ; wp0377 ; wp0378 ; wp0379 ; wp0380 ; wp0381 ; wp0382 ; wp0383 ; wp0384 ; wp0385 ; wp0386)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-sym12-at14213243 ; lem-sym23-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-beta-T-at0310243142 ; lem-sym12-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-SBsym-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D166 using (lem-sym23-at143143)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-beta-T-at12213443)
open import Examples.Groups.Clifford+CS.Five.D.D174 using (lem-auto-BOX⟨0·1234⟩-∣-CS04-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-K0-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0210243143 ; lem-beta-T-at143143)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ013 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-2-BOX⟨0·3142⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨1·0·2·4⟩ ; lem-nat-3-SBOXd⟨1·0·2·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-SBOX⟨0·1·2·3⟩ ; lem-nat-1-SBOX⟨0·2·1·3⟩ ; lem-nat-1-SBOXd⟨0·1·2·3⟩ ; lem-nat-1-SBOXd⟨0·2·1·3⟩ ; lem-nat-2-SBOX⟨1·0·3·4⟩ ; lem-nat-2-SBOXd⟨1·0·3·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-SBOX⟨1·0·2·4⟩ ; lem-nat-2-SBOXd⟨1·0·2·4⟩ ; lem-nat-3-SBOX⟨1·0·2·3⟩ ; lem-nat-3-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨0·3241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-SBOX⟨0·1·2·3⟩ ; lem-nat-0-SBOXd⟨0·1·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-SBOX⟨1·0·2·3⟩ ; lem-nat-0-SBOXd⟨1·0·2·3⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx0-1423 ∷ []) (Bx0-4123 ∷ []) (lem-sym12-at243243 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx0-4123 ∷ []) (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx0-4213 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at143143 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ []) (wp0373 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0374 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (K0⁻ ∷ K0 ∷ []) [] (wl0189 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (wp0375 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (wp0376 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ []) (c₁ (K) (X ↑ ↑ ↑))
  q12 : Ws → Eqn
  q12 c4 = eqn (K0 ∷ CCZ123 ∷ []) (CCZ123 ∷ K0 ∷ []) (c₁ (K) (CCZ))
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ []) (wp0343 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ []) (wp0344 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ []) (wp0345 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS04 ∷ []) (wp0346 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X ↑ ↑ ↑))
  q19 : Ws → Eqn
  q19 c4 = eqn (K0⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ K0⁻ ∷ []) (c₁ (K • iI) (CCZ))
  q20 : Ws → Eqn
  q20 c4 = eqn (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (wp0377 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (wp0378 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (wp0379 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ []) (wl0733 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0211 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ []) (wp0380 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ []) (wp0381 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS04⁻ ∷ []) (wp0382 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS04⁻ ∷ []) (wp0383 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ []) (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ123 ∷ CS02 ∷ []) (CS02 ∷ CCZ123 ∷ []) (wl0734 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (wp0384 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) (wp0296 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Sb2-0-41-3 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0210243143 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx0-4213 ∷ []) (Bx0-4123 ∷ []) (lem-sym23-at143143 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx0-4123 ∷ []) (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ []) (wl0364 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (K3 ∷ X4 ∷ []) (X4 ∷ K3 ∷ []) (wl0732 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Sb2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ234 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CCZ234 ∷ []) (wp0385 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ CCZ234 ∷ []) (wl0735 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ234 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CCZ234 ∷ []) (wp0386 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0600 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ []) (wl0736 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04-at0210243143 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CX42 ∷ []) (K2 ∷ CZ24 ∷ K2⁻ ∷ []) (wl0737 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ []) (wl0730 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (Bx2-0413 ∷ K2 ∷ []) (K2 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0210243143 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CS24 ∷ CS24 ∷ []) (CZ24 ∷ []) (wl0305 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) (wl0717 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ []) (wp0353 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (K2⁻ ∷ X4 ∷ []) (X4 ∷ K2⁻ ∷ []) (wl0738 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx2-0413 ∷ K2⁻ ∷ []) (K2⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0210243143 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ []) (wl0739 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (Bx2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0210243143 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ []) (wl0719 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ CS34 ∷ []) (wp0356 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (K3⁻ ∷ X4 ∷ []) (X4 ∷ K3⁻ ∷ []) (wl0740 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (Sb2-0-41-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ []) (wl0741 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Sb2-0-41-3 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0210243143 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ []) (wl0742 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (Sb2-0-41-3 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0210243143 c4)

-- F4 CS01^0|CS12^1: 648 steps
lem-F4-CS01ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣CS12ᵖ1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw 3 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw⁻ 14 (q6 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   re 7 1 (CS03 ∷ []) ∷
   re 13 1 (CS03⁻ ∷ []) ∷
   rw⁻ 6 (q8 c4) ∷
   re 10 1 (Sb2-0-3-1 ∷ []) ∷
   re 16 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 9 (q11 c4) ∷
   rw 11 (q13 c4) ∷
   rw⁻ 12 (q7 c4) ∷
   rw⁻ 15 (q7 c4) ∷
   rw⁻ 18 (q7 c4) ∷
   rw⁻ 21 (q7 c4) ∷
   rw⁻ 22 (q14 c4) ∷
   rw⁻ 19 (q15 c4) ∷
   rw⁻ 16 (q16 c4) ∷
   rw⁻ 13 (q15 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q7 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw⁻ 13 (q18 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw⁻ 11 (q18 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   rw⁻ 12 (q7 c4) ∷
   rw⁻ 15 (q7 c4) ∷
   rw⁻ 16 (q14 c4) ∷
   rw⁻ 13 (q15 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q7 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw⁻ 0 (q20 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q7 c4) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw 4 (q21 c4) ∷
   re 4 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   re 10 1 (CS02 ∷ []) ∷
   re 16 1 (CS02⁻ ∷ []) ∷
   rw⁻ 9 (q22 c4) ∷
   re 22 1 (Sb3-0-2-1 ∷ []) ∷
   re 28 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 6 (q23 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 13 (q12 c4) ∷
   rw⁻ 12 (q11 c4) ∷
   rw⁻ 13 (q25 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw⁻ 14 (q18 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw 17 (q26 c4) ∷
   rw⁻ 18 (q7 c4) ∷
   rw⁻ 21 (q7 c4) ∷
   rw⁻ 24 (q7 c4) ∷
   rw⁻ 27 (q7 c4) ∷
   rw⁻ 28 (q27 c4) ∷
   rw⁻ 25 (q28 c4) ∷
   rw⁻ 22 (q29 c4) ∷
   rw⁻ 19 (q28 c4) ∷
   rw⁻ 16 (q30 c4) ∷
   rw 19 (q7 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q7 c4) ∷
   rw 22 (q7 c4) ∷
   rw⁻ 18 (q26 c4) ∷
   rw⁻ 19 (q18 c4) ∷
   rw⁻ 18 (q19 c4) ∷
   rw⁻ 17 (q18 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw⁻ 19 (q12 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw⁻ 19 (q25 c4) ∷
   rw⁻ 22 (q18 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw⁻ 20 (q18 c4) ∷
   rw⁻ 23 (q11 c4) ∷
   rw⁻ 22 (q12 c4) ∷
   rw⁻ 21 (q11 c4) ∷
   rw⁻ 24 (q31 c4) ∷
   rw 23 (q32 c4) ∷
   rw⁻ 22 (q31 c4) ∷
   rw⁻ 25 (q18 c4) ∷
   rw⁻ 24 (q19 c4) ∷
   rw⁻ 23 (q18 c4) ∷
   rw⁻ 9 (q33 c4) ∷
   rw⁻ 8 (q11 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 9 (q11 c4) ∷
   rw 11 (q26 c4) ∷
   rw⁻ 12 (q7 c4) ∷
   rw⁻ 15 (q7 c4) ∷
   rw⁻ 18 (q7 c4) ∷
   rw⁻ 21 (q7 c4) ∷
   rw⁻ 22 (q27 c4) ∷
   rw⁻ 19 (q28 c4) ∷
   rw⁻ 16 (q29 c4) ∷
   rw⁻ 13 (q28 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q7 c4) ∷
   rw⁻ 12 (q26 c4) ∷
   rw⁻ 13 (q18 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw⁻ 11 (q18 c4) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 13 (q12 c4) ∷
   rw⁻ 12 (q11 c4) ∷
   rw⁻ 13 (q25 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw⁻ 14 (q18 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw⁻ 18 (q31 c4) ∷
   rw 17 (q32 c4) ∷
   rw⁻ 16 (q31 c4) ∷
   rw⁻ 19 (q18 c4) ∷
   rw⁻ 18 (q19 c4) ∷
   rw⁻ 17 (q18 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q7 c4) ∷
   rw 19 (q7 c4) ∷
   rw⁻ 16 (q24 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q7 c4) ∷
   rw 19 (q7 c4) ∷
   rw 20 (q7 c4) ∷
   re 16 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 16 (q21 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q6 c4) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw 0 (q4 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw⁻ 1 (q34 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw⁻ 13 (q6 c4) ∷
   rw⁻ 16 (q6 c4) ∷
   re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   re 9 1 (CS03 ∷ []) ∷
   re 15 1 (CS03⁻ ∷ []) ∷
   rw⁻ 8 (q8 c4) ∷
   re 12 1 (Sb2-0-3-1 ∷ []) ∷
   re 18 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 5 (q9 c4) ∷
   rw 3 (q10 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   rw⁻ 13 (q11 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw 13 (q13 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw⁻ 17 (q7 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   rw⁻ 23 (q7 c4) ∷
   rw⁻ 24 (q14 c4) ∷
   rw⁻ 21 (q15 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 15 (q15 c4) ∷
   rw⁻ 12 (q17 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q7 c4) ∷
   rw⁻ 14 (q13 c4) ∷
   rw⁻ 15 (q18 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 13 (q18 c4) ∷
   rw⁻ 8 (q20 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw⁻ 17 (q7 c4) ∷
   rw⁻ 18 (q14 c4) ∷
   rw⁻ 15 (q15 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q7 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q18 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 6 (q10 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q7 c4) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   rw 6 (q21 c4) ∷
   re 6 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   re 12 1 (CS02 ∷ []) ∷
   re 18 1 (CS02⁻ ∷ []) ∷
   rw⁻ 11 (q22 c4) ∷
   re 24 1 (Sb3-0-2-1 ∷ []) ∷
   re 30 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 8 (q23 c4) ∷
   rw 6 (q24 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   rw⁻ 16 (q11 c4) ∷
   rw⁻ 15 (q12 c4) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 15 (q25 c4) ∷
   rw⁻ 18 (q18 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   rw⁻ 18 (q12 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw 19 (q26 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   rw⁻ 23 (q7 c4) ∷
   rw⁻ 26 (q7 c4) ∷
   rw⁻ 29 (q7 c4) ∷
   rw⁻ 30 (q27 c4) ∷
   rw⁻ 27 (q28 c4) ∷
   rw⁻ 24 (q29 c4) ∷
   rw⁻ 21 (q28 c4) ∷
   rw⁻ 18 (q30 c4) ∷
   rw 21 (q7 c4) ∷
   rw 22 (q7 c4) ∷
   rw 23 (q7 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 20 (q26 c4) ∷
   rw⁻ 21 (q18 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw⁻ 19 (q18 c4) ∷
   rw⁻ 22 (q11 c4) ∷
   rw⁻ 21 (q12 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw⁻ 24 (q18 c4) ∷
   rw⁻ 23 (q19 c4) ∷
   rw⁻ 22 (q18 c4) ∷
   rw⁻ 25 (q11 c4) ∷
   rw⁻ 24 (q12 c4) ∷
   rw⁻ 23 (q11 c4) ∷
   rw⁻ 26 (q31 c4) ∷
   rw 25 (q32 c4) ∷
   rw⁻ 24 (q31 c4) ∷
   rw⁻ 27 (q18 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw⁻ 25 (q18 c4) ∷
   rw⁻ 11 (q33 c4) ∷
   rw⁻ 10 (q11 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 8 (q11 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw⁻ 12 (q18 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   rw⁻ 13 (q11 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw 13 (q26 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw⁻ 17 (q7 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   rw⁻ 23 (q7 c4) ∷
   rw⁻ 24 (q27 c4) ∷
   rw⁻ 21 (q28 c4) ∷
   rw⁻ 18 (q29 c4) ∷
   rw⁻ 15 (q28 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q7 c4) ∷
   rw⁻ 14 (q26 c4) ∷
   rw⁻ 15 (q18 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 13 (q18 c4) ∷
   rw⁻ 16 (q11 c4) ∷
   rw⁻ 15 (q12 c4) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 15 (q25 c4) ∷
   rw⁻ 18 (q18 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   rw⁻ 18 (q12 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 20 (q31 c4) ∷
   rw 19 (q32 c4) ∷
   rw⁻ 18 (q31 c4) ∷
   rw⁻ 21 (q18 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw⁻ 19 (q18 c4) ∷
   rw⁻ 5 (q33 c4) ∷
   rw 19 (q7 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q7 c4) ∷
   rw⁻ 18 (q24 c4) ∷
   rw 19 (q7 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q7 c4) ∷
   rw 22 (q7 c4) ∷
   re 18 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 18 (q21 c4) ∷
   rw 4 (q6 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   rw 4 (q35 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   rw 0 (q36 c4) ∷
   rw 0 (q37 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   re 15 1 (CS03⁻ ∷ []) ∷
   rw⁻ 14 (q41 c4) ∷
   re 16 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 11 (q42 c4) ∷
   re 9 1 (CS03 ∷ []) ∷
   rw⁻ 8 (q43 c4) ∷
   re 10 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 5 (q42 c4) ∷
   rw 5 (q44 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw 3 (q46 c4) ∷
   rw⁻ 2 (q45 c4) ∷
   rw 6 (q47 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   rw 4 (q49 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw⁻ 7 (q50 c4) ∷
   rw 5 (q10 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   rw⁻ 12 (q7 c4) ∷
   rw⁻ 13 (q51 c4) ∷
   rw⁻ 10 (q52 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw⁻ 4 (q52 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 6 (q10 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   rw⁻ 14 (q51 c4) ∷
   rw⁻ 11 (q52 c4) ∷
   rw⁻ 8 (q51 c4) ∷
   rw⁻ 5 (q52 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q7 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   rw 4 (q50 c4) ∷
   rw⁻ 7 (q53 c4) ∷
   rw 6 (q54 c4) ∷
   rw⁻ 5 (q53 c4) ∷
   rw⁻ 3 (q47 c4) ∷
   rw⁻ 6 (q55 c4) ∷
   rw 5 (q56 c4) ∷
   rw⁻ 4 (q55 c4) ∷
   rw 8 (q47 c4) ∷
   rw⁻ 7 (q48 c4) ∷
   rw 6 (q49 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   rw⁻ 9 (q50 c4) ∷
   rw 7 (q10 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw⁻ 15 (q51 c4) ∷
   rw⁻ 12 (q52 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   rw⁻ 6 (q52 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 8 (q10 c4) ∷
   rw 8 (q10 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   rw⁻ 12 (q7 c4) ∷
   rw⁻ 15 (q7 c4) ∷
   rw⁻ 16 (q51 c4) ∷
   rw⁻ 13 (q52 c4) ∷
   rw⁻ 10 (q51 c4) ∷
   rw⁻ 7 (q52 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q7 c4) ∷
   rw⁻ 9 (q10 c4) ∷
   rw 6 (q50 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   rw 8 (q54 c4) ∷
   rw⁻ 7 (q53 c4) ∷
   rw⁻ 5 (q47 c4) ∷
   rw 7 (q10 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw⁻ 15 (q57 c4) ∷
   rw⁻ 12 (q58 c4) ∷
   rw⁻ 9 (q57 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 8 (q10 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q7 c4) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 4 (q60 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw 1 (q38 c4) ∷
   re 5 1 (CS13 ∷ []) ∷
   rw⁻ 4 (q61 c4) ∷
   re 4 1 (Sb0-1-3-2 ∷ []) ∷
   rw 3 (q62 c4) ∷
   re 3 1 (CS13 ∷ []) ∷
   rw⁻ 2 (q61 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 6 (q38 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw 4 (q40 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   re 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   rw⁻ 12 (q7 c4) ∷
   rw⁻ 15 (q7 c4) ∷
   re 17 1 (CS03⁻ ∷ []) ∷
   rw⁻ 16 (q41 c4) ∷
   re 18 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 13 (q42 c4) ∷
   re 11 1 (CS03 ∷ []) ∷
   rw⁻ 10 (q43 c4) ∷
   re 12 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 7 (q42 c4) ∷
   rw 7 (q44 c4) ∷
   rw⁻ 6 (q45 c4) ∷
   rw 5 (q46 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw 8 (q47 c4) ∷
   rw⁻ 7 (q48 c4) ∷
   rw 6 (q49 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   rw⁻ 9 (q50 c4) ∷
   rw 7 (q10 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw⁻ 15 (q51 c4) ∷
   rw⁻ 12 (q52 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   rw⁻ 6 (q52 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 8 (q10 c4) ∷
   rw 8 (q10 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   rw⁻ 12 (q7 c4) ∷
   rw⁻ 15 (q7 c4) ∷
   rw⁻ 16 (q51 c4) ∷
   rw⁻ 13 (q52 c4) ∷
   rw⁻ 10 (q51 c4) ∷
   rw⁻ 7 (q52 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q7 c4) ∷
   rw⁻ 9 (q10 c4) ∷
   rw 6 (q50 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   rw 8 (q54 c4) ∷
   rw⁻ 7 (q53 c4) ∷
   rw⁻ 5 (q47 c4) ∷
   rw⁻ 8 (q55 c4) ∷
   rw 7 (q56 c4) ∷
   rw⁻ 6 (q55 c4) ∷
   rw 10 (q47 c4) ∷
   rw⁻ 9 (q48 c4) ∷
   rw 8 (q49 c4) ∷
   rw⁻ 7 (q48 c4) ∷
   rw⁻ 11 (q50 c4) ∷
   rw 9 (q10 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw⁻ 17 (q51 c4) ∷
   rw⁻ 14 (q52 c4) ∷
   rw⁻ 11 (q51 c4) ∷
   rw⁻ 8 (q52 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q7 c4) ∷
   rw⁻ 10 (q10 c4) ∷
   rw 10 (q10 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw⁻ 17 (q7 c4) ∷
   rw⁻ 18 (q51 c4) ∷
   rw⁻ 15 (q52 c4) ∷
   rw⁻ 12 (q51 c4) ∷
   rw⁻ 9 (q52 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q7 c4) ∷
   rw⁻ 11 (q10 c4) ∷
   rw 8 (q50 c4) ∷
   rw⁻ 11 (q53 c4) ∷
   rw 10 (q54 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   rw⁻ 7 (q47 c4) ∷
   rw 9 (q10 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw⁻ 17 (q57 c4) ∷
   rw⁻ 14 (q58 c4) ∷
   rw⁻ 11 (q57 c4) ∷
   rw⁻ 8 (q58 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q7 c4) ∷
   rw⁻ 10 (q10 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q7 c4) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 7 (q59 c4) ∷
   rw 6 (q60 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 3 (q38 c4) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q63 c4) ∷
   re 6 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw 5 (q64 c4) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q63 c4) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (Sw23 ∷ Bx0-3142 ∷ []) (Bx0-2143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3142⟩ (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (Bx0-2143 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4))

-- beta-T @13213442: 8 steps
lem-beta-T-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at13213442 c4 = derive (Bx0-3142 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q65 c4) ∷
   rw 1 (q66 c4) ∷
   rw 1 (q67 c4) ∷
   rw 0 (q68 c4) ∷
   rw 1 (q69 c4) ∷
   rw 2 (q68 c4) ∷
   rw 3 (q69 c4) ∷
   rw 4 (q65 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (Sw12 ∷ Bx0-3241 ∷ []) (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (Bx0-3142 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at13213442 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4))

-- beta-T @133441: 8 steps
lem-beta-T-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at133441 c4 = derive (Bx0-3241 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   rw 1 (q72 c4) ∷
   rw 0 (q73 c4) ∷
   rw 1 (q74 c4) ∷
   rw 2 (q73 c4) ∷
   rw 3 (q74 c4) ∷
   rw 4 (q70 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = eqn (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (Sb0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ c4 = derive (Sb0-1-23-4 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-3-4 ∷ Sb0-1-23-4 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw 0 (q75 c4) ∷
   rw 0 (q76 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   re 0 1 (Sb1-0-3-4 ∷ []) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (Sb0-1-32-4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ c4 = derive (Sb0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sb0-1-23-4 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q75 c4) ∷
   rw 0 (q77 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   re 0 1 (Sb⁻1-0-3-4 ∷ []) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (Sb0-1-23-4 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CCZ143 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2332 c4 = derive (Sb0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q65 c4) ∷
   rw 1 (q78 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 0 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q65 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4))
  q85 : Ws → Eqn
  q85 c4 = eqn (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (Sb0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2332 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CCZ143 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 c4 = derive (Sb0-1-42-3 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q83 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 0 (q87 c4) ∷
   rw 1 (q88 c4) ∷
   rw 2 (q83 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (Sw01 ∷ Sb1-0-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (Sb0-1-42-3 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CCZ143 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0110243243 c4 = derive (Sb1-0-42-3 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw⁻ 2 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   rw⁻ 0 (q93 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (Sw12 ∷ Sb2-0-41-3 ∷ []) (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (Sb1-0-42-3 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0110243243 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CCZ143 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0210243143 c4 = derive (Sb2-0-41-3 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q70 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 0 (q98 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q70 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (Sw23 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·4⟩ (lit c4))
  q101 : Ws → Eqn
  q101 c4 = eqn (Sb0-1-23-4 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-3-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (Sw23 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-4 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q65 c4) ∷
   rw 1 (q78 c4) ∷
   rw 2 (q100 c4) ∷
   rw 1 (q101 c4) ∷
   rw 0 (q102 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q65 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = eqn (Sw34 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·3⟩ (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (Sb0-1-32-4 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (Sw34 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-3 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q83 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q103 c4) ∷
   rw 1 (q104 c4) ∷
   rw 0 (q105 c4) ∷
   rw 1 (q88 c4) ∷
   rw 2 (q83 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (Sw01 ∷ Sb0-1-2-3 ∷ []) (Sb1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·3⟩ (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (Sb0-1-42-3 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (Sw01 ∷ Sb1-0-2-3 ∷ []) (Sb0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·2·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 c4 = derive (Sb1-0-42-3 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-2-3 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q107 c4) ∷
   rw 0 (q108 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = eqn (Sw12 ∷ Sb0-2-1-3 ∷ []) (Sb0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·1·3⟩ (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (Sb1-0-42-3 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-2-3 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (Sw12 ∷ Sb0-1-2-3 ∷ []) (Sb0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·2·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 c4 = derive (Sb2-0-41-3 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-3 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q70 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw 0 (q111 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q70 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (Sw23 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·4⟩ (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (Sb0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ c4)
  q114 : Ws → Eqn
  q114 c4 = eqn (Sw23 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q65 c4) ∷
   rw 1 (q78 c4) ∷
   rw 2 (q112 c4) ∷
   rw 1 (q113 c4) ∷
   rw 0 (q114 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q65 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = eqn (Sw34 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·3⟩ (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (Sb0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (Sw34 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q83 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   rw 0 (q117 c4) ∷
   rw 1 (q88 c4) ∷
   rw 2 (q83 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = eqn (Sw01 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·3⟩ (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (Sb0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw01 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·2·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 c4 = derive (Sb1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q118 c4) ∷
   rw 1 (q119 c4) ∷
   rw 0 (q120 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·1·3⟩ (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (Sb1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (Sw12 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·2·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 c4 = derive (Sb2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q70 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q121 c4) ∷
   rw 1 (q122 c4) ∷
   rw 0 (q123 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q70 c4) ∷ []) Eq.refl
