{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D018 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0386 ; wl0401 ; wl0402 ; wl0403 ; wl0404 ; wl0405 ; wl0406 ; wl0407 ; wl0408 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0454 ; wl0455 ; wp0024 ; wp0060 ; wp0131 ; wp0132 ; wp0140 ; wp0141)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-X1-beta-at02203443 ; lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233241 ; lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233241 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym12-at0210213443 ; lem-sym12-at02203443 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-TOFF203-CX41)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) (wl0405 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sb2-0-41-3 ∷ CS34 ∷ []) (CS34 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sb2-0-41-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ []) (wl0401 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Toff201 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff201 ∷ []) (wl0386 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (X1 ∷ CCZ234 ∷ []) (CCZ234 ∷ X1 ∷ []) (c₂ (X ↑) (CCZ))
  q15 : Ws → Eqn
  q15 c4 = eqn (CK10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK10 ∷ []) (c₂ (CK₁₀) (CCZ))
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Toff314 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff314 ∷ []) (wp0132 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0131 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx2-0143 ∷ []) (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (X1 ∷ Bx2-1043 ∷ X1 ∷ []) (CCZ034 ∷ Bx2-1043 ∷ []) (lem-X1-beta-at02203443 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ034 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233241 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ034 ∷ X1 ∷ []) (X1 ∷ CCZ034 ∷ []) (wp0060 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ034 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233241 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ034 ∷ CCZ034 ∷ []) [] (wp0024 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) (wl0418 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sb2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) (wl0454 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) (wl0455 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0141 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0140 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) (wl0406 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (Toff203 ∷ CX41 ∷ []) (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) (wl0419 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4)

-- F1 CS-K0 [rhs shape] part12: 391 steps
lem-F1-CS-K0-rhs-shape-part12 : Ws → ⟪ (CS04 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0431 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ X1 ∷ CS03 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-rhs-shape-part12 c4 = derive (CS04 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0431 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ X1 ∷ CS03 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw 30 (q1 c4) ∷
   rw 31 (q2 c4) ∷
   rw 32 (q2 c4) ∷
   rw 33 (q2 c4) ∷
   rw 34 (q2 c4) ∷
   re 30 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 31 (q3 c4) ∷
   rw 30 (q4 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw⁻ 25 (q5 c4) ∷
   rw⁻ 28 (q6 c4) ∷
   rw 27 (q7 c4) ∷
   rw⁻ 26 (q6 c4) ∷
   rw 24 (q8 c4) ∷
   re 28 1 (CS03⁻ ∷ []) ∷
   rw⁻ 27 (q9 c4) ∷
   re 27 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 26 (q10 c4) ∷
   re 26 1 (CS03⁻ ∷ []) ∷
   rw⁻ 25 (q9 c4) ∷
   re 25 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 21 5 (Sb2-0-41-3 ∷ []) ∷
   re 21 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 21 (q11 c4) ∷
   rw 21 (q12 c4) ∷
   rw⁻ 18 (q13 c4) ∷
   rw 21 (q14 c4) ∷
   rw 20 (q15 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 20 (q13 c4) ∷
   rw 23 (q14 c4) ∷
   rw 22 (q15 c4) ∷
   rw 21 (q14 c4) ∷
   rw⁻ 18 (q12 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 19 (q17 c4) ∷
   re 23 1 (CS03 ∷ []) ∷
   re 25 1 (CS03⁻ ∷ []) ∷
   rw⁻ 20 (q18 c4) ∷
   re 20 1 (Sb2-0-3-1 ∷ []) ∷
   re 22 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 18 5 (Sb2-0-41-3 ∷ []) ∷
   re 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 19 (q2 c4) ∷
   rw 18 (q11 c4) ∷
   rw 18 (q19 c4) ∷
   rw 17 (q20 c4) ∷
   rw 18 (q21 c4) ∷
   rw 18 (q16 c4) ∷
   rw 17 (q22 c4) ∷
   rw 16 (q23 c4) ∷
   rw⁻ 17 (q2 c4) ∷
   rw 16 (q11 c4) ∷
   rw 16 (q19 c4) ∷
   rw 15 (q20 c4) ∷
   rw 16 (q21 c4) ∷
   rw 16 (q16 c4) ∷
   rw 15 (q22 c4) ∷
   rw 19 (q24 c4) ∷
   rw 16 (q24 c4) ∷
   rw 17 (q25 c4) ∷
   rw 18 (q24 c4) ∷
   rw 19 (q26 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 18 (q27 c4) ∷
   rw 17 (q28 c4) ∷
   rw⁻ 16 (q27 c4) ∷
   rw 20 (q5 c4) ∷
   re 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   re 30 1 (CS03⁻ ∷ []) ∷
   rw⁻ 29 (q29 c4) ∷
   re 31 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q30 c4) ∷
   re 24 1 (CS03 ∷ []) ∷
   rw⁻ 23 (q31 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q30 c4) ∷
   rw 18 (q11 c4) ∷
   rw 18 (q12 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 26 (q32 c4) ∷
   rw⁻ 23 (q33 c4) ∷
   rw⁻ 20 (q32 c4) ∷
   rw⁻ 17 (q33 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   rw⁻ 19 (q12 c4) ∷
   rw 19 (q16 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   re 19 5 (Sb2-0-41-3 ∷ []) ∷
   re 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   re 31 1 (CS03⁻ ∷ []) ∷
   rw⁻ 30 (q34 c4) ∷
   re 34 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 25 1 (CS03 ∷ []) ∷
   rw⁻ 21 (q35 c4) ∷
   re 28 1 (Sb2-0-3-1 ∷ []) ∷
   rw 19 (q36 c4) ∷
   rw 19 (q37 c4) ∷
   rw 19 (q38 c4) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 27 (q39 c4) ∷
   rw⁻ 26 (q40 c4) ∷
   rw 25 (q41 c4) ∷
   rw⁻ 24 (q40 c4) ∷
   rw⁻ 25 (q42 c4) ∷
   rw⁻ 28 (q40 c4) ∷
   rw 27 (q41 c4) ∷
   rw⁻ 26 (q40 c4) ∷
   rw⁻ 21 (q39 c4) ∷
   rw⁻ 20 (q40 c4) ∷
   rw 19 (q41 c4) ∷
   rw⁻ 18 (q40 c4) ∷
   rw⁻ 19 (q42 c4) ∷
   rw⁻ 22 (q40 c4) ∷
   rw 21 (q41 c4) ∷
   rw⁻ 20 (q40 c4) ∷
   rw 23 (q2 c4) ∷
   rw 24 (q2 c4) ∷
   rw 25 (q2 c4) ∷
   rw⁻ 22 (q38 c4) ∷
   rw 22 (q43 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q2 c4) ∷
   rw 24 (q2 c4) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q2 c4) ∷
   re 22 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 23 (q3 c4) ∷
   rw 22 (q4 c4) ∷
   rw⁻ 21 (q3 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   rw⁻ 20 (q6 c4) ∷
   rw 19 (q7 c4) ∷
   rw⁻ 18 (q6 c4) ∷
   rw 16 (q8 c4) ∷
   re 20 1 (CS03 ∷ []) ∷
   rw⁻ 19 (q44 c4) ∷
   re 19 1 (Sb2-0-3-1 ∷ []) ∷
   rw 18 (q45 c4) ∷
   re 18 1 (CS03 ∷ []) ∷
   rw⁻ 17 (q44 c4) ∷
   re 17 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 21 (q8 c4) ∷
   rw⁻ 20 (q27 c4) ∷
   rw 19 (q28 c4) ∷
   rw⁻ 18 (q27 c4) ∷
   rw 22 (q5 c4) ∷
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 30 (q2 c4) ∷
   re 32 1 (CS03⁻ ∷ []) ∷
   rw⁻ 31 (q29 c4) ∷
   re 33 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 28 (q30 c4) ∷
   re 26 1 (CS03 ∷ []) ∷
   rw⁻ 25 (q31 c4) ∷
   re 27 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 22 (q30 c4) ∷
   rw 20 (q11 c4) ∷
   rw 20 (q12 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 28 (q32 c4) ∷
   rw⁻ 25 (q33 c4) ∷
   rw⁻ 22 (q32 c4) ∷
   rw⁻ 19 (q33 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw 24 (q2 c4) ∷
   rw⁻ 21 (q12 c4) ∷
   rw 21 (q16 c4) ∷
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
   re 33 1 (CS03⁻ ∷ []) ∷
   rw⁻ 32 (q34 c4) ∷
   re 36 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 27 1 (CS03 ∷ []) ∷
   rw⁻ 23 (q35 c4) ∷
   re 30 1 (Sb2-0-3-1 ∷ []) ∷
   rw 21 (q36 c4) ∷
   rw 21 (q37 c4) ∷
   rw 21 (q38 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 29 (q39 c4) ∷
   rw⁻ 28 (q40 c4) ∷
   rw 27 (q41 c4) ∷
   rw⁻ 26 (q40 c4) ∷
   rw⁻ 27 (q42 c4) ∷
   rw⁻ 30 (q40 c4) ∷
   rw 29 (q41 c4) ∷
   rw⁻ 28 (q40 c4) ∷
   rw⁻ 23 (q39 c4) ∷
   rw⁻ 22 (q40 c4) ∷
   rw 21 (q41 c4) ∷
   rw⁻ 20 (q40 c4) ∷
   rw⁻ 21 (q42 c4) ∷
   rw⁻ 24 (q40 c4) ∷
   rw 23 (q41 c4) ∷
   rw⁻ 22 (q40 c4) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q2 c4) ∷
   rw 27 (q2 c4) ∷
   rw⁻ 24 (q38 c4) ∷
   rw 24 (q43 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q2 c4) ∷
   rw 27 (q2 c4) ∷
   rw 28 (q2 c4) ∷
   re 24 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 25 (q3 c4) ∷
   rw 24 (q4 c4) ∷
   rw⁻ 23 (q3 c4) ∷
   rw⁻ 19 (q5 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw 21 (q7 c4) ∷
   rw⁻ 20 (q6 c4) ∷
   rw 18 (q8 c4) ∷
   re 22 1 (CS03⁻ ∷ []) ∷
   rw⁻ 21 (q9 c4) ∷
   re 21 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 20 (q10 c4) ∷
   re 20 1 (CS03⁻ ∷ []) ∷
   rw⁻ 19 (q9 c4) ∷
   re 19 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 15 5 (Sb2-0-41-3 ∷ []) ∷
   re 15 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 15 (q11 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw 15 (q14 c4) ∷
   rw 14 (q15 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 14 (q13 c4) ∷
   rw 17 (q14 c4) ∷
   rw 16 (q15 c4) ∷
   rw 15 (q14 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw 12 (q16 c4) ∷
   rw⁻ 13 (q17 c4) ∷
   re 17 1 (CS03 ∷ []) ∷
   re 19 1 (CS03⁻ ∷ []) ∷
   rw⁻ 14 (q18 c4) ∷
   re 14 1 (Sb2-0-3-1 ∷ []) ∷
   re 16 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 12 5 (Sb2-0-41-3 ∷ []) ∷
   re 12 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 13 (q2 c4) ∷
   rw 12 (q11 c4) ∷
   rw 12 (q19 c4) ∷
   rw 11 (q20 c4) ∷
   rw 12 (q21 c4) ∷
   rw 12 (q16 c4) ∷
   rw 11 (q22 c4) ∷
   rw 10 (q23 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   rw 10 (q11 c4) ∷
   rw 10 (q19 c4) ∷
   rw 9 (q20 c4) ∷
   rw 10 (q21 c4) ∷
   rw 10 (q16 c4) ∷
   rw 9 (q22 c4) ∷
   rw 13 (q24 c4) ∷
   rw 10 (q24 c4) ∷
   rw 11 (q25 c4) ∷
   rw 12 (q24 c4) ∷
   rw 13 (q26 c4) ∷
   rw⁻ 13 (q8 c4) ∷
   rw⁻ 12 (q27 c4) ∷
   rw 11 (q28 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 14 (q5 c4) ∷
   re 12 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 13 (q2 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   re 24 1 (CS03⁻ ∷ []) ∷
   rw⁻ 23 (q29 c4) ∷
   re 25 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q30 c4) ∷
   re 18 1 (CS03 ∷ []) ∷
   rw⁻ 17 (q31 c4) ∷
   re 19 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 14 (q30 c4) ∷
   rw 12 (q11 c4) ∷
   rw 12 (q12 c4) ∷
   rw⁻ 13 (q2 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 20 (q32 c4) ∷
   rw⁻ 17 (q33 c4) ∷
   rw⁻ 14 (q32 c4) ∷
   rw⁻ 11 (q33 c4) ∷
   rw 14 (q2 c4) ∷
   rw 15 (q2 c4) ∷
   rw 16 (q2 c4) ∷
   rw⁻ 13 (q12 c4) ∷
   rw 13 (q16 c4) ∷
   rw 14 (q2 c4) ∷
   rw 15 (q2 c4) ∷
   rw 16 (q2 c4) ∷
   rw 17 (q2 c4) ∷
   re 13 5 (Sb2-0-41-3 ∷ []) ∷
   re 13 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 14 (q2 c4) ∷
   rw⁻ 17 (q2 c4) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   re 25 1 (CS03⁻ ∷ []) ∷
   rw⁻ 24 (q34 c4) ∷
   re 28 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 19 1 (CS03 ∷ []) ∷
   rw⁻ 15 (q35 c4) ∷
   re 22 1 (Sb2-0-3-1 ∷ []) ∷
   rw 13 (q36 c4) ∷
   rw 13 (q37 c4) ∷
   rw 13 (q38 c4) ∷
   rw⁻ 14 (q2 c4) ∷
   rw⁻ 17 (q2 c4) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 21 (q39 c4) ∷
   rw⁻ 20 (q40 c4) ∷
   rw 19 (q41 c4) ∷
   rw⁻ 18 (q40 c4) ∷
   rw⁻ 19 (q42 c4) ∷
   rw⁻ 22 (q40 c4) ∷
   rw 21 (q41 c4) ∷
   rw⁻ 20 (q40 c4) ∷
   rw⁻ 15 (q39 c4) ∷
   rw⁻ 14 (q40 c4) ∷
   rw 13 (q41 c4) ∷
   rw⁻ 12 (q40 c4) ∷
   rw⁻ 13 (q42 c4) ∷
   rw⁻ 16 (q40 c4) ∷
   rw 15 (q41 c4) ∷
   rw⁻ 14 (q40 c4) ∷
   rw 17 (q2 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw⁻ 16 (q38 c4) ∷
   rw 16 (q43 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q2 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   re 16 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 17 (q3 c4) ∷
   rw 16 (q4 c4) ∷
   rw⁻ 15 (q3 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q6 c4) ∷
   rw 13 (q7 c4) ∷
   rw⁻ 12 (q6 c4) ∷
   rw 10 (q8 c4) ∷
   re 14 1 (CS03 ∷ []) ∷
   rw⁻ 13 (q44 c4) ∷
   re 13 1 (Sb2-0-3-1 ∷ []) ∷
   rw 12 (q45 c4) ∷
   re 12 1 (CS03 ∷ []) ∷ []) Eq.refl
