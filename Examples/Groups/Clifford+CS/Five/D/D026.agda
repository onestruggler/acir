{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D026 where

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
  q1 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) (wl0454 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) (wl0455 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0141 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0140 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) (wl0406 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Toff203 ∷ CX41 ∷ []) (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) (wl0405 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sb2-0-41-3 ∷ CS34 ∷ []) (CS34 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sb2-0-41-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) (wl0419 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) (wl0418 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sb2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ []) (wl0401 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Toff201 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff201 ∷ []) (wl0386 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (X1 ∷ CCZ234 ∷ []) (CCZ234 ∷ X1 ∷ []) (c₂ (X ↑) (CCZ))
  q35 : Ws → Eqn
  q35 c4 = eqn (CK10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK10 ∷ []) (c₂ (CK₁₀) (CCZ))
  q36 : Ws → Eqn
  q36 c4 = eqn (Toff314 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff314 ∷ []) (wp0132 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0131 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx2-0143 ∷ []) (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (X1 ∷ Bx2-1043 ∷ X1 ∷ []) (CCZ034 ∷ Bx2-1043 ∷ []) (lem-X1-beta-at02203443 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ034 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233241 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ034 ∷ X1 ∷ []) (X1 ∷ CCZ034 ∷ []) (wp0060 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ034 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233241 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ034 ∷ CCZ034 ∷ []) [] (wp0024 c4)

-- F1 CS-K0 [rhs shape] part20: 378 steps
lem-F1-CS-K0-rhs-shape-part20 : Ws → ⟪ (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-rhs-shape-part20 c4 = derive (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 37 (q2 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw 30 (q5 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   re 30 5 (Sb2-0-41-3 ∷ []) ∷
   re 30 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   re 42 1 (CS03⁻ ∷ []) ∷
   rw⁻ 41 (q6 c4) ∷
   re 45 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 36 1 (CS03 ∷ []) ∷
   rw⁻ 32 (q7 c4) ∷
   re 39 1 (Sb2-0-3-1 ∷ []) ∷
   rw 30 (q8 c4) ∷
   rw 30 (q9 c4) ∷
   rw 30 (q10 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 38 (q11 c4) ∷
   rw⁻ 37 (q12 c4) ∷
   rw 36 (q13 c4) ∷
   rw⁻ 35 (q12 c4) ∷
   rw⁻ 36 (q14 c4) ∷
   rw⁻ 39 (q12 c4) ∷
   rw 38 (q13 c4) ∷
   rw⁻ 37 (q12 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw 30 (q13 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 30 (q14 c4) ∷
   rw⁻ 33 (q12 c4) ∷
   rw 32 (q13 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   rw⁻ 33 (q10 c4) ∷
   rw 33 (q15 c4) ∷
   rw 33 (q16 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   re 33 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 34 (q17 c4) ∷
   rw 33 (q18 c4) ∷
   rw⁻ 32 (q17 c4) ∷
   rw⁻ 28 (q19 c4) ∷
   rw⁻ 31 (q20 c4) ∷
   rw 30 (q21 c4) ∷
   rw⁻ 29 (q20 c4) ∷
   rw 27 (q22 c4) ∷
   re 31 1 (CS03 ∷ []) ∷
   rw⁻ 30 (q23 c4) ∷
   re 30 1 (Sb2-0-3-1 ∷ []) ∷
   rw 29 (q24 c4) ∷
   re 29 1 (CS03 ∷ []) ∷
   rw⁻ 28 (q23 c4) ∷
   re 28 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q22 c4) ∷
   rw⁻ 31 (q25 c4) ∷
   rw 30 (q26 c4) ∷
   rw⁻ 29 (q25 c4) ∷
   rw 33 (q19 c4) ∷
   re 31 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   re 43 1 (CS03⁻ ∷ []) ∷
   rw⁻ 42 (q27 c4) ∷
   re 44 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 39 (q28 c4) ∷
   re 37 1 (CS03 ∷ []) ∷
   rw⁻ 36 (q29 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 33 (q28 c4) ∷
   rw 31 (q30 c4) ∷
   rw 31 (q4 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw⁻ 39 (q2 c4) ∷
   rw⁻ 36 (q3 c4) ∷
   rw⁻ 33 (q2 c4) ∷
   rw⁻ 30 (q3 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw 32 (q5 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   re 32 5 (Sb2-0-41-3 ∷ []) ∷
   re 32 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   re 44 1 (CS03⁻ ∷ []) ∷
   rw⁻ 43 (q6 c4) ∷
   re 47 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 38 1 (CS03 ∷ []) ∷
   rw⁻ 34 (q7 c4) ∷
   re 41 1 (Sb2-0-3-1 ∷ []) ∷
   rw 32 (q8 c4) ∷
   rw 32 (q9 c4) ∷
   rw 32 (q10 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 40 (q11 c4) ∷
   rw⁻ 39 (q12 c4) ∷
   rw 38 (q13 c4) ∷
   rw⁻ 37 (q12 c4) ∷
   rw⁻ 38 (q14 c4) ∷
   rw⁻ 41 (q12 c4) ∷
   rw 40 (q13 c4) ∷
   rw⁻ 39 (q12 c4) ∷
   rw⁻ 34 (q11 c4) ∷
   rw⁻ 33 (q12 c4) ∷
   rw 32 (q13 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 32 (q14 c4) ∷
   rw⁻ 35 (q12 c4) ∷
   rw 34 (q13 c4) ∷
   rw⁻ 33 (q12 c4) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   rw 38 (q1 c4) ∷
   rw⁻ 35 (q10 c4) ∷
   rw 35 (q15 c4) ∷
   rw 35 (q16 c4) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   re 35 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 36 (q17 c4) ∷
   rw 35 (q18 c4) ∷
   rw⁻ 34 (q17 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw⁻ 33 (q20 c4) ∷
   rw 32 (q21 c4) ∷
   rw⁻ 31 (q20 c4) ∷
   rw 29 (q22 c4) ∷
   re 33 1 (CS03⁻ ∷ []) ∷
   rw⁻ 32 (q31 c4) ∷
   re 32 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 31 (q32 c4) ∷
   re 31 1 (CS03⁻ ∷ []) ∷
   rw⁻ 30 (q31 c4) ∷
   re 30 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 26 5 (Sb2-0-41-3 ∷ []) ∷
   re 26 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 26 (q30 c4) ∷
   rw 26 (q4 c4) ∷
   rw⁻ 23 (q33 c4) ∷
   rw 26 (q34 c4) ∷
   rw 25 (q35 c4) ∷
   rw 24 (q34 c4) ∷
   rw⁻ 25 (q33 c4) ∷
   rw 28 (q34 c4) ∷
   rw 27 (q35 c4) ∷
   rw 26 (q34 c4) ∷
   rw⁻ 23 (q4 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 24 (q36 c4) ∷
   re 28 1 (CS03 ∷ []) ∷
   re 30 1 (CS03⁻ ∷ []) ∷
   rw⁻ 25 (q37 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   re 27 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 23 5 (Sb2-0-41-3 ∷ []) ∷
   re 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q1 c4) ∷
   rw 23 (q30 c4) ∷
   rw 23 (q38 c4) ∷
   rw 22 (q39 c4) ∷
   rw 23 (q40 c4) ∷
   rw 23 (q5 c4) ∷
   rw 22 (q41 c4) ∷
   rw 21 (q42 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw 21 (q30 c4) ∷
   rw 21 (q38 c4) ∷
   rw 20 (q39 c4) ∷
   rw 21 (q40 c4) ∷
   rw 21 (q5 c4) ∷
   rw 20 (q41 c4) ∷
   rw 24 (q43 c4) ∷
   rw 21 (q43 c4) ∷
   rw 22 (q44 c4) ∷
   rw 23 (q43 c4) ∷
   rw 24 (q45 c4) ∷
   rw⁻ 24 (q22 c4) ∷
   rw⁻ 23 (q25 c4) ∷
   rw 22 (q26 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw 25 (q19 c4) ∷
   re 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   re 35 1 (CS03⁻ ∷ []) ∷
   rw⁻ 34 (q27 c4) ∷
   re 36 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q28 c4) ∷
   re 29 1 (CS03 ∷ []) ∷
   rw⁻ 28 (q29 c4) ∷
   re 30 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q28 c4) ∷
   rw 23 (q30 c4) ∷
   rw 23 (q4 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 22 (q3 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw⁻ 24 (q4 c4) ∷
   rw 24 (q5 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   re 24 5 (Sb2-0-41-3 ∷ []) ∷
   re 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   re 36 1 (CS03⁻ ∷ []) ∷
   rw⁻ 35 (q6 c4) ∷
   re 39 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 30 1 (CS03 ∷ []) ∷
   rw⁻ 26 (q7 c4) ∷
   re 33 1 (Sb2-0-3-1 ∷ []) ∷
   rw 24 (q8 c4) ∷
   rw 24 (q9 c4) ∷
   rw 24 (q10 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw⁻ 28 (q1 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw 30 (q13 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 30 (q14 c4) ∷
   rw⁻ 33 (q12 c4) ∷
   rw 32 (q13 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 26 (q11 c4) ∷
   rw⁻ 25 (q12 c4) ∷
   rw 24 (q13 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 24 (q14 c4) ∷
   rw⁻ 27 (q12 c4) ∷
   rw 26 (q13 c4) ∷
   rw⁻ 25 (q12 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw⁻ 27 (q10 c4) ∷
   rw 27 (q15 c4) ∷
   rw 27 (q16 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   re 27 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 28 (q17 c4) ∷
   rw 27 (q18 c4) ∷
   rw⁻ 26 (q17 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw⁻ 25 (q20 c4) ∷
   rw 24 (q21 c4) ∷
   rw⁻ 23 (q20 c4) ∷
   rw 21 (q22 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   rw⁻ 24 (q23 c4) ∷
   re 24 1 (Sb2-0-3-1 ∷ []) ∷
   rw 23 (q24 c4) ∷
   re 23 1 (CS03 ∷ []) ∷
   rw⁻ 22 (q23 c4) ∷
   re 22 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q22 c4) ∷
   rw⁻ 25 (q25 c4) ∷
   rw 24 (q26 c4) ∷
   rw⁻ 23 (q25 c4) ∷
   rw 27 (q19 c4) ∷
   re 25 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   re 37 1 (CS03⁻ ∷ []) ∷
   rw⁻ 36 (q27 c4) ∷
   re 38 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 33 (q28 c4) ∷
   re 31 1 (CS03 ∷ []) ∷
   rw⁻ 30 (q29 c4) ∷
   re 32 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 27 (q28 c4) ∷
   rw 25 (q30 c4) ∷
   rw 25 (q4 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 33 (q2 c4) ∷
   rw⁻ 30 (q3 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 24 (q3 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw⁻ 26 (q4 c4) ∷
   rw 26 (q5 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   re 26 5 (Sb2-0-41-3 ∷ []) ∷
   re 26 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   re 38 1 (CS03⁻ ∷ []) ∷
   rw⁻ 37 (q6 c4) ∷
   re 41 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 32 1 (CS03 ∷ []) ∷
   rw⁻ 28 (q7 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ []) ∷
   rw 26 (q8 c4) ∷
   rw 26 (q9 c4) ∷
   rw 26 (q10 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 34 (q11 c4) ∷
   rw⁻ 33 (q12 c4) ∷
   rw 32 (q13 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 32 (q14 c4) ∷
   rw⁻ 35 (q12 c4) ∷
   rw 34 (q13 c4) ∷
   rw⁻ 33 (q12 c4) ∷
   rw⁻ 28 (q11 c4) ∷
   rw⁻ 27 (q12 c4) ∷
   rw 26 (q13 c4) ∷
   rw⁻ 25 (q12 c4) ∷
   rw⁻ 26 (q14 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw 28 (q13 c4) ∷ []) Eq.refl
