{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D041 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0386 ; wl0402 ; wl0403 ; wl0404 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0433 ; wl0434 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0444 ; wl0445 ; wl0454 ; wl0455 ; wl0461 ; wl0462 ; wl0463 ; wl0464 ; wp0131 ; wp0132 ; wp0143 ; wp0155 ; wp0168)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym34-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym12-at021021 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 ; lem-beta-T-at0210213443 ; lem-beta-T-at022330 ; lem-sym12-at02203443 ; lem-sym34-at0220)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-BOX⟨0·1234⟩-∣-CS40-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at0210243143)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ []) (wp0155 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Sb2-0-41-3 ∷ Toff204 ∷ []) (Toff204 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at0210243143 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ123 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0444 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) (wl0443 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ123 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ []) (wl0445 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ []) (wl0434 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS40-at0210243143 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym12-at021021 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1304 ∷ []) (lem-sym23-at0220 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CX13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx2-1304 ∷ []) (Bx2-1034 ∷ []) (lem-sym23-at022330 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1043 ∷ []) (lem-sym34-at0220 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ []) (wl0440 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0131 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Toff314 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff314 ∷ []) (wp0132 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Toff201 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff201 ∷ []) (wl0386 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (X1 ∷ CCZ234 ∷ []) (CCZ234 ∷ X1 ∷ []) (c₂ (X ↑) (CCZ))
  q38 : Ws → Eqn
  q38 c4 = eqn (CK10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK10 ∷ []) (c₂ (CK₁₀) (CCZ))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) (wl0419 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) (wl0418 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Sb2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) (wl0454 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) (wl0455 (lit c4))

-- F1 CS-K0 [rhs shape] part35: 344 steps
lem-F1-CS-K0-rhs-shape-part35 : Ws → ⟪ (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CCZ134 ∷ X1 ∷ K3⁻ ∷ Sb2-0-41-3 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-rhs-shape-part35 c4 = derive (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CCZ134 ∷ X1 ∷ K3⁻ ∷ Sb2-0-41-3 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 30 (q1 c4) ∷
   rw 28 (q2 c4) ∷
   rw 32 (q3 c4) ∷
   rw 32 (q4 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw 30 (q6 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   re 31 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q7 c4) ∷
   rw⁻ 35 (q7 c4) ∷
   rw⁻ 38 (q7 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   re 43 1 (CS03⁻ ∷ []) ∷
   rw⁻ 42 (q8 c4) ∷
   re 44 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 39 (q9 c4) ∷
   re 37 1 (CS03 ∷ []) ∷
   rw⁻ 36 (q10 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 33 (q9 c4) ∷
   rw 33 (q11 c4) ∷
   rw⁻ 32 (q12 c4) ∷
   rw 31 (q13 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw 32 (q14 c4) ∷
   rw 32 (q15 c4) ∷
   rw 32 (q16 c4) ∷
   rw 32 (q17 c4) ∷
   rw 32 (q18 c4) ∷
   rw⁻ 33 (q7 c4) ∷
   rw⁻ 36 (q7 c4) ∷
   rw⁻ 39 (q7 c4) ∷
   rw 41 (q19 c4) ∷
   rw⁻ 42 (q7 c4) ∷
   rw⁻ 45 (q7 c4) ∷
   rw⁻ 48 (q7 c4) ∷
   rw⁻ 51 (q7 c4) ∷
   rw⁻ 52 (q20 c4) ∷
   rw⁻ 49 (q21 c4) ∷
   rw⁻ 46 (q22 c4) ∷
   rw⁻ 43 (q21 c4) ∷
   rw⁻ 40 (q23 c4) ∷
   rw 43 (q7 c4) ∷
   rw 44 (q7 c4) ∷
   rw 45 (q7 c4) ∷
   rw 46 (q7 c4) ∷
   rw⁻ 42 (q19 c4) ∷
   rw⁻ 37 (q24 c4) ∷
   rw 35 (q19 c4) ∷
   rw⁻ 36 (q7 c4) ∷
   rw⁻ 39 (q7 c4) ∷
   rw⁻ 42 (q7 c4) ∷
   rw⁻ 45 (q7 c4) ∷
   rw⁻ 46 (q20 c4) ∷
   rw⁻ 43 (q21 c4) ∷
   rw⁻ 40 (q22 c4) ∷
   rw⁻ 37 (q21 c4) ∷
   rw⁻ 34 (q23 c4) ∷
   rw 37 (q7 c4) ∷
   rw 38 (q7 c4) ∷
   rw 39 (q7 c4) ∷
   rw 40 (q7 c4) ∷
   rw⁻ 36 (q19 c4) ∷
   rw⁻ 31 (q24 c4) ∷
   rw 34 (q7 c4) ∷
   rw 35 (q7 c4) ∷
   rw 36 (q7 c4) ∷
   rw⁻ 33 (q18 c4) ∷
   rw 33 (q25 c4) ∷
   rw 33 (q26 c4) ∷
   rw 33 (q27 c4) ∷
   rw 33 (q28 c4) ∷
   rw⁻ 34 (q29 c4) ∷
   rw 33 (q30 c4) ∷
   rw⁻ 32 (q29 c4) ∷
   rw 34 (q14 c4) ∷
   rw 34 (q15 c4) ∷
   rw 34 (q16 c4) ∷
   rw 34 (q17 c4) ∷
   rw 34 (q18 c4) ∷
   rw⁻ 35 (q7 c4) ∷
   rw⁻ 38 (q7 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   rw 43 (q19 c4) ∷
   rw⁻ 44 (q7 c4) ∷
   rw⁻ 47 (q7 c4) ∷
   rw⁻ 50 (q7 c4) ∷
   rw⁻ 53 (q7 c4) ∷
   rw⁻ 54 (q20 c4) ∷
   rw⁻ 51 (q21 c4) ∷
   rw⁻ 48 (q22 c4) ∷
   rw⁻ 45 (q21 c4) ∷
   rw⁻ 42 (q23 c4) ∷
   rw 45 (q7 c4) ∷
   rw 46 (q7 c4) ∷
   rw 47 (q7 c4) ∷
   rw 48 (q7 c4) ∷
   rw⁻ 44 (q19 c4) ∷
   rw⁻ 39 (q24 c4) ∷
   rw 37 (q19 c4) ∷
   rw⁻ 38 (q7 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   rw⁻ 44 (q7 c4) ∷
   rw⁻ 47 (q7 c4) ∷
   rw⁻ 48 (q20 c4) ∷
   rw⁻ 45 (q21 c4) ∷
   rw⁻ 42 (q22 c4) ∷
   rw⁻ 39 (q21 c4) ∷
   rw⁻ 36 (q23 c4) ∷
   rw 39 (q7 c4) ∷
   rw 40 (q7 c4) ∷
   rw 41 (q7 c4) ∷
   rw 42 (q7 c4) ∷
   rw⁻ 38 (q19 c4) ∷
   rw⁻ 33 (q24 c4) ∷
   rw 36 (q7 c4) ∷
   rw 37 (q7 c4) ∷
   rw 38 (q7 c4) ∷
   rw⁻ 35 (q18 c4) ∷
   rw 35 (q25 c4) ∷
   rw 35 (q26 c4) ∷
   rw 35 (q27 c4) ∷
   rw 35 (q28 c4) ∷
   rw 35 (q14 c4) ∷
   rw 35 (q31 c4) ∷
   rw⁻ 36 (q7 c4) ∷
   rw⁻ 39 (q7 c4) ∷
   rw⁻ 42 (q7 c4) ∷
   rw⁻ 43 (q32 c4) ∷
   rw⁻ 40 (q33 c4) ∷
   rw⁻ 37 (q32 c4) ∷
   rw⁻ 34 (q33 c4) ∷
   rw 37 (q7 c4) ∷
   rw 38 (q7 c4) ∷
   rw 39 (q7 c4) ∷
   rw⁻ 36 (q31 c4) ∷
   rw 36 (q28 c4) ∷
   rw⁻ 30 (q11 c4) ∷
   rw 33 (q7 c4) ∷
   rw 34 (q7 c4) ∷
   rw 35 (q7 c4) ∷
   rw 36 (q7 c4) ∷
   re 32 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 33 (q5 c4) ∷
   rw 32 (q6 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   re 33 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 34 (q7 c4) ∷
   rw⁻ 37 (q7 c4) ∷
   rw⁻ 40 (q7 c4) ∷
   rw⁻ 43 (q7 c4) ∷
   re 45 1 (CS03⁻ ∷ []) ∷
   rw⁻ 44 (q8 c4) ∷
   re 46 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 41 (q9 c4) ∷
   re 39 1 (CS03 ∷ []) ∷
   rw⁻ 38 (q10 c4) ∷
   re 40 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 35 (q9 c4) ∷
   rw 35 (q11 c4) ∷
   rw⁻ 34 (q12 c4) ∷
   rw 33 (q13 c4) ∷
   rw⁻ 32 (q12 c4) ∷
   rw 34 (q14 c4) ∷
   rw 34 (q15 c4) ∷
   rw 34 (q16 c4) ∷
   rw 34 (q17 c4) ∷
   rw 34 (q18 c4) ∷
   rw⁻ 35 (q7 c4) ∷
   rw⁻ 38 (q7 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   rw 43 (q19 c4) ∷
   rw⁻ 44 (q7 c4) ∷
   rw⁻ 47 (q7 c4) ∷
   rw⁻ 50 (q7 c4) ∷
   rw⁻ 53 (q7 c4) ∷
   rw⁻ 54 (q20 c4) ∷
   rw⁻ 51 (q21 c4) ∷
   rw⁻ 48 (q22 c4) ∷
   rw⁻ 45 (q21 c4) ∷
   rw⁻ 42 (q23 c4) ∷
   rw 45 (q7 c4) ∷
   rw 46 (q7 c4) ∷
   rw 47 (q7 c4) ∷
   rw 48 (q7 c4) ∷
   rw⁻ 44 (q19 c4) ∷
   rw⁻ 39 (q24 c4) ∷
   rw 37 (q19 c4) ∷
   rw⁻ 38 (q7 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   rw⁻ 44 (q7 c4) ∷
   rw⁻ 47 (q7 c4) ∷
   rw⁻ 48 (q20 c4) ∷
   rw⁻ 45 (q21 c4) ∷
   rw⁻ 42 (q22 c4) ∷
   rw⁻ 39 (q21 c4) ∷
   rw⁻ 36 (q23 c4) ∷
   rw 39 (q7 c4) ∷
   rw 40 (q7 c4) ∷
   rw 41 (q7 c4) ∷
   rw 42 (q7 c4) ∷
   rw⁻ 38 (q19 c4) ∷
   rw⁻ 33 (q24 c4) ∷
   rw 36 (q7 c4) ∷
   rw 37 (q7 c4) ∷
   rw 38 (q7 c4) ∷
   rw⁻ 35 (q18 c4) ∷
   rw 35 (q25 c4) ∷
   rw 35 (q26 c4) ∷
   rw 35 (q27 c4) ∷
   rw 35 (q28 c4) ∷
   rw⁻ 36 (q29 c4) ∷
   rw 35 (q30 c4) ∷
   rw⁻ 34 (q29 c4) ∷
   rw 36 (q14 c4) ∷
   rw 36 (q15 c4) ∷
   rw 36 (q16 c4) ∷
   rw 36 (q17 c4) ∷
   rw 36 (q18 c4) ∷
   rw⁻ 37 (q7 c4) ∷
   rw⁻ 40 (q7 c4) ∷
   rw⁻ 43 (q7 c4) ∷
   rw 45 (q19 c4) ∷
   rw⁻ 46 (q7 c4) ∷
   rw⁻ 49 (q7 c4) ∷
   rw⁻ 52 (q7 c4) ∷
   rw⁻ 55 (q7 c4) ∷
   rw⁻ 56 (q20 c4) ∷
   rw⁻ 53 (q21 c4) ∷
   rw⁻ 50 (q22 c4) ∷
   rw⁻ 47 (q21 c4) ∷
   rw⁻ 44 (q23 c4) ∷
   rw 47 (q7 c4) ∷
   rw 48 (q7 c4) ∷
   rw 49 (q7 c4) ∷
   rw 50 (q7 c4) ∷
   rw⁻ 46 (q19 c4) ∷
   rw⁻ 41 (q24 c4) ∷
   rw 39 (q19 c4) ∷
   rw⁻ 40 (q7 c4) ∷
   rw⁻ 43 (q7 c4) ∷
   rw⁻ 46 (q7 c4) ∷
   rw⁻ 49 (q7 c4) ∷
   rw⁻ 50 (q20 c4) ∷
   rw⁻ 47 (q21 c4) ∷
   rw⁻ 44 (q22 c4) ∷
   rw⁻ 41 (q21 c4) ∷
   rw⁻ 38 (q23 c4) ∷
   rw 41 (q7 c4) ∷
   rw 42 (q7 c4) ∷
   rw 43 (q7 c4) ∷
   rw 44 (q7 c4) ∷
   rw⁻ 40 (q19 c4) ∷
   rw⁻ 35 (q24 c4) ∷
   rw 38 (q7 c4) ∷
   rw 39 (q7 c4) ∷
   rw 40 (q7 c4) ∷
   rw⁻ 37 (q18 c4) ∷
   rw 37 (q25 c4) ∷
   rw 37 (q26 c4) ∷
   rw 37 (q27 c4) ∷
   rw 37 (q28 c4) ∷
   rw 37 (q14 c4) ∷
   rw 37 (q31 c4) ∷
   rw⁻ 38 (q7 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   rw⁻ 44 (q7 c4) ∷
   rw⁻ 45 (q32 c4) ∷
   rw⁻ 42 (q33 c4) ∷
   rw⁻ 39 (q32 c4) ∷
   rw⁻ 36 (q33 c4) ∷
   rw 39 (q7 c4) ∷
   rw 40 (q7 c4) ∷
   rw 41 (q7 c4) ∷
   rw⁻ 38 (q31 c4) ∷
   rw 38 (q28 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw 35 (q7 c4) ∷
   rw 36 (q7 c4) ∷
   rw 37 (q7 c4) ∷
   rw 38 (q7 c4) ∷
   re 34 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   re 25 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 25 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 25 1 (CS03 ∷ []) ∷
   re 27 1 (CS03⁻ ∷ []) ∷
   rw⁻ 22 (q34 c4) ∷
   re 22 1 (Sb2-0-3-1 ∷ []) ∷
   re 24 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q35 c4) ∷
   rw 29 (q3 c4) ∷
   rw 29 (q14 c4) ∷
   rw 29 (q31 c4) ∷
   rw⁻ 26 (q36 c4) ∷
   rw 29 (q37 c4) ∷
   rw 28 (q38 c4) ∷
   rw 27 (q37 c4) ∷
   rw⁻ 28 (q36 c4) ∷
   rw 31 (q37 c4) ∷
   rw 30 (q38 c4) ∷
   rw 29 (q37 c4) ∷
   rw⁻ 26 (q31 c4) ∷
   rw 26 (q28 c4) ∷
   rw⁻ 26 (q3 c4) ∷
   re 22 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 22 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 22 1 (CS03 ∷ []) ∷
   rw⁻ 21 (q39 c4) ∷
   re 21 1 (Sb2-0-3-1 ∷ []) ∷
   rw 20 (q40 c4) ∷
   re 20 1 (CS03 ∷ []) ∷
   rw⁻ 19 (q39 c4) ∷
   re 19 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 22 (q41 c4) ∷
   rw 21 (q42 c4) ∷
   rw⁻ 20 (q41 c4) ∷
   rw 24 (q43 c4) ∷
   re 22 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q7 c4) ∷
   rw⁻ 26 (q7 c4) ∷
   rw⁻ 29 (q7 c4) ∷
   rw⁻ 32 (q7 c4) ∷
   re 34 1 (CS03⁻ ∷ []) ∷
   rw⁻ 33 (q44 c4) ∷
   re 35 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q45 c4) ∷
   re 28 1 (CS03 ∷ []) ∷
   rw⁻ 27 (q46 c4) ∷
   re 29 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q45 c4) ∷
   rw 22 (q14 c4) ∷
   rw 22 (q31 c4) ∷
   rw⁻ 23 (q7 c4) ∷
   rw⁻ 26 (q7 c4) ∷
   rw⁻ 29 (q7 c4) ∷
   rw⁻ 30 (q47 c4) ∷
   rw⁻ 27 (q48 c4) ∷
   rw⁻ 24 (q47 c4) ∷
   rw⁻ 21 (q48 c4) ∷
   rw 24 (q7 c4) ∷
   rw 25 (q7 c4) ∷ []) Eq.refl
