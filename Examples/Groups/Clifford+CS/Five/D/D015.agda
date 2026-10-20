{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D015 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0401 ; wl0402 ; wl0403 ; wl0404 ; wl0405 ; wl0406 ; wl0407 ; wl0408 ; wl0409 ; wl0410 ; wl0411 ; wl0412 ; wl0413 ; wl0414 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0433 ; wl0434 ; wl0435 ; wl0436 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0444 ; wp0142 ; wp0143 ; wp0144 ; wp0153 ; wp0154 ; wp0155 ; wp0156 ; wp0157 ; wp0158)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym34-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym12-at021021 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 ; lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-beta-T-at022330 ; lem-sym12-at02203443 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441 ; lem-sym34-at0220)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-TOFF203-CX41)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Toff203 ∷ CX41 ∷ []) (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) (wl0406 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0153 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0154 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) (wl0405 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sb⁻2-0-41-3 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0210243143 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sb⁻2-0-41-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ []) (wl0401 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sb⁻2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) (wl0418 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sb⁻2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS13 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ []) (wl0414 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (Toff204 ∷ []) (wp0142 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ []) (X1 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ []) (wl0413 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ []) (wl0412 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CS13 ∷ []) (wl0411 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS13 ∷ []) (wl0410 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CS13 ∷ X1 ∷ K2 ∷ X1 ∷ []) (X1 ∷ K2 ∷ X1 ∷ CS13 ∷ []) (wl0409 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ []) (wp0155 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Sb⁻2-0-41-3 ∷ Toff204 ∷ []) (Toff204 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ []) (wl0434 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (Bx⁻2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx⁻2-0413 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CX13 ∷ []) (K3 ∷ CZ13 ∷ K3⁻ ∷ []) (wl0435 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym12-at021021 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1304 ∷ []) (lem-sym23-at0220 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (X1 ∷ K3 ∷ []) (K3 ∷ X1 ∷ []) (c₂ (X ↑) (K ↑))
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) (wp0156 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CZ13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CZ13 ∷ []) (wl0436 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CZ13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CZ13 ∷ []) (wp0157 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (CZ13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CZ13 ∷ []) (wl0437 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CZ13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CZ13 ∷ []) (wl0438 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (X1 ∷ K3⁻ ∷ []) (K3⁻ ∷ X1 ∷ []) (c₂ (X ↑) ((K • iI) ↑))
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) (wp0158 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (K3 ∷ CZ13 ∷ K3⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ K3 ∷ CZ13 ∷ K3⁻ ∷ []) (wl0439 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (Bx2-1304 ∷ []) (Bx2-1034 ∷ []) (lem-sym23-at022330 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1043 ∷ []) (lem-sym34-at0220 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ []) (wl0440 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Bx⁻2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx⁻2-0413 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0210243143 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) (wl0443 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ123 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0444 (lit c4))

-- F1 CS-K0 [rhs shape] part9: 337 steps
lem-F1-CS-K0-rhs-shape-part9 : Ws → ⟪ (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-rhs-shape-part9 c4 = derive (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw 52 (q1 c4) ∷
   rw⁻ 51 (q2 c4) ∷
   rw 54 (q3 c4) ∷
   rw 55 (q3 c4) ∷
   rw 56 (q3 c4) ∷
   rw⁻ 53 (q4 c4) ∷
   rw 53 (q5 c4) ∷
   rw 53 (q6 c4) ∷
   rw⁻ 53 (q7 c4) ∷
   re 44 1 (CS03⁻ ∷ []) ∷
   rw⁻ 40 (q8 c4) ∷
   re 47 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 38 1 (CS03 ∷ []) ∷
   rw⁻ 37 (q9 c4) ∷
   re 41 1 (Sb2-0-3-1 ∷ []) ∷
   rw 42 (q3 c4) ∷
   rw 43 (q3 c4) ∷
   rw 44 (q3 c4) ∷
   rw 45 (q3 c4) ∷
   re 41 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 42 (q10 c4) ∷
   rw 41 (q11 c4) ∷
   rw⁻ 40 (q10 c4) ∷
   rw⁻ 36 (q12 c4) ∷
   rw⁻ 39 (q13 c4) ∷
   rw 38 (q14 c4) ∷
   rw⁻ 37 (q13 c4) ∷
   rw 35 (q15 c4) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   rw⁻ 38 (q16 c4) ∷
   re 38 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 37 (q17 c4) ∷
   re 37 1 (CS03⁻ ∷ []) ∷
   rw⁻ 36 (q16 c4) ∷
   re 36 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 40 (q15 c4) ∷
   rw⁻ 39 (q18 c4) ∷
   rw 38 (q19 c4) ∷
   rw⁻ 37 (q18 c4) ∷
   rw 41 (q12 c4) ∷
   re 39 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 40 (q3 c4) ∷
   rw⁻ 43 (q3 c4) ∷
   rw⁻ 46 (q3 c4) ∷
   rw⁻ 49 (q3 c4) ∷
   rw 51 (q7 c4) ∷
   rw 51 (q20 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw⁻ 55 (q3 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 59 (q21 c4) ∷
   rw⁻ 57 (q22 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw⁻ 62 (q23 c4) ∷
   rw 60 (q24 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw⁻ 64 (q3 c4) ∷
   rw⁻ 67 (q3 c4) ∷
   rw⁻ 70 (q3 c4) ∷
   rw⁻ 71 (q25 c4) ∷
   rw⁻ 68 (q26 c4) ∷
   rw⁻ 65 (q27 c4) ∷
   rw⁻ 62 (q26 c4) ∷
   rw⁻ 59 (q28 c4) ∷
   rw 62 (q3 c4) ∷
   rw 63 (q3 c4) ∷
   rw 64 (q3 c4) ∷
   rw 65 (q3 c4) ∷
   rw⁻ 61 (q24 c4) ∷
   rw⁻ 56 (q29 c4) ∷
   rw 59 (q3 c4) ∷
   rw 60 (q3 c4) ∷
   rw 58 (q22 c4) ∷
   rw⁻ 53 (q21 c4) ∷
   rw⁻ 51 (q22 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw⁻ 55 (q3 c4) ∷
   rw⁻ 56 (q23 c4) ∷
   rw 54 (q24 c4) ∷
   rw⁻ 55 (q3 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw⁻ 64 (q3 c4) ∷
   rw⁻ 65 (q25 c4) ∷
   rw⁻ 62 (q26 c4) ∷
   rw⁻ 59 (q27 c4) ∷
   rw⁻ 56 (q26 c4) ∷
   rw⁻ 53 (q28 c4) ∷
   rw 56 (q3 c4) ∷
   rw 57 (q3 c4) ∷
   rw 58 (q3 c4) ∷
   rw 59 (q3 c4) ∷
   rw⁻ 55 (q24 c4) ∷
   rw⁻ 50 (q29 c4) ∷
   rw 53 (q3 c4) ∷
   rw 54 (q3 c4) ∷
   rw 52 (q22 c4) ∷
   rw 53 (q3 c4) ∷
   rw 54 (q3 c4) ∷
   rw 55 (q3 c4) ∷
   rw⁻ 52 (q20 c4) ∷
   rw⁻ 52 (q7 c4) ∷
   rw⁻ 47 (q30 c4) ∷
   re 45 1 (CS03⁻ ∷ []) ∷
   rw⁻ 44 (q31 c4) ∷
   re 46 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 41 (q30 c4) ∷
   re 39 1 (CS03 ∷ []) ∷
   rw⁻ 38 (q32 c4) ∷
   re 40 1 (Sb2-0-3-1 ∷ []) ∷
   rw 41 (q3 c4) ∷
   rw 42 (q3 c4) ∷
   rw 43 (q3 c4) ∷
   rw 44 (q3 c4) ∷
   re 40 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 40 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 41 (q3 c4) ∷
   rw⁻ 44 (q3 c4) ∷
   rw⁻ 47 (q3 c4) ∷
   rw⁻ 50 (q3 c4) ∷
   rw 52 (q7 c4) ∷
   rw 52 (q33 c4) ∷
   rw 52 (q34 c4) ∷
   rw 52 (q4 c4) ∷
   rw⁻ 53 (q3 c4) ∷
   rw⁻ 56 (q3 c4) ∷
   rw⁻ 59 (q3 c4) ∷
   rw⁻ 60 (q35 c4) ∷
   rw⁻ 59 (q2 c4) ∷
   rw 58 (q1 c4) ∷
   rw⁻ 57 (q2 c4) ∷
   rw⁻ 58 (q36 c4) ∷
   rw⁻ 61 (q2 c4) ∷
   rw 60 (q1 c4) ∷
   rw⁻ 59 (q2 c4) ∷
   rw⁻ 54 (q35 c4) ∷
   rw⁻ 53 (q2 c4) ∷
   rw 52 (q1 c4) ∷
   rw⁻ 51 (q2 c4) ∷
   rw⁻ 52 (q36 c4) ∷
   rw⁻ 55 (q2 c4) ∷
   rw 54 (q1 c4) ∷
   rw⁻ 53 (q2 c4) ∷
   rw 56 (q3 c4) ∷
   rw 57 (q3 c4) ∷
   rw 58 (q3 c4) ∷
   rw⁻ 55 (q4 c4) ∷
   rw 55 (q5 c4) ∷
   rw 55 (q6 c4) ∷
   rw⁻ 55 (q7 c4) ∷
   re 46 1 (CS03⁻ ∷ []) ∷
   rw⁻ 42 (q8 c4) ∷
   re 49 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 40 1 (CS03 ∷ []) ∷
   rw⁻ 39 (q9 c4) ∷
   re 43 1 (Sb2-0-3-1 ∷ []) ∷
   rw 44 (q3 c4) ∷
   rw 45 (q3 c4) ∷
   rw 46 (q3 c4) ∷
   rw 47 (q3 c4) ∷
   re 43 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 44 (q10 c4) ∷
   rw 43 (q11 c4) ∷
   rw⁻ 42 (q10 c4) ∷
   rw⁻ 38 (q12 c4) ∷
   rw⁻ 41 (q13 c4) ∷
   rw 40 (q14 c4) ∷
   rw⁻ 39 (q13 c4) ∷
   rw 37 (q15 c4) ∷
   rw 41 (q7 c4) ∷
   rw 41 (q20 c4) ∷
   rw⁻ 40 (q37 c4) ∷
   rw 39 (q38 c4) ∷
   rw⁻ 38 (q37 c4) ∷
   re 40 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 41 (q3 c4) ∷
   rw⁻ 44 (q3 c4) ∷
   rw⁻ 47 (q3 c4) ∷
   rw⁻ 50 (q3 c4) ∷
   rw 54 (q39 c4) ∷
   rw⁻ 53 (q40 c4) ∷
   rw 52 (q41 c4) ∷
   rw⁻ 51 (q40 c4) ∷
   rw 55 (q42 c4) ∷
   rw 53 (q7 c4) ∷
   rw 53 (q43 c4) ∷
   rw 53 (q44 c4) ∷
   rw 53 (q45 c4) ∷
   rw 53 (q46 c4) ∷
   rw 53 (q47 c4) ∷
   rw⁻ 54 (q3 c4) ∷
   rw⁻ 57 (q3 c4) ∷
   rw⁻ 60 (q3 c4) ∷
   rw 63 (q48 c4) ∷
   rw 62 (q49 c4) ∷
   rw 61 (q48 c4) ∷
   rw 63 (q24 c4) ∷
   rw⁻ 64 (q3 c4) ∷
   rw⁻ 67 (q3 c4) ∷
   rw⁻ 70 (q3 c4) ∷
   rw⁻ 73 (q3 c4) ∷
   rw⁻ 74 (q50 c4) ∷
   rw⁻ 71 (q51 c4) ∷
   rw⁻ 68 (q52 c4) ∷
   rw⁻ 65 (q51 c4) ∷
   rw⁻ 62 (q53 c4) ∷
   rw 65 (q3 c4) ∷
   rw 66 (q3 c4) ∷
   rw 67 (q3 c4) ∷
   rw 68 (q3 c4) ∷
   rw⁻ 64 (q24 c4) ∷
   rw 65 (q54 c4) ∷
   rw 64 (q55 c4) ∷
   rw 63 (q54 c4) ∷
   rw⁻ 58 (q56 c4) ∷
   rw 57 (q48 c4) ∷
   rw 56 (q49 c4) ∷
   rw 55 (q48 c4) ∷
   rw 57 (q24 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw⁻ 64 (q3 c4) ∷
   rw⁻ 67 (q3 c4) ∷
   rw⁻ 68 (q50 c4) ∷
   rw⁻ 65 (q51 c4) ∷
   rw⁻ 62 (q52 c4) ∷
   rw⁻ 59 (q51 c4) ∷
   rw⁻ 56 (q53 c4) ∷
   rw 59 (q3 c4) ∷
   rw 60 (q3 c4) ∷
   rw 61 (q3 c4) ∷
   rw 62 (q3 c4) ∷
   rw⁻ 58 (q24 c4) ∷
   rw 59 (q54 c4) ∷
   rw 58 (q55 c4) ∷
   rw 57 (q54 c4) ∷
   rw⁻ 52 (q56 c4) ∷
   rw 57 (q3 c4) ∷
   rw 58 (q3 c4) ∷
   rw 59 (q3 c4) ∷
   rw⁻ 56 (q47 c4) ∷
   rw 56 (q57 c4) ∷
   rw 56 (q58 c4) ∷
   rw 56 (q59 c4) ∷
   rw 56 (q60 c4) ∷
   rw⁻ 56 (q7 c4) ∷
   rw⁻ 52 (q42 c4) ∷
   rw⁻ 55 (q61 c4) ∷
   rw 54 (q62 c4) ∷
   rw⁻ 53 (q61 c4) ∷
   rw 57 (q42 c4) ∷
   rw 55 (q7 c4) ∷
   rw 55 (q43 c4) ∷
   rw 55 (q44 c4) ∷
   rw 55 (q45 c4) ∷
   rw 55 (q46 c4) ∷
   rw 55 (q47 c4) ∷
   rw⁻ 56 (q3 c4) ∷
   rw⁻ 59 (q3 c4) ∷
   rw⁻ 62 (q3 c4) ∷
   rw 65 (q48 c4) ∷
   rw 64 (q49 c4) ∷
   rw 63 (q48 c4) ∷
   rw 65 (q24 c4) ∷
   rw⁻ 66 (q3 c4) ∷
   rw⁻ 69 (q3 c4) ∷
   rw⁻ 72 (q3 c4) ∷
   rw⁻ 75 (q3 c4) ∷
   rw⁻ 76 (q50 c4) ∷
   rw⁻ 73 (q51 c4) ∷
   rw⁻ 70 (q52 c4) ∷
   rw⁻ 67 (q51 c4) ∷
   rw⁻ 64 (q53 c4) ∷
   rw 67 (q3 c4) ∷
   rw 68 (q3 c4) ∷
   rw 69 (q3 c4) ∷
   rw 70 (q3 c4) ∷
   rw⁻ 66 (q24 c4) ∷
   rw 67 (q54 c4) ∷
   rw 66 (q55 c4) ∷
   rw 65 (q54 c4) ∷
   rw⁻ 60 (q56 c4) ∷
   rw 59 (q48 c4) ∷
   rw 58 (q49 c4) ∷
   rw 57 (q48 c4) ∷
   rw 59 (q24 c4) ∷
   rw⁻ 60 (q3 c4) ∷
   rw⁻ 63 (q3 c4) ∷
   rw⁻ 66 (q3 c4) ∷
   rw⁻ 69 (q3 c4) ∷
   rw⁻ 70 (q50 c4) ∷
   rw⁻ 67 (q51 c4) ∷
   rw⁻ 64 (q52 c4) ∷
   rw⁻ 61 (q51 c4) ∷
   rw⁻ 58 (q53 c4) ∷
   rw 61 (q3 c4) ∷
   rw 62 (q3 c4) ∷
   rw 63 (q3 c4) ∷
   rw 64 (q3 c4) ∷
   rw⁻ 60 (q24 c4) ∷
   rw 61 (q54 c4) ∷
   rw 60 (q55 c4) ∷
   rw 59 (q54 c4) ∷
   rw⁻ 54 (q56 c4) ∷
   rw 59 (q3 c4) ∷
   rw 60 (q3 c4) ∷
   rw 61 (q3 c4) ∷
   rw⁻ 58 (q47 c4) ∷
   rw 58 (q57 c4) ∷
   rw 58 (q58 c4) ∷
   rw 58 (q59 c4) ∷
   rw 58 (q60 c4) ∷
   rw⁻ 58 (q7 c4) ∷
   rw⁻ 54 (q42 c4) ∷
   rw 56 (q7 c4) ∷
   rw 56 (q43 c4) ∷
   rw 56 (q63 c4) ∷
   rw⁻ 57 (q3 c4) ∷
   rw⁻ 60 (q3 c4) ∷
   rw⁻ 63 (q3 c4) ∷
   rw⁻ 64 (q64 c4) ∷
   rw⁻ 61 (q65 c4) ∷
   rw⁻ 58 (q64 c4) ∷
   rw⁻ 55 (q65 c4) ∷
   rw 58 (q3 c4) ∷
   rw 59 (q3 c4) ∷
   rw 60 (q3 c4) ∷
   rw⁻ 57 (q63 c4) ∷
   rw 57 (q60 c4) ∷
   rw⁻ 57 (q7 c4) ∷
   rw⁻ 51 (q39 c4) ∷
   rw⁻ 48 (q66 c4) ∷
   re 46 1 (CS03⁻ ∷ []) ∷
   rw⁻ 45 (q67 c4) ∷
   re 47 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 42 (q66 c4) ∷ []) Eq.refl
