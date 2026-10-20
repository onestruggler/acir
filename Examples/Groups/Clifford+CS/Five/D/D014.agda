{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D014 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0402 ; wl0404 ; wl0406 ; wl0407 ; wl0408 ; wl0409 ; wl0410 ; wl0411 ; wl0412 ; wl0413 ; wl0414 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0432 ; wl0433 ; wl0434 ; wl0435 ; wl0436 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0444 ; wl0445 ; wp0142 ; wp0143 ; wp0144 ; wp0151 ; wp0152 ; wp0155 ; wp0156 ; wp0157 ; wp0158)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym34-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym12-at021021 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 ; lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-beta-T-at022330 ; lem-sym12-at02203443 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at0220)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-TOFF203-CX41)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) (wl0443 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ123 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0444 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ123 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ []) (wl0445 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ []) (wp0155 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Sb⁻2-0-41-3 ∷ Toff204 ∷ []) (Toff204 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ []) (wl0434 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx⁻2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx⁻2-0413 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CX13 ∷ []) (K3 ∷ CZ13 ∷ K3⁻ ∷ []) (wl0435 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym12-at021021 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1304 ∷ []) (lem-sym23-at0220 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (X1 ∷ K3 ∷ []) (K3 ∷ X1 ∷ []) (c₂ (X ↑) (K ↑))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) (wp0156 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CZ13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CZ13 ∷ []) (wl0436 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CZ13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CZ13 ∷ []) (wp0157 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CZ13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CZ13 ∷ []) (wl0437 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CZ13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CZ13 ∷ []) (wl0438 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (X1 ∷ K3⁻ ∷ []) (K3⁻ ∷ X1 ∷ []) (c₂ (X ↑) ((K • iI) ↑))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) (wp0158 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (K3 ∷ CZ13 ∷ K3⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ K3 ∷ CZ13 ∷ K3⁻ ∷ []) (wl0439 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx2-1304 ∷ []) (Bx2-1034 ∷ []) (lem-sym23-at022330 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1043 ∷ []) (lem-sym34-at0220 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ []) (wl0440 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx⁻2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx⁻2-0413 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0210243143 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0151 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Toff314 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ Toff314 ∷ []) (wp0152 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Toff201 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ Toff201 ∷ []) (wl0432 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (X1 ∷ CCZ234 ∷ []) (CCZ234 ∷ X1 ∷ []) (c₂ (X ↑) (CCZ))
  q41 : Ws → Eqn
  q41 c4 = eqn (CK10⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CK10⁻ ∷ []) (c₂ (S ↑ • CK₁₀) (CCZ))
  q42 : Ws → Eqn
  q42 c4 = eqn (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) (wl0419 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (Sb⁻2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) (wl0418 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (Sb⁻2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CS13 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ []) (wl0414 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (Toff204 ∷ []) (wp0142 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ []) (X1 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ []) (wl0413 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ []) (wl0412 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CS13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CS13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CS13 ∷ []) (wl0411 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS13 ∷ []) (wl0410 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CS13 ∷ X1 ∷ K2 ∷ X1 ∷ []) (X1 ∷ K2 ∷ X1 ∷ CS13 ∷ []) (wl0409 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) (wl0406 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (Toff203 ∷ CX41 ∷ []) (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4))

-- F1 CS-K0 [rhs shape] part8: 340 steps
lem-F1-CS-K0-rhs-shape-part8 : Ws → ⟪ (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-rhs-shape-part8 c4 = derive (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 63 (q1 c4) ∷
   rw⁻ 66 (q1 c4) ∷
   rw⁻ 69 (q1 c4) ∷
   rw⁻ 70 (q2 c4) ∷
   rw⁻ 67 (q3 c4) ∷
   rw⁻ 64 (q2 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw 64 (q1 c4) ∷
   rw 65 (q1 c4) ∷
   rw 66 (q1 c4) ∷
   rw⁻ 63 (q4 c4) ∷
   rw 63 (q5 c4) ∷
   rw⁻ 63 (q6 c4) ∷
   rw⁻ 57 (q7 c4) ∷
   rw⁻ 54 (q8 c4) ∷
   re 52 1 (CS03⁻ ∷ []) ∷
   rw⁻ 51 (q9 c4) ∷
   re 53 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 48 (q8 c4) ∷
   re 46 1 (CS03 ∷ []) ∷
   rw⁻ 45 (q10 c4) ∷
   re 47 1 (Sb2-0-3-1 ∷ []) ∷
   rw 48 (q1 c4) ∷
   rw 49 (q1 c4) ∷
   rw 50 (q1 c4) ∷
   rw 51 (q1 c4) ∷
   re 47 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 48 (q11 c4) ∷
   rw 47 (q12 c4) ∷
   rw⁻ 46 (q11 c4) ∷
   re 48 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 49 (q1 c4) ∷
   rw⁻ 52 (q1 c4) ∷
   rw⁻ 55 (q1 c4) ∷
   rw⁻ 58 (q1 c4) ∷
   rw 62 (q7 c4) ∷
   rw⁻ 61 (q13 c4) ∷
   rw 60 (q14 c4) ∷
   rw⁻ 59 (q13 c4) ∷
   rw 63 (q15 c4) ∷
   rw 61 (q6 c4) ∷
   rw 61 (q16 c4) ∷
   rw 61 (q17 c4) ∷
   rw 61 (q18 c4) ∷
   rw 61 (q19 c4) ∷
   rw 61 (q20 c4) ∷
   rw⁻ 62 (q1 c4) ∷
   rw⁻ 65 (q1 c4) ∷
   rw⁻ 68 (q1 c4) ∷
   rw 71 (q21 c4) ∷
   rw 70 (q22 c4) ∷
   rw 69 (q21 c4) ∷
   rw 71 (q23 c4) ∷
   rw⁻ 72 (q1 c4) ∷
   rw⁻ 75 (q1 c4) ∷
   rw⁻ 78 (q1 c4) ∷
   rw⁻ 81 (q1 c4) ∷
   rw⁻ 82 (q24 c4) ∷
   rw⁻ 79 (q25 c4) ∷
   rw⁻ 76 (q26 c4) ∷
   rw⁻ 73 (q25 c4) ∷
   rw⁻ 70 (q27 c4) ∷
   rw 73 (q1 c4) ∷
   rw 74 (q1 c4) ∷
   rw 75 (q1 c4) ∷
   rw 76 (q1 c4) ∷
   rw⁻ 72 (q23 c4) ∷
   rw 73 (q28 c4) ∷
   rw 72 (q29 c4) ∷
   rw 71 (q28 c4) ∷
   rw⁻ 66 (q30 c4) ∷
   rw 65 (q21 c4) ∷
   rw 64 (q22 c4) ∷
   rw 63 (q21 c4) ∷
   rw 65 (q23 c4) ∷
   rw⁻ 66 (q1 c4) ∷
   rw⁻ 69 (q1 c4) ∷
   rw⁻ 72 (q1 c4) ∷
   rw⁻ 75 (q1 c4) ∷
   rw⁻ 76 (q24 c4) ∷
   rw⁻ 73 (q25 c4) ∷
   rw⁻ 70 (q26 c4) ∷
   rw⁻ 67 (q25 c4) ∷
   rw⁻ 64 (q27 c4) ∷
   rw 67 (q1 c4) ∷
   rw 68 (q1 c4) ∷
   rw 69 (q1 c4) ∷
   rw 70 (q1 c4) ∷
   rw⁻ 66 (q23 c4) ∷
   rw 67 (q28 c4) ∷
   rw 66 (q29 c4) ∷
   rw 65 (q28 c4) ∷
   rw⁻ 60 (q30 c4) ∷
   rw 65 (q1 c4) ∷
   rw 66 (q1 c4) ∷
   rw 67 (q1 c4) ∷
   rw⁻ 64 (q20 c4) ∷
   rw 64 (q31 c4) ∷
   rw 64 (q32 c4) ∷
   rw 64 (q33 c4) ∷
   rw 64 (q5 c4) ∷
   rw⁻ 64 (q6 c4) ∷
   rw⁻ 60 (q15 c4) ∷
   rw⁻ 63 (q34 c4) ∷
   rw 62 (q35 c4) ∷
   rw⁻ 61 (q34 c4) ∷
   rw 65 (q15 c4) ∷
   rw 63 (q6 c4) ∷
   rw 63 (q16 c4) ∷
   rw 63 (q17 c4) ∷
   rw 63 (q18 c4) ∷
   rw 63 (q19 c4) ∷
   rw 63 (q20 c4) ∷
   rw⁻ 64 (q1 c4) ∷
   rw⁻ 67 (q1 c4) ∷
   rw⁻ 70 (q1 c4) ∷
   rw 73 (q21 c4) ∷
   rw 72 (q22 c4) ∷
   rw 71 (q21 c4) ∷
   rw 73 (q23 c4) ∷
   rw⁻ 74 (q1 c4) ∷
   rw⁻ 77 (q1 c4) ∷
   rw⁻ 80 (q1 c4) ∷
   rw⁻ 83 (q1 c4) ∷
   rw⁻ 84 (q24 c4) ∷
   rw⁻ 81 (q25 c4) ∷
   rw⁻ 78 (q26 c4) ∷
   rw⁻ 75 (q25 c4) ∷
   rw⁻ 72 (q27 c4) ∷
   rw 75 (q1 c4) ∷
   rw 76 (q1 c4) ∷
   rw 77 (q1 c4) ∷
   rw 78 (q1 c4) ∷
   rw⁻ 74 (q23 c4) ∷
   rw 75 (q28 c4) ∷
   rw 74 (q29 c4) ∷
   rw 73 (q28 c4) ∷
   rw⁻ 68 (q30 c4) ∷
   rw 67 (q21 c4) ∷
   rw 66 (q22 c4) ∷
   rw 65 (q21 c4) ∷
   rw 67 (q23 c4) ∷
   rw⁻ 68 (q1 c4) ∷
   rw⁻ 71 (q1 c4) ∷
   rw⁻ 74 (q1 c4) ∷
   rw⁻ 77 (q1 c4) ∷
   rw⁻ 78 (q24 c4) ∷
   rw⁻ 75 (q25 c4) ∷
   rw⁻ 72 (q26 c4) ∷
   rw⁻ 69 (q25 c4) ∷
   rw⁻ 66 (q27 c4) ∷
   rw 69 (q1 c4) ∷
   rw 70 (q1 c4) ∷
   rw 71 (q1 c4) ∷
   rw 72 (q1 c4) ∷
   rw⁻ 68 (q23 c4) ∷
   rw 69 (q28 c4) ∷
   rw 68 (q29 c4) ∷
   rw 67 (q28 c4) ∷
   rw⁻ 62 (q30 c4) ∷
   rw 67 (q1 c4) ∷
   rw 68 (q1 c4) ∷
   rw 69 (q1 c4) ∷
   rw⁻ 66 (q20 c4) ∷
   rw 66 (q31 c4) ∷
   rw 66 (q32 c4) ∷
   rw 66 (q33 c4) ∷
   rw 66 (q5 c4) ∷
   rw⁻ 66 (q6 c4) ∷
   rw⁻ 62 (q15 c4) ∷
   rw 64 (q6 c4) ∷
   rw 64 (q16 c4) ∷
   rw 64 (q4 c4) ∷
   rw⁻ 65 (q1 c4) ∷
   rw⁻ 68 (q1 c4) ∷
   rw⁻ 71 (q1 c4) ∷
   rw⁻ 72 (q2 c4) ∷
   rw⁻ 69 (q3 c4) ∷
   rw⁻ 66 (q2 c4) ∷
   rw⁻ 63 (q3 c4) ∷
   rw 66 (q1 c4) ∷
   rw 67 (q1 c4) ∷
   rw 68 (q1 c4) ∷
   rw⁻ 65 (q4 c4) ∷
   rw 65 (q5 c4) ∷
   rw⁻ 65 (q6 c4) ∷
   rw⁻ 59 (q7 c4) ∷
   rw⁻ 56 (q8 c4) ∷
   re 54 1 (CS03⁻ ∷ []) ∷
   rw⁻ 53 (q9 c4) ∷
   re 55 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 50 (q8 c4) ∷
   re 48 1 (CS03 ∷ []) ∷
   rw⁻ 47 (q10 c4) ∷
   re 49 1 (Sb2-0-3-1 ∷ []) ∷
   rw 50 (q1 c4) ∷
   rw 51 (q1 c4) ∷
   rw 52 (q1 c4) ∷
   rw 53 (q1 c4) ∷
   re 49 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 44 (q36 c4) ∷
   rw⁻ 44 (q6 c4) ∷
   re 40 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 40 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 40 1 (CS03 ∷ []) ∷
   re 42 1 (CS03⁻ ∷ []) ∷
   rw⁻ 37 (q37 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ []) ∷
   re 39 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 40 (q38 c4) ∷
   rw 44 (q6 c4) ∷
   rw 44 (q16 c4) ∷
   rw 44 (q4 c4) ∷
   rw⁻ 41 (q39 c4) ∷
   rw 44 (q40 c4) ∷
   rw 43 (q41 c4) ∷
   rw 42 (q40 c4) ∷
   rw⁻ 43 (q39 c4) ∷
   rw 46 (q40 c4) ∷
   rw 45 (q41 c4) ∷
   rw 44 (q40 c4) ∷
   rw⁻ 41 (q4 c4) ∷
   rw 41 (q5 c4) ∷
   rw⁻ 41 (q6 c4) ∷
   re 37 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 37 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 37 1 (CS03 ∷ []) ∷
   rw⁻ 36 (q42 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ []) ∷
   rw 35 (q43 c4) ∷
   re 35 1 (CS03 ∷ []) ∷
   rw⁻ 34 (q42 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 38 (q44 c4) ∷
   rw⁻ 37 (q45 c4) ∷
   rw 36 (q46 c4) ∷
   rw⁻ 35 (q45 c4) ∷
   rw 39 (q47 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 38 (q1 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   rw⁻ 44 (q1 c4) ∷
   rw⁻ 47 (q1 c4) ∷
   rw 49 (q6 c4) ∷
   rw 49 (q36 c4) ∷
   rw⁻ 50 (q1 c4) ∷
   rw⁻ 53 (q1 c4) ∷
   rw⁻ 56 (q1 c4) ∷
   rw⁻ 57 (q48 c4) ∷
   rw⁻ 55 (q49 c4) ∷
   rw⁻ 56 (q1 c4) ∷
   rw⁻ 59 (q1 c4) ∷
   rw⁻ 60 (q50 c4) ∷
   rw 58 (q23 c4) ∷
   rw⁻ 59 (q1 c4) ∷
   rw⁻ 62 (q1 c4) ∷
   rw⁻ 65 (q1 c4) ∷
   rw⁻ 68 (q1 c4) ∷
   rw⁻ 69 (q51 c4) ∷
   rw⁻ 66 (q52 c4) ∷
   rw⁻ 63 (q53 c4) ∷
   rw⁻ 60 (q52 c4) ∷
   rw⁻ 57 (q54 c4) ∷
   rw 60 (q1 c4) ∷
   rw 61 (q1 c4) ∷
   rw 62 (q1 c4) ∷
   rw 63 (q1 c4) ∷
   rw⁻ 59 (q23 c4) ∷
   rw⁻ 54 (q55 c4) ∷
   rw 57 (q1 c4) ∷
   rw 58 (q1 c4) ∷
   rw 56 (q49 c4) ∷
   rw⁻ 51 (q48 c4) ∷
   rw⁻ 49 (q49 c4) ∷
   rw⁻ 50 (q1 c4) ∷
   rw⁻ 53 (q1 c4) ∷
   rw⁻ 54 (q50 c4) ∷
   rw 52 (q23 c4) ∷
   rw⁻ 53 (q1 c4) ∷
   rw⁻ 56 (q1 c4) ∷
   rw⁻ 59 (q1 c4) ∷
   rw⁻ 62 (q1 c4) ∷
   rw⁻ 63 (q51 c4) ∷
   rw⁻ 60 (q52 c4) ∷
   rw⁻ 57 (q53 c4) ∷
   rw⁻ 54 (q52 c4) ∷
   rw⁻ 51 (q54 c4) ∷
   rw 54 (q1 c4) ∷
   rw 55 (q1 c4) ∷
   rw 56 (q1 c4) ∷
   rw 57 (q1 c4) ∷
   rw⁻ 53 (q23 c4) ∷
   rw⁻ 48 (q55 c4) ∷
   rw 51 (q1 c4) ∷
   rw 52 (q1 c4) ∷
   rw 50 (q49 c4) ∷
   rw 51 (q1 c4) ∷
   rw 52 (q1 c4) ∷
   rw 53 (q1 c4) ∷
   rw⁻ 50 (q36 c4) ∷
   rw⁻ 50 (q6 c4) ∷
   rw⁻ 45 (q56 c4) ∷
   re 43 1 (CS03⁻ ∷ []) ∷
   rw⁻ 42 (q57 c4) ∷
   re 44 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 39 (q56 c4) ∷
   re 37 1 (CS03 ∷ []) ∷
   rw⁻ 36 (q58 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ []) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   rw 42 (q1 c4) ∷
   re 38 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 38 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw⁻ 45 (q1 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw 50 (q6 c4) ∷
   rw 50 (q59 c4) ∷
   rw 50 (q60 c4) ∷
   rw 50 (q61 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw⁻ 54 (q1 c4) ∷
   rw⁻ 57 (q1 c4) ∷
   rw⁻ 58 (q62 c4) ∷
   rw⁻ 57 (q63 c4) ∷
   rw 56 (q64 c4) ∷
   rw⁻ 55 (q63 c4) ∷
   rw⁻ 56 (q65 c4) ∷
   rw⁻ 59 (q63 c4) ∷
   rw 58 (q64 c4) ∷
   rw⁻ 57 (q63 c4) ∷
   rw⁻ 52 (q62 c4) ∷
   rw⁻ 51 (q63 c4) ∷
   rw 50 (q64 c4) ∷
   rw⁻ 49 (q63 c4) ∷
   rw⁻ 50 (q65 c4) ∷
   rw⁻ 53 (q63 c4) ∷ []) Eq.refl
