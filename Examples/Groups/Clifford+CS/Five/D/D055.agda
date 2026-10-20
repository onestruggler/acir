{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D055 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0397 ; wl0398 ; wl0399 ; wl0400 ; wl0433 ; wl0434 ; wl0435 ; wl0436 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0444 ; wl0445 ; wl0447 ; wl0448 ; wl0449 ; wl0450 ; wl0451 ; wp0139 ; wp0143 ; wp0155 ; wp0156 ; wp0157 ; wp0158 ; wp0159 ; wp0160 ; wp0161 ; wp0162)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym34-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym12-at021021 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 ; lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 ; lem-beta-T-at0210213443 ; lem-beta-T-at022330 ; lem-sym12-at02203443 ; lem-sym34-at0220)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CCZ123 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ []) (wl0445 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ []) (wp0155 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Sb⁻2-0-41-3 ∷ Toff204 ∷ []) (Toff204 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ []) (wl0434 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx⁻2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx⁻2-0413 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CX13 ∷ []) (K3 ∷ CZ13 ∷ K3⁻ ∷ []) (wl0435 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym12-at021021 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1304 ∷ []) (lem-sym23-at0220 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X1 ∷ K3 ∷ []) (K3 ∷ X1 ∷ []) (c₂ (X ↑) (K ↑))
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) (wp0156 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CZ13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CZ13 ∷ []) (wl0436 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CZ13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CZ13 ∷ []) (wp0157 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CZ13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CZ13 ∷ []) (wl0437 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CZ13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CZ13 ∷ []) (wl0438 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (X1 ∷ K3⁻ ∷ []) (K3⁻ ∷ X1 ∷ []) (c₂ (X ↑) ((K • iI) ↑))
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) (wp0158 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (K3 ∷ CZ13 ∷ K3⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ K3 ∷ CZ13 ∷ K3⁻ ∷ []) (wl0439 (lit c4))
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
  q30 c4 = eqn (Bx⁻2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx⁻2-0413 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0210243143 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) (wl0443 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ123 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0444 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS14 ∷ X1 ∷ CS14 ∷ X1 ∷ []) (X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ []) (wl0447 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CS14 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS14 ∷ []) (wl0448 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS14 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS14 ∷ []) (wp0159 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS14 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS14 ∷ []) (wl0449 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CS14 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS14 ∷ []) (wp0160 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CS14 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS14 ∷ []) (wp0161 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CS14 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CS14 ∷ []) (wp0162 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (S1⁻ ∷ X1 ∷ CS14 ∷ X1 ∷ []) (X1 ∷ CS14 ∷ X1 ∷ S1⁻ ∷ []) (wl0450 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (S1⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ []) (wl0397 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (S1⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1⁻ ∷ []) (wp0139 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ []) (wl0398 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (S1⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1⁻ ∷ []) (wl0400 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (S1⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1⁻ ∷ []) (wl0399 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (S1⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ S1⁻ ∷ []) (wl0451 (lit c4))

-- F1 CS-K0 part10: 367 steps
lem-F1-CS-K0-part10 : Ws → ⟪ (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ
lem-F1-CS-K0-part10 c4 = derive (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  (re 40 1 (CS03 ∷ []) ∷
   rw⁻ 39 (q1 c4) ∷
   re 41 1 (Sb2-0-3-1 ∷ []) ∷
   rw 42 (q2 c4) ∷
   rw 43 (q2 c4) ∷
   rw 44 (q2 c4) ∷
   rw 45 (q2 c4) ∷
   re 41 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 42 (q3 c4) ∷
   rw 41 (q4 c4) ∷
   rw⁻ 40 (q3 c4) ∷
   re 42 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 43 (q2 c4) ∷
   rw⁻ 46 (q2 c4) ∷
   rw⁻ 49 (q2 c4) ∷
   rw⁻ 52 (q2 c4) ∷
   rw 56 (q5 c4) ∷
   rw⁻ 55 (q6 c4) ∷
   rw 54 (q7 c4) ∷
   rw⁻ 53 (q6 c4) ∷
   rw 57 (q8 c4) ∷
   rw 55 (q9 c4) ∷
   rw 55 (q10 c4) ∷
   rw 55 (q11 c4) ∷
   rw 55 (q12 c4) ∷
   rw 55 (q13 c4) ∷
   rw 55 (q14 c4) ∷
   rw⁻ 56 (q2 c4) ∷
   rw⁻ 59 (q2 c4) ∷
   rw⁻ 62 (q2 c4) ∷
   rw 65 (q15 c4) ∷
   rw 64 (q16 c4) ∷
   rw 63 (q15 c4) ∷
   rw 65 (q17 c4) ∷
   rw⁻ 66 (q2 c4) ∷
   rw⁻ 69 (q2 c4) ∷
   rw⁻ 72 (q2 c4) ∷
   rw⁻ 75 (q2 c4) ∷
   rw⁻ 76 (q18 c4) ∷
   rw⁻ 73 (q19 c4) ∷
   rw⁻ 70 (q20 c4) ∷
   rw⁻ 67 (q19 c4) ∷
   rw⁻ 64 (q21 c4) ∷
   rw 67 (q2 c4) ∷
   rw 68 (q2 c4) ∷
   rw 69 (q2 c4) ∷
   rw 70 (q2 c4) ∷
   rw⁻ 66 (q17 c4) ∷
   rw 67 (q22 c4) ∷
   rw 66 (q23 c4) ∷
   rw 65 (q22 c4) ∷
   rw⁻ 60 (q24 c4) ∷
   rw 59 (q15 c4) ∷
   rw 58 (q16 c4) ∷
   rw 57 (q15 c4) ∷
   rw 59 (q17 c4) ∷
   rw⁻ 60 (q2 c4) ∷
   rw⁻ 63 (q2 c4) ∷
   rw⁻ 66 (q2 c4) ∷
   rw⁻ 69 (q2 c4) ∷
   rw⁻ 70 (q18 c4) ∷
   rw⁻ 67 (q19 c4) ∷
   rw⁻ 64 (q20 c4) ∷
   rw⁻ 61 (q19 c4) ∷
   rw⁻ 58 (q21 c4) ∷
   rw 61 (q2 c4) ∷
   rw 62 (q2 c4) ∷
   rw 63 (q2 c4) ∷
   rw 64 (q2 c4) ∷
   rw⁻ 60 (q17 c4) ∷
   rw 61 (q22 c4) ∷
   rw 60 (q23 c4) ∷
   rw 59 (q22 c4) ∷
   rw⁻ 54 (q24 c4) ∷
   rw 59 (q2 c4) ∷
   rw 60 (q2 c4) ∷
   rw 61 (q2 c4) ∷
   rw⁻ 58 (q14 c4) ∷
   rw 58 (q25 c4) ∷
   rw 58 (q26 c4) ∷
   rw 58 (q27 c4) ∷
   rw 58 (q28 c4) ∷
   rw⁻ 58 (q9 c4) ∷
   rw⁻ 54 (q8 c4) ∷
   rw⁻ 57 (q29 c4) ∷
   rw 56 (q30 c4) ∷
   rw⁻ 55 (q29 c4) ∷
   rw 59 (q8 c4) ∷
   rw 57 (q9 c4) ∷
   rw 57 (q10 c4) ∷
   rw 57 (q11 c4) ∷
   rw 57 (q12 c4) ∷
   rw 57 (q13 c4) ∷
   rw 57 (q14 c4) ∷
   rw⁻ 58 (q2 c4) ∷
   rw⁻ 61 (q2 c4) ∷
   rw⁻ 64 (q2 c4) ∷
   rw 67 (q15 c4) ∷
   rw 66 (q16 c4) ∷
   rw 65 (q15 c4) ∷
   rw 67 (q17 c4) ∷
   rw⁻ 68 (q2 c4) ∷
   rw⁻ 71 (q2 c4) ∷
   rw⁻ 74 (q2 c4) ∷
   rw⁻ 77 (q2 c4) ∷
   rw⁻ 78 (q18 c4) ∷
   rw⁻ 75 (q19 c4) ∷
   rw⁻ 72 (q20 c4) ∷
   rw⁻ 69 (q19 c4) ∷
   rw⁻ 66 (q21 c4) ∷
   rw 69 (q2 c4) ∷
   rw 70 (q2 c4) ∷
   rw 71 (q2 c4) ∷
   rw 72 (q2 c4) ∷
   rw⁻ 68 (q17 c4) ∷
   rw 69 (q22 c4) ∷
   rw 68 (q23 c4) ∷
   rw 67 (q22 c4) ∷
   rw⁻ 62 (q24 c4) ∷
   rw 61 (q15 c4) ∷
   rw 60 (q16 c4) ∷
   rw 59 (q15 c4) ∷
   rw 61 (q17 c4) ∷
   rw⁻ 62 (q2 c4) ∷
   rw⁻ 65 (q2 c4) ∷
   rw⁻ 68 (q2 c4) ∷
   rw⁻ 71 (q2 c4) ∷
   rw⁻ 72 (q18 c4) ∷
   rw⁻ 69 (q19 c4) ∷
   rw⁻ 66 (q20 c4) ∷
   rw⁻ 63 (q19 c4) ∷
   rw⁻ 60 (q21 c4) ∷
   rw 63 (q2 c4) ∷
   rw 64 (q2 c4) ∷
   rw 65 (q2 c4) ∷
   rw 66 (q2 c4) ∷
   rw⁻ 62 (q17 c4) ∷
   rw 63 (q22 c4) ∷
   rw 62 (q23 c4) ∷
   rw 61 (q22 c4) ∷
   rw⁻ 56 (q24 c4) ∷
   rw 61 (q2 c4) ∷
   rw 62 (q2 c4) ∷
   rw 63 (q2 c4) ∷
   rw⁻ 60 (q14 c4) ∷
   rw 60 (q25 c4) ∷
   rw 60 (q26 c4) ∷
   rw 60 (q27 c4) ∷
   rw 60 (q28 c4) ∷
   rw⁻ 60 (q9 c4) ∷
   rw⁻ 56 (q8 c4) ∷
   rw 58 (q9 c4) ∷
   rw 58 (q10 c4) ∷
   rw 58 (q31 c4) ∷
   rw⁻ 59 (q2 c4) ∷
   rw⁻ 62 (q2 c4) ∷
   rw⁻ 65 (q2 c4) ∷
   rw⁻ 66 (q32 c4) ∷
   rw⁻ 63 (q33 c4) ∷
   rw⁻ 60 (q32 c4) ∷
   rw⁻ 57 (q33 c4) ∷
   rw 60 (q2 c4) ∷
   rw 61 (q2 c4) ∷
   rw 62 (q2 c4) ∷
   rw⁻ 59 (q31 c4) ∷
   rw 59 (q28 c4) ∷
   rw⁻ 59 (q9 c4) ∷
   rw⁻ 53 (q5 c4) ∷
   rw⁻ 50 (q34 c4) ∷
   re 48 1 (CS03⁻ ∷ []) ∷
   rw⁻ 47 (q35 c4) ∷
   re 49 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 44 (q34 c4) ∷
   re 42 1 (CS03 ∷ []) ∷
   rw⁻ 41 (q1 c4) ∷
   re 43 1 (Sb2-0-3-1 ∷ []) ∷
   rw 44 (q2 c4) ∷
   rw 45 (q2 c4) ∷
   rw 46 (q2 c4) ∷
   rw 47 (q2 c4) ∷
   re 43 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 38 (q36 c4) ∷
   rw⁻ 38 (q9 c4) ∷
   re 34 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 50 (q37 c4) ∷
   re 48 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 49 (q2 c4) ∷
   rw⁻ 52 (q2 c4) ∷
   rw⁻ 55 (q2 c4) ∷
   rw⁻ 58 (q2 c4) ∷
   rw 60 (q9 c4) ∷
   rw 60 (q36 c4) ∷
   rw⁻ 61 (q2 c4) ∷
   rw⁻ 64 (q2 c4) ∷
   rw⁻ 67 (q2 c4) ∷
   rw⁻ 68 (q38 c4) ∷
   rw⁻ 65 (q39 c4) ∷
   rw⁻ 62 (q38 c4) ∷
   rw⁻ 59 (q39 c4) ∷
   rw 62 (q2 c4) ∷
   rw 63 (q2 c4) ∷
   rw 64 (q2 c4) ∷
   rw⁻ 61 (q36 c4) ∷
   rw⁻ 61 (q9 c4) ∷
   rw⁻ 56 (q40 c4) ∷
   re 54 1 (CS03⁻ ∷ []) ∷
   rw⁻ 53 (q41 c4) ∷
   re 55 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 50 (q40 c4) ∷
   re 48 1 (CS03 ∷ []) ∷
   rw⁻ 47 (q42 c4) ∷
   re 49 1 (Sb2-0-3-1 ∷ []) ∷
   rw 50 (q2 c4) ∷
   rw 51 (q2 c4) ∷
   rw 52 (q2 c4) ∷
   rw 53 (q2 c4) ∷
   re 49 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 44 (q43 c4) ∷
   re 42 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 43 (q2 c4) ∷
   rw⁻ 46 (q2 c4) ∷
   rw⁻ 49 (q2 c4) ∷
   rw⁻ 52 (q2 c4) ∷
   rw 54 (q9 c4) ∷
   rw 54 (q36 c4) ∷
   rw⁻ 55 (q2 c4) ∷
   rw⁻ 58 (q2 c4) ∷
   rw⁻ 61 (q2 c4) ∷
   rw⁻ 62 (q38 c4) ∷
   rw⁻ 59 (q39 c4) ∷
   rw⁻ 56 (q38 c4) ∷
   rw⁻ 53 (q39 c4) ∷
   rw 56 (q2 c4) ∷
   rw 57 (q2 c4) ∷
   rw 58 (q2 c4) ∷
   rw⁻ 55 (q36 c4) ∷
   rw⁻ 55 (q9 c4) ∷
   rw⁻ 50 (q40 c4) ∷
   re 48 1 (CS03⁻ ∷ []) ∷
   rw⁻ 47 (q41 c4) ∷
   re 49 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 44 (q40 c4) ∷
   re 42 1 (CS03 ∷ []) ∷
   rw⁻ 41 (q42 c4) ∷
   re 43 1 (Sb2-0-3-1 ∷ []) ∷
   rw 44 (q2 c4) ∷
   rw 45 (q2 c4) ∷
   rw 46 (q2 c4) ∷
   rw 47 (q2 c4) ∷
   re 43 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 38 (q43 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 37 (q2 c4) ∷
   rw⁻ 40 (q2 c4) ∷
   rw⁻ 43 (q2 c4) ∷
   rw⁻ 46 (q2 c4) ∷
   rw 48 (q9 c4) ∷
   rw 48 (q36 c4) ∷
   rw⁻ 49 (q2 c4) ∷
   rw⁻ 52 (q2 c4) ∷
   rw⁻ 55 (q2 c4) ∷
   rw⁻ 56 (q38 c4) ∷
   rw⁻ 53 (q39 c4) ∷
   rw⁻ 50 (q38 c4) ∷
   rw⁻ 47 (q39 c4) ∷
   rw 50 (q2 c4) ∷
   rw 51 (q2 c4) ∷
   rw 52 (q2 c4) ∷
   rw⁻ 49 (q36 c4) ∷
   rw⁻ 49 (q9 c4) ∷
   rw⁻ 44 (q40 c4) ∷
   re 42 1 (CS03⁻ ∷ []) ∷
   rw⁻ 41 (q41 c4) ∷
   re 43 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 38 (q40 c4) ∷
   re 36 1 (CS03 ∷ []) ∷
   rw⁻ 35 (q42 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ []) ∷
   rw 38 (q2 c4) ∷
   rw 39 (q2 c4) ∷
   rw 40 (q2 c4) ∷
   rw 41 (q2 c4) ∷
   re 37 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 51 (q44 c4) ∷
   re 49 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 50 (q2 c4) ∷
   rw⁻ 53 (q2 c4) ∷
   rw⁻ 56 (q2 c4) ∷
   rw⁻ 59 (q2 c4) ∷
   rw 61 (q9 c4) ∷
   rw 61 (q36 c4) ∷
   rw⁻ 62 (q2 c4) ∷
   rw⁻ 65 (q2 c4) ∷
   rw⁻ 68 (q2 c4) ∷
   rw⁻ 69 (q45 c4) ∷
   rw⁻ 66 (q46 c4) ∷
   rw⁻ 63 (q45 c4) ∷
   rw⁻ 60 (q46 c4) ∷
   rw 63 (q2 c4) ∷
   rw 64 (q2 c4) ∷
   rw 65 (q2 c4) ∷
   rw⁻ 62 (q36 c4) ∷
   rw⁻ 62 (q9 c4) ∷
   rw⁻ 57 (q47 c4) ∷
   re 55 1 (CS03⁻ ∷ []) ∷
   rw⁻ 54 (q48 c4) ∷
   re 56 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 51 (q47 c4) ∷
   re 49 1 (CS03 ∷ []) ∷
   rw⁻ 48 (q49 c4) ∷
   re 50 1 (Sb2-0-3-1 ∷ []) ∷
   rw 51 (q2 c4) ∷
   rw 52 (q2 c4) ∷
   rw 53 (q2 c4) ∷
   rw 54 (q2 c4) ∷
   re 50 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 45 (q50 c4) ∷
   re 43 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 44 (q2 c4) ∷
   rw⁻ 47 (q2 c4) ∷
   rw⁻ 50 (q2 c4) ∷
   rw⁻ 53 (q2 c4) ∷
   rw 55 (q9 c4) ∷
   rw 55 (q36 c4) ∷
   rw⁻ 56 (q2 c4) ∷
   rw⁻ 59 (q2 c4) ∷
   rw⁻ 62 (q2 c4) ∷
   rw⁻ 63 (q45 c4) ∷
   rw⁻ 60 (q46 c4) ∷
   rw⁻ 57 (q45 c4) ∷
   rw⁻ 54 (q46 c4) ∷
   rw 57 (q2 c4) ∷
   rw 58 (q2 c4) ∷
   rw 59 (q2 c4) ∷
   rw⁻ 56 (q36 c4) ∷
   rw⁻ 56 (q9 c4) ∷
   rw⁻ 51 (q47 c4) ∷
   re 49 1 (CS03⁻ ∷ []) ∷
   rw⁻ 48 (q48 c4) ∷
   re 50 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 45 (q47 c4) ∷
   re 43 1 (CS03 ∷ []) ∷
   rw⁻ 42 (q49 c4) ∷
   re 44 1 (Sb2-0-3-1 ∷ []) ∷
   rw 45 (q2 c4) ∷
   rw 46 (q2 c4) ∷
   rw 47 (q2 c4) ∷
   rw 48 (q2 c4) ∷
   re 44 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 39 (q50 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 38 (q2 c4) ∷
   rw⁻ 41 (q2 c4) ∷
   rw⁻ 44 (q2 c4) ∷
   rw⁻ 47 (q2 c4) ∷
   rw 49 (q9 c4) ∷
   rw 49 (q36 c4) ∷
   rw⁻ 50 (q2 c4) ∷
   rw⁻ 53 (q2 c4) ∷
   rw⁻ 56 (q2 c4) ∷
   rw⁻ 57 (q45 c4) ∷
   rw⁻ 54 (q46 c4) ∷
   rw⁻ 51 (q45 c4) ∷
   rw⁻ 48 (q46 c4) ∷
   rw 51 (q2 c4) ∷
   rw 52 (q2 c4) ∷
   rw 53 (q2 c4) ∷ []) Eq.refl
