{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D011 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0393 ; wl0424 ; wl0425 ; wl0426 ; wl0427 ; wl0428 ; wl0429 ; wl0430 ; wl0431 ; wl0433 ; wl0434 ; wl0435 ; wl0436 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0444 ; wl0445 ; wp0143 ; wp0146 ; wp0147 ; wp0148 ; wp0149 ; wp0150 ; wp0155 ; wp0156 ; wp0157 ; wp0158)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym34-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym12-at021021 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 ; lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 ; lem-beta-T-at0210213443 ; lem-beta-T-at022330 ; lem-sym12-at02203443 ; lem-sym34-at0220)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) (wp0156 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X1 ∷ K3 ∷ []) (K3 ∷ X1 ∷ []) (c₂ (X ↑) (K ↑))
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CZ13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CZ13 ∷ []) (wl0436 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CZ13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CZ13 ∷ []) (wp0157 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CZ13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CZ13 ∷ []) (wl0437 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CZ13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CZ13 ∷ []) (wl0438 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (X1 ∷ K3⁻ ∷ []) (K3⁻ ∷ X1 ∷ []) (c₂ (X ↑) ((K • iI) ↑))
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) (wp0158 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (K3 ∷ CZ13 ∷ K3⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ K3 ∷ CZ13 ∷ K3⁻ ∷ []) (wl0439 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx2-1304 ∷ []) (Bx2-1034 ∷ []) (lem-sym23-at022330 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1043 ∷ []) (lem-sym34-at0220 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CX13 ∷ []) (K3 ∷ CZ13 ∷ K3⁻ ∷ []) (wl0435 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) (wl0443 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ123 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0444 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ123 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ []) (wl0445 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ []) (wp0155 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Sb⁻2-0-41-3 ∷ Toff204 ∷ []) (Toff204 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ []) (wl0434 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx⁻2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx⁻2-0413 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym12-at021021 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1304 ∷ []) (lem-sym23-at0220 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ []) (wl0440 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx⁻2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx⁻2-0413 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0210243143 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CK10⁻ ∷ []) (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ []) (wl0424 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CS01⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ []) (wl0425 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01⁻ ∷ []) (wp0146 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ []) (wp0147 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0426 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01⁻ ∷ []) (wl0427 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (K0⁻ ∷ X1 ∷ []) (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X))
  q44 : Ws → Eqn
  q44 c4 = eqn (K0⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (CCZ ↑))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CS01⁻ ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ []) (wp0148 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CS01⁻ ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01⁻ ∷ []) (wl0428 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0429 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01⁻ ∷ []) (wl0430 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wl0431 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0149 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0150 c4)

-- F1 CS-K0 [rhs shape] part5: 336 steps
lem-F1-CS-K0-rhs-shape-part5 : Ws → ⟪ (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ K3 ∷ X1 ∷ CZ13 ∷ K3⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-rhs-shape-part5 c4 = derive (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ K3 ∷ X1 ∷ CZ13 ∷ K3⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw 56 (q1 c4) ∷
   rw 55 (q2 c4) ∷
   rw 57 (q3 c4) ∷
   rw⁻ 58 (q4 c4) ∷
   rw⁻ 61 (q4 c4) ∷
   rw⁻ 64 (q4 c4) ∷
   rw⁻ 67 (q4 c4) ∷
   rw⁻ 68 (q5 c4) ∷
   rw⁻ 65 (q6 c4) ∷
   rw⁻ 62 (q7 c4) ∷
   rw⁻ 59 (q6 c4) ∷
   rw⁻ 56 (q8 c4) ∷
   rw 59 (q4 c4) ∷
   rw 60 (q4 c4) ∷
   rw 61 (q4 c4) ∷
   rw 62 (q4 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw 59 (q9 c4) ∷
   rw 58 (q10 c4) ∷
   rw 57 (q9 c4) ∷
   rw⁻ 52 (q11 c4) ∷
   rw 57 (q4 c4) ∷
   rw 58 (q4 c4) ∷
   rw 59 (q4 c4) ∷
   rw⁻ 56 (q12 c4) ∷
   rw 56 (q13 c4) ∷
   rw 56 (q14 c4) ∷
   rw 56 (q15 c4) ∷
   rw 56 (q16 c4) ∷
   rw⁻ 56 (q17 c4) ∷
   rw⁻ 52 (q18 c4) ∷
   rw 54 (q17 c4) ∷
   rw 54 (q19 c4) ∷
   rw 54 (q20 c4) ∷
   rw⁻ 55 (q4 c4) ∷
   rw⁻ 58 (q4 c4) ∷
   rw⁻ 61 (q4 c4) ∷
   rw⁻ 62 (q21 c4) ∷
   rw⁻ 59 (q22 c4) ∷
   rw⁻ 56 (q21 c4) ∷
   rw⁻ 53 (q22 c4) ∷
   rw 56 (q4 c4) ∷
   rw 57 (q4 c4) ∷
   rw 58 (q4 c4) ∷
   rw⁻ 55 (q20 c4) ∷
   rw 55 (q16 c4) ∷
   rw⁻ 55 (q17 c4) ∷
   rw⁻ 49 (q23 c4) ∷
   rw⁻ 46 (q24 c4) ∷
   re 44 1 (CS03⁻ ∷ []) ∷
   rw⁻ 43 (q25 c4) ∷
   re 45 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 40 (q24 c4) ∷
   re 38 1 (CS03 ∷ []) ∷
   rw⁻ 37 (q26 c4) ∷
   re 39 1 (Sb2-0-3-1 ∷ []) ∷
   rw 40 (q4 c4) ∷
   rw 41 (q4 c4) ∷
   rw 42 (q4 c4) ∷
   rw 43 (q4 c4) ∷
   re 39 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 40 (q27 c4) ∷
   rw 39 (q28 c4) ∷
   rw⁻ 38 (q27 c4) ∷
   re 40 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 41 (q4 c4) ∷
   rw⁻ 44 (q4 c4) ∷
   rw⁻ 47 (q4 c4) ∷
   rw⁻ 50 (q4 c4) ∷
   rw 54 (q23 c4) ∷
   rw⁻ 53 (q29 c4) ∷
   rw 52 (q30 c4) ∷
   rw⁻ 51 (q29 c4) ∷
   rw 55 (q18 c4) ∷
   rw 53 (q17 c4) ∷
   rw 53 (q19 c4) ∷
   rw 53 (q31 c4) ∷
   rw 53 (q32 c4) ∷
   rw 53 (q33 c4) ∷
   rw 53 (q12 c4) ∷
   rw⁻ 54 (q4 c4) ∷
   rw⁻ 57 (q4 c4) ∷
   rw⁻ 60 (q4 c4) ∷
   rw 63 (q2 c4) ∷
   rw 62 (q1 c4) ∷
   rw 61 (q2 c4) ∷
   rw 63 (q3 c4) ∷
   rw⁻ 64 (q4 c4) ∷
   rw⁻ 67 (q4 c4) ∷
   rw⁻ 70 (q4 c4) ∷
   rw⁻ 73 (q4 c4) ∷
   rw⁻ 74 (q5 c4) ∷
   rw⁻ 71 (q6 c4) ∷
   rw⁻ 68 (q7 c4) ∷
   rw⁻ 65 (q6 c4) ∷
   rw⁻ 62 (q8 c4) ∷
   rw 65 (q4 c4) ∷
   rw 66 (q4 c4) ∷
   rw 67 (q4 c4) ∷
   rw 68 (q4 c4) ∷
   rw⁻ 64 (q3 c4) ∷
   rw 65 (q9 c4) ∷
   rw 64 (q10 c4) ∷
   rw 63 (q9 c4) ∷
   rw⁻ 58 (q11 c4) ∷
   rw 57 (q2 c4) ∷
   rw 56 (q1 c4) ∷
   rw 55 (q2 c4) ∷
   rw 57 (q3 c4) ∷
   rw⁻ 58 (q4 c4) ∷
   rw⁻ 61 (q4 c4) ∷
   rw⁻ 64 (q4 c4) ∷
   rw⁻ 67 (q4 c4) ∷
   rw⁻ 68 (q5 c4) ∷
   rw⁻ 65 (q6 c4) ∷
   rw⁻ 62 (q7 c4) ∷
   rw⁻ 59 (q6 c4) ∷
   rw⁻ 56 (q8 c4) ∷
   rw 59 (q4 c4) ∷
   rw 60 (q4 c4) ∷
   rw 61 (q4 c4) ∷
   rw 62 (q4 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw 59 (q9 c4) ∷
   rw 58 (q10 c4) ∷
   rw 57 (q9 c4) ∷
   rw⁻ 52 (q11 c4) ∷
   rw 57 (q4 c4) ∷
   rw 58 (q4 c4) ∷
   rw 59 (q4 c4) ∷
   rw⁻ 56 (q12 c4) ∷
   rw 56 (q13 c4) ∷
   rw 56 (q14 c4) ∷
   rw 56 (q15 c4) ∷
   rw 56 (q16 c4) ∷
   rw⁻ 56 (q17 c4) ∷
   rw⁻ 52 (q18 c4) ∷
   rw⁻ 55 (q34 c4) ∷
   rw 54 (q35 c4) ∷
   rw⁻ 53 (q34 c4) ∷
   rw 57 (q18 c4) ∷
   rw 55 (q17 c4) ∷
   rw 55 (q19 c4) ∷
   rw 55 (q31 c4) ∷
   rw 55 (q32 c4) ∷
   rw 55 (q33 c4) ∷
   rw 55 (q12 c4) ∷
   rw⁻ 56 (q4 c4) ∷
   rw⁻ 59 (q4 c4) ∷
   rw⁻ 62 (q4 c4) ∷
   rw 65 (q2 c4) ∷
   rw 64 (q1 c4) ∷
   rw 63 (q2 c4) ∷
   rw 65 (q3 c4) ∷
   rw⁻ 66 (q4 c4) ∷
   rw⁻ 69 (q4 c4) ∷
   rw⁻ 72 (q4 c4) ∷
   rw⁻ 75 (q4 c4) ∷
   rw⁻ 76 (q5 c4) ∷
   rw⁻ 73 (q6 c4) ∷
   rw⁻ 70 (q7 c4) ∷
   rw⁻ 67 (q6 c4) ∷
   rw⁻ 64 (q8 c4) ∷
   rw 67 (q4 c4) ∷
   rw 68 (q4 c4) ∷
   rw 69 (q4 c4) ∷
   rw 70 (q4 c4) ∷
   rw⁻ 66 (q3 c4) ∷
   rw 67 (q9 c4) ∷
   rw 66 (q10 c4) ∷
   rw 65 (q9 c4) ∷
   rw⁻ 60 (q11 c4) ∷
   rw 59 (q2 c4) ∷
   rw 58 (q1 c4) ∷
   rw 57 (q2 c4) ∷
   rw 59 (q3 c4) ∷
   rw⁻ 60 (q4 c4) ∷
   rw⁻ 63 (q4 c4) ∷
   rw⁻ 66 (q4 c4) ∷
   rw⁻ 69 (q4 c4) ∷
   rw⁻ 70 (q5 c4) ∷
   rw⁻ 67 (q6 c4) ∷
   rw⁻ 64 (q7 c4) ∷
   rw⁻ 61 (q6 c4) ∷
   rw⁻ 58 (q8 c4) ∷
   rw 61 (q4 c4) ∷
   rw 62 (q4 c4) ∷
   rw 63 (q4 c4) ∷
   rw 64 (q4 c4) ∷
   rw⁻ 60 (q3 c4) ∷
   rw 61 (q9 c4) ∷
   rw 60 (q10 c4) ∷
   rw 59 (q9 c4) ∷
   rw⁻ 54 (q11 c4) ∷
   rw 59 (q4 c4) ∷
   rw 60 (q4 c4) ∷
   rw 61 (q4 c4) ∷
   rw⁻ 58 (q12 c4) ∷
   rw 58 (q13 c4) ∷
   rw 58 (q14 c4) ∷
   rw 58 (q15 c4) ∷
   rw 58 (q16 c4) ∷
   rw⁻ 58 (q17 c4) ∷
   rw⁻ 54 (q18 c4) ∷
   rw 56 (q17 c4) ∷
   rw 56 (q19 c4) ∷
   rw 56 (q20 c4) ∷
   rw⁻ 57 (q4 c4) ∷
   rw⁻ 60 (q4 c4) ∷
   rw⁻ 63 (q4 c4) ∷
   rw⁻ 64 (q21 c4) ∷
   rw⁻ 61 (q22 c4) ∷
   rw⁻ 58 (q21 c4) ∷
   rw⁻ 55 (q22 c4) ∷
   rw 58 (q4 c4) ∷
   rw 59 (q4 c4) ∷
   rw 60 (q4 c4) ∷
   rw⁻ 57 (q20 c4) ∷
   rw 57 (q16 c4) ∷
   rw⁻ 57 (q17 c4) ∷
   rw⁻ 51 (q23 c4) ∷
   rw⁻ 48 (q24 c4) ∷
   re 46 1 (CS03⁻ ∷ []) ∷
   rw⁻ 45 (q25 c4) ∷
   re 47 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 42 (q24 c4) ∷
   re 40 1 (CS03 ∷ []) ∷
   rw⁻ 39 (q26 c4) ∷
   re 41 1 (Sb2-0-3-1 ∷ []) ∷
   rw 42 (q4 c4) ∷
   rw 43 (q4 c4) ∷
   rw 44 (q4 c4) ∷
   rw 45 (q4 c4) ∷
   re 41 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw⁻ 36 (q36 c4) ∷
   rw⁻ 36 (q17 c4) ∷
   re 32 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 42 (q37 c4) ∷
   re 40 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 41 (q4 c4) ∷
   rw⁻ 44 (q4 c4) ∷
   rw⁻ 47 (q4 c4) ∷
   rw⁻ 50 (q4 c4) ∷
   rw 52 (q17 c4) ∷
   rw 52 (q36 c4) ∷
   rw⁻ 53 (q4 c4) ∷
   rw⁻ 56 (q4 c4) ∷
   rw⁻ 59 (q4 c4) ∷
   rw⁻ 60 (q38 c4) ∷
   rw⁻ 57 (q39 c4) ∷
   rw⁻ 54 (q38 c4) ∷
   rw⁻ 51 (q39 c4) ∷
   rw 54 (q4 c4) ∷
   rw 55 (q4 c4) ∷
   rw 56 (q4 c4) ∷
   rw⁻ 53 (q36 c4) ∷
   rw⁻ 53 (q17 c4) ∷
   rw⁻ 48 (q40 c4) ∷
   re 46 1 (CS03⁻ ∷ []) ∷
   rw⁻ 45 (q41 c4) ∷
   re 47 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 42 (q40 c4) ∷
   re 40 1 (CS03 ∷ []) ∷
   rw⁻ 39 (q42 c4) ∷
   re 41 1 (Sb2-0-3-1 ∷ []) ∷
   rw 42 (q4 c4) ∷
   rw 43 (q4 c4) ∷
   rw 44 (q4 c4) ∷
   rw 45 (q4 c4) ∷
   re 41 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 41 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 42 (q4 c4) ∷
   rw⁻ 45 (q4 c4) ∷
   rw⁻ 48 (q4 c4) ∷
   rw⁻ 51 (q4 c4) ∷
   rw 53 (q17 c4) ∷
   rw 53 (q19 c4) ∷
   rw 53 (q20 c4) ∷
   rw⁻ 54 (q4 c4) ∷
   rw⁻ 57 (q4 c4) ∷
   rw⁻ 60 (q4 c4) ∷
   rw⁻ 63 (q43 c4) ∷
   rw⁻ 62 (q44 c4) ∷
   rw⁻ 61 (q43 c4) ∷
   rw 63 (q45 c4) ∷
   rw⁻ 64 (q4 c4) ∷
   rw⁻ 67 (q4 c4) ∷
   rw⁻ 70 (q4 c4) ∷
   rw⁻ 73 (q4 c4) ∷
   rw⁻ 74 (q46 c4) ∷
   rw⁻ 71 (q47 c4) ∷
   rw⁻ 68 (q48 c4) ∷
   rw⁻ 65 (q47 c4) ∷
   rw⁻ 62 (q49 c4) ∷
   rw 65 (q4 c4) ∷
   rw 66 (q4 c4) ∷
   rw 67 (q4 c4) ∷
   rw 68 (q4 c4) ∷
   rw⁻ 64 (q45 c4) ∷
   rw⁻ 65 (q43 c4) ∷
   rw⁻ 64 (q44 c4) ∷
   rw⁻ 63 (q43 c4) ∷
   rw⁻ 58 (q50 c4) ∷
   rw⁻ 57 (q43 c4) ∷
   rw⁻ 56 (q44 c4) ∷
   rw⁻ 55 (q43 c4) ∷
   rw 57 (q45 c4) ∷
   rw⁻ 58 (q4 c4) ∷
   rw⁻ 61 (q4 c4) ∷
   rw⁻ 64 (q4 c4) ∷
   rw⁻ 67 (q4 c4) ∷
   rw⁻ 68 (q46 c4) ∷
   rw⁻ 65 (q47 c4) ∷
   rw⁻ 62 (q48 c4) ∷
   rw⁻ 59 (q47 c4) ∷
   rw⁻ 56 (q49 c4) ∷
   rw 59 (q4 c4) ∷
   rw 60 (q4 c4) ∷
   rw 61 (q4 c4) ∷
   rw 62 (q4 c4) ∷
   rw⁻ 58 (q45 c4) ∷
   rw⁻ 59 (q43 c4) ∷
   rw⁻ 58 (q44 c4) ∷
   rw⁻ 57 (q43 c4) ∷
   rw⁻ 52 (q50 c4) ∷
   rw 57 (q4 c4) ∷
   rw 58 (q4 c4) ∷
   rw 59 (q4 c4) ∷
   rw⁻ 56 (q20 c4) ∷
   rw 56 (q16 c4) ∷
   rw⁻ 56 (q17 c4) ∷
   rw⁻ 49 (q51 c4) ∷
   re 41 1 (CS03 ∷ []) ∷
   re 47 1 (CS03⁻ ∷ []) ∷
   rw⁻ 40 (q52 c4) ∷
   re 44 1 (Sb2-0-3-1 ∷ []) ∷ []) Eq.refl
