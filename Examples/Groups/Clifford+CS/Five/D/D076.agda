{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D076 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0393 ; wl0424 ; wl0425 ; wl0426 ; wl0427 ; wl0428 ; wl0429 ; wl0430 ; wl0431 ; wl0433 ; wl0434 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0444 ; wl0445 ; wl0456 ; wl0457 ; wl0458 ; wl0459 ; wl0461 ; wl0462 ; wl0463 ; wl0464 ; wl0465 ; wl0466 ; wp0143 ; wp0146 ; wp0147 ; wp0148 ; wp0149 ; wp0150 ; wp0155 ; wp0164 ; wp0165 ; wp0168 ; wp0169 ; wp0170)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym34-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym12-at021021 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443 ; lem-beta-T-at022330 ; lem-sym12-at02203443 ; lem-sym34-at0220)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-BOX⟨0·1234⟩-∣-CS40-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at0210243143)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym12-at021021 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1304 ∷ []) (lem-sym23-at0220 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CX13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx2-1304 ∷ []) (Bx2-1034 ∷ []) (lem-sym23-at022330 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1043 ∷ []) (lem-sym34-at0220 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ []) (wp0155 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Sb2-0-41-3 ∷ Toff204 ∷ []) (Toff204 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at0210243143 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ123 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0444 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) (wl0443 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ123 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ []) (wl0445 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ []) (wl0434 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS40-at0210243143 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ []) (wl0440 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CS03 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CS03 ∷ []) (wp0164 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Toff314 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ Toff314 ∷ []) (wl0456 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CS03⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CS03⁻ ∷ []) (wp0165 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Toff204 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ Toff204 ∷ []) (wp0169 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ123 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0465 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS03 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CS03 ∷ []) (wl0458 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ []) (wl0457 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS03⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CS03⁻ ∷ []) (wl0459 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Toff204 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ Toff204 ∷ []) (wp0170 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ123 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CCZ123 ∷ []) (wl0466 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CK10⁻ ∷ []) (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ []) (wl0424 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0426 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ []) (wp0147 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01⁻ ∷ []) (wl0427 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CS01⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ []) (wl0425 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01⁻ ∷ []) (wp0146 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0150 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0149 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (K0⁻ ∷ X1 ∷ []) (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X))
  q51 : Ws → Eqn
  q51 c4 = eqn (K0⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (CCZ ↑))
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CS01⁻ ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ []) (wp0148 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CS01⁻ ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01⁻ ∷ []) (wl0428 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0429 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01⁻ ∷ []) (wl0430 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wl0431 (lit c4))

-- F1 CS-K0 part31: 348 steps
lem-F1-CS-K0-part31 : Ws → ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Bx2-0143 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ
lem-F1-CS-K0-part31 c4 = derive (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Bx2-0143 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  (rw 26 (q1 c4) ∷
   rw 26 (q2 c4) ∷
   rw 26 (q3 c4) ∷
   rw 26 (q4 c4) ∷
   rw⁻ 27 (q5 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw⁻ 33 (q5 c4) ∷
   rw 35 (q6 c4) ∷
   rw⁻ 36 (q5 c4) ∷
   rw⁻ 39 (q5 c4) ∷
   rw⁻ 42 (q5 c4) ∷
   rw⁻ 45 (q5 c4) ∷
   rw⁻ 46 (q7 c4) ∷
   rw⁻ 43 (q8 c4) ∷
   rw⁻ 40 (q9 c4) ∷
   rw⁻ 37 (q8 c4) ∷
   rw⁻ 34 (q10 c4) ∷
   rw 37 (q5 c4) ∷
   rw 38 (q5 c4) ∷
   rw 39 (q5 c4) ∷
   rw 40 (q5 c4) ∷
   rw⁻ 36 (q6 c4) ∷
   rw⁻ 31 (q11 c4) ∷
   rw 29 (q6 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw⁻ 33 (q5 c4) ∷
   rw⁻ 36 (q5 c4) ∷
   rw⁻ 39 (q5 c4) ∷
   rw⁻ 40 (q7 c4) ∷
   rw⁻ 37 (q8 c4) ∷
   rw⁻ 34 (q9 c4) ∷
   rw⁻ 31 (q8 c4) ∷
   rw⁻ 28 (q10 c4) ∷
   rw 31 (q5 c4) ∷
   rw 32 (q5 c4) ∷
   rw 33 (q5 c4) ∷
   rw 34 (q5 c4) ∷
   rw⁻ 30 (q6 c4) ∷
   rw⁻ 25 (q11 c4) ∷
   rw 28 (q5 c4) ∷
   rw 29 (q5 c4) ∷
   rw 30 (q5 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw 27 (q12 c4) ∷
   rw 27 (q13 c4) ∷
   rw 27 (q14 c4) ∷
   rw 27 (q15 c4) ∷
   rw 27 (q16 c4) ∷
   rw 27 (q17 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 34 (q5 c4) ∷
   rw⁻ 35 (q18 c4) ∷
   rw⁻ 32 (q19 c4) ∷
   rw⁻ 29 (q18 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw 29 (q5 c4) ∷
   rw 30 (q5 c4) ∷
   rw 31 (q5 c4) ∷
   rw⁻ 28 (q17 c4) ∷
   rw 28 (q15 c4) ∷
   rw⁻ 22 (q20 c4) ∷
   rw 25 (q5 c4) ∷
   rw 26 (q5 c4) ∷
   rw 27 (q5 c4) ∷
   rw 28 (q5 c4) ∷
   re 24 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 25 (q21 c4) ∷
   rw 24 (q22 c4) ∷
   rw⁻ 23 (q21 c4) ∷
   re 25 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 26 (q5 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   re 37 1 (CS03⁻ ∷ []) ∷
   rw⁻ 36 (q23 c4) ∷
   re 38 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 33 (q24 c4) ∷
   re 31 1 (CS03 ∷ []) ∷
   rw⁻ 30 (q25 c4) ∷
   re 32 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 27 (q24 c4) ∷
   rw 27 (q20 c4) ∷
   rw⁻ 26 (q26 c4) ∷
   rw 25 (q27 c4) ∷
   rw⁻ 24 (q26 c4) ∷
   rw 26 (q16 c4) ∷
   rw 26 (q1 c4) ∷
   rw 26 (q2 c4) ∷
   rw 26 (q3 c4) ∷
   rw 26 (q4 c4) ∷
   rw⁻ 27 (q5 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw⁻ 33 (q5 c4) ∷
   rw 35 (q6 c4) ∷
   rw⁻ 36 (q5 c4) ∷
   rw⁻ 39 (q5 c4) ∷
   rw⁻ 42 (q5 c4) ∷
   rw⁻ 45 (q5 c4) ∷
   rw⁻ 46 (q7 c4) ∷
   rw⁻ 43 (q8 c4) ∷
   rw⁻ 40 (q9 c4) ∷
   rw⁻ 37 (q8 c4) ∷
   rw⁻ 34 (q10 c4) ∷
   rw 37 (q5 c4) ∷
   rw 38 (q5 c4) ∷
   rw 39 (q5 c4) ∷
   rw 40 (q5 c4) ∷
   rw⁻ 36 (q6 c4) ∷
   rw⁻ 31 (q11 c4) ∷
   rw 29 (q6 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw⁻ 33 (q5 c4) ∷
   rw⁻ 36 (q5 c4) ∷
   rw⁻ 39 (q5 c4) ∷
   rw⁻ 40 (q7 c4) ∷
   rw⁻ 37 (q8 c4) ∷
   rw⁻ 34 (q9 c4) ∷
   rw⁻ 31 (q8 c4) ∷
   rw⁻ 28 (q10 c4) ∷
   rw 31 (q5 c4) ∷
   rw 32 (q5 c4) ∷
   rw 33 (q5 c4) ∷
   rw 34 (q5 c4) ∷
   rw⁻ 30 (q6 c4) ∷
   rw⁻ 25 (q11 c4) ∷
   rw 28 (q5 c4) ∷
   rw 29 (q5 c4) ∷
   rw 30 (q5 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw 27 (q12 c4) ∷
   rw 27 (q13 c4) ∷
   rw 27 (q14 c4) ∷
   rw 27 (q15 c4) ∷
   rw⁻ 28 (q28 c4) ∷
   rw 27 (q29 c4) ∷
   rw⁻ 26 (q28 c4) ∷
   rw 28 (q16 c4) ∷
   rw 28 (q1 c4) ∷
   rw 28 (q2 c4) ∷
   rw 28 (q3 c4) ∷
   rw 28 (q4 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw 37 (q6 c4) ∷
   rw⁻ 38 (q5 c4) ∷
   rw⁻ 41 (q5 c4) ∷
   rw⁻ 44 (q5 c4) ∷
   rw⁻ 47 (q5 c4) ∷
   rw⁻ 48 (q7 c4) ∷
   rw⁻ 45 (q8 c4) ∷
   rw⁻ 42 (q9 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw⁻ 36 (q10 c4) ∷
   rw 39 (q5 c4) ∷
   rw 40 (q5 c4) ∷
   rw 41 (q5 c4) ∷
   rw 42 (q5 c4) ∷
   rw⁻ 38 (q6 c4) ∷
   rw⁻ 33 (q11 c4) ∷
   rw 31 (q6 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw⁻ 38 (q5 c4) ∷
   rw⁻ 41 (q5 c4) ∷
   rw⁻ 42 (q7 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw⁻ 36 (q9 c4) ∷
   rw⁻ 33 (q8 c4) ∷
   rw⁻ 30 (q10 c4) ∷
   rw 33 (q5 c4) ∷
   rw 34 (q5 c4) ∷
   rw 35 (q5 c4) ∷
   rw 36 (q5 c4) ∷
   rw⁻ 32 (q6 c4) ∷
   rw⁻ 27 (q11 c4) ∷
   rw 30 (q5 c4) ∷
   rw 31 (q5 c4) ∷
   rw 32 (q5 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw 29 (q12 c4) ∷
   rw 29 (q13 c4) ∷
   rw 29 (q14 c4) ∷
   rw 29 (q15 c4) ∷
   rw 29 (q16 c4) ∷
   rw 29 (q17 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw⁻ 33 (q5 c4) ∷
   rw⁻ 36 (q5 c4) ∷
   rw⁻ 37 (q18 c4) ∷
   rw⁻ 34 (q19 c4) ∷
   rw⁻ 31 (q18 c4) ∷
   rw⁻ 28 (q19 c4) ∷
   rw 31 (q5 c4) ∷
   rw 32 (q5 c4) ∷
   rw 33 (q5 c4) ∷
   rw⁻ 30 (q17 c4) ∷
   rw 30 (q15 c4) ∷
   rw⁻ 24 (q20 c4) ∷
   rw 27 (q5 c4) ∷
   rw 28 (q5 c4) ∷
   rw 29 (q5 c4) ∷
   rw 30 (q5 c4) ∷
   re 26 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 21 (q30 c4) ∷
   rw⁻ 21 (q31 c4) ∷
   re 17 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 17 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 17 1 (CS03 ∷ []) ∷
   rw⁻ 14 (q32 c4) ∷
   re 14 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q33 c4) ∷
   re 19 1 (CS03⁻ ∷ []) ∷
   rw⁻ 16 (q34 c4) ∷
   re 16 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 17 (q33 c4) ∷
   rw 21 (q31 c4) ∷
   rw 21 (q30 c4) ∷
   rw⁻ 18 (q35 c4) ∷
   rw⁻ 19 (q36 c4) ∷
   rw⁻ 20 (q35 c4) ∷
   rw⁻ 21 (q36 c4) ∷
   rw⁻ 18 (q30 c4) ∷
   rw⁻ 18 (q31 c4) ∷
   re 14 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 14 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 14 1 (CS03 ∷ []) ∷
   rw⁻ 11 (q37 c4) ∷
   re 11 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 12 (q38 c4) ∷
   re 16 1 (CS03⁻ ∷ []) ∷
   rw⁻ 13 (q39 c4) ∷
   re 13 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 14 (q38 c4) ∷
   rw 18 (q31 c4) ∷
   rw 18 (q30 c4) ∷
   rw⁻ 15 (q40 c4) ∷
   rw⁻ 16 (q41 c4) ∷
   rw⁻ 17 (q40 c4) ∷
   rw⁻ 18 (q41 c4) ∷
   rw⁻ 15 (q30 c4) ∷
   rw⁻ 15 (q31 c4) ∷
   re 11 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 33 (q42 c4) ∷
   re 31 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw⁻ 38 (q5 c4) ∷
   rw⁻ 41 (q5 c4) ∷
   re 43 1 (CS03⁻ ∷ []) ∷
   rw⁻ 42 (q43 c4) ∷
   re 44 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 39 (q44 c4) ∷
   re 37 1 (CS03 ∷ []) ∷
   rw⁻ 36 (q45 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 33 (q44 c4) ∷
   rw 31 (q30 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw⁻ 38 (q5 c4) ∷
   rw⁻ 39 (q46 c4) ∷
   rw⁻ 36 (q47 c4) ∷
   rw⁻ 33 (q46 c4) ∷
   rw⁻ 30 (q47 c4) ∷
   rw 33 (q5 c4) ∷
   rw 34 (q5 c4) ∷
   rw 35 (q5 c4) ∷
   rw⁻ 32 (q30 c4) ∷
   rw 33 (q5 c4) ∷
   rw 34 (q5 c4) ∷
   rw 35 (q5 c4) ∷
   rw 36 (q5 c4) ∷
   re 32 5 (Sb2-0-41-3 ∷ []) ∷
   re 32 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 33 (q5 c4) ∷
   rw⁻ 36 (q5 c4) ∷
   rw⁻ 39 (q5 c4) ∷
   rw⁻ 42 (q5 c4) ∷
   re 38 1 (CS03 ∷ []) ∷
   re 44 1 (CS03⁻ ∷ []) ∷
   rw⁻ 37 (q48 c4) ∷
   re 41 1 (Sb2-0-3-1 ∷ []) ∷
   re 47 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 34 (q49 c4) ∷
   rw 32 (q16 c4) ∷
   rw 32 (q17 c4) ∷
   rw⁻ 33 (q5 c4) ∷
   rw⁻ 36 (q5 c4) ∷
   rw⁻ 39 (q5 c4) ∷
   rw⁻ 42 (q50 c4) ∷
   rw⁻ 41 (q51 c4) ∷
   rw⁻ 40 (q50 c4) ∷
   rw 42 (q52 c4) ∷
   rw⁻ 43 (q5 c4) ∷
   rw⁻ 46 (q5 c4) ∷
   rw⁻ 49 (q5 c4) ∷
   rw⁻ 52 (q5 c4) ∷
   rw⁻ 53 (q53 c4) ∷
   rw⁻ 50 (q54 c4) ∷
   rw⁻ 47 (q55 c4) ∷
   rw⁻ 44 (q54 c4) ∷
   rw⁻ 41 (q56 c4) ∷
   rw 44 (q5 c4) ∷
   rw 45 (q5 c4) ∷
   rw 46 (q5 c4) ∷
   rw 47 (q5 c4) ∷
   rw⁻ 43 (q52 c4) ∷
   rw⁻ 44 (q50 c4) ∷
   rw⁻ 43 (q51 c4) ∷
   rw⁻ 42 (q50 c4) ∷
   rw⁻ 37 (q57 c4) ∷
   rw⁻ 36 (q50 c4) ∷
   rw⁻ 35 (q51 c4) ∷
   rw⁻ 34 (q50 c4) ∷
   rw 36 (q52 c4) ∷
   rw⁻ 37 (q5 c4) ∷
   rw⁻ 40 (q5 c4) ∷
   rw⁻ 43 (q5 c4) ∷
   rw⁻ 46 (q5 c4) ∷
   rw⁻ 47 (q53 c4) ∷
   rw⁻ 44 (q54 c4) ∷
   rw⁻ 41 (q55 c4) ∷
   rw⁻ 38 (q54 c4) ∷
   rw⁻ 35 (q56 c4) ∷
   rw 38 (q5 c4) ∷
   rw 39 (q5 c4) ∷
   rw 40 (q5 c4) ∷
   rw 41 (q5 c4) ∷
   rw⁻ 37 (q52 c4) ∷
   rw⁻ 38 (q50 c4) ∷
   rw⁻ 37 (q51 c4) ∷
   rw⁻ 36 (q50 c4) ∷
   rw⁻ 31 (q57 c4) ∷
   rw 36 (q5 c4) ∷
   rw 37 (q5 c4) ∷
   rw 38 (q5 c4) ∷
   rw⁻ 35 (q17 c4) ∷
   rw 35 (q15 c4) ∷
   rw 36 (q5 c4) ∷
   rw 37 (q5 c4) ∷
   rw 38 (q5 c4) ∷
   rw 39 (q5 c4) ∷
   re 35 5 (Sb2-0-41-3 ∷ []) ∷
   re 35 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 36 (q5 c4) ∷ []) Eq.refl
