{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D043 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0248 ; wl0249 ; wl0250 ; wl0379 ; wl0397 ; wl0398 ; wl0399 ; wl0400 ; wl0433 ; wl0440 ; wl0441 ; wl0442 ; wl0448 ; wl0449 ; wl0456 ; wl0457 ; wl0458 ; wl0459 ; wl0461 ; wl0462 ; wl0463 ; wl0464 ; wl0465 ; wl0466 ; wl0469 ; wl0470 ; wl0471 ; wl0472 ; wl0473 ; wl0474 ; wl0475 ; wl0476 ; wl0477 ; wp0034 ; wp0059 ; wp0113 ; wp0139 ; wp0143 ; wp0159 ; wp0160 ; wp0161 ; wp0164 ; wp0165 ; wp0168 ; wp0169 ; wp0170 ; wp0172)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym34-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym12-at021021 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-F5-CS01-at1441 ; lem-SBsym-at1441 ; lem-beta-T-at0210213443 ; lem-beta-T-at022330 ; lem-sym12-at02203443 ; lem-sym34-at0220)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ []) (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx2-1304 ∷ []) (Bx2-1034 ∷ []) (lem-sym23-at022330 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1043 ∷ []) (lem-sym34-at0220 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx2-1043 ∷ []) (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ []) (wl0440 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym12-at021021 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1304 ∷ []) (lem-sym23-at0220 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CX13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS03 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CS03 ∷ []) (wp0164 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Toff314 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ Toff314 ∷ []) (wl0456 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS03⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CS03⁻ ∷ []) (wp0165 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Toff204 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ Toff204 ∷ []) (wp0169 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ123 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0465 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CS03 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CS03 ∷ []) (wl0458 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ []) (wl0457 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CS03⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CS03⁻ ∷ []) (wl0459 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Toff204 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ Toff204 ∷ []) (wp0170 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ123 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CCZ123 ∷ []) (wl0466 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CS14 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS14 ∷ []) (wp0160 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CS14 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS14 ∷ []) (wl0449 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS14 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS14 ∷ []) (wp0161 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CS14 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS14 ∷ []) (wl0448 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS14 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS14 ∷ []) (wp0159 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS14 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS14 ∷ []) (wp0172 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CS14 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CS14 ∷ []) (wl0469 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CS14 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CS14 ∷ []) (wl0470 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (S1⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1⁻ ∷ []) (wl0400 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ []) (wl0398 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (S1⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1⁻ ∷ []) (wl0399 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (S1⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ []) (wl0397 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (S1⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1⁻ ∷ []) (wp0139 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (S1⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ S1⁻ ∷ []) (wl0471 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (S1⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ S1⁻ ∷ []) (wl0472 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (S1⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ S1⁻ ∷ []) (wl0473 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS03⁻ ∷ CS03 ∷ []) [] (wl0249 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl0248 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CS03 ∷ CS03⁻ ∷ []) [] (wl0250 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) [] (wl0474 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp0034 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp0059 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CK10 ∷ CK10⁻ ∷ []) [] (wl0475 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CS14⁻ ∷ CS14 ∷ []) [] (wl0476 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (S1 ∷ S1⁻ ∷ []) [] (wl0477 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CS04 ∷ []) (CS04 ∷ []) (wp0113 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (X1 ∷ Sb2-0-14-3 ∷ X1 ∷ Sb2-0-14-3 ∷ []) (CS04 ∷ []) (lem-F5-CS01-at1441 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (Sb2-0-14-3 ∷ []) (Sb2-0-41-3 ∷ []) (lem-SBsym-at1441 c4)

-- F1 CS-K0 [rhs shape] part37: 426 steps
lem-F1-CS-K0-rhs-shape-part37 : Ws → ⟪ (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-rhs-shape-part37 c4 = derive (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 33 (q1 c4) ∷
   rw⁻ 30 (q2 c4) ∷
   rw 33 (q3 c4) ∷
   rw 34 (q3 c4) ∷
   rw 35 (q3 c4) ∷
   rw 36 (q3 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 27 (q5 c4) ∷
   rw 30 (q3 c4) ∷
   rw 31 (q3 c4) ∷
   rw 32 (q3 c4) ∷
   rw⁻ 29 (q6 c4) ∷
   rw 29 (q7 c4) ∷
   rw 29 (q8 c4) ∷
   rw 29 (q9 c4) ∷
   rw 29 (q10 c4) ∷
   rw⁻ 30 (q11 c4) ∷
   rw 29 (q12 c4) ∷
   rw⁻ 28 (q11 c4) ∷
   rw 30 (q13 c4) ∷
   rw 30 (q14 c4) ∷
   rw 30 (q15 c4) ∷
   rw 30 (q16 c4) ∷
   rw 30 (q6 c4) ∷
   rw⁻ 31 (q3 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw⁻ 37 (q3 c4) ∷
   rw 39 (q4 c4) ∷
   rw⁻ 40 (q3 c4) ∷
   rw⁻ 43 (q3 c4) ∷
   rw⁻ 46 (q3 c4) ∷
   rw⁻ 49 (q3 c4) ∷
   rw⁻ 50 (q17 c4) ∷
   rw⁻ 47 (q1 c4) ∷
   rw⁻ 44 (q18 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   rw⁻ 38 (q2 c4) ∷
   rw 41 (q3 c4) ∷
   rw 42 (q3 c4) ∷
   rw 43 (q3 c4) ∷
   rw 44 (q3 c4) ∷
   rw⁻ 40 (q4 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw 33 (q4 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw⁻ 37 (q3 c4) ∷
   rw⁻ 40 (q3 c4) ∷
   rw⁻ 43 (q3 c4) ∷
   rw⁻ 44 (q17 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   rw⁻ 38 (q18 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw 35 (q3 c4) ∷
   rw 36 (q3 c4) ∷
   rw 37 (q3 c4) ∷
   rw 38 (q3 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw 32 (q3 c4) ∷
   rw 33 (q3 c4) ∷
   rw 34 (q3 c4) ∷
   rw⁻ 31 (q6 c4) ∷
   rw 31 (q7 c4) ∷
   rw 31 (q8 c4) ∷
   rw 31 (q9 c4) ∷
   rw 31 (q10 c4) ∷
   rw 31 (q13 c4) ∷
   rw 31 (q19 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   rw⁻ 35 (q3 c4) ∷
   rw⁻ 38 (q3 c4) ∷
   rw⁻ 39 (q20 c4) ∷
   rw⁻ 36 (q21 c4) ∷
   rw⁻ 33 (q20 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw 33 (q3 c4) ∷
   rw 34 (q3 c4) ∷
   rw 35 (q3 c4) ∷
   rw⁻ 32 (q19 c4) ∷
   rw 32 (q10 c4) ∷
   rw⁻ 26 (q22 c4) ∷
   rw 29 (q3 c4) ∷
   rw 30 (q3 c4) ∷
   rw 31 (q3 c4) ∷
   rw 32 (q3 c4) ∷
   re 28 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 23 (q23 c4) ∷
   rw⁻ 23 (q24 c4) ∷
   re 19 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 19 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 19 1 (CS03 ∷ []) ∷
   rw⁻ 16 (q25 c4) ∷
   re 16 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 17 (q26 c4) ∷
   re 21 1 (CS03⁻ ∷ []) ∷
   rw⁻ 18 (q27 c4) ∷
   re 18 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 19 (q26 c4) ∷
   rw 23 (q24 c4) ∷
   rw 23 (q23 c4) ∷
   rw⁻ 20 (q28 c4) ∷
   rw⁻ 21 (q29 c4) ∷
   rw⁻ 22 (q28 c4) ∷
   rw⁻ 23 (q29 c4) ∷
   rw⁻ 20 (q23 c4) ∷
   rw⁻ 20 (q24 c4) ∷
   re 16 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 16 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 16 1 (CS03 ∷ []) ∷
   rw⁻ 13 (q30 c4) ∷
   re 13 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 14 (q31 c4) ∷
   re 18 1 (CS03⁻ ∷ []) ∷
   rw⁻ 15 (q32 c4) ∷
   re 15 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 16 (q31 c4) ∷
   rw 20 (q24 c4) ∷
   rw 20 (q23 c4) ∷
   rw⁻ 17 (q33 c4) ∷
   rw⁻ 18 (q34 c4) ∷
   rw⁻ 19 (q33 c4) ∷
   rw⁻ 20 (q34 c4) ∷
   rw⁻ 17 (q23 c4) ∷
   rw⁻ 17 (q24 c4) ∷
   re 13 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 33 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 34 (q3 c4) ∷
   rw⁻ 37 (q3 c4) ∷
   rw⁻ 40 (q3 c4) ∷
   rw⁻ 43 (q3 c4) ∷
   re 45 1 (CS03⁻ ∷ []) ∷
   rw⁻ 44 (q35 c4) ∷
   re 46 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 41 (q36 c4) ∷
   re 39 1 (CS03 ∷ []) ∷
   rw⁻ 38 (q37 c4) ∷
   re 40 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 35 (q36 c4) ∷
   rw 33 (q23 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw⁻ 37 (q3 c4) ∷
   rw⁻ 40 (q3 c4) ∷
   rw⁻ 41 (q38 c4) ∷
   rw⁻ 38 (q39 c4) ∷
   rw⁻ 35 (q38 c4) ∷
   rw⁻ 32 (q39 c4) ∷
   rw 35 (q3 c4) ∷
   rw 36 (q3 c4) ∷
   rw 37 (q3 c4) ∷
   rw⁻ 34 (q23 c4) ∷
   rw 35 (q3 c4) ∷
   rw 36 (q3 c4) ∷
   rw 37 (q3 c4) ∷
   rw 38 (q3 c4) ∷
   re 34 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 29 (q40 c4) ∷
   re 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 28 (q3 c4) ∷
   rw⁻ 31 (q3 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw⁻ 37 (q3 c4) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   rw⁻ 38 (q35 c4) ∷
   re 40 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 35 (q36 c4) ∷
   re 33 1 (CS03 ∷ []) ∷
   rw⁻ 32 (q37 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 29 (q36 c4) ∷
   rw 27 (q23 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw⁻ 31 (q3 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw⁻ 35 (q38 c4) ∷
   rw⁻ 32 (q39 c4) ∷
   rw⁻ 29 (q38 c4) ∷
   rw⁻ 26 (q39 c4) ∷
   rw 29 (q3 c4) ∷
   rw 30 (q3 c4) ∷
   rw 31 (q3 c4) ∷
   rw⁻ 28 (q23 c4) ∷
   rw 29 (q3 c4) ∷
   rw 30 (q3 c4) ∷
   rw 31 (q3 c4) ∷
   rw 32 (q3 c4) ∷
   re 28 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 23 (q40 c4) ∷
   re 21 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 22 (q3 c4) ∷
   rw⁻ 25 (q3 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw⁻ 31 (q3 c4) ∷
   re 33 1 (CS03⁻ ∷ []) ∷
   rw⁻ 32 (q35 c4) ∷
   re 34 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 29 (q36 c4) ∷
   re 27 1 (CS03 ∷ []) ∷
   rw⁻ 26 (q37 c4) ∷
   re 28 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q36 c4) ∷
   rw 21 (q23 c4) ∷
   rw⁻ 22 (q3 c4) ∷
   rw⁻ 25 (q3 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw⁻ 29 (q38 c4) ∷
   rw⁻ 26 (q39 c4) ∷
   rw⁻ 23 (q38 c4) ∷
   rw⁻ 20 (q39 c4) ∷
   rw 23 (q3 c4) ∷
   rw 24 (q3 c4) ∷
   rw 25 (q3 c4) ∷
   rw⁻ 22 (q23 c4) ∷
   rw 23 (q3 c4) ∷
   rw 24 (q3 c4) ∷
   rw 25 (q3 c4) ∷
   rw 26 (q3 c4) ∷
   re 22 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 17 (q41 c4) ∷
   rw⁻ 14 (q42 c4) ∷
   re 34 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 35 (q3 c4) ∷
   rw⁻ 38 (q3 c4) ∷
   rw⁻ 41 (q3 c4) ∷
   rw⁻ 44 (q3 c4) ∷
   re 46 1 (CS03⁻ ∷ []) ∷
   rw⁻ 45 (q43 c4) ∷
   re 47 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 42 (q44 c4) ∷
   re 40 1 (CS03 ∷ []) ∷
   rw⁻ 39 (q45 c4) ∷
   re 41 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 36 (q44 c4) ∷
   rw 34 (q23 c4) ∷
   rw⁻ 35 (q3 c4) ∷
   rw⁻ 38 (q3 c4) ∷
   rw⁻ 41 (q3 c4) ∷
   rw⁻ 42 (q46 c4) ∷
   rw⁻ 39 (q47 c4) ∷
   rw⁻ 36 (q46 c4) ∷
   rw⁻ 33 (q47 c4) ∷
   rw 36 (q3 c4) ∷
   rw 37 (q3 c4) ∷
   rw 38 (q3 c4) ∷
   rw⁻ 35 (q23 c4) ∷
   rw 36 (q3 c4) ∷
   rw 37 (q3 c4) ∷
   rw 38 (q3 c4) ∷
   rw 39 (q3 c4) ∷
   re 35 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 30 (q48 c4) ∷
   re 28 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 29 (q3 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   rw⁻ 35 (q3 c4) ∷
   rw⁻ 38 (q3 c4) ∷
   re 40 1 (CS03⁻ ∷ []) ∷
   rw⁻ 39 (q43 c4) ∷
   re 41 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 36 (q44 c4) ∷
   re 34 1 (CS03 ∷ []) ∷
   rw⁻ 33 (q45 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q44 c4) ∷
   rw 28 (q23 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   rw⁻ 35 (q3 c4) ∷
   rw⁻ 36 (q46 c4) ∷
   rw⁻ 33 (q47 c4) ∷
   rw⁻ 30 (q46 c4) ∷
   rw⁻ 27 (q47 c4) ∷
   rw 30 (q3 c4) ∷
   rw 31 (q3 c4) ∷
   rw 32 (q3 c4) ∷
   rw⁻ 29 (q23 c4) ∷
   rw 30 (q3 c4) ∷
   rw 31 (q3 c4) ∷
   rw 32 (q3 c4) ∷
   rw 33 (q3 c4) ∷
   re 29 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 24 (q48 c4) ∷
   re 22 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q3 c4) ∷
   rw⁻ 26 (q3 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   re 34 1 (CS03⁻ ∷ []) ∷
   rw⁻ 33 (q43 c4) ∷
   re 35 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q44 c4) ∷
   re 28 1 (CS03 ∷ []) ∷
   rw⁻ 27 (q45 c4) ∷
   re 29 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q44 c4) ∷
   rw 22 (q23 c4) ∷
   rw⁻ 23 (q3 c4) ∷
   rw⁻ 26 (q3 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw⁻ 30 (q46 c4) ∷
   rw⁻ 27 (q47 c4) ∷
   rw⁻ 24 (q46 c4) ∷
   rw⁻ 21 (q47 c4) ∷
   rw 24 (q3 c4) ∷
   rw 25 (q3 c4) ∷
   rw 26 (q3 c4) ∷
   rw⁻ 23 (q23 c4) ∷
   rw 24 (q3 c4) ∷
   rw 25 (q3 c4) ∷
   rw 26 (q3 c4) ∷
   rw 27 (q3 c4) ∷
   re 23 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 18 (q49 c4) ∷
   rw⁻ 15 (q50 c4) ∷
   rw 36 (q3 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 35 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   re 40 1 (CS03 ∷ []) ∷
   rw 39 (q51 c4) ∷
   rw 38 (q52 c4) ∷
   re 37 1 (CS03 ∷ []) ∷
   re 38 1 (CS03⁻ ∷ []) ∷
   rw 37 (q53 c4) ∷
   rw 36 (q52 c4) ∷
   re 36 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   re 35 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 40 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 42 1 (CZ03 ∷ []) ∷
   re 45 1 (CZ03 ∷ []) ∷
   re 46 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 46 1 (CZ03 ∷ []) ∷
   re 49 1 (CZ03 ∷ []) ∷
   rw 40 (q54 c4) ∷
   rw 39 (q55 c4) ∷
   rw 38 (q56 c4) ∷
   re 37 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 39 1 (CZ03 ∷ []) ∷
   re 42 1 (CZ03 ∷ []) ∷
   re 43 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 43 1 (CZ03 ∷ []) ∷
   re 46 1 (CZ03 ∷ []) ∷
   rw 37 (q54 c4) ∷
   rw 36 (q56 c4) ∷
   rw 35 (q55 c4) ∷
   rw 34 (q3 c4) ∷
   rw 33 (q3 c4) ∷
   rw 32 (q57 c4) ∷
   rw 31 (q3 c4) ∷
   rw 30 (q3 c4) ∷
   re 30 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 29 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 33 1 (CS03⁻ ∷ []) ∷
   re 34 1 (CS03 ∷ []) ∷
   rw 33 (q51 c4) ∷
   rw 32 (q52 c4) ∷
   re 31 1 (CS03 ∷ []) ∷
   re 32 1 (CS03⁻ ∷ []) ∷
   rw 31 (q53 c4) ∷
   rw 30 (q52 c4) ∷
   re 30 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   re 29 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 34 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 36 1 (CZ03 ∷ []) ∷
   re 39 1 (CZ03 ∷ []) ∷
   re 40 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 40 1 (CZ03 ∷ []) ∷
   re 43 1 (CZ03 ∷ []) ∷
   rw 34 (q54 c4) ∷
   rw 33 (q55 c4) ∷
   rw 32 (q56 c4) ∷
   re 31 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 33 1 (CZ03 ∷ []) ∷
   re 36 1 (CZ03 ∷ []) ∷
   re 37 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 37 1 (CZ03 ∷ []) ∷
   re 40 1 (CZ03 ∷ []) ∷
   rw 31 (q54 c4) ∷
   rw 30 (q56 c4) ∷
   rw 29 (q55 c4) ∷
   rw 28 (q3 c4) ∷
   rw 27 (q3 c4) ∷
   rw 26 (q57 c4) ∷
   rw 25 (q3 c4) ∷
   rw 24 (q3 c4) ∷
   re 24 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 27 1 (CS03⁻ ∷ []) ∷
   re 28 1 (CS03 ∷ []) ∷
   rw 27 (q51 c4) ∷
   rw 26 (q52 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   re 26 1 (CS03⁻ ∷ []) ∷
   rw 25 (q53 c4) ∷
   rw 24 (q52 c4) ∷
   re 24 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   re 23 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 28 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 30 1 (CZ03 ∷ []) ∷
   re 33 1 (CZ03 ∷ []) ∷
   re 34 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 34 1 (CZ03 ∷ []) ∷
   re 37 1 (CZ03 ∷ []) ∷
   rw 28 (q54 c4) ∷
   rw 27 (q55 c4) ∷
   rw 26 (q56 c4) ∷
   re 25 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 27 1 (CZ03 ∷ []) ∷
   re 30 1 (CZ03 ∷ []) ∷
   re 31 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 31 1 (CZ03 ∷ []) ∷
   re 34 1 (CZ03 ∷ []) ∷
   rw 25 (q54 c4) ∷
   rw 24 (q56 c4) ∷
   rw 23 (q55 c4) ∷
   rw 22 (q3 c4) ∷
   rw 21 (q3 c4) ∷
   rw 20 (q58 c4) ∷
   rw 19 (q3 c4) ∷
   rw 18 (q3 c4) ∷
   rw 17 (q59 c4) ∷
   rw 16 (q3 c4) ∷
   rw 0 (q60 c4) ∷
   rw⁻ 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 3 (q62 c4) ∷ []) Eq.refl
