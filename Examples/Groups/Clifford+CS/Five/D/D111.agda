{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D111 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0509 ; wl0514 ; wl0528 ; wl0529 ; wl0530 ; wl0531 ; wl0548 ; wl0550 ; wl0551 ; wl0554 ; wl0558 ; wl0571 ; wl0572 ; wl0579 ; wl0580 ; wl0581 ; wl0582 ; wl0583 ; wl0584 ; wl0585 ; wp0200 ; wp0201 ; wp0202 ; wp0203 ; wp0204 ; wp0225 ; wp0245 ; wp0246 ; wp0247 ; wp0248)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-beta-T-at0310243142 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-auto-CCZ012-∣-CCZ314-at0112243043 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 ; lem-beta-T-at03103441 ; lem-sym23-at0310243241 ; lem-sym23-at03103441 ; lem-sym34-at0310243142 ; lem-sym34-at0310243241)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CCZ134-CX20)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CCZ134 ∷ K2 ∷ []) (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (X0 ∷ K2 ∷ []) (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑))
  q3 : Ws → Eqn
  q3 c4 = eqn (CX20 ∷ X0 ∷ []) (X0 ∷ CX20 ∷ []) (wl0583 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ134 ∷ CX20 ∷ []) (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (X0 ∷ K2⁻ ∷ []) (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ134 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ X0 ∷ CS03⁻ ∷ []) (wp0247 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X0 ∷ CS23 ∷ []) (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑))
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ134 ∷ CS23 ∷ []) (CS23 ∷ CCZ134 ∷ []) (wl0558 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (wl0584 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (K2⁻ ∷ K2 ∷ []) [] (wl0550 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl0581 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ124 ∷ X0 ∷ []) (X0 ∷ CCZ124 ∷ []) (wp0225 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Sb2-0-41-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0210243143 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Toff203 ∷ X0 ∷ CS02⁻ ∷ X0 ∷ []) (X0 ∷ CS02⁻ ∷ X0 ∷ Toff203 ∷ []) (wl0571 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (K2 ∷ K2⁻ ∷ []) [] (wl0579 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ124 ∷ []) (K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ []) (wp0245 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ023 ∷ []) (K2⁻ ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ []) (wl0580 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at0112243043 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Toff203 ∷ X0 ∷ CS02 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ X0 ∷ Toff203 ∷ []) (wl0572 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ []) (wl0582 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff304 ∷ X0 ∷ []) (X0 ∷ Toff304 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ []) (wp0246 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CS03 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS03 ∷ []) (wl0585 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Toff314 ∷ CS03⁻ ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (wp0248 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) (wl0514 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (X0 ∷ CCZ234 ∷ []) (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑))
  q42 : Ws → Eqn
  q42 c4 = eqn (CK01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ))
  q43 : Ws → Eqn
  q43 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03 ∷ []) (wl0531 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0204 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ []) (wp0202 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (Sb2-0-41-3 ∷ Toff314 ∷ []) (Toff314 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CS03⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ []) (wl0529 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) (wp0201 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)

-- F1 CS-K1 [rhs shape] part20: 349 steps
lem-F1-CS-K1-rhs-shape-part20 : Ws → ⟪ (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ K2 ∷ X0 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-rhs-shape-part20 c4 = derive (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ K2 ∷ X0 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw 32 (q1 c4) ∷
   rw 31 (q2 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw 33 (q4 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   rw 35 (q5 c4) ∷
   rw 34 (q6 c4) ∷
   rw 33 (q5 c4) ∷
   rw 36 (q2 c4) ∷
   rw 35 (q1 c4) ∷
   rw 34 (q2 c4) ∷
   rw⁻ 35 (q7 c4) ∷
   rw 38 (q5 c4) ∷
   rw 37 (q6 c4) ∷
   rw 36 (q5 c4) ∷
   rw 39 (q2 c4) ∷
   rw 38 (q1 c4) ∷
   rw 37 (q2 c4) ∷
   rw⁻ 40 (q3 c4) ∷
   rw 39 (q4 c4) ∷
   rw⁻ 38 (q3 c4) ∷
   rw 41 (q5 c4) ∷
   rw 40 (q6 c4) ∷
   rw 39 (q5 c4) ∷
   rw 42 (q2 c4) ∷
   rw 41 (q1 c4) ∷
   rw 40 (q2 c4) ∷
   rw 43 (q8 c4) ∷
   rw 42 (q9 c4) ∷
   rw 41 (q8 c4) ∷
   rw 44 (q5 c4) ∷
   rw 43 (q6 c4) ∷
   rw 42 (q5 c4) ∷
   rw⁻ 28 (q10 c4) ∷
   rw 42 (q11 c4) ∷
   rw 43 (q11 c4) ∷
   rw 44 (q11 c4) ∷
   rw⁻ 41 (q12 c4) ∷
   rw 41 (q13 c4) ∷
   rw 41 (q14 c4) ∷
   rw 27 (q15 c4) ∷
   rw 28 (q15 c4) ∷
   rw 29 (q15 c4) ∷
   rw 30 (q15 c4) ∷
   rw⁻ 26 (q16 c4) ∷
   rw 25 (q17 c4) ∷
   rw 28 (q11 c4) ∷
   rw 29 (q11 c4) ∷
   rw 30 (q11 c4) ∷
   rw 31 (q11 c4) ∷
   re 27 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 27 (q18 c4) ∷
   rw⁻ 28 (q19 c4) ∷
   rw 27 (q20 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw 28 (q18 c4) ∷
   re 28 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 29 (q11 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 35 (q11 c4) ∷
   rw⁻ 38 (q11 c4) ∷
   re 40 1 (CS02⁻ ∷ []) ∷
   rw⁻ 39 (q21 c4) ∷
   re 41 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 39 (q17 c4) ∷
   rw⁻ 36 (q22 c4) ∷
   rw⁻ 41 (q22 c4) ∷
   rw⁻ 46 (q22 c4) ∷
   rw⁻ 37 (q23 c4) ∷
   rw⁻ 38 (q24 c4) ∷
   rw 37 (q25 c4) ∷
   rw 37 (q24 c4) ∷
   rw 42 (q23 c4) ∷
   rw 36 (q22 c4) ∷
   rw 39 (q22 c4) ∷
   rw 42 (q22 c4) ∷
   rw 36 (q17 c4) ∷
   re 34 1 (CS02 ∷ []) ∷
   rw⁻ 33 (q26 c4) ∷
   re 35 1 (Sb3-0-2-1 ∷ []) ∷
   rw⁻ 33 (q17 c4) ∷
   rw⁻ 30 (q22 c4) ∷
   rw⁻ 35 (q22 c4) ∷
   rw⁻ 40 (q22 c4) ∷
   rw⁻ 31 (q23 c4) ∷
   rw⁻ 32 (q24 c4) ∷
   rw 31 (q25 c4) ∷
   rw 31 (q24 c4) ∷
   rw 36 (q23 c4) ∷
   rw 30 (q22 c4) ∷
   rw 33 (q22 c4) ∷
   rw 36 (q22 c4) ∷
   rw 30 (q17 c4) ∷
   rw⁻ 30 (q17 c4) ∷
   rw 31 (q16 c4) ∷
   rw⁻ 32 (q15 c4) ∷
   rw⁻ 35 (q15 c4) ∷
   rw⁻ 38 (q15 c4) ∷
   rw⁻ 41 (q15 c4) ∷
   rw 28 (q27 c4) ∷
   rw⁻ 29 (q11 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 35 (q11 c4) ∷
   rw⁻ 36 (q28 c4) ∷
   rw⁻ 33 (q29 c4) ∷
   rw⁻ 30 (q28 c4) ∷
   rw⁻ 27 (q29 c4) ∷
   rw 32 (q11 c4) ∷
   rw 33 (q11 c4) ∷
   rw 34 (q11 c4) ∷
   rw⁻ 31 (q27 c4) ∷
   rw 31 (q30 c4) ∷
   rw 31 (q31 c4) ∷
   rw 31 (q12 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 35 (q11 c4) ∷
   rw⁻ 38 (q11 c4) ∷
   rw 41 (q2 c4) ∷
   rw 40 (q1 c4) ∷
   rw 39 (q2 c4) ∷
   rw⁻ 42 (q3 c4) ∷
   rw 41 (q4 c4) ∷
   rw⁻ 40 (q3 c4) ∷
   rw 43 (q5 c4) ∷
   rw 42 (q6 c4) ∷
   rw 41 (q5 c4) ∷
   rw 44 (q2 c4) ∷
   rw 43 (q1 c4) ∷
   rw 42 (q2 c4) ∷
   rw⁻ 43 (q7 c4) ∷
   rw 46 (q5 c4) ∷
   rw 45 (q6 c4) ∷
   rw 44 (q5 c4) ∷
   rw 47 (q2 c4) ∷
   rw 46 (q1 c4) ∷
   rw 45 (q2 c4) ∷
   rw⁻ 48 (q3 c4) ∷
   rw 47 (q4 c4) ∷
   rw⁻ 46 (q3 c4) ∷
   rw 49 (q5 c4) ∷
   rw 48 (q6 c4) ∷
   rw 47 (q5 c4) ∷
   rw 50 (q2 c4) ∷
   rw 49 (q1 c4) ∷
   rw 48 (q2 c4) ∷
   rw 51 (q8 c4) ∷
   rw 50 (q9 c4) ∷
   rw 49 (q8 c4) ∷
   rw 52 (q5 c4) ∷
   rw 51 (q6 c4) ∷
   rw 50 (q5 c4) ∷
   rw⁻ 36 (q10 c4) ∷
   rw 35 (q2 c4) ∷
   rw 34 (q1 c4) ∷
   rw 33 (q2 c4) ∷
   rw⁻ 36 (q3 c4) ∷
   rw 35 (q4 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw 37 (q5 c4) ∷
   rw 36 (q6 c4) ∷
   rw 35 (q5 c4) ∷
   rw 38 (q2 c4) ∷
   rw 37 (q1 c4) ∷
   rw 36 (q2 c4) ∷
   rw⁻ 37 (q7 c4) ∷
   rw 40 (q5 c4) ∷
   rw 39 (q6 c4) ∷
   rw 38 (q5 c4) ∷
   rw 41 (q2 c4) ∷
   rw 40 (q1 c4) ∷
   rw 39 (q2 c4) ∷
   rw⁻ 42 (q3 c4) ∷
   rw 41 (q4 c4) ∷
   rw⁻ 40 (q3 c4) ∷
   rw 43 (q5 c4) ∷
   rw 42 (q6 c4) ∷
   rw 41 (q5 c4) ∷
   rw 44 (q2 c4) ∷
   rw 43 (q1 c4) ∷
   rw 42 (q2 c4) ∷
   rw 45 (q8 c4) ∷
   rw 44 (q9 c4) ∷
   rw 43 (q8 c4) ∷
   rw 46 (q5 c4) ∷
   rw 45 (q6 c4) ∷
   rw 44 (q5 c4) ∷
   rw⁻ 30 (q10 c4) ∷
   rw 44 (q11 c4) ∷
   rw 45 (q11 c4) ∷
   rw 46 (q11 c4) ∷
   rw⁻ 43 (q12 c4) ∷
   rw 43 (q13 c4) ∷
   rw 43 (q14 c4) ∷
   rw 29 (q15 c4) ∷
   rw 30 (q15 c4) ∷
   rw 31 (q15 c4) ∷
   rw 32 (q15 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   rw 27 (q17 c4) ∷
   rw 30 (q11 c4) ∷
   rw 31 (q11 c4) ∷
   rw 32 (q11 c4) ∷
   rw 33 (q11 c4) ∷
   re 29 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 29 (q18 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw 29 (q20 c4) ∷
   rw⁻ 28 (q19 c4) ∷
   rw⁻ 25 (q32 c4) ∷
   rw 25 (q33 c4) ∷
   rw 25 (q34 c4) ∷
   rw⁻ 25 (q35 c4) ∷
   re 21 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 21 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 21 1 (CS03 ∷ []) ∷
   rw⁻ 18 (q36 c4) ∷
   re 18 1 (Sb2-0-3-1 ∷ []) ∷
   re 23 1 (CS03⁻ ∷ []) ∷
   rw⁻ 19 (q37 c4) ∷
   re 20 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 25 (q35 c4) ∷
   rw 25 (q38 c4) ∷
   rw 25 (q39 c4) ∷
   rw⁻ 22 (q40 c4) ∷
   rw 25 (q41 c4) ∷
   rw 24 (q42 c4) ∷
   rw 23 (q41 c4) ∷
   rw⁻ 24 (q40 c4) ∷
   rw 27 (q41 c4) ∷
   rw 26 (q42 c4) ∷
   rw 25 (q41 c4) ∷
   rw⁻ 22 (q39 c4) ∷
   rw 22 (q43 c4) ∷
   rw⁻ 22 (q35 c4) ∷
   re 18 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 18 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 18 1 (CS03 ∷ []) ∷
   re 16 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw⁻ 23 (q11 c4) ∷
   rw⁻ 26 (q11 c4) ∷
   re 28 1 (CS03⁻ ∷ []) ∷
   rw⁻ 27 (q44 c4) ∷
   re 29 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 22 1 (CS03 ∷ []) ∷
   rw⁻ 18 (q45 c4) ∷
   re 23 1 (Sb2-0-3-1 ∷ []) ∷
   rw 16 (q46 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw⁻ 23 (q11 c4) ∷
   rw⁻ 24 (q47 c4) ∷
   rw⁻ 21 (q48 c4) ∷
   rw⁻ 18 (q47 c4) ∷
   rw⁻ 15 (q48 c4) ∷
   rw 18 (q11 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q11 c4) ∷
   rw⁻ 17 (q46 c4) ∷
   rw 18 (q11 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q11 c4) ∷
   rw 21 (q11 c4) ∷
   re 17 5 (Sb2-0-41-3 ∷ []) ∷
   re 15 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 18 (q49 c4) ∷
   rw 17 (q50 c4) ∷
   rw⁻ 16 (q49 c4) ∷
   re 20 1 (CS03⁻ ∷ []) ∷
   re 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 19 (q11 c4) ∷
   rw⁻ 22 (q11 c4) ∷
   rw⁻ 25 (q11 c4) ∷
   rw⁻ 28 (q11 c4) ∷
   re 30 1 (CS03⁻ ∷ []) ∷
   rw⁻ 29 (q51 c4) ∷
   re 31 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 24 1 (CS03 ∷ []) ∷
   rw⁻ 20 (q52 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   rw 18 (q46 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   rw⁻ 22 (q11 c4) ∷
   rw⁻ 25 (q11 c4) ∷
   rw⁻ 26 (q53 c4) ∷
   rw⁻ 23 (q54 c4) ∷
   rw⁻ 20 (q53 c4) ∷
   rw⁻ 17 (q54 c4) ∷
   rw 20 (q11 c4) ∷
   rw 21 (q11 c4) ∷
   rw 22 (q11 c4) ∷
   rw⁻ 19 (q46 c4) ∷
   rw 20 (q11 c4) ∷
   rw 21 (q11 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q11 c4) ∷
   re 19 5 (Sb2-0-41-3 ∷ []) ∷
   re 17 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q49 c4) ∷
   rw 19 (q50 c4) ∷
   rw⁻ 18 (q49 c4) ∷
   rw 22 (q35 c4) ∷
   rw 22 (q55 c4) ∷
   rw 22 (q56 c4) ∷
   rw 22 (q32 c4) ∷
   rw 20 (q18 c4) ∷
   re 20 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 21 (q11 c4) ∷
   rw⁻ 24 (q11 c4) ∷
   rw⁻ 27 (q11 c4) ∷
   rw⁻ 30 (q11 c4) ∷
   re 32 1 (CS02⁻ ∷ []) ∷
   rw⁻ 31 (q21 c4) ∷
   re 33 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 31 (q17 c4) ∷
   rw⁻ 28 (q22 c4) ∷
   rw⁻ 33 (q22 c4) ∷
   rw⁻ 38 (q22 c4) ∷
   rw⁻ 29 (q23 c4) ∷
   rw⁻ 30 (q24 c4) ∷
   rw 29 (q25 c4) ∷
   rw 29 (q24 c4) ∷
   rw 34 (q23 c4) ∷
   rw 28 (q22 c4) ∷
   rw 31 (q22 c4) ∷
   rw 34 (q22 c4) ∷
   rw 28 (q17 c4) ∷
   re 26 1 (CS02 ∷ []) ∷
   rw⁻ 25 (q26 c4) ∷
   re 27 1 (Sb3-0-2-1 ∷ []) ∷
   rw⁻ 25 (q17 c4) ∷
   rw⁻ 22 (q22 c4) ∷
   rw⁻ 27 (q22 c4) ∷
   rw⁻ 32 (q22 c4) ∷
   rw⁻ 23 (q23 c4) ∷
   rw⁻ 24 (q24 c4) ∷
   rw 23 (q25 c4) ∷
   rw 23 (q24 c4) ∷
   rw 28 (q23 c4) ∷
   rw 22 (q22 c4) ∷
   rw 25 (q22 c4) ∷
   rw 28 (q22 c4) ∷
   rw 22 (q17 c4) ∷
   rw⁻ 22 (q17 c4) ∷
   rw 23 (q16 c4) ∷
   rw⁻ 24 (q15 c4) ∷
   rw⁻ 27 (q15 c4) ∷
   rw⁻ 30 (q15 c4) ∷ []) Eq.refl
