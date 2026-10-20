{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D109 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0503 ; wl0509 ; wl0513 ; wl0514 ; wl0528 ; wl0529 ; wl0530 ; wl0531 ; wl0548 ; wl0550 ; wl0551 ; wl0554 ; wl0558 ; wl0571 ; wl0572 ; wl0576 ; wl0577 ; wl0579 ; wl0580 ; wl0581 ; wl0582 ; wl0583 ; wl0584 ; wp0192 ; wp0200 ; wp0201 ; wp0202 ; wp0203 ; wp0204 ; wp0205 ; wp0225 ; wp0238 ; wp0239 ; wp0240 ; wp0241 ; wp0242 ; wp0243 ; wp0245 ; wp0246 ; wp0247)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-beta-T-at0310243142 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-X1-beta-at0210243143 ; lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04233240 ; lem-auto-CCZ012-∣-CCZ314-at0112243043 ; lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04233240 ; lem-auto-CSd01-∣-BOX⟨2·0134⟩-at143143 ; lem-auto-S0-∣-BOX⟨1·0234⟩-at12243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 ; lem-beta-T-at03103441 ; lem-sym23-at0310243241 ; lem-sym23-at03103441 ; lem-sym34-at0310243142 ; lem-sym34-at0310243241)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CCZ134-CX20)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) (wl0514 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (X0 ∷ CCZ234 ∷ []) (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑))
  q6 : Ws → Eqn
  q6 c4 = eqn (CK01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ))
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Toff314 ∷ CS03 ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) (wp0192 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CS03⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS03⁻ ∷ []) (wl0513 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (X0 ∷ Bx2-0413 ∷ X0 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ []) (lem-X1-beta-at0210243143 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ134 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ134 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04233240 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ []) (wp0205 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ134 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ134 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04233240 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl0503 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ []) (wp0202 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Sb2-0-41-3 ∷ Toff314 ∷ []) (Toff314 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03 ∷ []) (wl0531 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0204 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS03⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ []) (wl0529 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) (wp0201 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS04⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS04⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩-at143143 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ134 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CCZ134 ∷ []) (wp0238 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Toff314 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ []) (wp0239 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CS03 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CS03 ∷ []) (wp0240 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CS03⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CS03⁻ ∷ []) (wp0241 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (S0 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·0234⟩-at12243143 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ134 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CCZ134 ∷ []) (wp0242 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff314 ∷ []) (wp0243 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CS03 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CS03 ∷ []) (wl0576 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS03⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CS03⁻ ∷ []) (wl0577 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (Toff203 ∷ X0 ∷ CS02⁻ ∷ X0 ∷ []) (X0 ∷ CS02⁻ ∷ X0 ∷ Toff203 ∷ []) (wl0571 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (K2 ∷ K2⁻ ∷ []) [] (wl0579 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ124 ∷ []) (K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ []) (wp0245 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ023 ∷ []) (K2⁻ ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ []) (wl0580 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at0112243043 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (Toff203 ∷ X0 ∷ CS02 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ X0 ∷ Toff203 ∷ []) (wl0572 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl0581 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (K2⁻ ∷ K2 ∷ []) [] (wl0550 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ []) (wl0582 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff304 ∷ X0 ∷ []) (X0 ∷ Toff304 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ []) (wp0246 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (X0 ∷ K2 ∷ []) (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑))
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ134 ∷ K2 ∷ []) (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CX20 ∷ X0 ∷ []) (X0 ∷ CX20 ∷ []) (wl0583 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ134 ∷ CX20 ∷ []) (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (X0 ∷ K2⁻ ∷ []) (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑))
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ134 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ X0 ∷ CS03⁻ ∷ []) (wp0247 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (X0 ∷ CS23 ∷ []) (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑))
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ134 ∷ CS23 ∷ []) (CS23 ∷ CCZ134 ∷ []) (wl0558 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (wl0584 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (CCZ124 ∷ X0 ∷ []) (X0 ∷ CCZ124 ∷ []) (wp0225 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (Sb2-0-41-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0210243143 c4)

-- F1 CS-K1 [rhs shape] part18: 375 steps
lem-F1-CS-K1-rhs-shape-part18 : Ws → ⟪ (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ Toff203 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-rhs-shape-part18 c4 = derive (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ Toff203 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   re 26 5 (Sb2-0-41-3 ∷ []) ∷
   re 24 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 20 5 (Sb2-0-41-3 ∷ []) ∷
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 20 (q2 c4) ∷
   rw 20 (q3 c4) ∷
   rw⁻ 17 (q4 c4) ∷
   rw 20 (q5 c4) ∷
   rw 19 (q6 c4) ∷
   rw 18 (q5 c4) ∷
   rw⁻ 19 (q4 c4) ∷
   rw 22 (q5 c4) ∷
   rw 21 (q6 c4) ∷
   rw 20 (q5 c4) ∷
   rw⁻ 17 (q3 c4) ∷
   rw 17 (q7 c4) ∷
   re 22 1 (CS03 ∷ []) ∷
   rw⁻ 18 (q8 c4) ∷
   re 19 1 (Sb2-0-3-1 ∷ []) ∷
   re 24 1 (CS03⁻ ∷ []) ∷
   rw⁻ 21 (q9 c4) ∷
   re 21 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 17 5 (Sb2-0-41-3 ∷ []) ∷
   re 17 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 18 (q1 c4) ∷
   rw 16 (q10 c4) ∷
   rw 16 (q11 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw 14 (q10 c4) ∷
   rw 14 (q11 c4) ∷
   rw 18 (q13 c4) ∷
   rw 15 (q13 c4) ∷
   rw 16 (q14 c4) ∷
   rw 17 (q13 c4) ∷
   rw 18 (q15 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw 16 (q17 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   re 19 1 (CS03 ∷ []) ∷
   re 17 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   re 29 1 (CS03⁻ ∷ []) ∷
   rw⁻ 28 (q18 c4) ∷
   re 30 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 23 1 (CS03 ∷ []) ∷
   rw⁻ 19 (q19 c4) ∷
   re 24 1 (Sb2-0-3-1 ∷ []) ∷
   rw 17 (q20 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 25 (q21 c4) ∷
   rw⁻ 22 (q22 c4) ∷
   rw⁻ 19 (q21 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw⁻ 18 (q20 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   re 18 5 (Sb2-0-41-3 ∷ []) ∷
   re 16 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 19 (q16 c4) ∷
   rw 18 (q17 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   re 21 1 (CS03⁻ ∷ []) ∷
   re 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   re 31 1 (CS03⁻ ∷ []) ∷
   rw⁻ 30 (q23 c4) ∷
   re 32 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 25 1 (CS03 ∷ []) ∷
   rw⁻ 21 (q24 c4) ∷
   re 26 1 (Sb2-0-3-1 ∷ []) ∷
   rw 19 (q20 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 27 (q25 c4) ∷
   rw⁻ 24 (q26 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw⁻ 18 (q26 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw⁻ 20 (q20 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   re 20 5 (Sb2-0-41-3 ∷ []) ∷
   re 18 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 14 5 (Sb2-0-41-3 ∷ []) ∷
   re 14 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q1 c4) ∷
   rw 13 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 12 (q27 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw 11 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 15 (q13 c4) ∷
   rw 12 (q28 c4) ∷
   rw 15 (q15 c4) ∷
   rw⁻ 12 (q29 c4) ∷
   re 16 1 (CS03 ∷ []) ∷
   rw⁻ 13 (q30 c4) ∷
   re 13 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 14 (q29 c4) ∷
   re 18 1 (CS03⁻ ∷ []) ∷
   rw⁻ 15 (q31 c4) ∷
   re 15 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 11 5 (Sb2-0-41-3 ∷ []) ∷
   re 11 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 12 (q1 c4) ∷
   rw 10 (q10 c4) ∷
   rw 10 (q11 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw 8 (q10 c4) ∷
   rw 8 (q11 c4) ∷
   rw 12 (q13 c4) ∷
   rw 9 (q33 c4) ∷
   rw 12 (q15 c4) ∷
   rw⁻ 9 (q34 c4) ∷
   re 13 1 (CS03 ∷ []) ∷
   rw⁻ 10 (q35 c4) ∷
   re 10 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 11 (q34 c4) ∷
   re 15 1 (CS03⁻ ∷ []) ∷
   rw⁻ 12 (q36 c4) ∷
   re 12 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 8 5 (Sb2-0-41-3 ∷ []) ∷
   re 30 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 30 1 (CS03 ∷ []) ∷
   re 28 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   re 40 1 (CS03⁻ ∷ []) ∷
   rw⁻ 39 (q18 c4) ∷
   re 41 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 34 1 (CS03 ∷ []) ∷
   rw⁻ 30 (q19 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ []) ∷
   rw 28 (q20 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 36 (q21 c4) ∷
   rw⁻ 33 (q22 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw⁻ 27 (q22 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw⁻ 29 (q20 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   re 29 5 (Sb2-0-41-3 ∷ []) ∷
   re 27 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q16 c4) ∷
   rw 29 (q17 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   re 32 1 (CS03⁻ ∷ []) ∷
   re 30 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   re 42 1 (CS03⁻ ∷ []) ∷
   rw⁻ 41 (q23 c4) ∷
   re 43 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 36 1 (CS03 ∷ []) ∷
   rw⁻ 32 (q24 c4) ∷
   re 37 1 (Sb2-0-3-1 ∷ []) ∷
   rw 30 (q20 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 38 (q25 c4) ∷
   rw⁻ 35 (q26 c4) ∷
   rw⁻ 32 (q25 c4) ∷
   rw⁻ 29 (q26 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw⁻ 31 (q20 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   re 31 5 (Sb2-0-41-3 ∷ []) ∷
   re 29 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 32 (q16 c4) ∷
   rw 31 (q17 c4) ∷
   rw⁻ 30 (q16 c4) ∷
   rw 34 (q37 c4) ∷
   rw 34 (q38 c4) ∷
   rw 34 (q39 c4) ∷
   rw 34 (q40 c4) ∷
   rw 32 (q41 c4) ∷
   re 32 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   re 44 1 (CS02⁻ ∷ []) ∷
   rw⁻ 43 (q42 c4) ∷
   re 45 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 43 (q43 c4) ∷
   rw⁻ 40 (q44 c4) ∷
   rw⁻ 45 (q44 c4) ∷
   rw⁻ 50 (q44 c4) ∷
   rw⁻ 41 (q45 c4) ∷
   rw⁻ 42 (q46 c4) ∷
   rw 41 (q47 c4) ∷
   rw 41 (q46 c4) ∷
   rw 46 (q45 c4) ∷
   rw 40 (q44 c4) ∷
   rw 43 (q44 c4) ∷
   rw 46 (q44 c4) ∷
   rw 40 (q43 c4) ∷
   re 38 1 (CS02 ∷ []) ∷
   rw⁻ 37 (q48 c4) ∷
   re 39 1 (Sb3-0-2-1 ∷ []) ∷
   rw⁻ 37 (q43 c4) ∷
   rw⁻ 34 (q44 c4) ∷
   rw⁻ 39 (q44 c4) ∷
   rw⁻ 44 (q44 c4) ∷
   rw⁻ 35 (q45 c4) ∷
   rw⁻ 36 (q46 c4) ∷
   rw 35 (q47 c4) ∷
   rw 35 (q46 c4) ∷
   rw 40 (q45 c4) ∷
   rw 34 (q44 c4) ∷
   rw 37 (q44 c4) ∷
   rw 40 (q44 c4) ∷
   rw 34 (q43 c4) ∷
   rw⁻ 34 (q43 c4) ∷
   rw 35 (q49 c4) ∷
   rw⁻ 36 (q50 c4) ∷
   rw⁻ 39 (q50 c4) ∷
   rw⁻ 42 (q50 c4) ∷
   rw⁻ 45 (q50 c4) ∷
   rw 32 (q51 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 40 (q52 c4) ∷
   rw⁻ 37 (q53 c4) ∷
   rw⁻ 34 (q52 c4) ∷
   rw⁻ 31 (q53 c4) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   rw 38 (q1 c4) ∷
   rw⁻ 35 (q51 c4) ∷
   rw 35 (q54 c4) ∷
   rw 35 (q55 c4) ∷
   rw 35 (q56 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw 45 (q57 c4) ∷
   rw 44 (q58 c4) ∷
   rw 43 (q57 c4) ∷
   rw⁻ 46 (q59 c4) ∷
   rw 45 (q60 c4) ∷
   rw⁻ 44 (q59 c4) ∷
   rw 47 (q61 c4) ∷
   rw 46 (q62 c4) ∷
   rw 45 (q61 c4) ∷
   rw 48 (q57 c4) ∷
   rw 47 (q58 c4) ∷
   rw 46 (q57 c4) ∷
   rw⁻ 47 (q63 c4) ∷
   rw 50 (q61 c4) ∷
   rw 49 (q62 c4) ∷
   rw 48 (q61 c4) ∷
   rw 51 (q57 c4) ∷
   rw 50 (q58 c4) ∷
   rw 49 (q57 c4) ∷
   rw⁻ 52 (q59 c4) ∷
   rw 51 (q60 c4) ∷
   rw⁻ 50 (q59 c4) ∷
   rw 53 (q61 c4) ∷
   rw 52 (q62 c4) ∷
   rw 51 (q61 c4) ∷
   rw 54 (q57 c4) ∷
   rw 53 (q58 c4) ∷
   rw 52 (q57 c4) ∷
   rw 55 (q64 c4) ∷
   rw 54 (q65 c4) ∷
   rw 53 (q64 c4) ∷
   rw 56 (q61 c4) ∷
   rw 55 (q62 c4) ∷
   rw 54 (q61 c4) ∷
   rw⁻ 40 (q66 c4) ∷
   rw 39 (q57 c4) ∷
   rw 38 (q58 c4) ∷
   rw 37 (q57 c4) ∷
   rw⁻ 40 (q59 c4) ∷
   rw 39 (q60 c4) ∷
   rw⁻ 38 (q59 c4) ∷
   rw 41 (q61 c4) ∷
   rw 40 (q62 c4) ∷
   rw 39 (q61 c4) ∷
   rw 42 (q57 c4) ∷
   rw 41 (q58 c4) ∷
   rw 40 (q57 c4) ∷
   rw⁻ 41 (q63 c4) ∷
   rw 44 (q61 c4) ∷
   rw 43 (q62 c4) ∷
   rw 42 (q61 c4) ∷
   rw 45 (q57 c4) ∷
   rw 44 (q58 c4) ∷
   rw 43 (q57 c4) ∷
   rw⁻ 46 (q59 c4) ∷
   rw 45 (q60 c4) ∷
   rw⁻ 44 (q59 c4) ∷
   rw 47 (q61 c4) ∷
   rw 46 (q62 c4) ∷
   rw 45 (q61 c4) ∷
   rw 48 (q57 c4) ∷
   rw 47 (q58 c4) ∷
   rw 46 (q57 c4) ∷
   rw 49 (q64 c4) ∷
   rw 48 (q65 c4) ∷
   rw 47 (q64 c4) ∷
   rw 50 (q61 c4) ∷
   rw 49 (q62 c4) ∷
   rw 48 (q61 c4) ∷
   rw⁻ 34 (q66 c4) ∷
   rw 48 (q1 c4) ∷
   rw 49 (q1 c4) ∷
   rw 50 (q1 c4) ∷
   rw⁻ 47 (q56 c4) ∷
   rw 47 (q67 c4) ∷
   rw 47 (q68 c4) ∷
   rw 33 (q50 c4) ∷
   rw 34 (q50 c4) ∷
   rw 35 (q50 c4) ∷
   rw 36 (q50 c4) ∷
   rw⁻ 32 (q49 c4) ∷
   rw 31 (q43 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   re 33 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 33 (q41 c4) ∷
   rw⁻ 34 (q69 c4) ∷
   rw 33 (q70 c4) ∷
   rw⁻ 32 (q69 c4) ∷
   rw 34 (q41 c4) ∷
   re 34 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷ []) Eq.refl
