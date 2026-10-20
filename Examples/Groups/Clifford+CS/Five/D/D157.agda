{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D157 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0393 ; wl0509 ; wl0510 ; wl0511 ; wl0512 ; wl0528 ; wl0529 ; wl0530 ; wl0531 ; wl0535 ; wl0536 ; wl0537 ; wl0538 ; wl0539 ; wl0540 ; wl0541 ; wl0542 ; wl0548 ; wl0551 ; wl0554 ; wl0558 ; wl0563 ; wl0571 ; wl0572 ; wl0579 ; wl0580 ; wl0581 ; wl0583 ; wl0587 ; wl0595 ; wp0190 ; wp0191 ; wp0200 ; wp0201 ; wp0202 ; wp0203 ; wp0204 ; wp0208 ; wp0209 ; wp0210 ; wp0225 ; wp0247 ; wp0251 ; wp0258 ; wp0259)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-auto-CCZ012-∣-CCZ314-at122331)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 ; lem-beta-T-at03103441 ; lem-sym23-at0310243241 ; lem-sym23-at03103441 ; lem-sym34-at0310243142 ; lem-sym34-at0310243241)
open import Examples.Groups.Clifford+CS.Five.D.D123 using (lem-auto-CCZ012-∣-SBOX⟨0·3·12·4⟩-at0214213043)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CX20-CCZ134)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl0563 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (K2 ∷ K2⁻ ∷ []) [] (wl0579 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ023 ∷ []) (K2⁻ ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ []) (wl0580 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ124 ∷ []) (K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ X0 ∷ CCZ124 ∷ X0 ∷ X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ []) (wp0259 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at122331 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Toff203 ∷ X0 ∷ CS02⁻ ∷ X0 ∷ []) (X0 ∷ CS02⁻ ∷ X0 ∷ Toff203 ∷ []) (wl0571 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ124 ∷ X0 ∷ []) (X0 ∷ CCZ124 ∷ []) (wp0225 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ124 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·3·12·4⟩-at0214213043 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (wl0595 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (X0 ∷ K2⁻ ∷ []) (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑))
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ134 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl0581 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (X0 ∷ CS23 ∷ []) (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ134 ∷ CS23 ∷ []) (CS23 ∷ CCZ134 ∷ []) (wl0558 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CX20 ∷ X0 ∷ []) (X0 ∷ CX20 ∷ []) (wl0583 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CX20 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ X0 ∷ CS03⁻ ∷ []) (wp0247 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CS03 ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ X0 ∷ CS03 ∷ []) (wp0258 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (X0 ∷ K2 ∷ []) (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑))
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ134 ∷ K2 ∷ []) (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Toff203 ∷ X0 ∷ CS02 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ X0 ∷ Toff203 ∷ []) (wl0572 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ []) (wp0202 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Toff314 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Toff314 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) (wp0201 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS03⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ []) (wl0529 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0204 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS03 ∷ []) (wl0531 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CK01⁻ ∷ []) (CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ []) (wl0535 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (X0 ∷ ι⁻ ∷ []) (ι⁻ ∷ X0 ∷ []) zc⁻
  q47 : Ws → Eqn
  q47 c4 = eqn (Sb2-0-41-3 ∷ ι⁻ ∷ []) (ι⁻ ∷ Sb2-0-41-3 ∷ []) zc⁻
  q48 : Ws → Eqn
  q48 c4 = eqn (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) (wp0190 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) (wl0510 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) (wp0191 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (S0 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0 ∷ []) (wl0511 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0 ∷ []) (wl0512 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS01⁻ ∷ []) (wp0208 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ CS01⁻ ∷ []) (wl0536 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS01⁻ ∷ []) (wp0209 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CS01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS01⁻ ∷ []) (wl0538 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CS01⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS01⁻ ∷ []) (wl0537 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) (wl0542 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (X0 ∷ K1⁻ ∷ []) (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI))
  q62 : Ws → Eqn
  q62 c4 = eqn (K1⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ K1⁻ ∷ []) (c₂ ((K • iI) ↑) (CCZ))
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS01⁻ ∷ []) (wl0541 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (X0 ∷ CX43 ∷ X0 ∷ CS01⁻ ∷ []) (wl0539 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CS01⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS01⁻ ∷ []) (wl0540 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CS01⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ []) (wp0210 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) (wp0251 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) (wl0587 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)

-- F1 CS-K1 part33: 500 steps
lem-F1-CS-K1-part33 : Ws → ⟪ (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CS04 ∷ S0⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-part33 c4 = derive (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CS04 ∷ S0⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 32 (q1 c4) ∷
   rw⁻ 33 (q2 c4) ∷
   rw⁻ 36 (q2 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw⁻ 33 (q3 c4) ∷
   rw⁻ 44 (q3 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw 29 (q6 c4) ∷
   rw 29 (q5 c4) ∷
   rw 40 (q4 c4) ∷
   rw 28 (q3 c4) ∷
   rw 37 (q3 c4) ∷
   rw 40 (q3 c4) ∷
   rw 30 (q2 c4) ∷
   rw 31 (q2 c4) ∷
   rw 29 (q1 c4) ∷
   rw 31 (q7 c4) ∷
   re 33 1 (CS02⁻ ∷ []) ∷
   rw 31 (q8 c4) ∷
   re 32 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw 24 (q2 c4) ∷
   re 20 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 20 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q10 c4) ∷
   rw 19 (q9 c4) ∷
   re 19 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 17 (q7 c4) ∷
   rw 21 (q12 c4) ∷
   rw 21 (q13 c4) ∷
   rw 21 (q14 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw 17 (q15 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 23 (q17 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 25 (q19 c4) ∷
   rw⁻ 26 (q20 c4) ∷
   rw⁻ 27 (q19 c4) ∷
   rw 24 (q21 c4) ∷
   rw 25 (q22 c4) ∷
   rw 26 (q21 c4) ∷
   rw 23 (q23 c4) ∷
   rw 22 (q21 c4) ∷
   rw 23 (q22 c4) ∷
   rw 24 (q21 c4) ∷
   rw 21 (q24 c4) ∷
   rw⁻ 24 (q18 c4) ∷
   rw⁻ 20 (q25 c4) ∷
   rw⁻ 21 (q26 c4) ∷
   rw⁻ 22 (q25 c4) ∷
   rw 23 (q15 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   rw⁻ 29 (q17 c4) ∷
   rw⁻ 30 (q16 c4) ∷
   rw 27 (q18 c4) ∷
   rw⁻ 31 (q19 c4) ∷
   rw⁻ 32 (q20 c4) ∷
   rw⁻ 33 (q19 c4) ∷
   rw 30 (q21 c4) ∷
   rw 31 (q22 c4) ∷
   rw 32 (q21 c4) ∷
   rw 29 (q23 c4) ∷
   rw 28 (q21 c4) ∷
   rw 29 (q22 c4) ∷
   rw 30 (q21 c4) ∷
   rw 27 (q24 c4) ∷
   rw⁻ 30 (q18 c4) ∷
   rw⁻ 26 (q25 c4) ∷
   rw⁻ 27 (q26 c4) ∷
   rw⁻ 28 (q25 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw⁻ 18 (q14 c4) ∷
   rw 18 (q27 c4) ∷
   rw 18 (q28 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 20 (q3 c4) ∷
   rw⁻ 25 (q3 c4) ∷
   rw⁻ 36 (q3 c4) ∷
   rw⁻ 21 (q4 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw 21 (q6 c4) ∷
   rw 21 (q5 c4) ∷
   rw 32 (q4 c4) ∷
   rw 20 (q3 c4) ∷
   rw 29 (q3 c4) ∷
   rw 32 (q3 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw 21 (q1 c4) ∷
   rw 23 (q7 c4) ∷
   re 25 1 (CS02 ∷ []) ∷
   rw 23 (q29 c4) ∷
   re 24 1 (Sb3-0-2-1 ∷ []) ∷
   rw⁻ 26 (q7 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 26 (q3 c4) ∷
   rw⁻ 31 (q3 c4) ∷
   rw⁻ 42 (q3 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw 27 (q6 c4) ∷
   rw 27 (q5 c4) ∷
   rw 38 (q4 c4) ∷
   rw 26 (q3 c4) ∷
   rw 35 (q3 c4) ∷
   rw 38 (q3 c4) ∷
   rw 28 (q2 c4) ∷
   rw 29 (q2 c4) ∷
   rw 27 (q1 c4) ∷
   rw 29 (q7 c4) ∷
   re 31 1 (CS02⁻ ∷ []) ∷
   rw 29 (q8 c4) ∷
   re 30 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   re 18 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 20 (q30 c4) ∷
   rw 20 (q31 c4) ∷
   rw 20 (q32 c4) ∷
   rw⁻ 20 (q33 c4) ∷
   rw 16 (q34 c4) ∷
   rw 17 (q35 c4) ∷
   rw 18 (q34 c4) ∷
   re 15 1 (CS03⁻ ∷ []) ∷
   re 17 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw 17 (q36 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw 15 (q37 c4) ∷
   rw 18 (q38 c4) ∷
   rw 21 (q37 c4) ∷
   rw 24 (q38 c4) ∷
   rw 17 (q2 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw⁻ 16 (q36 c4) ∷
   re 23 1 (CS03 ∷ []) ∷
   rw 18 (q39 c4) ∷
   re 22 1 (Sb2-0-3-1 ∷ []) ∷
   re 29 1 (CS03⁻ ∷ []) ∷
   rw 27 (q40 c4) ∷
   re 28 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 17 (q2 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   re 16 5 (Sb2-0-41-3 ∷ []) ∷
   re 18 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 14 (q34 c4) ∷
   rw 15 (q35 c4) ∷
   rw 16 (q34 c4) ∷
   re 13 1 (CS03 ∷ []) ∷
   re 15 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 16 (q2 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw 15 (q36 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw 13 (q41 c4) ∷
   rw 16 (q42 c4) ∷
   rw 19 (q41 c4) ∷
   rw 22 (q42 c4) ∷
   rw 15 (q2 c4) ∷
   rw 16 (q2 c4) ∷
   rw 17 (q2 c4) ∷
   rw⁻ 14 (q36 c4) ∷
   re 21 1 (CS03 ∷ []) ∷
   rw 16 (q43 c4) ∷
   re 20 1 (Sb2-0-3-1 ∷ []) ∷
   re 27 1 (CS03⁻ ∷ []) ∷
   rw 25 (q44 c4) ∷
   re 26 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 15 (q2 c4) ∷
   rw 16 (q2 c4) ∷
   rw 17 (q2 c4) ∷
   rw 18 (q2 c4) ∷
   re 14 5 (Sb2-0-41-3 ∷ []) ∷
   re 16 1 (Sb2-0-3-1 ∷ []) ∷
   re 16 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 12 (q45 c4) ∷
   rw⁻ 18 (q46 c4) ∷
   rw⁻ 19 (q47 c4) ∷
   rw⁻ 20 (q46 c4) ∷
   re 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw 19 (q36 c4) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw 17 (q48 c4) ∷
   rw 20 (q49 c4) ∷
   rw 23 (q48 c4) ∷
   rw 26 (q49 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw⁻ 18 (q36 c4) ∷
   rw 20 (q50 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   rw 23 (q51 c4) ∷
   re 24 1 (Sb2-0-3-1 ∷ []) ∷
   rw 26 (q50 c4) ∷
   re 31 1 (CS03⁻ ∷ []) ∷
   rw 29 (q52 c4) ∷
   re 30 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   re 18 5 (Sb2-0-41-3 ∷ []) ∷
   re 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw 18 (q36 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw 16 (q53 c4) ∷
   rw 19 (q54 c4) ∷
   rw 22 (q53 c4) ∷
   rw 25 (q54 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw⁻ 17 (q36 c4) ∷
   rw 19 (q55 c4) ∷
   re 24 1 (CS03 ∷ []) ∷
   rw 22 (q56 c4) ∷
   re 23 1 (Sb2-0-3-1 ∷ []) ∷
   rw 25 (q55 c4) ∷
   re 30 1 (CS03⁻ ∷ []) ∷
   rw 28 (q57 c4) ∷
   re 29 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   re 17 5 (Sb2-0-41-3 ∷ []) ∷
   re 17 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw 17 (q58 c4) ∷
   rw 17 (q59 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw 13 (q60 c4) ∷
   rw⁻ 18 (q61 c4) ∷
   rw 19 (q62 c4) ∷
   rw⁻ 20 (q61 c4) ∷
   rw 19 (q63 c4) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw 17 (q64 c4) ∷
   rw 20 (q65 c4) ∷
   rw 23 (q66 c4) ∷
   rw 26 (q65 c4) ∷
   rw 29 (q67 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   rw⁻ 18 (q63 c4) ∷
   rw⁻ 16 (q61 c4) ∷
   rw 17 (q62 c4) ∷
   rw⁻ 18 (q61 c4) ∷
   rw 19 (q60 c4) ∷
   rw⁻ 24 (q61 c4) ∷
   rw 25 (q62 c4) ∷
   rw⁻ 26 (q61 c4) ∷
   rw 25 (q63 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   rw 23 (q64 c4) ∷
   rw 26 (q65 c4) ∷
   rw 29 (q66 c4) ∷
   rw 32 (q65 c4) ∷
   rw 35 (q67 c4) ∷
   rw 25 (q2 c4) ∷
   rw 26 (q2 c4) ∷
   rw 27 (q2 c4) ∷
   rw 28 (q2 c4) ∷
   rw⁻ 24 (q63 c4) ∷
   rw⁻ 22 (q61 c4) ∷
   rw 23 (q62 c4) ∷
   rw⁻ 24 (q61 c4) ∷
   rw 15 (q2 c4) ∷
   rw 16 (q2 c4) ∷
   rw 17 (q2 c4) ∷
   rw⁻ 14 (q59 c4) ∷
   rw 14 (q68 c4) ∷
   re 23 1 (CS03 ∷ []) ∷
   rw 16 (q69 c4) ∷
   re 20 1 (Sb2-0-3-1 ∷ []) ∷
   re 29 1 (CS03⁻ ∷ []) ∷
   rw 25 (q70 c4) ∷
   re 26 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 15 (q2 c4) ∷
   rw 16 (q2 c4) ∷
   rw 17 (q2 c4) ∷
   rw 18 (q2 c4) ∷
   re 14 5 (Sb2-0-41-3 ∷ []) ∷
   re 14 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q2 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw 14 (q36 c4) ∷
   rw⁻ 15 (q2 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw 12 (q53 c4) ∷
   rw 15 (q54 c4) ∷
   rw 18 (q53 c4) ∷
   rw 21 (q54 c4) ∷
   rw 14 (q2 c4) ∷
   rw 15 (q2 c4) ∷
   rw 16 (q2 c4) ∷
   rw⁻ 13 (q36 c4) ∷
   rw 15 (q55 c4) ∷
   re 20 1 (CS03 ∷ []) ∷
   rw 18 (q56 c4) ∷
   re 19 1 (Sb2-0-3-1 ∷ []) ∷
   rw 21 (q55 c4) ∷
   re 26 1 (CS03⁻ ∷ []) ∷
   rw 24 (q57 c4) ∷
   re 25 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 14 (q2 c4) ∷
   rw 15 (q2 c4) ∷
   rw 16 (q2 c4) ∷
   rw 17 (q2 c4) ∷
   re 13 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 15 (q45 c4) ∷
   re 11 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw 15 (q33 c4) ∷
   rw 15 (q71 c4) ∷
   rw 15 (q72 c4) ∷
   rw 15 (q30 c4) ∷
   rw 18 (q10 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q10 c4) ∷
   rw 19 (q9 c4) ∷
   re 19 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 17 (q7 c4) ∷
   rw 21 (q12 c4) ∷
   rw 21 (q13 c4) ∷
   rw 21 (q14 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw 17 (q15 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 23 (q17 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 25 (q19 c4) ∷
   rw⁻ 26 (q20 c4) ∷
   rw⁻ 27 (q19 c4) ∷
   rw 24 (q21 c4) ∷
   rw 25 (q22 c4) ∷
   rw 26 (q21 c4) ∷
   rw 23 (q23 c4) ∷
   rw 22 (q21 c4) ∷
   rw 23 (q22 c4) ∷
   rw 24 (q21 c4) ∷
   rw 21 (q24 c4) ∷
   rw⁻ 24 (q18 c4) ∷
   rw⁻ 20 (q25 c4) ∷
   rw⁻ 21 (q26 c4) ∷
   rw⁻ 22 (q25 c4) ∷
   rw 23 (q15 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   rw⁻ 29 (q17 c4) ∷
   rw⁻ 30 (q16 c4) ∷
   rw 27 (q18 c4) ∷
   rw⁻ 31 (q19 c4) ∷
   rw⁻ 32 (q20 c4) ∷
   rw⁻ 33 (q19 c4) ∷
   rw 30 (q21 c4) ∷
   rw 31 (q22 c4) ∷
   rw 32 (q21 c4) ∷
   rw 29 (q23 c4) ∷
   rw 28 (q21 c4) ∷
   rw 29 (q22 c4) ∷
   rw 30 (q21 c4) ∷
   rw 27 (q24 c4) ∷
   rw⁻ 30 (q18 c4) ∷
   rw⁻ 26 (q25 c4) ∷
   rw⁻ 27 (q26 c4) ∷
   rw⁻ 28 (q25 c4) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw⁻ 18 (q14 c4) ∷
   rw 18 (q27 c4) ∷
   rw 18 (q28 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 20 (q3 c4) ∷
   rw⁻ 25 (q3 c4) ∷
   rw⁻ 36 (q3 c4) ∷
   rw⁻ 21 (q4 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw 21 (q6 c4) ∷
   rw 21 (q5 c4) ∷
   rw 32 (q4 c4) ∷
   rw 20 (q3 c4) ∷
   rw 29 (q3 c4) ∷
   rw 32 (q3 c4) ∷
   rw 22 (q2 c4) ∷
   rw 23 (q2 c4) ∷
   rw 21 (q1 c4) ∷
   rw 23 (q7 c4) ∷
   re 25 1 (CS02 ∷ []) ∷
   rw 23 (q29 c4) ∷
   re 24 1 (Sb3-0-2-1 ∷ []) ∷
   rw⁻ 26 (q7 c4) ∷
   rw⁻ 30 (q1 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 26 (q3 c4) ∷
   rw⁻ 31 (q3 c4) ∷
   rw⁻ 42 (q3 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw 27 (q6 c4) ∷
   rw 27 (q5 c4) ∷
   rw 38 (q4 c4) ∷
   rw 26 (q3 c4) ∷
   rw 35 (q3 c4) ∷
   rw 38 (q3 c4) ∷
   rw 28 (q2 c4) ∷
   rw 29 (q2 c4) ∷
   rw 27 (q1 c4) ∷
   rw 29 (q7 c4) ∷
   re 31 1 (CS02⁻ ∷ []) ∷
   rw 29 (q8 c4) ∷
   re 30 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw 19 (q2 c4) ∷
   rw 20 (q2 c4) ∷
   rw 21 (q2 c4) ∷
   rw 22 (q2 c4) ∷
   re 18 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 18 (q9 c4) ∷
   rw 16 (q10 c4) ∷
   rw 17 (q11 c4) ∷
   rw 18 (q10 c4) ∷
   rw 17 (q9 c4) ∷
   re 17 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 18 (q2 c4) ∷ []) Eq.refl
