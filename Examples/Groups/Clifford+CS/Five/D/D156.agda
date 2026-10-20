{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D156 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0248 ; wl0249 ; wl0250 ; wl0433 ; wl0474 ; wl0509 ; wl0525 ; wl0526 ; wl0527 ; wl0548 ; wl0551 ; wl0554 ; wl0558 ; wl0563 ; wl0572 ; wl0579 ; wl0580 ; wl0581 ; wl0583 ; wl0590 ; wl0591 ; wl0592 ; wl0593 ; wl0594 ; wl0595 ; wp0034 ; wp0059 ; wp0198 ; wp0199 ; wp0225 ; wp0227 ; wp0228 ; wp0229 ; wp0230 ; wp0231 ; wp0232 ; wp0233 ; wp0234 ; wp0247 ; wp0253 ; wp0254 ; wp0255 ; wp0256 ; wp0257 ; wp0258 ; wp0259)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-auto-CCZ012-∣-CCZ314-at122331)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D044 using (lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at0412203143)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-F5-CS01-at0440 ; lem-SBtgt-at0440 ; lem-beta-T-at03103441 ; lem-sym23-at0310243241 ; lem-sym23-at03103441 ; lem-sym34-at0310243142 ; lem-sym34-at0310243241)
open import Examples.Groups.Clifford+CS.Five.D.D123 using (lem-auto-CCZ012-∣-SBOX⟨0·3·12·4⟩-at0214213043)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CX20-CCZ134)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CS04 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS04 ∷ []) (wp0233 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CS04 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS04 ∷ []) (wp0232 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CS04 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS04 ∷ []) (wp0234 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl0509 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CS04 ∷ X0 ∷ CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ X0 ∷ CS04 ∷ []) (wp0227 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CS04 ∷ X0 ∷ CX13 ∷ X0 ∷ []) (X0 ∷ CX13 ∷ X0 ∷ CS04 ∷ []) (wp0228 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CS04 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS04 ∷ []) (wp0229 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CS04 ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS04 ∷ []) (wp0230 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CS04 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS04 ∷ []) (wp0231 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) (wp0253 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CS04 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CS04 ∷ []) (wp0254 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) (wp0255 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (S0⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ S0⁻ ∷ []) (wl0527 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (S0⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) (wp0199 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (S0⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ S0⁻ ∷ []) (wl0526 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (S0⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) (wl0525 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) (wp0198 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (S0⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ S0⁻ ∷ []) (wl0590 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (S0⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ S0⁻ ∷ []) (wp0256 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (S0⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ S0⁻ ∷ []) (wl0591 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS03⁻ ∷ CS03 ∷ []) [] (wl0249 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl0248 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS03 ∷ CS03⁻ ∷ []) [] (wl0250 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) [] (wl0474 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp0034 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp0059 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CK01 ∷ CK01⁻ ∷ []) [] (wl0592 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CS04⁻ ∷ CS04 ∷ []) [] (wp0257 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (S0 ∷ S0⁻ ∷ []) [] (wl0593 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (CS14 ∷ []) (lem-F5-CS01-at0440 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Sb2-4-01-3 ∷ []) (Sb2-0-41-3 ∷ []) (lem-SBtgt-at0440 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (S4⁻ ∷ X0 ∷ []) (X0 ∷ S4⁻ ∷ []) (wl0594 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S4⁻ ∷ []) (lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ124 ∷ X0 ∷ []) (X0 ∷ CCZ124 ∷ []) (wp0225 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ124 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·3·12·4⟩-at0214213043 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (wl0595 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (X0 ∷ K2⁻ ∷ []) (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑))
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ134 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl0581 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (X0 ∷ CS23 ∷ []) (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑))
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ134 ∷ CS23 ∷ []) (CS23 ∷ CCZ134 ∷ []) (wl0558 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CX20 ∷ X0 ∷ []) (X0 ∷ CX20 ∷ []) (wl0583 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CX20 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ X0 ∷ CS03⁻ ∷ []) (wp0247 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CS03 ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ X0 ∷ CS03 ∷ []) (wp0258 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (X0 ∷ K2 ∷ []) (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑))
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ134 ∷ K2 ∷ []) (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl0563 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (K2 ∷ K2⁻ ∷ []) [] (wl0579 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ023 ∷ []) (K2⁻ ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ []) (wl0580 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ124 ∷ []) (K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ X0 ∷ CCZ124 ∷ X0 ∷ X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ []) (wp0259 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at122331 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Toff203 ∷ X0 ∷ CS02 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ X0 ∷ Toff203 ∷ []) (wl0572 (lit c4))

-- F1 CS-K1 part32: 500 steps
lem-F1-CS-K1-part32 : Ws → ⟪ (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CS04 ∷ S0⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-part32 c4 = derive (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CS04 ∷ S0⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 38 (q1 c4) ∷
   re 40 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 35 (q2 c4) ∷
   re 33 1 (CS03 ∷ []) ∷
   rw⁻ 32 (q3 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 29 (q2 c4) ∷
   rw 27 (q4 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 34 (q5 c4) ∷
   rw 36 (q6 c4) ∷
   rw⁻ 37 (q5 c4) ∷
   rw⁻ 40 (q5 c4) ∷
   rw⁻ 43 (q5 c4) ∷
   rw⁻ 46 (q5 c4) ∷
   rw⁻ 47 (q7 c4) ∷
   rw⁻ 44 (q8 c4) ∷
   rw⁻ 41 (q9 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 35 (q10 c4) ∷
   rw 38 (q5 c4) ∷
   rw 39 (q5 c4) ∷
   rw 40 (q5 c4) ∷
   rw 41 (q5 c4) ∷
   rw⁻ 37 (q6 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw 30 (q6 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 34 (q5 c4) ∷
   rw⁻ 37 (q5 c4) ∷
   rw⁻ 40 (q5 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 35 (q9 c4) ∷
   rw⁻ 32 (q8 c4) ∷
   rw⁻ 29 (q10 c4) ∷
   rw 32 (q5 c4) ∷
   rw 33 (q5 c4) ∷
   rw 34 (q5 c4) ∷
   rw 35 (q5 c4) ∷
   rw⁻ 31 (q6 c4) ∷
   rw⁻ 26 (q11 c4) ∷
   rw 29 (q5 c4) ∷
   rw 30 (q5 c4) ∷
   rw 31 (q5 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw 29 (q5 c4) ∷
   rw 30 (q5 c4) ∷
   rw 31 (q5 c4) ∷
   rw 32 (q5 c4) ∷
   re 28 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 23 (q12 c4) ∷
   re 21 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 22 (q5 c4) ∷
   rw⁻ 25 (q5 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   re 33 1 (CS03⁻ ∷ []) ∷
   rw⁻ 32 (q1 c4) ∷
   re 34 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 29 (q2 c4) ∷
   re 27 1 (CS03 ∷ []) ∷
   rw⁻ 26 (q3 c4) ∷
   re 28 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q2 c4) ∷
   rw 21 (q4 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw⁻ 25 (q5 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw 30 (q6 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 34 (q5 c4) ∷
   rw⁻ 37 (q5 c4) ∷
   rw⁻ 40 (q5 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 35 (q9 c4) ∷
   rw⁻ 32 (q8 c4) ∷
   rw⁻ 29 (q10 c4) ∷
   rw 32 (q5 c4) ∷
   rw 33 (q5 c4) ∷
   rw 34 (q5 c4) ∷
   rw 35 (q5 c4) ∷
   rw⁻ 31 (q6 c4) ∷
   rw⁻ 26 (q11 c4) ∷
   rw 24 (q6 c4) ∷
   rw⁻ 25 (q5 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 34 (q5 c4) ∷
   rw⁻ 35 (q7 c4) ∷
   rw⁻ 32 (q8 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw⁻ 26 (q8 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw 26 (q5 c4) ∷
   rw 27 (q5 c4) ∷
   rw 28 (q5 c4) ∷
   rw 29 (q5 c4) ∷
   rw⁻ 25 (q6 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw 23 (q5 c4) ∷
   rw 24 (q5 c4) ∷
   rw 25 (q5 c4) ∷
   rw⁻ 22 (q4 c4) ∷
   rw 23 (q5 c4) ∷
   rw 24 (q5 c4) ∷
   rw 25 (q5 c4) ∷
   rw 26 (q5 c4) ∷
   re 22 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 17 (q13 c4) ∷
   rw⁻ 14 (q14 c4) ∷
   re 34 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 35 (q5 c4) ∷
   rw⁻ 38 (q5 c4) ∷
   rw⁻ 41 (q5 c4) ∷
   rw⁻ 44 (q5 c4) ∷
   re 46 1 (CS03⁻ ∷ []) ∷
   rw⁻ 45 (q15 c4) ∷
   re 47 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 42 (q16 c4) ∷
   re 40 1 (CS03 ∷ []) ∷
   rw⁻ 39 (q17 c4) ∷
   re 41 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 36 (q16 c4) ∷
   rw 34 (q4 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw⁻ 38 (q5 c4) ∷
   rw⁻ 41 (q5 c4) ∷
   rw⁻ 42 (q18 c4) ∷
   rw⁻ 39 (q19 c4) ∷
   rw⁻ 36 (q18 c4) ∷
   rw⁻ 33 (q19 c4) ∷
   rw 36 (q5 c4) ∷
   rw 37 (q5 c4) ∷
   rw 38 (q5 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw 36 (q5 c4) ∷
   rw 37 (q5 c4) ∷
   rw 38 (q5 c4) ∷
   rw 39 (q5 c4) ∷
   re 35 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 30 (q20 c4) ∷
   re 28 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 29 (q5 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw⁻ 38 (q5 c4) ∷
   re 40 1 (CS03⁻ ∷ []) ∷
   rw⁻ 39 (q15 c4) ∷
   re 41 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 36 (q16 c4) ∷
   re 34 1 (CS03 ∷ []) ∷
   rw⁻ 33 (q17 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q16 c4) ∷
   rw 28 (q4 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw⁻ 36 (q18 c4) ∷
   rw⁻ 33 (q19 c4) ∷
   rw⁻ 30 (q18 c4) ∷
   rw⁻ 27 (q19 c4) ∷
   rw 30 (q5 c4) ∷
   rw 31 (q5 c4) ∷
   rw 32 (q5 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw 30 (q5 c4) ∷
   rw 31 (q5 c4) ∷
   rw 32 (q5 c4) ∷
   rw 33 (q5 c4) ∷
   re 29 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 24 (q20 c4) ∷
   re 22 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q5 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   re 34 1 (CS03⁻ ∷ []) ∷
   rw⁻ 33 (q15 c4) ∷
   re 35 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 30 (q16 c4) ∷
   re 28 1 (CS03 ∷ []) ∷
   rw⁻ 27 (q17 c4) ∷
   re 29 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q16 c4) ∷
   rw 22 (q4 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw⁻ 30 (q18 c4) ∷
   rw⁻ 27 (q19 c4) ∷
   rw⁻ 24 (q18 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw 24 (q5 c4) ∷
   rw 25 (q5 c4) ∷
   rw 26 (q5 c4) ∷
   rw⁻ 23 (q4 c4) ∷
   rw 24 (q5 c4) ∷
   rw 25 (q5 c4) ∷
   rw 26 (q5 c4) ∷
   rw 27 (q5 c4) ∷
   re 23 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 18 (q21 c4) ∷
   rw⁻ 15 (q22 c4) ∷
   rw 36 (q5 c4) ∷
   re 36 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 35 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 39 1 (CS03⁻ ∷ []) ∷
   re 40 1 (CS03 ∷ []) ∷
   rw 39 (q23 c4) ∷
   rw 38 (q24 c4) ∷
   re 37 1 (CS03 ∷ []) ∷
   re 38 1 (CS03⁻ ∷ []) ∷
   rw 37 (q25 c4) ∷
   rw 36 (q24 c4) ∷
   re 36 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   re 35 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 40 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 42 1 (CZ03 ∷ []) ∷
   re 45 1 (CZ03 ∷ []) ∷
   re 46 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 46 1 (CZ03 ∷ []) ∷
   re 49 1 (CZ03 ∷ []) ∷
   rw 40 (q26 c4) ∷
   rw 39 (q27 c4) ∷
   rw 38 (q28 c4) ∷
   re 37 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 39 1 (CZ03 ∷ []) ∷
   re 42 1 (CZ03 ∷ []) ∷
   re 43 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 43 1 (CZ03 ∷ []) ∷
   re 46 1 (CZ03 ∷ []) ∷
   rw 37 (q26 c4) ∷
   rw 36 (q28 c4) ∷
   rw 35 (q27 c4) ∷
   rw 34 (q5 c4) ∷
   rw 33 (q5 c4) ∷
   rw 32 (q29 c4) ∷
   rw 31 (q5 c4) ∷
   rw 30 (q5 c4) ∷
   re 30 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 29 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 33 1 (CS03⁻ ∷ []) ∷
   re 34 1 (CS03 ∷ []) ∷
   rw 33 (q23 c4) ∷
   rw 32 (q24 c4) ∷
   re 31 1 (CS03 ∷ []) ∷
   re 32 1 (CS03⁻ ∷ []) ∷
   rw 31 (q25 c4) ∷
   rw 30 (q24 c4) ∷
   re 30 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   re 29 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 34 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 36 1 (CZ03 ∷ []) ∷
   re 39 1 (CZ03 ∷ []) ∷
   re 40 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 40 1 (CZ03 ∷ []) ∷
   re 43 1 (CZ03 ∷ []) ∷
   rw 34 (q26 c4) ∷
   rw 33 (q27 c4) ∷
   rw 32 (q28 c4) ∷
   re 31 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 33 1 (CZ03 ∷ []) ∷
   re 36 1 (CZ03 ∷ []) ∷
   re 37 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 37 1 (CZ03 ∷ []) ∷
   re 40 1 (CZ03 ∷ []) ∷
   rw 31 (q26 c4) ∷
   rw 30 (q28 c4) ∷
   rw 29 (q27 c4) ∷
   rw 28 (q5 c4) ∷
   rw 27 (q5 c4) ∷
   rw 26 (q29 c4) ∷
   rw 25 (q5 c4) ∷
   rw 24 (q5 c4) ∷
   re 24 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 27 1 (CS03⁻ ∷ []) ∷
   re 28 1 (CS03 ∷ []) ∷
   rw 27 (q23 c4) ∷
   rw 26 (q24 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   re 26 1 (CS03⁻ ∷ []) ∷
   rw 25 (q25 c4) ∷
   rw 24 (q24 c4) ∷
   re 24 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   re 23 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 28 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 30 1 (CZ03 ∷ []) ∷
   re 33 1 (CZ03 ∷ []) ∷
   re 34 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 34 1 (CZ03 ∷ []) ∷
   re 37 1 (CZ03 ∷ []) ∷
   rw 28 (q26 c4) ∷
   rw 27 (q27 c4) ∷
   rw 26 (q28 c4) ∷
   re 25 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 27 1 (CZ03 ∷ []) ∷
   re 30 1 (CZ03 ∷ []) ∷
   re 31 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 31 1 (CZ03 ∷ []) ∷
   re 34 1 (CZ03 ∷ []) ∷
   rw 25 (q26 c4) ∷
   rw 24 (q28 c4) ∷
   rw 23 (q27 c4) ∷
   rw 22 (q5 c4) ∷
   rw 21 (q5 c4) ∷
   rw 20 (q30 c4) ∷
   rw 19 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw 17 (q31 c4) ∷
   rw 16 (q5 c4) ∷
   rw⁻ 17 (q32 c4) ∷
   rw 18 (q33 c4) ∷
   rw 20 (q33 c4) ∷
   rw 16 (q34 c4) ∷
   rw 17 (q35 c4) ∷
   rw 18 (q34 c4) ∷
   re 17 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 18 (q5 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw⁻ 27 (q5 c4) ∷
   rw 17 (q4 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 15 (q19 c4) ∷
   rw 18 (q18 c4) ∷
   rw 21 (q19 c4) ∷
   rw 24 (q18 c4) ∷
   rw 17 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 16 (q4 c4) ∷
   rw 18 (q16 c4) ∷
   re 23 1 (CS03 ∷ []) ∷
   rw 21 (q17 c4) ∷
   re 22 1 (Sb2-0-3-1 ∷ []) ∷
   rw 24 (q16 c4) ∷
   re 29 1 (CS03⁻ ∷ []) ∷
   rw 27 (q15 c4) ∷
   re 28 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 17 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw 19 (q5 c4) ∷
   rw 20 (q5 c4) ∷
   re 16 5 (Sb2-0-41-3 ∷ []) ∷
   re 16 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 17 (q5 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   rw 16 (q4 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw 14 (q11 c4) ∷
   rw 19 (q6 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw 17 (q10 c4) ∷
   rw 20 (q8 c4) ∷
   rw 23 (q9 c4) ∷
   rw 26 (q8 c4) ∷
   rw 29 (q7 c4) ∷
   rw 19 (q5 c4) ∷
   rw 20 (q5 c4) ∷
   rw 21 (q5 c4) ∷
   rw 22 (q5 c4) ∷
   rw⁻ 18 (q6 c4) ∷
   rw 20 (q11 c4) ∷
   rw 25 (q6 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw 23 (q10 c4) ∷
   rw 26 (q8 c4) ∷
   rw 29 (q9 c4) ∷
   rw 32 (q8 c4) ∷
   rw 35 (q7 c4) ∷
   rw 25 (q5 c4) ∷
   rw 26 (q5 c4) ∷
   rw 27 (q5 c4) ∷
   rw 28 (q5 c4) ∷
   rw⁻ 24 (q6 c4) ∷
   rw 16 (q5 c4) ∷
   rw 17 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw 17 (q2 c4) ∷
   re 22 1 (CS03 ∷ []) ∷
   rw 20 (q3 c4) ∷
   re 21 1 (Sb2-0-3-1 ∷ []) ∷
   rw 23 (q2 c4) ∷
   re 28 1 (CS03⁻ ∷ []) ∷
   rw 26 (q1 c4) ∷
   re 27 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 16 (q5 c4) ∷
   rw 17 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw 19 (q5 c4) ∷
   re 15 5 (Sb2-0-41-3 ∷ []) ∷
   re 13 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw 17 (q36 c4) ∷
   rw 17 (q37 c4) ∷
   rw 17 (q38 c4) ∷
   rw 17 (q39 c4) ∷
   rw 20 (q40 c4) ∷
   rw 21 (q41 c4) ∷
   rw 22 (q40 c4) ∷
   rw 21 (q42 c4) ∷
   re 21 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 22 (q5 c4) ∷
   rw⁻ 25 (q5 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 19 (q43 c4) ∷
   rw 23 (q44 c4) ∷
   rw 23 (q45 c4) ∷
   rw 23 (q46 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw⁻ 27 (q5 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw 19 (q47 c4) ∷
   rw⁻ 24 (q48 c4) ∷
   rw⁻ 25 (q49 c4) ∷
   rw⁻ 26 (q48 c4) ∷
   rw 23 (q50 c4) ∷
   rw⁻ 27 (q51 c4) ∷
   rw⁻ 28 (q52 c4) ∷
   rw⁻ 29 (q51 c4) ∷
   rw 26 (q53 c4) ∷
   rw 27 (q54 c4) ∷
   rw 28 (q53 c4) ∷
   rw 25 (q55 c4) ∷
   rw 24 (q53 c4) ∷
   rw 25 (q54 c4) ∷
   rw 26 (q53 c4) ∷
   rw 23 (q56 c4) ∷
   rw⁻ 26 (q50 c4) ∷
   rw⁻ 22 (q57 c4) ∷
   rw⁻ 23 (q58 c4) ∷
   rw⁻ 24 (q57 c4) ∷
   rw 25 (q47 c4) ∷
   rw⁻ 30 (q48 c4) ∷
   rw⁻ 31 (q49 c4) ∷
   rw⁻ 32 (q48 c4) ∷
   rw 29 (q50 c4) ∷
   rw⁻ 33 (q51 c4) ∷
   rw⁻ 34 (q52 c4) ∷
   rw⁻ 35 (q51 c4) ∷
   rw 32 (q53 c4) ∷
   rw 33 (q54 c4) ∷
   rw 34 (q53 c4) ∷
   rw 31 (q55 c4) ∷
   rw 30 (q53 c4) ∷
   rw 31 (q54 c4) ∷
   rw 32 (q53 c4) ∷
   rw 29 (q56 c4) ∷
   rw⁻ 32 (q50 c4) ∷
   rw⁻ 28 (q57 c4) ∷
   rw⁻ 29 (q58 c4) ∷
   rw⁻ 30 (q57 c4) ∷
   rw 21 (q5 c4) ∷
   rw 22 (q5 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 20 (q46 c4) ∷
   rw 20 (q59 c4) ∷
   rw 20 (q60 c4) ∷
   rw 22 (q43 c4) ∷
   rw⁻ 22 (q43 c4) ∷
   rw⁻ 26 (q61 c4) ∷
   rw⁻ 27 (q5 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw⁻ 22 (q62 c4) ∷
   rw⁻ 27 (q62 c4) ∷
   rw⁻ 38 (q62 c4) ∷
   rw⁻ 23 (q63 c4) ∷
   rw⁻ 24 (q64 c4) ∷
   rw 23 (q65 c4) ∷
   rw 23 (q64 c4) ∷
   rw 34 (q63 c4) ∷
   rw 22 (q62 c4) ∷
   rw 31 (q62 c4) ∷
   rw 34 (q62 c4) ∷
   rw 24 (q5 c4) ∷
   rw 25 (q5 c4) ∷
   rw 23 (q61 c4) ∷
   rw 25 (q43 c4) ∷
   re 27 1 (CS02 ∷ []) ∷
   rw 25 (q66 c4) ∷
   re 26 1 (Sb3-0-2-1 ∷ []) ∷
   rw⁻ 28 (q43 c4) ∷ []) Eq.refl
