{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D195 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0008 ; wl0010 ; wl0061 ; wl0064 ; wl0159 ; wl0161 ; wl0885 ; wl0886 ; wl0887 ; wl0888 ; wp0461 ; wp0462 ; wp0463 ; wp0464 ; wp0465 ; wp0468)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F5-CS01)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-F4-CS01ᵖ0∣iIᵖ1 ; lem-F4-K1ᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-F4-CS01ᵖ0∣CS01ᵖ1 ; lem-F4-CS01ᵖ0∣K1ᵖ1 ; lem-F4-CS01ᵖ0∣S0ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1)
open import Examples.Groups.Clifford+CS.Five.D.D192 using (lem-DB4K1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12-S1-S1-S1)
open import Examples.Groups.Clifford+CS.Five.D.D194 using (lem-F1-rel-269-rhs)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.TR using (tr03 ; tr04)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw01 ∷ Toff324 ∷ []) (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw01 ∷ Sb1-0-3-2 ∷ []) (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q7 : Ws → Eqn
  q7 c4 = eqn (CK31 ∷ Sw01 ∷ []) (Sw01 ∷ CK30 ∷ []) (wl0161 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw12 ∷ Sb2-0-3-1 ∷ []) (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q14 : Ws → Eqn
  q14 c4 = eqn (CK30 ∷ Sw12 ∷ []) (Sw12 ∷ CK30 ∷ []) (wl0159 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (tr04 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-DB4K1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12-S1-S1-S1 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (tr03 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (wp0468 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-F1-rel-269-rhs c4)

-- F1 rel-269: 460 steps
lem-F1-rel-269 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-rel-269 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 3 (q1 c4) ∷
   re 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   re 3 5 (Sb1-0-42-3 ∷ []) ∷
   re 1 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) ∷
   rw⁻ 3 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   re 2 3 (CK40 ∷ []) ∷
   re 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 4 (q8 c4) ∷
   re 3 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 7 (q9 c4) ∷
   rw⁻ 6 (q10 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   re 2 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   re 3 3 (CK40 ∷ []) ∷
   re 1 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 5 (q9 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   re 2 5 (Sb2-0-41-3 ∷ []) ∷
   rw 2 (q15 c4) ∷
   re 2 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 1 (q13 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 3 (q13 c4) ∷
   re 1 3 (CK40 ∷ []) ∷
   re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 2 (q12 c4) ∷
   rw 3 (q10 c4) ∷
   rw 4 (q11 c4) ∷
   rw 5 (q10 c4) ∷
   rw 6 (q9 c4) ∷
   re 2 5 (Sb1-0-42-3 ∷ []) ∷
   re 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 3 (q12 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q10 c4) ∷
   rw 7 (q9 c4) ∷
   re 3 5 (Sb1-0-42-3 ∷ []) ∷
   re 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 4 (q12 c4) ∷
   rw 5 (q10 c4) ∷
   rw 6 (q11 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q9 c4) ∷
   re 4 5 (Sb1-0-42-3 ∷ []) ∷
   re 6 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 5 (q12 c4) ∷
   rw 6 (q10 c4) ∷
   rw 7 (q11 c4) ∷
   rw 8 (q10 c4) ∷
   rw 9 (q9 c4) ∷
   re 5 5 (Sb1-0-42-3 ∷ []) ∷
   re 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 6 (q12 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q11 c4) ∷
   rw 9 (q10 c4) ∷
   rw 10 (q9 c4) ∷
   re 6 5 (Sb1-0-42-3 ∷ []) ∷
   re 8 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 7 (q12 c4) ∷
   rw 8 (q10 c4) ∷
   rw 9 (q11 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q9 c4) ∷
   re 7 5 (Sb1-0-42-3 ∷ []) ∷
   re 9 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 8 (q12 c4) ∷
   rw 9 (q10 c4) ∷
   rw 10 (q11 c4) ∷
   rw 11 (q10 c4) ∷
   rw 12 (q9 c4) ∷
   re 8 5 (Sb1-0-42-3 ∷ []) ∷
   re 10 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 9 (q12 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q9 c4) ∷
   re 9 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 10 (q16 c4) ∷
   rw 11 (q17 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   re 16 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 15 (q12 c4) ∷
   rw 16 (q10 c4) ∷
   rw 17 (q11 c4) ∷
   rw 18 (q10 c4) ∷
   rw 19 (q9 c4) ∷
   re 15 5 (Sb1-0-42-3 ∷ []) ∷
   re 17 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 16 (q13 c4) ∷
   rw⁻ 17 (q14 c4) ∷
   rw 18 (q13 c4) ∷
   re 16 3 (CK40 ∷ []) ∷
   re 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 17 (q12 c4) ∷
   rw 18 (q10 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q10 c4) ∷
   rw 21 (q9 c4) ∷
   re 17 5 (Sb1-0-42-3 ∷ []) ∷
   re 19 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 18 (q13 c4) ∷
   rw⁻ 19 (q14 c4) ∷
   rw 20 (q13 c4) ∷
   re 18 3 (CK40 ∷ []) ∷
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 19 (q12 c4) ∷
   rw 20 (q10 c4) ∷
   rw 21 (q11 c4) ∷
   rw 22 (q10 c4) ∷
   rw 23 (q9 c4) ∷
   re 19 5 (Sb1-0-42-3 ∷ []) ∷
   re 21 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 20 (q13 c4) ∷
   rw⁻ 21 (q18 c4) ∷
   rw 22 (q13 c4) ∷
   re 20 3 (CS04 ∷ []) ∷
   re 22 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 21 (q13 c4) ∷
   rw⁻ 22 (q18 c4) ∷
   rw 23 (q13 c4) ∷
   re 21 3 (CS04 ∷ []) ∷
   re 23 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 22 (q13 c4) ∷
   rw⁻ 23 (q18 c4) ∷
   rw 24 (q13 c4) ∷
   re 22 3 (CS04 ∷ []) ∷
   re 24 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 23 (q13 c4) ∷
   rw⁻ 24 (q18 c4) ∷
   rw 25 (q13 c4) ∷
   re 23 3 (CS04 ∷ []) ∷
   re 25 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 24 (q13 c4) ∷
   rw⁻ 25 (q18 c4) ∷
   rw 26 (q13 c4) ∷
   re 24 3 (CS04 ∷ []) ∷
   re 26 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 25 (q13 c4) ∷
   rw⁻ 26 (q18 c4) ∷
   rw 27 (q13 c4) ∷
   re 25 3 (CS04 ∷ []) ∷
   re 27 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 26 (q13 c4) ∷
   rw⁻ 27 (q18 c4) ∷
   rw 28 (q13 c4) ∷
   re 26 3 (CS04 ∷ []) ∷
   re 28 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 27 (q13 c4) ∷
   rw⁻ 28 (q18 c4) ∷
   rw 29 (q13 c4) ∷
   re 27 3 (CS04 ∷ []) ∷
   re 29 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 28 (q13 c4) ∷
   rw⁻ 29 (q18 c4) ∷
   rw 30 (q13 c4) ∷
   re 28 3 (CS04 ∷ []) ∷
   rw 29 (q17 c4) ∷
   rw⁻ 30 (q16 c4) ∷
   rw⁻ 31 (q16 c4) ∷
   rw⁻ 32 (q16 c4) ∷
   re 34 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 33 (q12 c4) ∷
   rw 34 (q10 c4) ∷
   rw 35 (q11 c4) ∷
   rw 36 (q10 c4) ∷
   rw 37 (q9 c4) ∷
   re 33 5 (Sb1-0-42-3 ∷ []) ∷
   re 35 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 34 (q13 c4) ∷
   rw⁻ 35 (q14 c4) ∷
   rw 36 (q13 c4) ∷
   re 34 3 (CK40 ∷ []) ∷
   re 36 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 35 (q12 c4) ∷
   rw 36 (q10 c4) ∷
   rw 37 (q11 c4) ∷
   rw 38 (q10 c4) ∷
   rw 39 (q9 c4) ∷
   re 35 5 (Sb1-0-42-3 ∷ []) ∷
   re 37 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 36 (q13 c4) ∷
   rw⁻ 37 (q14 c4) ∷
   rw 38 (q13 c4) ∷
   re 36 3 (CK40 ∷ []) ∷
   re 38 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 37 (q12 c4) ∷
   rw 38 (q10 c4) ∷
   rw 39 (q11 c4) ∷
   rw 40 (q10 c4) ∷
   rw 41 (q9 c4) ∷
   re 37 5 (Sb1-0-42-3 ∷ []) ∷
   re 39 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 38 (q12 c4) ∷
   rw 39 (q10 c4) ∷
   rw 40 (q11 c4) ∷
   rw 41 (q10 c4) ∷
   rw 42 (q9 c4) ∷
   re 38 5 (Sb1-0-42-3 ∷ []) ∷
   re 40 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 39 (q12 c4) ∷
   rw 40 (q10 c4) ∷
   rw 41 (q11 c4) ∷
   rw 42 (q10 c4) ∷
   rw 43 (q9 c4) ∷
   re 39 5 (Sb1-0-42-3 ∷ []) ∷
   re 41 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 40 (q13 c4) ∷
   rw⁻ 41 (q18 c4) ∷
   rw 42 (q13 c4) ∷
   re 40 3 (CS04 ∷ []) ∷
   re 42 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 41 (q13 c4) ∷
   rw⁻ 42 (q18 c4) ∷
   rw 43 (q13 c4) ∷
   re 41 3 (CS04 ∷ []) ∷
   re 43 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 42 (q13 c4) ∷
   rw⁻ 43 (q18 c4) ∷
   rw 44 (q13 c4) ∷
   re 42 3 (CS04 ∷ []) ∷
   rw 43 (q8 c4) ∷
   re 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 0 (q6 c4) ∷
   rw⁻ 1 (q7 c4) ∷
   rw 2 (q6 c4) ∷
   re 0 3 (CK41 ∷ []) ∷
   re 2 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw 4 (q3 c4) ∷
   rw 5 (q2 c4) ∷
   re 1 5 (Sb0-1-42-3 ∷ []) ∷
   re 3 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 2 (q5 c4) ∷
   rw 3 (q3 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q3 c4) ∷
   rw 6 (q2 c4) ∷
   re 2 5 (Sb0-1-42-3 ∷ []) ∷
   re 4 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 3 (q5 c4) ∷
   rw 4 (q3 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q3 c4) ∷
   rw 7 (q2 c4) ∷
   re 3 5 (Sb0-1-42-3 ∷ []) ∷
   re 5 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q3 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q3 c4) ∷
   rw 8 (q2 c4) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   re 6 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q3 c4) ∷
   rw 7 (q4 c4) ∷
   rw 8 (q3 c4) ∷
   rw 9 (q2 c4) ∷
   re 5 5 (Sb0-1-42-3 ∷ []) ∷
   re 7 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q3 c4) ∷
   rw 8 (q4 c4) ∷
   rw 9 (q3 c4) ∷
   rw 10 (q2 c4) ∷
   re 6 5 (Sb0-1-42-3 ∷ []) ∷
   re 8 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q3 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q3 c4) ∷
   rw 11 (q2 c4) ∷
   re 7 5 (Sb0-1-42-3 ∷ []) ∷
   re 9 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q3 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q3 c4) ∷
   rw 12 (q2 c4) ∷
   re 8 5 (Sb0-1-42-3 ∷ []) ∷
   rw 9 (q19 c4) ∷
   rw 10 (q20 c4) ∷
   rw 11 (q19 c4) ∷
   rw 12 (q19 c4) ∷
   rw 13 (q19 c4) ∷
   re 15 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 14 (q5 c4) ∷
   rw 15 (q3 c4) ∷
   rw 16 (q4 c4) ∷
   rw 17 (q3 c4) ∷
   rw 18 (q2 c4) ∷
   re 14 5 (Sb0-1-42-3 ∷ []) ∷
   re 16 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 15 (q6 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw 17 (q6 c4) ∷
   re 15 3 (CK41 ∷ []) ∷
   re 17 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 16 (q5 c4) ∷
   rw 17 (q3 c4) ∷
   rw 18 (q4 c4) ∷
   rw 19 (q3 c4) ∷
   rw 20 (q2 c4) ∷
   re 16 5 (Sb0-1-42-3 ∷ []) ∷
   re 18 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 17 (q6 c4) ∷
   rw⁻ 18 (q7 c4) ∷
   rw 19 (q6 c4) ∷
   re 17 3 (CK41 ∷ []) ∷
   re 19 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 18 (q5 c4) ∷
   rw 19 (q3 c4) ∷
   rw 20 (q4 c4) ∷
   rw 21 (q3 c4) ∷
   rw 22 (q2 c4) ∷
   re 18 5 (Sb0-1-42-3 ∷ []) ∷
   re 20 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 19 (q6 c4) ∷
   rw⁻ 20 (q21 c4) ∷
   rw 21 (q6 c4) ∷
   re 19 3 (CS14 ∷ []) ∷
   re 21 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 20 (q6 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw 22 (q6 c4) ∷
   re 20 3 (CS14 ∷ []) ∷
   re 22 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 21 (q6 c4) ∷
   rw⁻ 22 (q21 c4) ∷
   rw 23 (q6 c4) ∷
   re 21 3 (CS14 ∷ []) ∷
   re 23 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 22 (q6 c4) ∷
   rw⁻ 23 (q21 c4) ∷
   rw 24 (q6 c4) ∷
   re 22 3 (CS14 ∷ []) ∷
   re 24 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 23 (q6 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw 25 (q6 c4) ∷
   re 23 3 (CS14 ∷ []) ∷
   re 25 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 24 (q6 c4) ∷
   rw⁻ 25 (q21 c4) ∷
   rw 26 (q6 c4) ∷
   re 24 3 (CS14 ∷ []) ∷
   re 26 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 25 (q6 c4) ∷
   rw⁻ 26 (q21 c4) ∷
   rw 27 (q6 c4) ∷
   re 25 3 (CS14 ∷ []) ∷
   re 27 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 26 (q6 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw 28 (q6 c4) ∷
   re 26 3 (CS14 ∷ []) ∷
   re 28 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 27 (q6 c4) ∷
   rw⁻ 28 (q21 c4) ∷
   rw 29 (q6 c4) ∷
   re 27 3 (CS14 ∷ []) ∷
   rw 28 (q20 c4) ∷
   rw 29 (q19 c4) ∷
   rw 30 (q19 c4) ∷
   rw 31 (q19 c4) ∷
   re 33 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 32 (q5 c4) ∷
   rw 33 (q3 c4) ∷
   rw 34 (q4 c4) ∷
   rw 35 (q3 c4) ∷
   rw 36 (q2 c4) ∷
   re 32 5 (Sb0-1-42-3 ∷ []) ∷
   re 34 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 33 (q6 c4) ∷
   rw⁻ 34 (q7 c4) ∷
   rw 35 (q6 c4) ∷
   re 33 3 (CK41 ∷ []) ∷
   re 35 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 34 (q5 c4) ∷
   rw 35 (q3 c4) ∷
   rw 36 (q4 c4) ∷
   rw 37 (q3 c4) ∷
   rw 38 (q2 c4) ∷
   re 34 5 (Sb0-1-42-3 ∷ []) ∷
   re 36 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 35 (q6 c4) ∷
   rw⁻ 36 (q7 c4) ∷
   rw 37 (q6 c4) ∷
   re 35 3 (CK41 ∷ []) ∷
   re 37 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 36 (q5 c4) ∷
   rw 37 (q3 c4) ∷
   rw 38 (q4 c4) ∷
   rw 39 (q3 c4) ∷
   rw 40 (q2 c4) ∷
   re 36 5 (Sb0-1-42-3 ∷ []) ∷
   re 38 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 37 (q5 c4) ∷
   rw 38 (q3 c4) ∷
   rw 39 (q4 c4) ∷
   rw 40 (q3 c4) ∷
   rw 41 (q2 c4) ∷
   re 37 5 (Sb0-1-42-3 ∷ []) ∷
   re 39 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 38 (q5 c4) ∷
   rw 39 (q3 c4) ∷
   rw 40 (q4 c4) ∷
   rw 41 (q3 c4) ∷
   rw 42 (q2 c4) ∷
   re 38 5 (Sb0-1-42-3 ∷ []) ∷
   re 40 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 39 (q6 c4) ∷
   rw⁻ 40 (q21 c4) ∷
   rw 41 (q6 c4) ∷
   re 39 3 (CS14 ∷ []) ∷
   re 41 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 40 (q6 c4) ∷
   rw⁻ 41 (q21 c4) ∷
   rw 42 (q6 c4) ∷
   re 40 3 (CS14 ∷ []) ∷
   re 42 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 41 (q6 c4) ∷
   rw⁻ 42 (q21 c4) ∷
   rw 43 (q6 c4) ∷
   re 41 3 (CS14 ∷ []) ∷
   rw 42 (q1 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   rw 42 (q23 c4) ∷
   rw⁻ 42 (q24 c4) ∷
   rw⁻ 0 (q25 c4) ∷
   rw⁻ 0 (q26 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ []) (lem-F5-CS01 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl0886 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (wp0462 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣iIᵖ1 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4))

-- split4[S0 iI S0 S0 S0 CS01 K1 CS01 K1 CS01]: 55 steps
lem-split4S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 : Ws → ⟪ (S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-split4S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 c4 = derive (S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 9 (q27 c4) ∷
   rw 8 (q28 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 6 (q28 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   rw 4 (q29 c4) ∷
   rw 3 (q29 c4) ∷
   rw 2 (q29 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw 0 (q29 c4) ∷
   rw 3 (q31 c4) ∷
   rw 7 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw 11 (q33 c4) ∷
   rw 10 (q32 c4) ∷
   rw 9 (q33 c4) ∷
   rw 15 (q33 c4) ∷
   rw 14 (q33 c4) ∷
   rw 13 (q32 c4) ∷
   rw 12 (q33 c4) ∷
   rw⁻ 19 (q34 c4) ∷
   rw⁻ 18 (q34 c4) ∷
   rw⁻ 17 (q34 c4) ∷
   rw⁻ 16 (q35 c4) ∷
   rw⁻ 15 (q34 c4) ∷
   rw⁻ 23 (q36 c4) ∷
   rw 22 (q37 c4) ∷
   rw 21 (q37 c4) ∷
   rw 20 (q37 c4) ∷
   rw 19 (q38 c4) ∷
   rw 18 (q37 c4) ∷
   rw⁻ 27 (q39 c4) ∷
   rw⁻ 26 (q40 c4) ∷
   rw⁻ 25 (q34 c4) ∷
   rw⁻ 24 (q34 c4) ∷
   rw⁻ 23 (q34 c4) ∷
   rw⁻ 22 (q35 c4) ∷
   rw⁻ 21 (q34 c4) ∷
   rw⁻ 31 (q36 c4) ∷
   rw 30 (q41 c4) ∷
   rw⁻ 29 (q36 c4) ∷
   rw 28 (q37 c4) ∷
   rw 27 (q37 c4) ∷
   rw 26 (q37 c4) ∷
   rw 25 (q38 c4) ∷
   rw 24 (q37 c4) ∷
   rw⁻ 35 (q39 c4) ∷
   rw⁻ 34 (q40 c4) ∷
   rw⁻ 33 (q39 c4) ∷
   rw⁻ 32 (q40 c4) ∷
   rw⁻ 31 (q34 c4) ∷
   rw⁻ 30 (q34 c4) ∷
   rw⁻ 29 (q34 c4) ∷
   rw⁻ 28 (q35 c4) ∷
   rw⁻ 27 (q34 c4) ∷ []) Eq.refl

-- split4[iI S0 S0 S0 CS01 K1 CS01 K1 CS01]: 45 steps
lem-split4iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 : Ws → ⟪ (ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-split4iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 c4 = derive (ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 8 (q27 c4) ∷
   rw 7 (q28 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw 5 (q28 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   rw 3 (q29 c4) ∷
   rw 2 (q29 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 0 (q30 c4) ∷
   rw 3 (q32 c4) ∷
   rw 7 (q33 c4) ∷
   rw 6 (q32 c4) ∷
   rw 11 (q33 c4) ∷
   rw 10 (q33 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 15 (q34 c4) ∷
   rw⁻ 14 (q34 c4) ∷
   rw⁻ 13 (q34 c4) ∷
   rw⁻ 12 (q35 c4) ∷
   rw⁻ 19 (q36 c4) ∷
   rw 18 (q37 c4) ∷
   rw 17 (q37 c4) ∷
   rw 16 (q37 c4) ∷
   rw 15 (q38 c4) ∷
   rw⁻ 23 (q39 c4) ∷
   rw⁻ 22 (q40 c4) ∷
   rw⁻ 21 (q34 c4) ∷
   rw⁻ 20 (q34 c4) ∷
   rw⁻ 19 (q34 c4) ∷
   rw⁻ 18 (q35 c4) ∷
   rw⁻ 27 (q36 c4) ∷
   rw 26 (q41 c4) ∷
   rw⁻ 25 (q36 c4) ∷
   rw 24 (q37 c4) ∷
   rw 23 (q37 c4) ∷
   rw 22 (q37 c4) ∷
   rw 21 (q38 c4) ∷
   rw⁻ 31 (q39 c4) ∷
   rw⁻ 30 (q40 c4) ∷
   rw⁻ 29 (q39 c4) ∷
   rw⁻ 28 (q40 c4) ∷
   rw⁻ 27 (q34 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw⁻ 25 (q34 c4) ∷
   rw⁻ 24 (q35 c4) ∷ []) Eq.refl
