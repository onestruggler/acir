{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D200 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0008 ; wl0010 ; wl0011 ; wl0015 ; wl0017 ; wl0061 ; wl0064 ; wl0159 ; wl0160 ; wl0161 ; wl0162 ; wl0163 ; wl0164 ; wl0900 ; wl0901 ; wl0902 ; wl0903 ; wl0904 ; wl0905 ; wl0906 ; wl0907 ; wl0908 ; wl0909 ; wp0469 ; wp0470 ; wp0471 ; wp0472)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-F1-comm-CS-S0 ; lem-F1-comm-CS-S1 ; lem-F1-order-CS)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F1-X-CS0 ; lem-F1-X-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-F1-CS-K0)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-F1-CS-K1)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-F1-comm-CS-CS)
open import Examples.Groups.Clifford+CS.Five.D.D196 using (lem-DB4K1-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1)
open import Examples.Groups.Clifford+CS.Five.D.D198 using (lem-DB4K1-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1)
open import Examples.Groups.Clifford+CS.Five.D.D199 using (lem-F1-rel-272-rhs)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-CS04 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-1-SBOX⟨3·0·41·2⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩ ; lem-nat-2-SBOX⟨1·0·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-2-CS04)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-SBOX⟨0·2·43·1⟩ ; lem-nat-0-SBOX⟨1·2·43·0⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-SBOX⟨1·0·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-SBOX⟨0·1·43·2⟩ ; lem-nat-0-SBOX⟨3·0·42·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-CK40 ; lem-nat-0-CK41 ; lem-nat-0-SBOX⟨1·0·43·2⟩ ; lem-nat-1-CK40 ; lem-nat-2-CK40)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-SBOX⟨3·0·42·1⟩ ; lem-nat-2-SBOX⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨3·0·41·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-0-SBOX⟨3·1·42·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.TR using (tr07 ; tr08 ; tr09)

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
  q15 c4 = eqn (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CK40 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (tr09 c4)
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
  q22 c4 = eqn (CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-DB4K1-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn [] (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (tr08 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (tr07 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-DB4K1-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (wp0469 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (lem-F1-rel-272-rhs c4)

-- F1 rel-272: 349 steps
lem-F1-rel-272 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-rel-272 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 5 (q1 c4) ∷
   re 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 8 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   re 5 5 (Sb1-0-42-3 ∷ []) ∷
   re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   re 4 5 (Sb1-0-42-3 ∷ []) ∷
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
   rw⁻ 6 (q8 c4) ∷
   re 5 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 9 (q9 c4) ∷
   rw⁻ 8 (q10 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw⁻ 6 (q10 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   re 4 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   re 5 5 (Sb2-0-41-3 ∷ []) ∷
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
   rw⁻ 2 (q16 c4) ∷
   rw 3 (q17 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   re 8 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 7 (q12 c4) ∷
   rw 8 (q10 c4) ∷
   rw 9 (q11 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q9 c4) ∷
   re 7 5 (Sb1-0-42-3 ∷ []) ∷
   re 9 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 8 (q13 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw 10 (q13 c4) ∷
   re 8 3 (CK40 ∷ []) ∷
   re 10 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 9 (q12 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q9 c4) ∷
   re 9 5 (Sb1-0-42-3 ∷ []) ∷
   re 11 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 10 (q13 c4) ∷
   rw⁻ 11 (q14 c4) ∷
   rw 12 (q13 c4) ∷
   re 10 3 (CK40 ∷ []) ∷
   re 12 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 11 (q12 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q9 c4) ∷
   re 11 5 (Sb1-0-42-3 ∷ []) ∷
   re 13 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 12 (q13 c4) ∷
   rw⁻ 13 (q18 c4) ∷
   rw 14 (q13 c4) ∷
   re 12 3 (CS04 ∷ []) ∷
   re 14 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 13 (q13 c4) ∷
   rw⁻ 14 (q18 c4) ∷
   rw 15 (q13 c4) ∷
   re 13 3 (CS04 ∷ []) ∷
   re 15 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 14 (q13 c4) ∷
   rw⁻ 15 (q18 c4) ∷
   rw 16 (q13 c4) ∷
   re 14 3 (CS04 ∷ []) ∷
   re 16 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 15 (q13 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw 17 (q13 c4) ∷
   re 15 3 (CS04 ∷ []) ∷
   re 17 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 16 (q13 c4) ∷
   rw⁻ 17 (q18 c4) ∷
   rw 18 (q13 c4) ∷
   re 16 3 (CS04 ∷ []) ∷
   re 18 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 17 (q13 c4) ∷
   rw⁻ 18 (q18 c4) ∷
   rw 19 (q13 c4) ∷
   re 17 3 (CS04 ∷ []) ∷
   re 19 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 18 (q13 c4) ∷
   rw⁻ 19 (q18 c4) ∷
   rw 20 (q13 c4) ∷
   re 18 3 (CS04 ∷ []) ∷
   re 20 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 19 (q13 c4) ∷
   rw⁻ 20 (q18 c4) ∷
   rw 21 (q13 c4) ∷
   re 19 3 (CS04 ∷ []) ∷
   re 21 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 20 (q13 c4) ∷
   rw⁻ 21 (q18 c4) ∷
   rw 22 (q13 c4) ∷
   re 20 3 (CS04 ∷ []) ∷
   rw 21 (q17 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 23 (q16 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   re 26 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 25 (q12 c4) ∷
   rw 26 (q10 c4) ∷
   rw 27 (q11 c4) ∷
   rw 28 (q10 c4) ∷
   rw 29 (q9 c4) ∷
   re 25 5 (Sb1-0-42-3 ∷ []) ∷
   re 27 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 26 (q13 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw 28 (q13 c4) ∷
   re 26 3 (CK40 ∷ []) ∷
   re 28 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 27 (q12 c4) ∷
   rw 28 (q10 c4) ∷
   rw 29 (q11 c4) ∷
   rw 30 (q10 c4) ∷
   rw 31 (q9 c4) ∷
   re 27 5 (Sb1-0-42-3 ∷ []) ∷
   re 29 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 28 (q13 c4) ∷
   rw⁻ 29 (q14 c4) ∷
   rw 30 (q13 c4) ∷
   re 28 3 (CK40 ∷ []) ∷
   re 30 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 29 (q12 c4) ∷
   rw 30 (q10 c4) ∷
   rw 31 (q11 c4) ∷
   rw 32 (q10 c4) ∷
   rw 33 (q9 c4) ∷
   re 29 5 (Sb1-0-42-3 ∷ []) ∷
   re 31 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 30 (q13 c4) ∷
   rw⁻ 31 (q18 c4) ∷
   rw 32 (q13 c4) ∷
   re 30 3 (CS04 ∷ []) ∷
   re 32 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 31 (q13 c4) ∷
   rw⁻ 32 (q18 c4) ∷
   rw 33 (q13 c4) ∷
   re 31 3 (CS04 ∷ []) ∷
   re 33 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 32 (q13 c4) ∷
   rw⁻ 33 (q18 c4) ∷
   rw 34 (q13 c4) ∷
   re 32 3 (CS04 ∷ []) ∷
   rw 33 (q8 c4) ∷
   re 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 0 (q6 c4) ∷
   rw⁻ 1 (q7 c4) ∷
   rw 2 (q6 c4) ∷
   re 0 3 (CK41 ∷ []) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   re 7 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q3 c4) ∷
   rw 8 (q4 c4) ∷
   rw 9 (q3 c4) ∷
   rw 10 (q2 c4) ∷
   re 6 5 (Sb0-1-42-3 ∷ []) ∷
   re 8 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw 9 (q6 c4) ∷
   re 7 3 (CK41 ∷ []) ∷
   re 9 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q3 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q3 c4) ∷
   rw 12 (q2 c4) ∷
   re 8 5 (Sb0-1-42-3 ∷ []) ∷
   re 10 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   rw 11 (q6 c4) ∷
   re 9 3 (CK41 ∷ []) ∷
   re 11 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q3 c4) ∷
   rw 12 (q4 c4) ∷
   rw 13 (q3 c4) ∷
   rw 14 (q2 c4) ∷
   re 10 5 (Sb0-1-42-3 ∷ []) ∷
   re 12 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 11 (q6 c4) ∷
   rw⁻ 12 (q21 c4) ∷
   rw 13 (q6 c4) ∷
   re 11 3 (CS14 ∷ []) ∷
   re 13 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 12 (q6 c4) ∷
   rw⁻ 13 (q21 c4) ∷
   rw 14 (q6 c4) ∷
   re 12 3 (CS14 ∷ []) ∷
   re 14 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 13 (q6 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw 15 (q6 c4) ∷
   re 13 3 (CS14 ∷ []) ∷
   re 15 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 14 (q6 c4) ∷
   rw⁻ 15 (q21 c4) ∷
   rw 16 (q6 c4) ∷
   re 14 3 (CS14 ∷ []) ∷
   re 16 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 15 (q6 c4) ∷
   rw⁻ 16 (q21 c4) ∷
   rw 17 (q6 c4) ∷
   re 15 3 (CS14 ∷ []) ∷
   re 17 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 16 (q6 c4) ∷
   rw⁻ 17 (q21 c4) ∷
   rw 18 (q6 c4) ∷
   re 16 3 (CS14 ∷ []) ∷
   re 18 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 17 (q6 c4) ∷
   rw⁻ 18 (q21 c4) ∷
   rw 19 (q6 c4) ∷
   re 17 3 (CS14 ∷ []) ∷
   re 19 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 18 (q6 c4) ∷
   rw⁻ 19 (q21 c4) ∷
   rw 20 (q6 c4) ∷
   re 18 3 (CS14 ∷ []) ∷
   re 20 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 19 (q6 c4) ∷
   rw⁻ 20 (q21 c4) ∷
   rw 21 (q6 c4) ∷
   re 19 3 (CS14 ∷ []) ∷
   rw 20 (q20 c4) ∷
   rw 21 (q19 c4) ∷
   rw 22 (q19 c4) ∷
   rw 23 (q19 c4) ∷
   re 25 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 24 (q5 c4) ∷
   rw 25 (q3 c4) ∷
   rw 26 (q4 c4) ∷
   rw 27 (q3 c4) ∷
   rw 28 (q2 c4) ∷
   re 24 5 (Sb0-1-42-3 ∷ []) ∷
   re 26 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 25 (q6 c4) ∷
   rw⁻ 26 (q7 c4) ∷
   rw 27 (q6 c4) ∷
   re 25 3 (CK41 ∷ []) ∷
   re 27 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 26 (q5 c4) ∷
   rw 27 (q3 c4) ∷
   rw 28 (q4 c4) ∷
   rw 29 (q3 c4) ∷
   rw 30 (q2 c4) ∷
   re 26 5 (Sb0-1-42-3 ∷ []) ∷
   re 28 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 27 (q6 c4) ∷
   rw⁻ 28 (q7 c4) ∷
   rw 29 (q6 c4) ∷
   re 27 3 (CK41 ∷ []) ∷
   re 29 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 28 (q5 c4) ∷
   rw 29 (q3 c4) ∷
   rw 30 (q4 c4) ∷
   rw 31 (q3 c4) ∷
   rw 32 (q2 c4) ∷
   re 28 5 (Sb0-1-42-3 ∷ []) ∷
   re 30 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 29 (q6 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw 31 (q6 c4) ∷
   re 29 3 (CS14 ∷ []) ∷
   re 31 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 30 (q6 c4) ∷
   rw⁻ 31 (q21 c4) ∷
   rw 32 (q6 c4) ∷
   re 30 3 (CS14 ∷ []) ∷
   re 32 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 31 (q6 c4) ∷
   rw⁻ 32 (q21 c4) ∷
   rw 33 (q6 c4) ∷
   re 31 3 (CS14 ∷ []) ∷
   rw 32 (q1 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   rw 35 (q23 c4) ∷
   rw 33 (q24 c4) ∷
   rw⁻ 33 (q25 c4) ∷
   rw⁻ 0 (q26 c4) ∷
   rw⁻ 0 (q27 c4) ∷ []) Eq.refl

private
  q28 : Ws → Eqn
  q28 c4 = eqn (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) [] (wl0900 (lit c4))

-- tr order-I at 3: 1 steps
lem-tr-order-I-at-3 : Ws → ⟪ (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-I-at-3 c4 = derive (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) []
  (rw 0 (q28 c4) ∷ []) Eq.refl

-- tr order-I at 4: 1 steps
lem-tr-order-I-at-4 : Ws → ⟪ (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-I-at-4 c4 = derive (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) []
  (rw 0 (q28 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = eqn (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) [] (wl0902 (lit c4))

-- tr order-S at 2: 1 steps
lem-tr-order-S-at-2 : Ws → ⟪ (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-S-at-2 c4 = derive (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) []
  (rw 0 (q29 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = eqn (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) [] (wl0903 (lit c4))

-- tr order-S at 3: 1 steps
lem-tr-order-S-at-3 : Ws → ⟪ (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-S-at-3 c4 = derive (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) []
  (rw 0 (q30 c4) ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = eqn (CK42 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) (wl0905 (lit c4))

-- tr order-K at 2: 1 steps
lem-tr-order-K-at-2 : Ws → ⟪ (CK42 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-tr-order-K-at-2 c4 = derive (CK42 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  (rw 0 (q31 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = eqn (CK43 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) (wl0906 (lit c4))

-- tr order-K at 3: 1 steps
lem-tr-order-K-at-3 : Ws → ⟪ (CK43 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-tr-order-K-at-3 c4 = derive (CK43 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  (rw 0 (q32 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = eqn (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) (wl0908 (lit c4))

-- tr order-SK at 2: 1 steps
lem-tr-order-SK-at-2 : Ws → ⟪ (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-tr-order-SK-at-2 c4 = derive (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  (rw 0 (q33 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = eqn (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) (wl0909 (lit c4))

-- tr order-SK at 3: 1 steps
lem-tr-order-SK-at-3 : Ws → ⟪ (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-tr-order-SK-at-3 c4 = derive (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  (rw 0 (q34 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) [] (lem-F1-order-CS c4)

-- F1 order-CS @1221: 7 steps
lem-F1-order-CS-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS-at1221 c4 = derive (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ []) []
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q35 c4) ∷
   rw 2 (q35 c4) ∷
   rw 3 (q35 c4) ∷
   rw 4 (q35 c4) ∷
   rw 1 (q36 c4) ∷
   rw 0 (q8 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ []) [] (lem-F1-order-CS-at1221 c4)

-- F1 order-CS @011220: 7 steps
lem-F1-order-CS-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS-at011220 c4 = derive (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) []
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q37 c4) ∷
   rw 3 (q37 c4) ∷
   rw 4 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) [] (lem-F1-order-CS-at011220 c4)

-- tr order-CS at 1: 1 steps
lem-tr-order-CS-at-1 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-CS-at-1 c4 = derive (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) []
  (rw 0 (q39 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (Sw23 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4))

-- F1 order-CS @132132: 7 steps
lem-F1-order-CS-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS-at132132 c4 = derive (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ []) []
  (rw⁻ 0 (q40 c4) ∷
   rw 1 (q41 c4) ∷
   rw 2 (q41 c4) ∷
   rw 3 (q41 c4) ∷
   rw 4 (q41 c4) ∷
   rw 1 (q38 c4) ∷
   rw 0 (q40 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = eqn (Sw01 ∷ Sb0-1-43-2 ∷ []) (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ []) [] (lem-F1-order-CS-at132132 c4)

-- F1 order-CS @01132032: 7 steps
lem-F1-order-CS-at01132032 : Ws → ⟪ (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS-at01132032 c4 = derive (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) []
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q42 c4) ∷
   rw 3 (q42 c4) ∷
   rw 4 (q42 c4) ∷
   rw 1 (q43 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) [] (lem-F1-order-CS-at01132032 c4)

-- F1 order-CS @02132031: 7 steps
lem-F1-order-CS-at02132031 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS-at02132031 c4 = derive (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) []
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q44 c4) ∷
   rw 3 (q44 c4) ∷
   rw 4 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 0 (q8 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) [] (lem-F1-order-CS-at02132031 c4)

-- tr order-CS at 2: 1 steps
lem-tr-order-CS-at-2 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-CS-at-2 c4 = derive (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) []
  (rw 0 (q46 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Sb2-0-41-3 ∷ CS04 ∷ []) (CS04 ∷ Sb2-0-41-3 ∷ []) (lem-F1-comm-CS-S0 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (Sw12 ∷ Sb2-0-41-3 ∷ []) (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4))

-- F1 comm-CS-S0 @1221: 7 steps
lem-F1-comm-CS-S0-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0-at1221 c4 = derive (Sb1-0-42-3 ∷ CS04 ∷ []) (CS04 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q35 c4) ∷
   rw 2 (q47 c4) ∷
   rw 1 (q48 c4) ∷
   rw 0 (q47 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (Sb1-0-42-3 ∷ CS04 ∷ []) (CS04 ∷ Sb1-0-42-3 ∷ []) (lem-F1-comm-CS-S0-at1221 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (Sw01 ∷ Sb1-0-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4))

-- F1 comm-CS-S0 @011220: 7 steps
lem-F1-comm-CS-S0-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0-at011220 c4 = derive (Sb0-1-42-3 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = eqn (Sb0-1-42-3 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-42-3 ∷ []) (lem-F1-comm-CS-S0-at011220 c4)

-- tr comm-CS-S0 at 1: 1 steps
lem-tr-comm-CS-S0-at-1 : Ws → ⟪ (Sb0-1-42-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-comm-CS-S0-at-1 c4 = derive (Sb0-1-42-3 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q54 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (Sw23 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4))

-- F1 comm-CS-S0 @132132: 7 steps
lem-F1-comm-CS-S0-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0-at132132 c4 = derive (Sb1-0-43-2 ∷ CS04 ∷ []) (CS04 ∷ Sb1-0-43-2 ∷ [])
  (rw⁻ 0 (q40 c4) ∷
   rw 1 (q41 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q51 c4) ∷
   rw 0 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q40 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (Sb1-0-43-2 ∷ CS04 ∷ []) (CS04 ∷ Sb1-0-43-2 ∷ []) (lem-F1-comm-CS-S0-at132132 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (Sw01 ∷ Sb1-0-43-2 ∷ []) (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4))

-- F1 comm-CS-S0 @01132032: 7 steps
lem-F1-comm-CS-S0-at01132032 : Ws → ⟪ (Sb0-1-43-2 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0-at01132032 c4 = derive (Sb0-1-43-2 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q50 c4) ∷
   rw 1 (q57 c4) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q58 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (Sb0-1-43-2 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-43-2 ∷ []) (lem-F1-comm-CS-S0-at01132032 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Sw12 ∷ Sb0-1-43-2 ∷ []) (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4))

-- F1 comm-CS-S0 @02132031: 7 steps
lem-F1-comm-CS-S0-at02132031 : Ws → ⟪ (Sb0-2-43-1 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0-at02132031 c4 = derive (Sb0-2-43-1 ∷ CS24 ∷ []) (CS24 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q44 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = eqn (Sb0-2-43-1 ∷ CS24 ∷ []) (CS24 ∷ Sb0-2-43-1 ∷ []) (lem-F1-comm-CS-S0-at02132031 c4)

-- tr comm-CS-S0 at 2: 1 steps
lem-tr-comm-CS-S0-at-2 : Ws → ⟪ (Sb0-2-43-1 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm-CS-S0-at-2 c4 = derive (Sb0-2-43-1 ∷ CS24 ∷ []) (CS24 ∷ Sb0-2-43-1 ∷ [])
  (rw 0 (q62 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (Sb2-0-41-3 ∷ CS14 ∷ []) (CS14 ∷ Sb2-0-41-3 ∷ []) (lem-F1-comm-CS-S1 c4)

-- F1 comm-CS-S1 @1221: 7 steps
lem-F1-comm-CS-S1-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1-at1221 c4 = derive (Sb1-0-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q35 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw 1 (q63 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = eqn (Sb1-0-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb1-0-42-3 ∷ []) (lem-F1-comm-CS-S1-at1221 c4)

-- F1 comm-CS-S1 @011220: 7 steps
lem-F1-comm-CS-S1-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1-at011220 c4 = derive (Sb0-1-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q19 c4) ∷
   rw 1 (q64 c4) ∷
   rw 0 (q19 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (Sb0-1-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-42-3 ∷ []) (lem-F1-comm-CS-S1-at011220 c4)

-- tr comm-CS-S1 at 1: 1 steps
lem-tr-comm-CS-S1-at-1 : Ws → ⟪ (Sb0-1-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-comm-CS-S1-at-1 c4 = derive (Sb0-1-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q65 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 (lit c4))

-- F1 comm-CS-S1 @132132: 7 steps
lem-F1-comm-CS-S1-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1-at132132 c4 = derive (Sb1-0-43-2 ∷ CS34 ∷ []) (CS34 ∷ Sb1-0-43-2 ∷ [])
  (rw⁻ 0 (q40 c4) ∷
   rw 1 (q41 c4) ∷
   rw⁻ 2 (q66 c4) ∷
   rw 1 (q64 c4) ∷
   rw⁻ 0 (q67 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q40 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q69 : Ws → Eqn
  q69 c4 = eqn (Sb1-0-43-2 ∷ CS34 ∷ []) (CS34 ∷ Sb1-0-43-2 ∷ []) (lem-F1-comm-CS-S1-at132132 c4)

-- F1 comm-CS-S1 @01132032: 7 steps
lem-F1-comm-CS-S1-at01132032 : Ws → ⟪ (Sb0-1-43-2 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1-at01132032 c4 = derive (Sb0-1-43-2 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q68 c4) ∷
   rw 1 (q69 c4) ∷
   rw 0 (q68 c4) ∷
   rw 1 (q58 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q71 : Ws → Eqn
  q71 c4 = eqn (Sb0-1-43-2 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-43-2 ∷ []) (lem-F1-comm-CS-S1-at01132032 c4)

-- F1 comm-CS-S1 @02132031: 7 steps
lem-F1-comm-CS-S1-at02132031 : Ws → ⟪ (Sb0-2-43-1 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1-at02132031 c4 = derive (Sb0-2-43-1 ∷ CS34 ∷ []) (CS34 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   rw 0 (q70 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (Sb0-2-43-1 ∷ CS34 ∷ []) (CS34 ∷ Sb0-2-43-1 ∷ []) (lem-F1-comm-CS-S1-at02132031 c4)

-- tr comm-CS-S1 at 2: 1 steps
lem-tr-comm-CS-S1-at-2 : Ws → ⟪ (Sb0-2-43-1 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm-CS-S1-at-2 c4 = derive (Sb0-2-43-1 ∷ CS34 ∷ []) (CS34 ∷ Sb0-2-43-1 ∷ [])
  (rw 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (Sw12 ∷ CK40 ∷ []) (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (lem-F1-X-CS0 c4)

-- F1 X-CS0 @1221: 18 steps
lem-F1-X-CS0-at1221 : Ws → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-F1-X-CS0-at1221 c4 = derive (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS24 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q47 c4) ∷
   rw 3 (q47 c4) ∷
   rw 4 (q73 c4) ∷
   rw 5 (q17 c4) ∷
   rw 6 (q35 c4) ∷
   rw 1 (q74 c4) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q49 c4) ∷
   rw 3 (q73 c4) ∷
   rw 4 (q47 c4) ∷
   rw 5 (q47 c4) ∷
   rw 6 (q73 c4) ∷
   rw 7 (q17 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw 9 (q8 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = eqn (Sw01 ∷ CK41 ∷ []) (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS24 ∷ []) (lem-F1-X-CS0-at1221 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (Sw01 ∷ CK40 ∷ []) (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4))

-- F1 X-CS0 @011220: 18 steps
lem-F1-X-CS0-at011220 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-F1-X-CS0-at011220 c4 = derive (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q50 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q75 c4) ∷
   rw 5 (q20 c4) ∷
   rw 6 (q37 c4) ∷
   rw 1 (q76 c4) ∷
   rw 0 (q53 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q53 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q52 c4) ∷
   rw 5 (q52 c4) ∷
   rw 6 (q77 c4) ∷
   rw 7 (q20 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q1 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = eqn (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (lem-F1-X-CS0-at011220 c4)

-- tr X-CS0 at 1: 1 steps
lem-tr-X-CS0-at-1 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-X-CS0-at-1 c4 = derive (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  (rw 0 (q78 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = eqn (Sw23 ∷ CK40 ∷ []) (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))

-- F1 X-CS0 @132132: 18 steps
lem-F1-X-CS0-at132132 : Ws → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-F1-X-CS0-at132132 c4 = derive (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS34 ∷ [])
  (rw⁻ 0 (q40 c4) ∷
   rw 1 (q79 c4) ∷
   rw 2 (q55 c4) ∷
   rw 3 (q55 c4) ∷
   rw 4 (q79 c4) ∷
   rw 5 (q80 c4) ∷
   rw 6 (q41 c4) ∷
   rw 1 (q76 c4) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q56 c4) ∷
   rw 3 (q79 c4) ∷
   rw 4 (q55 c4) ∷
   rw 5 (q55 c4) ∷
   rw 6 (q79 c4) ∷
   rw 7 (q80 c4) ∷
   rw⁻ 8 (q67 c4) ∷
   rw 9 (q40 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS34 ∷ []) (lem-F1-X-CS0-at132132 c4)

-- F1 X-CS0 @01132032: 18 steps
lem-F1-X-CS0-at01132032 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-F1-X-CS0-at01132032 c4 = derive (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS34 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q50 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q75 c4) ∷
   rw 5 (q20 c4) ∷
   rw 6 (q42 c4) ∷
   rw 1 (q81 c4) ∷
   rw 0 (q58 c4) ∷
   rw 1 (q58 c4) ∷
   rw 2 (q58 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q52 c4) ∷
   rw 5 (q52 c4) ∷
   rw 6 (q77 c4) ∷
   rw 7 (q20 c4) ∷
   rw 8 (q68 c4) ∷
   rw 9 (q1 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl0160 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS34 ∷ []) (lem-F1-X-CS0-at01132032 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (CK42 ∷ Sw12 ∷ []) (Sw12 ∷ CK41 ∷ []) (wl0164 (lit c4))

-- F1 X-CS0 @02132031: 18 steps
lem-F1-X-CS0-at02132031 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-F1-X-CS0-at02132031 c4 = derive (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw⁻ 1 (q82 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 5 (q17 c4) ∷
   rw 6 (q44 c4) ∷
   rw 1 (q83 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q61 c4) ∷
   rw⁻ 3 (q84 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 7 (q17 c4) ∷
   rw 8 (q70 c4) ∷
   rw 9 (q8 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (lem-F1-X-CS0-at02132031 c4)

-- tr X-CS0 at 2: 1 steps
lem-tr-X-CS0-at-2 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-X-CS0-at-2 c4 = derive (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  (rw 0 (q85 c4) ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = eqn (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (lem-F1-X-CS1 c4)

-- F1 X-CS1 @1221: 18 steps
lem-F1-X-CS1-at1221 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-F1-X-CS1-at1221 c4 = derive (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS04 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw⁻ 1 (q82 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 5 (q17 c4) ∷
   rw 6 (q35 c4) ∷
   rw 1 (q86 c4) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q49 c4) ∷
   rw⁻ 3 (q84 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 7 (q17 c4) ∷
   rw 8 (q47 c4) ∷
   rw 9 (q8 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))
  q88 : Ws → Eqn
  q88 c4 = eqn (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS04 ∷ []) (lem-F1-X-CS1-at1221 c4)

-- F1 X-CS1 @011220: 18 steps
lem-F1-X-CS1-at011220 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-F1-X-CS1-at011220 c4 = derive (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q87 c4) ∷
   rw 2 (q19 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q87 c4) ∷
   rw 5 (q20 c4) ∷
   rw 6 (q37 c4) ∷
   rw 1 (q88 c4) ∷
   rw 0 (q53 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q53 c4) ∷
   rw 3 (q87 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q87 c4) ∷
   rw 7 (q20 c4) ∷
   rw 8 (q52 c4) ∷
   rw 9 (q1 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = eqn (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (lem-F1-X-CS1-at011220 c4)

-- tr X-CS1 at 1: 1 steps
lem-tr-X-CS1-at-1 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-tr-X-CS1-at-1 c4 = derive (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  (rw 0 (q89 c4) ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl0162 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) (wl0163 (lit c4))

-- F1 X-CS1 @132132: 18 steps
lem-F1-X-CS1-at132132 : Ws → ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-F1-X-CS1-at132132 c4 = derive (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS04 ∷ [])
  (rw⁻ 0 (q40 c4) ∷
   rw⁻ 1 (q90 c4) ∷
   rw⁻ 2 (q66 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   rw⁻ 4 (q90 c4) ∷
   rw 5 (q80 c4) ∷
   rw 6 (q41 c4) ∷
   rw 1 (q88 c4) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q56 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   rw⁻ 5 (q67 c4) ∷
   rw⁻ 6 (q91 c4) ∷
   rw 7 (q80 c4) ∷
   rw 8 (q55 c4) ∷
   rw 9 (q40 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = eqn (Sw01 ∷ CK43 ∷ []) (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑))
  q93 : Ws → Eqn
  q93 c4 = eqn (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS04 ∷ []) (lem-F1-X-CS1-at132132 c4)

-- F1 X-CS1 @01132032: 18 steps
lem-F1-X-CS1-at01132032 : Ws → ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-F1-X-CS1-at01132032 c4 = derive (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS14 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q92 c4) ∷
   rw 2 (q68 c4) ∷
   rw 3 (q68 c4) ∷
   rw 4 (q92 c4) ∷
   rw 5 (q20 c4) ∷
   rw 6 (q42 c4) ∷
   rw 1 (q93 c4) ∷
   rw 0 (q58 c4) ∷
   rw 1 (q58 c4) ∷
   rw 2 (q58 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q68 c4) ∷
   rw 5 (q68 c4) ∷
   rw 6 (q92 c4) ∷
   rw 7 (q20 c4) ∷
   rw 8 (q52 c4) ∷
   rw 9 (q1 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))
  q95 : Ws → Eqn
  q95 c4 = eqn (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS14 ∷ []) (lem-F1-X-CS1-at01132032 c4)

-- F1 X-CS1 @02132031: 18 steps
lem-F1-X-CS1-at02132031 : Ws → ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-F1-X-CS1-at02132031 c4 = derive (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q70 c4) ∷
   rw 3 (q70 c4) ∷
   rw 4 (q94 c4) ∷
   rw 5 (q17 c4) ∷
   rw 6 (q44 c4) ∷
   rw 1 (q95 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q61 c4) ∷
   rw 3 (q94 c4) ∷
   rw 4 (q70 c4) ∷
   rw 5 (q70 c4) ∷
   rw 6 (q94 c4) ∷
   rw 7 (q17 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw 9 (q8 c4) ∷ []) Eq.refl

private
  q96 : Ws → Eqn
  q96 c4 = eqn (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (lem-F1-X-CS1-at02132031 c4)

-- tr X-CS1 at 2: 1 steps
lem-tr-X-CS1-at-2 : Ws → ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-X-CS1-at-2 c4 = derive (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  (rw 0 (q96 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = eqn (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0 c4)

-- F1 CS-K0 @1221: 13 steps
lem-F1-CS-K0-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-at1221 c4 = derive (Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q35 c4) ∷
   rw 2 (q73 c4) ∷
   rw 3 (q35 c4) ∷
   rw 4 (q73 c4) ∷
   rw 5 (q47 c4) ∷
   rw 1 (q97 c4) ∷
   rw 0 (q47 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q49 c4) ∷
   rw 3 (q73 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q8 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = eqn (Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ []) (lem-F1-CS-K0-at1221 c4)

-- F1 CS-K0 @011220: 13 steps
lem-F1-CS-K0-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-at011220 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q75 c4) ∷
   rw 3 (q37 c4) ∷
   rw 4 (q75 c4) ∷
   rw 5 (q50 c4) ∷
   rw 1 (q98 c4) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q53 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q53 c4) ∷
   rw 5 (q1 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = eqn (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (lem-F1-CS-K0-at011220 c4)

-- tr CS-K0 at 1: 1 steps
lem-tr-CS-K0-at-1 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-CS-K0-at-1 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q99 c4) ∷ []) Eq.refl

-- F1 CS-K0 @132132: 13 steps
lem-F1-CS-K0-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ CK40 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK40 ∷ Sb1-0-43-2 ∷ CK40 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-F1-CS-K0-at132132 c4 = derive (Sb1-0-43-2 ∷ CK40 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ CK40 ∷ Sb1-0-43-2 ∷ CK40 ∷ Sb1-0-43-2 ∷ [])
  (rw⁻ 0 (q40 c4) ∷
   rw 1 (q41 c4) ∷
   rw 2 (q79 c4) ∷
   rw 3 (q41 c4) ∷
   rw 4 (q79 c4) ∷
   rw 5 (q55 c4) ∷
   rw 1 (q98 c4) ∷
   rw 0 (q55 c4) ∷
   rw 1 (q79 c4) ∷
   rw 2 (q56 c4) ∷
   rw 3 (q79 c4) ∷
   rw 4 (q56 c4) ∷
   rw 5 (q40 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (Sb1-0-43-2 ∷ CK40 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ CK40 ∷ Sb1-0-43-2 ∷ CK40 ∷ Sb1-0-43-2 ∷ []) (lem-F1-CS-K0-at132132 c4)

-- F1 CS-K0 @01132032: 13 steps
lem-F1-CS-K0-at01132032 : Ws → ⟪ (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-CS-K0-at01132032 c4 = derive (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q75 c4) ∷
   rw 3 (q42 c4) ∷
   rw 4 (q75 c4) ∷
   rw 5 (q50 c4) ∷
   rw 1 (q100 c4) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q58 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q58 c4) ∷
   rw 5 (q1 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) (lem-F1-CS-K0-at01132032 c4)

-- F1 CS-K0 @02132031: 13 steps
lem-F1-CS-K0-at02132031 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-CS-K0-at02132031 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q44 c4) ∷
   rw⁻ 2 (q82 c4) ∷
   rw 3 (q44 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 1 (q101 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw⁻ 1 (q84 c4) ∷
   rw 2 (q61 c4) ∷
   rw⁻ 3 (q84 c4) ∷
   rw 4 (q61 c4) ∷
   rw 5 (q8 c4) ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (lem-F1-CS-K0-at02132031 c4)

-- tr CS-K0 at 2: 1 steps
lem-tr-CS-K0-at-2 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-CS-K0-at-2 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ [])
  (rw 0 (q102 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = eqn (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K1 c4)

-- F1 CS-K1 @1221: 13 steps
lem-F1-CS-K1-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-at1221 c4 = derive (Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q35 c4) ∷
   rw⁻ 2 (q82 c4) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 1 (q103 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw⁻ 1 (q84 c4) ∷
   rw 2 (q49 c4) ∷
   rw⁻ 3 (q84 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q8 c4) ∷ []) Eq.refl

private
  q104 : Ws → Eqn
  q104 c4 = eqn (Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ []) (lem-F1-CS-K1-at1221 c4)

-- F1 CS-K1 @011220: 13 steps
lem-F1-CS-K1-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-at011220 c4 = derive (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q87 c4) ∷
   rw 3 (q37 c4) ∷
   rw 4 (q87 c4) ∷
   rw 5 (q19 c4) ∷
   rw 1 (q104 c4) ∷
   rw 0 (q19 c4) ∷
   rw 1 (q87 c4) ∷
   rw 2 (q53 c4) ∷
   rw 3 (q87 c4) ∷
   rw 4 (q53 c4) ∷
   rw 5 (q1 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) (lem-F1-CS-K1-at011220 c4)

-- tr CS-K1 at 1: 1 steps
lem-tr-CS-K1-at-1 : Ws → ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-CS-K1-at-1 c4 = derive (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q105 c4) ∷ []) Eq.refl

-- F1 CS-K1 @132132: 13 steps
lem-F1-CS-K1-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-F1-CS-K1-at132132 c4 = derive (Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ [])
  (rw⁻ 0 (q40 c4) ∷
   rw 1 (q41 c4) ∷
   rw⁻ 2 (q90 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 4 (q90 c4) ∷
   rw⁻ 5 (q66 c4) ∷
   rw 1 (q104 c4) ∷
   rw⁻ 0 (q67 c4) ∷
   rw⁻ 1 (q91 c4) ∷
   rw 2 (q56 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw 4 (q56 c4) ∷
   rw 5 (q40 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ []) (lem-F1-CS-K1-at132132 c4)

-- F1 CS-K1 @01132032: 13 steps
lem-F1-CS-K1-at01132032 : Ws → ⟪ (Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-CS-K1-at01132032 c4 = derive (Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q92 c4) ∷
   rw 3 (q42 c4) ∷
   rw 4 (q92 c4) ∷
   rw 5 (q68 c4) ∷
   rw 1 (q106 c4) ∷
   rw 0 (q68 c4) ∷
   rw 1 (q92 c4) ∷
   rw 2 (q58 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q58 c4) ∷
   rw 5 (q1 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = eqn (Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ []) (lem-F1-CS-K1-at01132032 c4)

-- F1 CS-K1 @02132031: 13 steps
lem-F1-CS-K1-at02132031 : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-CS-K1-at02132031 c4 = derive (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q44 c4) ∷
   rw 4 (q94 c4) ∷
   rw 5 (q70 c4) ∷
   rw 1 (q107 c4) ∷
   rw 0 (q70 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q61 c4) ∷
   rw 3 (q94 c4) ∷
   rw 4 (q61 c4) ∷
   rw 5 (q8 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (lem-F1-CS-K1-at02132031 c4)

-- tr CS-K1 at 2: 1 steps
lem-tr-CS-K1-at-2 : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-CS-K1-at-2 c4 = derive (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ [])
  (rw 0 (q108 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = eqn (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (lem-F1-comm-CS-CS c4)

-- tr comm-CS-CS at 0: 1 steps
lem-tr-comm-CS-CS-at-0 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-comm-CS-CS-at-0 c4 = derive (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q109 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = eqn (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (Sw23 ∷ Sb3-0-41-2 ∷ []) (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (Sw23 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4))

-- F1 comm-CS-CS @2332: 7 steps
lem-F1-comm-CS-CS-at2332 : Ws → ⟪ (Sb0-1-43-2 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-comm-CS-CS-at2332 c4 = derive (Sb0-1-43-2 ∷ Sb3-0-41-2 ∷ []) (Sb3-0-41-2 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q40 c4) ∷
   rw 1 (q110 c4) ∷
   rw 2 (q111 c4) ∷
   rw 1 (q109 c4) ∷
   rw 0 (q112 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q40 c4) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = eqn (Sw12 ∷ Sb3-0-42-1 ∷ []) (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (Sb0-1-43-2 ∷ Sb3-0-41-2 ∷ []) (Sb3-0-41-2 ∷ Sb0-1-43-2 ∷ []) (lem-F1-comm-CS-CS-at2332 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw12 ∷ Sb3-0-41-2 ∷ []) (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4))

-- F1 comm-CS-CS @122331: 7 steps
lem-F1-comm-CS-CS-at122331 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CS-CS-at122331 c4 = derive (Sb0-2-43-1 ∷ Sb3-0-42-1 ∷ []) (Sb3-0-42-1 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q114 c4) ∷
   rw 1 (q115 c4) ∷
   rw 0 (q116 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (Sw01 ∷ Sb1-2-43-0 ∷ []) (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (Sw01 ∷ Sb3-1-42-0 ∷ []) (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (Sb0-2-43-1 ∷ Sb3-0-42-1 ∷ []) (Sb3-0-42-1 ∷ Sb0-2-43-1 ∷ []) (lem-F1-comm-CS-CS-at122331 c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw01 ∷ Sb3-0-42-1 ∷ []) (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4))

-- F1 comm-CS-CS @01122330: 7 steps
lem-F1-comm-CS-CS-at01122330 : Ws → ⟪ (Sb1-2-43-0 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ
lem-F1-comm-CS-CS-at01122330 c4 = derive (Sb1-2-43-0 ∷ Sb3-1-42-0 ∷ []) (Sb3-1-42-0 ∷ Sb1-2-43-0 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q117 c4) ∷
   rw 2 (q118 c4) ∷
   rw 1 (q119 c4) ∷
   rw 0 (q120 c4) ∷
   rw 1 (q121 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)

-- F0 @2332: 5 steps
lem-F0-at2332 : Ws → ⟪ (Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F0-at2332 c4 = derive (Sb3-0-41-2 ∷ []) (Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q40 c4) ∷
   rw 1 (q111 c4) ∷
   rw 1 (q122 c4) ∷
   rw 0 (q111 c4) ∷
   rw 1 (q40 c4) ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = eqn (Sb3-0-41-2 ∷ []) (Sb2-0-41-3 ∷ []) (lem-F0-at2332 c4)

-- F0 @122331: 5 steps
lem-F0-at122331 : Ws → ⟪ (Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ []) ⟫ʷ
lem-F0-at122331 c4 = derive (Sb3-0-42-1 ∷ []) (Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q8 c4) ∷
   rw 1 (q114 c4) ∷
   rw 1 (q123 c4) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q8 c4) ∷ []) Eq.refl

private
  q124 : Ws → Eqn
  q124 c4 = eqn (Sb3-0-42-1 ∷ []) (Sb1-0-42-3 ∷ []) (lem-F0-at122331 c4)

-- F0 @01122330: 5 steps
lem-F0-at01122330 : Ws → ⟪ (Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F0-at01122330 c4 = derive (Sb3-1-42-0 ∷ []) (Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q118 c4) ∷
   rw 1 (q124 c4) ∷
   rw 0 (q53 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl
