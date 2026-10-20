{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D199 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0008 ; wl0010 ; wl0061 ; wl0064 ; wl0159 ; wl0161)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-F1-comm-CS-CS)
open import Examples.Groups.Clifford+CS.Five.D.D196 using (lem-DB4K1-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1)
open import Examples.Groups.Clifford+CS.Five.D.D198 using (lem-DB4K1-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.TR using (tr07 ; tr08 ; tr09)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (tr07 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-DB4K1-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn [] (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (tr08 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw12 ∷ Sb2-0-3-1 ∷ []) (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw01 ∷ Toff324 ∷ []) (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw01 ∷ Sb1-0-3-2 ∷ []) (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q15 : Ws → Eqn
  q15 c4 = eqn (CK31 ∷ Sw01 ∷ []) (Sw01 ∷ CK30 ∷ []) (wl0161 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q17 : Ws → Eqn
  q17 c4 = eqn (CK30 ∷ Sw12 ∷ []) (Sw12 ∷ CK30 ∷ []) (wl0159 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CK40 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (tr09 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-DB4K1-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (lem-F1-comm-CS-CS c4)

-- F1 rel-272 [rhs]: 408 steps
lem-F1-rel-272-rhs : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-rel-272-rhs c4 = derive (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 35 (q3 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw 37 (q5 c4) ∷
   re 37 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 36 (q6 c4) ∷
   rw 37 (q7 c4) ∷
   rw 38 (q8 c4) ∷
   rw 39 (q7 c4) ∷
   rw 40 (q9 c4) ∷
   re 36 5 (Sb1-0-42-3 ∷ []) ∷
   re 38 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 37 (q6 c4) ∷
   rw 38 (q7 c4) ∷
   rw 39 (q8 c4) ∷
   rw 40 (q7 c4) ∷
   rw 41 (q9 c4) ∷
   re 37 5 (Sb1-0-42-3 ∷ []) ∷
   re 39 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 38 (q6 c4) ∷
   rw 39 (q7 c4) ∷
   rw 40 (q8 c4) ∷
   rw 41 (q7 c4) ∷
   rw 42 (q9 c4) ∷
   re 38 5 (Sb1-0-42-3 ∷ []) ∷
   re 40 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 39 (q6 c4) ∷
   rw 40 (q7 c4) ∷
   rw 41 (q8 c4) ∷
   rw 42 (q7 c4) ∷
   rw 43 (q9 c4) ∷
   re 39 5 (Sb1-0-42-3 ∷ []) ∷
   rw 40 (q4 c4) ∷
   re 36 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 35 (q10 c4) ∷
   rw 36 (q11 c4) ∷
   rw 37 (q12 c4) ∷
   rw 38 (q11 c4) ∷
   rw 39 (q13 c4) ∷
   re 35 5 (Sb0-1-42-3 ∷ []) ∷
   re 37 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 36 (q10 c4) ∷
   rw 37 (q11 c4) ∷
   rw 38 (q12 c4) ∷
   rw 39 (q11 c4) ∷
   rw 40 (q13 c4) ∷
   re 36 5 (Sb0-1-42-3 ∷ []) ∷
   re 38 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 37 (q10 c4) ∷
   rw 38 (q11 c4) ∷
   rw 39 (q12 c4) ∷
   rw 40 (q11 c4) ∷
   rw 41 (q13 c4) ∷
   re 37 5 (Sb0-1-42-3 ∷ []) ∷
   re 39 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 38 (q10 c4) ∷
   rw 39 (q11 c4) ∷
   rw 40 (q12 c4) ∷
   rw 41 (q11 c4) ∷
   rw 42 (q13 c4) ∷
   re 38 5 (Sb0-1-42-3 ∷ []) ∷
   rw 39 (q3 c4) ∷
   rw⁻ 38 (q3 c4) ∷
   re 37 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 41 (q13 c4) ∷
   rw⁻ 40 (q11 c4) ∷
   rw⁻ 39 (q12 c4) ∷
   rw⁻ 38 (q11 c4) ∷
   rw⁻ 37 (q10 c4) ∷
   re 38 5 (Sb1-0-42-3 ∷ []) ∷
   re 36 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 40 (q13 c4) ∷
   rw⁻ 39 (q11 c4) ∷
   rw⁻ 38 (q12 c4) ∷
   rw⁻ 37 (q11 c4) ∷
   rw⁻ 36 (q10 c4) ∷
   re 37 5 (Sb1-0-42-3 ∷ []) ∷
   re 35 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 39 (q13 c4) ∷
   rw⁻ 38 (q11 c4) ∷
   rw⁻ 37 (q12 c4) ∷
   rw⁻ 36 (q11 c4) ∷
   rw⁻ 35 (q10 c4) ∷
   re 36 5 (Sb1-0-42-3 ∷ []) ∷
   re 34 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) ∷
   rw⁻ 36 (q14 c4) ∷
   rw 35 (q15 c4) ∷
   rw⁻ 34 (q14 c4) ∷
   re 35 3 (CK40 ∷ []) ∷
   re 33 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 37 (q13 c4) ∷
   rw⁻ 36 (q11 c4) ∷
   rw⁻ 35 (q12 c4) ∷
   rw⁻ 34 (q11 c4) ∷
   rw⁻ 33 (q10 c4) ∷
   re 34 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 39 (q4 c4) ∷
   re 38 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 42 (q9 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   rw⁻ 40 (q8 c4) ∷
   rw⁻ 39 (q7 c4) ∷
   rw⁻ 38 (q6 c4) ∷
   re 39 5 (Sb2-0-41-3 ∷ []) ∷
   re 37 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 41 (q9 c4) ∷
   rw⁻ 40 (q7 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw⁻ 38 (q7 c4) ∷
   rw⁻ 37 (q6 c4) ∷
   re 38 5 (Sb2-0-41-3 ∷ []) ∷
   re 36 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 40 (q9 c4) ∷
   rw⁻ 39 (q7 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 37 (q7 c4) ∷
   rw⁻ 36 (q6 c4) ∷
   re 37 5 (Sb2-0-41-3 ∷ []) ∷
   re 35 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw⁻ 37 (q16 c4) ∷
   rw 36 (q17 c4) ∷
   rw⁻ 35 (q16 c4) ∷
   re 36 3 (CK40 ∷ []) ∷
   re 34 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 38 (q9 c4) ∷
   rw⁻ 37 (q7 c4) ∷
   rw⁻ 36 (q8 c4) ∷
   rw⁻ 35 (q7 c4) ∷
   rw⁻ 34 (q6 c4) ∷
   re 35 5 (Sb2-0-41-3 ∷ []) ∷
   rw 35 (q18 c4) ∷
   re 35 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 34 (q16 c4) ∷
   rw⁻ 35 (q17 c4) ∷
   rw 36 (q16 c4) ∷
   re 34 3 (CK40 ∷ []) ∷
   rw⁻ 35 (q19 c4) ∷
   rw 36 (q20 c4) ∷
   rw⁻ 37 (q19 c4) ∷
   rw⁻ 38 (q19 c4) ∷
   rw⁻ 39 (q19 c4) ∷
   re 41 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 40 (q6 c4) ∷
   rw 41 (q7 c4) ∷
   rw 42 (q8 c4) ∷
   rw 43 (q7 c4) ∷
   rw 44 (q9 c4) ∷
   re 40 5 (Sb1-0-42-3 ∷ []) ∷
   re 42 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 41 (q16 c4) ∷
   rw⁻ 42 (q17 c4) ∷
   rw 43 (q16 c4) ∷
   re 41 3 (CK40 ∷ []) ∷
   re 43 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 42 (q6 c4) ∷
   rw 43 (q7 c4) ∷
   rw 44 (q8 c4) ∷
   rw 45 (q7 c4) ∷
   rw 46 (q9 c4) ∷
   re 42 5 (Sb1-0-42-3 ∷ []) ∷
   re 44 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 43 (q16 c4) ∷
   rw⁻ 44 (q17 c4) ∷
   rw 45 (q16 c4) ∷
   re 43 3 (CK40 ∷ []) ∷
   re 45 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 44 (q6 c4) ∷
   rw 45 (q7 c4) ∷
   rw 46 (q8 c4) ∷
   rw 47 (q7 c4) ∷
   rw 48 (q9 c4) ∷
   re 44 5 (Sb1-0-42-3 ∷ []) ∷
   re 46 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 45 (q16 c4) ∷
   rw⁻ 46 (q21 c4) ∷
   rw 47 (q16 c4) ∷
   re 45 3 (CS04 ∷ []) ∷
   re 47 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 46 (q16 c4) ∷
   rw⁻ 47 (q21 c4) ∷
   rw 48 (q16 c4) ∷
   re 46 3 (CS04 ∷ []) ∷
   re 48 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 47 (q16 c4) ∷
   rw⁻ 48 (q21 c4) ∷
   rw 49 (q16 c4) ∷
   re 47 3 (CS04 ∷ []) ∷
   re 49 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 48 (q16 c4) ∷
   rw⁻ 49 (q21 c4) ∷
   rw 50 (q16 c4) ∷
   re 48 3 (CS04 ∷ []) ∷
   re 50 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 49 (q16 c4) ∷
   rw⁻ 50 (q21 c4) ∷
   rw 51 (q16 c4) ∷
   re 49 3 (CS04 ∷ []) ∷
   re 51 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 50 (q16 c4) ∷
   rw⁻ 51 (q21 c4) ∷
   rw 52 (q16 c4) ∷
   re 50 3 (CS04 ∷ []) ∷
   re 52 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 51 (q16 c4) ∷
   rw⁻ 52 (q21 c4) ∷
   rw 53 (q16 c4) ∷
   re 51 3 (CS04 ∷ []) ∷
   re 53 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 52 (q16 c4) ∷
   rw⁻ 53 (q21 c4) ∷
   rw 54 (q16 c4) ∷
   re 52 3 (CS04 ∷ []) ∷
   re 54 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 53 (q16 c4) ∷
   rw⁻ 54 (q21 c4) ∷
   rw 55 (q16 c4) ∷
   re 53 3 (CS04 ∷ []) ∷
   rw 54 (q20 c4) ∷
   rw⁻ 55 (q19 c4) ∷
   rw⁻ 56 (q19 c4) ∷
   rw⁻ 57 (q19 c4) ∷
   re 59 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 58 (q6 c4) ∷
   rw 59 (q7 c4) ∷
   rw 60 (q8 c4) ∷
   rw 61 (q7 c4) ∷
   rw 62 (q9 c4) ∷
   re 58 5 (Sb1-0-42-3 ∷ []) ∷
   re 60 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 59 (q16 c4) ∷
   rw⁻ 60 (q17 c4) ∷
   rw 61 (q16 c4) ∷
   re 59 3 (CK40 ∷ []) ∷
   re 61 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 60 (q6 c4) ∷
   rw 61 (q7 c4) ∷
   rw 62 (q8 c4) ∷
   rw 63 (q7 c4) ∷
   rw 64 (q9 c4) ∷
   re 60 5 (Sb1-0-42-3 ∷ []) ∷
   re 62 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 61 (q16 c4) ∷
   rw⁻ 62 (q17 c4) ∷
   rw 63 (q16 c4) ∷
   re 61 3 (CK40 ∷ []) ∷
   re 63 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 62 (q6 c4) ∷
   rw 63 (q7 c4) ∷
   rw 64 (q8 c4) ∷
   rw 65 (q7 c4) ∷
   rw 66 (q9 c4) ∷
   re 62 5 (Sb1-0-42-3 ∷ []) ∷
   re 64 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 63 (q16 c4) ∷
   rw⁻ 64 (q21 c4) ∷
   rw 65 (q16 c4) ∷
   re 63 3 (CS04 ∷ []) ∷
   re 65 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 64 (q16 c4) ∷
   rw⁻ 65 (q21 c4) ∷
   rw 66 (q16 c4) ∷
   re 64 3 (CS04 ∷ []) ∷
   re 66 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 65 (q16 c4) ∷
   rw⁻ 66 (q21 c4) ∷
   rw 67 (q16 c4) ∷
   re 65 3 (CS04 ∷ []) ∷
   rw 66 (q4 c4) ∷
   re 34 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 33 (q14 c4) ∷
   rw⁻ 34 (q15 c4) ∷
   rw 35 (q14 c4) ∷
   re 33 3 (CK41 ∷ []) ∷
   rw 34 (q22 c4) ∷
   rw 35 (q23 c4) ∷
   rw 36 (q22 c4) ∷
   rw 37 (q22 c4) ∷
   rw 38 (q22 c4) ∷
   re 40 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 39 (q10 c4) ∷
   rw 40 (q11 c4) ∷
   rw 41 (q12 c4) ∷
   rw 42 (q11 c4) ∷
   rw 43 (q13 c4) ∷
   re 39 5 (Sb0-1-42-3 ∷ []) ∷
   re 41 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 40 (q14 c4) ∷
   rw⁻ 41 (q15 c4) ∷
   rw 42 (q14 c4) ∷
   re 40 3 (CK41 ∷ []) ∷
   re 42 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 41 (q10 c4) ∷
   rw 42 (q11 c4) ∷
   rw 43 (q12 c4) ∷
   rw 44 (q11 c4) ∷
   rw 45 (q13 c4) ∷
   re 41 5 (Sb0-1-42-3 ∷ []) ∷
   re 43 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 42 (q14 c4) ∷
   rw⁻ 43 (q15 c4) ∷
   rw 44 (q14 c4) ∷
   re 42 3 (CK41 ∷ []) ∷
   re 44 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 43 (q10 c4) ∷
   rw 44 (q11 c4) ∷
   rw 45 (q12 c4) ∷
   rw 46 (q11 c4) ∷
   rw 47 (q13 c4) ∷
   re 43 5 (Sb0-1-42-3 ∷ []) ∷
   re 45 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 44 (q14 c4) ∷
   rw⁻ 45 (q24 c4) ∷
   rw 46 (q14 c4) ∷
   re 44 3 (CS14 ∷ []) ∷
   re 46 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 45 (q14 c4) ∷
   rw⁻ 46 (q24 c4) ∷
   rw 47 (q14 c4) ∷
   re 45 3 (CS14 ∷ []) ∷
   re 47 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 46 (q14 c4) ∷
   rw⁻ 47 (q24 c4) ∷
   rw 48 (q14 c4) ∷
   re 46 3 (CS14 ∷ []) ∷
   re 48 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 47 (q14 c4) ∷
   rw⁻ 48 (q24 c4) ∷
   rw 49 (q14 c4) ∷
   re 47 3 (CS14 ∷ []) ∷
   re 49 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 48 (q14 c4) ∷
   rw⁻ 49 (q24 c4) ∷
   rw 50 (q14 c4) ∷
   re 48 3 (CS14 ∷ []) ∷
   re 50 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 49 (q14 c4) ∷
   rw⁻ 50 (q24 c4) ∷
   rw 51 (q14 c4) ∷
   re 49 3 (CS14 ∷ []) ∷
   re 51 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 50 (q14 c4) ∷
   rw⁻ 51 (q24 c4) ∷
   rw 52 (q14 c4) ∷
   re 50 3 (CS14 ∷ []) ∷
   re 52 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 51 (q14 c4) ∷
   rw⁻ 52 (q24 c4) ∷
   rw 53 (q14 c4) ∷
   re 51 3 (CS14 ∷ []) ∷
   re 53 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 52 (q14 c4) ∷
   rw⁻ 53 (q24 c4) ∷
   rw 54 (q14 c4) ∷
   re 52 3 (CS14 ∷ []) ∷
   rw 53 (q23 c4) ∷
   rw 54 (q22 c4) ∷
   rw 55 (q22 c4) ∷
   rw 56 (q22 c4) ∷
   re 58 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 57 (q10 c4) ∷
   rw 58 (q11 c4) ∷
   rw 59 (q12 c4) ∷
   rw 60 (q11 c4) ∷
   rw 61 (q13 c4) ∷
   re 57 5 (Sb0-1-42-3 ∷ []) ∷
   re 59 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 58 (q14 c4) ∷
   rw⁻ 59 (q15 c4) ∷
   rw 60 (q14 c4) ∷
   re 58 3 (CK41 ∷ []) ∷
   re 60 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 59 (q10 c4) ∷
   rw 60 (q11 c4) ∷
   rw 61 (q12 c4) ∷
   rw 62 (q11 c4) ∷
   rw 63 (q13 c4) ∷
   re 59 5 (Sb0-1-42-3 ∷ []) ∷
   re 61 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 60 (q14 c4) ∷
   rw⁻ 61 (q15 c4) ∷
   rw 62 (q14 c4) ∷
   re 60 3 (CK41 ∷ []) ∷
   re 62 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 61 (q10 c4) ∷
   rw 62 (q11 c4) ∷
   rw 63 (q12 c4) ∷
   rw 64 (q11 c4) ∷
   rw 65 (q13 c4) ∷
   re 61 5 (Sb0-1-42-3 ∷ []) ∷
   re 63 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 62 (q14 c4) ∷
   rw⁻ 63 (q24 c4) ∷
   rw 64 (q14 c4) ∷
   re 62 3 (CS14 ∷ []) ∷
   re 64 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 63 (q14 c4) ∷
   rw⁻ 64 (q24 c4) ∷
   rw 65 (q14 c4) ∷
   re 63 3 (CS14 ∷ []) ∷
   re 65 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 64 (q14 c4) ∷
   rw⁻ 65 (q24 c4) ∷
   rw 66 (q14 c4) ∷
   re 64 3 (CS14 ∷ []) ∷
   rw 65 (q3 c4) ∷
   rw⁻ 33 (q25 c4) ∷
   rw 65 (q26 c4) ∷ []) Eq.refl
