{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D193 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0008 ; wl0010 ; wl0061 ; wl0064 ; wl0159 ; wl0161)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.TR using (tr03 ; tr04)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (tr03 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw01 ∷ Toff324 ∷ []) (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw01 ∷ Sb1-0-3-2 ∷ []) (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q9 : Ws → Eqn
  q9 c4 = eqn (CK31 ∷ Sw01 ∷ []) (Sw01 ∷ CK30 ∷ []) (wl0161 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw12 ∷ Sb2-0-3-1 ∷ []) (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q16 : Ws → Eqn
  q16 c4 = eqn (CK30 ∷ Sw12 ∷ []) (Sw12 ∷ CK30 ∷ []) (wl0159 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (tr04 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 (lit c4))

-- F1 rel-269 [rhs] part0: 352 steps
lem-F1-rel-269-rhs-part0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) ⟫ʷ
lem-F1-rel-269-rhs-part0 c4 = derive (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  (rw 0 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 45 (q3 c4) ∷
   re 44 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 48 (q4 c4) ∷
   rw⁻ 47 (q5 c4) ∷
   rw⁻ 46 (q6 c4) ∷
   rw⁻ 45 (q5 c4) ∷
   rw⁻ 44 (q7 c4) ∷
   re 45 5 (Sb1-0-42-3 ∷ []) ∷
   re 43 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) ∷
   rw⁻ 45 (q8 c4) ∷
   rw 44 (q9 c4) ∷
   rw⁻ 43 (q8 c4) ∷
   re 44 3 (CK40 ∷ []) ∷
   re 42 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 46 (q4 c4) ∷
   rw⁻ 45 (q5 c4) ∷
   rw⁻ 44 (q6 c4) ∷
   rw⁻ 43 (q5 c4) ∷
   rw⁻ 42 (q7 c4) ∷
   re 43 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 46 (q10 c4) ∷
   re 45 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 49 (q11 c4) ∷
   rw⁻ 48 (q12 c4) ∷
   rw⁻ 47 (q13 c4) ∷
   rw⁻ 46 (q12 c4) ∷
   rw⁻ 45 (q14 c4) ∷
   re 46 5 (Sb2-0-41-3 ∷ []) ∷
   re 44 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw⁻ 46 (q15 c4) ∷
   rw 45 (q16 c4) ∷
   rw⁻ 44 (q15 c4) ∷
   re 45 3 (CK40 ∷ []) ∷
   re 43 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 47 (q11 c4) ∷
   rw⁻ 46 (q12 c4) ∷
   rw⁻ 45 (q13 c4) ∷
   rw⁻ 44 (q12 c4) ∷
   rw⁻ 43 (q14 c4) ∷
   re 44 5 (Sb2-0-41-3 ∷ []) ∷
   rw 44 (q17 c4) ∷
   re 44 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 43 (q15 c4) ∷
   rw⁻ 44 (q16 c4) ∷
   rw 45 (q15 c4) ∷
   re 43 3 (CK40 ∷ []) ∷
   re 45 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 44 (q14 c4) ∷
   rw 45 (q12 c4) ∷
   rw 46 (q13 c4) ∷
   rw 47 (q12 c4) ∷
   rw 48 (q11 c4) ∷
   re 44 5 (Sb1-0-42-3 ∷ []) ∷
   re 46 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 45 (q14 c4) ∷
   rw 46 (q12 c4) ∷
   rw 47 (q13 c4) ∷
   rw 48 (q12 c4) ∷
   rw 49 (q11 c4) ∷
   re 45 5 (Sb1-0-42-3 ∷ []) ∷
   re 47 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 46 (q14 c4) ∷
   rw 47 (q12 c4) ∷
   rw 48 (q13 c4) ∷
   rw 49 (q12 c4) ∷
   rw 50 (q11 c4) ∷
   re 46 5 (Sb1-0-42-3 ∷ []) ∷
   re 48 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 47 (q14 c4) ∷
   rw 48 (q12 c4) ∷
   rw 49 (q13 c4) ∷
   rw 50 (q12 c4) ∷
   rw 51 (q11 c4) ∷
   re 47 5 (Sb1-0-42-3 ∷ []) ∷
   re 49 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 48 (q14 c4) ∷
   rw 49 (q12 c4) ∷
   rw 50 (q13 c4) ∷
   rw 51 (q12 c4) ∷
   rw 52 (q11 c4) ∷
   re 48 5 (Sb1-0-42-3 ∷ []) ∷
   re 50 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 49 (q14 c4) ∷
   rw 50 (q12 c4) ∷
   rw 51 (q13 c4) ∷
   rw 52 (q12 c4) ∷
   rw 53 (q11 c4) ∷
   re 49 5 (Sb1-0-42-3 ∷ []) ∷
   re 51 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 50 (q14 c4) ∷
   rw 51 (q12 c4) ∷
   rw 52 (q13 c4) ∷
   rw 53 (q12 c4) ∷
   rw 54 (q11 c4) ∷
   re 50 5 (Sb1-0-42-3 ∷ []) ∷
   re 52 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 51 (q14 c4) ∷
   rw 52 (q12 c4) ∷
   rw 53 (q13 c4) ∷
   rw 54 (q12 c4) ∷
   rw 55 (q11 c4) ∷
   re 51 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 52 (q18 c4) ∷
   rw 53 (q19 c4) ∷
   rw⁻ 54 (q18 c4) ∷
   rw⁻ 55 (q18 c4) ∷
   rw⁻ 56 (q18 c4) ∷
   re 58 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 57 (q14 c4) ∷
   rw 58 (q12 c4) ∷
   rw 59 (q13 c4) ∷
   rw 60 (q12 c4) ∷
   rw 61 (q11 c4) ∷
   re 57 5 (Sb1-0-42-3 ∷ []) ∷
   re 59 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 58 (q15 c4) ∷
   rw⁻ 59 (q16 c4) ∷
   rw 60 (q15 c4) ∷
   re 58 3 (CK40 ∷ []) ∷
   re 60 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 59 (q14 c4) ∷
   rw 60 (q12 c4) ∷
   rw 61 (q13 c4) ∷
   rw 62 (q12 c4) ∷
   rw 63 (q11 c4) ∷
   re 59 5 (Sb1-0-42-3 ∷ []) ∷
   re 61 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 60 (q15 c4) ∷
   rw⁻ 61 (q16 c4) ∷
   rw 62 (q15 c4) ∷
   re 60 3 (CK40 ∷ []) ∷
   re 62 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 61 (q14 c4) ∷
   rw 62 (q12 c4) ∷
   rw 63 (q13 c4) ∷
   rw 64 (q12 c4) ∷
   rw 65 (q11 c4) ∷
   re 61 5 (Sb1-0-42-3 ∷ []) ∷
   re 63 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 62 (q15 c4) ∷
   rw⁻ 63 (q20 c4) ∷
   rw 64 (q15 c4) ∷
   re 62 3 (CS04 ∷ []) ∷
   re 64 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 63 (q15 c4) ∷
   rw⁻ 64 (q20 c4) ∷
   rw 65 (q15 c4) ∷
   re 63 3 (CS04 ∷ []) ∷
   re 65 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 64 (q15 c4) ∷
   rw⁻ 65 (q20 c4) ∷
   rw 66 (q15 c4) ∷
   re 64 3 (CS04 ∷ []) ∷
   re 66 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 65 (q15 c4) ∷
   rw⁻ 66 (q20 c4) ∷
   rw 67 (q15 c4) ∷
   re 65 3 (CS04 ∷ []) ∷
   re 67 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 66 (q15 c4) ∷
   rw⁻ 67 (q20 c4) ∷
   rw 68 (q15 c4) ∷
   re 66 3 (CS04 ∷ []) ∷
   re 68 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 67 (q15 c4) ∷
   rw⁻ 68 (q20 c4) ∷
   rw 69 (q15 c4) ∷
   re 67 3 (CS04 ∷ []) ∷
   re 69 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 68 (q15 c4) ∷
   rw⁻ 69 (q20 c4) ∷
   rw 70 (q15 c4) ∷
   re 68 3 (CS04 ∷ []) ∷
   re 70 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 69 (q15 c4) ∷
   rw⁻ 70 (q20 c4) ∷
   rw 71 (q15 c4) ∷
   re 69 3 (CS04 ∷ []) ∷
   re 71 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 70 (q15 c4) ∷
   rw⁻ 71 (q20 c4) ∷
   rw 72 (q15 c4) ∷
   re 70 3 (CS04 ∷ []) ∷
   rw 71 (q19 c4) ∷
   rw⁻ 72 (q18 c4) ∷
   rw⁻ 73 (q18 c4) ∷
   rw⁻ 74 (q18 c4) ∷
   re 76 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 75 (q14 c4) ∷
   rw 76 (q12 c4) ∷
   rw 77 (q13 c4) ∷
   rw 78 (q12 c4) ∷
   rw 79 (q11 c4) ∷
   re 75 5 (Sb1-0-42-3 ∷ []) ∷
   re 77 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 76 (q15 c4) ∷
   rw⁻ 77 (q16 c4) ∷
   rw 78 (q15 c4) ∷
   re 76 3 (CK40 ∷ []) ∷
   re 78 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 77 (q14 c4) ∷
   rw 78 (q12 c4) ∷
   rw 79 (q13 c4) ∷
   rw 80 (q12 c4) ∷
   rw 81 (q11 c4) ∷
   re 77 5 (Sb1-0-42-3 ∷ []) ∷
   re 79 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 78 (q15 c4) ∷
   rw⁻ 79 (q16 c4) ∷
   rw 80 (q15 c4) ∷
   re 78 3 (CK40 ∷ []) ∷
   re 80 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 79 (q14 c4) ∷
   rw 80 (q12 c4) ∷
   rw 81 (q13 c4) ∷
   rw 82 (q12 c4) ∷
   rw 83 (q11 c4) ∷
   re 79 5 (Sb1-0-42-3 ∷ []) ∷
   re 81 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 80 (q14 c4) ∷
   rw 81 (q12 c4) ∷
   rw 82 (q13 c4) ∷
   rw 83 (q12 c4) ∷
   rw 84 (q11 c4) ∷
   re 80 5 (Sb1-0-42-3 ∷ []) ∷
   re 82 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 81 (q14 c4) ∷
   rw 82 (q12 c4) ∷
   rw 83 (q13 c4) ∷
   rw 84 (q12 c4) ∷
   rw 85 (q11 c4) ∷
   re 81 5 (Sb1-0-42-3 ∷ []) ∷
   re 83 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 82 (q15 c4) ∷
   rw⁻ 83 (q20 c4) ∷
   rw 84 (q15 c4) ∷
   re 82 3 (CS04 ∷ []) ∷
   re 84 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 83 (q15 c4) ∷
   rw⁻ 84 (q20 c4) ∷
   rw 85 (q15 c4) ∷
   re 83 3 (CS04 ∷ []) ∷
   re 85 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 84 (q15 c4) ∷
   rw⁻ 85 (q20 c4) ∷
   rw 86 (q15 c4) ∷
   re 84 3 (CS04 ∷ []) ∷
   rw 85 (q10 c4) ∷
   re 43 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 42 (q8 c4) ∷
   rw⁻ 43 (q9 c4) ∷
   rw 44 (q8 c4) ∷
   re 42 3 (CK41 ∷ []) ∷
   re 44 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 43 (q7 c4) ∷
   rw 44 (q5 c4) ∷
   rw 45 (q6 c4) ∷
   rw 46 (q5 c4) ∷
   rw 47 (q4 c4) ∷
   re 43 5 (Sb0-1-42-3 ∷ []) ∷
   re 45 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 44 (q7 c4) ∷
   rw 45 (q5 c4) ∷
   rw 46 (q6 c4) ∷
   rw 47 (q5 c4) ∷
   rw 48 (q4 c4) ∷
   re 44 5 (Sb0-1-42-3 ∷ []) ∷
   re 46 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 45 (q7 c4) ∷
   rw 46 (q5 c4) ∷
   rw 47 (q6 c4) ∷
   rw 48 (q5 c4) ∷
   rw 49 (q4 c4) ∷
   re 45 5 (Sb0-1-42-3 ∷ []) ∷
   re 47 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 46 (q7 c4) ∷
   rw 47 (q5 c4) ∷
   rw 48 (q6 c4) ∷
   rw 49 (q5 c4) ∷
   rw 50 (q4 c4) ∷
   re 46 5 (Sb0-1-42-3 ∷ []) ∷
   re 48 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 47 (q7 c4) ∷
   rw 48 (q5 c4) ∷
   rw 49 (q6 c4) ∷
   rw 50 (q5 c4) ∷
   rw 51 (q4 c4) ∷
   re 47 5 (Sb0-1-42-3 ∷ []) ∷
   re 49 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 48 (q7 c4) ∷
   rw 49 (q5 c4) ∷
   rw 50 (q6 c4) ∷
   rw 51 (q5 c4) ∷
   rw 52 (q4 c4) ∷
   re 48 5 (Sb0-1-42-3 ∷ []) ∷
   re 50 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 49 (q7 c4) ∷
   rw 50 (q5 c4) ∷
   rw 51 (q6 c4) ∷
   rw 52 (q5 c4) ∷
   rw 53 (q4 c4) ∷
   re 49 5 (Sb0-1-42-3 ∷ []) ∷
   re 51 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 50 (q7 c4) ∷
   rw 51 (q5 c4) ∷
   rw 52 (q6 c4) ∷
   rw 53 (q5 c4) ∷
   rw 54 (q4 c4) ∷
   re 50 5 (Sb0-1-42-3 ∷ []) ∷
   rw 51 (q21 c4) ∷
   rw 52 (q22 c4) ∷
   rw 53 (q21 c4) ∷
   rw 54 (q21 c4) ∷
   rw 55 (q21 c4) ∷
   re 57 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 56 (q7 c4) ∷
   rw 57 (q5 c4) ∷
   rw 58 (q6 c4) ∷
   rw 59 (q5 c4) ∷
   rw 60 (q4 c4) ∷
   re 56 5 (Sb0-1-42-3 ∷ []) ∷
   re 58 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 57 (q8 c4) ∷
   rw⁻ 58 (q9 c4) ∷
   rw 59 (q8 c4) ∷
   re 57 3 (CK41 ∷ []) ∷
   re 59 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 58 (q7 c4) ∷
   rw 59 (q5 c4) ∷
   rw 60 (q6 c4) ∷
   rw 61 (q5 c4) ∷
   rw 62 (q4 c4) ∷
   re 58 5 (Sb0-1-42-3 ∷ []) ∷
   re 60 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 59 (q8 c4) ∷
   rw⁻ 60 (q9 c4) ∷
   rw 61 (q8 c4) ∷
   re 59 3 (CK41 ∷ []) ∷
   re 61 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 60 (q7 c4) ∷
   rw 61 (q5 c4) ∷
   rw 62 (q6 c4) ∷
   rw 63 (q5 c4) ∷
   rw 64 (q4 c4) ∷
   re 60 5 (Sb0-1-42-3 ∷ []) ∷
   re 62 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 61 (q8 c4) ∷
   rw⁻ 62 (q23 c4) ∷
   rw 63 (q8 c4) ∷
   re 61 3 (CS14 ∷ []) ∷ []) Eq.refl
