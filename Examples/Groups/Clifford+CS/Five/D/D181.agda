{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D181 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0100 ; wl0111 ; wl0283 ; wl0341 ; wl0602 ; wl0729 ; wl0731 ; wl0827 ; wl0828 ; wl0829 ; wl0830 ; wl0831 ; wl0832 ; wl0833 ; wl0834 ; wl0835 ; wl0836 ; wl0837 ; wl0838 ; wl0839 ; wl0840 ; wl0841 ; wl0842 ; wl0843 ; wl0844 ; wl0845 ; wl0846 ; wl0847 ; wl0848 ; wl0849 ; wl0850 ; wl0851 ; wl0852 ; wp0178 ; wp0352 ; wp0411 ; wp0430 ; wp0431 ; wp0432 ; wp0433 ; wp0434 ; wp0435 ; wp0436 ; wp0437 ; wp0438 ; wp0439 ; wp0440)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym23-at12213443 ; lem-sym23-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-beta-T-at12213443 ; lem-beta-T-at122441 ; lem-sym34-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D180 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-SBOX⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨1·2430⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CK41 ∷ []) (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (wp0178 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (ι1 ∷ []) (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl)
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ ι ∷ []) (ι ∷ X4 ∷ []) (zc)
  q4 : Ws → Eqn
  q4 c4 = eqn (Sb0-2-43-1 ∷ ι ∷ []) (ι ∷ Sb0-2-43-1 ∷ []) (zc)
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (S4⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ S4⁻ ∷ []) (wl0838 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (S4⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ S4⁻ ∷ []) (wl0839 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ S4⁻ ∷ []) (wl0840 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ S4⁻ ∷ []) (wp0436 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ S4⁻ ∷ []) (wp0437 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ CS14 ∷ []) (wl0827 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ CS14 ∷ []) (wl0828 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS14 ∷ []) (wl0829 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ CS14 ∷ []) (wp0430 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ CS14 ∷ []) (wp0431 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (K1 ∷ X4 ∷ []) (X4 ∷ K1 ∷ []) (wl0841 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sb0-2-43-1 ∷ K1 ∷ []) (K1 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at122441 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (ι ∷ []) (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl)

-- F4 CS23^0|K1^1: 133 steps
lem-F4-CS23ᵖ0∣K1ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣K1ᵖ1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 3 (q1 c4) ∷
   rw 3 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 0 (q3 c4) ∷
   re 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   re 14 1 (CS12⁻ ∷ []) ∷
   rw⁻ 13 (q6 c4) ∷
   re 15 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 10 (q7 c4) ∷
   re 8 1 (CS12 ∷ []) ∷
   rw⁻ 7 (q8 c4) ∷
   re 9 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 10 (q10 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   re 3 5 (Sb0-2-43-1 ∷ []) ∷
   re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   re 15 1 (CS12⁻ ∷ []) ∷
   rw⁻ 14 (q12 c4) ∷
   re 16 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 11 (q13 c4) ∷
   re 9 1 (CS12 ∷ []) ∷
   rw⁻ 8 (q14 c4) ∷
   re 10 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 11 (q15 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q5 c4) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 5 (q17 c4) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   re 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   re 17 1 (CS12⁻ ∷ []) ∷
   rw⁻ 16 (q12 c4) ∷
   re 18 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 13 (q13 c4) ∷
   re 11 1 (CS12 ∷ []) ∷
   rw⁻ 10 (q14 c4) ∷
   re 12 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 5 (q9 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw⁻ 13 (q15 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q5 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   re 6 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   re 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   re 19 1 (CS12⁻ ∷ []) ∷
   rw⁻ 18 (q12 c4) ∷
   re 20 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 15 (q13 c4) ∷
   re 13 1 (CS12 ∷ []) ∷
   rw⁻ 12 (q14 c4) ∷
   re 14 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 15 (q15 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   rw 12 (q5 c4) ∷
   re 8 5 (Sb0-2-43-1 ∷ []) ∷
   rw 0 (q19 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q20 : Ws → Eqn
  q20 c4 = eqn (CK42 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (wl0729 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS24 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ CS24 ∷ []) (wl0830 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ CS24 ∷ []) (wl0831 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS24 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS24 ∷ []) (wl0832 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (wp0352 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ []) (wl0834 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ []) (wp0432 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (wp0411 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ []) (wp0433 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) (wl0842 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) (wl0843 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (X ↑))
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) (wp0438 c4)

-- F4 CS23^0|K2^1: 219 steps
lem-F4-CS23ᵖ0∣K2ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣K2ᵖ1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 3 (q20 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 0 (q3 c4) ∷
   re 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   re 14 1 (CS12⁻ ∷ []) ∷
   rw⁻ 13 (q6 c4) ∷
   re 15 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 10 (q7 c4) ∷
   re 8 1 (CS12 ∷ []) ∷
   rw⁻ 7 (q8 c4) ∷
   re 9 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 10 (q10 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   re 3 5 (Sb0-2-43-1 ∷ []) ∷
   re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   re 15 1 (CS12⁻ ∷ []) ∷
   rw⁻ 14 (q21 c4) ∷
   re 16 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 11 (q22 c4) ∷
   re 9 1 (CS12 ∷ []) ∷
   rw⁻ 8 (q23 c4) ∷
   re 10 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 5 (q22 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw 12 (q24 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw⁻ 19 (q5 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw⁻ 23 (q25 c4) ∷
   rw⁻ 20 (q26 c4) ∷
   rw⁻ 17 (q27 c4) ∷
   rw⁻ 14 (q26 c4) ∷
   rw⁻ 11 (q28 c4) ∷
   rw 14 (q5 c4) ∷
   rw 15 (q5 c4) ∷
   rw 16 (q5 c4) ∷
   rw 17 (q5 c4) ∷
   rw⁻ 13 (q24 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw 6 (q24 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw⁻ 17 (q25 c4) ∷
   rw⁻ 14 (q26 c4) ∷
   rw⁻ 11 (q27 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q5 c4) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   re 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   re 10 1 (CS12 ∷ []) ∷
   re 16 1 (CS12⁻ ∷ []) ∷
   rw⁻ 9 (q30 c4) ∷
   re 13 1 (Sb0-2-1-3 ∷ []) ∷
   re 19 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 6 (q31 c4) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q32 c4) ∷
   rw 13 (q33 c4) ∷
   rw⁻ 12 (q32 c4) ∷
   rw 14 (q24 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw⁻ 25 (q25 c4) ∷
   rw⁻ 22 (q26 c4) ∷
   rw⁻ 19 (q27 c4) ∷
   rw⁻ 16 (q26 c4) ∷
   rw⁻ 13 (q28 c4) ∷
   rw 16 (q5 c4) ∷
   rw 17 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 15 (q24 c4) ∷
   rw⁻ 16 (q32 c4) ∷
   rw 15 (q33 c4) ∷
   rw⁻ 14 (q32 c4) ∷
   rw⁻ 9 (q34 c4) ∷
   rw⁻ 8 (q32 c4) ∷
   rw 7 (q33 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   rw 8 (q24 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw⁻ 19 (q25 c4) ∷
   rw⁻ 16 (q26 c4) ∷
   rw⁻ 13 (q27 c4) ∷
   rw⁻ 10 (q26 c4) ∷
   rw⁻ 7 (q28 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   rw 12 (q5 c4) ∷
   rw 13 (q5 c4) ∷
   rw⁻ 9 (q24 c4) ∷
   rw⁻ 10 (q32 c4) ∷
   rw 9 (q33 c4) ∷
   rw⁻ 8 (q32 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   re 7 5 (Sb0-2-43-1 ∷ []) ∷
   re 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   re 19 1 (CS12⁻ ∷ []) ∷
   rw⁻ 18 (q21 c4) ∷
   re 20 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 15 (q22 c4) ∷
   re 13 1 (CS12 ∷ []) ∷
   rw⁻ 12 (q23 c4) ∷
   re 14 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 9 (q22 c4) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw 16 (q24 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   rw⁻ 27 (q25 c4) ∷
   rw⁻ 24 (q26 c4) ∷
   rw⁻ 21 (q27 c4) ∷
   rw⁻ 18 (q26 c4) ∷
   rw⁻ 15 (q28 c4) ∷
   rw 18 (q5 c4) ∷
   rw 19 (q5 c4) ∷
   rw 20 (q5 c4) ∷
   rw 21 (q5 c4) ∷
   rw⁻ 17 (q24 c4) ∷
   rw⁻ 12 (q29 c4) ∷
   rw 10 (q24 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw⁻ 18 (q26 c4) ∷
   rw⁻ 15 (q27 c4) ∷
   rw⁻ 12 (q26 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw 12 (q5 c4) ∷
   rw 13 (q5 c4) ∷
   rw 14 (q5 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 11 (q24 c4) ∷
   rw⁻ 6 (q29 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   rw 12 (q5 c4) ∷
   re 8 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 0 (q20 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = eqn (CK43 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (wl0731 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ []) (wl0835 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ CS34 ∷ []) (wl0836 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS34 ∷ []) (wl0837 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ CS34 ∷ []) (wp0434 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS34 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ CS34 ∷ []) (wp0435 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) (wl0845 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) (wl0846 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) (wl0847 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2413 ∷ []) (lem-sym34-at122441 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx0-2143 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) (wp0439 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (K3 ∷ X4 ∷ []) (X4 ∷ K3 ∷ []) (c₄ (K ↑ ↑ ↑) (X))
  q49 : Ws → Eqn
  q49 c4 = eqn (Toff012 ∷ K3 ∷ []) (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K))
  q50 : Ws → Eqn
  q50 c4 = eqn (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wl0341 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ []) (wl0848 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ []) (wp0440 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) (wl0849 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ []) (wl0850 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (wl0851 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ X4 ∷ CS34 ∷ []) (wl0852 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4)

-- F4 CS23^0|K3^1: 185 steps
lem-F4-CS23ᵖ0∣K3ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣K3ᵖ1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 3 (q35 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 0 (q3 c4) ∷
   re 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   re 14 1 (CS12⁻ ∷ []) ∷
   rw⁻ 13 (q6 c4) ∷
   re 15 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 10 (q7 c4) ∷
   re 8 1 (CS12 ∷ []) ∷
   rw⁻ 7 (q8 c4) ∷
   re 9 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 10 (q10 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   re 3 5 (Sb0-2-43-1 ∷ []) ∷
   re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   re 15 1 (CS12⁻ ∷ []) ∷
   rw⁻ 14 (q36 c4) ∷
   re 16 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 11 (q37 c4) ∷
   re 9 1 (CS12 ∷ []) ∷
   rw⁻ 8 (q38 c4) ∷
   re 10 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 5 (q37 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 11 (q39 c4) ∷
   rw⁻ 8 (q40 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw⁻ 2 (q40 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q5 c4) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   re 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   re 16 1 (CS12⁻ ∷ []) ∷
   rw⁻ 15 (q41 c4) ∷
   re 19 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 12 (q42 c4) ∷
   re 10 1 (CS12 ∷ []) ∷
   rw⁻ 9 (q43 c4) ∷
   re 13 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 6 (q42 c4) ∷
   rw 4 (q44 c4) ∷
   rw 4 (q45 c4) ∷
   rw 4 (q46 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 12 (q47 c4) ∷
   rw⁻ 11 (q48 c4) ∷
   rw 10 (q49 c4) ∷
   rw⁻ 9 (q48 c4) ∷
   rw⁻ 11 (q50 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 16 (q51 c4) ∷
   rw 14 (q52 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw⁻ 25 (q53 c4) ∷
   rw⁻ 22 (q54 c4) ∷
   rw⁻ 19 (q55 c4) ∷
   rw⁻ 16 (q54 c4) ∷
   rw⁻ 13 (q56 c4) ∷
   rw 16 (q5 c4) ∷
   rw 17 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 15 (q52 c4) ∷
   rw⁻ 10 (q57 c4) ∷
   rw 13 (q5 c4) ∷
   rw 14 (q5 c4) ∷
   rw 12 (q50 c4) ∷
   rw⁻ 13 (q48 c4) ∷
   rw 12 (q49 c4) ∷
   rw⁻ 11 (q48 c4) ∷
   rw⁻ 6 (q47 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   rw 4 (q49 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw⁻ 5 (q50 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 10 (q51 c4) ∷
   rw 8 (q52 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw⁻ 19 (q53 c4) ∷
   rw⁻ 16 (q54 c4) ∷
   rw⁻ 13 (q55 c4) ∷
   rw⁻ 10 (q54 c4) ∷
   rw⁻ 7 (q56 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   rw 12 (q5 c4) ∷
   rw 13 (q5 c4) ∷
   rw⁻ 9 (q52 c4) ∷
   rw⁻ 4 (q57 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q5 c4) ∷
   rw 6 (q50 c4) ∷
   rw⁻ 7 (q48 c4) ∷
   rw 6 (q49 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw⁻ 7 (q46 c4) ∷
   rw 7 (q58 c4) ∷
   rw 7 (q59 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   re 7 5 (Sb0-2-43-1 ∷ []) ∷
   re 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   re 19 1 (CS12⁻ ∷ []) ∷
   rw⁻ 18 (q36 c4) ∷
   re 20 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 15 (q37 c4) ∷
   re 13 1 (CS12 ∷ []) ∷
   rw⁻ 12 (q38 c4) ∷
   re 14 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 9 (q37 c4) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 15 (q39 c4) ∷
   rw⁻ 12 (q40 c4) ∷
   rw⁻ 9 (q39 c4) ∷
   rw⁻ 6 (q40 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   rw 12 (q5 c4) ∷
   re 8 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 0 (q35 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (Sw01 ∷ Bx1-2430 ∷ []) (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Sw01 ∷ Toff024 ∷ []) (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ013 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ013 ∷ []) (wl0100 (lit c4))

-- beta-T @01122440: 8 steps
lem-beta-T-at01122440 : Ws → ⟪ (Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at01122440 c4 = derive (Bx1-2430 ∷ []) (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   rw 1 (q9 c4) ∷
   rw 0 (q62 c4) ∷
   rw⁻ 1 (q63 c4) ∷
   rw 2 (q62 c4) ∷
   rw⁻ 3 (q63 c4) ∷
   rw 4 (q60 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (Sb0-1-43-2 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2442 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw12 ∷ Sb0-1-43-2 ∷ []) (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CCZ143 @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at122441 c4 = derive (Sb0-2-43-1 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw⁻ 2 (q66 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 0 (q66 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (Sw12 ∷ Sb2-0-3-1 ∷ []) (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Sb0-1-43-2 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-3-2 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (Sw12 ∷ Sb1-0-3-2 ∷ []) (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·2⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at122441 c4 = derive (Sb0-2-43-1 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   rw 0 (q71 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (Sb0-1-43-2 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·2⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at122441 c4 = derive (Sb0-2-43-1 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q72 c4) ∷
   rw 1 (q73 c4) ∷
   rw 0 (q74 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl
