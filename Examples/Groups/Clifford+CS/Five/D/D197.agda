{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D197 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0008 ; wl0064 ; wl0159 ; wl0161 ; wl0887 ; wl0888 ; wl0889 ; wl0890 ; wl0891 ; wl0892 ; wl0894 ; wl0895 ; wl0896 ; wl0897 ; wl0898 ; wl0899)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-F4-K1ᵖ0∣CS12ᵖ1 ; lem-F4-S2ᵖ0∣CS12ᵖ1 ; lem-F4-iIᵖ0∣CS12ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-F4-CS12ᵖ0∣S1ᵖ1 ; lem-F4-CS12ᵖ0∣S2ᵖ1 ; lem-F4-CS12ᵖ0∣iIᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D178 using (lem-F4-CS12ᵖ0∣K1ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D179 using (lem-F4-CS12ᵖ0∣CS12ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D196 using (lem-split4S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 ; lem-split4iI-S2-S2-S2-CS12-K1-CS12-K1-CS12)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (lem-split4S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (lem-split4iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl0889 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS12ᵖ1 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (wl0890 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (wl0894 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (wl0891 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (wl0898 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (wl0899 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S1ᵖ1 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣iIᵖ1 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw01 ∷ Toff324 ∷ []) (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sw01 ∷ Sb1-0-3-2 ∷ []) (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q30 : Ws → Eqn
  q30 c4 = eqn (CK31 ∷ Sw01 ∷ []) (Sw01 ∷ CK30 ∷ []) (wl0161 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw12 ∷ Sb2-0-3-1 ∷ []) (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q40 : Ws → Eqn
  q40 c4 = eqn (CK30 ∷ Sw12 ∷ []) (Sw12 ∷ CK30 ∷ []) (wl0159 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 (lit c4))

-- DB4[K1 S2 iI S2 S2 S2 CS12 K1 CS12 K1 CS12 S1 S1 S1 S1 S1 S1 S1 S1 S1 iI S2 S2 S2 CS12 K1 CS12 K1 CS12 S1 S1 S1] part0: 330 steps
lem-DB4K1-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-part0 : Ws → ⟪ (CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sw01 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sw12 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sw12 ∷ Sw01 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-DB4K1-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-part0 c4 = derive (CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sw01 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sw12 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sw12 ∷ Sw01 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 50 (q2 c4) ∷
   rw 49 (q3 c4) ∷
   rw 48 (q3 c4) ∷
   rw 47 (q3 c4) ∷
   rw 46 (q3 c4) ∷
   rw 45 (q3 c4) ∷
   rw 44 (q3 c4) ∷
   rw 43 (q3 c4) ∷
   rw 42 (q3 c4) ∷
   rw 41 (q3 c4) ∷
   rw⁻ 40 (q4 c4) ∷
   rw 39 (q5 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw 37 (q5 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw 35 (q6 c4) ∷
   rw 34 (q6 c4) ∷
   rw 33 (q6 c4) ∷
   rw 32 (q7 c4) ∷
   rw 31 (q6 c4) ∷
   rw 52 (q8 c4) ∷
   rw 51 (q8 c4) ∷
   rw 50 (q8 c4) ∷
   rw 49 (q8 c4) ∷
   rw 48 (q8 c4) ∷
   rw 47 (q8 c4) ∷
   rw 46 (q8 c4) ∷
   rw 45 (q8 c4) ∷
   rw 44 (q8 c4) ∷
   rw⁻ 43 (q9 c4) ∷
   rw 42 (q10 c4) ∷
   rw⁻ 41 (q9 c4) ∷
   rw 40 (q10 c4) ∷
   rw⁻ 39 (q9 c4) ∷
   rw 38 (q11 c4) ∷
   rw 37 (q11 c4) ∷
   rw 36 (q11 c4) ∷
   rw 35 (q12 c4) ∷
   rw 34 (q11 c4) ∷
   rw 55 (q8 c4) ∷
   rw 54 (q8 c4) ∷
   rw 53 (q8 c4) ∷
   rw 52 (q8 c4) ∷
   rw 51 (q8 c4) ∷
   rw 50 (q8 c4) ∷
   rw 49 (q8 c4) ∷
   rw 48 (q8 c4) ∷
   rw 47 (q8 c4) ∷
   rw⁻ 46 (q9 c4) ∷
   rw 45 (q10 c4) ∷
   rw⁻ 44 (q9 c4) ∷
   rw 43 (q10 c4) ∷
   rw⁻ 42 (q9 c4) ∷
   rw 41 (q11 c4) ∷
   rw 40 (q11 c4) ∷
   rw 39 (q11 c4) ∷
   rw 38 (q12 c4) ∷
   rw 37 (q11 c4) ∷
   rw 58 (q8 c4) ∷
   rw 57 (q8 c4) ∷
   rw 56 (q8 c4) ∷
   rw 55 (q8 c4) ∷
   rw 54 (q8 c4) ∷
   rw 53 (q8 c4) ∷
   rw 52 (q8 c4) ∷
   rw 51 (q8 c4) ∷
   rw 50 (q8 c4) ∷
   rw⁻ 49 (q9 c4) ∷
   rw 48 (q10 c4) ∷
   rw⁻ 47 (q9 c4) ∷
   rw 46 (q10 c4) ∷
   rw⁻ 45 (q9 c4) ∷
   rw 44 (q11 c4) ∷
   rw 43 (q11 c4) ∷
   rw 42 (q11 c4) ∷
   rw 41 (q12 c4) ∷
   rw 40 (q11 c4) ∷
   rw⁻ 61 (q13 c4) ∷
   rw⁻ 60 (q13 c4) ∷
   rw⁻ 59 (q13 c4) ∷
   rw⁻ 58 (q13 c4) ∷
   rw⁻ 57 (q13 c4) ∷
   rw⁻ 56 (q13 c4) ∷
   rw⁻ 55 (q13 c4) ∷
   rw⁻ 54 (q13 c4) ∷
   rw⁻ 53 (q13 c4) ∷
   rw⁻ 52 (q14 c4) ∷
   rw⁻ 51 (q15 c4) ∷
   rw⁻ 50 (q14 c4) ∷
   rw⁻ 49 (q15 c4) ∷
   rw⁻ 48 (q14 c4) ∷
   rw⁻ 47 (q16 c4) ∷
   rw⁻ 46 (q16 c4) ∷
   rw⁻ 45 (q16 c4) ∷
   rw⁻ 44 (q17 c4) ∷
   rw⁻ 43 (q16 c4) ∷
   rw 64 (q18 c4) ∷
   rw 63 (q18 c4) ∷
   rw 62 (q18 c4) ∷
   rw 61 (q18 c4) ∷
   rw 60 (q18 c4) ∷
   rw 59 (q18 c4) ∷
   rw 58 (q18 c4) ∷
   rw 57 (q18 c4) ∷
   rw 56 (q18 c4) ∷
   rw⁻ 55 (q19 c4) ∷
   rw 54 (q20 c4) ∷
   rw⁻ 53 (q19 c4) ∷
   rw 52 (q20 c4) ∷
   rw⁻ 51 (q19 c4) ∷
   rw 50 (q21 c4) ∷
   rw 49 (q21 c4) ∷
   rw 48 (q21 c4) ∷
   rw 47 (q22 c4) ∷
   rw 46 (q21 c4) ∷
   rw⁻ 67 (q13 c4) ∷
   rw⁻ 66 (q13 c4) ∷
   rw⁻ 65 (q13 c4) ∷
   rw⁻ 64 (q13 c4) ∷
   rw⁻ 63 (q13 c4) ∷
   rw⁻ 62 (q13 c4) ∷
   rw⁻ 61 (q13 c4) ∷
   rw⁻ 60 (q13 c4) ∷
   rw⁻ 59 (q13 c4) ∷
   rw⁻ 58 (q14 c4) ∷
   rw⁻ 57 (q15 c4) ∷
   rw⁻ 56 (q14 c4) ∷
   rw⁻ 55 (q15 c4) ∷
   rw⁻ 54 (q14 c4) ∷
   rw⁻ 53 (q16 c4) ∷
   rw⁻ 52 (q16 c4) ∷
   rw⁻ 51 (q16 c4) ∷
   rw⁻ 50 (q17 c4) ∷
   rw⁻ 49 (q16 c4) ∷
   rw 70 (q18 c4) ∷
   rw 69 (q18 c4) ∷
   rw 68 (q18 c4) ∷
   rw 67 (q18 c4) ∷
   rw 66 (q18 c4) ∷
   rw 65 (q18 c4) ∷
   rw 64 (q18 c4) ∷
   rw 63 (q18 c4) ∷
   rw 62 (q18 c4) ∷
   rw⁻ 61 (q19 c4) ∷
   rw 60 (q20 c4) ∷
   rw⁻ 59 (q19 c4) ∷
   rw 58 (q20 c4) ∷
   rw⁻ 57 (q19 c4) ∷
   rw 56 (q21 c4) ∷
   rw 55 (q21 c4) ∷
   rw 54 (q21 c4) ∷
   rw 53 (q22 c4) ∷
   rw 52 (q21 c4) ∷
   rw⁻ 73 (q13 c4) ∷
   rw⁻ 72 (q13 c4) ∷
   rw⁻ 71 (q13 c4) ∷
   rw⁻ 70 (q13 c4) ∷
   rw⁻ 69 (q13 c4) ∷
   rw⁻ 68 (q13 c4) ∷
   rw⁻ 67 (q13 c4) ∷
   rw⁻ 66 (q13 c4) ∷
   rw⁻ 65 (q13 c4) ∷
   rw⁻ 64 (q14 c4) ∷
   rw⁻ 63 (q15 c4) ∷
   rw⁻ 62 (q14 c4) ∷
   rw⁻ 61 (q15 c4) ∷
   rw⁻ 60 (q14 c4) ∷
   rw⁻ 59 (q16 c4) ∷
   rw⁻ 58 (q16 c4) ∷
   rw⁻ 57 (q16 c4) ∷
   rw⁻ 56 (q17 c4) ∷
   rw⁻ 55 (q16 c4) ∷
   rw⁻ 58 (q23 c4) ∷
   rw⁻ 57 (q24 c4) ∷
   re 56 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 60 (q25 c4) ∷
   rw⁻ 59 (q26 c4) ∷
   rw⁻ 58 (q27 c4) ∷
   rw⁻ 57 (q26 c4) ∷
   rw⁻ 56 (q28 c4) ∷
   re 57 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 55 (q24 c4) ∷
   rw⁻ 54 (q24 c4) ∷
   re 53 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) ∷
   rw⁻ 55 (q29 c4) ∷
   rw 54 (q30 c4) ∷
   rw⁻ 53 (q29 c4) ∷
   re 54 3 (CK40 ∷ []) ∷
   rw⁻ 52 (q24 c4) ∷
   rw⁻ 51 (q24 c4) ∷
   re 50 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 54 (q25 c4) ∷
   rw⁻ 53 (q26 c4) ∷
   rw⁻ 52 (q27 c4) ∷
   rw⁻ 51 (q26 c4) ∷
   rw⁻ 50 (q28 c4) ∷
   re 51 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 49 (q24 c4) ∷
   rw⁻ 48 (q24 c4) ∷
   re 47 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) ∷
   rw⁻ 49 (q29 c4) ∷
   rw 48 (q30 c4) ∷
   rw⁻ 47 (q29 c4) ∷
   re 48 3 (CK40 ∷ []) ∷
   rw⁻ 46 (q24 c4) ∷
   rw⁻ 45 (q24 c4) ∷
   re 44 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 48 (q25 c4) ∷
   rw⁻ 47 (q26 c4) ∷
   rw⁻ 46 (q27 c4) ∷
   rw⁻ 45 (q26 c4) ∷
   rw⁻ 44 (q28 c4) ∷
   re 45 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 43 (q24 c4) ∷
   rw⁻ 42 (q24 c4) ∷
   rw⁻ 41 (q31 c4) ∷
   rw⁻ 40 (q24 c4) ∷
   rw⁻ 39 (q24 c4) ∷
   rw⁻ 38 (q31 c4) ∷
   rw⁻ 37 (q24 c4) ∷
   rw⁻ 36 (q24 c4) ∷
   rw⁻ 35 (q31 c4) ∷
   rw⁻ 34 (q24 c4) ∷
   rw⁻ 33 (q24 c4) ∷
   rw⁻ 32 (q32 c4) ∷
   rw⁻ 31 (q24 c4) ∷
   rw⁻ 30 (q24 c4) ∷
   re 29 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 33 (q25 c4) ∷
   rw⁻ 32 (q26 c4) ∷
   rw⁻ 31 (q27 c4) ∷
   rw⁻ 30 (q26 c4) ∷
   rw⁻ 29 (q28 c4) ∷
   re 30 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 28 (q24 c4) ∷
   rw⁻ 27 (q24 c4) ∷
   re 26 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) ∷
   rw⁻ 28 (q29 c4) ∷
   rw 27 (q30 c4) ∷
   rw⁻ 26 (q29 c4) ∷
   re 27 3 (CK40 ∷ []) ∷
   rw⁻ 25 (q24 c4) ∷
   rw⁻ 24 (q24 c4) ∷
   re 23 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 27 (q25 c4) ∷
   rw⁻ 26 (q26 c4) ∷
   rw⁻ 25 (q27 c4) ∷
   rw⁻ 24 (q26 c4) ∷
   rw⁻ 23 (q28 c4) ∷
   re 24 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 22 (q24 c4) ∷
   rw⁻ 21 (q24 c4) ∷
   re 20 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) ∷
   rw⁻ 22 (q29 c4) ∷
   rw 21 (q30 c4) ∷
   rw⁻ 20 (q29 c4) ∷
   re 21 3 (CK40 ∷ []) ∷
   rw⁻ 19 (q24 c4) ∷
   rw⁻ 18 (q24 c4) ∷
   re 17 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 21 (q25 c4) ∷
   rw⁻ 20 (q26 c4) ∷
   rw⁻ 19 (q27 c4) ∷
   rw⁻ 18 (q26 c4) ∷
   rw⁻ 17 (q28 c4) ∷
   re 18 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 16 (q24 c4) ∷
   rw⁻ 15 (q24 c4) ∷
   rw⁻ 14 (q31 c4) ∷
   rw⁻ 13 (q24 c4) ∷
   rw⁻ 12 (q24 c4) ∷
   rw⁻ 11 (q31 c4) ∷
   rw⁻ 10 (q24 c4) ∷
   rw⁻ 9 (q24 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw⁻ 6 (q24 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   rw⁻ 3 (q24 c4) ∷
   rw⁻ 2 (q31 c4) ∷
   rw⁻ 1 (q24 c4) ∷
   rw⁻ 59 (q33 c4) ∷
   rw⁻ 58 (q34 c4) ∷
   re 57 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 61 (q35 c4) ∷
   rw⁻ 60 (q36 c4) ∷
   rw⁻ 59 (q37 c4) ∷
   rw⁻ 58 (q36 c4) ∷
   rw⁻ 57 (q38 c4) ∷
   re 58 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 56 (q34 c4) ∷
   rw⁻ 55 (q34 c4) ∷
   re 54 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw⁻ 56 (q39 c4) ∷
   rw 55 (q40 c4) ∷
   rw⁻ 54 (q39 c4) ∷
   re 55 3 (CK40 ∷ []) ∷
   rw⁻ 53 (q34 c4) ∷
   rw⁻ 52 (q34 c4) ∷
   re 51 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 55 (q35 c4) ∷
   rw⁻ 54 (q36 c4) ∷
   rw⁻ 53 (q37 c4) ∷
   rw⁻ 52 (q36 c4) ∷
   rw⁻ 51 (q38 c4) ∷
   re 52 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 50 (q34 c4) ∷
   rw⁻ 49 (q34 c4) ∷
   re 48 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw⁻ 50 (q39 c4) ∷
   rw 49 (q40 c4) ∷
   rw⁻ 48 (q39 c4) ∷
   re 49 3 (CK40 ∷ []) ∷
   rw⁻ 47 (q34 c4) ∷
   rw⁻ 46 (q34 c4) ∷
   re 45 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 49 (q35 c4) ∷
   rw⁻ 48 (q36 c4) ∷
   rw⁻ 47 (q37 c4) ∷
   rw⁻ 46 (q36 c4) ∷
   rw⁻ 45 (q38 c4) ∷
   re 46 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 44 (q34 c4) ∷
   rw⁻ 43 (q34 c4) ∷
   rw 42 (q41 c4) ∷
   rw⁻ 41 (q34 c4) ∷
   rw⁻ 40 (q34 c4) ∷
   rw 39 (q41 c4) ∷ []) Eq.refl
