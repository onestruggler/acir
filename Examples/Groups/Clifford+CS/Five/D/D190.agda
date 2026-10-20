{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D190 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0887 ; wl0888 ; wl0889 ; wl0890 ; wl0891 ; wl0892 ; wl0894 ; wl0895 ; wl0896 ; wl0897 ; wl0898 ; wl0899)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-SB2-at011220)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-F4-K1ᵖ0∣CS12ᵖ1 ; lem-F4-S2ᵖ0∣CS12ᵖ1 ; lem-F4-iIᵖ0∣CS12ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-F4-CS12ᵖ0∣S1ᵖ1 ; lem-F4-CS12ᵖ0∣S2ᵖ1 ; lem-F4-CS12ᵖ0∣iIᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D178 using (lem-F4-CS12ᵖ0∣K1ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D179 using (lem-F4-CS12ᵖ0∣CS12ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-split4CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 ; lem-split4iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ []) (lem-SB2-at011220 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (lem-split4CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (lem-split4iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl0889 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS12ᵖ1 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (wl0890 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (wl0894 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (wl0891 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (wl0898 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (wl0899 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S1ᵖ1 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣iIᵖ1 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4))

-- DB4[K1 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 S2 iI S2 S2 S2 CS12 K1 CS12 K1 CS12 S1 S1 S1 S1 S1 S1 S1 S1 S1 iI S2 S2 S2 CS12 K1 CS12 K1 CS12 CS12 CS12 S1 S1 S1] part0: 245 steps
lem-DB4K1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12-S1-S1-S1-part0 : Ws → ⟪ (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-DB4K1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12-S1-S1-S1-part0 c4 = derive (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 3 (q2 c4) ∷
   rw 76 (q3 c4) ∷
   rw 75 (q4 c4) ∷
   rw 74 (q4 c4) ∷
   rw 73 (q4 c4) ∷
   rw 72 (q4 c4) ∷
   rw 71 (q4 c4) ∷
   rw 70 (q4 c4) ∷
   rw 69 (q4 c4) ∷
   rw 68 (q4 c4) ∷
   rw 67 (q4 c4) ∷
   rw⁻ 66 (q5 c4) ∷
   rw 65 (q6 c4) ∷
   rw⁻ 64 (q5 c4) ∷
   rw 63 (q6 c4) ∷
   rw⁻ 62 (q5 c4) ∷
   rw 61 (q7 c4) ∷
   rw 60 (q7 c4) ∷
   rw 59 (q7 c4) ∷
   rw 58 (q8 c4) ∷
   rw 57 (q7 c4) ∷
   rw⁻ 56 (q5 c4) ∷
   rw⁻ 55 (q5 c4) ∷
   rw⁻ 54 (q5 c4) ∷
   rw⁻ 53 (q5 c4) ∷
   rw⁻ 52 (q5 c4) ∷
   rw⁻ 51 (q5 c4) ∷
   rw 78 (q9 c4) ∷
   rw 77 (q9 c4) ∷
   rw 76 (q9 c4) ∷
   rw 75 (q9 c4) ∷
   rw 74 (q9 c4) ∷
   rw 73 (q9 c4) ∷
   rw 72 (q9 c4) ∷
   rw 71 (q9 c4) ∷
   rw 70 (q9 c4) ∷
   rw⁻ 69 (q10 c4) ∷
   rw 68 (q11 c4) ∷
   rw⁻ 67 (q10 c4) ∷
   rw 66 (q11 c4) ∷
   rw⁻ 65 (q10 c4) ∷
   rw 64 (q12 c4) ∷
   rw 63 (q12 c4) ∷
   rw 62 (q12 c4) ∷
   rw 61 (q13 c4) ∷
   rw 60 (q12 c4) ∷
   rw⁻ 59 (q10 c4) ∷
   rw⁻ 58 (q10 c4) ∷
   rw⁻ 57 (q10 c4) ∷
   rw⁻ 56 (q10 c4) ∷
   rw⁻ 55 (q10 c4) ∷
   rw⁻ 54 (q10 c4) ∷
   rw 81 (q9 c4) ∷
   rw 80 (q9 c4) ∷
   rw 79 (q9 c4) ∷
   rw 78 (q9 c4) ∷
   rw 77 (q9 c4) ∷
   rw 76 (q9 c4) ∷
   rw 75 (q9 c4) ∷
   rw 74 (q9 c4) ∷
   rw 73 (q9 c4) ∷
   rw⁻ 72 (q10 c4) ∷
   rw 71 (q11 c4) ∷
   rw⁻ 70 (q10 c4) ∷
   rw 69 (q11 c4) ∷
   rw⁻ 68 (q10 c4) ∷
   rw 67 (q12 c4) ∷
   rw 66 (q12 c4) ∷
   rw 65 (q12 c4) ∷
   rw 64 (q13 c4) ∷
   rw 63 (q12 c4) ∷
   rw⁻ 62 (q10 c4) ∷
   rw⁻ 61 (q10 c4) ∷
   rw⁻ 60 (q10 c4) ∷
   rw⁻ 59 (q10 c4) ∷
   rw⁻ 58 (q10 c4) ∷
   rw⁻ 57 (q10 c4) ∷
   rw 84 (q9 c4) ∷
   rw 83 (q9 c4) ∷
   rw 82 (q9 c4) ∷
   rw 81 (q9 c4) ∷
   rw 80 (q9 c4) ∷
   rw 79 (q9 c4) ∷
   rw 78 (q9 c4) ∷
   rw 77 (q9 c4) ∷
   rw 76 (q9 c4) ∷
   rw⁻ 75 (q10 c4) ∷
   rw 74 (q11 c4) ∷
   rw⁻ 73 (q10 c4) ∷
   rw 72 (q11 c4) ∷
   rw⁻ 71 (q10 c4) ∷
   rw 70 (q12 c4) ∷
   rw 69 (q12 c4) ∷
   rw 68 (q12 c4) ∷
   rw 67 (q13 c4) ∷
   rw 66 (q12 c4) ∷
   rw⁻ 65 (q10 c4) ∷
   rw⁻ 64 (q10 c4) ∷
   rw⁻ 63 (q10 c4) ∷
   rw⁻ 62 (q10 c4) ∷
   rw⁻ 61 (q10 c4) ∷
   rw⁻ 60 (q10 c4) ∷
   rw⁻ 87 (q14 c4) ∷
   rw⁻ 86 (q14 c4) ∷
   rw⁻ 85 (q14 c4) ∷
   rw⁻ 84 (q14 c4) ∷
   rw⁻ 83 (q14 c4) ∷
   rw⁻ 82 (q14 c4) ∷
   rw⁻ 81 (q14 c4) ∷
   rw⁻ 80 (q14 c4) ∷
   rw⁻ 79 (q14 c4) ∷
   rw⁻ 78 (q15 c4) ∷
   rw⁻ 77 (q16 c4) ∷
   rw⁻ 76 (q15 c4) ∷
   rw⁻ 75 (q16 c4) ∷
   rw⁻ 74 (q15 c4) ∷
   rw⁻ 73 (q17 c4) ∷
   rw⁻ 72 (q17 c4) ∷
   rw⁻ 71 (q17 c4) ∷
   rw⁻ 70 (q18 c4) ∷
   rw⁻ 69 (q17 c4) ∷
   rw⁻ 68 (q15 c4) ∷
   rw⁻ 67 (q15 c4) ∷
   rw⁻ 66 (q15 c4) ∷
   rw⁻ 65 (q15 c4) ∷
   rw⁻ 64 (q15 c4) ∷
   rw⁻ 63 (q15 c4) ∷
   rw 90 (q19 c4) ∷
   rw 89 (q19 c4) ∷
   rw 88 (q19 c4) ∷
   rw 87 (q19 c4) ∷
   rw 86 (q19 c4) ∷
   rw 85 (q19 c4) ∷
   rw 84 (q19 c4) ∷
   rw 83 (q19 c4) ∷
   rw 82 (q19 c4) ∷
   rw⁻ 81 (q20 c4) ∷
   rw 80 (q21 c4) ∷
   rw⁻ 79 (q20 c4) ∷
   rw 78 (q21 c4) ∷
   rw⁻ 77 (q20 c4) ∷
   rw 76 (q22 c4) ∷
   rw 75 (q22 c4) ∷
   rw 74 (q22 c4) ∷
   rw 73 (q23 c4) ∷
   rw 72 (q22 c4) ∷
   rw⁻ 71 (q20 c4) ∷
   rw⁻ 70 (q20 c4) ∷
   rw⁻ 69 (q20 c4) ∷
   rw⁻ 68 (q20 c4) ∷
   rw⁻ 67 (q20 c4) ∷
   rw⁻ 66 (q20 c4) ∷
   rw⁻ 93 (q14 c4) ∷
   rw⁻ 92 (q14 c4) ∷
   rw⁻ 91 (q14 c4) ∷
   rw⁻ 90 (q14 c4) ∷
   rw⁻ 89 (q14 c4) ∷
   rw⁻ 88 (q14 c4) ∷
   rw⁻ 87 (q14 c4) ∷
   rw⁻ 86 (q14 c4) ∷
   rw⁻ 85 (q14 c4) ∷
   rw⁻ 84 (q15 c4) ∷
   rw⁻ 83 (q16 c4) ∷
   rw⁻ 82 (q15 c4) ∷
   rw⁻ 81 (q16 c4) ∷
   rw⁻ 80 (q15 c4) ∷
   rw⁻ 79 (q17 c4) ∷
   rw⁻ 78 (q17 c4) ∷
   rw⁻ 77 (q17 c4) ∷
   rw⁻ 76 (q18 c4) ∷
   rw⁻ 75 (q17 c4) ∷
   rw⁻ 74 (q15 c4) ∷
   rw⁻ 73 (q15 c4) ∷
   rw⁻ 72 (q15 c4) ∷
   rw⁻ 71 (q15 c4) ∷
   rw⁻ 70 (q15 c4) ∷
   rw⁻ 69 (q15 c4) ∷
   rw 96 (q19 c4) ∷
   rw 95 (q19 c4) ∷
   rw 94 (q19 c4) ∷
   rw 93 (q19 c4) ∷
   rw 92 (q19 c4) ∷
   rw 91 (q19 c4) ∷
   rw 90 (q19 c4) ∷
   rw 89 (q19 c4) ∷
   rw 88 (q19 c4) ∷
   rw⁻ 87 (q20 c4) ∷
   rw 86 (q21 c4) ∷
   rw⁻ 85 (q20 c4) ∷
   rw 84 (q21 c4) ∷
   rw⁻ 83 (q20 c4) ∷
   rw 82 (q22 c4) ∷
   rw 81 (q22 c4) ∷
   rw 80 (q22 c4) ∷
   rw 79 (q23 c4) ∷
   rw 78 (q22 c4) ∷
   rw⁻ 77 (q20 c4) ∷
   rw⁻ 76 (q20 c4) ∷
   rw⁻ 75 (q20 c4) ∷
   rw⁻ 74 (q20 c4) ∷
   rw⁻ 73 (q20 c4) ∷
   rw⁻ 72 (q20 c4) ∷
   rw⁻ 99 (q14 c4) ∷
   rw⁻ 98 (q14 c4) ∷
   rw⁻ 97 (q14 c4) ∷
   rw⁻ 96 (q14 c4) ∷
   rw⁻ 95 (q14 c4) ∷
   rw⁻ 94 (q14 c4) ∷
   rw⁻ 93 (q14 c4) ∷
   rw⁻ 92 (q14 c4) ∷
   rw⁻ 91 (q14 c4) ∷
   rw⁻ 90 (q15 c4) ∷
   rw⁻ 89 (q16 c4) ∷
   rw⁻ 88 (q15 c4) ∷
   rw⁻ 87 (q16 c4) ∷
   rw⁻ 86 (q15 c4) ∷
   rw⁻ 85 (q17 c4) ∷
   rw⁻ 84 (q17 c4) ∷
   rw⁻ 83 (q17 c4) ∷
   rw⁻ 82 (q18 c4) ∷
   rw⁻ 81 (q17 c4) ∷
   rw⁻ 80 (q15 c4) ∷
   rw⁻ 79 (q15 c4) ∷
   rw⁻ 78 (q15 c4) ∷
   rw⁻ 77 (q15 c4) ∷
   rw⁻ 76 (q15 c4) ∷
   rw⁻ 75 (q15 c4) ∷
   rw⁻ 102 (q14 c4) ∷
   rw⁻ 101 (q14 c4) ∷
   rw⁻ 100 (q14 c4) ∷
   rw⁻ 99 (q14 c4) ∷
   rw⁻ 98 (q14 c4) ∷
   rw⁻ 97 (q14 c4) ∷
   rw⁻ 96 (q14 c4) ∷
   rw⁻ 95 (q14 c4) ∷
   rw⁻ 94 (q14 c4) ∷
   rw⁻ 93 (q15 c4) ∷
   rw⁻ 92 (q16 c4) ∷
   rw⁻ 91 (q15 c4) ∷
   rw⁻ 90 (q16 c4) ∷
   rw⁻ 89 (q15 c4) ∷
   rw⁻ 88 (q17 c4) ∷
   rw⁻ 87 (q17 c4) ∷
   rw⁻ 86 (q17 c4) ∷ []) Eq.refl
