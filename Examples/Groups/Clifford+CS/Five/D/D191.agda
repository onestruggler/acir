{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D191 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0064 ; wl0161)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-F4-CS12ᵖ0∣S1ᵖ1 ; lem-F4-CS12ᵖ0∣S2ᵖ1 ; lem-F4-CS12ᵖ0∣iIᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D178 using (lem-F4-CS12ᵖ0∣K1ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D179 using (lem-F4-CS12ᵖ0∣CS12ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣iIᵖ1 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S1ᵖ1 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw01 ∷ Toff324 ∷ []) (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw01 ∷ Sb1-0-3-2 ∷ []) (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q13 : Ws → Eqn
  q13 c4 = eqn (CK31 ∷ Sw01 ∷ []) (Sw01 ∷ CK30 ∷ []) (wl0161 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw12 ∷ Sb2-0-3-1 ∷ []) (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))

-- DB4[K1 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 S2 iI S2 S2 S2 CS12 K1 CS12 K1 CS12 S1 S1 S1 S1 S1 S1 S1 S1 S1 iI S2 S2 S2 CS12 K1 CS12 K1 CS12 CS12 CS12 S1 S1 S1] part1: 236 steps
lem-DB4K1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12-S1-S1-S1-part1 : Ws → ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sw12 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-DB4K1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12-S1-S1-S1-part1 c4 = derive (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sw12 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw⁻ 85 (q1 c4) ∷
   rw⁻ 84 (q2 c4) ∷
   rw⁻ 83 (q3 c4) ∷
   rw⁻ 82 (q3 c4) ∷
   rw⁻ 81 (q3 c4) ∷
   rw⁻ 80 (q3 c4) ∷
   rw⁻ 79 (q3 c4) ∷
   rw⁻ 78 (q3 c4) ∷
   rw⁻ 105 (q4 c4) ∷
   rw⁻ 104 (q4 c4) ∷
   rw⁻ 103 (q4 c4) ∷
   rw⁻ 102 (q4 c4) ∷
   rw⁻ 101 (q4 c4) ∷
   rw⁻ 100 (q4 c4) ∷
   rw⁻ 99 (q4 c4) ∷
   rw⁻ 98 (q4 c4) ∷
   rw⁻ 97 (q4 c4) ∷
   rw⁻ 96 (q3 c4) ∷
   rw⁻ 95 (q5 c4) ∷
   rw⁻ 94 (q3 c4) ∷
   rw⁻ 93 (q5 c4) ∷
   rw⁻ 92 (q3 c4) ∷
   rw⁻ 91 (q2 c4) ∷
   rw⁻ 90 (q2 c4) ∷
   rw⁻ 89 (q2 c4) ∷
   rw⁻ 88 (q1 c4) ∷
   rw⁻ 87 (q2 c4) ∷
   rw⁻ 86 (q3 c4) ∷
   rw⁻ 85 (q3 c4) ∷
   rw⁻ 84 (q3 c4) ∷
   rw⁻ 83 (q3 c4) ∷
   rw⁻ 82 (q3 c4) ∷
   rw⁻ 81 (q3 c4) ∷
   rw⁻ 84 (q6 c4) ∷
   rw⁻ 83 (q7 c4) ∷
   re 82 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 86 (q8 c4) ∷
   rw⁻ 85 (q9 c4) ∷
   rw⁻ 84 (q10 c4) ∷
   rw⁻ 83 (q9 c4) ∷
   rw⁻ 82 (q11 c4) ∷
   re 83 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 81 (q7 c4) ∷
   rw⁻ 80 (q7 c4) ∷
   re 79 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 83 (q8 c4) ∷
   rw⁻ 82 (q9 c4) ∷
   rw⁻ 81 (q10 c4) ∷
   rw⁻ 80 (q9 c4) ∷
   rw⁻ 79 (q11 c4) ∷
   re 80 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 78 (q7 c4) ∷
   rw⁻ 77 (q7 c4) ∷
   re 76 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 80 (q8 c4) ∷
   rw⁻ 79 (q9 c4) ∷
   rw⁻ 78 (q10 c4) ∷
   rw⁻ 77 (q9 c4) ∷
   rw⁻ 76 (q11 c4) ∷
   re 77 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 75 (q7 c4) ∷
   rw⁻ 74 (q7 c4) ∷
   re 73 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) ∷
   rw⁻ 75 (q12 c4) ∷
   rw 74 (q13 c4) ∷
   rw⁻ 73 (q12 c4) ∷
   re 74 3 (CK40 ∷ []) ∷
   rw⁻ 72 (q7 c4) ∷
   rw⁻ 71 (q7 c4) ∷
   re 70 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 74 (q8 c4) ∷
   rw⁻ 73 (q9 c4) ∷
   rw⁻ 72 (q10 c4) ∷
   rw⁻ 71 (q9 c4) ∷
   rw⁻ 70 (q11 c4) ∷
   re 71 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 69 (q7 c4) ∷
   rw⁻ 68 (q7 c4) ∷
   re 67 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) ∷
   rw⁻ 69 (q12 c4) ∷
   rw 68 (q13 c4) ∷
   rw⁻ 67 (q12 c4) ∷
   re 68 3 (CK40 ∷ []) ∷
   rw⁻ 66 (q7 c4) ∷
   rw⁻ 65 (q7 c4) ∷
   re 64 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 68 (q8 c4) ∷
   rw⁻ 67 (q9 c4) ∷
   rw⁻ 66 (q10 c4) ∷
   rw⁻ 65 (q9 c4) ∷
   rw⁻ 64 (q11 c4) ∷
   re 65 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 63 (q7 c4) ∷
   rw⁻ 62 (q7 c4) ∷
   rw⁻ 61 (q14 c4) ∷
   rw⁻ 60 (q7 c4) ∷
   rw⁻ 59 (q7 c4) ∷
   rw⁻ 58 (q14 c4) ∷
   rw⁻ 57 (q7 c4) ∷
   rw⁻ 56 (q7 c4) ∷
   rw⁻ 55 (q14 c4) ∷
   rw⁻ 54 (q7 c4) ∷
   rw⁻ 53 (q7 c4) ∷
   rw⁻ 52 (q15 c4) ∷
   rw⁻ 51 (q7 c4) ∷
   rw⁻ 50 (q7 c4) ∷
   re 49 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 53 (q8 c4) ∷
   rw⁻ 52 (q9 c4) ∷
   rw⁻ 51 (q10 c4) ∷
   rw⁻ 50 (q9 c4) ∷
   rw⁻ 49 (q11 c4) ∷
   re 50 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 48 (q7 c4) ∷
   rw⁻ 47 (q7 c4) ∷
   re 46 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) ∷
   rw⁻ 48 (q12 c4) ∷
   rw 47 (q13 c4) ∷
   rw⁻ 46 (q12 c4) ∷
   re 47 3 (CK40 ∷ []) ∷
   rw⁻ 45 (q7 c4) ∷
   rw⁻ 44 (q7 c4) ∷
   re 43 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 47 (q8 c4) ∷
   rw⁻ 46 (q9 c4) ∷
   rw⁻ 45 (q10 c4) ∷
   rw⁻ 44 (q9 c4) ∷
   rw⁻ 43 (q11 c4) ∷
   re 44 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 42 (q7 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   re 40 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) ∷
   rw⁻ 42 (q12 c4) ∷
   rw 41 (q13 c4) ∷
   rw⁻ 40 (q12 c4) ∷
   re 41 3 (CK40 ∷ []) ∷
   rw⁻ 39 (q7 c4) ∷
   rw⁻ 38 (q7 c4) ∷
   re 37 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 41 (q8 c4) ∷
   rw⁻ 40 (q9 c4) ∷
   rw⁻ 39 (q10 c4) ∷
   rw⁻ 38 (q9 c4) ∷
   rw⁻ 37 (q11 c4) ∷
   re 38 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 36 (q7 c4) ∷
   rw⁻ 35 (q7 c4) ∷
   rw⁻ 34 (q14 c4) ∷
   rw⁻ 33 (q7 c4) ∷
   rw⁻ 32 (q7 c4) ∷
   rw⁻ 31 (q14 c4) ∷
   rw⁻ 30 (q7 c4) ∷
   rw⁻ 29 (q7 c4) ∷
   rw⁻ 28 (q14 c4) ∷
   rw⁻ 27 (q7 c4) ∷
   rw⁻ 26 (q7 c4) ∷
   rw⁻ 25 (q15 c4) ∷
   rw⁻ 24 (q7 c4) ∷
   rw⁻ 23 (q7 c4) ∷
   rw⁻ 22 (q14 c4) ∷
   rw⁻ 21 (q7 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   re 19 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 21 (q10 c4) ∷
   rw⁻ 20 (q9 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   re 20 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 18 (q7 c4) ∷
   rw⁻ 17 (q7 c4) ∷
   re 16 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 20 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q10 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw⁻ 16 (q11 c4) ∷
   re 17 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 15 (q7 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   re 13 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 17 (q8 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw⁻ 15 (q10 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   rw⁻ 13 (q11 c4) ∷
   re 14 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 12 (q7 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   re 10 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 14 (q8 c4) ∷
   rw⁻ 13 (q9 c4) ∷
   rw⁻ 12 (q10 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw⁻ 10 (q11 c4) ∷
   re 11 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 9 (q7 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   re 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 11 (q8 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw⁻ 9 (q10 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   re 8 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 8 (q8 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   rw⁻ 6 (q10 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 5 5 (Sb1-0-42-3 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 85 (q16 c4) ∷
   rw⁻ 84 (q17 c4) ∷
   re 83 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 87 (q18 c4) ∷
   rw⁻ 86 (q19 c4) ∷
   rw⁻ 85 (q20 c4) ∷
   rw⁻ 84 (q19 c4) ∷
   rw⁻ 83 (q21 c4) ∷
   re 84 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 82 (q17 c4) ∷
   rw⁻ 81 (q17 c4) ∷
   re 80 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw⁻ 84 (q18 c4) ∷
   rw⁻ 83 (q19 c4) ∷
   rw⁻ 82 (q20 c4) ∷
   rw⁻ 81 (q19 c4) ∷
   rw⁻ 80 (q21 c4) ∷
   re 81 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 79 (q17 c4) ∷
   rw⁻ 78 (q17 c4) ∷
   re 77 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷ []) Eq.refl
