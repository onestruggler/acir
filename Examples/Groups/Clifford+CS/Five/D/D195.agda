{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D195 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0008 ; wl0010 ; wl0061 ; wl0064 ; wl0159 ; wl0161 ; wl0885 ; wl0886 ; wl0887 ; wl0888 ; wp0461 ; wp0462 ; wp0463 ; wp0464 ; wp0465 ; wp0468)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F5-CS01)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-F4-CS01ᵖ0∣iIᵖ1 ; lem-F4-K1ᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-F4-CS01ᵖ0∣CS01ᵖ1 ; lem-F4-CS01ᵖ0∣K1ᵖ1 ; lem-F4-CS01ᵖ0∣S0ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1)
open import Examples.Groups.Clifford+CS.Five.D.D192 using (lem-DB4K1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12-S1-S1-S1)
open import Examples.Groups.Clifford+CS.Five.D.D194 using (lem-F1-rel-269-rhs)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.TR using (tr03 ; tr04)
-- F1 rel-269: 460 steps
lem-F1-rel-269 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-rel-269 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (run b57)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sb0-1-42-3 ∷ CK41 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 2 (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (sym (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))) ▸
       at 5 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 4 2 (Sw01 ∷ Sb1-0-3-2 ∷ []) (sym (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))) ▸
       at 3 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 2 2 (Sw01 ∷ Bx1-0423 ∷ []) (sym (lem-nat-0-BOX⟨1·0423⟩ (lit c4))) ▸
       at 3 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done

  b1 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b1 = at 1 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CK30 ∷ []) (wl0161 (lit c4)) ▸
       at 1 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 2 (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (sym (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))) ▸
       at 3 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Sw12 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b2 = at 2 2 (Sw01 ∷ Sb1-0-3-2 ∷ []) (sym (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))) ▸
       at 1 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 0 2 (Sw01 ∷ Bx1-0423 ∷ []) (sym (lem-nat-0-BOX⟨1·0423⟩ (lit c4))) ▸
       at 1 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 3 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 7 2 (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (sym (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))) ▸
       at 6 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸ done

  b3 : Chain (Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Sw12 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ Sb1-0-42-3 ∷ Sw12 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b3 = at 5 2 (Sw12 ∷ Sb2-0-3-1 ∷ []) (sym (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))) ▸
       at 4 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸
       at 3 2 (Sw12 ∷ Bx2-0413 ∷ []) (sym (lem-nat-1-BOX⟨2·0413⟩ (lit c4))) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 2 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 2 (Sw12 ∷ CK30 ∷ []) (wl0159 (lit c4)) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b4 : Chain (Sw01 ∷ Sb1-0-42-3 ∷ Sw12 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ Sw12 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b4 = at 3 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (sym (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))) ▸
       at 4 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸
       at 3 2 (Sw12 ∷ Sb2-0-3-1 ∷ []) (sym (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))) ▸
       at 2 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸
       at 1 2 (Sw12 ∷ Bx2-0413 ∷ []) (sym (lem-nat-1-BOX⟨2·0413⟩ (lit c4))) ▸
       at 2 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b5 : Chain (Sw01 ∷ Sw12 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Bx1-0423 ∷ Sw12 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b5 = at 2 3 (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (tr04 c4) ▸
       at 2 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 2 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 3 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸ done

  b6 : Chain (Sw01 ∷ CK40 ∷ Bx1-0423 ∷ Sw12 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sw12 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b6 = at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 4 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 5 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 6 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 2 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 4 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b7 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sw12 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Sw12 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b7 = at 5 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 6 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 7 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 3 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 5 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 6 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸ done

  b8 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Sw12 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b8 = at 7 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 8 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 4 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 6 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 6 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 7 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 8 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b9 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sw12 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b9 = at 9 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 5 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 7 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 8 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 9 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 10 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸ done

  b10 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sw12 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b10 = at 6 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 8 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 7 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 8 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 9 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 10 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 11 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 7 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done

  b11 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b11 = at 9 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 8 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 9 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 10 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 11 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 12 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 8 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 10 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b12 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ Sw12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b12 = at 9 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 10 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 11 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 12 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 13 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 9 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 10 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 11 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸ done

  b13 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ Sw12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b13 = at 12 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 13 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 14 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 16 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 15 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 16 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 17 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 18 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b14 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b14 = at 19 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 15 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 17 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 17 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 18 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 16 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b15 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw34 ∷ Sw12 ∷ CK30 ∷ Sw34 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b15 = at 17 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 18 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 19 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 20 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 21 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 17 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 19 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b16 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw34 ∷ Sw12 ∷ CK30 ∷ Sw34 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b16 = at 19 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 20 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 18 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 19 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 20 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 21 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 22 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b17 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b17 = at 23 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 19 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 21 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 21 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 22 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 20 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 22 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b18 = at 21 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 22 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 23 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 21 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 23 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 23 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 24 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b19 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b19 = at 22 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 24 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 24 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 25 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 23 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 25 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b20 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b20 = at 25 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 26 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 24 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 26 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 26 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 27 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 25 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b21 = at 27 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 27 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 28 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 26 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 28 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 28 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸ done

  b22 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sw12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b22 = at 29 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 27 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 29 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 29 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 30 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 28 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸ done

  b23 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sw12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b23 = at 30 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 31 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 32 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 34 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 33 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 34 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 35 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 36 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b24 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b24 = at 37 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 33 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 35 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 34 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 35 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 36 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 34 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 36 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b25 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw34 ∷ Sw12 ∷ CK30 ∷ Sw34 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b25 = at 35 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 36 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 37 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 38 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 39 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 35 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 37 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 36 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b26 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw34 ∷ Sw12 ∷ CK30 ∷ Sw34 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b26 = at 37 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 38 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 36 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 38 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 37 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 38 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 39 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 40 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b27 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sw12 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b27 = at 41 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 37 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 39 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 38 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 39 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 40 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 41 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 42 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸ done

  b28 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sw12 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b28 = at 38 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 40 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 39 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 40 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 41 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 42 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 43 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 39 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done

  b29 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b29 = at 41 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 40 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 41 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 42 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 40 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 42 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 41 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 42 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸ done

  b30 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b30 = at 43 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 41 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 43 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 42 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 43 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 44 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 42 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 43 2 [] (wl0001 (lit c4)) ▸ done

  b31 : Chain (Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sw01 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b31 = at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 (lit c4))) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b32 : Chain (CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sw01 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b32 = at 3 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 4 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 5 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 1 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸ done

  b33 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sw01 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b33 = at 5 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 6 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 4 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 3 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 4 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 5 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 6 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b34 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sw01 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b34 = at 7 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 5 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 4 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 5 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 6 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 7 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 8 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸ done

  b35 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b35 = at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 6 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 5 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 6 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 7 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 8 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 9 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 5 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b36 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b36 = at 7 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 6 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 7 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 8 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 9 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 10 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 8 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸ done

  b37 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Sw01 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b37 = at 7 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 8 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 9 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 10 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 11 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 7 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 9 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 8 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸ done

  b38 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Sw01 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sw01 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b38 = at 9 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 10 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 11 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 12 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 8 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 9 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 10 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 11 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b39 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sw01 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b39 = at 12 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 13 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 15 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 14 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 15 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 16 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 17 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 18 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸ done

  b40 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Sw01 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b40 = at 14 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 16 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 16 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 (lit c4))) ▸
       at 17 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 15 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸
       at 17 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 16 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸ done

  b41 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Sw01 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw34 ∷ CK31 ∷ Sw01 ∷ Sw34 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b41 = at 17 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 18 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 19 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 20 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 16 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 18 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 18 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 (lit c4))) ▸ done

  b42 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw34 ∷ CK31 ∷ Sw01 ∷ Sw34 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b42 = at 19 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 17 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸
       at 19 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 18 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 19 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 20 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 21 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 22 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸ done

  b43 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw34 ∷ Sw01 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b43 = at 18 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 20 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 20 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 21 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 19 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 21 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸ done

  b44 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw34 ∷ Sw01 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b44 = at 21 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 22 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 20 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 22 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 22 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 23 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 21 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

  b45 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw34 ∷ CS13 ∷ Sw01 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b45 = at 23 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 23 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 24 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 22 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 24 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 24 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸ done

  b46 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw34 ∷ CS13 ∷ Sw01 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b46 = at 25 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 23 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 25 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 25 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 26 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 24 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 26 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b47 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b47 = at 25 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 26 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 27 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 25 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 27 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 27 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 28 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸ done

  b48 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ Sw01 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b48 = at 26 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 28 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 28 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 29 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 27 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 29 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b49 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ Sw01 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b49 = at 30 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 31 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 33 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 32 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 33 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 34 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 35 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 36 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸ done

  b50 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Sw01 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b50 = at 32 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 34 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 33 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 34 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 (lit c4))) ▸
       at 35 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 33 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸
       at 35 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 34 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸ done

  b51 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Sw01 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw34 ∷ CK31 ∷ Sw01 ∷ Sw34 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b51 = at 35 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 36 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 37 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 38 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 34 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 36 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 35 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 36 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 (lit c4))) ▸ done

  b52 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw34 ∷ CK31 ∷ Sw01 ∷ Sw34 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b52 = at 37 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 35 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸
       at 37 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 36 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 37 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 38 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 39 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 40 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸ done

  b53 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b53 = at 36 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 38 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 37 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 38 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 39 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 40 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 41 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 37 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b54 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b54 = at 39 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 38 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 39 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 40 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 41 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 42 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 38 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 40 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b55 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b55 = at 39 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 40 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 41 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 39 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 41 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 40 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 41 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 42 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸ done

  b56 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b56 = at 40 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 42 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 41 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 42 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 43 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 41 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 42 2 [] (wl0002 (lit c4)) ▸
       at 0 42 (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (sym (lem-DB4K1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12-S1-S1-S1 c4)) ▸ done

  b57 : Chain (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b57 = at 42 3 (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (tr03 c4) ▸
       at 42 42 (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (sym (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1 c4)) ▸
       at 0 83 (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (sym (wp0468 c4)) ▸
       at 0 83 (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F1-rel-269-rhs c4)) ▸ done


-- split4[S0 iI S0 S0 S0 CS01 K1 CS01 K1 CS01]: 55 steps
lem-split4S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 : Ws → ⟪ (S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-split4S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (S0 ∷ ι ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 9 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 8 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 7 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 6 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 5 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 4 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4) ▸
       at 3 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4) ▸
       at 2 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4) ▸ done

  b1 : Chain (S0 ∷ ι ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b1 = at 1 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl0886 (lit c4))) ▸
       at 0 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4) ▸
       at 3 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (wp0462 c4) ▸
       at 7 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4) ▸
       at 6 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 11 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 10 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4) ▸
       at 9 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸ done

  b2 : Chain (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b2 = at 15 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 14 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 13 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4) ▸
       at 12 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 19 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 18 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 17 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 16 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸ done

  b3 : Chain (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b3 = at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 23 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 22 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 21 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 20 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 19 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 18 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 27 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸ done

  b4 : Chain (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b4 = at 26 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 25 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 24 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 23 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 22 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸
       at 21 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 31 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 30 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4)) ▸ done

  b5 : Chain (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b5 = at 29 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 28 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 27 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 26 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 25 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 24 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 35 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 34 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b6 : Chain (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b6 = at 33 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 32 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 29 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 28 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸
       at 27 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸ done


-- split4[iI S0 S0 S0 CS01 K1 CS01 K1 CS01]: 45 steps
lem-split4iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 : Ws → ⟪ (ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-split4iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (ι ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 8 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 7 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 6 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 5 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 4 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 3 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4) ▸
       at 2 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4) ▸
       at 1 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4) ▸ done

  b1 : Chain (ι ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b1 = at 0 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl0886 (lit c4))) ▸
       at 3 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4) ▸
       at 7 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 6 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4) ▸
       at 11 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 10 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 9 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸ done

  b2 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b2 = at 14 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 13 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 12 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸
       at 19 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 18 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 17 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 16 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 15 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b3 = at 23 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 22 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 21 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 20 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 19 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 18 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸
       at 27 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 26 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4)) ▸ done

  b4 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b4 = at 25 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 24 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 23 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 22 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 21 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 29 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸ done

  b5 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b5 = at 28 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 27 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 26 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 25 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 24 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸ done

