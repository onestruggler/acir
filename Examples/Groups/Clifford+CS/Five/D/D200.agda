{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D200 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0008 ; wl0010 ; wl0011 ; wl0015 ; wl0017 ; wl0061 ; wl0064 ; wl0159 ; wl0160 ; wl0161 ; wl0162 ; wl0163 ; wl0164 ; wl0900 ; wl0901 ; wl0902 ; wl0903 ; wl0904 ; wl0905 ; wl0906 ; wl0907 ; wl0908 ; wl0909 ; wp0469 ; wp0470 ; wp0471 ; wp0472)
open import Examples.Groups.Clifford+CS.Five.Chain
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
-- F1 rel-272: 349 steps
lem-F1-rel-272 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-rel-272 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (run b43)))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 5 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 8 2 (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (sym (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))) ▸
       at 7 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 6 2 (Sw01 ∷ Sb1-0-3-2 ∷ []) (sym (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))) ▸
       at 5 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 4 2 (Sw01 ∷ Bx1-0423 ∷ []) (sym (lem-nat-0-BOX⟨1·0423⟩ (lit c4))) ▸
       at 5 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done

  b1 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b1 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 7 2 (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (sym (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))) ▸
       at 6 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 5 2 (Sw01 ∷ Sb1-0-3-2 ∷ []) (sym (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))) ▸
       at 4 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (Sw01 ∷ Bx1-0423 ∷ []) (sym (lem-nat-0-BOX⟨1·0423⟩ (lit c4))) ▸
       at 4 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ CK31 ∷ Sw01 ∷ Sw34 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b2 = at 6 2 (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (sym (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))) ▸
       at 5 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 4 2 (Sw01 ∷ Sb1-0-3-2 ∷ []) (sym (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))) ▸
       at 3 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 2 2 (Sw01 ∷ Bx1-0423 ∷ []) (sym (lem-nat-0-BOX⟨1·0423⟩ (lit c4))) ▸
       at 3 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done

  b3 : Chain (Sb0-1-42-3 ∷ Sw34 ∷ CK31 ∷ Sw01 ∷ Sw34 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Sw01 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b3 = at 2 2 (Sw01 ∷ CK30 ∷ []) (wl0161 (lit c4)) ▸
       at 1 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 2 (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (sym (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))) ▸
       at 3 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 2 2 (Sw01 ∷ Sb1-0-3-2 ∷ []) (sym (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))) ▸
       at 1 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸ done

  b4 : Chain (Bx0-1423 ∷ Sw01 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Sw12 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b4 = at 0 2 (Sw01 ∷ Bx1-0423 ∷ []) (sym (lem-nat-0-BOX⟨1·0423⟩ (lit c4))) ▸
       at 1 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 5 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 9 2 (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (sym (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))) ▸
       at 8 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸
       at 7 2 (Sw12 ∷ Sb2-0-3-1 ∷ []) (sym (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))) ▸
       at 6 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸ done

  b5 : Chain (Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Sw12 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b5 = at 5 2 (Sw12 ∷ Bx2-0413 ∷ []) (sym (lem-nat-1-BOX⟨2·0413⟩ (lit c4))) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 4 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 8 2 (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (sym (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))) ▸
       at 7 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸
       at 6 2 (Sw12 ∷ Sb2-0-3-1 ∷ []) (sym (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))) ▸
       at 5 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸
       at 4 2 (Sw12 ∷ Bx2-0413 ∷ []) (sym (lem-nat-1-BOX⟨2·0413⟩ (lit c4))) ▸ done

  b6 : Chain (Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sw12 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b6 = at 5 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 7 2 (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (sym (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))) ▸
       at 6 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸
       at 5 2 (Sw12 ∷ Sb2-0-3-1 ∷ []) (sym (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))) ▸
       at 4 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸
       at 3 2 (Sw12 ∷ Bx2-0413 ∷ []) (sym (lem-nat-1-BOX⟨2·0413⟩ (lit c4))) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b7 : Chain (Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sw12 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Sw12 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b7 = at 2 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 2 (Sw12 ∷ CK30 ∷ []) (wl0159 (lit c4)) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (sym (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))) ▸
       at 4 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸ done

  b8 : Chain (Sw01 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Sw12 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ Sw34 ∷ CK30 ∷ Sw12 ∷ Sw34 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b8 = at 3 2 (Sw12 ∷ Sb2-0-3-1 ∷ []) (sym (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))) ▸
       at 2 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸
       at 1 2 (Sw12 ∷ Bx2-0413 ∷ []) (sym (lem-nat-1-BOX⟨2·0413⟩ (lit c4))) ▸
       at 2 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 2 5 (CK40 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (tr09 c4) ▸
       at 2 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 2 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸ done

  b9 : Chain (Sw01 ∷ Sw34 ∷ CK30 ∷ Sw12 ∷ Sw34 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b9 = at 3 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 3 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 4 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 5 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 6 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 8 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b10 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ Sw34 ∷ Sw12 ∷ CK30 ∷ Sw34 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b10 = at 7 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 8 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 9 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 10 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 11 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 7 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 9 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b11 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ Sw34 ∷ Sw12 ∷ CK30 ∷ Sw34 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b11 = at 9 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 9 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 10 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 11 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 12 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b12 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b12 = at 13 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 9 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 11 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 11 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 12 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 10 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b13 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b13 = at 11 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 12 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 13 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 14 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 15 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 11 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 13 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b14 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b14 = at 13 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 14 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 12 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 14 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 14 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 15 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 13 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b15 = at 15 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 15 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 16 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 14 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 16 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 16 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸ done

  b16 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b16 = at 17 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 15 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 17 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 17 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 18 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 16 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 18 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b17 = at 17 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 18 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 19 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 17 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 19 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 19 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 20 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b18 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b18 = at 18 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 20 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 20 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 21 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 19 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 21 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b19 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b19 = at 21 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 22 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 20 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 22 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 23 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 24 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 26 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b20 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ Sw34 ∷ Sw12 ∷ CK30 ∷ Sw34 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b20 = at 25 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 26 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 27 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 28 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 29 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 25 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 27 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b21 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ Sw34 ∷ Sw12 ∷ CK30 ∷ Sw34 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b21 = at 27 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 28 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 26 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 28 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 27 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 28 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 29 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 30 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b22 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b22 = at 31 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 27 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 29 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 29 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 30 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 28 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 30 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b23 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b23 = at 29 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 30 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 31 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 32 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 33 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 29 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 31 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b24 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b24 = at 31 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 32 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 30 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 32 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 31 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 32 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 33 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 31 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (Sw01 ∷ CK40 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sw34 ∷ Sw01 ∷ CK30 ∷ Sw34 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b25 = at 33 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 33 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 34 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 32 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 33 2 [] (wl0001 (lit c4)) ▸
       at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸ done

  b26 : Chain (Sw34 ∷ Sw01 ∷ CK30 ∷ Sw34 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b26 = at 1 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 (lit c4))) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 2 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 3 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 4 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 5 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b27 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b27 = at 7 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 6 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 7 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 8 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 9 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 10 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 8 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b28 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b28 = at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 8 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 (lit c4))) ▸
       at 9 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 7 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 8 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 9 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 10 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸ done

  b29 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b29 = at 11 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 12 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 8 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 10 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 10 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 (lit c4))) ▸
       at 11 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 9 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b30 = at 11 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 10 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 11 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 12 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 13 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 14 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 10 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 12 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b31 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b31 = at 11 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 12 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 13 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 11 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 13 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 14 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸ done

  b32 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw34 ∷ Sw01 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b32 = at 12 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 14 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 14 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 15 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 13 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 15 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸ done

  b33 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw34 ∷ Sw01 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b33 = at 15 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 16 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 14 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 16 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 16 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 17 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 15 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

  b34 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw34 ∷ CS13 ∷ Sw01 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b34 = at 17 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 17 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 18 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 16 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 18 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 18 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸ done

  b35 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw34 ∷ CS13 ∷ Sw01 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b35 = at 19 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 17 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 19 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 19 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 20 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 18 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 20 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b36 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b36 = at 19 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 20 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 21 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 19 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 21 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 22 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 23 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b37 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b37 = at 25 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 24 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 25 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 26 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 27 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 28 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 24 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 26 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b38 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b38 = at 25 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 26 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 (lit c4))) ▸
       at 27 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 25 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸
       at 27 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 26 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 27 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 28 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸ done

  b39 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b39 = at 29 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 30 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 26 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 28 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 28 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 (lit c4))) ▸
       at 29 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 27 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done

  b40 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b40 = at 29 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 28 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 29 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 30 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 31 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 32 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 28 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 30 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b41 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b41 = at 29 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 30 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 31 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 29 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 31 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 31 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 32 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸ done

  b42 : Chain (CK41 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ CS04 ∷ Sw01 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b42 = at 30 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 32 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 31 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 32 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 33 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 31 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 [] (wl0002 (lit c4)) ▸
       at 0 32 (CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (sym (lem-DB4K1-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-S1-S1-S1 c4)) ▸ done

  b43 : Chain (CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b43 = at 35 0 (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (tr08 c4) ▸
       at 33 5 (CK41 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (tr07 c4) ▸
       at 33 32 (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (sym (lem-DB4K1-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1 c4)) ▸
       at 0 65 (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (sym (wp0469 c4)) ▸
       at 0 67 (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F1-rel-272-rhs c4)) ▸ done


-- tr order-I at 3: 1 steps
lem-tr-order-I-at-3 : Ws → ⟪ (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-I-at-3 c4 = run b0
  where
  b0 : Chain (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) []
  b0 = at 0 4 [] (wl0900 (lit c4)) ▸ done


-- tr order-I at 4: 1 steps
lem-tr-order-I-at-4 : Ws → ⟪ (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-I-at-4 c4 = run b0
  where
  b0 : Chain (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) []
  b0 = at 0 4 [] (wl0900 (lit c4)) ▸ done


-- tr order-S at 2: 1 steps
lem-tr-order-S-at-2 : Ws → ⟪ (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-S-at-2 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) []
  b0 = at 0 4 [] (wl0902 (lit c4)) ▸ done


-- tr order-S at 3: 1 steps
lem-tr-order-S-at-3 : Ws → ⟪ (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-S-at-3 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) []
  b0 = at 0 4 [] (wl0903 (lit c4)) ▸ done


-- tr order-K at 2: 1 steps
lem-tr-order-K-at-2 : Ws → ⟪ (CK42 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-tr-order-K-at-2 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 2 (S4 ∷ S4 ∷ S4 ∷ []) (wl0905 (lit c4)) ▸ done


-- tr order-K at 3: 1 steps
lem-tr-order-K-at-3 : Ws → ⟪ (CK43 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-tr-order-K-at-3 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 2 (S4 ∷ S4 ∷ S4 ∷ []) (wl0906 (lit c4)) ▸ done


-- tr order-SK at 2: 1 steps
lem-tr-order-SK-at-2 : Ws → ⟪ (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-tr-order-SK-at-2 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 6 (S4 ∷ S4 ∷ S4 ∷ []) (wl0908 (lit c4)) ▸ done


-- tr order-SK at 3: 1 steps
lem-tr-order-SK-at-3 : Ws → ⟪ (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-tr-order-SK-at-3 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 6 (S4 ∷ S4 ∷ S4 ∷ []) (wl0909 (lit c4)) ▸ done


-- F1 order-CS @1221: 7 steps
lem-F1-order-CS-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS-at1221 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 3 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 4 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 4 [] (lem-F1-order-CS c4) ▸
       at 0 2 [] (wl0001 (lit c4)) ▸ done


-- F1 order-CS @011220: 7 steps
lem-F1-order-CS-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS-at011220 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 3 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 4 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 4 [] (lem-F1-order-CS-at1221 c4) ▸
       at 0 2 [] (wl0002 (lit c4)) ▸ done


-- tr order-CS at 1: 1 steps
lem-tr-order-CS-at-1 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-CS-at-1 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) []
  b0 = at 0 4 [] (lem-F1-order-CS-at011220 c4) ▸ done


-- F1 order-CS @132132: 7 steps
lem-F1-order-CS-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS-at132132 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ []) []
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 3 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 4 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 4 [] (lem-F1-order-CS-at1221 c4) ▸
       at 0 2 [] (wl0006 (lit c4)) ▸ done


-- F1 order-CS @01132032: 7 steps
lem-F1-order-CS-at01132032 : Ws → ⟪ (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS-at01132032 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 3 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 4 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 4 [] (lem-F1-order-CS-at132132 c4) ▸
       at 0 2 [] (wl0002 (lit c4)) ▸ done


-- F1 order-CS @02132031: 7 steps
lem-F1-order-CS-at02132031 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS-at02132031 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 3 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 4 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 4 [] (lem-F1-order-CS-at01132032 c4) ▸
       at 0 2 [] (wl0001 (lit c4)) ▸ done


-- tr order-CS at 2: 1 steps
lem-tr-order-CS-at-2 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-CS-at-2 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) []
  b0 = at 0 4 [] (lem-F1-order-CS-at02132031 c4) ▸ done


-- F1 comm-CS-S0 @1221: 7 steps
lem-F1-comm-CS-S0-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0-at1221 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CS04 ∷ []) (CS04 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 1 2 (CS04 ∷ Sb2-0-41-3 ∷ []) (lem-F1-comm-CS-S0 c4) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F1 comm-CS-S0 @011220: 7 steps
lem-F1-comm-CS-S0-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0-at011220 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 1 2 (CS04 ∷ Sb1-0-42-3 ∷ []) (lem-F1-comm-CS-S0-at1221 c4) ▸
       at 0 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- tr comm-CS-S0 at 1: 1 steps
lem-tr-comm-CS-S0-at-1 : Ws → ⟪ (Sb0-1-42-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-comm-CS-S0-at-1 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 2 (CS14 ∷ Sb0-1-42-3 ∷ []) (lem-F1-comm-CS-S0-at011220 c4) ▸ done


-- F1 comm-CS-S0 @132132: 7 steps
lem-F1-comm-CS-S0-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0-at132132 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ CS04 ∷ []) (CS04 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 1 2 (CS04 ∷ Sb1-0-42-3 ∷ []) (lem-F1-comm-CS-S0-at1221 c4) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- F1 comm-CS-S0 @01132032: 7 steps
lem-F1-comm-CS-S0-at01132032 : Ws → ⟪ (Sb0-1-43-2 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0-at01132032 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 1 2 (CS04 ∷ Sb1-0-43-2 ∷ []) (lem-F1-comm-CS-S0-at132132 c4) ▸
       at 0 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F1 comm-CS-S0 @02132031: 7 steps
lem-F1-comm-CS-S0-at02132031 : Ws → ⟪ (Sb0-2-43-1 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0-at02132031 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CS24 ∷ []) (CS24 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 1 2 (CS14 ∷ Sb0-1-43-2 ∷ []) (lem-F1-comm-CS-S0-at01132032 c4) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- tr comm-CS-S0 at 2: 1 steps
lem-tr-comm-CS-S0-at-2 : Ws → ⟪ (Sb0-2-43-1 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm-CS-S0-at-2 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CS24 ∷ []) (CS24 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 2 (CS24 ∷ Sb0-2-43-1 ∷ []) (lem-F1-comm-CS-S0-at02132031 c4) ▸ done


-- F1 comm-CS-S1 @1221: 7 steps
lem-F1-comm-CS-S1-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1-at1221 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 1 2 (CS14 ∷ Sb2-0-41-3 ∷ []) (lem-F1-comm-CS-S1 c4) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F1 comm-CS-S1 @011220: 7 steps
lem-F1-comm-CS-S1-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1-at011220 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 2 (CS24 ∷ Sb1-0-42-3 ∷ []) (lem-F1-comm-CS-S1-at1221 c4) ▸
       at 0 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- tr comm-CS-S1 at 1: 1 steps
lem-tr-comm-CS-S1-at-1 : Ws → ⟪ (Sb0-1-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-comm-CS-S1-at-1 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 2 (CS24 ∷ Sb0-1-42-3 ∷ []) (lem-F1-comm-CS-S1-at011220 c4) ▸ done


-- F1 comm-CS-S1 @132132: 7 steps
lem-F1-comm-CS-S1-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1-at132132 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ CS34 ∷ []) (CS34 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 1 2 (CS24 ∷ Sb1-0-42-3 ∷ []) (lem-F1-comm-CS-S1-at1221 c4) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- F1 comm-CS-S1 @01132032: 7 steps
lem-F1-comm-CS-S1-at01132032 : Ws → ⟪ (Sb0-1-43-2 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1-at01132032 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (CS34 ∷ Sb1-0-43-2 ∷ []) (lem-F1-comm-CS-S1-at132132 c4) ▸
       at 0 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F1 comm-CS-S1 @02132031: 7 steps
lem-F1-comm-CS-S1-at02132031 : Ws → ⟪ (Sb0-2-43-1 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1-at02132031 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CS34 ∷ []) (CS34 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 2 (CS34 ∷ Sb0-1-43-2 ∷ []) (lem-F1-comm-CS-S1-at01132032 c4) ▸
       at 0 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- tr comm-CS-S1 at 2: 1 steps
lem-tr-comm-CS-S1-at-2 : Ws → ⟪ (Sb0-2-43-1 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm-CS-S1-at-2 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CS34 ∷ []) (CS34 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 2 (CS34 ∷ Sb0-2-43-1 ∷ []) (lem-F1-comm-CS-S1-at02132031 c4) ▸ done


-- F1 X-CS0 @1221: 18 steps
lem-F1-X-CS0-at1221 : Ws → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-F1-X-CS0-at1221 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ []) (Sw12 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 3 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 5 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 6 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 6 (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (lem-F1-X-CS0 c4) ▸ done

  b1 : Chain (Sw12 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ Sw12 ∷ []) (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ [])
  b1 = at 0 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 3 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 4 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 6 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 7 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸ done

  b2 : Chain (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ []) (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS24 ∷ [])
  b2 = at 8 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 9 2 [] (wl0001 (lit c4)) ▸ done


-- F1 X-CS0 @011220: 18 steps
lem-F1-X-CS0-at011220 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-F1-X-CS0-at011220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS24 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 3 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 5 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 6 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 6 (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS24 ∷ []) (lem-F1-X-CS0-at1221 c4) ▸ done

  b1 : Chain (Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS24 ∷ Sw01 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ [])
  b1 = at 0 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 3 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4)) ▸
       at 4 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 5 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 6 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4)) ▸
       at 7 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸ done

  b2 : Chain (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b2 = at 8 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 9 2 [] (wl0002 (lit c4)) ▸ done


-- tr X-CS0 at 1: 1 steps
lem-tr-X-CS0-at-1 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-X-CS0-at-1 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b0 = at 0 6 (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (lem-F1-X-CS0-at011220 c4) ▸ done


-- F1 X-CS0 @132132: 18 steps
lem-F1-X-CS0-at132132 : Ws → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-F1-X-CS0-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-43-2 ∷ []) (Sw23 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS24 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 3 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 5 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 6 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 6 (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS24 ∷ []) (lem-F1-X-CS0-at1221 c4) ▸ done

  b1 : Chain (Sw23 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS24 ∷ Sw23 ∷ []) (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw23 ∷ CS24 ∷ Sw23 ∷ [])
  b1 = at 0 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 3 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 4 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 6 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 7 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸ done

  b2 : Chain (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw23 ∷ CS24 ∷ Sw23 ∷ []) (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS34 ∷ [])
  b2 = at 8 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 9 2 [] (wl0006 (lit c4)) ▸ done


-- F1 X-CS0 @01132032: 18 steps
lem-F1-X-CS0-at01132032 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-F1-X-CS0-at01132032 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ []) (Sw01 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS34 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 3 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 5 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 6 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 6 (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS34 ∷ []) (lem-F1-X-CS0-at132132 c4) ▸ done

  b1 : Chain (Sw01 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS34 ∷ Sw01 ∷ []) (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ CS34 ∷ Sw01 ∷ [])
  b1 = at 0 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 3 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4)) ▸
       at 4 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 5 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 6 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4)) ▸
       at 7 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸ done

  b2 : Chain (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ CS34 ∷ Sw01 ∷ []) (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS34 ∷ [])
  b2 = at 8 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 9 2 [] (wl0002 (lit c4)) ▸ done


-- F1 X-CS0 @02132031: 18 steps
lem-F1-X-CS0-at02132031 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-F1-X-CS0-at02132031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sw12 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS34 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 4 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 5 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 6 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 6 (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS34 ∷ []) (lem-F1-X-CS0-at01132032 c4) ▸ done

  b1 : Chain (Sw12 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS34 ∷ Sw12 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ CS34 ∷ Sw12 ∷ [])
  b1 = at 0 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 3 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 4 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 5 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 6 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 7 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸ done

  b2 : Chain (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ CS34 ∷ Sw12 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b2 = at 8 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 9 2 [] (wl0001 (lit c4)) ▸ done


-- tr X-CS0 at 2: 1 steps
lem-tr-X-CS0-at-2 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-X-CS0-at-2 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b0 = at 0 6 (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (lem-F1-X-CS0-at02132031 c4) ▸ done


-- F1 X-CS1 @1221: 18 steps
lem-F1-X-CS1-at1221 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-F1-X-CS1-at1221 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb1-0-42-3 ∷ []) (Sw12 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 4 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 5 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 6 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 6 (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (lem-F1-X-CS1 c4) ▸ done

  b1 : Chain (Sw12 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ Sw12 ∷ []) (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ CS04 ∷ Sw12 ∷ [])
  b1 = at 0 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 3 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 4 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 5 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 6 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 7 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸ done

  b2 : Chain (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ CS04 ∷ Sw12 ∷ []) (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS04 ∷ [])
  b2 = at 8 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 9 2 [] (wl0001 (lit c4)) ▸ done


-- F1 X-CS1 @011220: 18 steps
lem-F1-X-CS1-at011220 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-F1-X-CS1-at011220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS04 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 2 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 3 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 4 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 5 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 6 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 6 (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS04 ∷ []) (lem-F1-X-CS1-at1221 c4) ▸ done

  b1 : Chain (Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS04 ∷ Sw01 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw01 ∷ CS04 ∷ Sw01 ∷ [])
  b1 = at 0 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 3 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 4 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 5 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 6 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 7 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸ done

  b2 : Chain (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw01 ∷ CS04 ∷ Sw01 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b2 = at 8 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 9 2 [] (wl0002 (lit c4)) ▸ done


-- tr X-CS1 at 1: 1 steps
lem-tr-X-CS1-at-1 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-tr-X-CS1-at-1 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b0 = at 0 6 (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (lem-F1-X-CS1-at011220 c4) ▸ done


-- F1 X-CS1 @132132: 18 steps
lem-F1-X-CS1-at132132 : Ws → ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-F1-X-CS1-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb1-0-43-2 ∷ []) (Sw23 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS04 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 4 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 5 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 6 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 6 (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS04 ∷ []) (lem-F1-X-CS1-at1221 c4) ▸ done

  b1 : Chain (Sw23 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS04 ∷ Sw23 ∷ []) (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sw23 ∷ CS04 ∷ Sw23 ∷ [])
  b1 = at 0 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 3 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0163 (lit c4))) ▸
       at 4 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 5 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 6 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0163 (lit c4))) ▸
       at 7 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸ done

  b2 : Chain (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sw23 ∷ CS04 ∷ Sw23 ∷ []) (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS04 ∷ [])
  b2 = at 8 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 9 2 [] (wl0006 (lit c4)) ▸ done


-- F1 X-CS1 @01132032: 18 steps
lem-F1-X-CS1-at01132032 : Ws → ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-F1-X-CS1-at01132032 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-1-43-2 ∷ []) (Sw01 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS04 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 2 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 3 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 4 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 5 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 6 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 6 (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS04 ∷ []) (lem-F1-X-CS1-at132132 c4) ▸ done

  b1 : Chain (Sw01 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS04 ∷ Sw01 ∷ []) (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sw01 ∷ CS04 ∷ Sw01 ∷ [])
  b1 = at 0 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 3 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 4 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 5 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 6 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 7 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸ done

  b2 : Chain (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sw01 ∷ CS04 ∷ Sw01 ∷ []) (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS14 ∷ [])
  b2 = at 8 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 9 2 [] (wl0002 (lit c4)) ▸ done


-- F1 X-CS1 @02132031: 18 steps
lem-F1-X-CS1-at02132031 : Ws → ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-F1-X-CS1-at02132031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sw12 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS14 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 2 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 3 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 4 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 5 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 6 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 6 (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS14 ∷ []) (lem-F1-X-CS1-at01132032 c4) ▸ done

  b1 : Chain (Sw12 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS14 ∷ Sw12 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ [])
  b1 = at 0 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 3 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 4 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 5 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 6 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 7 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸ done

  b2 : Chain (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b2 = at 8 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 9 2 [] (wl0001 (lit c4)) ▸ done


-- tr X-CS1 at 2: 1 steps
lem-tr-X-CS1-at-2 : Ws → ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-X-CS1-at-2 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b0 = at 0 6 (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (lem-F1-X-CS1-at02132031 c4) ▸ done


-- F1 CS-K0 @1221: 13 steps
lem-F1-CS-K0-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 3 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 1 5 (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0 c4) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸ done

  b1 : Chain (CS04 ∷ Sw12 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sw12 ∷ []) (CS04 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ [])
  b1 = at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 3 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 4 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 5 2 [] (wl0001 (lit c4)) ▸ done


-- F1 CS-K0 @011220: 13 steps
lem-F1-CS-K0-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-at011220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 3 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 5 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 1 5 (CS04 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ []) (lem-F1-CS-K0-at1221 c4) ▸
       at 0 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸ done

  b1 : Chain (CS14 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw01 ∷ []) (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b1 = at 1 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 3 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4)) ▸
       at 4 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 5 2 [] (wl0002 (lit c4)) ▸ done


-- tr CS-K0 at 1: 1 steps
lem-tr-CS-K0-at-1 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-CS-K0-at-1 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 5 (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (lem-F1-CS-K0-at011220 c4) ▸ done


-- F1 CS-K0 @132132: 13 steps
lem-F1-CS-K0-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ CK40 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK40 ∷ Sb1-0-43-2 ∷ CK40 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-F1-CS-K0-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb1-0-43-2 ∷ CK40 ∷ Sb1-0-43-2 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 2 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 3 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 1 5 (CS04 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ []) (lem-F1-CS-K0-at1221 c4) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸ done

  b1 : Chain (CS04 ∷ Sw23 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw23 ∷ []) (CS04 ∷ CK40 ∷ Sb1-0-43-2 ∷ CK40 ∷ Sb1-0-43-2 ∷ [])
  b1 = at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 2 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 3 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 4 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 5 2 [] (wl0006 (lit c4)) ▸ done


-- F1 CS-K0 @01132032: 13 steps
lem-F1-CS-K0-at01132032 : Ws → ⟪ (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-CS-K0-at01132032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ Sw01 ∷ CK40 ∷ Sb1-0-43-2 ∷ CK40 ∷ Sb1-0-43-2 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 3 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 5 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 1 5 (CS04 ∷ CK40 ∷ Sb1-0-43-2 ∷ CK40 ∷ Sb1-0-43-2 ∷ []) (lem-F1-CS-K0-at132132 c4) ▸
       at 0 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸ done

  b1 : Chain (CS14 ∷ Sw01 ∷ CK40 ∷ Sb1-0-43-2 ∷ CK40 ∷ Sb1-0-43-2 ∷ Sw01 ∷ []) (CS14 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ [])
  b1 = at 1 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 3 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4)) ▸
       at 4 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 5 2 [] (wl0002 (lit c4)) ▸ done


-- F1 CS-K0 @02132031: 13 steps
lem-F1-CS-K0-at02132031 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-CS-K0-at02132031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ Sw12 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 3 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 4 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 5 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 1 5 (CS14 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) (lem-F1-CS-K0-at01132032 c4) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸ done

  b1 : Chain (CS24 ∷ Sw12 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sw12 ∷ []) (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ [])
  b1 = at 1 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 3 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 4 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 5 2 [] (wl0001 (lit c4)) ▸ done


-- tr CS-K0 at 2: 1 steps
lem-tr-CS-K0-at-2 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-CS-K0-at-2 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 5 (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (lem-F1-CS-K0-at02132031 c4) ▸ done


-- F1 CS-K1 @1221: 13 steps
lem-F1-CS-K1-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ Sw12 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 3 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 4 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 5 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 1 5 (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K1 c4) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸ done

  b1 : Chain (CS24 ∷ Sw12 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw12 ∷ []) (CS24 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ [])
  b1 = at 1 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 3 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 4 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 5 2 [] (wl0001 (lit c4)) ▸ done


-- F1 CS-K1 @011220: 13 steps
lem-F1-CS-K1-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-at011220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 3 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 4 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 5 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 5 (CS24 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ []) (lem-F1-CS-K1-at1221 c4) ▸
       at 0 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b1 : Chain (CS24 ∷ Sw01 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ Sw01 ∷ []) (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ [])
  b1 = at 1 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 3 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 4 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 5 2 [] (wl0002 (lit c4)) ▸ done


-- tr CS-K1 at 1: 1 steps
lem-tr-CS-K1-at-1 : Ws → ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-CS-K1-at-1 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 5 (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) (lem-F1-CS-K1-at011220 c4) ▸ done


-- F1 CS-K1 @132132: 13 steps
lem-F1-CS-K1-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-F1-CS-K1-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ Sw23 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 2 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 3 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 4 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 5 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 1 5 (CS24 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ []) (lem-F1-CS-K1-at1221 c4) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸ done

  b1 : Chain (CS34 ∷ Sw23 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ Sw23 ∷ []) (CS34 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ [])
  b1 = at 1 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0163 (lit c4))) ▸
       at 2 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 3 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0163 (lit c4))) ▸
       at 4 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 5 2 [] (wl0006 (lit c4)) ▸ done


-- F1 CS-K1 @01132032: 13 steps
lem-F1-CS-K1-at01132032 : Ws → ⟪ (Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-CS-K1-at01132032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 3 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 4 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 5 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 5 (CS34 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ []) (lem-F1-CS-K1-at132132 c4) ▸
       at 0 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸ done

  b1 : Chain (CS34 ∷ Sw01 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ Sw01 ∷ []) (CS34 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ [])
  b1 = at 1 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 3 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 4 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 5 2 [] (wl0002 (lit c4)) ▸ done


-- F1 CS-K1 @02132031: 13 steps
lem-F1-CS-K1-at02132031 : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-CS-K1-at02132031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 3 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 4 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 5 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 5 (CS34 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ []) (lem-F1-CS-K1-at01132032 c4) ▸
       at 0 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸ done

  b1 : Chain (CS34 ∷ Sw12 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sw12 ∷ []) (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ [])
  b1 = at 1 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 3 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 4 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 5 2 [] (wl0001 (lit c4)) ▸ done


-- tr CS-K1 at 2: 1 steps
lem-tr-CS-K1-at-2 : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-CS-K1-at-2 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 5 (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (lem-F1-CS-K1-at02132031 c4) ▸ done


-- tr comm-CS-CS at 0: 1 steps
lem-tr-comm-CS-CS-at-0 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-comm-CS-CS-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (lem-F1-comm-CS-CS c4) ▸ done


-- F1 comm-CS-CS @2332: 7 steps
lem-F1-comm-CS-CS-at2332 : Ws → ⟪ (Sb0-1-43-2 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-comm-CS-CS-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb3-0-41-2 ∷ []) (Sb3-0-41-2 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (lem-F1-comm-CS-CS c4) ▸
       at 0 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- F1 comm-CS-CS @122331: 7 steps
lem-F1-comm-CS-CS-at122331 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CS-CS-at122331 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb3-0-42-1 ∷ []) (Sb3-0-42-1 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 1 2 (Sb3-0-41-2 ∷ Sb0-1-43-2 ∷ []) (lem-F1-comm-CS-CS-at2332 c4) ▸
       at 0 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F1 comm-CS-CS @01122330: 7 steps
lem-F1-comm-CS-CS-at01122330 : Ws → ⟪ (Sb1-2-43-0 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ
lem-F1-comm-CS-CS-at01122330 c4 = run b0
  where
  b0 : Chain (Sb1-2-43-0 ∷ Sb3-1-42-0 ∷ []) (Sb3-1-42-0 ∷ Sb1-2-43-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 2 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 1 2 (Sb3-0-42-1 ∷ Sb0-2-43-1 ∷ []) (lem-F1-comm-CS-CS-at122331 c4) ▸
       at 0 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F0 @2332: 5 steps
lem-F0-at2332 : Ws → ⟪ (Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F0-at2332 c4 = run b0
  where
  b0 : Chain (Sb3-0-41-2 ∷ []) (Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 1 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- F0 @122331: 5 steps
lem-F0-at122331 : Ws → ⟪ (Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ []) ⟫ʷ
lem-F0-at122331 c4 = run b0
  where
  b0 : Chain (Sb3-0-42-1 ∷ []) (Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 1 1 (Sb2-0-41-3 ∷ []) (lem-F0-at2332 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- F0 @01122330: 5 steps
lem-F0-at01122330 : Ws → ⟪ (Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F0-at01122330 c4 = run b0
  where
  b0 : Chain (Sb3-1-42-0 ∷ []) (Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 1 1 (Sb1-0-42-3 ∷ []) (lem-F0-at122331 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done

