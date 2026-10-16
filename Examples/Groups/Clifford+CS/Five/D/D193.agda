{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D193 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0008 ; wl0010 ; wl0061 ; wl0064 ; wl0159 ; wl0161)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.TR using (tr03 ; tr04)
-- F1 rel-269 [rhs] part0: 352 steps
lem-F1-rel-269-rhs-part0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) ⟫ʷ
lem-F1-rel-269-rhs-part0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (run b43)))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Sw01 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sw01 ∷ [])
  b0 = at 0 3 (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (tr03 c4) ▸
       at 0 42 (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (sym (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1 c4)) ▸
       at 45 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 44 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 48 2 (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (sym (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))) ▸
       at 47 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 46 2 (Sw01 ∷ Sb1-0-3-2 ∷ []) (sym (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))) ▸
       at 45 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸ done

  b1 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Sw01 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw01 ∷ [])
  b1 = at 44 2 (Sw01 ∷ Bx1-0423 ∷ []) (sym (lem-nat-0-BOX⟨1·0423⟩ (lit c4))) ▸
       at 45 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 43 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 45 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 44 2 (Sw01 ∷ CK30 ∷ []) (wl0161 (lit c4)) ▸
       at 43 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 44 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 42 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ [])
  b2 = at 46 2 (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (sym (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))) ▸
       at 45 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 44 2 (Sw01 ∷ Sb1-0-3-2 ∷ []) (sym (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))) ▸
       at 43 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 42 2 (Sw01 ∷ Bx1-0423 ∷ []) (sym (lem-nat-0-BOX⟨1·0423⟩ (lit c4))) ▸
       at 43 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 46 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 45 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸ done

  b3 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sw34 ∷ CK30 ∷ Sw12 ∷ Sw34 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ [])
  b3 = at 49 2 (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (sym (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))) ▸
       at 48 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸
       at 47 2 (Sw12 ∷ Sb2-0-3-1 ∷ []) (sym (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))) ▸
       at 46 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸
       at 45 2 (Sw12 ∷ Bx2-0413 ∷ []) (sym (lem-nat-1-BOX⟨2·0413⟩ (lit c4))) ▸
       at 46 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 44 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 46 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b4 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sw34 ∷ CK30 ∷ Sw12 ∷ Sw34 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ Bx1-0423 ∷ Sw12 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ [])
  b4 = at 45 2 (Sw12 ∷ CK30 ∷ []) (wl0159 (lit c4)) ▸
       at 44 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 45 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 43 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 47 2 (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (sym (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))) ▸
       at 46 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸
       at 45 2 (Sw12 ∷ Sb2-0-3-1 ∷ []) (sym (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))) ▸
       at 44 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0064 (lit c4))) ▸ done

  b5 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ Bx1-0423 ∷ Sw12 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sw12 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b5 = at 43 2 (Sw12 ∷ Bx2-0413 ∷ []) (sym (lem-nat-1-BOX⟨2·0413⟩ (lit c4))) ▸
       at 44 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 44 3 (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (tr04 c4) ▸
       at 44 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 43 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 44 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 45 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 43 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sw12 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b6 = at 45 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 44 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 45 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 46 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 47 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 48 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 44 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 46 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b7 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw12 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Sw12 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b7 = at 45 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 46 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 47 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 48 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 49 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 45 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 47 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 46 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸ done

  b8 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Sw12 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sw12 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b8 = at 47 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 48 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 49 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 50 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 46 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 48 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 47 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 48 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b9 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sw12 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Sw12 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b9 = at 49 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 50 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 51 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 47 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 49 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 48 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 49 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 50 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸ done

  b10 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Sw12 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b10 = at 51 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 52 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 48 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 50 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 49 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 50 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 51 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 52 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b11 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sw12 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b11 = at 53 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 49 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 51 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 50 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 51 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 52 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 53 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 54 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸ done

  b12 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sw12 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b12 = at 50 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 52 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 51 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 52 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 53 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 54 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 55 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 51 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done

  b13 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx1-0423 ∷ Toff324 ∷ Sw12 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b13 = at 52 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 53 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 54 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 55 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 56 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 58 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 57 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 58 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b14 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx1-0423 ∷ Toff324 ∷ Sw12 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw12 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b14 = at 59 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 60 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 61 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 57 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 59 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 58 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 59 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 60 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b15 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw12 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw12 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b15 = at 58 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 60 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 59 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 60 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 61 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 62 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 63 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 59 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done

  b16 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw12 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sw12 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b16 = at 61 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 60 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 61 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 62 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 60 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 62 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 61 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 62 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b17 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sw12 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b17 = at 63 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 64 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 65 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 61 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 63 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 62 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 63 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 64 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b18 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b18 = at 62 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 64 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 63 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 64 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 65 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 63 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 65 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 64 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b19 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b19 = at 65 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 66 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 64 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 66 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 65 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 66 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 67 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 65 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b20 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b20 = at 67 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 66 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 67 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 68 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 66 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 68 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 67 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 68 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸ done

  b21 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b21 = at 69 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 67 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 69 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 68 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 69 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 70 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 68 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 70 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b22 = at 69 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 70 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 71 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 69 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 71 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 70 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 71 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 72 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b23 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx1-0423 ∷ Toff324 ∷ Sw12 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b23 = at 70 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 71 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 72 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 73 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 74 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 76 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 75 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 76 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b24 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx1-0423 ∷ Toff324 ∷ Sw12 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw12 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b24 = at 77 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 78 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 79 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 75 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 77 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 76 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 77 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 78 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b25 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw12 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw12 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b25 = at 76 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 78 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 77 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 78 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 79 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 80 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 81 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 77 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done

  b26 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw12 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sw12 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b26 = at 79 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 78 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 79 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 80 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 78 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 80 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 79 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 80 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b27 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Bx1-0423 ∷ Toff324 ∷ Sw12 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Sw12 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b27 = at 81 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 82 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 83 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 79 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 81 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 80 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 81 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 82 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸ done

  b28 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Sw12 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b28 = at 83 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 84 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 80 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 82 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 81 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 82 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 83 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 84 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸ done

  b29 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sw12 ∷ Sb⁻2-0-3-1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b29 = at 85 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 81 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 83 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 82 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 83 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 84 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 82 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 84 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ [])
  b30 = at 83 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 84 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 85 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 83 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 85 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 84 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 85 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 86 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b31 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw01 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sw01 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  b31 = at 84 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 85 2 [] (wl0001 (lit c4)) ▸
       at 43 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 42 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 43 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 (lit c4))) ▸
       at 44 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 42 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸
       at 44 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸ done

  b32 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sw01 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Sw01 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  b32 = at 43 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 44 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 45 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 46 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 47 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 43 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 45 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 44 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸ done

  b33 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Sw01 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sw01 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  b33 = at 45 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 46 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 47 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 48 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 44 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 46 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 45 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 46 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b34 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sw01 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  b34 = at 47 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 48 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 49 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 45 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 47 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 46 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 47 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 48 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸ done

  b35 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sw01 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  b35 = at 49 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 50 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 46 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 48 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 47 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 48 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 49 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 50 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b36 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sw01 ∷ Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  b36 = at 51 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 47 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 49 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 48 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 49 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 50 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 51 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 52 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸ done

  b37 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Sw01 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  b37 = at 48 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 50 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 49 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 50 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 51 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 52 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 53 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 49 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b38 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ Sw01 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  b38 = at 51 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 50 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 51 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 52 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 53 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 54 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 50 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 51 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b39 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ Sw01 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  b39 = at 52 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 53 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 54 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 55 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 57 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 56 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 57 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 58 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸ done

  b40 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  b40 = at 59 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 60 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 56 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 58 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 57 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 58 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 (lit c4))) ▸
       at 59 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 57 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done

  b41 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sw01 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  b41 = at 59 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 58 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 59 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 60 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 61 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 62 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 58 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 60 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b42 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  b42 = at 59 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 60 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 (lit c4))) ▸
       at 61 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 59 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸
       at 61 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 60 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 61 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 62 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸ done

  b43 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Sw01 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ [])
  b43 = at 63 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 64 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 60 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 62 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 61 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 62 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 63 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 61 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

