{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D181 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0100 ; wl0111 ; wl0283 ; wl0341 ; wl0602 ; wl0729 ; wl0731 ; wl0827 ; wl0828 ; wl0829 ; wl0830 ; wl0831 ; wl0832 ; wl0833 ; wl0834 ; wl0835 ; wl0836 ; wl0837 ; wl0838 ; wl0839 ; wl0840 ; wl0841 ; wl0842 ; wl0843 ; wl0844 ; wl0845 ; wl0846 ; wl0847 ; wl0848 ; wl0849 ; wl0850 ; wl0851 ; wl0852 ; wp0178 ; wp0352 ; wp0411 ; wp0430 ; wp0431 ; wp0432 ; wp0433 ; wp0434 ; wp0435 ; wp0436 ; wp0437 ; wp0438 ; wp0439 ; wp0440)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym23-at12213443 ; lem-sym23-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-beta-T-at12213443 ; lem-beta-T-at122441 ; lem-sym34-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D180 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-SBOX⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨1·2430⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩)
-- F4 CS23^0|K1^1: 133 steps
lem-F4-CS23ᵖ0∣K1ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣K1ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b0 = at 3 1 (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (wp0178 c4) ▸
       at 3 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb0-2-43-1 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b1 = at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS12⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 15 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0839 (lit c4))) ▸
       at 8 1 (CS12 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0840 (lit c4))) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b2 = at 9 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0839 (lit c4))) ▸
       at 2 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0436 c4)) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0437 c4)) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b3 = at 4 4 (S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0436 c4)) ▸
       at 1 4 (S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0437 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b4 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b5 = at 15 1 (CS12⁻ ∷ []) (refl) ▸
       at 14 4 (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0827 (lit c4))) ▸
       at 16 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 11 4 (CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0828 (lit c4))) ▸
       at 9 1 (CS12 ∷ []) (refl) ▸
       at 8 4 (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0829 (lit c4))) ▸
       at 10 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 5 4 (CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0828 (lit c4))) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b6 = at 3 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 4 (CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0430 c4)) ▸
       at 8 4 (CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0431 c4)) ▸
       at 5 4 (CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0430 c4)) ▸
       at 2 4 (CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0431 c4)) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b7 = at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b8 = at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 5 2 (K1 ∷ X4 ∷ []) (sym (wl0841 (lit c4))) ▸
       at 4 2 (K1 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at122441 c4) ▸
       at 3 2 (K1 ∷ X4 ∷ []) (sym (wl0841 (lit c4))) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K1 ∷ CS14 ∷ [])
  b9 = at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 1 (CS12⁻ ∷ []) (refl) ▸
       at 16 4 (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0827 (lit c4))) ▸
       at 18 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 13 4 (CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0828 (lit c4))) ▸
       at 11 1 (CS12 ∷ []) (refl) ▸
       at 10 4 (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0829 (lit c4))) ▸
       at 12 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ Toff024 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K1 ∷ CS14 ∷ [])
  b10 = at 7 4 (CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0828 (lit c4))) ▸
       at 5 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 4 (CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0430 c4)) ▸
       at 10 4 (CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0431 c4)) ▸
       at 7 4 (CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0430 c4)) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ Toff024 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K1 ∷ CS14 ∷ [])
  b11 = at 4 4 (CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0431 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS14 ∷ [])
  b12 = at 10 2 [] (wl0283 (lit c4)) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 7 2 (K1 ∷ X4 ∷ []) (sym (wl0841 (lit c4))) ▸
       at 6 2 (K1 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at122441 c4) ▸
       at 5 2 (K1 ∷ X4 ∷ []) (sym (wl0841 (lit c4))) ▸
       at 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b13 = at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS12⁻ ∷ []) (refl) ▸
       at 18 4 (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0827 (lit c4))) ▸
       at 20 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 15 4 (CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0828 (lit c4))) ▸
       at 13 1 (CS12 ∷ []) (refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0829 (lit c4))) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b14 = at 14 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 9 4 (CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0828 (lit c4))) ▸
       at 7 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0430 c4)) ▸
       at 12 4 (CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0431 c4)) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b15 = at 9 4 (CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0430 c4)) ▸
       at 6 4 (CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0431 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b16 = at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 0 7 (CK41 ∷ []) (sym (wp0178 c4)) ▸ done


-- F4 CS23^0|K2^1: 219 steps
lem-F4-CS23ᵖ0∣K2ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣K2ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (run b27)))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b0 = at 3 1 (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (wl0729 (lit c4)) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb0-2-43-1 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b1 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS12⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 15 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0839 (lit c4))) ▸
       at 8 1 (CS12 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 9 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ X4 ∷ Toff024 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b2 = at 4 4 (S4⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0839 (lit c4))) ▸
       at 2 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0436 c4)) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0437 c4)) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0436 c4)) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff024 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b3 = at 1 4 (S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0437 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b4 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 1 (CS12⁻ ∷ []) (refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b5 = at 14 4 (CS24 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0830 (lit c4))) ▸
       at 16 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 11 4 (CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 9 1 (CS12 ∷ []) (refl) ▸
       at 8 4 (CS24 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0832 (lit c4))) ▸
       at 10 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 5 4 (CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 3 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b6 = at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4)) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b7 = at 23 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 20 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 17 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0432 c4)) ▸
       at 14 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 11 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b8 = at 17 2 [] (wl0283 (lit c4)) ▸
       at 13 5 (CCZ013 ∷ []) (sym (wl0833 (lit c4))) ▸
       at 8 4 (CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0433 c4)) ▸
       at 6 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4)) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b9 = at 17 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 14 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 11 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0432 c4)) ▸
       at 8 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 5 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b10 = at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (CCZ013 ∷ []) (sym (wl0833 (lit c4))) ▸
       at 2 4 (CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0433 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b11 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ [])
  b12 = at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 1 (CS12 ∷ []) (refl) ▸
       at 16 1 (CS12⁻ ∷ []) (refl) ▸
       at 9 12 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0842 (lit c4))) ▸
       at 13 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 19 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 6 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0843 (lit c4))) ▸
       at 4 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ [])
  b13 = at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 14 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ [])
  b14 = at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 22 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 19 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0432 c4)) ▸
       at 16 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 13 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ [])
  b15 = at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ013 ∷ []) (sym (wl0833 (lit c4))) ▸
       at 16 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 15 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ CS03 ∷ X4 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ [])
  b16 = at 9 6 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0438 c4)) ▸
       at 8 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 7 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 6 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 8 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4)) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b17 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ CS03 ∷ X4 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ [])
  b17 = at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 16 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 13 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0432 c4)) ▸
       at 10 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 7 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸ done

  b18 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ [])
  b18 = at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 9 5 (CCZ013 ∷ []) (sym (wl0833 (lit c4))) ▸
       at 10 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 9 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 8 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 3 6 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0438 c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸ done

  b19 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ [])
  b19 = at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

  b20 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b20 = at 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS12⁻ ∷ []) (refl) ▸
       at 18 4 (CS24 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0830 (lit c4))) ▸
       at 20 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b21 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b21 = at 15 4 (CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 13 1 (CS12 ∷ []) (refl) ▸
       at 12 4 (CS24 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0832 (lit c4))) ▸
       at 14 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 9 4 (CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 7 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b22 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b22 = at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4)) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 26 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 27 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 24 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸ done

  b23 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b23 = at 21 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0432 c4)) ▸
       at 18 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 15 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 17 5 (CCZ013 ∷ []) (sym (wl0833 (lit c4))) ▸ done

  b24 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b24 = at 12 4 (CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0433 c4)) ▸
       at 10 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4)) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 18 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸ done

  b25 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b25 = at 15 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0432 c4)) ▸
       at 12 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 9 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 11 5 (CCZ013 ∷ []) (sym (wl0833 (lit c4))) ▸ done

  b26 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b26 = at 6 4 (CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0433 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸ done

  b27 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b27 = at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 7 (CK42 ∷ []) (sym (wl0729 (lit c4))) ▸ done


-- F4 CS23^0|K3^1: 185 steps
lem-F4-CS23ᵖ0∣K3ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣K3ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (run b23)))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b0 = at 3 1 (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (wl0731 (lit c4)) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb0-2-43-1 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b1 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS12⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 15 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0839 (lit c4))) ▸
       at 8 1 (CS12 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 9 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ X4 ∷ Toff024 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b2 = at 4 4 (S4⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0839 (lit c4))) ▸
       at 2 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0436 c4)) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0437 c4)) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0436 c4)) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff024 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b3 = at 1 4 (S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0437 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b4 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 1 (CS12⁻ ∷ []) (refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b5 = at 14 4 (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 16 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 11 4 (CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0836 (lit c4))) ▸
       at 9 1 (CS12 ∷ []) (refl) ▸
       at 8 4 (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0837 (lit c4))) ▸
       at 10 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 5 4 (CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0836 (lit c4))) ▸
       at 3 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b6 = at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 4 (CS34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0434 c4)) ▸
       at 8 4 (CS34 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0435 c4)) ▸
       at 5 4 (CS34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0434 c4)) ▸
       at 2 4 (CS34 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0435 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b7 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ [])
  b8 = at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 1 (CS12⁻ ∷ []) (refl) ▸
       at 15 6 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0845 (lit c4))) ▸
       at 19 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ [])
  b9 = at 12 6 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0846 (lit c4))) ▸
       at 10 1 (CS12 ∷ []) (refl) ▸
       at 9 6 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0847 (lit c4))) ▸
       at 13 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 6 6 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0846 (lit c4))) ▸
       at 4 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 4 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 4 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ [])
  b10 = at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 6 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0439 c4)) ▸
       at 11 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ [])
  b11 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0848 (lit c4))) ▸
       at 14 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ [])
  b12 = at 25 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0440 c4)) ▸
       at 22 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 19 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 16 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 13 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0851 (lit c4))) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ [])
  b13 = at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 10 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 12 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 13 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ [])
  b14 = at 11 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 6 6 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0439 c4)) ▸
       at 5 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 4 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 3 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 5 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ [])
  b15 = at 10 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0848 (lit c4))) ▸
       at 8 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0440 c4)) ▸
       at 16 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ [])
  b16 = at 13 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 10 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 7 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0851 (lit c4))) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 9 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸ done

  b17 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ [])
  b17 = at 4 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 6 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 7 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 6 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 5 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸ done

  b18 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ [])
  b18 = at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 7 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 7 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 7 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b19 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ [])
  b19 = at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS12⁻ ∷ []) (refl) ▸ done

  b20 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b20 = at 18 4 (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 20 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 15 4 (CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0836 (lit c4))) ▸
       at 13 1 (CS12 ∷ []) (refl) ▸
       at 12 4 (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0837 (lit c4))) ▸
       at 14 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 9 4 (CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0836 (lit c4))) ▸
       at 7 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸ done

  b21 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b21 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0434 c4)) ▸
       at 12 4 (CS34 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0435 c4)) ▸
       at 9 4 (CS34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0434 c4)) ▸
       at 6 4 (CS34 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0435 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸ done

  b22 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b22 = at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

  b23 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b23 = at 0 7 (CK43 ∷ []) (sym (wl0731 (lit c4))) ▸ done


-- beta-T @01122440: 8 steps
lem-beta-T-at01122440 : Ws → ⟪ (Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at01122440 c4 = run b0
  where
  b0 : Chain (Bx1-2430 ∷ []) (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ (lit c4)) ▸
       at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 0 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 (lit c4))) ▸
       at 2 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 (lit c4)) ▸
       at 3 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 (lit c4))) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143 @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2442 c4) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-3-2 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 c4) ▸
       at 0 2 (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-3-2 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442 c4) ▸
       at 0 2 (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done

