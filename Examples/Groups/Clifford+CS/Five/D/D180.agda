{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D180 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0019 ; wl0056 ; wl0061 ; wl0062 ; wl0190 ; wl0212 ; wl0260 ; wl0283 ; wl0353 ; wl0661 ; wl0743 ; wl0754 ; wl0755 ; wl0762 ; wl0772 ; wl0775 ; wl0817 ; wl0818 ; wl0819 ; wl0820 ; wl0821 ; wl0822 ; wl0823 ; wl0824 ; wl0825 ; wl0826 ; wl0827 ; wl0828 ; wl0829 ; wl0830 ; wl0831 ; wl0832 ; wl0833 ; wl0834 ; wl0835 ; wl0836 ; wl0837 ; wl0838 ; wl0839 ; wl0840 ; wp0126 ; wp0343 ; wp0348 ; wp0349 ; wp0352 ; wp0365 ; wp0392 ; wp0411 ; wp0419 ; wp0420 ; wp0421 ; wp0422 ; wp0423 ; wp0424 ; wp0425 ; wp0426 ; wp0427 ; wp0428 ; wp0429 ; wp0430 ; wp0431 ; wp0432 ; wp0433 ; wp0434 ; wp0435 ; wp0436 ; wp0437)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D166 using (lem-sym12-at122441 ; lem-sym12-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-X1-beta-at1441 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 ; lem-beta-T-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at13213442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D179 using (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132130 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩ ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-SBOX⟨1·0·43·2⟩ ; lem-nat-2-SBOX⟨0·3·1·4⟩ ; lem-nat-2-SBOXd⟨0·3·1·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-2-SBOX⟨0·2·1·4⟩ ; lem-nat-2-SBOXd⟨0·2·1·4⟩ ; lem-nat-3-SBOX⟨0·2·1·3⟩ ; lem-nat-3-SBOX⟨0·2·1·4⟩ ; lem-nat-3-SBOXd⟨0·2·1·3⟩ ; lem-nat-3-SBOXd⟨0·2·1·4⟩)
-- auto SBOX(0;1;23;4) | SBOX(0;3;1;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb0-2-1-4 ∷ []) (Sb0-2-1-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb0-3-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·2·1·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-3-1-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩ c4) ▸
       at 0 2 (Sb0-2-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·1·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;3;1;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb0-2-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·1·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-1-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at2332 c4) ▸
       at 0 2 (Sb0-2-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·1·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;3;1;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb⁻0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-2-1-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb⁻0-3-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·2·1·4⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-3-1-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩ c4) ▸
       at 0 2 (Sb⁻0-2-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·3·1·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;3;1;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻0-2-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·1·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-2-1-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at2332 c4) ▸
       at 0 2 (Sb⁻0-2-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·1·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- F4 CS12^0|CS23^1: 420 steps
lem-F4-CS12ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (run b52))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 1 2 (Bx0-2431 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at243243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 2 2 (Sb0-1-42-3 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132130 c4) ▸
       at 3 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸ done

  b2 : Chain (Bx0-2431 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b2 = at 4 2 [] (wl0212 (lit c4)) ▸
       at 4 1 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (sym (wl0743 (lit c4))) ▸
       at 5 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4)) ▸
       at 6 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 9 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 12 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 15 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b3 : Chain (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b3 = at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 1 (CS13 ∷ []) (refl) ▸
       at 14 1 (CS13⁻ ∷ []) (refl) ▸
       at 7 12 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0817 (lit c4))) ▸
       at 11 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b4 : Chain (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b4 = at 17 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0818 (lit c4))) ▸
       at 2 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 11 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸ done

  b5 : Chain (Bx0-2431 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b5 = at 10 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 12 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 20 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸ done

  b6 : Chain (Bx0-2431 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b6 = at 17 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 14 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 11 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 13 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸ done

  b7 : Chain (Bx0-2431 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b7 = at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 13 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 12 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 7 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0419 c4)) ▸
       at 6 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 5 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 4 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 6 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸ done

  b8 : Chain (Bx0-2431 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b8 = at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 14 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 11 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 8 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸ done

  b9 : Chain (Bx0-2431 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1⁻ ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b9 = at 5 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸
       at 8 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 7 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸ done

  b10 : Chain (Bx0-2431 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1⁻ ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b10 = at 6 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 1 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0419 c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸ done

  b11 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b11 = at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 5 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b12 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b12 = at 11 1 (CS13 ∷ []) (refl) ▸
       at 17 1 (CS13⁻ ∷ []) (refl) ▸
       at 10 21 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0820 (lit c4))) ▸
       at 23 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 29 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 7 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0821 (lit c4))) ▸
       at 5 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b13 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ K1⁻ ∷ CCZ023 ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b13 = at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 13 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0420 c4)) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 16 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸ done

  b14 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ K1⁻ ∷ CCZ023 ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b14 = at 15 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 16 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 18 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b15 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b15 = at 28 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 29 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0392 c4)) ▸
       at 26 4 (CS14⁻ ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0822 (lit c4))) ▸
       at 23 4 (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0421 c4)) ▸
       at 20 4 (CS14⁻ ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0822 (lit c4))) ▸
       at 17 4 (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0422 c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸ done

  b16 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b16 = at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 19 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 19 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 18 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 20 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸ done

  b17 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b17 = at 19 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 20 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0420 c4)) ▸
       at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 22 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 21 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 24 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 23 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 22 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b18 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b18 = at 25 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 24 2 (CS13 ∷ CCZ023 ∷ []) (wl0823 (lit c4)) ▸
       at 23 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 26 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 25 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 24 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 10 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0423 c4)) ▸
       at 9 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b19 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b19 = at 8 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 7 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 8 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0420 c4)) ▸
       at 11 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 10 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 9 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 11 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸ done

  b20 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b20 = at 10 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 12 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0392 c4)) ▸
       at 20 4 (CS14⁻ ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0822 (lit c4))) ▸ done

  b21 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b21 = at 17 4 (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0421 c4)) ▸
       at 14 4 (CS14⁻ ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0822 (lit c4))) ▸
       at 11 4 (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0422 c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 13 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸ done

  b22 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b22 = at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 13 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 12 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 13 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0420 c4)) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b23 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b23 = at 16 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 15 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 16 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 18 2 (CS13 ∷ CCZ023 ∷ []) (wl0823 (lit c4)) ▸
       at 17 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸ done

  b24 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b24 = at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 19 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 18 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 4 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0423 c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 17 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸ done

  b25 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b25 = at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 17 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 2 [] (wl0260 (lit c4)) ▸
       at 4 2 [] (wl0260 (lit c4)) ▸
       at 5 2 [] (wl0260 (lit c4)) ▸ done

  b26 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Sb0-1-42-3 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b26 = at 6 2 [] (wl0260 (lit c4)) ▸
       at 2 5 (CCZ134 ∷ []) (sym (wl0190 (lit c4))) ▸
       at 1 3 (Toff134 ∷ []) (wl0743 (lit c4)) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 4 2 (CS12 ∷ X4 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 4 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 2 (Sb0-2-1-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at243243 c4) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸ done

  b27 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Sb0-1-42-3 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b27 = at 2 2 (CS12 ∷ X4 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (sym (wl0743 (lit c4))) ▸
       at 7 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4)) ▸
       at 8 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 11 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 14 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 17 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸ done

  b28 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b28 = at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 1 (CS13 ∷ []) (refl) ▸
       at 16 1 (CS13⁻ ∷ []) (refl) ▸
       at 9 12 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0817 (lit c4))) ▸ done

  b29 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b29 = at 13 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 19 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0818 (lit c4))) ▸
       at 4 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b30 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b30 = at 13 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸ done

  b31 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b31 = at 22 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 16 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 13 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸ done

  b32 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b32 = at 15 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸
       at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 15 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 9 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0419 c4)) ▸
       at 8 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 7 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 6 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b33 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b33 = at 8 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 16 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 13 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸ done

  b34 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b34 = at 10 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 7 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 9 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸
       at 10 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b35 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b35 = at 9 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 8 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 3 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0419 c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 7 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸ done

  b36 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b36 = at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b37 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b37 = at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS13 ∷ []) (refl) ▸
       at 19 1 (CS13⁻ ∷ []) (refl) ▸
       at 12 21 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0820 (lit c4))) ▸
       at 25 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 31 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 9 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0821 (lit c4))) ▸
       at 7 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸ done

  b38 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b38 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0420 c4)) ▸
       at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b39 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b39 = at 18 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 20 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 20 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b40 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b40 = at 27 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 31 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0392 c4)) ▸
       at 28 4 (CS14⁻ ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0822 (lit c4))) ▸
       at 25 4 (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0421 c4)) ▸
       at 22 4 (CS14⁻ ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0822 (lit c4))) ▸
       at 19 4 (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0422 c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸ done

  b41 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b41 = at 23 2 [] (wl0283 (lit c4)) ▸
       at 24 2 [] (wl0283 (lit c4)) ▸
       at 25 2 [] (wl0283 (lit c4)) ▸
       at 21 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸
       at 22 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 23 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b42 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b42 = at 22 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 22 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0420 c4)) ▸
       at 25 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 24 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 26 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 25 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸ done

  b43 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b43 = at 24 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 27 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 26 2 (CS13 ∷ CCZ023 ∷ []) (wl0823 (lit c4)) ▸
       at 25 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 28 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 27 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 26 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 12 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0423 c4)) ▸ done

  b44 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b44 = at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 10 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 9 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 10 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0420 c4)) ▸
       at 13 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 12 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 11 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b45 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b45 = at 13 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0392 c4)) ▸ done

  b46 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b46 = at 22 4 (CS14⁻ ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0822 (lit c4))) ▸
       at 19 4 (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0421 c4)) ▸
       at 16 4 (CS14⁻ ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0822 (lit c4))) ▸
       at 13 4 (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0422 c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸ done

  b47 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b47 = at 15 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸
       at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 15 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0420 c4)) ▸ done

  b48 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS13 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b48 = at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 20 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 21 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 20 2 (CS13 ∷ CCZ023 ∷ []) (wl0823 (lit c4)) ▸ done

  b49 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS13 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b49 = at 19 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 22 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 2 (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 6 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0423 c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸ done

  b50 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b50 = at 19 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 19 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 5 2 [] (wl0260 (lit c4)) ▸
       at 6 2 [] (wl0260 (lit c4)) ▸ done

  b51 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b51 = at 7 2 [] (wl0260 (lit c4)) ▸
       at 8 2 [] (wl0260 (lit c4)) ▸
       at 4 5 (CCZ134 ∷ []) (sym (wl0190 (lit c4))) ▸
       at 3 3 (Toff134 ∷ []) (wl0743 (lit c4)) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 6 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 2 (Sb⁻0-2-1-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at243243 c4) ▸ done

  b52 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b52 = at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- auto CS01 | SBOX(2;0;31;4) @0113203442: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0113203442 : Ws → ⟪ (CS13 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CS13 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0113203442 c4 = run b0
  where
  b0 : Chain (CS13 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS13 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 (lit c4))) ▸
       at 2 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-43-2 ∷ CS03 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at13213442 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F4 CS23^0|iI^1: 30 steps
lem-F4-CS23ᵖ0∣iIᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣iIᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS12⁻ ∷ []) (refl) ▸
       at 12 4 (S4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0824 (lit c4))) ▸
       at 14 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ S4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ S4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b1 = at 9 4 (S4 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0825 (lit c4))) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 6 4 (S4 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0826 (lit c4))) ▸
       at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (S4 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0825 (lit c4))) ▸
       at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ S4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 4 (S4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0424 c4)) ▸
       at 6 4 (S4 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0425 c4)) ▸
       at 3 4 (S4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0424 c4)) ▸
       at 0 4 (S4 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0425 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b3 : Chain (S4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4 CS23^0|S0^1: 30 steps
lem-F4-CS23ᵖ0∣S0ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣S0ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS12⁻ ∷ []) (refl) ▸
       at 12 4 (CS04 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wp0426 c4)) ▸
       at 14 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b1 = at 9 4 (CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wp0427 c4)) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 6 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wp0427 c4)) ▸
       at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 4 (CS04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0428 c4)) ▸
       at 6 4 (CS04 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0429 c4)) ▸
       at 3 4 (CS04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0428 c4)) ▸
       at 0 4 (CS04 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0429 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b3 : Chain (CS04 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4 CS23^0|S1^1: 30 steps
lem-F4-CS23ᵖ0∣S1ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣S1ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS12⁻ ∷ []) (refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0827 (lit c4))) ▸
       at 14 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b1 = at 9 4 (CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0828 (lit c4))) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 6 4 (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0829 (lit c4))) ▸
       at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0828 (lit c4))) ▸
       at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 4 (CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0430 c4)) ▸
       at 6 4 (CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0431 c4)) ▸
       at 3 4 (CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0430 c4)) ▸
       at 0 4 (CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0431 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b3 : Chain (CS14 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4 CS23^0|S2^1: 58 steps
lem-F4-CS23ᵖ0∣S2ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣S2ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS12⁻ ∷ []) (refl) ▸
       at 12 4 (CS24 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0830 (lit c4))) ▸
       at 14 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b1 = at 9 4 (CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 6 4 (CS24 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0832 (lit c4))) ▸
       at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4)) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 18 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸ done

  b3 : Chain (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b3 = at 15 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0432 c4)) ▸
       at 12 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 9 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 11 5 (CCZ013 ∷ []) (sym (wl0833 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b4 = at 6 4 (CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0433 c4)) ▸
       at 4 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4)) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 12 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸ done

  b5 : Chain (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b5 = at 9 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0432 c4)) ▸
       at 6 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 3 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0833 (lit c4))) ▸ done

  b6 : Chain (X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b6 = at 0 4 (CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0433 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b7 : Chain (CS24 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b7 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4 CS23^0|S3^1: 30 steps
lem-F4-CS23ᵖ0∣S3ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣S3ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS12⁻ ∷ []) (refl) ▸
       at 12 4 (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 14 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b1 = at 9 4 (CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0836 (lit c4))) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 6 4 (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0837 (lit c4))) ▸
       at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0836 (lit c4))) ▸
       at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 4 (CS34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0434 c4)) ▸
       at 6 4 (CS34 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0435 c4)) ▸
       at 3 4 (CS34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0434 c4)) ▸
       at 0 4 (CS34 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0435 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b3 : Chain (CS34 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | K0 @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ K0 ∷ []) (K0 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 1 2 (K0 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2442 c4) ▸
       at 0 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 CS23^0|K0^1: 131 steps
lem-F4-CS23ᵖ0∣K0ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣K0ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b0 = at 3 1 (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp0126 c4) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb0-2-43-1 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b1 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS12⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 15 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0839 (lit c4))) ▸
       at 8 1 (CS12 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 9 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ X4 ∷ Toff024 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b2 = at 4 4 (S4⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0839 (lit c4))) ▸
       at 2 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0436 c4)) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0437 c4)) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0436 c4)) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff024 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b3 = at 1 4 (S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0437 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b4 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 1 (CS12⁻ ∷ []) (refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b5 = at 14 4 (CS04 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wp0426 c4)) ▸
       at 16 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 11 4 (CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wp0427 c4)) ▸
       at 9 1 (CS12 ∷ []) (refl) ▸
       at 8 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 10 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 5 4 (CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wp0427 c4)) ▸
       at 3 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b6 = at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 4 (CS04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0428 c4)) ▸
       at 8 4 (CS04 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0429 c4)) ▸
       at 5 4 (CS04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0428 c4)) ▸
       at 2 4 (CS04 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0429 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b7 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b8 = at 5 2 (K0 ∷ X4 ∷ []) (sym (wl0772 (lit c4))) ▸
       at 4 2 (K0 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at122441 c4) ▸
       at 3 2 (K0 ∷ X4 ∷ []) (sym (wl0772 (lit c4))) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K0 ∷ CS04 ∷ [])
  b9 = at 17 1 (CS12⁻ ∷ []) (refl) ▸
       at 16 4 (CS04 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wp0426 c4)) ▸
       at 18 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 13 4 (CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wp0427 c4)) ▸
       at 11 1 (CS12 ∷ []) (refl) ▸
       at 10 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 12 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 4 (CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wp0427 c4)) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K0 ∷ CS04 ∷ [])
  b10 = at 5 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 4 (CS04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0428 c4)) ▸
       at 10 4 (CS04 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0429 c4)) ▸
       at 7 4 (CS04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0428 c4)) ▸
       at 4 4 (CS04 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0429 c4)) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K0 ∷ CS04 ∷ [])
  b11 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS04 ∷ [])
  b12 = at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 7 2 (K0 ∷ X4 ∷ []) (sym (wl0772 (lit c4))) ▸
       at 6 2 (K0 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at122441 c4) ▸
       at 5 2 (K0 ∷ X4 ∷ []) (sym (wl0772 (lit c4))) ▸
       at 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b13 = at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS12⁻ ∷ []) (refl) ▸
       at 18 4 (CS04 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wp0426 c4)) ▸
       at 20 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 15 4 (CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wp0427 c4)) ▸
       at 13 1 (CS12 ∷ []) (refl) ▸
       at 12 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 14 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff024 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b14 = at 9 4 (CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wp0427 c4)) ▸
       at 7 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0428 c4)) ▸
       at 12 4 (CS04 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0429 c4)) ▸
       at 9 4 (CS04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0428 c4)) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff024 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ [])
  b15 = at 6 4 (CS04 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0429 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ []) (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b16 = at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 7 (CK40 ∷ []) (sym (wp0126 c4)) ▸ done


-- auto SBOX(0;1;23;4) | K4 @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ K1 ∷ []) (K1 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 (lit c4))) ▸
       at 1 2 (K2 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2442 c4) ▸
       at 0 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 (lit c4))) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done

