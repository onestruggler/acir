{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D077 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 ; lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-X1-beta-at02203443 ; lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 ; lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 ; lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 ; lem-sym12-at0210213443 ; lem-sym12-at02203443)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-comm-CX41-TOFF203)
-- F1 CS-K0 part33: 500 steps
lem-F1-CS-K0-part33 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-part33 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b0 = at 22 6 (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 11 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 11 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b1 = at 12 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 11 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 12 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b2 = at 18 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸ done

  b3 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b3 = at 10 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 10 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 12 4 (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (CS03 ∷ []) (refl) ▸
       at 15 4 (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 18 4 (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (CS03⁻ ∷ []) (refl) ▸ done

  b4 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CCZ134 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b4 = at 21 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 22 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 10 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 12 5 (CCZ134 ∷ []) (lw0 c4 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CCZ134 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ CCZ034 ∷ Bx2-1043 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b5 = at 8 2 (X1 ∷ K3 ∷ []) (lw4 c4 (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sb2-0-41-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4) ▸
       at 10 2 (X1 ∷ K3 ∷ []) (lw4 c4 (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 11 3 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 9 1 (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4) ▸
       at 8 3 (CCZ034 ∷ Bx2-1043 ∷ []) (lem-X1-beta-at02203443 c4) ▸ done

  b6 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ CCZ034 ∷ Bx2-1043 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ CCZ034 ∷ Sb2-0-41-3 ∷ X1 ∷ CCZ034 ∷ Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b6 = at 9 1 (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4) ▸
       at 9 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 9 2 (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4) ▸
       at 10 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 12 1 (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4) ▸
       at 11 3 (CCZ034 ∷ Bx2-1043 ∷ []) (lem-X1-beta-at02203443 c4) ▸
       at 12 1 (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4) ▸ done

  b7 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ CCZ034 ∷ Sb2-0-41-3 ∷ X1 ∷ CCZ034 ∷ Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b7 = at 12 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 7 2 (CCZ034 ∷ X1 ∷ []) (pw2 c4 (X1 ∷ CCZ034 ∷ []) (CCZ034 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ034 ∷ X1 ∷ []) (pw2 c4 (X1 ∷ CCZ034 ∷ []) (CCZ034 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ034 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 c4) ▸
       at 8 2 (CCZ034 ∷ X1 ∷ []) (pw2 c4 (X1 ∷ CCZ034 ∷ []) (CCZ034 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 7 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸
       at 10 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 6 1 (ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ []) (lw4 c4 (CK10 ∷ []) (ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b8 = at 14 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b9 = at 21 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 21 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸ done

  b10 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b10 = at 13 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 15 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (CS03 ∷ []) (refl) ▸
       at 18 4 (X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 21 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 26 1 (CS03⁻ ∷ []) (refl) ▸
       at 24 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b11 = at 25 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 14 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 13 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 13 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 14 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b12 = at 17 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 13 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 14 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ CS24 ∷ X1 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b13 = at 9 6 (X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 15 2 (CCZ234 ∷ K0 ∷ []) (c₁ (K) (CCZ ↑)) ▸
       at 16 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 15 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ CS24 ∷ X1 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b14 = at 25 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) (lw2 c4 (CS01 ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (X1 ∷ CS23⁻ ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) (lw2 c4 (CS01 ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 15 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸ done

  b15 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ X1 ∷ K0 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b15 = at 17 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 14 5 (CCZ234 ∷ []) (lw0 c4 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 13 2 (CCZ234 ∷ K0 ∷ []) (c₁ (K) (CCZ ↑)) ▸
       at 14 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 15 6 (X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸ done

  b16 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ X1 ∷ K0 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b16 = at 21 2 (CCZ234 ∷ K0 ∷ []) (c₁ (K) (CCZ ↑)) ▸
       at 22 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 21 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 25 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X1 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b17 = at 22 4 (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) (lw2 c4 (CS01 ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (X1 ∷ CS23⁻ ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) (lw2 c4 (CS01 ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 21 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 24 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸ done

  b18 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X1 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Bx2-0143 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b18 = at 20 5 (CCZ234 ∷ []) (lw0 c4 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 19 2 (CCZ234 ∷ K0 ∷ []) (c₁ (K) (CCZ ↑)) ▸
       at 20 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 10 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸ done

  b19 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Bx2-0143 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b19 = at 10 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 12 6 (X1 ∷ Toff314 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (pw2 c4 (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (CS03 ∷ []) (refl) ▸
       at 25 1 (CS03⁻ ∷ []) (refl) ▸
       at 15 12 (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (pw2 c4 (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 22 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸ done

  b20 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b20 = at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 10 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 10 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 11 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b21 = at 20 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 11 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸ done

  b22 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b22 = at 17 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 9 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 11 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (CS03 ∷ []) (refl) ▸
       at 14 4 (X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸ done

  b23 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b23 = at 15 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 17 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 22 1 (CS03⁻ ∷ []) (refl) ▸
       at 20 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 21 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 10 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸ done

  b24 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b24 = at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 9 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 9 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 10 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸ done

  b25 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b25 = at 10 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (X1 ∷ Toff204 ∷ X1 ∷ S1⁻ ∷ []) (pw3 c4 (S1⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 4 (X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ []) (lw4 c4 (S1⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl) ▸
       at 13 4 (X1 ∷ Toff204 ∷ X1 ∷ S1⁻ ∷ []) (pw3 c4 (S1⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl) ▸
       at 16 4 (X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ []) (lw4 c4 (S1⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸ done

  b26 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b26 = at 10 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 8 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 10 4 (X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ []) (lw0 c4 (S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl) ▸
       at 15 1 (CS03 ∷ []) (refl) ▸
       at 13 4 (X1 ∷ CS03 ∷ X1 ∷ S1⁻ ∷ []) (lw4 c4 (S1⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 16 4 (X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ []) (lw0 c4 (S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl) ▸ done

  b27 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b27 = at 21 1 (CS03⁻ ∷ []) (refl) ▸
       at 19 4 (X1 ∷ CS03⁻ ∷ X1 ∷ S1⁻ ∷ []) (lw4 c4 (S1⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl) ▸
       at 20 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 9 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 8 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b28 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ ι ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b28 = at 6 2 (X1 ∷ ι ∷ []) (sym zc) ▸
       at 7 2 (Sb2-0-41-3 ∷ ι ∷ []) (sym zc) ▸
       at 8 2 (X1 ∷ ι ∷ []) (sym zc) ▸
       at 9 7 (CK10 ∷ []) (lw4 c4 (ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ []) (CK10 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸
       at 9 2 (X1 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b29 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ134 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b29 = at 10 2 (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4) ▸
       at 11 1 (CS03⁻ ∷ []) (refl) ▸
       at 11 2 (X1 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (X1 ∷ K3⁻ ∷ []) (lw4 c4 (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Sb2-0-41-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4) ▸
       at 12 2 (X1 ∷ K3⁻ ∷ []) (lw4 c4 (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b30 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ134 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b30 = at 9 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (X1 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4) ▸
       at 15 2 (X1 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done

  b31 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b31 = at 24 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 14 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 14 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸ done

  b32 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b32 = at 13 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 c4) ▸
       at 14 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 c4) ▸
       at 12 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 13 6 (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸ done

  b33 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b33 = at 19 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 c4) ▸
       at 20 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 16 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 c4) ▸
       at 18 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 19 6 (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸ done

  b34 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b34 = at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 11 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 11 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 11 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 20 1 (CS03 ∷ []) (refl) ▸
       at 13 12 (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b35 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b35 = at 26 1 (CS03⁻ ∷ []) (refl) ▸
       at 22 6 (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 11 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b36 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b36 = at 11 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 12 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 11 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 12 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done

  b37 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b37 = at 15 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸ done

  b38 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b38 = at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 10 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 10 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 12 4 (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (CS03 ∷ []) (refl) ▸
       at 15 4 (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 18 4 (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done

  b39 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b39 = at 23 1 (CS03⁻ ∷ []) (refl) ▸
       at 21 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 22 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 10 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b40 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ X1 ∷ Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b40 = at 12 5 (CCZ134 ∷ []) (lw0 c4 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (X1 ∷ K3 ∷ []) (lw4 c4 (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sb2-0-41-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4) ▸
       at 10 2 (X1 ∷ K3 ∷ []) (lw4 c4 (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 11 3 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 7 2 (X1 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b41 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ Toff314 ∷ X1 ∷ Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CCZ134 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b41 = at 8 2 (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4) ▸
       at 9 1 (CS03 ∷ []) (refl) ▸
       at 9 2 (X1 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 6 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (X1 ∷ K3⁻ ∷ []) (lw4 c4 (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sb2-0-41-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4) ▸
       at 10 2 (X1 ∷ K3⁻ ∷ []) (lw4 c4 (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b42 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CCZ134 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b42 = at 7 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (X1 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4) ▸
       at 13 2 (X1 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 13 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done

  b43 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b43 = at 22 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 12 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 12 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 13 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸ done

  b44 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b44 = at 11 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 c4) ▸
       at 12 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 c4) ▸
       at 10 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 11 6 (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸ done

  b45 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b45 = at 17 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 c4) ▸
       at 18 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 14 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 c4) ▸
       at 16 2 (X1 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 17 6 (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸ done

  b46 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b46 = at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 9 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 9 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 9 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 18 1 (CS03 ∷ []) (refl) ▸
       at 11 12 (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b47 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b47 = at 24 1 (CS03⁻ ∷ []) (refl) ▸
       at 20 6 (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 21 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 10 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 9 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b48 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b48 = at 9 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 10 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 9 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 10 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done

  b49 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b49 = at 13 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸ done

  b50 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b50 = at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 8 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 8 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 10 4 (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (CS03 ∷ []) (refl) ▸
       at 13 4 (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 16 4 (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done

  b51 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b51 = at 21 1 (CS03⁻ ∷ []) (refl) ▸
       at 19 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 9 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 8 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b52 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-1043 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b52 = at 10 5 (CCZ134 ∷ []) (lw0 c4 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (X1 ∷ K3 ∷ []) (lw4 c4 (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sb2-0-41-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4) ▸
       at 8 2 (X1 ∷ K3 ∷ []) (lw4 c4 (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 7 1 (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4) ▸ done

  b53 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-1043 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ CCZ034 ∷ Sb2-0-41-3 ∷ X1 ∷ CCZ034 ∷ Bx2-1043 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b53 = at 6 3 (CCZ034 ∷ Bx2-1043 ∷ []) (lem-X1-beta-at02203443 c4) ▸
       at 7 1 (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4) ▸
       at 7 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 7 2 (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4) ▸
       at 8 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 10 1 (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4) ▸
       at 9 3 (CCZ034 ∷ Bx2-1043 ∷ []) (lem-X1-beta-at02203443 c4) ▸ done

  b54 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ CCZ034 ∷ Sb2-0-41-3 ∷ X1 ∷ CCZ034 ∷ Bx2-1043 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b54 = at 10 1 (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4) ▸
       at 10 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 5 2 (CCZ034 ∷ X1 ∷ []) (pw2 c4 (X1 ∷ CCZ034 ∷ []) (CCZ034 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ X1 ∷ []) (pw2 c4 (X1 ∷ CCZ034 ∷ []) (CCZ034 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 c4) ▸
       at 6 2 (CCZ034 ∷ X1 ∷ []) (pw2 c4 (X1 ∷ CCZ034 ∷ []) (CCZ034 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸
       at 8 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b55 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b55 = at 4 1 (ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ []) (lw4 c4 (CK10 ∷ []) (ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 13 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 13 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done

  b56 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b56 = at 16 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸ done

  b57 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b57 = at 14 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 11 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 13 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (CS03 ∷ []) (refl) ▸
       at 16 4 (X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 19 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 24 1 (CS03⁻ ∷ []) (refl) ▸ done

  b58 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b58 = at 22 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 12 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 11 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 11 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b59 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b59 = at 12 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 11 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 12 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done

  b60 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X1 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b60 = at 18 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 7 6 (X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 13 2 (CCZ234 ∷ K0 ∷ []) (c₁ (K) (CCZ ↑)) ▸
       at 14 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 13 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done

  b61 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X1 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CS23 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b61 = at 20 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X1 ∷ X1 ∷ []) (lw4 c4 [] (X1 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) (lw2 c4 (CS01 ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (X1 ∷ CS23⁻ ∷ X1 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) (lw2 c4 (CS01 ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 13 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸ done

  b62 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CS23 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b62 = at 14 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw4 c4 (X1 ∷ X1 ∷ []) [] tt tt Eq.refl) ▸
       at 12 5 (CCZ234 ∷ []) (lw0 c4 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done

