{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D027 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0181 ; wl0207 ; wl0209 ; wl0217 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0263 ; wl0274 ; wl0508 ; wl1000 ; wl1292 ; wl1293 ; wp0053 ; wp0054 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0069 ; wp0070 ; wp0072 ; wp0074 ; wp0278 ; wp0632 ; wp0633 ; wp0805 ; wp0806)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at243243 ; lem-box2-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D007 using (lem-box-perm-1423-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-S2-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.FiveV.D.D015 using (lem-S2-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.FiveV.D.D018 using (lem-CKc-box-at233442 ; lem-box-perm-1342-at233442)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CCZ014-CS23 ; lem-comm-CCZ014-CSd23 ; lem-comm-CCZ014-CX23 ; lem-comm-TOFF023-CX14)
-- nf-rel-268@1: 473 steps
lem-nf-rel-268at1 : Ws → ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ []) ⟫ʷ
lem-nf-rel-268at1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (run b59)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ [])
  b0 = at 2 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 5 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 8 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CS13⁻ ∷ []) (refl) ▸
       at 10 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 12 1 (CS13 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ [])
  b1 = at 14 1 (CS13⁻ ∷ []) (refl) ▸
       at 10 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 13 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 12 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 15 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 14 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 15 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 16 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ Toff023 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ [])
  b2 = at 17 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 18 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 19 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 20 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 14 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 11 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 13 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 12 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸ done

  b3 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ Toff023 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ [])
  b3 = at 13 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 14 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 15 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 16 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 12 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 13 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 11 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 10 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸ done

  b4 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ [])
  b4 = at 12 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 11 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 12 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 15 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 16 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸ done

  b5 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Bx0-1423 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ [])
  b5 = at 11 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 12 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 12 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 15 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 14 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 13 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 12 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 13 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b6 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Bx0-1423 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ [])
  b6 = at 13 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 16 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 15 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 18 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 17 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 18 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 19 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 20 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b7 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ Toff023 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ [])
  b7 = at 21 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 22 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 23 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 17 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 14 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 16 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 15 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 16 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸ done

  b8 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ Toff023 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ [])
  b8 = at 17 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 18 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 19 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 15 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 16 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 14 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 13 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 15 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b9 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ [])
  b9 = at 14 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 15 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 16 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 17 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 18 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 19 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 20 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 14 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b10 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1342 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ [])
  b10 = at 15 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 15 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 18 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 17 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 16 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 15 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 16 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 16 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸ done

  b11 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1342 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ Toff023 ∷ CK42 ∷ S4 ∷ [])
  b11 = at 16 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) (lem-CKc-box-at233442 c4) ▸
       at 19 1 (Bx0-1423 ∷ []) (lem-box-perm-1342-at233442 c4) ▸
       at 19 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 22 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸
       at 22 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 21 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 22 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 23 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b12 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ Toff023 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ S4 ∷ [])
  b12 = at 24 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 25 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 21 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 20 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸
       at 20 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 19 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 20 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 21 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b13 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ S4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ S4 ∷ [])
  b13 = at 22 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 23 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 19 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 20 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 20 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 20 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) (lem-CKc-box-at233442 c4) ▸
       at 23 1 (Bx0-1423 ∷ []) (lem-box-perm-1342-at233442 c4) ▸
       at 23 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸ done

  b14 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ S4 ∷ []) (CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b14 = at 26 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 25 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 24 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 23 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 24 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 0 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 3 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 2 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸ done

  b15 : Chain (CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b15 = at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 4 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 5 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 10 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸ done

  b16 : Chain (CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b16 = at 4 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 1 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 3 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 2 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 3 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 4 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 5 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 6 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸ done

  b17 : Chain (CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b17 = at 2 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 3 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 0 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 2 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 1 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 2 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 3 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b18 : Chain (CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b18 = at 4 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 5 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 7 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 1 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b19 : Chain (CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b19 = at 4 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 3 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 2 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 5 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 8 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b20 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b20 = at 7 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 8 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 13 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 7 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b21 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b21 = at 4 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 6 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 5 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 9 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b22 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b22 = at 6 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 4 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 3 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 4 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 5 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b23 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b23 = at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 10 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 4 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸ done

  b24 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CCZ234 ∷ Toff023 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b24 = at 6 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 5 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 6 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) (lem-CKc-box-at233442 c4) ▸
       at 9 1 (Bx0-1423 ∷ []) (lem-box-perm-1342-at233442 c4) ▸
       at 9 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 12 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸ done

  b25 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CCZ234 ∷ Toff023 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ CCZ234 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b25 = at 12 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 11 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 12 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 14 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 15 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 10 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸ done

  b26 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ CCZ234 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ Bx0-1423 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b26 = at 10 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 9 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 10 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 12 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 9 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 10 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b27 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ Bx0-1423 ∷ CK42 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b27 = at 10 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 10 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) (lem-CKc-box-at233442 c4) ▸
       at 13 1 (Bx0-1423 ∷ []) (lem-box-perm-1342-at233442 c4) ▸
       at 13 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 16 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 15 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 14 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 13 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸ done

  b28 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b28 = at 14 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 14 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 18 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 17 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 18 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 19 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 20 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 21 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸ done

  b29 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ014 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b29 = at 17 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 16 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 16 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 15 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 16 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 17 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 18 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 19 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸ done

  b30 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ014 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b30 = at 15 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 14 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 15 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 15 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 19 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 18 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 19 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 20 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸ done

  b31 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ014 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b31 = at 21 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 22 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 18 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 17 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 17 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 16 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 17 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 18 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸ done

  b32 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ014 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b32 = at 19 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 20 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 16 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 15 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 16 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 16 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 19 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 18 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸ done

  b33 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b33 = at 21 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 20 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 21 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 22 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 23 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 24 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 25 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 26 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸ done

  b34 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b34 = at 20 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 17 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 19 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 18 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 19 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 20 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 21 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 22 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸ done

  b35 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b35 = at 18 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 19 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 17 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 16 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 18 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 17 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 18 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 19 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b36 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b36 = at 20 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 21 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 22 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 23 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 17 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 18 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 18 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 21 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b37 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS24 ∷ CX14 ∷ Toff023 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b37 = at 20 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 19 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 18 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 19 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 19 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 23 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 22 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 23 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸ done

  b38 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS24 ∷ CX14 ∷ Toff023 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ CS24 ∷ CX14 ∷ Toff023 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b38 = at 24 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 25 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 26 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 22 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 21 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 21 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 20 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 21 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸ done

  b39 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ CS24 ∷ CX14 ∷ Toff023 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b39 = at 22 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 23 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 24 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 20 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 19 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 20 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 20 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 23 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸ done

  b40 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b40 = at 22 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 25 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 24 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 25 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 26 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 27 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 28 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 29 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸ done

  b41 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff023 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b41 = at 30 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 24 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 21 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 23 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 22 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 23 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 24 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 25 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸ done

  b42 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff023 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b42 = at 26 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 22 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 23 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 21 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 20 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 22 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 21 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 22 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸ done

  b43 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b43 = at 23 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 24 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 25 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 26 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 27 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 21 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 22 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 22 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸ done

  b44 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b44 = at 25 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 24 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 23 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 22 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 23 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 23 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 26 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸
       at 26 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b45 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b45 = at 25 2 (CS23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CS23 (lit c4)) ▸
       at 26 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 27 2 (CS23⁻ ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CSd23 (lit c4)) ▸
       at 28 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 29 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 25 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 24 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸
       at 24 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b46 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ Bx0-1342 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b46 = at 23 2 (CS23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CS23 (lit c4)) ▸
       at 24 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 25 2 (CS23⁻ ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CSd23 (lit c4)) ▸
       at 26 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 27 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 23 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 24 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 24 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸ done

  b47 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ Bx0-1342 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b47 = at 24 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) (lem-CKc-box-at233442 c4) ▸
       at 27 1 (Bx0-1423 ∷ []) (lem-box-perm-1342-at233442 c4) ▸
       at 27 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 30 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸
       at 30 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 29 2 (CS23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CS23 (lit c4)) ▸
       at 30 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 31 2 (CS23⁻ ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CSd23 (lit c4)) ▸ done

  b48 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b48 = at 32 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 33 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 29 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 28 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸
       at 28 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 27 2 (CS23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CS23 (lit c4)) ▸
       at 28 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 29 2 (CS23⁻ ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CSd23 (lit c4)) ▸ done

  b49 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff023 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b49 = at 30 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 31 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 27 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 28 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 28 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 31 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸
       at 31 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 30 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸ done

  b50 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff023 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b50 = at 31 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 32 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 33 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 34 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 30 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 29 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸
       at 29 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 28 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸ done

  b51 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CCZ123 ∷ Toff023 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b51 = at 29 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 30 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 31 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 32 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 28 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 29 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 29 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 32 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸ done

  b52 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CCZ123 ∷ Toff023 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ014 ∷ CCZ123 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b52 = at 32 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 31 2 (CS23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CS23 (lit c4)) ▸
       at 32 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 33 2 (CS23⁻ ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CSd23 (lit c4)) ▸
       at 34 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 35 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 31 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 30 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸ done

  b53 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ014 ∷ CCZ123 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ Bx0-1423 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b53 = at 30 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 29 2 (CS23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CS23 (lit c4)) ▸
       at 30 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 31 2 (CS23⁻ ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CSd23 (lit c4)) ▸
       at 32 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 33 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 29 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 30 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b54 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ Bx0-1423 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CCZ014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ S4 ∷ Bx0-1423 ∷ [])
  b54 = at 30 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 30 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) (lem-CKc-box-at233442 c4) ▸
       at 33 1 (Bx0-1423 ∷ []) (lem-box-perm-1342-at233442 c4) ▸
       at 33 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 36 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸
       at 36 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 35 2 (CS23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CS23 (lit c4)) ▸
       at 36 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸ done

  b55 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CCZ014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS23 ∷ CX12 ∷ CCZ014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ S4 ∷ Bx0-1423 ∷ [])
  b55 = at 37 2 (CS23⁻ ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CSd23 (lit c4)) ▸
       at 38 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 39 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 35 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 34 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸
       at 34 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 33 2 (CS23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CS23 (lit c4)) ▸
       at 34 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸ done

  b56 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS23 ∷ CX12 ∷ CCZ014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ S4 ∷ Bx0-1423 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ S4 ∷ CCZ014 ∷ Toff023 ∷ Bx0-1423 ∷ [])
  b56 = at 35 2 (CS23⁻ ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CSd23 (lit c4)) ▸
       at 36 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 37 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 33 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 34 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 34 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 37 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 36 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸ done

  b57 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ S4 ∷ CCZ014 ∷ Toff023 ∷ Bx0-1423 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ [])
  b57 = at 35 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 34 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 35 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 35 2 [] (lem-box2-at243243 c4) ▸
       at 0 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 2 2 [] (wl0263 (lit c4)) ▸
       at 4 26 (CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ []) (wl1292 (lit c4)) ▸
       at 29 2 [] (wl0181 (lit c4)) ▸ done

  b58 : Chain (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ [])
  b58 = at 5 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 6 2 [] (wl0181 (lit c4)) ▸
       at 7 11 (S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ []) (wl1293 (lit c4)) ▸
       at 17 2 [] (wl0181 (lit c4)) ▸
       at 8 2 [] (wl0263 (lit c4)) ▸
       at 8 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 10 2 [] (wl0263 (lit c4)) ▸
       at 15 2 [] (wl0181 (lit c4)) ▸ done

  b59 : Chain (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ [])
  b59 = at 16 2 [] (wl0181 (lit c4)) ▸ done

