{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D024 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0297 ; wl0321 ; wl0617 ; wl0808 ; wl0881 ; wl0882 ; wl0883 ; wl0884 ; wl0954 ; wl1432 ; wl1433 ; wl1434 ; wl1436 ; wl1437 ; wl1438 ; wl1625 ; wp0007 ; wp0021 ; wp0032 ; wp0033 ; wp0036 ; wp0037 ; wp0039 ; wp0109 ; wp0127 ; wp0155 ; wp0156 ; wp0157 ; wp0161 ; wp0285 ; wp0311 ; wp0312 ; wp0314 ; wp1143 ; wp1284 ; wp1285 ; wp1288 ; wl0341 ; wl0461 ; wl0470 ; wl0861 ; wl0879 ; wl0929 ; wl1226 ; wl1430 ; wl1431 ; wl1501 ; wl1509 ; wl1517 ; wl1519 ; wl1703 ; wp0053 ; wp0060 ; wp0061 ; wp0065 ; wp0306 ; wp0317 ; wp0496 ; wp1278 ; wp1279 ; wp1318 ; wp1323 ; wp1335 ; wp1354 ; wp1355 ; wp1356 ; wl0635 ; wl0636 ; wl0788 ; wp1281 ; wl0193 ; wl0195 ; wl0746 ; wl0748 ; wl0807 ; wl0880 ; wl0921 ; wl1421 ; wl1422 ; wl1435 ; wl1446 ; wl1447 ; wl1448 ; wp0035 ; wp0104 ; wp0110 ; wp0653 ; wp0655 ; wp0760 ; wp1275 ; wp1276 ; wp1280 ; wp1282 ; wp1283 ; wp1286 ; wp1287 ; wp1289 ; wp1290 ; wp1291 ; wp1301 ; wp1302)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym-ab-at04122140 ; lem-sym-ab-at0412233140)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-tQ-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at043043)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at02132031 ; lem-box-tQ-at022440 ; lem-box-tQ-at03243240 ; lem-box-tQ-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-box-tQ-at0410233142 ; lem-box-tQ-at04122140 ; lem-box-tQ-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D013 using (lem-P-box-at02132031 ; lem-P-box-at022440 ; lem-P-box-at03122031 ; lem-P-box-at0410233142 ; lem-P-box-at0412233140 ; lem-P-box-at0413203241 ; lem-P-box-at043043 ; lem-t-cP-at04122041 ; lem-t-cP-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-box-cP-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at02132031 ; lem-box-cP-at0214203143 ; lem-box-cP-at022440 ; lem-box-cP-at03122031 ; lem-box-cP-at0314203142 ; lem-box-cP-at043043 ; lem-sym-bc-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at0410233142 ; lem-box-cP-at04122041 ; lem-box-cP-at0412233140 ; lem-box-cP-at0413203241 ; lem-box-cP-at0440 ; lem-box2-at04203243 ; lem-pairs-at04203243 ; lem-sym-bc-at0412233140 ; lem-sym-bc-at04133140)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-CCZ034 ; lem-comm-CS13-CCZ024 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX13-CCZ024 ; lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CX13 ; lem-comm-CS04-TOFF213 ; lem-comm-CX40-TOFF312)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX40-TOFF213 ; lem-comm-TOFF213-CX40)

-- CSu-box-3 @0314203142: 17 steps
lem-CSu-box-3-at0314203142 : Ws → ⟪ (CS13 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CS13 ∷ []) ⟫ʷ
lem-CSu-box-3-at0314203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS13 ∷ Bx3-4012 ∷ []) (CCZ034 ∷ Toff312 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 0 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 1 2 (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ []) (wl0881 (lit c4)) ▸
       at 4 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 7 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸ done

  b1 : Chain (CCZ034 ∷ Toff312 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ [])
  b1 = at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 5 2 (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (wl0882 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS12 ∷ []) (wl0883 (lit c4)) ▸
       at 3 2 (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ []) (wl0881 (lit c4)) ▸
       at 4 6 (CS13 ∷ []) (wl0884 (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ []) (Bx3-4012 ∷ CS13 ∷ [])
  b2 = at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸ done

-- box-perm-1342 @04203243: 3 steps
lem-box-perm-1342-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-box-perm-1342-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-1230 ∷ [])
  b0 = at 0 1 (Bx4-2310 ∷ []) (lem-pairs-at04203243 c4) ▸
       at 0 1 (Bx4-2130 ∷ []) (lem-sym-bc-at0412233140 c4) ▸
       at 0 1 (Bx4-1230 ∷ []) (lem-sym-ab-at04122140 c4) ▸ done

-- pairs @0410233142: 4 steps
lem-pairs-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-pairs-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ []) (Bx4-1203 ∷ [])
  b0 = at 0 1 (Toff412 ∷ Bx4-0312 ∷ Toff412 ∷ []) (sym (lem-P-box-at0410233142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-box-cP-at0410233142 c4) ▸
       at 4 2 [] (wl0470 (lit c4)) ▸
       at 0 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸ done

-- pairs @043043: 4 steps
lem-pairs-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ []) ⟫ʷ
lem-pairs-at043043 c4 = run b0
  where
  b0 : Chain (Bx4-1203 ∷ []) (Bx4-0312 ∷ [])
  b0 = at 0 1 (Toff403 ∷ Bx4-1203 ∷ Toff403 ∷ []) (sym (lem-P-box-at043043 c4)) ▸
       at 1 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 4 2 [] (wp0317 c4) ▸
       at 0 4 (Bx4-0312 ∷ []) (sym (lem-box-tQ-at0410233142 c4)) ▸ done

-- pairs @0412233140: 4 steps
lem-pairs-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-pairs-at0412233140 c4 = run b0
  where
  b0 : Chain (Bx4-2310 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 0 1 (Toff401 ∷ Bx4-2310 ∷ Toff401 ∷ []) (sym (lem-P-box-at0412233140 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233140 c4) ▸
       at 4 2 [] (wp0306 c4) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-tQ-at04203243 c4)) ▸ done

-- F4-I-CS0 @0440: 15 steps
lem-F4-I-CS0-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-CS0-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ S0 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 0 4 (CCZ024 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1278 c4)) ▸
       at 1 4 (Toff213 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1430 (lit c4))) ▸
       at 2 4 (CCZ024 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1278 c4)) ▸
       at 3 4 (Toff213 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1430 (lit c4))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ S0 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b1 = at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 1 7 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1279 c4)) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 1 3 (ι ∷ S0⁻ ∷ []) (wl1431 (lit c4)) ▸
       at 1 2 (X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1431 (lit c4))) ▸ done

-- box-perm-1324 @0214203143: 1 steps
lem-box-perm-1324-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-box-perm-1324-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 1 (Bx2-4103 ∷ []) (lem-sym-bc-at0214203143 c4) ▸ done

-- S2-SBOX(0;1;42;3) @0440: 86 steps
lem-S2-SBOX⟨0·1·42·3⟩-at0440 : Ws → ⟪ (Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·1·42·3⟩-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CCZ014 ∷ CS13⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 2 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸ done

  b1 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CCZ014 ∷ CS13⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CCZ014 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b1 = at 5 2 (Toff423 ∷ CS13⁻ ∷ []) (wl1517 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 7 2 (Toff423 ∷ CS13⁻ ∷ []) (wl1517 (lit c4)) ▸
       at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 3 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 9 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 8 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸ done

  b2 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CCZ014 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b2 = at 7 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 5 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 3 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 4 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 4 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 6 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b3 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b3 = at 12 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 11 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 10 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 6 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 7 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b4 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff402 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b4 = at 5 2 (CCZ014 ∷ Toff402 ∷ CCZ012 ∷ []) (sym (wp1335 c4)) ▸
       at 8 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 7 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 11 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 10 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 9 2 (Toff423 ∷ CS02⁻ ∷ []) (wp1355 c4) ▸
       at 8 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 7 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸ done

  b5 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff402 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CS13 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b5 = at 8 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 6 2 (Toff423 ∷ Toff402 ∷ []) (wp1318 c4) ▸
       at 7 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 3 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 3 2 (Toff423 ∷ CS13 ∷ []) (wl1509 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸ done

  b6 : Chain (Bx4-1023 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CS13 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ K3 ∷ CS03 ∷ CX23 ∷ CCZ014 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b6 = at 5 2 (Toff423 ∷ CS13 ∷ []) (wl1509 (lit c4)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 1 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 7 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 6 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 5 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸ done

  b7 : Chain (Bx4-1023 ∷ K3 ∷ CS03 ∷ CX23 ∷ CCZ014 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CCZ014 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b7 = at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 1 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 2 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 2 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 4 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 9 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸ done

  b8 : Chain (Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CCZ014 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ CCZ012 ∷ Toff423 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b8 = at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 5 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ Toff402 ∷ CCZ012 ∷ []) (sym (wp1335 c4)) ▸
       at 6 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸ done

  b9 : Chain (Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ CCZ012 ∷ Toff423 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ012 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b9 = at 5 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 9 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 8 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 7 2 (Toff423 ∷ CS02⁻ ∷ []) (wp1355 c4) ▸
       at 6 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 5 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 4 2 (Toff423 ∷ Toff402 ∷ []) (wp1318 c4) ▸ done

  b10 : Chain (Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ012 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (CCZ012 ∷ [])
  b10 = at 5 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 1 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 0 2 [] (lem-box2-at04203243 c4) ▸
       at 0 3 (Toff302 ∷ CS13 ∷ CCZ012 ∷ []) (wl1519 (lit c4)) ▸
       at 2 2 [] (wl0341 (lit c4)) ▸
       at 0 8 (CCZ012 ∷ []) (sym (wl1703 (lit c4))) ▸ done

-- box2 @04122041: 11 steps
lem-box2-at04122041 : Ws → ⟪ (Bx4-2031 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at04122041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-2031 ∷ Bx4-2031 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ [])
  b0 = at 0 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04122041 c4) ▸
       at 4 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 4 0 (Toff402 ∷ Toff402 ∷ []) (sym (wp1323 c4)) ▸
       at 5 5 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff402 ∷ []) (lem-t-cP-at04122041 c4) ▸
       at 5 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 5 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04122041 c4) ▸
       at 4 2 [] (wp1323 c4) ▸
       at 3 2 [] (wl0321 (lit c4)) ▸ done

  b1 : Chain (Toff402 ∷ CCZ134 ∷ Toff402 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) []
  b1 = at 2 2 [] (wp1323 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸
       at 0 2 [] (wp1323 c4) ▸ done

-- box2 @0440: 11 steps
lem-box2-at0440 : Ws → ⟪ (Bx4-1230 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1230 ∷ Bx4-1230 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  b0 = at 0 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at0440 c4) ▸
       at 4 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at0440 c4) ▸
       at 4 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0470 (lit c4))) ▸
       at 5 5 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ []) (lem-t-cP-at0440 c4) ▸
       at 5 4 (Bx4-1230 ∷ []) (sym (lem-box-cP-at0440 c4)) ▸
       at 5 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at0440 c4) ▸
       at 4 2 [] (wl0470 (lit c4)) ▸
       at 3 2 [] (wp0007 c4) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) []
  b1 = at 2 2 [] (wl0470 (lit c4)) ▸
       at 1 2 [] (wp0007 c4) ▸
       at 0 2 [] (wl0470 (lit c4)) ▸ done

-- pairs @0413203241: 4 steps
lem-pairs-at0413203241 : Ws → ⟪ (Bx4-3021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-pairs-at0413203241 c4 = run b0
  where
  b0 : Chain (Bx4-3021 ∷ []) (Bx4-2130 ∷ [])
  b0 = at 0 1 (Toff412 ∷ Bx4-3021 ∷ Toff412 ∷ []) (sym (lem-P-box-at0413203241 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-box-cP-at0413203241 c4) ▸
       at 4 2 [] (wl0470 (lit c4)) ▸
       at 0 4 (Bx4-2130 ∷ []) (sym (lem-box-tQ-at04122140 c4)) ▸ done

-- pairs @022440: 4 steps
lem-pairs-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-pairs-at022440 c4 = run b0
  where
  b0 : Chain (Bx2-1430 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 0 1 (Toff203 ∷ Bx2-1430 ∷ Toff203 ∷ []) (sym (lem-P-box-at022440 c4)) ▸
       at 1 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at022440 c4) ▸
       at 4 2 [] (wl0635 (lit c4)) ▸
       at 0 4 (Bx2-3014 ∷ []) (sym (lem-box-tQ-at02132031 c4)) ▸ done

-- pairs @02132031: 4 steps
lem-pairs-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-pairs-at02132031 c4 = run b0
  where
  b0 : Chain (Bx2-3014 ∷ []) (Bx2-1430 ∷ [])
  b0 = at 0 1 (Toff214 ∷ Bx2-3014 ∷ Toff214 ∷ []) (sym (lem-P-box-at02132031 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02132031 c4) ▸
       at 4 2 [] (wl0636 (lit c4)) ▸
       at 0 4 (Bx2-1430 ∷ []) (sym (lem-box-tQ-at022440 c4)) ▸ done

-- box-perm-4132 @04203243: 3 steps
lem-box-perm-4132-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-box-perm-4132-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-3120 ∷ [])
  b0 = at 0 1 (Bx4-2310 ∷ []) (lem-pairs-at04203243 c4) ▸
       at 0 1 (Bx4-3210 ∷ []) (lem-sym-ab-at0412233140 c4) ▸
       at 0 1 (Bx4-3120 ∷ []) (lem-sym-bc-at04133140 c4) ▸ done

-- pairs @03122031: 4 steps
lem-pairs-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-pairs-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 1 (Toff314 ∷ Bx3-2014 ∷ Toff314 ∷ []) (sym (lem-P-box-at03122031 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03122031 c4) ▸
       at 4 2 [] (wl0788 (lit c4)) ▸
       at 0 4 (Bx3-1420 ∷ []) (sym (lem-box-tQ-at03243240 c4)) ▸ done

-- CXu-box-4 @0314203142: 15 steps
lem-CXu-box-4-at0314203142 : Ws → ⟪ (CX23 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CX23 ∷ []) ⟫ʷ
lem-CXu-box-4-at0314203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX23 ∷ Bx3-4012 ∷ []) (CCZ034 ∷ CX23 ∷ Toff312 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 0 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (sym (wp0104 c4)) ▸
       at 2 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 6 2 (Toff312 ∷ CS24 ∷ []) (wl0879 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS02⁻ ∷ []) (wl1226 (lit c4)) ▸
       at 3 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4)) ▸ done

  b1 : Chain (CCZ034 ∷ CX23 ∷ Toff312 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ CCZ034 ∷ Toff312 ∷ []) (Bx3-4012 ∷ CX23 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸
       at 1 2 (Toff312 ∷ CX23 ∷ []) (wl0880 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 2 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (sym (wp0104 c4)) ▸
       at 3 3 (CX23 ∷ []) (wp0110 c4) ▸
       at 3 2 (Toff312 ∷ CX23 ∷ []) (wl0880 (lit c4)) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸ done

-- F4-CS0-I @0440: 15 steps
lem-F4-CS0-I-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-I-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) (X0 ∷ CCZ024 ∷ Toff213 ∷ ι ∷ S0⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (ι ∷ S0⁻ ∷ X0 ∷ []) (wl1446 (lit c4)) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 2 6 (ι ∷ S0⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (wp1301 c4) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 4 3 (ι ∷ S0⁻ ∷ Toff213 ∷ []) (wl1447 (lit c4)) ▸
       at 3 3 (ι ∷ S0⁻ ∷ CCZ024 ∷ []) (wp1302 c4) ▸ done

  b1 : Chain (X0 ∷ CCZ024 ∷ Toff213 ∷ ι ∷ S0⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (S0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b1 = at 2 3 (ι ∷ S0⁻ ∷ Toff213 ∷ []) (wl1447 (lit c4)) ▸
       at 1 3 (ι ∷ S0⁻ ∷ CCZ024 ∷ []) (wp1302 c4) ▸
       at 3 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 5 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 0 3 (S0 ∷ X0 ∷ []) (sym (wl1448 (lit c4))) ▸ done

-- F4-S0-CS0 @0440: 18 steps
lem-F4-S0-CS0-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-CS0-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (CCZ024 ∷ Toff213 ∷ X0 ∷ CS04 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 0 4 (CCZ024 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1280 c4)) ▸
       at 3 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ X0 ∷ CS04 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ S4 ∷ CS04⁻ ∷ [])
  b1 = at 2 3 (S4 ∷ CS04⁻ ∷ []) (sym (wp1281 c4)) ▸
       at 2 3 (CCZ024 ∷ S4 ∷ CS04⁻ ∷ []) (sym (wp1282 c4)) ▸
       at 4 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸
       at 3 2 (Toff213 ∷ S4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S))) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 1 6 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ S4 ∷ CS04⁻ ∷ []) (wp1283 c4) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ S4 ∷ CS04⁻ ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b2 = at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 1 2 (X0 ∷ CS04 ∷ X0 ∷ []) (wp1281 c4) ▸ done

-- F4-CS0-CS0 @0440: 286 steps
lem-F4-CS0-CS0-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-CS0-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 4 2 (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) (wl1432 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 6 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 9 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 8 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 7 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 4 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ CCZ024 ∷ CS34⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b2 = at 5 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 5 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 5 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸ done

  b3 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ CCZ024 ∷ CS34⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b3 = at 6 2 (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 8 2 (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4)) ▸
       at 5 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 4 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b4 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 5 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸
       at 7 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸ done

  b5 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ CCZ024 ∷ Toff301 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b5 = at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 12 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 7 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 8 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸ done

  b6 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ CCZ024 ∷ Toff301 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ Toff213 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff201 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b6 = at 6 2 (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp0760 c4)) ▸
       at 9 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸
       at 8 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 12 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 11 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 10 2 (Toff213 ∷ CS01⁻ ∷ []) (wl1422 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸ done

  b7 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ Toff213 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff201 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b7 = at 9 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 7 2 (Toff213 ∷ Toff201 ∷ []) (wl0921 (lit c4)) ▸
       at 8 3 (CCZ014 ∷ []) (sym (wp1275 c4)) ▸
       at 4 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 3 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸ done

  b8 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b8 = at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 6 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 3 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 8 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 7 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b9 : Chain (X0 ∷ Bx2-4013 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b9 = at 5 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 2 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 3 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸
       at 5 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸ done

  b10 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b10 = at 10 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 6 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp0760 c4)) ▸ done

  b11 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ Toff213 ∷ CCZ014 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b11 = at 7 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸
       at 6 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 10 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CS01⁻ ∷ []) (wl1422 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸ done

  b12 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ Toff213 ∷ CCZ014 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b12 = at 5 2 (Toff213 ∷ Toff201 ∷ []) (wl0921 (lit c4)) ▸
       at 6 3 (CCZ014 ∷ []) (sym (wp1275 c4)) ▸
       at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 0 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 2 2 (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) (wl1432 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸ done

  b13 : Chain (CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b13 = at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 7 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b14 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ024 ∷ CX41 ∷ CS34 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b14 = at 3 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸ done

  b15 : Chain (Bx2-4013 ∷ X0 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ024 ∷ CX41 ∷ CS34 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ024 ∷ CX41 ∷ CS34 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b15 = at 4 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 2 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 3 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 3 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 4 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 7 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸ done

  b16 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ024 ∷ CX41 ∷ CS34 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b16 = at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 5 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 8 (CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ []) (sym (wp1286 c4)) ▸
       at 10 2 [] (wl0321 (lit c4)) ▸ done

  b17 : Chain (Bx2-4013 ∷ X0 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b17 = at 3 3 (Toff301 ∷ CS34 ∷ CCZ014 ∷ []) (wp1276 c4) ▸
       at 5 2 [] (wp0161 c4) ▸
       at 4 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 6 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 2 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 3 2 (CX13 ∷ Toff301 ∷ X0 ∷ []) (sym (wl1434 (lit c4))) ▸
       at 2 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (CS34 ∷ []) (refl) ▸ done

  b18 : Chain (Bx2-4013 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ Toff301 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b18 = at 6 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 6 (CX13 ∷ Toff301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1287 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 5 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 7 2 (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (sym (wl1435 (lit c4))) ▸
       at 4 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸ done

  b19 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ Toff301 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b19 = at 10 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 10 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸ done

  b20 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff213 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b20 = at 9 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 3 2 (CX12 ∷ Toff213 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 5 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 4 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 5 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 6 2 (CS01⁻ ∷ Toff213 ∷ []) (sym (wl1422 (lit c4))) ▸
       at 7 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 8 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸ done

  b21 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff213 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff201 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ Toff213 ∷ CS14 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b21 = at 4 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 5 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 7 2 (Toff201 ∷ Toff213 ∷ []) (sym (wl0921 (lit c4))) ▸
       at 9 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 9 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 10 2 (CS01⁻ ∷ Toff213 ∷ []) (sym (wl1422 (lit c4))) ▸
       at 11 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸ done

  b22 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff201 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ Toff213 ∷ CS14 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CX13 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b22 = at 12 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 8 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 9 2 (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (sym (wl1435 (lit c4))) ▸
       at 3 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸
       at 5 3 (CCZ014 ∷ []) (sym (wp1275 c4)) ▸
       at 3 4 (CX13 ∷ Toff301 ∷ []) (wp1289 c4) ▸
       at 2 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸ done

  b23 : Chain (Bx2-4013 ∷ X0 ∷ CX13 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CX13 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b23 = at 3 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 4 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 9 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 3 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸ done

  b24 : Chain (Bx2-4013 ∷ X0 ∷ CX13 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ CS34 ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b24 = at 4 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 1 3 (Toff301 ∷ X0 ∷ []) (sym (wl1436 (lit c4))) ▸
       at 4 2 (CS34 ∷ X0 ∷ []) (sym (wl1437 (lit c4))) ▸
       at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸ done

  b25 : Chain (Bx2-4013 ∷ Toff301 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ CS34 ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b25 = at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 4 5 (CS34 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1290 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 6 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸ done

  b26 : Chain (Bx2-4013 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ [])
  b26 = at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 2 2 (CS34 ∷ X0 ∷ []) (sym (wl1437 (lit c4))) ▸
       at 5 2 (CX13 ∷ Toff301 ∷ X0 ∷ []) (sym (wl1434 (lit c4))) ▸
       at 4 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 6 1 (CS34 ∷ []) (refl) ▸
       at 8 1 (CS34⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b27 = at 5 6 (CX13 ∷ Toff301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1287 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 7 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 9 2 (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (sym (wl1435 (lit c4))) ▸
       at 6 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸
       at 12 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸ done

  b28 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 12 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 11 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸ done

  b29 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ Toff213 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b29 = at 5 2 (CX12 ∷ Toff213 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 7 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 6 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 7 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 8 2 (CS01⁻ ∷ Toff213 ∷ []) (sym (wl1422 (lit c4))) ▸
       at 9 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 10 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸ done

  b30 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ Toff213 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff201 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff213 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b30 = at 7 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 9 2 (Toff201 ∷ Toff213 ∷ []) (sym (wl0921 (lit c4))) ▸
       at 11 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 10 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 11 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 12 2 (CS01⁻ ∷ Toff213 ∷ []) (sym (wl1422 (lit c4))) ▸
       at 13 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 14 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸ done

  b31 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff201 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff213 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b31 = at 10 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 11 2 (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (sym (wl1435 (lit c4))) ▸
       at 5 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸
       at 7 3 (CCZ014 ∷ []) (sym (wp1275 c4)) ▸
       at 5 4 (CX13 ∷ Toff301 ∷ []) (wp1289 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b32 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ Toff301 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b32 = at 6 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 6 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸ done

  b33 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ Toff301 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS34⁻ ∷ X0 ∷ [])
  b33 = at 8 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 3 3 (Toff301 ∷ X0 ∷ []) (sym (wl1436 (lit c4))) ▸
       at 6 2 (CS34⁻ ∷ X0 ∷ []) (sym (wl1438 (lit c4))) ▸
       at 5 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 7 1 (CS34 ∷ []) (refl) ▸
       at 9 1 (CS34⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS34⁻ ∷ X0 ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b34 = at 6 5 (CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1291 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 8 2 (CS34⁻ ∷ Toff213 ∷ []) (sym (wl0807 (lit c4))) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 6 2 (CS34⁻ ∷ Toff213 ∷ []) (sym (wl0807 (lit c4))) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 6 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 8 1 (Sb2-4-3-1 ∷ []) (refl) ▸ done

  b35 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b35 = at 10 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 4 2 (CS34⁻ ∷ X0 ∷ []) (sym (wl1438 (lit c4))) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done
