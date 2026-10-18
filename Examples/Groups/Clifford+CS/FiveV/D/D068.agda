{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D068 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0193 ; wl0195 ; wl0321 ; wl0746 ; wl0748 ; wl0807 ; wl0808 ; wl0831 ; wl0921 ; wl0954 ; wl1380 ; wl1421 ; wl1422 ; wl1432 ; wl1433 ; wl1434 ; wl1435 ; wl1436 ; wl1437 ; wl1438 ; wl1439 ; wl1440 ; wl1441 ; wl1442 ; wl1443 ; wl1444 ; wl1445 ; wl1446 ; wl1447 ; wl1448 ; wl1449 ; wl1450 ; wl1451 ; wl1452 ; wl1453 ; wl1454 ; wp0021 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0039 ; wp0161 ; wp0179 ; wp0653 ; wp0655 ; wp0746 ; wp0760 ; wp1143 ; wp1275 ; wp1276 ; wp1282 ; wp1283 ; wp1284 ; wp1285 ; wp1286 ; wp1287 ; wp1288 ; wp1289 ; wp1290 ; wp1291 ; wp1292 ; wp1293 ; wp1294 ; wp1295 ; wp1296 ; wp1297 ; wp1298 ; wp1299 ; wp1300 ; wp1301 ; wp1302 ; wp1303 ; wp1304 ; wp1305)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D007 using (lem-sym-bc-at0210243143)
open import Examples.Groups.Clifford+CS.FiveV.D.D009 using (lem-sym-ab-at0214203143)
open import Examples.Groups.Clifford+CS.FiveV.D.D016 using (lem-box-cP-at0214203143)
open import Examples.Groups.Clifford+CS.FiveV.D.D034 using (lem-box-cP-at0214233041 ; lem-pairs-at0210213443)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CX31-CCZ024)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-TOFF213-CSd04)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CCZ024-CX31)
open import Examples.Groups.Clifford+CS.FiveV.D.R008 using (lem-comm-CX40-TOFF213 ; lem-comm-TOFF213-CX40)
-- F4-CS2-CS2 @0213243140: 286 steps
lem-F4-CS2-CS2-at0213243140 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-CS2-at0213243140 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 4 2 (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) (wl1432 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 6 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 9 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 7 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 7 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
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

  b3 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ CCZ024 ∷ CS34⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b3 = at 6 2 (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 8 2 (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4)) ▸
       at 5 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 4 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b4 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 5 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸
       at 7 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸ done

  b5 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ CCZ024 ∷ Toff301 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b5 = at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 12 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 11 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 9 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 7 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 8 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸ done

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

  b8 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CCZ024 ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b8 = at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 6 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 3 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 8 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 7 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b9 : Chain (X0 ∷ Bx2-4013 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CCZ024 ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b9 = at 5 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 4 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 2 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 3 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸
       at 5 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸ done

  b10 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b10 = at 10 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 9 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 7 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 6 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
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

  b12 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ Toff213 ∷ CCZ014 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b12 = at 5 2 (Toff213 ∷ Toff201 ∷ []) (wl0921 (lit c4)) ▸
       at 6 3 (CCZ014 ∷ []) (sym (wp1275 c4)) ▸
       at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 0 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 2 2 (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) (wl1432 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸ done

  b13 : Chain (CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b13 = at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 7 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 5 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b14 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b14 = at 3 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b15 : Chain (Bx2-4013 ∷ X0 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b15 = at 4 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 3 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 3 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 4 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 7 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b16 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b16 = at 6 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 5 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
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

  b19 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ Toff301 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b19 = at 10 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 10 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 11 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 12 2 (CS01⁻ ∷ CCZ024 ∷ []) (wp0179 c4) ▸
       at 13 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 14 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸ done

  b20 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff213 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b20 = at 9 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
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

  b22 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff201 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ Toff213 ∷ CS14 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CX13 ∷ CCZ024 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b22 = at 12 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 8 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 9 2 (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (sym (wl1435 (lit c4))) ▸
       at 3 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸
       at 5 3 (CCZ014 ∷ []) (sym (wp1275 c4)) ▸
       at 3 4 (CX13 ∷ Toff301 ∷ []) (wp1289 c4) ▸
       at 2 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸ done

  b23 : Chain (Bx2-4013 ∷ X0 ∷ CX13 ∷ CCZ024 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CX13 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b23 = at 3 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 4 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 5 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 6 2 (CS01⁻ ∷ CCZ024 ∷ []) (wp0179 c4) ▸
       at 7 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 8 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 9 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 3 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸ done

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

  b27 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b27 = at 5 6 (CX13 ∷ Toff301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1287 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 7 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 9 2 (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (sym (wl1435 (lit c4))) ▸
       at 6 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸
       at 12 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸ done

  b28 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 12 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 13 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 14 2 (CS01⁻ ∷ CCZ024 ∷ []) (wp0179 c4) ▸
       at 15 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 16 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 11 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸ done

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

  b31 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff201 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff213 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b31 = at 10 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 11 2 (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (sym (wl1435 (lit c4))) ▸
       at 5 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸
       at 7 3 (CCZ014 ∷ []) (sym (wp1275 c4)) ▸
       at 5 4 (CX13 ∷ Toff301 ∷ []) (wp1289 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b32 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ Toff301 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b32 = at 6 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 7 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 8 2 (CS01⁻ ∷ CCZ024 ∷ []) (wp0179 c4) ▸
       at 9 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 10 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
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


-- box-perm-1423 @0214203143: 3 steps
lem-box-perm-1423-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-box-perm-1423-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-4301 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4) ▸
       at 0 1 (Bx2-0143 ∷ []) (lem-sym-bc-at0210243143 c4) ▸
       at 0 1 (Bx2-4301 ∷ []) (lem-pairs-at0210213443 c4) ▸ done


-- F4-K3-CS2 @0213243140: 19 steps
lem-F4-K3-CS2-at0213243140 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-CS2-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (CCZ234 ∷ X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 1 (Bx2-4301 ∷ []) (lem-box-perm-1423-at0214203143 c4) ▸
       at 3 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4) ▸
       at 2 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 1 2 (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸ done

  b1 : Chain (CCZ234 ∷ X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b1 = at 1 4 (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1439 (lit c4))) ▸
       at 4 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 3 2 (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 3 4 (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1439 (lit c4))) ▸
       at 0 4 (Bx2-4301 ∷ []) (sym (lem-box-cP-at0214233041 c4)) ▸
       at 0 1 (Bx2-4013 ∷ []) (sym (lem-box-perm-1423-at0214203143 c4)) ▸
       at 1 7 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wp1292 c4)) ▸ done

  b2 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b2 = at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done


-- F4-I-K3 @0213243140: 1 steps
lem-F4-I-K3-at0213243140 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-K3-at0213243140 c4 = run b0
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b0 = at 0 4 (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1440 (lit c4))) ▸ done


-- F4-S2-K3 @0213243140: 1 steps
lem-F4-S2-K3-at0213243140 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S2-K3-at0213243140 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 4 (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1293 c4)) ▸ done


-- F4-CS2-K3 @0213243140: 21 steps
lem-F4-CS2-K3-at0213243140 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-K3-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (X0 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (K1 ∷ CK01 ∷ S0 ∷ X0 ∷ []) (sym (wl1441 (lit c4))) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK01 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1294 c4)) ▸
       at 1 1 (Bx2-4301 ∷ []) (lem-box-perm-1423-at0214203143 c4) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4) ▸
       at 4 4 (K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ []) (sym (wl1442 (lit c4))) ▸ done

  b1 : Chain (X0 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ Bx2-4301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b1 = at 3 2 (K1 ∷ CCZ234 ∷ []) (sym (c₂ (K ↑) (CCZ))) ▸
       at 4 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 5 2 (S0 ∷ CCZ234 ∷ []) (sym (c₁ (S) (CCZ ↑))) ▸
       at 2 4 (K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ []) (sym (wl1442 (lit c4))) ▸
       at 1 2 (K1 ∷ CCZ234 ∷ []) (sym (c₂ (K ↑) (CCZ))) ▸
       at 2 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 3 2 (S0 ∷ CCZ234 ∷ []) (sym (c₁ (S) (CCZ ↑))) ▸
       at 4 4 (Bx2-4301 ∷ []) (sym (lem-box-cP-at0214233041 c4)) ▸ done

  b2 : Chain (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ Bx2-4301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b2 = at 4 1 (Bx2-4013 ∷ []) (sym (lem-box-perm-1423-at0214203143 c4)) ▸
       at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 0 4 (CK01 ∷ X0 ∷ []) (sym (wl1443 (lit c4))) ▸ done


-- F4-K3-K3 @0213243140: 1 steps
lem-F4-K3-K3-at0213243140 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-K3-at0213243140 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b0 = at 0 4 (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1444 (lit c4))) ▸ done


-- F4-I-S2 @0213243140: 1 steps
lem-F4-I-S2-at0213243140 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-S2-at0213243140 c4 = run b0
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b0 = at 0 4 (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1295 c4)) ▸ done


-- F4-S2-S2 @0213243140: 1 steps
lem-F4-S2-S2-at0213243140 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S2-S2-at0213243140 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 4 (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1296 c4)) ▸ done


-- F4-CS2-S2 @0213243140: 17 steps
lem-F4-CS2-S2-at0213243140 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-S2-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (X0 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ S4 ∷ CS04⁻ ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (S4 ∷ CS04⁻ ∷ X0 ∷ []) (sym (wp1297 c4)) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 2 6 (S4 ∷ CS04⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1283 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 4 2 (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S)) ▸
       at 5 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ S4 ∷ CS04⁻ ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (X0 ∷ S4 ∷ CS04⁻ ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b1 = at 3 3 (S4 ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp1282 c4) ▸
       at 2 2 (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S)) ▸
       at 3 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4)) ▸
       at 1 3 (S4 ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp1282 c4) ▸
       at 3 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 5 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done

  b2 : Chain (X0 ∷ S4 ∷ CS04⁻ ∷ Sb2-4-01-3 ∷ X0 ∷ []) (CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b2 = at 0 3 (CS04 ∷ X0 ∷ []) (sym (wp1298 c4)) ▸ done


-- F4-K3-S2 @0213243140: 1 steps
lem-F4-K3-S2-at0213243140 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-S2-at0213243140 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b0 = at 0 4 (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wp1299 c4)) ▸ done


-- F4-I-I @0213243140: 1 steps
lem-F4-I-I-at0213243140 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-I-at0213243140 c4 = run b0
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b0 = at 0 4 (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1445 (lit c4))) ▸ done


-- F4-S2-I @0213243140: 1 steps
lem-F4-S2-I-at0213243140 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S2-I-at0213243140 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 4 (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1300 c4)) ▸ done


-- F4-CS2-I @0213243140: 15 steps
lem-F4-CS2-I-at0213243140 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-I-at0213243140 c4 = trans (run b0) (run b1)
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


-- F4-K3-I @0213243140: 1 steps
lem-F4-K3-I-at0213243140 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-I-at0213243140 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b0 = at 0 4 (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1449 (lit c4))) ▸ done


-- F4-I-S3 @0213243140: 1 steps
lem-F4-I-S3-at0213243140 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-S3-at0213243140 c4 = run b0
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ CS01 ∷ []) (CS01 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b0 = at 0 4 (CS01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1450 (lit c4))) ▸ done


-- F4-S2-S3 @0213243140: 1 steps
lem-F4-S2-S3-at0213243140 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S2-S3-at0213243140 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ CS01 ∷ []) (CS01 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 4 (CS01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1303 c4)) ▸ done


-- F4-CS2-S3 @0213243140: 15 steps
lem-F4-CS2-S3-at0213243140 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-S3-at0213243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS01 ∷ []) (X0 ∷ CCZ024 ∷ Toff213 ∷ S1 ∷ CS01⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (S1 ∷ CS01⁻ ∷ X0 ∷ []) (sym (wl1451 (lit c4))) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 2 6 (S1 ∷ CS01⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1304 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 4 3 (S1 ∷ CS01⁻ ∷ Toff213 ∷ []) (sym (wl1452 (lit c4))) ▸
       at 3 3 (S1 ∷ CS01⁻ ∷ CCZ024 ∷ []) (wp1305 c4) ▸ done

  b1 : Chain (X0 ∷ CCZ024 ∷ Toff213 ∷ S1 ∷ CS01⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (CS01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b1 = at 2 3 (S1 ∷ CS01⁻ ∷ Toff213 ∷ []) (sym (wl1452 (lit c4))) ▸
       at 1 3 (S1 ∷ CS01⁻ ∷ CCZ024 ∷ []) (wp1305 c4) ▸
       at 3 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 5 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 0 3 (CS01 ∷ X0 ∷ []) (sym (wl1453 (lit c4))) ▸ done


-- F4-K3-S3 @0213243140: 1 steps
lem-F4-K3-S3-at0213243140 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-S3-at0213243140 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ CS01 ∷ []) (CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b0 = at 0 4 (CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1454 (lit c4))) ▸ done

