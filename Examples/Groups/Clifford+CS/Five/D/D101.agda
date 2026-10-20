{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D101 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0155 ; wl0191 ; wl0196 ; wl0258 ; wl0321 ; wl0392 ; wl0393 ; wl0617 ; wl0808 ; wl0954 ; wl1338 ; wl1432 ; wl1433 ; wl1434 ; wl1436 ; wl1437 ; wl1438 ; wl1545 ; wl1588 ; wl1616 ; wl1620 ; wl1621 ; wl1622 ; wl1623 ; wl1624 ; wl1625 ; wl1626 ; wl1627 ; wl1628 ; wl1629 ; wl1630 ; wl1631 ; wl1634 ; wp0007 ; wp0021 ; wp0032 ; wp0033 ; wp0036 ; wp0037 ; wp0039 ; wp0088 ; wp0089 ; wp0285 ; wp0320 ; wp0728 ; wp0729 ; wp1192 ; wp1284 ; wp1285 ; wp1398 ; wp1419 ; wp1420 ; wp1421 ; wp1422 ; wp1423 ; wp1424 ; wp1425 ; wp1426 ; wp1427 ; wp1428 ; wp1431 ; wp1432)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-CSdu-box-3-at0214203143 ; lem-CSdu-box-3-at04122041 ; lem-CSu-box-3-at0214203143 ; lem-CSu-box-3-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D033 using (lem-CXAu-S-at0410213243 ; lem-box-perm-1342-at0214203143 ; lem-box-perm-1423-at02142140 ; lem-box-perm-2431-at0440 ; lem-box-perm-4132-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D061 using (lem-CXuA-S-at0410213243 ; lem-XCKX-box-2-at0214203143 ; lem-box-box-2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX13-CCZ024 ; lem-comm-CZ13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CX13 ; lem-comm-CCZ034-CS12)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX40-TOFF213 ; lem-comm-TOFF413-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-TOFF413-CS02)

-- F4-CS2-CS0 @0440: 284 steps
lem-F4-CS2-CS0-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-CS0-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (X0 ∷ Sb4-2-03-1 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 4 2 (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) (wl1432 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 6 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb4-2-03-1 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Sb4-2-03-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 9 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 8 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 7 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 4 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb4-2-03-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b2 = at 5 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 5 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 2 (Bx2-4013 ∷ CS12⁻ ∷ []) (lem-CSdu-box-3-at0214203143 c4) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸ done

  b3 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b3 = at 4 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸ done

  b4 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff203 ∷ CCZ034 ∷ Toff213 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b4 = at 5 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff103 ∷ Toff203 ∷ []) (wl1620 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ Toff203 ∷ CCZ034 ∷ []) (sym (wp1192 c4)) ▸
       at 6 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 12 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 11 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 10 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸ done

  b5 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff203 ∷ CCZ034 ∷ Toff213 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff103 ∷ Toff203 ∷ CS03 ∷ CX40 ∷ Toff213 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b5 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 6 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 7 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 9 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 13 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 12 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 11 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸ done

  b6 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff103 ∷ Toff203 ∷ CS03 ∷ CX40 ∷ Toff213 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Bx2-4013 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b6 = at 10 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 10 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 8 2 (Toff213 ∷ Toff203 ∷ []) (wl1338 (lit c4)) ▸
       at 7 2 (Toff213 ∷ Toff103 ∷ Toff203 ∷ []) (wl1620 (lit c4)) ▸
       at 8 3 (Toff103 ∷ []) (wl1621 (lit c4)) ▸
       at 4 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸ done

  b7 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Bx2-4013 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ K1 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b7 = at 3 2 (Bx2-4013 ∷ CS12 ∷ []) (lem-CSu-box-3-at0214203143 c4) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 8 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 7 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b8 : Chain (X0 ∷ Bx4-2031 ∷ K1 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff203 ∷ CCZ034 ∷ Toff213 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b8 = at 3 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 2 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 3 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff103 ∷ Toff203 ∷ []) (wl1620 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ Toff203 ∷ CCZ034 ∷ []) (sym (wp1192 c4)) ▸
       at 4 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b9 : Chain (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff203 ∷ CCZ034 ∷ Toff213 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff103 ∷ Toff203 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ Toff213 ∷ CS34 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b9 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 5 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 7 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 11 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸ done

  b10 : Chain (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff103 ∷ Toff203 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ Toff213 ∷ CS34 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b10 = at 10 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 8 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 6 2 (Toff213 ∷ Toff203 ∷ []) (wl1338 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff103 ∷ Toff203 ∷ []) (wl1620 (lit c4)) ▸
       at 6 3 (Toff103 ∷ []) (wl1621 (lit c4)) ▸ done

  b11 : Chain (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (CCZ024 ∷ X0 ∷ CZ24 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b11 = at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 1 1 (Bx4-1230 ∷ []) (lem-box-perm-4132-at04122041 c4) ▸
       at 2 1 (Bx2-4130 ∷ []) (lem-box-perm-1342-at0214203143 c4) ▸
       at 1 2 (Bx2-4130 ∷ Bx4-1230 ∷ []) (lem-box-box-2-at0440 c4) ▸
       at 1 1 (Bx2-4013 ∷ []) (lem-box-perm-1423-at02142140 c4) ▸
       at 2 1 (Bx4-2031 ∷ []) (lem-box-perm-2431-at0440 c4) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 0 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b12 : Chain (CCZ024 ∷ X0 ∷ CZ24 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CCZ024 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ Toff213 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b12 = at 2 2 (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) (wl1432 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 7 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸ done

  b13 : Chain (CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CCZ024 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ Toff213 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ134 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b13 = at 5 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 3 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸ done

  b14 : Chain (Bx2-4013 ∷ X0 ∷ CCZ134 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CZ13 ∷ CCZ134 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b14 = at 2 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 2 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 3 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 3 2 (Toff413 ∷ CZ13 ∷ CCZ134 ∷ []) (wl1616 (lit c4)) ▸ done

  b15 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CZ13 ∷ CCZ134 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CZ13 ∷ CCZ134 ∷ Toff413 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b15 = at 5 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 8 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 7 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 5 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸ done

  b16 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CZ13 ∷ CCZ134 ∷ Toff413 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b16 = at 5 3 (Toff413 ∷ CCZ134 ∷ []) (wl1622 (lit c4)) ▸
       at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 3 (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp1419 c4) ▸
       at 6 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 5 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 6 4 (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp1420 c4) ▸
       at 8 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 9 2 (X0 ∷ CCZ134 ∷ []) (wp1421 c4) ▸ done

  b17 : Chain (Bx2-4013 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ Sb4-2-03-1 ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b17 = at 10 2 [] (wl0321 (lit c4)) ▸
       at 4 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 5 2 (Toff103 ∷ CCZ034 ∷ []) (wp1422 c4) ▸
       at 6 2 [] (wp0007 c4) ▸
       at 4 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 6 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 2 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 3 2 (CX13 ∷ Toff301 ∷ X0 ∷ []) (sym (wl1434 (lit c4))) ▸ done

  b18 : Chain (Bx2-4013 ∷ X0 ∷ Sb4-2-03-1 ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CCZ024 ∷ CX13 ∷ Toff401 ∷ Toff301 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b18 = at 2 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸
       at 6 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 6 (CX13 ∷ Toff301 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1623 (lit c4))) ▸
       at 2 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 5 2 (CX14 ∷ CX13 ∷ Toff413 ∷ []) (sym (wl1624 (lit c4))) ▸
       at 7 2 (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) (sym (wp1423 c4)) ▸
       at 4 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸ done

  b19 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CCZ024 ∷ CX13 ∷ Toff401 ∷ Toff301 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b19 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (Toff401 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp1424 c4) ▸
       at 10 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 10 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b20 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b20 = at 14 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 9 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 3 2 (CX14 ∷ Toff413 ∷ []) (sym (wl1626 (lit c4))) ▸
       at 5 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 4 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 5 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 6 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸ done

  b21 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ CX13 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ Toff413 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b21 = at 7 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 8 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 4 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 5 2 (CX14 ∷ CX13 ∷ Toff413 ∷ []) (sym (wl1624 (lit c4))) ▸
       at 7 2 (Toff401 ∷ Toff413 ∷ []) (sym (wp1425 c4)) ▸
       at 9 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 8 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 9 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸ done

  b22 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ CX13 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ Toff413 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX13 ∷ Toff301 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b22 = at 10 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 11 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 12 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 8 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 9 2 (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) (sym (wp1423 c4)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wp0728 c4)) ▸
       at 5 3 (CCZ012 ∷ []) (sym (wp1426 c4)) ▸
       at 3 4 (CX13 ∷ Toff301 ∷ []) (wl1627 (lit c4)) ▸ done

  b23 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX13 ∷ Toff301 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CX13 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b23 = at 2 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 3 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 4 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸ done

  b24 : Chain (Bx2-4013 ∷ X0 ∷ CX13 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ X0 ∷ Sb4-2-03-1 ∷ CS34 ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b24 = at 9 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 3 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 4 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 6 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 1 3 (Toff301 ∷ X0 ∷ []) (sym (wl1436 (lit c4))) ▸
       at 4 2 (CS34 ∷ X0 ∷ []) (sym (wl1437 (lit c4))) ▸ done

  b25 : Chain (Bx2-4013 ∷ Toff301 ∷ X0 ∷ Sb4-2-03-1 ∷ CS34 ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b25 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 7 2 (CS34 ∷ CS12⁻ ∷ []) (wl1628 (lit c4)) ▸
       at 6 2 (CS34 ∷ Toff103 ∷ []) (sym (wp1427 c4)) ▸
       at 5 2 (CS34 ∷ CS12 ∷ []) (wl1629 (lit c4)) ▸
       at 4 2 (CS34 ∷ Toff103 ∷ []) (sym (wp1427 c4)) ▸
       at 3 2 (CS34 ∷ Bx4-2031 ∷ []) (sym (lem-CSu-box-3-at04122041 c4)) ▸ done

  b26 : Chain (Bx2-4013 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ [])
  b26 = at 6 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 2 2 (CS34 ∷ X0 ∷ []) (sym (wl1437 (lit c4))) ▸
       at 5 2 (CX13 ∷ Toff301 ∷ X0 ∷ []) (sym (wl1434 (lit c4))) ▸
       at 4 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b27 = at 5 6 (CX13 ∷ Toff301 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1623 (lit c4))) ▸
       at 4 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 7 2 (CX14 ∷ CX13 ∷ Toff413 ∷ []) (sym (wl1624 (lit c4))) ▸
       at 9 2 (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) (sym (wp1423 c4)) ▸
       at 6 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (Toff401 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp1424 c4) ▸
       at 12 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸ done

  b28 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 12 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 11 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸ done

  b29 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CCZ012 ∷ Toff413 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b29 = at 5 2 (CX14 ∷ Toff413 ∷ []) (sym (wl1626 (lit c4))) ▸
       at 7 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 6 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 7 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 8 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 9 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 10 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸ done

  b30 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CCZ012 ∷ Toff413 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ CX13 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b30 = at 7 2 (CX14 ∷ CX13 ∷ Toff413 ∷ []) (sym (wl1624 (lit c4))) ▸
       at 9 2 (Toff401 ∷ Toff413 ∷ []) (sym (wp1425 c4)) ▸
       at 11 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 10 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 11 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 12 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 13 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 14 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸ done

  b31 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ CX13 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b31 = at 10 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 11 2 (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) (sym (wp1423 c4)) ▸
       at 5 3 (CCZ012 ∷ []) (sym (wp0728 c4)) ▸
       at 7 3 (CCZ012 ∷ []) (sym (wp1426 c4)) ▸
       at 5 4 (CX13 ∷ Toff301 ∷ []) (wl1627 (lit c4)) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b32 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ Toff301 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b32 = at 6 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 6 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸ done

  b33 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ Toff301 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS34⁻ ∷ X0 ∷ [])
  b33 = at 8 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 3 3 (Toff301 ∷ X0 ∷ []) (sym (wl1436 (lit c4))) ▸
       at 6 2 (CS34⁻ ∷ X0 ∷ []) (sym (wl1438 (lit c4))) ▸
       at 5 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS34⁻ ∷ X0 ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  b34 = at 9 2 (CS34⁻ ∷ CS12⁻ ∷ []) (wl1630 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ Toff103 ∷ []) (sym (wp1428 c4)) ▸
       at 7 2 (CS34⁻ ∷ CS12 ∷ []) (wl1631 (lit c4)) ▸
       at 6 2 (CS34⁻ ∷ Toff103 ∷ []) (sym (wp1428 c4)) ▸
       at 5 2 (CS34⁻ ∷ Bx4-2031 ∷ []) (sym (lem-CSdu-box-3-at04122041 c4)) ▸
       at 8 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb4-2-03-1 ∷ []) (refl) ▸ done

  b35 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ Sb4-2-03-1 ∷ X0 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  b35 = at 4 2 (CS34⁻ ∷ X0 ∷ []) (sym (wl1438 (lit c4))) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done

-- F4-K2-CS0 @0440: 11 steps
lem-F4-K2-CS0-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-CS0-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 4 (Bx2-4013 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-XCKX-box-2-at0214203143 c4) ▸
       at 1 4 (Toff301 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1634 (lit c4))) ▸
       at 2 4 (CS34 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wp1431 c4)) ▸
       at 3 4 (Toff301 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1634 (lit c4))) ▸
       at 4 4 (CS34⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wp1432 c4)) ▸ done

  b1 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b1 = at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done

-- SW-S @0410213243: 5 steps
lem-SW-S-at0410213243 : Ws → ⟪ (Sw23 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-SW-S-at0410213243 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ Sw23 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 2 2 (Sb2-4-01-3 ∷ CX23 ∷ []) (lem-CXuA-S-at0410213243 c4) ▸
       at 1 2 (Sb2-4-01-3 ∷ CX32 ∷ []) (lem-CXAu-S-at0410213243 c4) ▸
       at 0 2 (Sb2-4-01-3 ∷ CX23 ∷ []) (lem-CXuA-S-at0410213243 c4) ▸
       at 1 3 (Sw23 ∷ []) (wl0258 (lit c4)) ▸ done
