{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D146 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0155 ; wl0181 ; wl0191 ; wl0196 ; wl0242 ; wl0341 ; wl0491 ; wl0492 ; wl0808 ; wl0809 ; wl0965 ; wl0971 ; wl0976 ; wl0978 ; wl1265 ; wl1338 ; wl1384 ; wl1433 ; wl1498 ; wl1499 ; wl1505 ; wl1510 ; wl1511 ; wl1513 ; wl1545 ; wl1588 ; wl1621 ; wl1625 ; wl1628 ; wl1629 ; wl1630 ; wl1631 ; wl1718 ; wl1719 ; wl1720 ; wl1721 ; wl1722 ; wp0021 ; wp0032 ; wp0033 ; wp0037 ; wp0039 ; wp0081 ; wp0088 ; wp0089 ; wp0091 ; wp0092 ; wp0320 ; wp0789 ; wp1284 ; wp1285 ; wp1398 ; wp1425 ; wp1426 ; wp1467 ; wp1484 ; wp1485 ; wp1486 ; wp1487)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-CSdu-box-3-at0214203143 ; lem-CSdu-box-3-at04122041 ; lem-CSu-box-3-at0214203143 ; lem-CSu-box-3-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D033 using (lem-box-perm-1342-at0214203143 ; lem-box-perm-1423-at02142140)
open import Examples.Groups.Clifford+CS.Five.D.D036 using (lem-box-perm-1432-at04122041 ; lem-box-perm-1432-at04122140)
open import Examples.Groups.Clifford+CS.Five.D.D066 using (lem-box-box-1-at02142140)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX13-CCZ024 ; lem-comm-CZ13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CX13 ; lem-comm-CCZ024-CX31)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CSd02-TOFF413 ; lem-comm-TOFF213-CX40)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS02-TOFF413)

-- F4-CS0-CS2 @0440: 284 steps
lem-F4-CS0-CS2-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-CS2-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 4 2 (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) (wl1498 (lit c4)) ▸
       at 3 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 6 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 4 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b2 = at 5 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 6 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 5 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 5 2 (Bx4-2031 ∷ CS34⁻ ∷ []) (lem-CSdu-box-3-at04122041 c4) ▸
       at 5 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸ done

  b3 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b3 = at 4 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸ done

  b4 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff413 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b4 = at 5 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 5 2 (Toff413 ∷ Toff401 ∷ Toff301 ∷ []) (wp1484 c4) ▸
       at 7 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 12 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b5 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff413 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ Toff401 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b5 = at 8 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 7 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 8 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ Toff401 ∷ CCZ012 ∷ []) (sym (wp1485 c4)) ▸
       at 9 2 (Toff413 ∷ Toff401 ∷ Toff301 ∷ []) (wp1484 c4) ▸
       at 8 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 12 2 (Toff413 ∷ CS01 ∷ []) (wp1398 c4) ▸
       at 11 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸ done

  b6 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ Toff401 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Bx4-2031 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b6 = at 10 2 (Toff413 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF413 (lit c4)) ▸
       at 9 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF413 (lit c4)) ▸
       at 9 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 7 2 (Toff413 ∷ Toff401 ∷ []) (wp1425 c4) ▸
       at 8 3 (CCZ012 ∷ []) (sym (wp1426 c4)) ▸
       at 4 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸ done

  b7 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Bx4-2031 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ K3 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b7 = at 3 2 (Bx4-2031 ∷ CS34 ∷ []) (lem-CSu-box-3-at04122041 c4) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 2 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 8 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 7 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b8 : Chain (X0 ∷ Bx2-4013 ∷ K3 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff413 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b8 = at 3 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 2 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 3 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 3 2 (Toff413 ∷ Toff401 ∷ Toff301 ∷ []) (wp1484 c4) ▸
       at 5 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 10 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b9 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff413 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ Toff401 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b9 = at 8 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 6 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ Toff401 ∷ CCZ012 ∷ []) (sym (wp1485 c4)) ▸
       at 7 2 (Toff413 ∷ Toff401 ∷ Toff301 ∷ []) (wp1484 c4) ▸
       at 6 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸ done

  b10 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ Toff401 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b10 = at 10 2 (Toff413 ∷ CS01 ∷ []) (wp1398 c4) ▸
       at 9 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF413 (lit c4)) ▸
       at 7 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸
       at 6 2 (Toff413 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF413 (lit c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 5 2 (Toff413 ∷ Toff401 ∷ []) (wp1425 c4) ▸
       at 6 3 (CCZ012 ∷ []) (sym (wp1426 c4)) ▸ done

  b11 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CCZ024 ∷ X0 ∷ CZ24 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Bx2-4013 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b11 = at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 1 1 (Bx2-4130 ∷ []) (lem-box-perm-1342-at0214203143 c4) ▸
       at 2 1 (Bx4-2130 ∷ []) (lem-box-perm-1432-at04122041 c4) ▸
       at 1 2 (Bx4-2130 ∷ Bx2-4130 ∷ []) (lem-box-box-1-at02142140 c4) ▸
       at 1 1 (Bx4-2031 ∷ []) (lem-box-perm-1432-at04122140 c4) ▸
       at 2 1 (Bx2-4013 ∷ []) (lem-box-perm-1423-at02142140 c4) ▸
       at 1 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 0 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b12 : Chain (CCZ024 ∷ X0 ∷ CZ24 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Bx2-4013 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CCZ024 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff413 ∷ Bx2-4013 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b12 = at 2 2 (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) (wl1498 (lit c4)) ▸
       at 1 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸ done

  b13 : Chain (CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CCZ024 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff413 ∷ Bx2-4013 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b13 = at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 3 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 4 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 3 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸ done

  b14 : Chain (Bx4-2031 ∷ X0 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CZ13 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b14 = at 2 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) (wl0965 (lit c4)) ▸ done

  b15 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CZ13 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CZ13 ∷ CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b15 = at 5 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸ done

  b16 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CZ13 ∷ CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ Bx2-4013 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b16 = at 5 3 (Toff213 ∷ CCZ123 ∷ []) (wl0971 (lit c4)) ▸
       at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 3 (CCZ012 ∷ Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) (sym (wl1718 (lit c4))) ▸
       at 6 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 5 2 (CS34 ∷ CCZ123 ∷ []) (wl0492 (lit c4)) ▸
       at 6 4 (CCZ012 ∷ Toff301 ∷ CCZ123 ∷ []) (sym (wl1719 (lit c4))) ▸
       at 8 2 (CS34⁻ ∷ CCZ123 ∷ []) (wl0491 (lit c4)) ▸
       at 9 2 (X0 ∷ CCZ123 ∷ []) (wl1720 (lit c4)) ▸ done

  b17 : Chain (Bx4-2031 ∷ X0 ∷ Bx2-4013 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ Sb2-4-01-3 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b17 = at 10 2 [] (wl0181 (lit c4)) ▸
       at 3 2 (Toff301 ∷ CCZ012 ∷ []) (wl1265 (lit c4)) ▸
       at 4 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 5 2 [] (wl0341 (lit c4)) ▸
       at 4 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 6 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 2 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 3 2 (CX31 ∷ Toff103 ∷ X0 ∷ []) (sym (wl1505 (lit c4))) ▸ done

  b18 : Chain (Bx4-2031 ∷ X0 ∷ Sb2-4-01-3 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CCZ024 ∷ CX32 ∷ Toff103 ∷ Toff203 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b18 = at 2 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (CS34 ∷ []) (refl) ▸
       at 6 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 6 (CX31 ∷ Toff103 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1486 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 5 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (sym (wl0976 (lit c4))) ▸
       at 7 2 (Toff103 ∷ Toff203 ∷ Toff213 ∷ []) (sym (wl1721 (lit c4))) ▸
       at 4 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸ done

  b19 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CCZ024 ∷ CX32 ∷ Toff103 ∷ Toff203 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K1⁻ ∷ Toff203 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b19 = at 5 2 (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0789 c4) ▸
       at 8 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 7 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 8 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸ done

  b20 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K1⁻ ∷ Toff203 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS03 ∷ CX40 ∷ Toff213 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff103 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b20 = at 13 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 7 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 8 2 (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1467 c4) ▸
       at 3 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (sym (wl0976 (lit c4))) ▸
       at 5 2 (CX32 ∷ Toff213 ∷ []) (sym (wl0809 (lit c4))) ▸
       at 7 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 6 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 7 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸ done

  b21 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS03 ∷ CX40 ∷ Toff213 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff103 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff103 ∷ Toff203 ∷ Toff203 ∷ CS03 ∷ Toff213 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b21 = at 8 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 9 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 10 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 6 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 7 2 (Toff103 ∷ Toff203 ∷ Toff213 ∷ []) (sym (wl1721 (lit c4))) ▸
       at 9 2 (Toff203 ∷ Toff213 ∷ []) (sym (wl1338 (lit c4))) ▸
       at 11 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 10 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸ done

  b22 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff103 ∷ Toff203 ∷ Toff203 ∷ CS03 ∷ Toff213 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ Toff103 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b22 = at 11 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 13 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 14 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 10 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 3 3 (CX31 ∷ []) (wl0978 (lit c4)) ▸
       at 5 3 (Toff103 ∷ []) (wl1621 (lit c4)) ▸
       at 3 4 (CX31 ∷ Toff103 ∷ []) (wp1487 c4) ▸ done

  b23 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ Toff103 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CX31 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b23 = at 2 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 4 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 3 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 4 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸ done

  b24 : Chain (Bx4-2031 ∷ X0 ∷ CX31 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ X0 ∷ Sb2-4-01-3 ∷ CS12 ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b24 = at 9 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 3 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 4 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 1 3 (Toff103 ∷ X0 ∷ []) (sym (wl1510 (lit c4))) ▸
       at 4 2 (CS12 ∷ X0 ∷ []) (sym (wl1511 (lit c4))) ▸ done

  b25 : Chain (Bx4-2031 ∷ Toff103 ∷ X0 ∷ Sb2-4-01-3 ∷ CS12 ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b25 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 7 2 (CS12 ∷ CS34⁻ ∷ []) (sym (wl1631 (lit c4))) ▸
       at 6 2 (CS12 ∷ Toff301 ∷ []) (sym (wl1384 (lit c4))) ▸
       at 5 2 (CS12 ∷ CS34 ∷ []) (sym (wl1629 (lit c4))) ▸
       at 4 2 (CS12 ∷ Toff301 ∷ []) (sym (wl1384 (lit c4))) ▸
       at 3 2 (CS12 ∷ Bx2-4013 ∷ []) (sym (lem-CSu-box-3-at0214203143 c4)) ▸ done

  b26 : Chain (Bx4-2031 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ [])
  b26 = at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X0 ∷ []) (sym (wl1511 (lit c4))) ▸
       at 5 2 (CX31 ∷ Toff103 ∷ X0 ∷ []) (sym (wl1505 (lit c4))) ▸
       at 4 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 6 1 (CS34 ∷ []) (refl) ▸
       at 8 1 (CS34⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff203 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b27 = at 5 6 (CX31 ∷ Toff103 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1486 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 7 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (sym (wl0976 (lit c4))) ▸
       at 9 2 (Toff103 ∷ Toff203 ∷ Toff213 ∷ []) (sym (wl1721 (lit c4))) ▸
       at 6 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 7 2 (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0789 c4) ▸
       at 10 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 9 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b28 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff203 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ Toff103 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b28 = at 10 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 15 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 9 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 10 2 (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1467 c4) ▸ done

  b29 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ Toff103 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff213 ∷ Toff103 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b29 = at 5 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (sym (wl0976 (lit c4))) ▸
       at 7 2 (CX32 ∷ Toff213 ∷ []) (sym (wl0809 (lit c4))) ▸
       at 9 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 8 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 9 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 10 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 11 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 12 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸ done

  b30 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff213 ∷ Toff103 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff103 ∷ Toff203 ∷ Toff203 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ Toff213 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b30 = at 8 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 9 2 (Toff103 ∷ Toff203 ∷ Toff213 ∷ []) (sym (wl1721 (lit c4))) ▸
       at 11 2 (Toff203 ∷ Toff213 ∷ []) (sym (wl1338 (lit c4))) ▸
       at 13 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 12 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 13 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 15 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸ done

  b31 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff103 ∷ Toff203 ∷ Toff203 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ Toff213 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b31 = at 16 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 12 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 5 3 (CX31 ∷ []) (wl0978 (lit c4)) ▸
       at 7 3 (Toff103 ∷ []) (wl1621 (lit c4)) ▸
       at 5 4 (CX31 ∷ Toff103 ∷ []) (wp1487 c4) ▸
       at 4 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 6 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b32 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CX31 ∷ Toff103 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b32 = at 6 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 6 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸ done

  b33 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CX31 ∷ Toff103 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS12⁻ ∷ X0 ∷ [])
  b33 = at 8 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 3 3 (Toff103 ∷ X0 ∷ []) (sym (wl1510 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ X0 ∷ []) (sym (wl1513 (lit c4))) ▸
       at 5 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 7 1 (CS34 ∷ []) (refl) ▸
       at 9 1 (CS34⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS12⁻ ∷ X0 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b34 = at 9 2 (CS12⁻ ∷ CS34⁻ ∷ []) (sym (wl1630 (lit c4))) ▸
       at 8 2 (CS12⁻ ∷ Toff301 ∷ []) (sym (wl1722 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CS34 ∷ []) (sym (wl1628 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ Toff301 ∷ []) (sym (wl1722 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ Bx2-4013 ∷ []) (sym (lem-CSdu-box-3-at0214203143 c4)) ▸
       at 8 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done

  b35 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ Sb2-4-01-3 ∷ X0 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b35 = at 4 2 (CS12⁻ ∷ X0 ∷ []) (sym (wl1513 (lit c4))) ▸
       at 2 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb4-2-03-1 ∷ []) (refl) ▸ done
