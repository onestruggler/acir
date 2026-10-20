{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D036 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl1441 ; wl1442 ; wl1443 ; wl1723 ; wp1294 ; wl1574 ; wl1576 ; wl1577 ; wl1739 ; wp1519)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym-ab-at022330 ; lem-sym-ab-at03122130 ; lem-sym-ab-at0314213240 ; lem-sym-ab-at03243240 ; lem-sym-ab-at0330)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym-ab-at02132130 ; lem-sym-ab-at02142140 ; lem-sym-ab-at022440 ; lem-sym-ab-at0410233241 ; lem-sym-ab-at04122041 ; lem-sym-ab-at04122140 ; lem-sym-ab-at04133140 ; lem-sym-ab-at04233240)
open import Examples.Groups.Clifford+CS.Five.D.D013 using (lem-CSdu-box-2-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-box-cP-at0214233041)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0214213043 ; lem-sym-bc-at02132031 ; lem-sym-bc-at02132130 ; lem-sym-bc-at03122031 ; lem-sym-bc-at03122130)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-sym-bc-at041041 ; lem-sym-bc-at0413213240 ; lem-sym-bc-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-pairs-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-Kdu-box-at0214203143 ; lem-Ku-box-at0214203143 ; lem-box-perm-1423-at0214203143 ; lem-pairs-at0413213240)
open import Examples.Groups.Clifford+CS.Five.D.D024 using (lem-box-perm-1324-at0214203143 ; lem-pairs-at02132031 ; lem-pairs-at022440 ; lem-pairs-at03122031 ; lem-pairs-at0412233140 ; lem-pairs-at0413203241)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ124-CK03)

-- F4-CS0-K1 @0440: 21 steps
lem-F4-CS0-K1-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-K1-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
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

-- box-perm-1432 @04122041: 4 steps
lem-box-perm-1432-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-box-perm-1432-at04122041 c4 = run b0
  where
  b0 : Chain (Bx4-2031 ∷ []) (Bx4-2130 ∷ [])
  b0 = at 0 1 (Bx4-0231 ∷ []) (lem-sym-ab-at04122041 c4) ▸
       at 0 1 (Bx4-0321 ∷ []) (lem-sym-bc-at041041 c4) ▸
       at 0 1 (Bx4-3021 ∷ []) (lem-sym-ab-at0410233241 c4) ▸
       at 0 1 (Bx4-2130 ∷ []) (lem-pairs-at0413203241 c4) ▸ done

-- box-perm-2341 @02142140: 4 steps
lem-box-perm-2341-at02142140 : Ws → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-box-perm-2341-at02142140 c4 = run b0
  where
  b0 : Chain (Bx2-4130 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 0 1 (Bx2-1430 ∷ []) (lem-sym-ab-at02142140 c4) ▸
       at 0 1 (Bx2-3014 ∷ []) (lem-pairs-at022440 c4) ▸
       at 0 1 (Bx2-3104 ∷ []) (lem-sym-bc-at02132031 c4) ▸
       at 0 1 (Bx2-1304 ∷ []) (lem-sym-ab-at02132130 c4) ▸ done

-- box-perm-4123 @022330: 4 steps
lem-box-perm-4123-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ []) ⟫ʷ
lem-box-perm-4123-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Bx2-4130 ∷ [])
  b0 = at 0 1 (Bx2-3104 ∷ []) (lem-sym-ab-at022330 c4) ▸
       at 0 1 (Bx2-3014 ∷ []) (lem-sym-bc-at02132130 c4) ▸
       at 0 1 (Bx2-1430 ∷ []) (lem-pairs-at02132031 c4) ▸
       at 0 1 (Bx2-4130 ∷ []) (lem-sym-ab-at022440 c4) ▸ done

-- box-perm-1432 @04122140: 4 steps
lem-box-perm-1432-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-box-perm-1432-at04122140 c4 = run b0
  where
  b0 : Chain (Bx4-2130 ∷ []) (Bx4-2031 ∷ [])
  b0 = at 0 1 (Bx4-1230 ∷ []) (lem-sym-ab-at04122140 c4) ▸
       at 0 1 (Bx4-1320 ∷ []) (lem-sym-bc-at0440 c4) ▸
       at 0 1 (Bx4-3120 ∷ []) (lem-sym-ab-at04233240 c4) ▸
       at 0 1 (Bx4-2031 ∷ []) (lem-pairs-at0413213240 c4) ▸ done

-- CKu-box-2 @0214203143: 7 steps
lem-CKu-box-2-at0214203143 : Ws → ⟪ (CK02 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CK02 ∷ []) ⟫ʷ
lem-CKu-box-2-at0214203143 c4 = run b0
  where
  b0 : Chain (CK02 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CK02 ∷ [])
  b0 = at 0 1 (CS02⁻ ∷ K2⁻ ∷ CS02⁻ ∷ K2 ∷ CS02⁻ ∷ []) (wl1723 (lit c4)) ▸
       at 4 2 (Bx2-4013 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2-at0214203143 c4) ▸
       at 3 2 (Bx2-4013 ∷ K2 ∷ []) (lem-Ku-box-at0214203143 c4) ▸
       at 2 2 (Bx2-4013 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2-at0214203143 c4) ▸
       at 1 2 (Bx2-4013 ∷ K2⁻ ∷ []) (lem-Kdu-box-at0214203143 c4) ▸
       at 0 2 (Bx2-4013 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2-at0214203143 c4) ▸
       at 1 5 (CK02 ∷ []) (sym (wl1723 (lit c4))) ▸ done

-- box-perm-2341 @0314213240: 4 steps
lem-box-perm-2341-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-2341-at0314213240 c4 = run b0
  where
  b0 : Chain (Bx3-4120 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Bx3-1420 ∷ []) (lem-sym-ab-at0314213240 c4) ▸
       at 0 1 (Bx3-2014 ∷ []) (lem-pairs-at03243240 c4) ▸
       at 0 1 (Bx3-2104 ∷ []) (lem-sym-bc-at03122031 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-sym-ab-at03122130 c4) ▸ done

-- box-perm-4123 @0330: 4 steps
lem-box-perm-4123-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-box-perm-4123-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 1 (Bx3-2104 ∷ []) (lem-sym-ab-at0330 c4) ▸
       at 0 1 (Bx3-2014 ∷ []) (lem-sym-bc-at03122130 c4) ▸
       at 0 1 (Bx3-1420 ∷ []) (lem-pairs-at03122031 c4) ▸
       at 0 1 (Bx3-4120 ∷ []) (lem-sym-ab-at03243240 c4) ▸ done

-- box-perm-2431 @0413213240: 3 steps
lem-box-perm-2431-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-box-perm-2431-at0413213240 c4 = run b0
  where
  b0 : Chain (Bx4-3120 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 0 1 (Bx4-3210 ∷ []) (lem-sym-bc-at0413213240 c4) ▸
       at 0 1 (Bx4-2310 ∷ []) (lem-sym-ab-at04133140 c4) ▸
       at 0 1 (Bx4-1023 ∷ []) (lem-pairs-at0412233140 c4) ▸ done

-- F4-CS0-K3 @0440: 21 steps
lem-F4-CS0-K3-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-K3-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK03 ∷ []) (X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ K3 ∷ CK03 ∷ S0 ∷ Toff203 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (K3 ∷ CK03 ∷ S0 ∷ X0 ∷ []) (sym (wl1574 (lit c4))) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK03 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1519 c4)) ▸
       at 1 1 (Bx2-4103 ∷ []) (lem-box-perm-1324-at0214203143 c4) ▸
       at 1 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at0214213043 c4) ▸
       at 4 4 (K3 ∷ CK03 ∷ S0 ∷ Toff203 ∷ []) (sym (wl1739 (lit c4))) ▸ done

  b1 : Chain (X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ K3 ∷ CK03 ∷ S0 ∷ Toff203 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ Bx2-4103 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ124 ∷ []) (wl1576 (lit c4)) ▸
       at 4 2 (CK03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CK03 (lit c4)) ▸
       at 5 2 (S0 ∷ CCZ124 ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))) ▸
       at 2 4 (K3 ∷ CK03 ∷ S0 ∷ Toff203 ∷ []) (sym (wl1739 (lit c4))) ▸
       at 1 2 (K3 ∷ CCZ124 ∷ []) (wl1576 (lit c4)) ▸
       at 2 2 (CK03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CK03 (lit c4)) ▸
       at 3 2 (S0 ∷ CCZ124 ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))) ▸
       at 4 4 (Bx2-4103 ∷ []) (sym (lem-box-cP-at0214213043 c4)) ▸ done

  b2 : Chain (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ Bx2-4103 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (CK03 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b2 = at 4 1 (Bx2-4013 ∷ []) (sym (lem-box-perm-1324-at0214203143 c4)) ▸
       at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 0 4 (CK03 ∷ X0 ∷ []) (sym (wl1577 (lit c4))) ▸ done
