{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D446 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00007 ; wn00020 ; wn00021 ; wn00027 ; wn00029 ; wn00031 ; wn00049 ; wn00051 ; wn00076 ; wn00137 ; wn00139 ; wn00140 ; wn00142 ; wn00157 ; wn00158)
open import Examples.Groups.Clifford+CS.Four.Wins.W03 using (wn00416 ; wn00445 ; wn00457)
open import Examples.Groups.Clifford+CS.Four.Wins.W04 using (wn00523)
open import Examples.Groups.Clifford+CS.Four.Wins.W06 using (wn00588 ; wn00593 ; wn00607 ; wn00609 ; wn00626)
open import Examples.Groups.Clifford+CS.Four.Wins.W15 using (wn00915 ; wn00917)
open import Examples.Groups.Clifford+CS.Four.Wins.W22 using (wn01140 ; wn01142)
open import Examples.Groups.Clifford+CS.Four.Wins.W23 using (wn01170 ; wn01189 ; wn01190 ; wn01191 ; wn01192 ; wn01193)

-- groups [CKd30] [CS13 CS23 CX12 CSd23 CX12]: 59 steps
lem-groups-CKd30-vs-CS13-CS23-CX12-CSd23-CX12 : ⟪ (CK30⁻ ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-groups-CKd30-vs-CS13-CS23-CX12-CSd23-CX12 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CK30⁻ ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (CS12 ∷ CK20⁻ ∷ []) wn01189 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸ done

  b2 : Chain (CS13 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ [])
  b2 = at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23 ∷ CK31⁻ ∷ []) wn01190 ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b3 : Chain (CS13 ∷ CS23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ [])
  b3 = at 2 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00031 ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX23 ∷ Sw12 ∷ []) wn00157 ▸
       at 4 2 (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁)) ▸
       at 3 2 (CX13 ∷ Sw12 ∷ []) wn00158 ▸ done

  b4 : Chain (CS13 ∷ CS23 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ Sw23 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ [])
  b4 = at 3 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 5 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 3 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸ done

  b5 : Chain (CS13 ∷ CS23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ Sw23 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX12 ∷ [])
  b5 = at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ CK31⁻ ∷ []) wn01191 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b6 : Chain (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b6 = at 4 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX23 ∷ Sw12 ∷ []) wn00157 ▸
       at 6 2 (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁)) ▸
       at 5 2 (CX13 ∷ Sw12 ∷ []) wn00158 ▸ done

  b7 : Chain (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CK30⁻ ∷ [])
  b7 = at 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 5 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸ done

-- groups [CKd30] [CSd23]: 15 steps
lem-groups-CKd30-vs-CSd23 : ⟪ (CK30⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CK30⁻ ∷ []) ⟫ʷ
lem-groups-CKd30-vs-CSd23 = trans (run b0) (run b1)
  where
  b0 : Chain (CK30⁻ ∷ CS23⁻ ∷ []) (Sw01 ∷ CS23⁻ ∷ CK31⁻ ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ CK31⁻ ∷ []) wn01191 ▸ done

  b1 : Chain (Sw01 ∷ CS23⁻ ∷ CK31⁻ ∷ Sw01 ∷ []) (CS23⁻ ∷ CK30⁻ ∷ [])
  b1 = at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 2 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

-- groups [CK10 CS02 CK20 CSd02 CKd10 CS02 CKd20 CSd02] [CS12 CS13 CX23 CSd13 CX23]: 305 steps
lem-groups-CK10-CS02-CK20-CSd02-CKd10-CS02-CKd20-CSd02-vs-CS12-CS13-CX23-CSd13-CX23 : ⟪ (CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-groups-CK10-CS02-CK20-CSd02-CKd10-CS02-CKd20-CSd02-vs-CS12-CS13-CX23-CSd13-CX23 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (run b38))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b0 = at 0 9 (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) wn01192 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸ done

  b1 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS13 ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b1 = at 11 2 (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS)) ▸
       at 10 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 10 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS13 ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS23 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b2 = at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 10 2 (CS23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CS)) ▸ done

  b3 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS23 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b3 = at 9 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 5 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b4 = at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 9 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 8 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸ done

  b5 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b5 = at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b6 = at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 6 2 (CS12 ∷ CK10⁻ ∷ []) wn01140 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 7 2 [] wn00003 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b7 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 7 2 (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS)) ▸
       at 6 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸ done

  b8 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b8 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b9 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b9 = at 4 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 6 2 (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS)) ▸
       at 5 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ Sw23 ∷ CS03 ∷ CS12 ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b10 = at 4 2 [] wn00003 ▸
       at 5 5 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (CS12 ∷ CK10 ∷ Sw23 ∷ CS03 ∷ CS12 ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b11 = at 3 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 5 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 4 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸ done

  b12 : Chain (CS12 ∷ CK10 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ Sw23 ∷ CK10 ∷ CS12 ∷ Sw23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b12 = at 4 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸ done

  b13 : Chain (CS12 ∷ Sw23 ∷ CK10 ∷ CS12 ∷ Sw23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw01 ∷ CS12⁻ ∷ CX23 ∷ Sw01 ∷ CS13⁻ ∷ CX23 ∷ [])
  b13 = at 2 2 (CS12 ∷ CK10 ∷ []) wn00607 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 3 2 [] wn00003 ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 10 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 9 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸ done

  b14 : Chain (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw01 ∷ CS12⁻ ∷ CX23 ∷ Sw01 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw01 ∷ CX23 ∷ CK21⁻ ∷ Sw01 ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ [])
  b14 = at 10 2 (CX23 ∷ CS12⁻ ∷ []) wn01170 ▸
       at 9 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 10 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 11 2 [] wn00031 ▸
       at 10 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 9 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 8 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸
       at 9 2 (CX23 ∷ CK21⁻ ∷ []) wn01193 ▸ done

  b15 : Chain (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw01 ∷ CX23 ∷ CK21⁻ ∷ Sw01 ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CX23 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ [])
  b15 = at 8 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 9 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 10 2 [] wn00031 ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (CX23 ∷ CS12 ∷ []) wn00915 ▸
       at 7 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸ done

  b16 : Chain (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CX23 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CX23 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ [])
  b16 = at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 9 2 [] wn00031 ▸
       at 6 2 (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁)) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 5 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 6 2 (CX23 ∷ CS12⁻ ∷ []) wn01170 ▸
       at 5 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸ done

  b17 : Chain (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CX23 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CX23 ∷ CK20 ∷ Sw01 ∷ Sw01 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ [])
  b17 = at 6 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 7 2 [] wn00031 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 4 2 (Sw01 ∷ CK21 ∷ []) wn00140 ▸
       at 5 2 (CX23 ∷ CK21 ∷ []) wn00917 ▸
       at 4 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 5 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸ done

  b18 : Chain (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CX23 ∷ CK20 ∷ Sw01 ∷ Sw01 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CK10 ∷ CX23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ [])
  b18 = at 6 2 [] wn00031 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 3 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 4 2 (CX23 ∷ CS12 ∷ []) wn00915 ▸
       at 3 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 5 2 [] wn00031 ▸ done

  b19 : Chain (CS12 ∷ CS13 ∷ CK10 ∷ CX23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ [])
  b19 = at 2 2 (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁)) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 15 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸ done

  b20 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS13⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b20 = at 13 2 (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS))) ▸
       at 12 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 12 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS13⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CX23 ∷ [])
  b21 = at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 12 2 (CS23⁻ ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) ((CS • CS • CS))) ▸ done

  b22 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b22 = at 11 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 11 5 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b23 = at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 11 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 10 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸ done

  b24 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b24 = at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 10 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b25 = at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 8 2 (CS12⁻ ∷ CK10⁻ ∷ []) wn01142 ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 9 2 [] wn00003 ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b26 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b26 = at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 9 2 (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS))) ▸
       at 8 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸ done

  b27 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b27 = at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b28 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b28 = at 6 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 8 2 (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS))) ▸
       at 7 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b29 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ Sw23 ∷ CS03 ∷ CS12⁻ ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b29 = at 6 2 [] wn00003 ▸
       at 7 5 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ Sw23 ∷ CS03 ∷ CS12⁻ ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b30 = at 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 7 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 6 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸ done

  b31 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ Sw23 ∷ CK10 ∷ CS12⁻ ∷ Sw23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b31 = at 6 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸ done

  b32 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ Sw23 ∷ CK10 ∷ CS12⁻ ∷ Sw23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw01 ∷ CS12⁻ ∷ CX23 ∷ Sw01 ∷ [])
  b32 = at 4 2 (CS12⁻ ∷ CK10 ∷ []) wn00609 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 5 2 [] wn00003 ▸
       at 13 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 12 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 11 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸ done

  b33 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw01 ∷ CS12⁻ ∷ CX23 ∷ Sw01 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw01 ∷ CX23 ∷ CK21⁻ ∷ Sw01 ∷ CS02⁻ ∷ [])
  b33 = at 12 2 (CX23 ∷ CS12⁻ ∷ []) wn01170 ▸
       at 11 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 12 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 13 2 [] wn00031 ▸
       at 12 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 11 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 10 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸
       at 11 2 (CX23 ∷ CK21⁻ ∷ []) wn01193 ▸ done

  b34 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw01 ∷ CX23 ∷ CK21⁻ ∷ Sw01 ∷ CS02⁻ ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CX23 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CK20⁻ ∷ CS02⁻ ∷ [])
  b34 = at 10 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 11 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 12 2 [] wn00031 ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 10 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 10 2 (CX23 ∷ CS12 ∷ []) wn00915 ▸
       at 9 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸ done

  b35 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CX23 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CX23 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ [])
  b35 = at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 [] wn00031 ▸
       at 8 2 (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁)) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 7 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 8 2 (CX23 ∷ CS12⁻ ∷ []) wn01170 ▸
       at 7 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸ done

  b36 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CX23 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CX23 ∷ CK20 ∷ Sw01 ∷ Sw01 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ [])
  b36 = at 8 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 9 2 [] wn00031 ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 6 2 (Sw01 ∷ CK21 ∷ []) wn00140 ▸
       at 7 2 (CX23 ∷ CK21 ∷ []) wn00917 ▸
       at 6 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 7 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸ done

  b37 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CX23 ∷ CK20 ∷ Sw01 ∷ Sw01 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CX23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ [])
  b37 = at 8 2 [] wn00031 ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 6 2 (CX23 ∷ CS12 ∷ []) wn00915 ▸
       at 5 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 [] wn00031 ▸ done

  b38 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CX23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ [])
  b38 = at 4 2 (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁)) ▸ done

-- groups [CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S1 S1 S1 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01] [CSd23]: 116 steps
lem-groups-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-vs-CSd23 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-groups-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-vs-CSd23 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS23⁻ ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS23⁻ ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b0 = at 55 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 54 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 53 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 52 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 51 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 50 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 49 2 (CS23⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((CS • CS • CS))) ▸
       at 48 2 (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS))) ▸ done

  b1 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS23⁻ ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS23⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b1 = at 47 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 46 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 45 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 44 2 (CS23⁻ ∷ CX21 ∷ []) wn00457 ▸
       at 43 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 42 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 41 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 40 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸ done

  b2 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS23⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ CS23⁻ ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b2 = at 39 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 38 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 37 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 36 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 35 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 34 2 (CS23⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((CS • CS • CS))) ▸
       at 33 2 (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS))) ▸
       at 32 2 (CS23⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((CS • CS • CS))) ▸ done

  b3 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ CS23⁻ ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS23⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b3 = at 31 2 (CS23⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((CS • CS • CS))) ▸
       at 30 2 (CS23⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((CS • CS • CS))) ▸
       at 29 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 28 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 27 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 26 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 25 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 24 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸ done

  b4 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS23⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS23⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b4 = at 23 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 22 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 21 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 20 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 19 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 18 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 17 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 16 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸ done

  b5 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS23⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS23⁻ ∷ Sw01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b5 = at 15 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 14 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 13 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 12 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 11 2 (CS23⁻ ∷ CX21 ∷ []) wn00457 ▸
       at 12 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 11 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b6 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS23⁻ ∷ Sw01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CS23⁻ ∷ CS12 ∷ Sw01 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b6 = at 11 2 (CS23⁻ ∷ CS12 ∷ []) wn00416 ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 12 2 [] wn00031 ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 10 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 10 2 (CS23⁻ ∷ CS12 ∷ []) wn00416 ▸ done

  b7 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CS23⁻ ∷ CS12 ∷ Sw01 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS23⁻ ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b7 = at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 [] wn00031 ▸
       at 10 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 9 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 8 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 9 2 (CS23⁻ ∷ CS12 ∷ []) wn00416 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b8 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS23⁻ ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS23⁻ ∷ CS02 ∷ Sw01 ∷ Sw01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b8 = at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 [] wn00031 ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (CS23⁻ ∷ CS12 ∷ []) wn00416 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b9 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS23⁻ ∷ CS02 ∷ Sw01 ∷ Sw01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS23⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b9 = at 9 2 [] wn00031 ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 6 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 7 2 (CS23⁻ ∷ CS12 ∷ []) wn00416 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 [] wn00031 ▸ done

  b10 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS23⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS23⁻ ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b10 = at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 6 2 (CS23⁻ ∷ CS12 ∷ []) wn00416 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 [] wn00031 ▸
       at 4 2 (CS23⁻ ∷ S2 ∷ []) wn00445 ▸ done

  b11 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS23⁻ ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CS23⁻ ∷ Sw01 ∷ Sw01 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b11 = at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 3 2 (Sw01 ∷ CK21 ∷ []) wn00140 ▸
       at 4 2 (CS23⁻ ∷ CK21 ∷ []) wn00626 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸
       at 5 2 [] wn00031 ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b12 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CS23⁻ ∷ Sw01 ∷ Sw01 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b12 = at 3 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 2 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 3 2 (CS23⁻ ∷ CS12 ∷ []) wn00416 ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 4 2 [] wn00031 ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸ done

  b13 : Chain (CS02 ∷ CS02 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (Sw01 ∷ CS12 ∷ CS23⁻ ∷ Sw01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b13 = at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 2 2 (CS23⁻ ∷ CS12 ∷ []) wn00416 ▸
       at 1 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 [] wn00031 ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 0 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b14 : Chain (Sw01 ∷ CS12 ∷ CS23⁻ ∷ Sw01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS23⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  b14 = at 1 2 (CS23⁻ ∷ CS12 ∷ []) wn00416 ▸
       at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 2 [] wn00031 ▸ done

-- groups [CK30] [CS13 CS23 CX12 CSd23 CX12]: 59 steps
lem-groups-CK30-vs-CS13-CS23-CX12-CSd23-CX12 : ⟪ (CK30 ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CK30 ∷ []) ⟫ʷ
lem-groups-CK30-vs-CS13-CS23-CX12-CSd23-CX12 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CK30 ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (CS12 ∷ CK20 ∷ []) wn00523 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ Sw23 ∷ Sw01 ∷ CK21 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CK21 ∷ []) wn00140 ▸ done

  b2 : Chain (CS13 ∷ Sw23 ∷ Sw01 ∷ CK21 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ [])
  b2 = at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23 ∷ CK31 ∷ []) wn00588 ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b3 : Chain (CS13 ∷ CS23 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ [])
  b3 = at 2 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00031 ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX23 ∷ Sw12 ∷ []) wn00157 ▸
       at 4 2 (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁)) ▸
       at 3 2 (CX13 ∷ Sw12 ∷ []) wn00158 ▸ done

  b4 : Chain (CS13 ∷ CS23 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CK21 ∷ Sw23 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ [])
  b4 = at 3 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 5 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CK21 ∷ []) wn00140 ▸ done

  b5 : Chain (CS13 ∷ CS23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CK21 ∷ Sw23 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX12 ∷ [])
  b5 = at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ CK31 ∷ []) wn00593 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b6 : Chain (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ [])
  b6 = at 4 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX23 ∷ Sw12 ∷ []) wn00157 ▸
       at 6 2 (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁)) ▸
       at 5 2 (CX13 ∷ Sw12 ∷ []) wn00158 ▸ done

  b7 : Chain (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CK30 ∷ [])
  b7 = at 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 5 (CK30 ∷ []) (by-assoc Eq.refl) ▸ done

-- groups [CK30] [CSd23]: 15 steps
lem-groups-CK30-vs-CSd23 : ⟪ (CK30 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CK30 ∷ []) ⟫ʷ
lem-groups-CK30-vs-CSd23 = trans (run b0) (run b1)
  where
  b0 : Chain (CK30 ∷ CS23⁻ ∷ []) (Sw01 ∷ CS23⁻ ∷ CK31 ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CK21 ∷ []) wn00140 ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ CK31 ∷ []) wn00593 ▸ done

  b1 : Chain (Sw01 ∷ CS23⁻ ∷ CK31 ∷ Sw01 ∷ []) (CS23⁻ ∷ CK30 ∷ [])
  b1 = at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 2 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done
