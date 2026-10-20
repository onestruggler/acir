{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D003 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0344 ; wl0433 ; wl0477 ; wl1303 ; wl1379 ; wp0130 ; wp0131 ; wp0262 ; wp0294 ; wp0363 ; wp0661 ; wp1068 ; wp1232 ; wl1341 ; wl0003 ; wl0011 ; wl0018 ; wl0549 ; wl0550 ; wl0563 ; wl0564 ; wp0403 ; wp0404 ; wp0440 ; wp0441 ; wp0469 ; wp0470 ; wp0471 ; wp0474 ; wl0551 ; wl0553 ; wl0575 ; wl0577 ; wl0579 ; wl0603 ; wl0605 ; wl0607 ; wl0576 ; wl0604 ; wp0410 ; wp0411 ; wp0412 ; wp0416 ; wp0494 ; wl0554 ; wl0565 ; wl0568 ; wl0655 ; wl0656 ; wl0657 ; wl0660 ; wl1440 ; wl1444 ; wl1445 ; wl1449 ; wl1450 ; wl1454 ; wp1293 ; wp1295 ; wp1296 ; wp1299 ; wp1300 ; wp1303 ; wl1271 ; wl1476 ; wp0212 ; wl1531 ; wl1532 ; wl1126 ; wl1556 ; wl1559 ; wl1560 ; wl1573 ; wl1578 ; wl1579 ; wl1580 ; wl1582 ; wl1584 ; wl1592 ; wl1593 ; wl1594 ; wl1595 ; wp0516 ; wp0594 ; wp0596 ; wp0733 ; wp0766 ; wp0767 ; wp0986 ; wp0987 ; wp0992 ; wp1048 ; wl1596 ; wl1613 ; wl1614 ; wp0211 ; wp0675 ; wp0676 ; wp0677 ; wp0678 ; wp0695 ; wp0696 ; wl0012 ; wl1659 ; wl1660 ; wp0719 ; wp0732 ; wp1436 ; wp1437 ; wl0756 ; wp1488 ; wp1503 ; wp1518)
open import Examples.Groups.Clifford+CS.Five.Chain

-- sym-ab @0310213442: 18 steps
lem-sym-ab-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-sym-ab-at0310213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-0142 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp1068 c4) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ CZ12 ∷ Toff134 ∷ CCZ134 ∷ CZ12 ∷ []) (sym (wl1379 (lit c4))) ▸
       at 4 1 (Bx3-12 ∷ []) (refl) ▸
       at 7 1 (Bx3-12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ [])
  b1 = at 2 6 (Bx1-342 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wp1068 c4) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ CZ12 ∷ Toff134 ∷ CCZ134 ∷ CZ12 ∷ []) (sym (wl1379 (lit c4))) ▸
       at 7 1 (Bx3-12 ∷ []) (refl) ▸
       at 10 1 (Bx3-12 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) (Bx3-1042 ∷ [])
  b2 = at 5 6 (Bx1-342 ∷ []) (refl) ▸
       at 0 6 (Bx3-1042 ∷ []) (refl) ▸ done

-- cQ @03203442: 7 steps
lem-cQ-at03203442 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at03203442 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (wl0477 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS03⁻ ∷ []) (sym (wp0363 c4)) ▸
       at 1 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0477 (lit c4))) ▸ done

-- sym-ab @03203442: 18 steps
lem-sym-ab-at03203442 : Ws → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym-ab-at03203442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-1042 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl1379 (lit c4)) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ []) (sym (wp1068 c4)) ▸
       at 4 1 (Bx3-02 ∷ []) (refl) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ []) (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ [])
  b1 = at 2 6 (Bx0-342 ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wl1379 (lit c4)) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ []) (sym (wp1068 c4)) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸
       at 10 1 (Bx3-02 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (Bx3-0142 ∷ [])
  b2 = at 5 6 (Bx0-342 ∷ []) (refl) ▸
       at 0 6 (Bx3-0142 ∷ []) (refl) ▸ done

-- sym-ab @02132130: 18 steps
lem-sym-ab-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym-ab-at02132130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-3104 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (sym (wp0130 c4)) ▸
       at 4 1 (Bx2-14 ∷ []) (refl) ▸
       at 7 1 (Bx2-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ [])
  b1 = at 2 6 (Bx1-204 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (sym (wp0130 c4)) ▸
       at 7 1 (Bx2-14 ∷ []) (refl) ▸
       at 10 1 (Bx2-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (Bx2-1304 ∷ [])
  b2 = at 5 6 (Bx1-204 ∷ []) (refl) ▸
       at 0 6 (Bx2-1304 ∷ []) (refl) ▸ done

-- sym-ab @031031: 18 steps
lem-sym-ab-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-sym-ab-at031031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-0214 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 2 1 (CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ []) (sym (wl1303 (lit c4))) ▸
       at 4 1 (Bx3-24 ∷ []) (refl) ▸
       at 7 1 (Bx3-24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ [])
  b1 = at 2 6 (Bx2-314 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 5 1 (CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ []) (sym (wl1303 (lit c4))) ▸
       at 7 1 (Bx3-24 ∷ []) (refl) ▸
       at 10 1 (Bx3-24 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (Bx3-2014 ∷ [])
  b2 = at 5 6 (Bx2-314 ∷ []) (refl) ▸
       at 0 6 (Bx3-2014 ∷ []) (refl) ▸ done

-- sym-ab @03243042: 18 steps
lem-sym-ab-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-sym-ab-at03243042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-1402 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (wp0661 c4) ▸
       at 4 1 (Bx3-42 ∷ []) (refl) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ [])
  b1 = at 2 6 (Bx4-302 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (wp0661 c4) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸
       at 10 1 (Bx3-42 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (Bx3-4102 ∷ [])
  b2 = at 5 6 (Bx4-302 ∷ []) (refl) ▸
       at 0 6 (Bx3-4102 ∷ []) (refl) ▸ done

-- sym-ab @0314213042: 18 steps
lem-sym-ab-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-sym-ab-at0314213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-4102 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (sym (wl0344 (lit c4))) ▸
       at 4 1 (Bx3-12 ∷ []) (refl) ▸
       at 7 1 (Bx3-12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ [])
  b1 = at 2 6 (Bx1-302 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (sym (wl0344 (lit c4))) ▸
       at 7 1 (Bx3-12 ∷ []) (refl) ▸
       at 10 1 (Bx3-12 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (Bx3-1402 ∷ [])
  b2 = at 5 6 (Bx1-302 ∷ []) (refl) ▸
       at 0 6 (Bx3-1402 ∷ []) (refl) ▸ done

-- sym-ab @142142: 18 steps
lem-sym-ab-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-sym-ab-at142142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-4132 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (sym (wl0344 (lit c4))) ▸
       at 4 1 (Bx0-12 ∷ []) (refl) ▸
       at 7 1 (Bx0-12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ [])
  b1 = at 2 6 (Bx1-032 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (sym (wl0344 (lit c4))) ▸
       at 7 1 (Bx0-12 ∷ []) (refl) ▸
       at 10 1 (Bx0-12 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (Bx0-1432 ∷ [])
  b2 = at 5 6 (Bx1-032 ∷ []) (refl) ▸
       at 0 6 (Bx0-1432 ∷ []) (refl) ▸ done

-- sym-ab @2442: 18 steps
lem-sym-ab-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-sym-ab-at2442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1432 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (wp0661 c4) ▸
       at 4 1 (Bx0-42 ∷ []) (refl) ▸
       at 7 1 (Bx0-42 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ [])
  b1 = at 2 6 (Bx4-032 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (wp0661 c4) ▸
       at 7 1 (Bx0-42 ∷ []) (refl) ▸
       at 10 1 (Bx0-42 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (Bx0-4132 ∷ [])
  b2 = at 5 6 (Bx4-032 ∷ []) (refl) ▸
       at 0 6 (Bx0-4132 ∷ []) (refl) ▸ done

-- sym-ab @02102331: 18 steps
lem-sym-ab-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-sym-ab-at02102331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-0314 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp1232 c4) ▸
       at 2 1 (CCZ123 ∷ Toff312 ∷ CZ34 ∷ Toff312 ∷ CCZ123 ∷ CZ34 ∷ []) (sym (wl1341 (lit c4))) ▸
       at 4 1 (Bx2-34 ∷ []) (refl) ▸
       at 7 1 (Bx2-34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ [])
  b1 = at 2 6 (Bx3-214 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (wp1232 c4) ▸
       at 5 1 (CCZ123 ∷ Toff312 ∷ CZ34 ∷ Toff312 ∷ CCZ123 ∷ CZ34 ∷ []) (sym (wl1341 (lit c4))) ▸
       at 7 1 (Bx2-34 ∷ []) (refl) ▸
       at 10 1 (Bx2-34 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (Bx2-3014 ∷ [])
  b2 = at 5 6 (Bx3-214 ∷ []) (refl) ▸
       at 0 6 (Bx2-3014 ∷ []) (refl) ▸ done

-- sym-ab @02132031: 18 steps
lem-sym-ab-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym-ab-at02132031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-3014 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wl1341 (lit c4)) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ []) (sym (wp1232 c4)) ▸
       at 4 1 (Bx2-04 ∷ []) (refl) ▸
       at 7 1 (Bx2-04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ [])
  b1 = at 2 6 (Bx0-214 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (wl1341 (lit c4)) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ []) (sym (wp1232 c4)) ▸
       at 7 1 (Bx2-04 ∷ []) (refl) ▸
       at 10 1 (Bx2-04 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (Bx2-0314 ∷ [])
  b2 = at 5 6 (Bx0-214 ∷ []) (refl) ▸
       at 0 6 (Bx2-0314 ∷ []) (refl) ▸ done

-- F4-I-K2 @02132031: 1 steps
lem-F4-I-K2-at02132031 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K2-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0404 c4)) ▸ done

-- F4-S3-K2 @02132031: 1 steps
lem-F4-S3-K2-at02132031 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K2-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0441 c4)) ▸ done

-- F4-K2-K2 @02132031: 1 steps
lem-F4-K2-K2-at02132031 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K2-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0474 c4)) ▸ done

-- F4-I-S3 @02132031: 1 steps
lem-F4-I-S3-at02132031 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S3-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0550 (lit c4))) ▸ done

-- F4-S3-S3 @02132031: 1 steps
lem-F4-S3-S3-at02132031 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S3-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0564 (lit c4))) ▸ done

-- F4-K2-S3 @02132031: 1 steps
lem-F4-K2-S3-at02132031 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S3-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0471 c4)) ▸ done

-- F4-I-I @02132031: 1 steps
lem-F4-I-I-at02132031 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-I-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0549 (lit c4))) ▸ done

-- F4-S3-I @02132031: 1 steps
lem-F4-S3-I-at02132031 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-I-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0563 (lit c4))) ▸ done

-- F4-K2-I @02132031: 1 steps
lem-F4-K2-I-at02132031 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-I-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0469 c4)) ▸ done

-- F4-I-S2 @02132031: 1 steps
lem-F4-I-S2-at02132031 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S2-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0403 c4)) ▸ done

-- F4-S3-S2 @02132031: 1 steps
lem-F4-S3-S2-at02132031 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S2-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0440 c4)) ▸ done

-- F4-K2-S2 @02132031: 1 steps
lem-F4-K2-S2-at02132031 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S2-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0470 c4)) ▸ done

-- F4-I-K2 @132132: 1 steps
lem-F4-I-K2-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K2-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0553 (lit c4))) ▸ done

-- F4-S3-K2 @132132: 1 steps
lem-F4-S3-K2-at132132 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K2-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0579 (lit c4))) ▸ done

-- F4-K2-K2 @132132: 1 steps
lem-F4-K2-K2-at132132 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K2-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0607 (lit c4))) ▸ done

-- F4-I-S3 @132132: 1 steps
lem-F4-I-S3-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S3-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0551 (lit c4))) ▸ done

-- F4-S3-S3 @132132: 1 steps
lem-F4-S3-S3-at132132 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S3-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0577 (lit c4))) ▸ done

-- F4-K2-S3 @132132: 1 steps
lem-F4-K2-S3-at132132 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S3-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0605 (lit c4))) ▸ done

-- F4-I-I @132132: 1 steps
lem-F4-I-I-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-I-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0549 (lit c4))) ▸ done

-- F4-S3-I @132132: 1 steps
lem-F4-S3-I-at132132 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-I-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0575 (lit c4))) ▸ done

-- F4-K2-I @132132: 1 steps
lem-F4-K2-I-at132132 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-I-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0603 (lit c4))) ▸ done

-- F4-I-S2 @132132: 1 steps
lem-F4-I-S2-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S2-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0550 (lit c4))) ▸ done

-- F4-S3-S2 @132132: 1 steps
lem-F4-S3-S2-at132132 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S2-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0576 (lit c4))) ▸ done

-- F4-K2-S2 @132132: 1 steps
lem-F4-K2-S2-at132132 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S2-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0604 (lit c4))) ▸ done

-- F4-I-K3 @02132031: 1 steps
lem-F4-I-K3-at02132031 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K3-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0553 (lit c4))) ▸ done

-- F4-S2-K3 @02132031: 1 steps
lem-F4-S2-K3-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K3-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0416 c4)) ▸ done

-- F4-K3-K3 @02132031: 1 steps
lem-F4-K3-K3-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K3-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0607 (lit c4))) ▸ done

-- F4-S2-S2 @02132031: 1 steps
lem-F4-S2-S2-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S2-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸ done

-- F4-K3-S2 @02132031: 1 steps
lem-F4-K3-S2-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S2-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0494 c4)) ▸ done

-- F4-S2-I @02132031: 1 steps
lem-F4-S2-I-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-I-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0410 c4)) ▸ done

-- F4-K3-I @02132031: 1 steps
lem-F4-K3-I-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-I-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0603 (lit c4))) ▸ done

-- F4-S2-S3 @02132031: 1 steps
lem-F4-S2-S3-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S3-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0412 c4)) ▸ done

-- F4-K3-S3 @02132031: 1 steps
lem-F4-K3-S3-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S3-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0604 (lit c4))) ▸ done

-- F4-I-K3 @132132: 1 steps
lem-F4-I-K3-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K3-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0554 (lit c4))) ▸ done

-- F4-S2-K3 @132132: 1 steps
lem-F4-S2-K3-at132132 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K3-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0568 (lit c4))) ▸ done

-- F4-K3-K3 @132132: 1 steps
lem-F4-K3-K3-at132132 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K3-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0660 (lit c4))) ▸ done

-- F4-S2-S2 @132132: 1 steps
lem-F4-S2-S2-at132132 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S2-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0564 (lit c4))) ▸ done

-- F4-K3-S2 @132132: 1 steps
lem-F4-K3-S2-at132132 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S2-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0656 (lit c4))) ▸ done

-- F4-S2-I @132132: 1 steps
lem-F4-S2-I-at132132 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-I-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0563 (lit c4))) ▸ done

-- F4-K3-I @132132: 1 steps
lem-F4-K3-I-at132132 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-I-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0655 (lit c4))) ▸ done

-- F4-S2-S3 @132132: 1 steps
lem-F4-S2-S3-at132132 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S3-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0565 (lit c4))) ▸ done

-- F4-K3-S3 @132132: 1 steps
lem-F4-K3-S3-at132132 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S3-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0657 (lit c4))) ▸ done

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

-- F4-K3-S3 @0213243140: 1 steps
lem-F4-K3-S3-at0213243140 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-S3-at0213243140 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ CS01 ∷ []) (CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b0 = at 0 4 (CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1454 (lit c4))) ▸ done

-- F4-K2-K1 @0440: 1 steps
lem-F4-K2-K1-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-K1-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b0 = at 0 4 (CK01 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1476 (lit c4))) ▸ done

-- F4-K2-K2 @0440: 1 steps
lem-F4-K2-K2-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-K2-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b0 = at 0 4 (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1531 (lit c4))) ▸ done

-- F4-I-K2 @0440: 1 steps
lem-F4-I-K2-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-K2-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b0 = at 0 4 (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1532 (lit c4))) ▸ done

-- F4-I-K1 @0440: 1 steps
lem-F4-I-K1-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-K1-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b0 = at 0 4 (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1440 (lit c4))) ▸ done

-- F4-K2-I @0440: 1 steps
lem-F4-K2-I-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-I-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b0 = at 0 4 (S0 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1556 (lit c4))) ▸ done

-- F4-I-I @0440: 1 steps
lem-F4-I-I-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-I-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b0 = at 0 4 (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1445 (lit c4))) ▸ done

-- F4-K3-I @0440: 1 steps
lem-F4-K3-I-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-I-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK03 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b0 = at 0 4 (S0 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wl1559 (lit c4))) ▸ done

-- F4-K3-K2 @0440: 1 steps
lem-F4-K3-K2-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-K2-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK03 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b0 = at 0 4 (CK02 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wl1560 (lit c4))) ▸ done

-- sym-ab @04122041: 18 steps
lem-sym-ab-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ []) ⟫ʷ
lem-sym-ab-at04122041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-2031 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (sym (wp1048 c4)) ▸
       at 4 1 (Bx4-01 ∷ []) (refl) ▸
       at 7 1 (Bx4-01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ [])
  b1 = at 2 6 (Bx0-431 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (sym (wp1048 c4)) ▸
       at 7 1 (Bx4-01 ∷ []) (refl) ▸
       at 10 1 (Bx4-01 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (Bx4-0231 ∷ [])
  b2 = at 5 6 (Bx0-431 ∷ []) (refl) ▸
       at 0 6 (Bx4-0231 ∷ []) (refl) ▸ done

-- nat-SWbc @041041: 23 steps
lem-nat-SWbc-at041041 : Ws → ⟪ (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ []) ⟫ʷ
lem-nat-SWbc-at041041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ Sw23 ∷ CCZ034 ∷ Bx4-01 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (wp0987 c4) ▸
       at 3 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (wp0986 c4) ▸
       at 4 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 5 2 (Toff024 ∷ Sw23 ∷ []) (wp0986 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ Sw23 ∷ CCZ034 ∷ Bx4-01 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ Toff403 ∷ CCZ034 ∷ CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Sw23 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 7 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 8 2 (Toff403 ∷ Sw23 ∷ []) (wp0987 c4) ▸
       at 9 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 11 2 (Toff024 ∷ Sw23 ∷ []) (wp0986 c4) ▸
       at 12 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸ done

  b2 : Chain (CCZ034 ∷ Toff403 ∷ CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ Toff403 ∷ CCZ034 ∷ CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Sw23 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ Sw23 ∷ []) (Bx4-0321 ∷ [])
  b2 = at 13 2 (Toff024 ∷ Sw23 ∷ []) (wp0986 c4) ▸
       at 14 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 15 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 16 2 [] (wl0003 (lit c4)) ▸
       at 2 6 (Bx0-421 ∷ []) (refl) ▸
       at 5 6 (Bx0-421 ∷ []) (refl) ▸
       at 0 6 (Bx4-0321 ∷ []) (refl) ▸ done

-- F4-K3-K1 @0440: 1 steps
lem-F4-K3-K1-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-K1-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b0 = at 0 4 (CK01 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wl1573 (lit c4))) ▸ done

-- F4-K3-K3 @0440: 1 steps
lem-F4-K3-K3-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-K3-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b0 = at 0 4 (CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wl1578 (lit c4))) ▸ done

-- F4-I-K3 @0440: 1 steps
lem-F4-I-K3-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-K3-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b0 = at 0 4 (CK03 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1579 (lit c4))) ▸ done

-- F4-K2-K3 @0440: 1 steps
lem-F4-K2-K3-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-K3-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b0 = at 0 4 (CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1580 (lit c4))) ▸ done

-- F4-K1-I @0440: 1 steps
lem-F4-K1-I-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-I-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b0 = at 0 4 (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1449 (lit c4))) ▸ done

-- F4-K1-K3 @0440: 1 steps
lem-F4-K1-K3-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-K3-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b0 = at 0 4 (CK03 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1582 (lit c4))) ▸ done

-- F4-K1-K2 @0440: 1 steps
lem-F4-K1-K2-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-K2-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b0 = at 0 4 (CK02 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1584 (lit c4))) ▸ done

-- F4-K1-K1 @0440: 1 steps
lem-F4-K1-K1-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-K1-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b0 = at 0 4 (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1444 (lit c4))) ▸ done

-- sym-ab @0413213240: 18 steps
lem-sym-ab-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-sym-ab-at0413213240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-3120 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (wp0767 c4) ▸
       at 4 1 (Bx4-10 ∷ []) (refl) ▸
       at 7 1 (Bx4-10 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ []) (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ [])
  b1 = at 2 6 (Bx1-420 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (wp0767 c4) ▸
       at 7 1 (Bx4-10 ∷ []) (refl) ▸
       at 10 1 (Bx4-10 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (Bx4-1320 ∷ [])
  b2 = at 5 6 (Bx1-420 ∷ []) (refl) ▸
       at 0 6 (Bx4-1320 ∷ []) (refl) ▸ done

-- nat-SWbc @04233240: 23 steps
lem-nat-SWbc-at04233240 : Ws → ⟪ (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-nat-SWbc-at04233240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ Sw23 ∷ CCZ124 ∷ Bx4-10 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (sym (wl1592 (lit c4))) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (wl1593 (lit c4)) ▸
       at 3 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (sym (wl1594 (lit c4))) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (wl1595 (lit c4)) ▸
       at 4 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 5 2 (Toff134 ∷ Sw23 ∷ []) (wl1595 (lit c4)) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ Sw23 ∷ CCZ124 ∷ Bx4-10 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ Sw23 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Sw23 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ134 ∷ Sw23 ∷ []) (sym (wl1594 (lit c4))) ▸
       at 7 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 8 2 (Toff412 ∷ Sw23 ∷ []) (wl1593 (lit c4)) ▸
       at 9 2 (CCZ124 ∷ Sw23 ∷ []) (sym (wl1592 (lit c4))) ▸
       at 11 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 10 2 (CCZ134 ∷ Sw23 ∷ []) (sym (wl1594 (lit c4))) ▸
       at 11 2 (Toff134 ∷ Sw23 ∷ []) (wl1595 (lit c4)) ▸
       at 12 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸ done

  b2 : Chain (CCZ124 ∷ Toff412 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Sw23 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ Sw23 ∷ []) (Bx4-1230 ∷ [])
  b2 = at 13 2 (Toff134 ∷ Sw23 ∷ []) (wl1595 (lit c4)) ▸
       at 14 2 (CCZ134 ∷ Sw23 ∷ []) (sym (wl1594 (lit c4))) ▸
       at 15 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 16 2 [] (wl0003 (lit c4)) ▸
       at 2 6 (Bx1-430 ∷ []) (refl) ▸
       at 5 6 (Bx1-430 ∷ []) (refl) ▸
       at 0 6 (Bx4-1230 ∷ []) (refl) ▸ done

-- sym-ab @022440: 18 steps
lem-sym-ab-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ []) ⟫ʷ
lem-sym-ab-at022440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-1430 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (wp0992 c4) ▸
       at 4 1 (Bx2-40 ∷ []) (refl) ▸
       at 7 1 (Bx2-40 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (CCZ124 ∷ Toff214 ∷ Bx4-230 ∷ Toff214 ∷ CCZ124 ∷ CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ [])
  b1 = at 2 6 (Bx4-230 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (wp0992 c4) ▸
       at 7 1 (Bx2-40 ∷ []) (refl) ▸
       at 10 1 (Bx2-40 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ124 ∷ Toff214 ∷ Bx4-230 ∷ Toff214 ∷ CCZ124 ∷ CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) (Bx2-4130 ∷ [])
  b2 = at 5 6 (Bx4-230 ∷ []) (refl) ▸
       at 0 6 (Bx2-4130 ∷ []) (refl) ▸ done

-- nat-SWbc @0413203142: 23 steps
lem-nat-SWbc-at0413203142 : Ws → ⟪ (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-nat-SWbc-at0413203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ Sw01 ∷ CCZ134 ∷ Bx4-32 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (wp0678 c4) ▸
       at 3 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (wp0676 c4) ▸
       at 4 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 5 2 (Toff304 ∷ Sw01 ∷ []) (wp0676 c4) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ Sw01 ∷ CCZ134 ∷ Bx4-32 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ Sw01 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ Toff413 ∷ CCZ134 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Sw01 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 7 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 8 2 (Toff413 ∷ Sw01 ∷ []) (wp0678 c4) ▸
       at 9 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 11 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 11 2 (Toff304 ∷ Sw01 ∷ []) (wp0676 c4) ▸
       at 12 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ Toff413 ∷ CCZ134 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Sw01 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ Sw01 ∷ []) (Bx4-3102 ∷ [])
  b2 = at 13 2 (Toff304 ∷ Sw01 ∷ []) (wp0676 c4) ▸
       at 14 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 15 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx3-402 ∷ []) (refl) ▸
       at 5 6 (Bx3-402 ∷ []) (refl) ▸
       at 0 6 (Bx4-3102 ∷ []) (refl) ▸ done

-- sym-ab @0413213042: 18 steps
lem-sym-ab-at0413213042 : Ws → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ []) ⟫ʷ
lem-sym-ab-at0413213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-3102 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (sym (wp0212 c4)) ▸
       at 4 1 (Bx4-12 ∷ []) (refl) ▸
       at 7 1 (Bx4-12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ [])
  b1 = at 2 6 (Bx1-402 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (sym (wp0212 c4)) ▸
       at 7 1 (Bx4-12 ∷ []) (refl) ▸
       at 10 1 (Bx4-12 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (Bx4-1302 ∷ [])
  b2 = at 5 6 (Bx1-402 ∷ []) (refl) ▸
       at 0 6 (Bx4-1302 ∷ []) (refl) ▸ done

-- sym-ab @04233042: 18 steps
lem-sym-ab-at04233042 : Ws → ⟪ (Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-sym-ab-at04233042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-1302 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (wp0211 c4) ▸
       at 4 1 (Bx4-32 ∷ []) (refl) ▸
       at 7 1 (Bx4-32 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ []) (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ [])
  b1 = at 2 6 (Bx3-402 ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (wp0211 c4) ▸
       at 7 1 (Bx4-32 ∷ []) (refl) ▸
       at 10 1 (Bx4-32 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (Bx4-3102 ∷ [])
  b2 = at 5 6 (Bx3-402 ∷ []) (refl) ▸
       at 0 6 (Bx4-3102 ∷ []) (refl) ▸ done

-- nat-SWbc @0413213042: 23 steps
lem-nat-SWbc-at0413213042 : Ws → ⟪ (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-nat-SWbc-at0413213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ Sw01 ∷ CCZ034 ∷ Bx4-32 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (wp0696 c4) ▸
       at 3 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (wp0695 c4) ▸
       at 4 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 5 2 (Toff314 ∷ Sw01 ∷ []) (wp0695 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ Sw01 ∷ CCZ034 ∷ Bx4-32 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ Sw01 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Sw01 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 7 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 8 2 (Toff403 ∷ Sw01 ∷ []) (wp0696 c4) ▸
       at 9 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 10 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 11 2 (Toff314 ∷ Sw01 ∷ []) (wp0695 c4) ▸
       at 12 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff403 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Sw01 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ Sw01 ∷ []) (Bx4-3012 ∷ [])
  b2 = at 13 2 (Toff314 ∷ Sw01 ∷ []) (wp0695 c4) ▸
       at 14 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 15 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx3-412 ∷ []) (refl) ▸
       at 5 6 (Bx3-412 ∷ []) (refl) ▸
       at 0 6 (Bx4-3012 ∷ []) (refl) ▸ done

-- sym-ab @02142140: 18 steps
lem-sym-ab-at02142140 : Ws → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-sym-ab-at02142140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-4130 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ Toff214 ∷ CCZ124 ∷ Bx4-230 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-230 ∷ Toff214 ∷ CCZ124 ∷ Bx4-230 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (wl1126 (lit c4)) ▸
       at 4 1 (Bx2-10 ∷ []) (refl) ▸
       at 7 1 (Bx2-10 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ Toff214 ∷ CCZ124 ∷ Bx4-230 ∷ []) (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ [])
  b1 = at 2 6 (Bx1-230 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (wl1126 (lit c4)) ▸
       at 7 1 (Bx2-10 ∷ []) (refl) ▸
       at 10 1 (Bx2-10 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (Bx2-1430 ∷ [])
  b2 = at 5 6 (Bx1-230 ∷ []) (refl) ▸
       at 0 6 (Bx2-1430 ∷ []) (refl) ▸ done

-- nat-SWbc @0440: 23 steps
lem-nat-SWbc-at0440 : Ws → ⟪ (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-nat-SWbc-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ Sw23 ∷ CCZ134 ∷ Bx4-10 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (sym (wl1594 (lit c4))) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (wl1613 (lit c4)) ▸
       at 3 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (sym (wl1592 (lit c4))) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (wl1614 (lit c4)) ▸
       at 4 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 5 2 (Toff124 ∷ Sw23 ∷ []) (wl1614 (lit c4)) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ Sw23 ∷ CCZ134 ∷ Bx4-10 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ Sw23 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ Toff413 ∷ CCZ134 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Sw23 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ124 ∷ Sw23 ∷ []) (sym (wl1592 (lit c4))) ▸
       at 7 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 8 2 (Toff413 ∷ Sw23 ∷ []) (wl1613 (lit c4)) ▸
       at 9 2 (CCZ134 ∷ Sw23 ∷ []) (sym (wl1594 (lit c4))) ▸
       at 11 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 10 2 (CCZ124 ∷ Sw23 ∷ []) (sym (wl1592 (lit c4))) ▸
       at 11 2 (Toff124 ∷ Sw23 ∷ []) (wl1614 (lit c4)) ▸
       at 12 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ Toff413 ∷ CCZ134 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Sw23 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ Sw23 ∷ []) (Bx4-1320 ∷ [])
  b2 = at 13 2 (Toff124 ∷ Sw23 ∷ []) (wl1614 (lit c4)) ▸
       at 14 2 (CCZ124 ∷ Sw23 ∷ []) (sym (wl1592 (lit c4))) ▸
       at 15 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 16 2 [] (wl0003 (lit c4)) ▸
       at 2 6 (Bx1-420 ∷ []) (refl) ▸
       at 5 6 (Bx1-420 ∷ []) (refl) ▸
       at 0 6 (Bx4-1320 ∷ []) (refl) ▸ done

-- sym-ab @04233240: 18 steps
lem-sym-ab-at04233240 : Ws → ⟪ (Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-sym-ab-at04233240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-1320 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (wp0766 c4) ▸
       at 4 1 (Bx4-30 ∷ []) (refl) ▸
       at 7 1 (Bx4-30 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ [])
  b1 = at 2 6 (Bx3-420 ∷ []) (refl) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (wp0766 c4) ▸
       at 7 1 (Bx4-30 ∷ []) (refl) ▸
       at 10 1 (Bx4-30 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (Bx4-3120 ∷ [])
  b2 = at 5 6 (Bx3-420 ∷ []) (refl) ▸
       at 0 6 (Bx4-3120 ∷ []) (refl) ▸ done

-- nat-S @0410213243: 31 steps
lem-nat-S-at0410213243 : Ws → ⟪ (Sw23 ∷ Sb2-4-01-3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-01-2 ∷ []) ⟫ʷ
lem-nat-S-at0410213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw23 ∷ Sb2-4-01-3 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff304 ∷ Sw23 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (wp0719 c4) ▸
       at 3 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 5 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ Sw23 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Sw23 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Sw23 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Sw23 ∷ [])
  b1 = at 8 1 (CZ34 ∷ []) (refl) ▸
       at 2 7 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ Sw23 ∷ []) (sym (wl1659 (lit c4))) ▸
       at 4 1 (Bx3-42 ∷ []) (refl) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸
       at 2 6 (Bx4-312 ∷ []) (refl) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (wp0719 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 6 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Sw23 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Sw23 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ Toff201 ∷ CS24 ∷ Sw23 ∷ Toff301 ∷ CS34⁻ ∷ Sw23 ∷ [])
  b2 = at 8 1 (CZ34 ∷ []) (refl) ▸
       at 11 1 (CZ34 ∷ []) (refl) ▸
       at 5 7 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ Sw23 ∷ []) (sym (wl1659 (lit c4))) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸
       at 10 1 (Bx3-42 ∷ []) (refl) ▸
       at 5 6 (Bx4-312 ∷ []) (refl) ▸
       at 6 2 (Toff201 ∷ Sw23 ∷ []) (wl1660 (lit c4)) ▸
       at 7 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸ done

  b3 : Chain (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ Toff201 ∷ CS24 ∷ Sw23 ∷ Toff301 ∷ CS34⁻ ∷ Sw23 ∷ []) (Sb3-4-01-2 ∷ [])
  b3 = at 8 2 (Toff201 ∷ Sw23 ∷ []) (wl1660 (lit c4)) ▸
       at 9 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 (lit c4))) ▸
       at 10 2 [] (wl0003 (lit c4)) ▸
       at 0 6 (Bx3-4012 ∷ []) (refl) ▸
       at 2 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 0 5 (Sb3-4-01-2 ∷ []) (refl) ▸ done

-- sym-ab @04122140: 18 steps
lem-sym-ab-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-sym-ab-at04122140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-2130 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (wp0733 c4) ▸
       at 4 1 (Bx4-10 ∷ []) (refl) ▸
       at 7 1 (Bx4-10 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ [])
  b1 = at 2 6 (Bx1-430 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (wp0733 c4) ▸
       at 7 1 (Bx4-10 ∷ []) (refl) ▸
       at 10 1 (Bx4-10 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (Bx4-1230 ∷ [])
  b2 = at 5 6 (Bx1-430 ∷ []) (refl) ▸
       at 0 6 (Bx4-1230 ∷ []) (refl) ▸ done

-- sym-ab @0413203142: 18 steps
lem-sym-ab-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ []) ⟫ʷ
lem-sym-ab-at0413203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-3012 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (sym (wl1596 (lit c4))) ▸
       at 2 1 (CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) (sym (wp1437 c4)) ▸
       at 4 1 (Bx4-02 ∷ []) (refl) ▸
       at 7 1 (Bx4-02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ [])
  b1 = at 2 6 (Bx0-412 ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (sym (wl1596 (lit c4))) ▸
       at 5 1 (CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) (sym (wp1437 c4)) ▸
       at 7 1 (Bx4-02 ∷ []) (refl) ▸
       at 10 1 (Bx4-02 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (Bx4-0312 ∷ [])
  b2 = at 5 6 (Bx0-412 ∷ []) (refl) ▸
       at 0 6 (Bx4-0312 ∷ []) (refl) ▸ done

-- sym-ab @0410233142: 18 steps
lem-sym-ab-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-sym-ab-at0410233142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-0312 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp1437 c4) ▸
       at 2 1 (CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ []) (wl1596 (lit c4)) ▸
       at 4 1 (Bx4-32 ∷ []) (refl) ▸
       at 7 1 (Bx4-32 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ [])
  b1 = at 2 6 (Bx3-412 ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (wp1437 c4) ▸
       at 5 1 (CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ []) (wl1596 (lit c4)) ▸
       at 7 1 (Bx4-32 ∷ []) (refl) ▸
       at 10 1 (Bx4-32 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (Bx4-3012 ∷ [])
  b2 = at 5 6 (Bx3-412 ∷ []) (refl) ▸
       at 0 6 (Bx4-3012 ∷ []) (refl) ▸ done

-- sym-ab @0440: 18 steps
lem-sym-ab-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-sym-ab-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-1230 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (wp0732 c4) ▸
       at 4 1 (Bx4-20 ∷ []) (refl) ▸
       at 7 1 (Bx4-20 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ [])
  b1 = at 2 6 (Bx2-430 ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (wp0732 c4) ▸
       at 7 1 (Bx4-20 ∷ []) (refl) ▸
       at 10 1 (Bx4-20 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (Bx4-2130 ∷ [])
  b2 = at 5 6 (Bx2-430 ∷ []) (refl) ▸
       at 0 6 (Bx4-2130 ∷ []) (refl) ▸ done

-- F4-S0-K1 @0440: 1 steps
lem-F4-S0-K1-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-K1-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 4 (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1293 c4)) ▸ done

-- sym-ab @0410233241: 18 steps
lem-sym-ab-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3021 ∷ []) ⟫ʷ
lem-sym-ab-at0410233241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-0321 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (wl0756 (lit c4)) ▸
       at 4 1 (Bx4-31 ∷ []) (refl) ▸
       at 7 1 (Bx4-31 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (CCZ034 ∷ Toff403 ∷ Bx3-421 ∷ Toff403 ∷ CCZ034 ∷ CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ [])
  b1 = at 2 6 (Bx3-421 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (wl0756 (lit c4)) ▸
       at 7 1 (Bx4-31 ∷ []) (refl) ▸
       at 10 1 (Bx4-31 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff403 ∷ Bx3-421 ∷ Toff403 ∷ CCZ034 ∷ CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) (Bx4-3021 ∷ [])
  b2 = at 5 6 (Bx3-421 ∷ []) (refl) ▸
       at 0 6 (Bx4-3021 ∷ []) (refl) ▸ done

-- F4-S0-K2 @0440: 1 steps
lem-F4-S0-K2-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-K2-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 4 (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1488 c4)) ▸ done

-- sym-ab @0412233140: 18 steps
lem-sym-ab-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ []) ⟫ʷ
lem-sym-ab-at0412233140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-2310 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp1436 c4)) ▸
       at 2 1 (CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ []) (wp1503 c4) ▸
       at 4 1 (Bx4-30 ∷ []) (refl) ▸
       at 7 1 (Bx4-30 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ []) (CCZ234 ∷ Toff423 ∷ Bx3-410 ∷ Toff423 ∷ CCZ234 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ [])
  b1 = at 2 6 (Bx3-410 ∷ []) (refl) ▸
       at 5 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (sym (wp1436 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ []) (wp1503 c4) ▸
       at 7 1 (Bx4-30 ∷ []) (refl) ▸
       at 10 1 (Bx4-30 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ234 ∷ Toff423 ∷ Bx3-410 ∷ Toff423 ∷ CCZ234 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (Bx4-3210 ∷ [])
  b2 = at 5 6 (Bx3-410 ∷ []) (refl) ▸
       at 0 6 (Bx4-3210 ∷ []) (refl) ▸ done

-- sym-ab @04133140: 18 steps
lem-sym-ab-at04133140 : Ws → ⟪ (Bx4-3210 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-sym-ab-at04133140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-3210 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff423 ∷ Bx3-410 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp1503 c4)) ▸
       at 2 1 (CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ []) (wp1436 c4) ▸
       at 4 1 (Bx4-20 ∷ []) (refl) ▸
       at 7 1 (Bx4-20 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ []) (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ [])
  b1 = at 2 6 (Bx2-410 ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (sym (wp1503 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ []) (wp1436 c4) ▸
       at 7 1 (Bx4-20 ∷ []) (refl) ▸
       at 10 1 (Bx4-20 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (Bx4-2310 ∷ [])
  b2 = at 5 6 (Bx2-410 ∷ []) (refl) ▸
       at 0 6 (Bx4-2310 ∷ []) (refl) ▸ done

-- F4-S0-I @0440: 1 steps
lem-F4-S0-I-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-I-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 4 (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1300 c4)) ▸ done

-- F4-S0-K3 @0440: 1 steps
lem-F4-S0-K3-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-K3-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 4 (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1518 c4)) ▸ done
