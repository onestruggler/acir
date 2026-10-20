{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D001 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0003 ; wl0182 ; wl0184 ; wl0205 ; wl0231 ; wl0268 ; wl0269 ; wp0008 ; wp0111 ; wp0115 ; wp0116 ; wp0117 ; wl0288 ; wl0292 ; wl0328 ; wp0130 ; wp0131 ; wp0136 ; wp0153 ; wp0154 ; wp0162 ; wp0180 ; wp0198 ; wp0211 ; wp0212 ; wp0214 ; wl0348 ; wl0414 ; wl0415 ; wp0216 ; wp0217 ; wp0218 ; wp0279 ; wp0280 ; wl0432 ; wl0433 ; wl0451 ; wl0452 ; wl0477 ; wl0486 ; wl0493 ; wl0494 ; wp0294 ; wp0301 ; wp0302 ; wp0305 ; wp0341 ; wp0342 ; wl0004 ; wl0518 ; wl0548 ; wl0549 ; wl0550 ; wl0551 ; wl0552 ; wl0553 ; wl0554 ; wl0555 ; wl0563 ; wl0564 ; wl0565 ; wl0566 ; wl0567 ; wl0568 ; wl0569 ; wp0363 ; wp0398 ; wp0399 ; wp0400 ; wp0401 ; wp0402 ; wp0403 ; wp0404 ; wp0410 ; wp0411 ; wp0412 ; wp0413 ; wp0414 ; wp0415 ; wp0416 ; wp0417 ; wp0418 ; wp0440 ; wp0441 ; wl0006 ; wl0018 ; wl0575 ; wl0576 ; wl0577 ; wl0578 ; wl0579 ; wl0580 ; wl0581 ; wl0588 ; wl0589 ; wl0590 ; wl0591 ; wl0592 ; wl0593 ; wl0594 ; wl0603 ; wl0604 ; wl0605 ; wl0606 ; wl0607 ; wl0608 ; wl0609 ; wl0610 ; wl0655 ; wl0656 ; wl0657 ; wl0658 ; wl0659 ; wl0660 ; wl0661 ; wp0447 ; wp0448 ; wp0462 ; wp0463 ; wp0469 ; wp0470 ; wp0471 ; wp0472 ; wp0473 ; wp0474 ; wp0475 ; wp0476 ; wp0477 ; wp0494 ; wp0495 ; wp0509 ; wp0510 ; wp0511 ; wp0512 ; wp0516 ; wp0527 ; wp0528 ; wp0529 ; wp0530 ; wp0532 ; wp0533 ; wp0551 ; wp0552 ; wp0553 ; wp0554 ; wl0687 ; wl0688 ; wl0689 ; wl0690 ; wl0691 ; wl0692 ; wl0693 ; wp0557 ; wp0558 ; wp0594 ; wl0756 ; wp0675 ; wp0676 ; wp0677 ; wp0678 ; wp0695 ; wp0696 ; wl0814 ; wl0815 ; wl0816 ; wl0817 ; wl0838 ; wl0839 ; wl0840 ; wl0841 ; wl0876 ; wl0877 ; wp0714 ; wp0715 ; wp0719 ; wp0732 ; wp0733)
open import Examples.Groups.Clifford+CS.Five.Chain

-- sym-ab: 18 steps
lem-sym-ab : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym-ab c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (sym (wp0111 c4)) ▸
       at 4 1 (Bx0-24 ∷ []) (refl) ▸
       at 7 1 (Bx0-24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ [])
  b1 = at 2 6 (Bx2-034 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (sym (wp0111 c4)) ▸
       at 7 1 (Bx0-24 ∷ []) (refl) ▸
       at 10 1 (Bx0-24 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (Bx0-2134 ∷ [])
  b2 = at 5 6 (Bx2-034 ∷ []) (refl) ▸
       at 0 6 (Bx0-2134 ∷ []) (refl) ▸ done

-- cQ @13243142: 7 steps
lem-cQ-at13243142 : Ws → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at13243142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (wp0115 c4) ▸
       at 4 2 (CCZ012 ∷ CS03 ∷ []) (sym (wl0268 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (CCZ012 ∷ CS04⁻ ∷ []) (sym (wp0116 c4)) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 0 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0115 c4)) ▸ done

-- cQ @13243241: 7 steps
lem-cQ-at13243241 : Ws → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at13243241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (wp0115 c4) ▸
       at 4 2 (CCZ012 ∷ CS03 ∷ []) (sym (wl0268 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (CCZ012 ∷ CS04⁻ ∷ []) (sym (wp0116 c4)) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 0 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0115 c4)) ▸ done

-- sym-ab @2332: 18 steps
lem-sym-ab-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym-ab-at2332 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1324 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (sym (wp0131 c4)) ▸
       at 4 1 (Bx0-34 ∷ []) (refl) ▸
       at 7 1 (Bx0-34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ [])
  b1 = at 2 6 (Bx3-024 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (sym (wp0131 c4)) ▸
       at 7 1 (Bx0-34 ∷ []) (refl) ▸
       at 10 1 (Bx0-34 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (Bx0-3124 ∷ [])
  b2 = at 5 6 (Bx3-024 ∷ []) (refl) ▸
       at 0 6 (Bx0-3124 ∷ []) (refl) ▸ done

-- sym-ab @13243142: 18 steps
lem-sym-ab-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-sym-ab-at13243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3412 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0269 (lit c4))) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (wp0136 c4) ▸
       at 4 1 (Bx0-42 ∷ []) (refl) ▸
       at 7 1 (Bx0-42 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ [])
  b1 = at 2 6 (Bx4-012 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (sym (wl0269 (lit c4))) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (wp0136 c4) ▸
       at 7 1 (Bx0-42 ∷ []) (refl) ▸
       at 10 1 (Bx0-42 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (Bx0-4312 ∷ [])
  b2 = at 5 6 (Bx4-012 ∷ []) (refl) ▸
       at 0 6 (Bx0-4312 ∷ []) (refl) ▸ done

-- sym-ab @122331: 18 steps
lem-sym-ab-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym-ab-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2314 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (wp0153 c4) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (sym (wp0154 c4)) ▸
       at 4 1 (Bx0-34 ∷ []) (refl) ▸
       at 7 1 (Bx0-34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ [])
  b1 = at 2 6 (Bx3-014 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (wp0153 c4) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (sym (wp0154 c4)) ▸
       at 7 1 (Bx0-34 ∷ []) (refl) ▸
       at 10 1 (Bx0-34 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (Bx0-3214 ∷ [])
  b2 = at 5 6 (Bx3-014 ∷ []) (refl) ▸
       at 0 6 (Bx0-3214 ∷ []) (refl) ▸ done

-- sym-ab @13243241: 18 steps
lem-sym-ab-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-sym-ab-at13243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3421 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (wp0162 c4) ▸
       at 4 1 (Bx0-41 ∷ []) (refl) ▸
       at 7 1 (Bx0-41 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ [])
  b1 = at 2 6 (Bx4-021 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (wp0162 c4) ▸
       at 7 1 (Bx0-41 ∷ []) (refl) ▸
       at 10 1 (Bx0-41 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (Bx0-4321 ∷ [])
  b2 = at 5 6 (Bx4-021 ∷ []) (refl) ▸
       at 0 6 (Bx0-4321 ∷ []) (refl) ▸ done

-- sym-ab @12243143: 18 steps
lem-sym-ab-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym-ab-at12243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2413 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (wl0292 (lit c4)) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (wp0180 c4) ▸
       at 4 1 (Bx0-43 ∷ []) (refl) ▸
       at 7 1 (Bx0-43 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ [])
  b1 = at 2 6 (Bx4-013 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸
       at 5 6 (CCZ013 ∷ []) (wl0292 (lit c4)) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (wp0180 c4) ▸
       at 7 1 (Bx0-43 ∷ []) (refl) ▸
       at 10 1 (Bx0-43 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (Bx0-4213 ∷ [])
  b2 = at 5 6 (Bx4-013 ∷ []) (refl) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done

-- cQ @14233142: 7 steps
lem-cQ-at14233142 : Ws → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at14233142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) (wp0198 c4) ▸
       at 4 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 3 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 2 2 (CCZ012 ∷ CS03⁻ ∷ []) (sym (wl0328 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 0 2 (CCZ012 ∷ CS03 ∷ []) (sym (wl0268 (lit c4))) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0198 c4)) ▸ done

-- sym-ab @13213442: 18 steps
lem-sym-ab-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym-ab-at13213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3142 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (sym (wp0212 c4)) ▸
       at 4 1 (Bx0-12 ∷ []) (refl) ▸
       at 7 1 (Bx0-12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ [])
  b1 = at 2 6 (Bx1-042 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (sym (wp0212 c4)) ▸
       at 7 1 (Bx0-12 ∷ []) (refl) ▸
       at 10 1 (Bx0-12 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (Bx0-1342 ∷ [])
  b2 = at 5 6 (Bx1-042 ∷ []) (refl) ▸
       at 0 6 (Bx0-1342 ∷ []) (refl) ▸ done

-- sym-ab @243243: 18 steps
lem-sym-ab-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-sym-ab-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1423 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0205 (lit c4)) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (wp0216 c4) ▸
       at 4 1 (Bx0-43 ∷ []) (refl) ▸
       at 7 1 (Bx0-43 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ [])
  b1 = at 2 6 (Bx4-023 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (wl0205 (lit c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (wp0216 c4) ▸
       at 7 1 (Bx0-43 ∷ []) (refl) ▸
       at 10 1 (Bx0-43 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (Bx0-4123 ∷ [])
  b2 = at 5 6 (Bx4-023 ∷ []) (refl) ▸
       at 0 6 (Bx0-4123 ∷ []) (refl) ▸ done

-- sym-ab @133441: 18 steps
lem-sym-ab-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym-ab-at133441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3241 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp0217 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (wp0218 c4) ▸
       at 4 1 (Bx0-21 ∷ []) (refl) ▸
       at 7 1 (Bx0-21 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ [])
  b1 = at 2 6 (Bx2-041 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (sym (wp0217 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (wp0218 c4) ▸
       at 7 1 (Bx0-21 ∷ []) (refl) ▸
       at 10 1 (Bx0-21 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (Bx0-2341 ∷ [])
  b2 = at 5 6 (Bx2-041 ∷ []) (refl) ▸
       at 0 6 (Bx0-2341 ∷ []) (refl) ▸ done

-- sym-ab @12233441: 18 steps
lem-sym-ab-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-sym-ab-at12233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2341 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp0218 c4)) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) (wp0217 c4) ▸
       at 4 1 (Bx0-31 ∷ []) (refl) ▸
       at 7 1 (Bx0-31 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ [])
  b1 = at 2 6 (Bx3-041 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (sym (wp0218 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) (wp0217 c4) ▸
       at 7 1 (Bx0-31 ∷ []) (refl) ▸
       at 10 1 (Bx0-31 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (Bx0-3241 ∷ [])
  b2 = at 5 6 (Bx3-041 ∷ []) (refl) ▸
       at 0 6 (Bx0-3241 ∷ []) (refl) ▸ done

-- sym-ab @1221: 18 steps
lem-sym-ab-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym-ab-at1221 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2134 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (sym (wp0008 c4)) ▸
       at 4 1 (Bx0-14 ∷ []) (refl) ▸
       at 7 1 (Bx0-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ [])
  b1 = at 2 6 (Bx1-034 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (sym (wp0008 c4)) ▸
       at 7 1 (Bx0-14 ∷ []) (refl) ▸
       at 10 1 (Bx0-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (Bx0-1234 ∷ [])
  b2 = at 5 6 (Bx1-034 ∷ []) (refl) ▸
       at 0 6 (Bx0-1234 ∷ []) (refl) ▸ done

-- cQ @021021: 7 steps
lem-cQ-at021021 : Ws → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at021021 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CS02 ∷ []) (sym (wp0279 c4)) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS12⁻ ∷ []) (sym (wl0414 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸ done

-- sym-ab @233442: 18 steps
lem-sym-ab-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym-ab-at233442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1342 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (wp0211 c4) ▸
       at 4 1 (Bx0-32 ∷ []) (refl) ▸
       at 7 1 (Bx0-32 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ [])
  b1 = at 2 6 (Bx3-042 ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (wp0211 c4) ▸
       at 7 1 (Bx0-32 ∷ []) (refl) ▸
       at 10 1 (Bx0-32 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (Bx0-3142 ∷ [])
  b2 = at 5 6 (Bx3-042 ∷ []) (refl) ▸
       at 0 6 (Bx0-3142 ∷ []) (refl) ▸ done

-- cQ @03102132: 7 steps
lem-cQ-at03102132 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at03102132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸ done

-- sym-ab @14233142: 18 steps
lem-sym-ab-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-sym-ab-at14233142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-4312 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0136 c4)) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (wl0269 (lit c4)) ▸
       at 4 1 (Bx0-32 ∷ []) (refl) ▸
       at 7 1 (Bx0-32 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ [])
  b1 = at 2 6 (Bx3-012 ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (sym (wp0136 c4)) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (wl0269 (lit c4)) ▸
       at 7 1 (Bx0-32 ∷ []) (refl) ▸
       at 10 1 (Bx0-32 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (Bx0-3412 ∷ [])
  b2 = at 5 6 (Bx3-012 ∷ []) (refl) ▸
       at 0 6 (Bx0-3412 ∷ []) (refl) ▸ done

-- cQ @0410213243: 7 steps
lem-cQ-at0410213243 : Ws → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at0410213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 4 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS14⁻ ∷ []) (sym (wl0451 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 1 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸ done

-- cQ @04203243: 7 steps
lem-cQ-at04203243 : Ws → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at04203243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 4 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸
       at 1 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 1 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸ done

-- sym-ab @04203243: 18 steps
lem-sym-ab-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-sym-ab-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-1023 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0486 (lit c4)) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (sym (wp0305 c4)) ▸
       at 4 1 (Bx4-03 ∷ []) (refl) ▸
       at 7 1 (Bx4-03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ [])
  b1 = at 2 6 (Bx0-423 ∷ []) (refl) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wl0486 (lit c4)) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (sym (wp0305 c4)) ▸
       at 7 1 (Bx4-03 ∷ []) (refl) ▸
       at 10 1 (Bx4-03 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (Bx4-0123 ∷ [])
  b2 = at 5 6 (Bx0-423 ∷ []) (refl) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸ done

-- sym-ab @0310243142: 18 steps
lem-sym-ab-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym-ab-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-0412 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl0493 (lit c4)) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (wl0494 (lit c4)) ▸
       at 4 1 (Bx3-42 ∷ []) (refl) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ [])
  b1 = at 2 6 (Bx4-312 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (wl0493 (lit c4)) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (wl0494 (lit c4)) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸
       at 10 1 (Bx3-42 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (Bx3-4012 ∷ [])
  b2 = at 5 6 (Bx4-312 ∷ []) (refl) ▸
       at 0 6 (Bx3-4012 ∷ []) (refl) ▸ done

-- sym-ab @0314203142: 18 steps
lem-sym-ab-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym-ab-at0314203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-4012 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl0494 (lit c4))) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (sym (wl0493 (lit c4))) ▸
       at 4 1 (Bx3-02 ∷ []) (refl) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ [])
  b1 = at 2 6 (Bx0-312 ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (sym (wl0494 (lit c4))) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (sym (wl0493 (lit c4))) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸
       at 10 1 (Bx3-02 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (Bx3-0412 ∷ [])
  b2 = at 5 6 (Bx0-312 ∷ []) (refl) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done

-- sym-ab @0410213243: 18 steps
lem-sym-ab-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-sym-ab-at0410213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-0123 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (sym (wl0486 (lit c4))) ▸
       at 4 1 (Bx4-13 ∷ []) (refl) ▸
       at 7 1 (Bx4-13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ [])
  b1 = at 2 6 (Bx1-423 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (sym (wl0486 (lit c4))) ▸
       at 7 1 (Bx4-13 ∷ []) (refl) ▸
       at 10 1 (Bx4-13 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (Bx4-1023 ∷ [])
  b2 = at 5 6 (Bx1-423 ∷ []) (refl) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done

-- sym-ab @03102132: 18 steps
lem-sym-ab-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym-ab-at03102132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-0124 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (sym (wl0518 (lit c4))) ▸
       at 4 1 (Bx3-14 ∷ []) (refl) ▸
       at 7 1 (Bx3-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ [])
  b1 = at 2 6 (Bx1-324 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (sym (wl0518 (lit c4))) ▸
       at 7 1 (Bx3-14 ∷ []) (refl) ▸
       at 10 1 (Bx3-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (Bx3-1024 ∷ [])
  b2 = at 5 6 (Bx1-324 ∷ []) (refl) ▸
       at 0 6 (Bx3-1024 ∷ []) (refl) ▸ done

-- cQ @032032: 7 steps
lem-cQ-at032032 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at032032 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (wl0477 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS03⁻ ∷ []) (sym (wp0363 c4)) ▸
       at 1 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0477 (lit c4))) ▸ done

-- sym-ab @032032: 18 steps
lem-sym-ab-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym-ab-at032032 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-1024 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (sym (wp0280 c4)) ▸
       at 4 1 (Bx3-04 ∷ []) (refl) ▸
       at 7 1 (Bx3-04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ [])
  b1 = at 2 6 (Bx0-324 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (sym (wp0280 c4)) ▸
       at 7 1 (Bx3-04 ∷ []) (refl) ▸
       at 10 1 (Bx3-04 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (Bx3-0124 ∷ [])
  b2 = at 5 6 (Bx0-324 ∷ []) (refl) ▸
       at 0 6 (Bx3-0124 ∷ []) (refl) ▸ done

-- nat-S: 31 steps
lem-nat-S : Ws → ⟪ (Sw34 ∷ Sb3-0-12-4 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-12-3 ∷ []) ⟫ʷ
lem-nat-S c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw34 ∷ Sb3-0-12-4 ∷ Sw34 ∷ []) (CCZ014 ∷ Toff401 ∷ Sw34 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 3 1 (CS04 ∷ []) (refl) ▸
       at 5 1 (CS04⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (wp0399 c4) ▸
       at 3 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 5 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ Sw34 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Sw34 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ [])
  b1 = at 8 1 (CZ04 ∷ []) (refl) ▸
       at 2 7 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ Sw34 ∷ []) (sym (wp0400 c4)) ▸
       at 4 1 (Bx4-03 ∷ []) (refl) ▸
       at 7 1 (Bx4-03 ∷ []) (refl) ▸
       at 2 6 (Bx0-423 ∷ []) (refl) ▸
       at 3 2 (Toff401 ∷ Sw34 ∷ []) (wp0399 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 6 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Sw34 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ Toff312 ∷ CS03 ∷ Sw34 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ [])
  b2 = at 8 1 (CZ04 ∷ []) (refl) ▸
       at 11 1 (CZ04 ∷ []) (refl) ▸
       at 5 7 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ Sw34 ∷ []) (sym (wp0400 c4)) ▸
       at 7 1 (Bx4-03 ∷ []) (refl) ▸
       at 10 1 (Bx4-03 ∷ []) (refl) ▸
       at 5 6 (Bx0-423 ∷ []) (refl) ▸
       at 6 2 (Toff312 ∷ Sw34 ∷ []) (wl0548 (lit c4)) ▸
       at 7 2 (CS03 ∷ Sw34 ∷ []) (sym (wp0401 c4)) ▸ done

  b3 : Chain (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ Toff312 ∷ CS03 ∷ Sw34 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ []) (Sb4-0-12-3 ∷ [])
  b3 = at 8 2 (Toff312 ∷ Sw34 ∷ []) (wl0548 (lit c4)) ▸
       at 9 2 (CS03⁻ ∷ Sw34 ∷ []) (sym (wp0402 c4)) ▸
       at 10 2 [] (wl0004 (lit c4)) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸
       at 2 1 (Sb4-0-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-0-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-0-12-3 ∷ []) (refl) ▸ done

-- F4-I-I: 1 steps
lem-F4-I-I : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-I c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0549 (lit c4))) ▸ done

-- F4-I-S0: 1 steps
lem-F4-I-S0 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0403 c4)) ▸ done

-- F4-I-S1: 1 steps
lem-F4-I-S1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0550 (lit c4))) ▸ done

-- F4-I-S2: 1 steps
lem-F4-I-S2 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0551 (lit c4))) ▸ done

-- F4-I-S3: 1 steps
lem-F4-I-S3 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0552 (lit c4))) ▸ done

-- F4-I-K0: 1 steps
lem-F4-I-K0 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0404 c4)) ▸ done

-- F4-I-K1: 1 steps
lem-F4-I-K1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0553 (lit c4))) ▸ done

-- F4-I-K2: 1 steps
lem-F4-I-K2 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0554 (lit c4))) ▸ done

-- F4-I-K3: 1 steps
lem-F4-I-K3 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0555 (lit c4))) ▸ done

-- F4-S0-I: 1 steps
lem-F4-S0-I : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0410 c4)) ▸ done

-- F4-S0-S0: 1 steps
lem-F4-S0-S0 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸ done

-- F4-S0-S1: 1 steps
lem-F4-S0-S1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0412 c4)) ▸ done

-- F4-S0-S2: 1 steps
lem-F4-S0-S2 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0413 c4)) ▸ done

-- F4-S0-S3: 1 steps
lem-F4-S0-S3 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0414 c4)) ▸ done

-- F4-S0-K0: 1 steps
lem-F4-S0-K0 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0415 c4)) ▸ done

-- F4-S0-K1: 1 steps
lem-F4-S0-K1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0416 c4)) ▸ done

-- F4-S0-K2: 1 steps
lem-F4-S0-K2 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0417 c4)) ▸ done

-- F4-S0-K3: 1 steps
lem-F4-S0-K3 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0418 c4)) ▸ done

-- F4-S1-I: 1 steps
lem-F4-S1-I : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0563 (lit c4))) ▸ done

-- F4-S1-S0: 1 steps
lem-F4-S1-S0 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0440 c4)) ▸ done

-- F4-S1-S1: 1 steps
lem-F4-S1-S1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0564 (lit c4))) ▸ done

-- F4-S1-S2: 1 steps
lem-F4-S1-S2 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0565 (lit c4))) ▸ done

-- F4-S1-S3: 1 steps
lem-F4-S1-S3 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0566 (lit c4))) ▸ done

-- F4-S1-K0: 1 steps
lem-F4-S1-K0 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0441 c4)) ▸ done

-- F4-S1-K1: 1 steps
lem-F4-S1-K1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0567 (lit c4))) ▸ done

-- F4-S1-K2: 1 steps
lem-F4-S1-K2 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0568 (lit c4))) ▸ done

-- F4-S1-K3: 1 steps
lem-F4-S1-K3 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0569 (lit c4))) ▸ done

-- F4-S2-I: 1 steps
lem-F4-S2-I : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0575 (lit c4))) ▸ done

-- F4-S2-S0: 1 steps
lem-F4-S2-S0 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0447 c4)) ▸ done

-- F4-S2-S1: 1 steps
lem-F4-S2-S1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0576 (lit c4))) ▸ done

-- F4-S2-S2: 1 steps
lem-F4-S2-S2 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0577 (lit c4))) ▸ done

-- F4-S2-S3: 1 steps
lem-F4-S2-S3 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0578 (lit c4))) ▸ done

-- F4-S2-K0: 1 steps
lem-F4-S2-K0 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0448 c4)) ▸ done

-- F4-S2-K1: 1 steps
lem-F4-S2-K1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0579 (lit c4))) ▸ done

-- F4-S2-K2: 1 steps
lem-F4-S2-K2 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0580 (lit c4))) ▸ done

-- F4-S2-K3: 1 steps
lem-F4-S2-K3 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0581 (lit c4))) ▸ done

-- F4-S3-I: 1 steps
lem-F4-S3-I : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0588 (lit c4))) ▸ done

-- F4-S3-S0: 1 steps
lem-F4-S3-S0 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0462 c4)) ▸ done

-- F4-S3-S1: 1 steps
lem-F4-S3-S1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0589 (lit c4))) ▸ done

-- F4-S3-S2: 1 steps
lem-F4-S3-S2 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0590 (lit c4))) ▸ done

-- F4-S3-S3: 1 steps
lem-F4-S3-S3 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0591 (lit c4))) ▸ done

-- F4-S3-K0: 1 steps
lem-F4-S3-K0 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0463 c4)) ▸ done

-- F4-S3-K1: 1 steps
lem-F4-S3-K1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0592 (lit c4))) ▸ done

-- F4-S3-K2: 1 steps
lem-F4-S3-K2 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0593 (lit c4))) ▸ done

-- F4-S3-K3: 1 steps
lem-F4-S3-K3 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0594 (lit c4))) ▸ done

-- F4-K0-I: 1 steps
lem-F4-K0-I : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0469 c4)) ▸ done

-- F4-K0-S0: 1 steps
lem-F4-K0-S0 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0470 c4)) ▸ done

-- F4-K0-S1: 1 steps
lem-F4-K0-S1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0471 c4)) ▸ done

-- F4-K0-S2: 1 steps
lem-F4-K0-S2 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0472 c4)) ▸ done

-- F4-K0-S3: 1 steps
lem-F4-K0-S3 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0473 c4)) ▸ done

-- F4-K0-K0: 1 steps
lem-F4-K0-K0 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0474 c4)) ▸ done

-- F4-K0-K1: 1 steps
lem-F4-K0-K1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0475 c4)) ▸ done

-- F4-K0-K2: 1 steps
lem-F4-K0-K2 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0476 c4)) ▸ done

-- F4-K0-K3: 1 steps
lem-F4-K0-K3 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0477 c4)) ▸ done

-- F4-K1-I: 1 steps
lem-F4-K1-I : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0603 (lit c4))) ▸ done

-- F4-K1-S0: 1 steps
lem-F4-K1-S0 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0494 c4)) ▸ done

-- F4-K1-S1: 1 steps
lem-F4-K1-S1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0604 (lit c4))) ▸ done

-- F4-K1-S2: 1 steps
lem-F4-K1-S2 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0605 (lit c4))) ▸ done

-- F4-K1-S3: 1 steps
lem-F4-K1-S3 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0606 (lit c4))) ▸ done

-- F4-K1-K0: 1 steps
lem-F4-K1-K0 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0495 c4)) ▸ done

-- F4-K1-K1: 1 steps
lem-F4-K1-K1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0607 (lit c4))) ▸ done

-- F4-K1-K2: 1 steps
lem-F4-K1-K2 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0608 (lit c4))) ▸ done

-- F4-K1-K3: 1 steps
lem-F4-K1-K3 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0609 (lit c4))) ▸ done

-- sym-ab @0210243143: 18 steps
lem-sym-ab-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym-ab-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-0413 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl0182 (lit c4)) ▸
       at 2 1 (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (wl0610 (lit c4)) ▸
       at 4 1 (Bx2-43 ∷ []) (refl) ▸
       at 7 1 (Bx2-43 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ [])
  b1 = at 2 6 (Bx4-213 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (wl0182 (lit c4)) ▸
       at 5 1 (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (wl0610 (lit c4)) ▸
       at 7 1 (Bx2-43 ∷ []) (refl) ▸
       at 10 1 (Bx2-43 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (Bx2-4013 ∷ [])
  b2 = at 5 6 (Bx4-213 ∷ []) (refl) ▸
       at 0 6 (Bx2-4013 ∷ []) (refl) ▸ done

-- nat-SWbc @0214203143: 23 steps
lem-nat-SWbc-at0214203143 : Ws → ⟪ (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-nat-SWbc-at0214203143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ Sw01 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (sym (wp0509 c4)) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (wp0510 c4) ▸
       at 3 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw01 ∷ []) (sym (wp0511 c4)) ▸
       at 3 2 (Toff402 ∷ Sw01 ∷ []) (wp0512 c4) ▸
       at 4 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 5 2 (Toff402 ∷ Sw01 ∷ []) (wp0512 c4) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ Sw01 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ Sw01 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Sw01 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw01 ∷ []) (sym (wp0511 c4)) ▸
       at 7 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 8 2 (Toff214 ∷ Sw01 ∷ []) (wp0510 c4) ▸
       at 9 2 (CCZ124 ∷ Sw01 ∷ []) (sym (wp0509 c4)) ▸
       at 11 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw01 ∷ []) (sym (wp0511 c4)) ▸
       at 11 2 (Toff402 ∷ Sw01 ∷ []) (wp0512 c4) ▸
       at 12 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸ done

  b2 : Chain (CCZ124 ∷ Toff214 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Sw01 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Sw01 ∷ []) (Bx2-4103 ∷ [])
  b2 = at 13 2 (Toff402 ∷ Sw01 ∷ []) (wp0512 c4) ▸
       at 14 2 (CCZ024 ∷ Sw01 ∷ []) (sym (wp0511 c4)) ▸
       at 15 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx4-203 ∷ []) (refl) ▸
       at 5 6 (Bx4-203 ∷ []) (refl) ▸
       at 0 6 (Bx2-4103 ∷ []) (refl) ▸ done

-- nat-SWbc @122441: 23 steps
lem-nat-SWbc-at122441 : Ws → ⟪ (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-nat-SWbc-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ Sw34 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (wp0528 c4) ▸
       at 3 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (wp0530 c4) ▸
       at 4 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 5 2 (Toff204 ∷ Sw34 ∷ []) (wp0530 c4) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ Sw34 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ Sw34 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Sw34 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 7 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 8 2 (Toff023 ∷ Sw34 ∷ []) (wp0528 c4) ▸
       at 9 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 11 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 11 2 (Toff204 ∷ Sw34 ∷ []) (wp0530 c4) ▸
       at 12 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Sw34 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Sw34 ∷ []) (Bx0-2341 ∷ [])
  b2 = at 13 2 (Toff204 ∷ Sw34 ∷ []) (wp0530 c4) ▸
       at 14 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 15 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx2-041 ∷ []) (refl) ▸
       at 5 6 (Bx2-041 ∷ []) (refl) ▸
       at 0 6 (Bx0-2341 ∷ []) (refl) ▸ done

-- F4-K2-I: 1 steps
lem-F4-K2-I : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0655 (lit c4))) ▸ done

-- F4-K2-S0: 1 steps
lem-F4-K2-S0 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0532 c4)) ▸ done

-- F4-K2-S1: 1 steps
lem-F4-K2-S1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0656 (lit c4))) ▸ done

-- F4-K2-S2: 1 steps
lem-F4-K2-S2 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0657 (lit c4))) ▸ done

-- F4-K2-S3: 1 steps
lem-F4-K2-S3 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0658 (lit c4))) ▸ done

-- F4-K2-K0: 1 steps
lem-F4-K2-K0 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0533 c4)) ▸ done

-- F4-K2-K1: 1 steps
lem-F4-K2-K1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0659 (lit c4))) ▸ done

-- F4-K2-K2: 1 steps
lem-F4-K2-K2 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0660 (lit c4))) ▸ done

-- F4-K2-K3: 1 steps
lem-F4-K2-K3 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0661 (lit c4))) ▸ done

-- nat-SWbc @14213243: 23 steps
lem-nat-SWbc-at14213243 : Ws → ⟪ (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-nat-SWbc-at14213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ Sw12 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (wp0552 c4) ▸
       at 3 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (wp0554 c4) ▸
       at 4 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 5 2 (Toff401 ∷ Sw12 ∷ []) (wp0554 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ Sw12 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ Sw12 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Sw12 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 7 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 8 2 (Toff024 ∷ Sw12 ∷ []) (wp0552 c4) ▸
       at 9 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 11 2 (Toff401 ∷ Sw12 ∷ []) (wp0554 c4) ▸
       at 12 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Sw12 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Sw12 ∷ []) (Bx0-4213 ∷ [])
  b2 = at 13 2 (Toff401 ∷ Sw12 ∷ []) (wp0554 c4) ▸
       at 14 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 15 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx4-013 ∷ []) (refl) ▸
       at 5 6 (Bx4-013 ∷ []) (refl) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done

-- F4-K3-I: 1 steps
lem-F4-K3-I : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0687 (lit c4))) ▸ done

-- F4-K3-S0: 1 steps
lem-F4-K3-S0 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0557 c4)) ▸ done

-- F4-K3-S1: 1 steps
lem-F4-K3-S1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0688 (lit c4))) ▸ done

-- F4-K3-S2: 1 steps
lem-F4-K3-S2 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0689 (lit c4))) ▸ done

-- F4-K3-S3: 1 steps
lem-F4-K3-S3 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0690 (lit c4))) ▸ done

-- F4-K3-K0: 1 steps
lem-F4-K3-K0 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0558 c4)) ▸ done

-- F4-K3-K1: 1 steps
lem-F4-K3-K1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0691 (lit c4))) ▸ done

-- F4-K3-K2: 1 steps
lem-F4-K3-K2 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0692 (lit c4))) ▸ done

-- F4-K3-K3: 1 steps
lem-F4-K3-K3 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0693 (lit c4))) ▸ done

-- cQ @0210213443: 7 steps
lem-cQ-at0210213443 : Ws → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at0210213443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CS02 ∷ []) (sym (wp0279 c4)) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS12⁻ ∷ []) (sym (wl0414 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸ done

-- sym-ab @122441: 18 steps
lem-sym-ab-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-sym-ab-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2431 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (wp0214 c4) ▸
       at 4 1 (Bx0-41 ∷ []) (refl) ▸
       at 7 1 (Bx0-41 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ [])
  b1 = at 2 6 (Bx4-031 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (wp0214 c4) ▸
       at 7 1 (Bx0-41 ∷ []) (refl) ▸
       at 10 1 (Bx0-41 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (Bx0-4231 ∷ [])
  b2 = at 5 6 (Bx4-031 ∷ []) (refl) ▸
       at 0 6 (Bx0-4231 ∷ []) (refl) ▸ done

-- cQ @14233241: 7 steps
lem-cQ-at14233241 : Ws → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at14233241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) (wp0198 c4) ▸
       at 4 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 3 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 2 2 (CCZ012 ∷ CS03⁻ ∷ []) (sym (wl0328 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 0 2 (CCZ012 ∷ CS03 ∷ []) (sym (wl0268 (lit c4))) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0198 c4)) ▸ done

-- nat-SWbc @0314213042: 23 steps
lem-nat-SWbc-at0314213042 : Ws → ⟪ (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-nat-SWbc-at0314213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ Sw01 ∷ CCZ034 ∷ Bx3-42 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (wp0676 c4) ▸
       at 3 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 3 2 (Toff413 ∷ Sw01 ∷ []) (wp0678 c4) ▸
       at 4 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 5 2 (Toff413 ∷ Sw01 ∷ []) (wp0678 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ Sw01 ∷ CCZ034 ∷ Bx3-42 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ Sw01 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Sw01 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 7 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 8 2 (Toff304 ∷ Sw01 ∷ []) (wp0676 c4) ▸
       at 9 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 10 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 11 2 (Toff413 ∷ Sw01 ∷ []) (wp0678 c4) ▸
       at 12 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Sw01 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ Sw01 ∷ []) (Bx3-4012 ∷ [])
  b2 = at 13 2 (Toff413 ∷ Sw01 ∷ []) (wp0678 c4) ▸
       at 14 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 15 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx4-312 ∷ []) (refl) ▸
       at 5 6 (Bx4-312 ∷ []) (refl) ▸
       at 0 6 (Bx3-4012 ∷ []) (refl) ▸ done

-- sym-ab @0210233441: 18 steps
lem-sym-ab-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ []) ⟫ʷ
lem-sym-ab-at0210233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-0341 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (wl0756 (lit c4)) ▸
       at 4 1 (Bx2-31 ∷ []) (refl) ▸
       at 7 1 (Bx2-31 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ [])
  b1 = at 2 6 (Bx3-241 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (wl0756 (lit c4)) ▸
       at 7 1 (Bx2-31 ∷ []) (refl) ▸
       at 10 1 (Bx2-31 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (Bx2-3041 ∷ [])
  b2 = at 5 6 (Bx3-241 ∷ []) (refl) ▸
       at 0 6 (Bx2-3041 ∷ []) (refl) ▸ done

-- sym-ab @0213203441: 18 steps
lem-sym-ab-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym-ab-at0213203441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-3041 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (sym (wp0516 c4)) ▸
       at 4 1 (Bx2-01 ∷ []) (refl) ▸
       at 7 1 (Bx2-01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ [])
  b1 = at 2 6 (Bx0-241 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (sym (wp0516 c4)) ▸
       at 7 1 (Bx2-01 ∷ []) (refl) ▸
       at 10 1 (Bx2-01 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (Bx2-0341 ∷ [])
  b2 = at 5 6 (Bx0-241 ∷ []) (refl) ▸
       at 0 6 (Bx2-0341 ∷ []) (refl) ▸ done

-- nat-SWbc @0314203142: 23 steps
lem-nat-SWbc-at0314203142 : Ws → ⟪ (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-nat-SWbc-at0314203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ Sw01 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (wp0695 c4) ▸
       at 3 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (wp0696 c4) ▸
       at 4 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 5 2 (Toff403 ∷ Sw01 ∷ []) (wp0696 c4) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ Sw01 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ Sw01 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Sw01 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 7 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 8 2 (Toff314 ∷ Sw01 ∷ []) (wp0695 c4) ▸
       at 9 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 11 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 11 2 (Toff403 ∷ Sw01 ∷ []) (wp0696 c4) ▸
       at 12 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Sw01 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Sw01 ∷ []) (Bx3-4102 ∷ [])
  b2 = at 13 2 (Toff403 ∷ Sw01 ∷ []) (wp0696 c4) ▸
       at 14 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 15 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx4-302 ∷ []) (refl) ▸
       at 5 6 (Bx4-302 ∷ []) (refl) ▸
       at 0 6 (Bx3-4102 ∷ []) (refl) ▸ done

-- nat-SWbc @0214213043: 23 steps
lem-nat-SWbc-at0214213043 : Ws → ⟪ (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-nat-SWbc-at0214213043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ Sw01 ∷ CCZ024 ∷ Bx2-43 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (sym (wp0511 c4)) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (wp0714 c4) ▸
       at 3 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 2 2 (CCZ124 ∷ Sw01 ∷ []) (sym (wp0509 c4)) ▸
       at 3 2 (Toff412 ∷ Sw01 ∷ []) (wp0715 c4) ▸
       at 4 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 5 2 (Toff412 ∷ Sw01 ∷ []) (wp0715 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ Sw01 ∷ CCZ024 ∷ Bx2-43 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ Sw01 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Sw01 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ124 ∷ Sw01 ∷ []) (sym (wp0509 c4)) ▸
       at 7 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 8 2 (Toff204 ∷ Sw01 ∷ []) (wp0714 c4) ▸
       at 9 2 (CCZ024 ∷ Sw01 ∷ []) (sym (wp0511 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 10 2 (CCZ124 ∷ Sw01 ∷ []) (sym (wp0509 c4)) ▸
       at 11 2 (Toff412 ∷ Sw01 ∷ []) (wp0715 c4) ▸
       at 12 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Sw01 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ Sw01 ∷ []) (Bx2-4013 ∷ [])
  b2 = at 13 2 (Toff412 ∷ Sw01 ∷ []) (wp0715 c4) ▸
       at 14 2 (CCZ124 ∷ Sw01 ∷ []) (sym (wp0509 c4)) ▸
       at 15 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx4-213 ∷ []) (refl) ▸
       at 5 6 (Bx4-213 ∷ []) (refl) ▸
       at 0 6 (Bx2-4013 ∷ []) (refl) ▸ done

-- sym-ab @0214203143: 18 steps
lem-sym-ab-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym-ab-at0214203143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-4013 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl0610 (lit c4))) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (sym (wl0182 (lit c4))) ▸
       at 4 1 (Bx2-03 ∷ []) (refl) ▸
       at 7 1 (Bx2-03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ [])
  b1 = at 2 6 (Bx0-213 ∷ []) (refl) ▸
       at 5 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (sym (wl0610 (lit c4))) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (sym (wl0182 (lit c4))) ▸
       at 7 1 (Bx2-03 ∷ []) (refl) ▸
       at 10 1 (Bx2-03 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (Bx2-0413 ∷ [])
  b2 = at 5 6 (Bx0-213 ∷ []) (refl) ▸
       at 0 6 (Bx2-0413 ∷ []) (refl) ▸ done

-- nat-S @14213243: 31 steps
lem-nat-S-at14213243 : Ws → ⟪ (Sw23 ∷ Sb2-0-41-3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ []) ⟫ʷ
lem-nat-S-at14213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw23 ∷ Sb2-0-41-3 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff304 ∷ Sw23 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (wp0719 c4) ▸
       at 3 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 5 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ Sw23 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Sw23 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Sw23 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Sw23 ∷ [])
  b1 = at 8 1 (CZ03 ∷ []) (refl) ▸
       at 2 7 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ Sw23 ∷ []) (sym (wl0814 (lit c4))) ▸
       at 4 1 (Bx3-02 ∷ []) (refl) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸
       at 2 6 (Bx0-312 ∷ []) (refl) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (wp0719 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 6 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Sw23 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Sw23 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ Toff214 ∷ CS02 ∷ Sw23 ∷ Toff314 ∷ CS03⁻ ∷ Sw23 ∷ [])
  b2 = at 8 1 (CZ03 ∷ []) (refl) ▸
       at 11 1 (CZ03 ∷ []) (refl) ▸
       at 5 7 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ Sw23 ∷ []) (sym (wl0814 (lit c4))) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸
       at 10 1 (Bx3-02 ∷ []) (refl) ▸
       at 5 6 (Bx0-312 ∷ []) (refl) ▸
       at 6 2 (Toff214 ∷ Sw23 ∷ []) (wl0815 (lit c4)) ▸
       at 7 2 (CS02 ∷ Sw23 ∷ []) (sym (wl0816 (lit c4))) ▸ done

  b3 : Chain (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ Toff214 ∷ CS02 ∷ Sw23 ∷ Toff314 ∷ CS03⁻ ∷ Sw23 ∷ []) (Sb3-0-41-2 ∷ [])
  b3 = at 8 2 (Toff214 ∷ Sw23 ∷ []) (wl0815 (lit c4)) ▸
       at 9 2 (CS02⁻ ∷ Sw23 ∷ []) (sym (wl0817 (lit c4))) ▸
       at 10 2 [] (wl0003 (lit c4)) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸
       at 2 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-41-2 ∷ []) (refl) ▸ done

-- nat-SWbc @1331: 23 steps
lem-nat-SWbc-at1331 : Ws → ⟪ (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-nat-SWbc-at1331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ Sw12 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (wl0839 (lit c4)) ▸
       at 3 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (wl0841 (lit c4)) ▸
       at 4 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 5 2 (Toff302 ∷ Sw12 ∷ []) (wl0841 (lit c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ Sw12 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ Sw12 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Sw12 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 7 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 8 2 (Toff013 ∷ Sw12 ∷ []) (wl0839 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 11 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 11 2 (Toff302 ∷ Sw12 ∷ []) (wl0841 (lit c4)) ▸
       at 12 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Sw12 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Sw12 ∷ []) (Bx0-3124 ∷ [])
  b2 = at 13 2 (Toff302 ∷ Sw12 ∷ []) (wl0841 (lit c4)) ▸
       at 14 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 15 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx3-024 ∷ []) (refl) ▸
       at 5 6 (Bx3-024 ∷ []) (refl) ▸
       at 0 6 (Bx0-3124 ∷ []) (refl) ▸ done

-- sym-ab @0312213440: 18 steps
lem-sym-ab-at0312213440 : Ws → ⟪ (Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-sym-ab-at0312213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-2140 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (wp0733 c4) ▸
       at 4 1 (Bx3-10 ∷ []) (refl) ▸
       at 7 1 (Bx3-10 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ [])
  b1 = at 2 6 (Bx1-340 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (wp0733 c4) ▸
       at 7 1 (Bx3-10 ∷ []) (refl) ▸
       at 10 1 (Bx3-10 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (Bx3-1240 ∷ [])
  b2 = at 5 6 (Bx1-340 ∷ []) (refl) ▸
       at 0 6 (Bx3-1240 ∷ []) (refl) ▸ done

-- sym-ab @033440: 18 steps
lem-sym-ab-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-sym-ab-at033440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-1240 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (wp0732 c4) ▸
       at 4 1 (Bx3-20 ∷ []) (refl) ▸
       at 7 1 (Bx3-20 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ [])
  b1 = at 2 6 (Bx2-340 ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (wp0732 c4) ▸
       at 7 1 (Bx3-20 ∷ []) (refl) ▸
       at 10 1 (Bx3-20 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (Bx3-2140 ∷ [])
  b2 = at 5 6 (Bx2-340 ∷ []) (refl) ▸
       at 0 6 (Bx3-2140 ∷ []) (refl) ▸ done

-- nat-SWbc @132132: 23 steps
lem-nat-SWbc-at132132 : Ws → ⟪ (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-nat-SWbc-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ Sw12 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (wl0876 (lit c4)) ▸
       at 3 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (wl0877 (lit c4)) ▸
       at 4 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 5 2 (Toff301 ∷ Sw12 ∷ []) (wl0877 (lit c4)) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ Sw12 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ Sw12 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Sw12 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 7 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 8 2 (Toff023 ∷ Sw12 ∷ []) (wl0876 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 11 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 11 2 (Toff301 ∷ Sw12 ∷ []) (wl0877 (lit c4)) ▸
       at 12 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Sw12 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Sw12 ∷ []) (Bx0-3214 ∷ [])
  b2 = at 13 2 (Toff301 ∷ Sw12 ∷ []) (wl0877 (lit c4)) ▸
       at 14 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 15 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx3-014 ∷ []) (refl) ▸
       at 5 6 (Bx3-014 ∷ []) (refl) ▸
       at 0 6 (Bx0-3214 ∷ []) (refl) ▸ done
