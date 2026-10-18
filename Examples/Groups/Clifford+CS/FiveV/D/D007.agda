{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D007 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0003 ; wl0156 ; wl0157 ; wl0158 ; wl0159 ; wl0160 ; wl0161 ; wl0162 ; wl0175 ; wl0179 ; wl0184 ; wl0207 ; wl0225 ; wl0226 ; wl0227 ; wl0228 ; wl0229 ; wl0230 ; wl0231 ; wl0254 ; wl0257 ; wl0258 ; wl0259 ; wl0260 ; wl0261 ; wl0262 ; wl0263 ; wl0268 ; wl0270 ; wl0300 ; wl0305 ; wl0306 ; wl0312 ; wl0315 ; wl0316 ; wl0317 ; wl0318 ; wl0319 ; wl0320 ; wl0321 ; wl0322 ; wl0327 ; wl0328 ; wl0338 ; wl0339 ; wl0340 ; wl0341 ; wl0342 ; wl0348 ; wl0414 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0420 ; wl0421 ; wl0424 ; wl0490 ; wl0491 ; wl0492 ; wl0508 ; wl0572 ; wl0573 ; wl0613 ; wl0645 ; wl0670 ; wl0682 ; wl0683 ; wl0684 ; wl0685 ; wl0686 ; wl0687 ; wl0688 ; wl0689 ; wl0690 ; wl0691 ; wl0692 ; wl0693 ; wl0694 ; wl0695 ; wl0696 ; wl0697 ; wl0698 ; wl0699 ; wl0700 ; wl0701 ; wl0702 ; wl0703 ; wl0704 ; wl0705 ; wl0706 ; wl0707 ; wl0708 ; wl0709 ; wl0710 ; wl0711 ; wl0712 ; wl0713 ; wl0714 ; wl0715 ; wl0716 ; wl0717 ; wl0718 ; wl0719 ; wl0720 ; wl0721 ; wl0722 ; wl0723 ; wl0724 ; wl0725 ; wl0726 ; wl0727 ; wl0728 ; wl0729 ; wl0730 ; wl0731 ; wl0732 ; wl0733 ; wl0734 ; wl0735 ; wl0736 ; wl0737 ; wl0738 ; wp0001 ; wp0003 ; wp0004 ; wp0005 ; wp0006 ; wp0007 ; wp0077 ; wp0078 ; wp0079 ; wp0080 ; wp0083 ; wp0084 ; wp0117 ; wp0118 ; wp0119 ; wp0120 ; wp0135 ; wp0162 ; wp0180 ; wp0194 ; wp0196 ; wp0198 ; wp0212 ; wp0213 ; wp0214 ; wp0255 ; wp0279 ; wp0299 ; wp0305 ; wp0352 ; wp0357 ; wp0420 ; wp0421 ; wp0445 ; wp0497 ; wp0502 ; wp0519 ; wp0525 ; wp0541 ; wp0543 ; wp0547 ; wp0555 ; wp0556 ; wp0557 ; wp0558 ; wp0559 ; wp0560 ; wp0561 ; wp0562 ; wp0563 ; wp0564 ; wp0565 ; wp0566 ; wp0567 ; wp0568 ; wp0569 ; wp0570 ; wp0571 ; wp0572 ; wp0573 ; wp0574 ; wp0575 ; wp0576 ; wp0577 ; wp0578 ; wp0579 ; wp0580 ; wp0581 ; wp0582 ; wp0583 ; wp0584 ; wp0585 ; wp0586 ; wp0587 ; wp0588 ; wp0589 ; wp0590 ; wp0591 ; wp0592 ; wp0593 ; wp0594 ; wp0595 ; wp0596 ; wp0597 ; wp0598 ; wp0599 ; wp0600 ; wp0601 ; wp0602 ; wp0603 ; wp0604 ; wp0605 ; wp0606 ; wp0607 ; wp0608 ; wp0609 ; wp0610 ; wp0611 ; wp0612 ; wp0613 ; wp0614 ; wp0615 ; wp0616 ; wp0617 ; wp0618 ; wp0619 ; wp0620 ; wp0621 ; wp0622 ; wp0623 ; wp0624 ; wp0625 ; wp0626 ; wp0627 ; wp0628 ; wp0629 ; wp0630 ; wp0631 ; wp0632 ; wp0633 ; wp0634 ; wp0635 ; wp0636 ; wp0637 ; wp0638)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at0210243143 ; lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box-tQ-at0210243143 ; lem-box-tQ-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-box-tQ-at1441)
open import Examples.Groups.Clifford+CS.FiveV.D.D003 using (lem-box-tQ-at233442 ; lem-cQ-at233442 ; lem-sym-ab-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-box-cP-at3443)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-CSdu-box-2-at243243 ; lem-Su-box-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-CSdu-box-2-at0210243143 ; lem-Kdu-box-at0210243143 ; lem-Kdu-box-at243243 ; lem-Ku-box-at0210243143 ; lem-Ku-box-at243243 ; lem-SWbc-box-at14213243 ; lem-Su-box-at0210243143 ; lem-box-cP-at0210233441 ; lem-box-perm-1423-at0210243143 ; lem-nat-SWbc-at14213243)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CSd12-TOFF034 ; lem-comm-CX04-CCZ123 ; lem-comm-CX14-CCZ023 ; lem-comm-CZ12-CCZ034 ; lem-comm-CZ12-TOFF034)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CSd13-TOFF024 ; lem-comm-CSd23-TOFF014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX21-CCZ034 ; lem-comm-CZ24-CCZ013 ; lem-comm-TOFF013-CSd24 ; lem-comm-TOFF023-CSd14 ; lem-comm-TOFF024-CSd13)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS13-TOFF024 ; lem-comm-CX42-CCZ013 ; lem-comm-TOFF034-CSd12)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CCZ013-CK42 ; lem-comm-CCZ023-CK41 ; lem-comm-CK42-CCZ013 ; lem-comm-CK42-TOFF013 ; lem-comm-CS13-TOFF204 ; lem-comm-CS23-TOFF014 ; lem-comm-CSd13-TOFF204 ; lem-comm-CZ13-TOFF024 ; lem-comm-SWAP14-BOX⟨2·03⟩ ; lem-comm-SWAP23-BOX⟨0·41⟩ ; lem-comm-SWAP24-BOX⟨0·13⟩ ; lem-comm-TOFF023-CK41 ; lem-comm-TOFF213-CK40 ; lem-comm-TOFF213-CSd04)
-- sym-bc @14213243: 2 steps
lem-sym-bc-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym-bc-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at14213243 c4)) ▸
       at 0 3 (Bx0-4213 ∷ []) (lem-nat-SWbc-at14213243 c4) ▸ done


-- cQ @143143: 7 steps
lem-cQ-at143143 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at143143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 4 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 3 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS02⁻ ∷ []) (sym (wl0342 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS02 ∷ []) (sym (wl0225 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸ done


-- box-tQ @143143: 13 steps
lem-box-tQ-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at143143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4213 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0180 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0180 c4)) ▸
       at 0 2 (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) (wp0083 c4) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at143143 c4) ▸
       at 2 4 (Toff024 ∷ []) (wp0084 c4) ▸ done


-- tP @143143: 7 steps
lem-tP-at143143 : Ws → ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-tP-at143143 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0078 c4)) ▸
       at 3 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0226 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at143143 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff013 ∷ []) (wl0226 (lit c4)) ▸
       at 1 3 (Toff024 ∷ []) (wp0078 c4) ▸ done


-- P-box @143143: 8 steps
lem-P-box-at143143 : Ws → ⟪ (Toff013 ∷ Bx0-4213 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-P-box-at143143 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Bx0-4213 ∷ Toff013 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at143143 c4) ▸
       at 0 2 (Toff024 ∷ Toff013 ∷ []) (sym (lem-tP-at143143 c4)) ▸
       at 1 2 (CCZ013 ∷ CZ13 ∷ Toff013 ∷ []) (sym (wl0682 (lit c4))) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (sym (lem-tP-at143143 c4)) ▸
       at 4 3 (CCZ013 ∷ CZ13 ∷ []) (sym (wl0683 (lit c4))) ▸
       at 2 2 (Toff024 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF024 (lit c4)) ▸
       at 3 3 (CCZ013 ∷ []) (sym (wl0684 (lit c4))) ▸
       at 0 4 (Bx0-4213 ∷ []) (sym (lem-box-tQ-at143143 c4)) ▸ done


-- VPQ @143143: 14 steps
lem-VPQ-at143143 : Ws → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at143143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (sym (wp0079 c4)) ▸
       at 4 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (sym (wl0227 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 2 2 (CS13⁻ ∷ Toff024 ∷ []) (lem-comm-TOFF024-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 2 (CS13⁻ ∷ CS24⁻ ∷ []) (sym (wl0228 (lit c4))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at143143 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS24⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS24⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff013 ∷ CCZ013 ∷ []) (wl0227 (lit c4)) ▸
       at 2 4 (Toff024 ∷ CCZ024 ∷ []) (wp0079 c4) ▸ done


-- QVQ @143143: 3 steps
lem-QVQ-at143143 : Ws → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at143143 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Toff013 ∷ Toff013 ∷ []) (sym (wl0229 (lit c4))) ▸
       at 1 4 (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at143143 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done


-- box-cP @143143: 12 steps
lem-box-cP-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at143143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4213 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0180 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0180 c4)) ▸
       at 2 4 (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at143143 c4) ▸
       at 1 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at143143 c4) ▸
       at 2 2 [] (wp0080 c4) ▸ done


-- pairs @143143: 4 steps
lem-pairs-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-pairs-at143143 c4 = run b0
  where
  b0 : Chain (Bx0-4213 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 1 (Toff013 ∷ Bx0-4213 ∷ Toff013 ∷ []) (sym (lem-P-box-at143143 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at143143 c4) ▸
       at 4 2 [] (wl0229 (lit c4)) ▸
       at 0 4 (Bx0-1342 ∷ []) (sym (lem-box-tQ-at233442 c4)) ▸ done


-- box-perm-1423 @243243: 3 steps
lem-box-perm-1423-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-box-perm-1423-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸
       at 0 1 (Bx0-4213 ∷ []) (lem-sym-bc-at14213243 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-pairs-at143143 c4) ▸ done


-- tP @233442: 7 steps
lem-tP-at233442 : Ws → ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ
lem-tP-at233442 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0226 (lit c4))) ▸
       at 3 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0078 c4)) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at233442 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff024 ∷ []) (wp0078 c4) ▸
       at 1 3 (Toff013 ∷ []) (wl0226 (lit c4)) ▸ done


-- VPQ @233442: 14 steps
lem-VPQ-at233442 : Ws → ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at233442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (sym (wl0227 (lit c4))) ▸
       at 4 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (sym (wp0079 c4)) ▸
       at 3 2 (CS24⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 1 2 (CS24⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS24⁻ ∷ CS13⁻ ∷ []) (wl0228 (lit c4)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at233442 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS13⁻ ∷ []) (sym (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS13⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 0 4 (Toff024 ∷ CCZ024 ∷ []) (wp0079 c4) ▸
       at 2 4 (Toff013 ∷ CCZ013 ∷ []) (wl0227 (lit c4)) ▸ done


-- QVQ @233442: 3 steps
lem-QVQ-at233442 : Ws → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at233442 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0080 c4)) ▸
       at 1 4 (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at233442 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done


-- box-cP @233442: 12 steps
lem-box-cP-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at233442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1342 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 2 4 (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at233442 c4) ▸
       at 1 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at233442 c4) ▸
       at 2 2 [] (wl0229 (lit c4)) ▸ done


-- F4-K2-CS1: 19 steps
lem-F4-K2-CS1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ013 ∷ X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 3 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at233442 c4) ▸
       at 2 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 1 2 (CCZ013 ∷ CK42 ∷ []) (lem-comm-CK42-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸ done

  b1 : Chain (CCZ013 ∷ X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0555 c4)) ▸
       at 4 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 3 2 (CCZ013 ∷ CK42 ∷ []) (lem-comm-CK42-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 3 4 (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0555 c4)) ▸
       at 0 4 (Bx0-1342 ∷ []) (sym (lem-box-cP-at233442 c4)) ▸
       at 0 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1423-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0685 (lit c4))) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4-K2-CS2: 17 steps
lem-F4-K2-CS2 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0556 c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 2 2 (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 (lit c4)) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b1 = at 2 4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0556 c4)) ▸
       at 5 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 2 (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0686 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


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


-- CXbc-box @0210243143: 17 steps
lem-CXbc-box-at0210243143 : Ws → ⟪ (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX41 ∷ CCZ234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CCZ123 ∷ CX04 ∷ CS03 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ CX41 ∷ []) (wp0502 c4) ▸
       at 1 2 (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) (sym (wl0694 (lit c4))) ▸
       at 3 2 (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp0559 c4) ▸
       at 2 2 (Toff204 ∷ CX41 ∷ []) (wp0502 c4) ▸
       at 5 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 9 2 (CCZ123 ∷ CS03 ∷ []) (sym (wl0490 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX41 ∷ CCZ234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CCZ123 ∷ CX04 ∷ CS03 ∷ CX41 ∷ []) (Bx2-0413 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS34⁻ ∷ []) (sym (wl0491 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS34 ∷ []) (sym (wl0492 (lit c4))) ▸
       at 6 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 4 2 (CCZ123 ∷ CCZ234 ∷ []) (sym (wl0508 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) (sym (wl0694 (lit c4))) ▸
       at 4 3 (CX41 ∷ []) (wl0695 (lit c4)) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done

  b2 : Chain (Bx2-0413 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ [])
  b2 = at 1 3 (CCZ034 ∷ []) (sym (wp0560 c4)) ▸ done


-- CXcb-box @0210243143: 18 steps
lem-CXcb-box-at0210243143 : Ws → ⟪ (CX14 ∷ Bx2-0413 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx2-0413 ∷ CX14 ∷ []) (Toff204 ∷ CCZ123 ∷ CX14 ∷ Toff201 ∷ CS13 ∷ CX01 ∷ Toff204 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ CX14 ∷ Toff201 ∷ []) (wp0561 c4) ▸
       at 2 2 (CCZ123 ∷ Toff201 ∷ CCZ013 ∷ []) (sym (wl0696 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX14 ∷ []) (sym (wl0424 (lit c4))) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 8 2 (Toff204 ∷ CS03 ∷ []) (wp0562 c4) ▸
       at 7 2 (Toff204 ∷ CX01 ∷ []) (wp0497 c4) ▸
       at 6 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ CX14 ∷ Toff201 ∷ CS13 ∷ CX01 ∷ Toff204 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ CX14 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ [])
  b1 = at 5 2 (Toff204 ∷ CX01 ∷ []) (wp0497 c4) ▸
       at 4 2 (Toff204 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF204 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 3 2 (Toff204 ∷ Toff201 ∷ []) (wp0563 c4) ▸
       at 2 2 (Toff204 ∷ CX14 ∷ Toff201 ∷ []) (wp0561 c4) ▸
       at 3 3 (CX14 ∷ []) (wp0564 c4) ▸
       at 4 2 (CCZ123 ∷ CCZ013 ∷ []) (wl0327 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ CX14 ∷ []) (sym (wl0424 (lit c4))) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wp0565 c4)) ▸ done


-- SWbc-box @0210243143: 11 steps
lem-SWbc-box-at0210243143 : Ws → ⟪ (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-SWbc-box-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) (CX41 ∷ Bx2-0413 ∷ CX41 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 2 3 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0210243143 c4) ▸
       at 3 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0566 c4) ▸
       at 1 3 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-CXcb-box-at0210243143 c4) ▸
       at 4 2 (CX41 ∷ CCZ034 ∷ []) (wp0357 c4) ▸
       at 3 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0567 c4) ▸
       at 2 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0567 c4) ▸ done

  b1 : Chain (CX41 ∷ Bx2-0413 ∷ CX41 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (Bx2-0413 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (wp0568 c4) ▸
       at 0 3 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0210243143 c4) ▸
       at 1 2 [] (wp0007 c4) ▸ done


-- nat-SWbc @0210243143: 23 steps
lem-nat-SWbc-at0210243143 : Ws → ⟪ (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-nat-SWbc-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ Sw14 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 1 2 (Toff201 ∷ Sw14 ∷ []) (wp0569 c4) ▸
       at 3 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 3 2 (Toff024 ∷ Sw14 ∷ []) (wp0570 c4) ▸
       at 4 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4)) ▸
       at 5 2 (Toff024 ∷ Sw14 ∷ []) (wp0570 c4) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ Sw14 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Sw14 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Sw14 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 7 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4)) ▸
       at 8 2 (Toff201 ∷ Sw14 ∷ []) (wp0569 c4) ▸
       at 9 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 11 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 11 2 (Toff024 ∷ Sw14 ∷ []) (wp0570 c4) ▸
       at 12 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Sw14 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Sw14 ∷ []) (Bx2-0143 ∷ [])
  b2 = at 13 2 (Toff024 ∷ Sw14 ∷ []) (wp0570 c4) ▸
       at 14 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 15 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx0-243 ∷ []) (refl) ▸
       at 5 6 (Bx0-243 ∷ []) (refl) ▸
       at 0 6 (Bx2-0143 ∷ []) (refl) ▸ done


-- sym-bc @0210243143: 2 steps
lem-sym-bc-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-sym-bc-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0210243143 c4)) ▸
       at 0 3 (Bx2-0143 ∷ []) (lem-nat-SWbc-at0210243143 c4) ▸ done


-- box-perm-1324 @0210243143: 1 steps
lem-box-perm-1324-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-box-perm-1324-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 1 (Bx2-0143 ∷ []) (lem-sym-bc-at0210243143 c4) ▸ done


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


-- tP @0210213443: 7 steps
lem-tP-at0210213443 : Ws → ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ
lem-tP-at0210213443 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (sym (wl0416 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (sym (wl0417 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at0210213443 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff234 ∷ []) (wl0417 (lit c4)) ▸
       at 1 3 (Toff201 ∷ []) (wl0416 (lit c4)) ▸ done


-- VPQ @0210213443: 14 steps
lem-VPQ-at0210213443 : Ws → ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at0210213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (sym (wl0418 (lit c4))) ▸
       at 4 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (sym (wl0419 (lit c4))) ▸
       at 3 2 (CS34⁻ ∷ S2⁻ ∷ []) (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS)) ▸
       at 2 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S2 ∷ []) (c₃ (S ↑ ↑) (CS • CS • CS)) ▸
       at 0 2 (CS34⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((CS • CS • CS) ↑)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0210213443 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S)) ▸
       at 2 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸
       at 3 2 (S2⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S • S • S)) ▸
       at 0 4 (Toff234 ∷ CCZ234 ∷ []) (wl0419 (lit c4)) ▸
       at 2 4 (Toff201 ∷ CCZ012 ∷ []) (wl0418 (lit c4)) ▸ done


-- QVQ @0210213443: 3 steps
lem-QVQ-at0210213443 : Ws → ⟪ (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-QVQ-at0210213443 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ [])
  b0 = at 0 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 1 4 (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at0210213443 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done


-- box-cP @0210213443: 12 steps
lem-box-cP-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-box-cP-at0210213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0143 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 2 4 (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-QVQ-at0210213443 c4) ▸
       at 1 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0210213443 c4) ▸
       at 2 2 [] (wl0421 (lit c4)) ▸ done


-- F4-K3-CS0: 19 steps
lem-F4-K3-CS0 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (Bx2-0143 ∷ []) (lem-box-perm-1324-at0210243143 c4) ▸
       at 3 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0210213443 c4) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 0 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸ done

  b1 : Chain (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0697 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 4 (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0697 (lit c4))) ▸
       at 0 4 (Bx2-0143 ∷ []) (sym (lem-box-cP-at0210213443 c4)) ▸
       at 0 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1324-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0571 c4)) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- CXbc-box @243243: 17 steps
lem-CXbc-box-at243243 : Ws → ⟪ (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX42 ∷ CCZ034 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CCZ023 ∷ CX14 ∷ CS13 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (Toff014 ∷ CX42 ∷ []) (wp0547 c4) ▸
       at 1 2 (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) (sym (wp0572 c4)) ▸
       at 3 2 (Toff014 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0573 c4) ▸
       at 2 2 (Toff014 ∷ CX42 ∷ []) (wp0547 c4) ▸
       at 5 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS13 ∷ []) (sym (wl0670 (lit c4))) ▸
       at 8 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX42 ∷ CCZ034 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CCZ023 ∷ CX14 ∷ CS13 ∷ CX42 ∷ []) (Bx0-1423 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS34⁻ ∷ []) (sym (wp0574 c4)) ▸
       at 6 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS34 ∷ []) (sym (wp0543 c4)) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ CCZ034 ∷ []) (sym (wp0575 c4)) ▸
       at 3 2 (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) (sym (wp0572 c4)) ▸
       at 4 3 (CX42 ∷ []) (wp0576 c4) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸ done

  b2 : Chain (Bx0-1423 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wl0312 (lit c4))) ▸ done


-- CXcb-box @243243: 18 steps
lem-CXcb-box-at243243 : Ws → ⟪ (CX24 ∷ Bx0-1423 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx0-1423 ∷ CX24 ∷ []) (Toff014 ∷ CCZ023 ∷ CX24 ∷ Toff012 ∷ CS23 ∷ CX12 ∷ Toff014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ023 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (Toff014 ∷ CX24 ∷ Toff012 ∷ []) (wp0577 c4) ▸
       at 2 2 (CCZ023 ∷ Toff012 ∷ CCZ123 ∷ []) (sym (wl0699 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX24 ∷ []) (sym (wp0578 c4)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (Toff014 ∷ CS13 ∷ []) (wp0579 c4) ▸
       at 7 2 (Toff014 ∷ CX12 ∷ []) (wp0541 c4) ▸
       at 6 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CX24 ∷ Toff012 ∷ CS23 ∷ CX12 ∷ Toff014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ023 ∷ CX24 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ [])
  b1 = at 5 2 (Toff014 ∷ CX12 ∷ []) (wp0541 c4) ▸
       at 4 2 (Toff014 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff014 ∷ Toff012 ∷ []) (wp0580 c4) ▸
       at 2 2 (Toff014 ∷ CX24 ∷ Toff012 ∷ []) (wp0577 c4) ▸
       at 3 3 (CX24 ∷ []) (wp0581 c4) ▸
       at 4 2 (CCZ023 ∷ CCZ123 ∷ []) (sym (wl0613 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX24 ∷ []) (sym (wp0578 c4)) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0315 (lit c4))) ▸ done


-- SWbc-box @243243: 11 steps
lem-SWbc-box-at243243 : Ws → ⟪ (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-SWbc-box-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) (CX42 ∷ Bx0-1423 ∷ CX42 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 4 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 2 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CXbc-box-at243243 c4) ▸
       at 3 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0317 (lit c4)) ▸
       at 1 3 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-CXcb-box-at243243 c4) ▸
       at 4 2 (CX42 ∷ CCZ134 ∷ []) (wl0318 (lit c4)) ▸
       at 3 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0319 (lit c4)) ▸
       at 2 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0319 (lit c4)) ▸ done

  b1 : Chain (CX42 ∷ Bx0-1423 ∷ CX42 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (Bx0-1423 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wl0320 (lit c4)) ▸
       at 0 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CXbc-box-at243243 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done


-- nat-SWbc @243243: 23 steps
lem-nat-SWbc-at243243 : Ws → ⟪ (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-nat-SWbc-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ Sw24 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw24 ∷ []) (sym (wp0582 c4)) ▸
       at 1 2 (Toff012 ∷ Sw24 ∷ []) (wp0583 c4) ▸
       at 3 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw24 ∷ []) (sym (wp0584 c4)) ▸
       at 3 2 (Toff104 ∷ Sw24 ∷ []) (wp0585 c4) ▸
       at 4 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4)) ▸
       at 5 2 (Toff104 ∷ Sw24 ∷ []) (wp0585 c4) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ Sw24 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ Sw24 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Sw24 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw24 ∷ []) (sym (wp0584 c4)) ▸
       at 7 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4)) ▸
       at 8 2 (Toff012 ∷ Sw24 ∷ []) (wp0583 c4) ▸
       at 9 2 (CCZ012 ∷ Sw24 ∷ []) (sym (wp0582 c4)) ▸
       at 11 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw24 ∷ []) (sym (wp0584 c4)) ▸
       at 11 2 (Toff104 ∷ Sw24 ∷ []) (wp0585 c4) ▸
       at 12 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Sw24 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Sw24 ∷ []) (Bx0-1243 ∷ [])
  b2 = at 13 2 (Toff104 ∷ Sw24 ∷ []) (wp0585 c4) ▸
       at 14 2 (CCZ014 ∷ Sw24 ∷ []) (sym (wp0584 c4)) ▸
       at 15 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4)) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx1-043 ∷ []) (refl) ▸
       at 5 6 (Bx1-043 ∷ []) (refl) ▸
       at 0 6 (Bx0-1243 ∷ []) (refl) ▸ done


-- sym-bc @243243: 2 steps
lem-sym-bc-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-sym-bc-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at243243 c4)) ▸
       at 0 3 (Bx0-1243 ∷ []) (lem-nat-SWbc-at243243 c4) ▸ done


-- box-perm-1324 @243243: 1 steps
lem-box-perm-1324-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-box-perm-1324-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-sym-bc-at243243 c4) ▸ done


-- F4-K3-CS1: 19 steps
lem-F4-K3-CS1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 3 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 0 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸ done

  b1 : Chain (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0586 c4)) ▸
       at 4 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 4 (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0586 c4)) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸
       at 0 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0700 (lit c4))) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


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


-- CXbc-box @1441: 17 steps
lem-CXbc-box-at1441 : Ws → ⟪ (CX23 ∷ Bx0-4231 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at1441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx0-4231 ∷ CX23 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX23 ∷ CCZ012 ∷ CS12 ∷ CX42 ∷ CS12⁻ ∷ CCZ013 ∷ CX42 ∷ CS14 ∷ CX23 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at1441 c4) ▸
       at 0 2 (Toff024 ∷ CX23 ∷ []) (wp0525 c4) ▸
       at 1 2 (CCZ013 ∷ CX23 ∷ CCZ012 ∷ []) (sym (wl0701 (lit c4))) ▸
       at 3 2 (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp0587 c4) ▸
       at 2 2 (Toff024 ∷ CX23 ∷ []) (wp0525 c4) ▸
       at 5 1 (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (wl0702 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 8 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX23 ∷ CCZ012 ∷ CS12 ∷ CX42 ∷ CS12⁻ ∷ CCZ013 ∷ CX42 ∷ CS14 ∷ CX23 ∷ []) (Bx0-4231 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS12⁻ ∷ []) (sym (wl0703 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CS12 ∷ []) (sym (wl0645 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0702 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CCZ012 ∷ []) (wl0704 (lit c4)) ▸
       at 3 2 (CCZ013 ∷ CX23 ∷ CCZ012 ∷ []) (sym (wl0701 (lit c4))) ▸
       at 4 3 (CX23 ∷ []) (wl0705 (lit c4)) ▸
       at 0 4 (Bx0-4231 ∷ []) (sym (lem-box-tQ-at1441 c4)) ▸ done

  b2 : Chain (Bx0-4231 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ []) (Bx0-4231 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wl0257 (lit c4))) ▸ done


-- CXcb-box @1441: 18 steps
lem-CXcb-box-at1441 : Ws → ⟪ (CX32 ∷ Bx0-4231 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at1441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX32 ∷ Bx0-4231 ∷ CX32 ∷ []) (Toff024 ∷ CCZ013 ∷ CX32 ∷ Toff034 ∷ CS13 ∷ CX43 ∷ Toff024 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ CCZ013 ∷ CX32 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at1441 c4) ▸
       at 0 2 (Toff024 ∷ CX32 ∷ Toff034 ∷ []) (wp0588 c4) ▸
       at 2 2 (CCZ013 ∷ Toff034 ∷ CCZ134 ∷ []) (sym (wp0589 c4)) ▸
       at 1 2 (CCZ013 ∷ CX32 ∷ []) (sym (wl0706 (lit c4))) ▸
       at 4 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0707 (lit c4)) ▸
       at 8 2 (Toff024 ∷ CS14 ∷ []) (wp0590 c4) ▸
       at 7 2 (Toff024 ∷ CX43 ∷ []) (wp0519 c4) ▸
       at 6 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CX32 ∷ Toff034 ∷ CS13 ∷ CX43 ∷ Toff024 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ CCZ013 ∷ CX32 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ [])
  b1 = at 5 2 (Toff024 ∷ CX43 ∷ []) (wp0519 c4) ▸
       at 4 2 (Toff024 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF024 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0707 (lit c4))) ▸
       at 3 2 (Toff024 ∷ Toff034 ∷ []) (sym (wp0591 c4)) ▸
       at 2 2 (Toff024 ∷ CX32 ∷ Toff034 ∷ []) (wp0588 c4) ▸
       at 3 3 (CX32 ∷ []) (wp0592 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ134 ∷ []) (sym (wp0593 c4)) ▸
       at 3 2 (CCZ013 ∷ CX32 ∷ []) (sym (wl0706 (lit c4))) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ []) (Bx0-4231 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-4231 ∷ []) (sym (lem-box-tQ-at1441 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wl0254 (lit c4))) ▸ done


-- SWbc-box @1441: 11 steps
lem-SWbc-box-at1441 : Ws → ⟪ (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-SWbc-box-at1441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) (CX23 ∷ Bx0-4231 ∷ CX23 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 4 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 2 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1441 c4) ▸
       at 3 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl0259 (lit c4)) ▸
       at 1 3 (Bx0-4231 ∷ CCZ134 ∷ []) (lem-CXcb-box-at1441 c4) ▸
       at 4 2 (CX23 ∷ CCZ124 ∷ []) (wl0260 (lit c4)) ▸
       at 3 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0261 (lit c4)) ▸
       at 2 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0261 (lit c4)) ▸ done

  b1 : Chain (CX23 ∷ Bx0-4231 ∷ CX23 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) (Bx0-4231 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wl0262 (lit c4)) ▸
       at 0 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1441 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done


-- nat-SWbc @1441: 23 steps
lem-nat-SWbc-at1441 : Ws → ⟪ (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-nat-SWbc-at1441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ Sw23 ∷ CCZ034 ∷ Bx0-41 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (wp0595 c4) ▸
       at 3 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (wp0597 c4) ▸
       at 4 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4)) ▸
       at 5 2 (Toff402 ∷ Sw23 ∷ []) (wp0597 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ Sw23 ∷ CCZ034 ∷ Bx0-41 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Sw23 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 7 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4)) ▸
       at 8 2 (Toff034 ∷ Sw23 ∷ []) (wp0595 c4) ▸
       at 9 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 11 2 (Toff402 ∷ Sw23 ∷ []) (wp0597 c4) ▸
       at 12 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Sw23 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ Sw23 ∷ []) (Bx0-4321 ∷ [])
  b2 = at 13 2 (Toff402 ∷ Sw23 ∷ []) (wp0597 c4) ▸
       at 14 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 15 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4)) ▸
       at 16 2 [] (wl0003 (lit c4)) ▸
       at 2 6 (Bx4-021 ∷ []) (refl) ▸
       at 5 6 (Bx4-021 ∷ []) (refl) ▸
       at 0 6 (Bx0-4321 ∷ []) (refl) ▸ done


-- sym-bc @1441: 2 steps
lem-sym-bc-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-sym-bc-at1441 c4 = run b0
  where
  b0 : Chain (Bx0-4231 ∷ []) (Bx0-4321 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at1441 c4)) ▸
       at 0 3 (Bx0-4321 ∷ []) (lem-nat-SWbc-at1441 c4) ▸ done


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


-- box-tQ @14233241: 13 steps
lem-box-tQ-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at14233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4321 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 0 2 (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) (wp0118 c4) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at14233241 c4) ▸
       at 2 4 (Toff034 ∷ []) (wp0119 c4) ▸ done


-- tP @14233241: 7 steps
lem-tP-at14233241 : Ws → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at14233241 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (sym (wp0004 c4)) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0156 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at14233241 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff012 ∷ []) (wl0156 (lit c4)) ▸
       at 1 3 (Toff034 ∷ []) (wp0004 c4) ▸ done


-- P-box @14233241: 8 steps
lem-P-box-at14233241 : Ws → ⟪ (Toff012 ∷ Bx0-4321 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-P-box-at14233241 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-4321 ∷ Toff012 ∷ []) (Bx0-4321 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233241 c4) ▸
       at 0 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at14233241 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (sym (wl0338 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at14233241 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ12 ∷ []) (sym (wl0339 (lit c4))) ▸
       at 2 2 (Toff034 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF034 (lit c4)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wl0340 (lit c4))) ▸
       at 0 4 (Bx0-4321 ∷ []) (sym (lem-box-tQ-at14233241 c4)) ▸ done


-- VPQ @14233241: 14 steps
lem-VPQ-at14233241 : Ws → ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at14233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (sym (wp0005 c4)) ▸
       at 4 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (sym (wl0158 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (CS • CS • CS)) ▸
       at 2 2 (CS12⁻ ∷ Toff034 ∷ []) (lem-comm-TOFF034-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S0 ∷ []) (c₁ (S) (CS • CS • CS)) ▸
       at 0 2 (CS12⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at14233241 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS34⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑ ↑))) ▸
       at 2 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 3 2 (S0⁻ ∷ CS34⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))) ▸
       at 0 4 (Toff012 ∷ CCZ012 ∷ []) (wl0158 (lit c4)) ▸
       at 2 4 (Toff034 ∷ CCZ034 ∷ []) (wp0005 c4) ▸ done


-- QVQ @14233241: 3 steps
lem-QVQ-at14233241 : Ws → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at14233241 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 1 4 (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at14233241 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done


-- box-cP @14233241: 12 steps
lem-box-cP-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at14233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4321 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 2 4 (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at14233241 c4) ▸
       at 1 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at14233241 c4) ▸
       at 2 2 [] (wp0006 c4) ▸ done


-- cQ @12213443: 7 steps
lem-cQ-at12213443 : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at12213443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0270 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS01⁻ ∷ []) (sym (wp0120 c4)) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0270 (lit c4))) ▸ done


-- box-tQ @12213443: 13 steps
lem-box-tQ-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at12213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2143 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 0 2 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (wl0160 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at12213443 c4) ▸
       at 2 4 (Toff012 ∷ []) (wl0161 (lit c4)) ▸ done


-- pairs @14233241: 4 steps
lem-pairs-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-pairs-at14233241 c4 = run b0
  where
  b0 : Chain (Bx0-4321 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Toff012 ∷ Bx0-4321 ∷ Toff012 ∷ []) (sym (lem-P-box-at14233241 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at14233241 c4) ▸
       at 4 2 [] (wl0162 (lit c4)) ▸
       at 0 4 (Bx0-2143 ∷ []) (sym (lem-box-tQ-at12213443 c4)) ▸ done


-- box-perm-1423 @122441: 3 steps
lem-box-perm-1423-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-box-perm-1423-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Bx0-4231 ∷ []) (lem-sym-ab-at122441 c4) ▸
       at 0 1 (Bx0-4321 ∷ []) (lem-sym-bc-at1441 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-pairs-at14233241 c4) ▸ done


-- tP @12213443: 7 steps
lem-tP-at12213443 : Ws → ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-tP-at12213443 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0156 (lit c4))) ▸
       at 3 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (sym (wp0004 c4)) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at12213443 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff034 ∷ []) (wp0004 c4) ▸
       at 1 3 (Toff012 ∷ []) (wl0156 (lit c4)) ▸ done


-- VPQ @12213443: 14 steps
lem-VPQ-at12213443 : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at12213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (sym (wl0158 (lit c4))) ▸
       at 4 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (sym (wp0005 c4)) ▸
       at 3 2 (CS34⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑)) ▸
       at 2 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑ ↑)) ▸
       at 0 2 (CS34⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (CS • CS • CS)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at12213443 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS12⁻ ∷ []) (sym (c₁ (S) (CS • CS • CS))) ▸
       at 2 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS12⁻ ∷ []) (sym (c₁ (S • S • S) (CS • CS • CS))) ▸
       at 0 4 (Toff034 ∷ CCZ034 ∷ []) (wp0005 c4) ▸
       at 2 4 (Toff012 ∷ CCZ012 ∷ []) (wl0158 (lit c4)) ▸ done


-- QVQ @12213443: 3 steps
lem-QVQ-at12213443 : Ws → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ-at12213443 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 0 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 1 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at12213443 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done


-- box-cP @12213443: 12 steps
lem-box-cP-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP-at12213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2143 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 2 4 (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ-at12213443 c4) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at12213443 c4) ▸
       at 2 2 [] (wl0162 (lit c4)) ▸ done


-- F4-K3-CS2: 19 steps
lem-F4-K3-CS2 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4) ▸
       at 3 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at12213443 c4) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 0 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸ done

  b1 : Chain (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0586 c4)) ▸
       at 4 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 4 (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0586 c4)) ▸
       at 0 4 (Bx0-2143 ∷ []) (sym (lem-box-cP-at12213443 c4)) ▸
       at 0 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1423-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0708 (lit c4))) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4-CS0-I: 19 steps
lem-F4-CS0-I : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-I c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ ι1 ∷ S4⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (ι ∷ S4⁻ ∷ X4 ∷ []) (wl0709 (lit c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (ι ∷ S4⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0599 c4) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 5 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 4 3 (ι1 ∷ S4⁻ ∷ Toff213 ∷ []) (wp0600 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ ι1 ∷ S4⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ ι ∷ S4⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 4 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 3 3 (ι ∷ S4⁻ ∷ CCZ024 ∷ []) (wp0601 c4) ▸
       at 3 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 2 3 (ι1 ∷ S4⁻ ∷ Toff213 ∷ []) (wp0600 c4) ▸
       at 2 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 1 3 (ι ∷ S4⁻ ∷ CCZ024 ∷ []) (wp0601 c4) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ ι ∷ S4⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 3 (S4 ∷ X4 ∷ []) (sym (wl0710 (lit c4))) ▸ done


-- F4-CS0-S0: 17 steps
lem-F4-CS0-S0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ S0 ∷ CS04⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S0 ∷ CS04⁻ ∷ X4 ∷ []) (sym (wp0602 c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (S0 ∷ CS04⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0421 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (S0 ∷ Toff213 ∷ []) (sym (c₁ (S) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 5 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ S0 ∷ CS04⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b1 = at 3 3 (S0 ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp0420 c4) ▸
       at 2 2 (S0 ∷ Toff213 ∷ []) (sym (c₁ (S) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4)) ▸
       at 1 3 (S0 ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp0420 c4) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 0 3 (CS04 ∷ X4 ∷ []) (sym (wp0603 c4)) ▸ done


-- F4-CS0-S1: 15 steps
lem-F4-CS0-S1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ S1 ∷ CS14⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S1 ∷ CS14⁻ ∷ X4 ∷ []) (sym (wl0711 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (S1 ∷ CS14⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0604 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 3 (S1 ∷ CS14⁻ ∷ Toff213 ∷ []) (sym (wl0712 (lit c4))) ▸
       at 3 3 (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) (wp0605 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ S1 ∷ CS14⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b1 = at 2 3 (S1 ∷ CS14⁻ ∷ Toff213 ∷ []) (sym (wl0712 (lit c4))) ▸
       at 1 3 (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) (wp0605 c4) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 3 (CS14 ∷ X4 ∷ []) (sym (wl0713 (lit c4))) ▸ done


-- F4-CS0-S2: 14 steps
lem-F4-CS0-S2 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ Bx2-0413 ∷ S2 ∷ CS24⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S2 ∷ CS24⁻ ∷ X4 ∷ []) (sym (wl0714 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 3 (S2 ∷ CS24⁻ ∷ CS03⁻ ∷ []) (wp0606 c4) ▸
       at 4 3 (S2 ∷ CS24⁻ ∷ Toff314 ∷ []) (sym (wl0715 (lit c4))) ▸
       at 3 3 (S2 ∷ CS24⁻ ∷ CS03 ∷ []) (wp0607 c4) ▸
       at 2 3 (S2 ∷ CS24⁻ ∷ Toff314 ∷ []) (sym (wl0715 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ S2 ∷ CS24⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b1 = at 1 2 (S2 ∷ Bx2-0413 ∷ []) (sym (lem-Su-box-at0210243143 c4)) ▸
       at 2 2 (CS24⁻ ∷ Bx2-0413 ∷ []) (sym (lem-CSdu-box-2-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 3 (CS24 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸ done


-- F4-CS0-S3: 15 steps
lem-F4-CS0-S3 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S3 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ S3 ∷ CS34⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S3 ∷ CS34⁻ ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (S3 ∷ CS34⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0608 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 3 (S3 ∷ CS34⁻ ∷ Toff213 ∷ []) (sym (wl0718 (lit c4))) ▸
       at 3 3 (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) (wp0609 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ S3 ∷ CS34⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b1 = at 2 3 (S3 ∷ CS34⁻ ∷ Toff213 ∷ []) (sym (wl0718 (lit c4))) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) (wp0609 c4) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 3 (CS34 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸ done


-- F4-CS0-K0: 19 steps
lem-F4-CS0-K0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ K0 ∷ CK40 ∷ Toff213 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (sym (wp0610 c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 7 (K0 ∷ CK40 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0611 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (K0 ∷ Toff213 ∷ []) (sym (c₁ (K) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 5 2 (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ K0 ∷ CK40 ∷ Toff213 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 6 2 (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S)) ▸
       at 3 4 (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ []) (wp0612 c4) ▸
       at 2 2 (K0 ∷ Toff213 ∷ []) (sym (c₁ (K) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S)) ▸
       at 1 4 (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ []) (wp0612 c4) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 4 (CK40 ∷ X4 ∷ []) (sym (wp0613 c4)) ▸ done


-- F4-CS0-K1: 21 steps
lem-F4-CS0-K1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (X4 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK41 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0614 c4)) ▸
       at 1 1 (Bx2-0341 ∷ []) (lem-box-perm-1423-at0210243143 c4) ▸
       at 1 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0210233441 c4) ▸
       at 4 4 (K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ []) (sym (wl0721 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx2-0341 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K1 ∷ CCZ023 ∷ []) (wl0722 (lit c4)) ▸
       at 4 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 (lit c4)) ▸
       at 5 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 2 4 (K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ []) (sym (wl0721 (lit c4))) ▸
       at 1 2 (K1 ∷ CCZ023 ∷ []) (wl0722 (lit c4)) ▸
       at 2 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 (lit c4)) ▸
       at 3 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 4 4 (Bx2-0341 ∷ []) (sym (lem-box-cP-at0210233441 c4)) ▸ done

  b2 : Chain (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx2-0341 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1423-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 4 (CK41 ∷ X4 ∷ []) (sym (wl0723 (lit c4))) ▸ done


-- CKu-box-2 @0210243143: 7 steps
lem-CKu-box-2-at0210243143 : Ws → ⟪ (CK42 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CK42 ∷ []) ⟫ʷ
lem-CKu-box-2-at0210243143 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CK42 ∷ [])
  b0 = at 0 1 (CS24⁻ ∷ K2⁻ ∷ CS24⁻ ∷ K2 ∷ CS24⁻ ∷ []) (wl0724 (lit c4)) ▸
       at 4 2 (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4) ▸
       at 3 2 (Bx2-0413 ∷ K2 ∷ []) (lem-Ku-box-at0210243143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4) ▸
       at 1 2 (Bx2-0413 ∷ K2⁻ ∷ []) (lem-Kdu-box-at0210243143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4) ▸
       at 1 5 (CK42 ∷ []) (sym (wl0724 (lit c4))) ▸ done


-- F4-CS0-K2: 20 steps
lem-F4-CS0-K2 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) (X4 ∷ Bx2-0413 ∷ K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 4 (K2 ∷ CK42 ∷ S4 ∷ CS03⁻ ∷ []) (wp0615 c4) ▸
       at 4 4 (K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ []) (sym (wl0726 (lit c4))) ▸
       at 3 4 (K2 ∷ CK42 ∷ S4 ∷ CS03 ∷ []) (wp0616 c4) ▸
       at 2 4 (K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ []) (sym (wl0726 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 1 2 (K2 ∷ Bx2-0413 ∷ []) (sym (lem-Ku-box-at0210243143 c4)) ▸
       at 2 2 (CK42 ∷ Bx2-0413 ∷ []) (sym (lem-CKu-box-2-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (S4 ∷ Toff213 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 5 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 4 2 (S4 ∷ Toff213 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 3 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done

  b2 : Chain (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 4 (CK42 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸ done


-- F4-CS0-K3: 21 steps
lem-F4-CS0-K3 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) (X4 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (sym (wl0729 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK43 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0618 c4)) ▸
       at 1 1 (Bx2-0143 ∷ []) (lem-box-perm-1324-at0210243143 c4) ▸
       at 1 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0210213443 c4) ▸
       at 4 4 (K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ []) (sym (wl0730 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx2-0143 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 4 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 5 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 2 4 (K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 1 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 2 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 3 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 4 4 (Bx2-0143 ∷ []) (sym (lem-box-cP-at0210213443 c4)) ▸ done

  b2 : Chain (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx2-0143 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1324-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 4 (CK43 ∷ X4 ∷ []) (sym (wl0731 (lit c4))) ▸ done


-- F4-CS1-I: 17 steps
lem-F4-CS1-I : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-I c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ ι ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (ι ∷ S4⁻ ∷ X4 ∷ []) (wl0709 (lit c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 2 6 (ι1 ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (wp0619 c4) ▸
       at 2 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ ι ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ ι ∷ S4⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 4 3 (ι ∷ S4⁻ ∷ Toff023 ∷ []) (wp0620 c4) ▸
       at 3 3 (ι ∷ S4⁻ ∷ CCZ014 ∷ []) (wp0621 c4) ▸
       at 2 3 (ι ∷ S4⁻ ∷ Toff023 ∷ []) (wp0620 c4) ▸
       at 1 3 (ι ∷ S4⁻ ∷ CCZ014 ∷ []) (wp0621 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ ι ∷ S4⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 0 3 (S4 ∷ X4 ∷ []) (sym (wl0710 (lit c4))) ▸ done


-- F4-CS1-S0: 14 steps
lem-F4-CS1-S0 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) (X4 ∷ Bx0-1423 ∷ S0 ∷ CS04⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S0 ∷ CS04⁻ ∷ X4 ∷ []) (sym (wp0602 c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 3 (S0 ∷ CS04⁻ ∷ CS13⁻ ∷ []) (wp0622 c4) ▸
       at 4 3 (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) (sym (wp0623 c4)) ▸
       at 3 3 (S0 ∷ CS04⁻ ∷ CS13 ∷ []) (wp0624 c4) ▸
       at 2 3 (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) (sym (wp0623 c4)) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ S0 ∷ CS04⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 1 2 (S0 ∷ Bx0-1423 ∷ []) (sym (lem-Su-box-at243243 c4)) ▸
       at 2 2 (CS04⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CSdu-box-2-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 3 (CS04 ∷ X4 ∷ []) (sym (wp0603 c4)) ▸ done


-- F4-CS1-S1: 17 steps
lem-F4-CS1-S1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ S1 ∷ CS14⁻ ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S1 ∷ CS14⁻ ∷ X4 ∷ []) (sym (wl0711 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (S1 ∷ CS14⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0573 (lit c4))) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (S1 ∷ Toff023 ∷ []) (sym (wl0572 (lit c4))) ▸
       at 5 2 (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ S1 ∷ CS14⁻ ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ S1 ∷ CS14⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 3 3 (S1 ∷ CS14⁻ ∷ CCZ014 ∷ []) (wp0445 c4) ▸
       at 2 2 (S1 ∷ Toff023 ∷ []) (sym (wl0572 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 (lit c4)) ▸
       at 1 3 (S1 ∷ CS14⁻ ∷ CCZ014 ∷ []) (wp0445 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ S1 ∷ CS14⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 0 3 (CS14 ∷ X4 ∷ []) (sym (wl0713 (lit c4))) ▸ done


-- F4-CS1-S2: 15 steps
lem-F4-CS1-S2 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ S2 ∷ CS24⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S2 ∷ CS24⁻ ∷ X4 ∷ []) (sym (wl0714 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (S2 ∷ CS24⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0732 (lit c4))) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 3 (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) (sym (wp0625 c4)) ▸
       at 3 3 (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) (wp0626 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ S2 ∷ CS24⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 2 3 (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) (sym (wp0625 c4)) ▸
       at 1 3 (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) (wp0626 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 3 (CS24 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸ done


-- F4-CS1-S3: 15 steps
lem-F4-CS1-S3 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S3 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ S3 ∷ CS34⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S3 ∷ CS34⁻ ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (S3 ∷ CS34⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0733 (lit c4))) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 3 (S3 ∷ CS34⁻ ∷ Toff023 ∷ []) (sym (wp0627 c4)) ▸
       at 3 3 (S3 ∷ CS34⁻ ∷ CCZ014 ∷ []) (wp0628 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ S3 ∷ CS34⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 2 3 (S3 ∷ CS34⁻ ∷ Toff023 ∷ []) (sym (wp0627 c4)) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ CCZ014 ∷ []) (wp0628 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 3 (CS34 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸ done


-- CKu-box-2 @243243: 7 steps
lem-CKu-box-2-at243243 : Ws → ⟪ (CK40 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CK40 ∷ []) ⟫ʷ
lem-CKu-box-2-at243243 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CK40 ∷ [])
  b0 = at 0 1 (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) (wp0255 c4) ▸
       at 4 2 (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4) ▸
       at 3 2 (Bx0-1423 ∷ K0 ∷ []) (lem-Ku-box-at243243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4) ▸
       at 1 2 (Bx0-1423 ∷ K0⁻ ∷ []) (lem-Kdu-box-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4) ▸
       at 1 5 (CK40 ∷ []) (sym (wp0255 c4)) ▸ done


-- F4-CS1-K0: 20 steps
lem-F4-CS1-K0 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) (X4 ∷ Bx0-1423 ∷ K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (sym (wp0610 c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 4 (K0 ∷ CK40 ∷ S4 ∷ CS13⁻ ∷ []) (wp0629 c4) ▸
       at 4 4 (K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ []) (sym (wp0630 c4)) ▸
       at 3 4 (K0 ∷ CK40 ∷ S4 ∷ CS13 ∷ []) (wp0631 c4) ▸
       at 2 4 (K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ []) (sym (wp0630 c4)) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b1 = at 1 2 (K0 ∷ Bx0-1423 ∷ []) (sym (lem-Ku-box-at243243 c4)) ▸
       at 2 2 (CK40 ∷ Bx0-1423 ∷ []) (sym (lem-CKu-box-2-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 5 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 4 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 3 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b2 : Chain (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 4 (CK40 ∷ X4 ∷ []) (sym (wp0613 c4)) ▸ done


-- F4-CS1-K1: 19 steps
lem-F4-CS1-K1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CK41 ∷ Toff023 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK41 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0734 (lit c4))) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 5 2 (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CK41 ∷ Toff023 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b1 = at 6 2 (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 3 4 (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) (wp0634 c4) ▸
       at 2 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 3 2 (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 1 4 (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) (wp0634 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 4 (CK41 ∷ X4 ∷ []) (sym (wl0723 (lit c4))) ▸ done


-- F4-CS1-K2: 21 steps
lem-F4-CS1-K2 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 7 (K2 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0736 (lit c4))) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at233442 c4) ▸
       at 4 4 (K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ []) (sym (wp0635 c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx0-1342 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K2 ∷ CCZ013 ∷ []) (wl0737 (lit c4)) ▸
       at 4 2 (CK42 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CK42 (lit c4)) ▸
       at 5 2 (S4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (S)) ▸
       at 2 4 (K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ []) (sym (wp0635 c4)) ▸
       at 1 2 (K2 ∷ CCZ013 ∷ []) (wl0737 (lit c4)) ▸
       at 2 2 (CK42 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CK42 (lit c4)) ▸
       at 3 2 (S4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (S)) ▸
       at 4 4 (Bx0-1342 ∷ []) (sym (lem-box-cP-at233442 c4)) ▸ done

  b2 : Chain (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx0-1342 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1423-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 4 (CK42 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸ done


-- F4-CS1-K3: 21 steps
lem-F4-CS1-K3 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) (X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (sym (wl0729 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK43 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0738 (lit c4))) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 4 4 (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (sym (wp0636 c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx0-1243 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 4 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 5 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 2 4 (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (sym (wp0636 c4)) ▸
       at 1 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 2 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 3 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 4 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸ done

  b2 : Chain (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx0-1243 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 4 (CK43 ∷ X4 ∷ []) (sym (wl0731 (lit c4))) ▸ done


-- F4-CS2-I: 17 steps
lem-F4-CS2-I : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-I c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ ι ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (ι ∷ S4⁻ ∷ X4 ∷ []) (wl0709 (lit c4)) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 2 6 (ι1 ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (wp0637 c4) ▸
       at 2 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ ι ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ ι ∷ S4⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 4 3 (ι ∷ S4⁻ ∷ Toff013 ∷ []) (wp0638 c4) ▸
       at 3 3 (ι ∷ S4⁻ ∷ CCZ024 ∷ []) (wp0601 c4) ▸
       at 2 3 (ι ∷ S4⁻ ∷ Toff013 ∷ []) (wp0638 c4) ▸
       at 1 3 (ι ∷ S4⁻ ∷ CCZ024 ∷ []) (wp0601 c4) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ ι ∷ S4⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 0 3 (S4 ∷ X4 ∷ []) (sym (wl0710 (lit c4))) ▸ done

