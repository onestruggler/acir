{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D008 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0018 ; wl0171 ; wl0173 ; wl0175 ; wl0179 ; wl0183 ; wl0184 ; wl0185 ; wl0186 ; wl0187 ; wl0190 ; wl0191 ; wl0192 ; wl0193 ; wl0194 ; wl0195 ; wl0196 ; wl0197 ; wl0199 ; wl0204 ; wl0230 ; wl0263 ; wl0310 ; wl0334 ; wl0436 ; wl0441 ; wl0494 ; wl0499 ; wl0501 ; wl0560 ; wl0586 ; wl0587 ; wl0611 ; wl0612 ; wl0613 ; wl0614 ; wl0616 ; wl0617 ; wl0619 ; wl0620 ; wl0621 ; wl0624 ; wl0625 ; wl0629 ; wl0630 ; wl0631 ; wl0632 ; wl0633 ; wl0634 ; wl0635 ; wl0636 ; wl0639 ; wl0669 ; wl0670 ; wl0711 ; wl0713 ; wl0714 ; wl0716 ; wl0717 ; wl0719 ; wl0720 ; wl0722 ; wl0723 ; wl0725 ; wl0728 ; wl0729 ; wl0731 ; wl0739 ; wl0740 ; wl0741 ; wl0742 ; wl0743 ; wl0744 ; wl0745 ; wl0746 ; wl0747 ; wl0748 ; wl0749 ; wl0750 ; wl0751 ; wl0752 ; wl0753 ; wl0754 ; wl0755 ; wl0756 ; wl0757 ; wl0758 ; wl0759 ; wl0760 ; wl0761 ; wl0762 ; wl0763 ; wl0764 ; wl0765 ; wl0766 ; wl0767 ; wl0768 ; wl0769 ; wl0770 ; wl0771 ; wl0772 ; wl0773 ; wl0774 ; wl0775 ; wl0776 ; wl0777 ; wl0778 ; wl0779 ; wl0780 ; wl0781 ; wl0782 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wl0787 ; wp0020 ; wp0021 ; wp0022 ; wp0023 ; wp0032 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0041 ; wp0042 ; wp0044 ; wp0108 ; wp0135 ; wp0161 ; wp0255 ; wp0353 ; wp0354 ; wp0357 ; wp0461 ; wp0496 ; wp0513 ; wp0514 ; wp0515 ; wp0516 ; wp0543 ; wp0602 ; wp0603 ; wp0605 ; wp0609 ; wp0610 ; wp0613 ; wp0617 ; wp0636 ; wp0639 ; wp0640 ; wp0641 ; wp0642 ; wp0643 ; wp0644 ; wp0645 ; wp0646 ; wp0647 ; wp0648 ; wp0649 ; wp0650 ; wp0651 ; wp0652 ; wp0653 ; wp0654 ; wp0655 ; wp0656 ; wp0657 ; wp0658 ; wp0659 ; wp0660 ; wp0661 ; wp0662 ; wp0663 ; wp0664 ; wp0665 ; wp0666 ; wp0667 ; wp0668 ; wp0669 ; wp0670 ; wp0671 ; wp0672 ; wp0673 ; wp0674 ; wp0675 ; wp0676 ; wp0677 ; wp0678 ; wp0679 ; wp0680 ; wp0681 ; wp0682 ; wp0683 ; wp0684 ; wp0685 ; wp0686 ; wp0687 ; wp0688 ; wp0689 ; wp0690 ; wp0691 ; wp0692 ; wp0693 ; wp0694 ; wp0695 ; wp0696 ; wp0697 ; wp0698 ; wp0699 ; wp0700 ; wp0701 ; wp0702 ; wp0703)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at0210243143 ; lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-box-tQ-at0310243142 ; lem-cQ-at0314203142 ; lem-sym-ab-at0310243142)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-CSdu-box-2-at122441 ; lem-Su-box-at122441 ; lem-box-cP-at0314203142 ; lem-sym-ab-at0314203142)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-Kdu-box-at122441 ; lem-Ku-box-at122441 ; lem-box-cP-at0210233441 ; lem-box-cP-at12233441 ; lem-box-perm-1324-at122441 ; lem-box-tQ-at0210233441 ; lem-box-tQ-at0214213043 ; lem-pairs-at0214213043 ; lem-sym-ab-at0210243143 ; lem-sym-bc-at0214203143 ; lem-tP-at0210233441)
open import Examples.Groups.Clifford+CS.FiveV.D.D007 using (lem-box-cP-at12213443 ; lem-box-perm-1423-at122441)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX04-CCZ123 ; lem-comm-CX04-TOFF213 ; lem-comm-CX13-CCZ024 ; lem-comm-CZ04-CCZ123)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CZ14-CCZ023 ; lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS12-CCZ034 ; lem-comm-CS14-CCZ023 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd12-TOFF304 ; lem-comm-CSd14-CCZ023 ; lem-comm-CX40-CCZ123)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CCZ023-CK41 ; lem-comm-CCZ024-CX13 ; lem-comm-CS02-TOFF314 ; lem-comm-CS12-TOFF304 ; lem-comm-CSd02-TOFF314 ; lem-comm-CSd03-TOFF214 ; lem-comm-CSd14-TOFF302 ; lem-comm-CX04-TOFF312 ; lem-comm-CX30-CCZ124 ; lem-comm-CX30-TOFF214 ; lem-comm-CX41-CCZ023 ; lem-comm-CZ02-TOFF314 ; lem-comm-CZ14-TOFF203 ; lem-comm-TOFF013-CK42 ; lem-comm-TOFF203-CSd14 ; lem-comm-TOFF213-CX04 ; lem-comm-TOFF314-CSd02)
-- F4-CS2-S0: 14 steps
lem-F4-CS2-S0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) (X4 ∷ Bx0-2431 ∷ S0 ∷ CS04⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S0 ∷ CS04⁻ ∷ X4 ∷ []) (sym (wp0602 c4)) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 3 (S0 ∷ CS04⁻ ∷ CS12⁻ ∷ []) (wp0639 c4) ▸
       at 4 3 (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) (sym (wp0640 c4)) ▸
       at 3 3 (S0 ∷ CS04⁻ ∷ CS12 ∷ []) (wp0641 c4) ▸
       at 2 3 (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) (sym (wp0640 c4)) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ S0 ∷ CS04⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 1 2 (S0 ∷ Bx0-2431 ∷ []) (sym (lem-Su-box-at122441 c4)) ▸
       at 2 2 (CS04⁻ ∷ Bx0-2431 ∷ []) (sym (lem-CSdu-box-2-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 3 (CS04 ∷ X4 ∷ []) (sym (wp0603 c4)) ▸ done


-- F4-CS2-S1: 15 steps
lem-F4-CS2-S1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ S1 ∷ CS14⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S1 ∷ CS14⁻ ∷ X4 ∷ []) (sym (wl0711 (lit c4))) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (S1 ∷ CS14⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl0739 (lit c4))) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 3 (S1 ∷ CS14⁻ ∷ Toff013 ∷ []) (sym (wp0642 c4)) ▸
       at 3 3 (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) (wp0605 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ S1 ∷ CS14⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 2 3 (S1 ∷ CS14⁻ ∷ Toff013 ∷ []) (sym (wp0642 c4)) ▸
       at 1 3 (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) (wp0605 c4) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 3 (CS14 ∷ X4 ∷ []) (sym (wl0713 (lit c4))) ▸ done


-- F4-CS2-S2: 17 steps
lem-F4-CS2-S2 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ S2 ∷ CS24⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S2 ∷ CS24⁻ ∷ X4 ∷ []) (sym (wl0714 (lit c4))) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (S2 ∷ CS24⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl0587 (lit c4))) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (S2 ∷ Toff013 ∷ []) (sym (wl0586 (lit c4))) ▸
       at 5 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ S2 ∷ CS24⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ S2 ∷ CS24⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 3 3 (S2 ∷ CS24⁻ ∷ CCZ024 ∷ []) (wp0461 c4) ▸
       at 2 2 (S2 ∷ Toff013 ∷ []) (sym (wl0586 (lit c4))) ▸
       at 3 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 1 3 (S2 ∷ CS24⁻ ∷ CCZ024 ∷ []) (wp0461 c4) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ S2 ∷ CS24⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 0 3 (CS24 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸ done


-- F4-CS2-S3: 15 steps
lem-F4-CS2-S3 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S3 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ S3 ∷ CS34⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S3 ∷ CS34⁻ ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (S3 ∷ CS34⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl0740 (lit c4))) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 3 (S3 ∷ CS34⁻ ∷ Toff013 ∷ []) (sym (wp0643 c4)) ▸
       at 3 3 (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) (wp0609 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ S3 ∷ CS34⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 2 3 (S3 ∷ CS34⁻ ∷ Toff013 ∷ []) (sym (wp0643 c4)) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) (wp0609 c4) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 3 (CS34 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸ done


-- CKu-box-2 @122441: 7 steps
lem-CKu-box-2-at122441 : Ws → ⟪ (CK40 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CK40 ∷ []) ⟫ʷ
lem-CKu-box-2-at122441 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CK40 ∷ [])
  b0 = at 0 1 (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) (wp0255 c4) ▸
       at 4 2 (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4) ▸
       at 3 2 (Bx0-2431 ∷ K0 ∷ []) (lem-Ku-box-at122441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4) ▸
       at 1 2 (Bx0-2431 ∷ K0⁻ ∷ []) (lem-Kdu-box-at122441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4) ▸
       at 1 5 (CK40 ∷ []) (sym (wp0255 c4)) ▸ done


-- F4-CS2-K0: 20 steps
lem-F4-CS2-K0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) (X4 ∷ Bx0-2431 ∷ K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (sym (wp0610 c4)) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 4 (K0 ∷ CK40 ∷ S4 ∷ CS12⁻ ∷ []) (wp0644 c4) ▸
       at 4 4 (K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ []) (sym (wp0645 c4)) ▸
       at 3 4 (K0 ∷ CK40 ∷ S4 ∷ CS12 ∷ []) (wp0646 c4) ▸
       at 2 4 (K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ []) (sym (wp0645 c4)) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b1 = at 1 2 (K0 ∷ Bx0-2431 ∷ []) (sym (lem-Ku-box-at122441 c4)) ▸
       at 2 2 (CK40 ∷ Bx0-2431 ∷ []) (sym (lem-CKu-box-2-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (S4 ∷ Toff013 ∷ []) (sym (wp0647 c4)) ▸
       at 5 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 4 2 (S4 ∷ Toff013 ∷ []) (sym (wp0647 c4)) ▸
       at 3 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b2 : Chain (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 4 (CK40 ∷ X4 ∷ []) (sym (wp0613 c4)) ▸ done


-- F4-CS2-K1: 21 steps
lem-F4-CS2-K1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) (X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK41 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl0741 (lit c4))) ▸
       at 1 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 1 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 4 4 (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) (sym (wp0648 c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-2341 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K1 ∷ CCZ023 ∷ []) (wl0722 (lit c4)) ▸
       at 4 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 (lit c4)) ▸
       at 5 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 2 4 (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) (sym (wp0648 c4)) ▸
       at 1 2 (K1 ∷ CCZ023 ∷ []) (wl0722 (lit c4)) ▸
       at 2 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 (lit c4)) ▸
       at 3 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 4 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸ done

  b2 : Chain (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-2341 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 4 (CK41 ∷ X4 ∷ []) (sym (wl0723 (lit c4))) ▸ done


-- F4-CS2-K2: 19 steps
lem-F4-CS2-K2 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ K2 ∷ CK42 ∷ Toff013 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 7 (K2 ∷ CK42 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl0742 (lit c4))) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸
       at 5 2 (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ K2 ∷ CK42 ∷ Toff013 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b1 = at 6 2 (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S)) ▸
       at 3 4 (K2 ∷ CK42 ∷ S4 ∷ CCZ024 ∷ []) (wp0649 c4) ▸
       at 2 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸
       at 3 2 (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S)) ▸
       at 1 4 (K2 ∷ CK42 ∷ S4 ∷ CCZ024 ∷ []) (wp0649 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 4 (CK42 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸ done


-- F4-CS2-K3: 21 steps
lem-F4-CS2-K3 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (sym (wl0729 (lit c4))) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK43 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl0744 (lit c4))) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at12213443 c4) ▸
       at 4 4 (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (sym (wp0636 c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx0-2143 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 4 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 5 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 2 4 (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (sym (wp0636 c4)) ▸
       at 1 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 2 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 3 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 4 4 (Bx0-2143 ∷ []) (sym (lem-box-cP-at12213443 c4)) ▸ done

  b2 : Chain (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx0-2143 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1423-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 4 (CK43 ∷ X4 ∷ []) (sym (wl0731 (lit c4))) ▸ done


-- F4-CS0-CS0: 286 steps
lem-F4-CS0-CS0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-CS0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 4 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl0183 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 6 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 9 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 8 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 7 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 4 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CCZ013 ∷ []) (wl0186 (lit c4)) ▸
       at 5 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 5 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸ done

  b3 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b3 = at 6 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 8 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 5 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸ done

  b4 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸ done

  b5 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ Toff314 ∷ Toff213 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b5 = at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 12 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 7 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 8 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸ done

  b6 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ Toff314 ∷ Toff213 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b6 = at 6 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 9 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 8 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 12 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 11 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 10 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸ done

  b7 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b7 = at 9 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 7 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 8 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 3 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 4 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸ done

  b8 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b8 = at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 6 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 8 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 7 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b9 : Chain (X4 ∷ Bx2-0413 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b9 = at 5 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 2 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 3 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸ done

  b10 : Chain (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b10 = at 10 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 6 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸ done

  b11 : Chain (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b11 = at 7 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 6 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 10 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸ done

  b12 : Chain (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Bx2-0413 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b12 = at 5 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 6 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 2 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl0183 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸ done

  b13 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Bx2-0413 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Bx2-0413 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b13 = at 8 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b14 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Bx2-0413 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ024 ∷ CX01 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b14 = at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CCZ013 ∷ []) (wl0186 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸ done

  b15 : Chain (Bx2-0413 ∷ X4 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ024 ∷ CX01 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ024 ∷ CX01 ∷ CS03 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b15 = at 4 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 2 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 3 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 3 2 (Toff213 ∷ CCZ013 ∷ []) (wl0186 (lit c4)) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸ done

  b16 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ024 ∷ CX01 ∷ CS03 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ Bx2-0413 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b16 = at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 5 2 (Toff213 ∷ CCZ013 ∷ []) (wl0186 (lit c4)) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 8 (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ []) (wp0650 c4) ▸
       at 10 2 [] (wl0230 (lit c4)) ▸ done

  b17 : Chain (Bx2-0413 ∷ X4 ∷ Bx2-0413 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b17 = at 3 3 (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp0651 c4) ▸
       at 5 2 [] (wp0161 c4) ▸
       at 4 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 6 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 2 (CX13 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0745 (lit c4))) ▸
       at 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (CS03 ∷ []) (refl) ▸ done

  b18 : Chain (Bx2-0413 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ Toff314 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b18 = at 6 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 6 (CX13 ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0652 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 5 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 4 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸ done

  b19 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ Toff314 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b19 = at 10 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 10 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸ done

  b20 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff213 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b20 = at 9 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 2 (CX12 ∷ Toff213 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 4 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 5 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 6 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 7 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 8 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸ done

  b21 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff213 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ Toff213 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b21 = at 4 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 5 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 7 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸
       at 9 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 8 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 10 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 11 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸ done

  b22 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ Toff213 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CX13 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b22 = at 12 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 8 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 9 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 3 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸
       at 5 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 3 4 (CX13 ∷ Toff314 ∷ []) (wp0656 c4) ▸
       at 2 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸ done

  b23 : Chain (Bx2-0413 ∷ X4 ∷ CX13 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CX13 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b23 = at 3 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 4 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 9 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 3 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸ done

  b24 : Chain (Bx2-0413 ∷ X4 ∷ CX13 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS03 ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b24 = at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 3 (Toff314 ∷ X4 ∷ []) (sym (wl0187 (lit c4))) ▸
       at 4 2 (CS03 ∷ X4 ∷ []) (sym (wp0657 c4)) ▸
       at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸ done

  b25 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS03 ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b25 = at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 5 (CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0658 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 5 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 4 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 3 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done

  b26 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ [])
  b26 = at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 2 2 (CS03 ∷ X4 ∷ []) (sym (wp0657 c4)) ▸
       at 5 2 (CX13 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0745 (lit c4))) ▸
       at 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸
       at 8 1 (CS03⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b27 = at 5 6 (CX13 ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0652 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 7 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 9 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 6 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 12 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸ done

  b28 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 12 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 11 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸ done

  b29 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ Toff213 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b29 = at 5 2 (CX12 ∷ Toff213 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 7 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 6 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 7 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 8 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 10 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸ done

  b30 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ Toff213 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff213 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b30 = at 7 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 9 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸
       at 11 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 10 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 11 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 12 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 13 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 14 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸ done

  b31 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff213 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b31 = at 10 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 11 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 5 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸
       at 7 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 5 4 (CX13 ∷ Toff314 ∷ []) (wp0656 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b32 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ Toff314 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b32 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done

  b33 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ Toff314 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03⁻ ∷ X4 ∷ [])
  b33 = at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 3 (Toff314 ∷ X4 ∷ []) (sym (wl0187 (lit c4))) ▸
       at 6 2 (CS03⁻ ∷ X4 ∷ []) (sym (wp0659 c4)) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03⁻ ∷ X4 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b34 = at 6 5 (CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0660 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 8 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 7 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 6 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 5 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b35 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b35 = at 10 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 4 2 (CS03⁻ ∷ X4 ∷ []) (sym (wp0659 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- box-perm-2314 @0210243143: 2 steps
lem-box-perm-2314-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-box-perm-2314-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4) ▸
       at 0 1 (Bx2-4103 ∷ []) (lem-sym-bc-at0214203143 c4) ▸ done


-- cQ @0314213042: 7 steps
lem-cQ-at0314213042 : Ws → ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at0314213042 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CS34 ∷ []) (sym (wp0543 c4)) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS13⁻ ∷ []) (sym (wl0669 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS13 ∷ []) (sym (wl0670 (lit c4))) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸ done


-- box-tQ @0314213042: 13 steps
lem-box-tQ-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at0314213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4102 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 0 2 (Toff314 ∷ CCZ134 ∷ CZ14 ∷ []) (wl0749 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at0314213042 c4) ▸
       at 2 4 (Toff314 ∷ []) (wl0750 (lit c4)) ▸ done


-- CXbc-box @0314213042: 17 steps
lem-CXbc-box-at0314213042 : Ws → ⟪ (CX10 ∷ Bx3-4102 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at0314213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx3-4102 ∷ CX10 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CX10 ∷ CCZ123 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ023 ∷ CX41 ∷ CS24 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4) ▸
       at 0 2 (Toff314 ∷ CX10 ∷ []) (wp0662 c4) ▸
       at 1 2 (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) (sym (wl0751 (lit c4))) ▸
       at 3 2 (Toff314 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0752 (lit c4)) ▸
       at 2 2 (Toff314 ∷ CX10 ∷ []) (wp0662 c4) ▸
       at 5 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 8 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CX10 ∷ CCZ123 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ023 ∷ CX41 ∷ CS24 ∷ CX10 ∷ []) (Bx3-4102 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0620 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ CCZ123 ∷ []) (sym (wl0613 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) (sym (wl0751 (lit c4))) ▸
       at 4 3 (CX10 ∷ []) (wl0753 (lit c4)) ▸
       at 0 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸ done

  b2 : Chain (Bx3-4102 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ []) (Bx3-4102 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wp0663 c4)) ▸ done


-- CXcb-box @0314213042: 18 steps
lem-CXcb-box-at0314213042 : Ws → ⟪ (CX01 ∷ Bx3-4102 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at0314213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx3-4102 ∷ CX01 ∷ []) (Toff314 ∷ CCZ023 ∷ CX01 ∷ Toff304 ∷ CS02 ∷ CX40 ∷ Toff314 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ CCZ023 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4) ▸
       at 0 2 (Toff314 ∷ CX01 ∷ Toff304 ∷ []) (wp0664 c4) ▸
       at 2 2 (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp0665 c4)) ▸
       at 1 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 4 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 8 2 (Toff314 ∷ CS24 ∷ []) (wl0754 (lit c4)) ▸
       at 7 2 (Toff314 ∷ CX40 ∷ []) (wp0666 c4) ▸
       at 6 2 (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4)) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ CX01 ∷ Toff304 ∷ CS02 ∷ CX40 ∷ Toff314 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ CCZ023 ∷ CX01 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ [])
  b1 = at 5 2 (Toff314 ∷ CX40 ∷ []) (wp0666 c4) ▸
       at 4 2 (Toff314 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF314 (lit c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸
       at 3 2 (Toff314 ∷ Toff304 ∷ []) (wp0667 c4) ▸
       at 2 2 (Toff314 ∷ CX01 ∷ Toff304 ∷ []) (wp0664 c4) ▸
       at 3 3 (CX01 ∷ []) (wp0668 c4) ▸
       at 4 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 3 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸ done

  b2 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ []) (Bx3-4102 ∷ CCZ024 ∷ [])
  b2 = at 0 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (sym (wp0670 c4)) ▸ done


-- SWbc-box @0314213042: 11 steps
lem-SWbc-box-at0314213042 : Ws → ⟪ (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-SWbc-box-at0314213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) (CX10 ∷ Bx3-4102 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 4 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 2 3 (Bx3-4102 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0314213042 c4) ▸
       at 3 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0671 c4) ▸
       at 1 3 (Bx3-4102 ∷ CCZ024 ∷ []) (lem-CXcb-box-at0314213042 c4) ▸
       at 4 2 (CX10 ∷ CCZ124 ∷ []) (wp0672 c4) ▸
       at 3 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸
       at 2 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸ done

  b1 : Chain (CX10 ∷ Bx3-4102 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (Bx3-4102 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wp0674 c4) ▸
       at 0 3 (Bx3-4102 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0314213042 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done


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


-- sym-bc @0314213042: 2 steps
lem-sym-bc-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym-bc-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0314213042 c4)) ▸
       at 0 3 (Bx3-4012 ∷ []) (lem-nat-SWbc-at0314213042 c4) ▸ done


-- box-perm-1324 @0314213042: 1 steps
lem-box-perm-1324-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-1324-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Bx3-4012 ∷ []) (lem-sym-bc-at0314213042 c4) ▸ done


-- box-perm-3124 @0314213042: 2 steps
lem-box-perm-3124-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-3124-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Bx3-4012 ∷ []) (lem-sym-bc-at0314213042 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4) ▸ done


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


-- box-perm-4312 @0214213043: 2 steps
lem-box-perm-4312-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ []) ⟫ʷ
lem-box-perm-4312-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-3041 ∷ [])
  b0 = at 0 1 (Bx2-0341 ∷ []) (lem-pairs-at0214213043 c4) ▸
       at 0 1 (Bx2-3041 ∷ []) (lem-sym-ab-at0210233441 c4) ▸ done


-- cQ @0213203441: 7 steps
lem-cQ-at0213203441 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at0213203441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0757 (lit c4)) ▸
       at 4 2 (CCZ124 ∷ CS23 ∷ []) (sym (wl0639 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS02⁻ ∷ []) (sym (wp0679 c4)) ▸
       at 1 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS02 ∷ []) (sym (wp0515 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0757 (lit c4))) ▸ done


-- tP @0213203441: 7 steps
lem-tP-at0213203441 : Ws → ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ
lem-tP-at0213203441 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0625 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0624 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-cQ-at0213203441 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff214 ∷ []) (wl0624 (lit c4)) ▸
       at 1 3 (Toff203 ∷ []) (wl0625 (lit c4)) ▸ done


-- VPQ @0213203441: 14 steps
lem-VPQ-at0213203441 : Ws → ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at0213203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (sym (wl0630 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (sym (wl0629 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S2⁻ ∷ []) (sym (wl0634 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff203 ∷ []) (lem-comm-TOFF203-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S2 ∷ []) (sym (wl0633 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS03⁻ ∷ []) (wp0514 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0213203441 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS03⁻ ∷ []) (wl0632 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS03⁻ ∷ []) (wl0631 (lit c4)) ▸
       at 0 4 (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4)) ▸
       at 2 4 (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4)) ▸ done


-- QVQ @0213203441: 3 steps
lem-QVQ-at0213203441 : Ws → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at0213203441 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  b0 = at 0 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0636 (lit c4))) ▸
       at 1 4 (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0213203441 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done


-- box-cP @0213203441: 12 steps
lem-box-cP-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at0213203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3041 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 2 4 (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-QVQ-at0213203441 c4) ▸
       at 1 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0213203441 c4) ▸
       at 2 2 [] (wl0635 (lit c4)) ▸ done


-- box-box-4 @0310243142: 103 steps
lem-box-box-4-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-box-box-4-at0310243142 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Bx3-0412 ∷ Bx2-3041 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CCZ023 ∷ CX34 ∷ CS13 ∷ CCZ123 ∷ Toff214 ∷ [])
  b0 = at 0 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4) ▸
       at 4 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0213203441 c4) ▸
       at 3 2 (CCZ023 ∷ CCZ123 ∷ []) (sym (wl0613 (lit c4))) ▸
       at 4 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CCZ123 ∷ []) (sym (wl0613 (lit c4))) ▸
       at 5 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0310 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS13 ∷ []) (sym (wl0670 (lit c4))) ▸
       at 8 2 (CCZ023 ∷ CX34 ∷ []) (sym (wp0680 c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CCZ023 ∷ CX34 ∷ CS13 ∷ CCZ123 ∷ Toff214 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff304 ∷ CCZ024 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CX34 ∷ []) (sym (wp0680 c4)) ▸
       at 5 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0310 (lit c4))) ▸
       at 6 3 (Toff214 ∷ CCZ123 ∷ []) (wl0759 (lit c4)) ▸
       at 3 4 (Bx2-3041 ∷ []) (sym (lem-box-cP-at0213203441 c4)) ▸
       at 3 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0213203441 c4) ▸
       at 2 2 (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp0665 c4)) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff304 ∷ CCZ024 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ K3 ∷ Toff214 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ CCZ024 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ [])
  b2 = at 4 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wp0681 c4)) ▸
       at 9 2 (Toff214 ∷ K3⁻ ∷ []) (wl0760 (lit c4)) ▸
       at 8 2 (Toff214 ∷ CS34 ∷ []) (wl0761 (lit c4)) ▸
       at 7 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CS04⁻ ∷ []) (wp0682 c4) ▸
       at 5 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 4 2 (Toff214 ∷ CS04 ∷ []) (wp0683 c4) ▸ done

  b3 : Chain (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ K3 ∷ Toff214 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ CCZ024 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff214 ∷ Toff304 ∷ CS14 ∷ CCZ023 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ024 ∷ Toff214 ∷ CCZ123 ∷ [])
  b3 = at 3 2 (Toff214 ∷ K3 ∷ []) (wl0762 (lit c4)) ▸
       at 4 7 (Toff304 ∷ []) (wp0681 c4) ▸
       at 6 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 8 2 (CCZ023 ∷ CX04 ∷ []) (sym (wp0684 c4)) ▸
       at 7 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CX04 ∷ []) (sym (wp0684 c4)) ▸ done

  b4 : Chain (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff214 ∷ Toff304 ∷ CS14 ∷ CCZ023 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ024 ∷ Toff214 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ Toff214 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ [])
  b4 = at 5 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp0665 c4)) ▸
       at 6 3 (CCZ014 ∷ []) (sym (wp0685 c4)) ▸
       at 6 2 (Toff214 ∷ CCZ014 ∷ []) (wp0686 c4) ▸
       at 5 1 (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wp0681 c4)) ▸
       at 11 2 (Toff214 ∷ K3⁻ ∷ []) (wl0760 (lit c4)) ▸
       at 10 2 (Toff214 ∷ CS34 ∷ []) (wl0761 (lit c4)) ▸ done

  b5 : Chain (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ Toff214 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b5 = at 9 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 8 2 (Toff214 ∷ CS04⁻ ∷ []) (wp0682 c4) ▸
       at 7 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CS04 ∷ []) (wp0683 c4) ▸
       at 5 2 (Toff214 ∷ K3 ∷ []) (wl0762 (lit c4)) ▸
       at 6 7 (Toff304 ∷ []) (wp0681 c4) ▸
       at 2 4 (Bx2-3041 ∷ []) (sym (lem-box-cP-at0213203441 c4)) ▸
       at 2 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0213203441 c4) ▸ done

  b6 : Chain (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CCZ023 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ CCZ123 ∷ Toff214 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b6 = at 1 2 (CCZ023 ∷ CCZ123 ∷ []) (sym (wl0613 (lit c4))) ▸
       at 2 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ123 ∷ []) (sym (wl0613 (lit c4))) ▸
       at 3 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0310 (lit c4)) ▸
       at 7 2 (CCZ023 ∷ CS13 ∷ []) (sym (wl0670 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CX34 ∷ []) (sym (wp0680 c4)) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CX34 ∷ []) (sym (wp0680 c4)) ▸ done

  b7 : Chain (Toff304 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CCZ023 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ CCZ123 ∷ Toff214 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ023 ∷ K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b7 = at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 4 5 (CCZ134 ∷ []) (sym (wl0310 (lit c4))) ▸
       at 4 3 (Toff214 ∷ CCZ123 ∷ []) (wl0759 (lit c4)) ▸
       at 1 4 (Bx2-3041 ∷ []) (sym (lem-box-cP-at0213203441 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0213203441 c4) ▸
       at 0 2 (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp0665 c4)) ▸
       at 2 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 1 1 (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wp0681 c4)) ▸ done

  b8 : Chain (CCZ023 ∷ K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ023 ∷ Toff214 ∷ Toff304 ∷ CCZ014 ∷ CCZ024 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b8 = at 7 2 (Toff214 ∷ K3⁻ ∷ []) (wl0760 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CS34 ∷ []) (wl0761 (lit c4)) ▸
       at 5 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 4 2 (Toff214 ∷ CS04⁻ ∷ []) (wp0682 c4) ▸
       at 3 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CS04 ∷ []) (wp0683 c4) ▸
       at 1 2 (Toff214 ∷ K3 ∷ []) (wl0762 (lit c4)) ▸
       at 2 7 (Toff304 ∷ []) (wp0681 c4) ▸ done

  b9 : Chain (CCZ023 ∷ Toff214 ∷ Toff304 ∷ CCZ014 ∷ CCZ024 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ023 ∷ Toff214 ∷ Toff304 ∷ CCZ023 ∷ CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b9 = at 4 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 3 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 7 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CX04 ∷ []) (sym (wp0684 c4)) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CX04 ∷ []) (sym (wp0684 c4)) ▸
       at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 4 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸ done

  b10 : Chain (CCZ023 ∷ Toff214 ∷ Toff304 ∷ CCZ023 ∷ CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS04 ∷ CX30 ∷ Toff214 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b10 = at 2 2 (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp0665 c4)) ▸
       at 4 3 (CCZ014 ∷ []) (sym (wp0685 c4)) ▸
       at 4 2 (Toff214 ∷ CCZ014 ∷ []) (wp0686 c4) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wp0681 c4)) ▸
       at 9 2 (Toff214 ∷ K3⁻ ∷ []) (wl0760 (lit c4)) ▸
       at 8 2 (Toff214 ∷ CS34 ∷ []) (wl0761 (lit c4)) ▸
       at 7 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CS04⁻ ∷ []) (wp0682 c4) ▸ done

  b11 : Chain (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS04 ∷ CX30 ∷ Toff214 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx2-3041 ∷ Toff304 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CCZ123 ∷ CX04 ∷ CS01 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b11 = at 5 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 4 2 (Toff214 ∷ CS04 ∷ []) (wp0683 c4) ▸
       at 3 2 (Toff214 ∷ K3 ∷ []) (wl0762 (lit c4)) ▸
       at 4 7 (Toff304 ∷ []) (wp0681 c4) ▸
       at 0 4 (Bx2-3041 ∷ []) (sym (lem-box-cP-at0213203441 c4)) ▸
       at 2 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 6 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸ done

  b12 : Chain (Bx2-3041 ∷ Toff304 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CCZ123 ∷ CX04 ∷ CS01 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx2-3041 ∷ Bx3-0412 ∷ [])
  b12 = at 4 2 (CCZ123 ∷ CS14⁻ ∷ []) (sym (wl0764 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 3 2 (Toff304 ∷ CCZ014 ∷ []) (wp0687 c4) ▸
       at 4 2 [] (wp0161 c4) ▸
       at 1 4 (Bx3-0412 ∷ []) (sym (lem-box-tQ-at0310243142 c4)) ▸ done


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


-- P-box @0210233441: 8 steps
lem-P-box-at0210233441 : Ws → ⟪ (Toff214 ∷ Bx2-0341 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-P-box-at0210233441 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Bx2-0341 ∷ Toff214 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at0210233441 c4) ▸
       at 0 2 (Toff203 ∷ Toff214 ∷ []) (sym (lem-tP-at0210233441 c4)) ▸
       at 1 2 (CCZ124 ∷ CZ14 ∷ Toff214 ∷ []) (sym (wl0766 (lit c4))) ▸
       at 3 2 (Toff203 ∷ Toff214 ∷ []) (sym (lem-tP-at0210233441 c4)) ▸
       at 4 3 (CCZ124 ∷ CZ14 ∷ []) (sym (wl0767 (lit c4))) ▸
       at 2 2 (Toff203 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF203 (lit c4)) ▸
       at 3 3 (CCZ124 ∷ []) (sym (wl0768 (lit c4))) ▸
       at 0 4 (Bx2-0341 ∷ []) (sym (lem-box-tQ-at0210233441 c4)) ▸ done


-- pairs @0210233441: 4 steps
lem-pairs-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-pairs-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 1 (Toff214 ∷ Bx2-0341 ∷ Toff214 ∷ []) (sym (lem-P-box-at0210233441 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0210233441 c4) ▸
       at 4 2 [] (wl0636 (lit c4)) ▸
       at 0 4 (Bx2-4103 ∷ []) (sym (lem-box-tQ-at0214213043 c4)) ▸ done


-- box-perm-3421 @0213203441: 2 steps
lem-box-perm-3421-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-box-perm-3421-at0213203441 c4 = run b0
  where
  b0 : Chain (Bx2-3041 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 1 (Bx2-0341 ∷ []) (lem-sym-ab-at0213203441 c4) ▸
       at 0 1 (Bx2-4103 ∷ []) (lem-pairs-at0210233441 c4) ▸ done


-- box-tQ @0314203142: 13 steps
lem-box-tQ-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0314203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4012 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl0494 (lit c4))) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl0494 (lit c4))) ▸
       at 0 2 (Toff304 ∷ CCZ034 ∷ CZ04 ∷ []) (wp0353 c4) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0314203142 c4) ▸
       at 2 4 (Toff304 ∷ []) (wp0354 c4) ▸ done


-- CXbc-box @0314203142: 17 steps
lem-CXbc-box-at0314203142 : Ws → ⟪ (CX01 ∷ Bx3-4012 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at0314203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx3-4012 ∷ CX01 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX01 ∷ CCZ023 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CCZ123 ∷ CX40 ∷ CS24 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203142 c4) ▸
       at 0 2 (Toff304 ∷ CX01 ∷ []) (wp0688 c4) ▸
       at 1 2 (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) (sym (wl0612 (lit c4))) ▸
       at 3 2 (Toff304 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp0689 c4) ▸
       at 2 2 (Toff304 ∷ CX01 ∷ []) (wp0688 c4) ▸
       at 5 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 9 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX01 ∷ CCZ023 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CCZ123 ∷ CX40 ∷ CS24 ∷ CX01 ∷ []) (Bx3-4012 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS02⁻ ∷ []) (sym (wl0611 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸
       at 4 2 (CCZ123 ∷ CCZ023 ∷ []) (wl0613 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) (sym (wl0612 (lit c4))) ▸
       at 4 3 (CX01 ∷ []) (wl0614 (lit c4)) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-tQ-at0314203142 c4)) ▸ done

  b2 : Chain (Bx3-4012 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ []) (Bx3-4012 ∷ CCZ024 ∷ [])
  b2 = at 1 3 (CCZ024 ∷ []) (sym (wp0670 c4)) ▸ done


-- CXcb-box @0314203142: 18 steps
lem-CXcb-box-at0314203142 : Ws → ⟪ (CX10 ∷ Bx3-4012 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at0314203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx3-4012 ∷ CX10 ∷ []) (Toff304 ∷ CCZ123 ∷ CX10 ∷ Toff314 ∷ CS12 ∷ CX41 ∷ Toff304 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ123 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203142 c4) ▸
       at 0 2 (Toff304 ∷ CX10 ∷ Toff314 ∷ []) (wp0690 c4) ▸
       at 2 2 (CCZ123 ∷ Toff314 ∷ CCZ124 ∷ []) (sym (wl0769 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 4 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 8 2 (Toff304 ∷ CS24 ∷ []) (wp0691 c4) ▸
       at 7 2 (Toff304 ∷ CX41 ∷ []) (wp0692 c4) ▸
       at 6 2 (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ CX10 ∷ Toff314 ∷ CS12 ∷ CX41 ∷ Toff304 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ123 ∷ CX10 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ [])
  b1 = at 5 2 (Toff304 ∷ CX41 ∷ []) (wp0692 c4) ▸
       at 4 2 (Toff304 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF304 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 3 2 (Toff304 ∷ Toff314 ∷ []) (sym (wp0667 c4)) ▸
       at 2 2 (Toff304 ∷ CX10 ∷ Toff314 ∷ []) (wp0690 c4) ▸
       at 3 3 (CX10 ∷ []) (wp0693 c4) ▸
       at 4 2 (CCZ123 ∷ CCZ124 ∷ []) (sym (wl0770 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ []) (Bx3-4012 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-tQ-at0314203142 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wp0663 c4)) ▸ done


-- SWbc-box @0314203142: 11 steps
lem-SWbc-box-at0314203142 : Ws → ⟪ (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-SWbc-box-at0314203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) (CX01 ∷ Bx3-4012 ∷ CX01 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 4 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 2 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0314203142 c4) ▸
       at 3 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸
       at 1 3 (Bx3-4012 ∷ CCZ124 ∷ []) (lem-CXcb-box-at0314203142 c4) ▸
       at 4 2 (CX01 ∷ CCZ024 ∷ []) (wp0022 c4) ▸
       at 3 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0671 c4) ▸
       at 2 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0671 c4) ▸ done

  b1 : Chain (CX01 ∷ Bx3-4012 ∷ CX01 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ []) (Bx3-4012 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (wp0694 c4) ▸
       at 0 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0314203142 c4) ▸
       at 1 2 [] (wp0135 c4) ▸ done


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


-- sym-bc @0314203142: 2 steps
lem-sym-bc-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-sym-bc-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0314203142 c4)) ▸
       at 0 3 (Bx3-4102 ∷ []) (lem-nat-SWbc-at0314203142 c4) ▸ done


-- box-perm-2314 @0310243142: 2 steps
lem-box-perm-2314-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-box-perm-2314-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 0 1 (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4) ▸
       at 0 1 (Bx3-4102 ∷ []) (lem-sym-bc-at0314203142 c4) ▸ done


-- F0-B @14213243: 62 steps
lem-F0-B-at14213243 : Ws → ⟪ (CX23 ∷ Bx2-4103 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ Bx3-4102 ∷ []) ⟫ʷ
lem-F0-B-at14213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CX23 ∷ Bx2-4103 ∷ CX23 ∷ []) (Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ CZ02 ∷ CCZ014 ∷ CCZ023 ∷ CZ02 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at0214213043 c4) ▸
       at 0 2 (Toff214 ∷ Toff314 ∷ CX23 ∷ []) (wl0771 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CZ02 ∷ CX23 ∷ []) (sym (wl0772 (lit c4))) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ CX23 ∷ []) (wl0771 (lit c4)) ▸
       at 6 3 (CCZ023 ∷ CZ02 ∷ []) (sym (wl0773 (lit c4))) ▸
       at 3 2 (Toff214 ∷ CZ02 ∷ CCZ014 ∷ []) (wp0697 c4) ▸
       at 5 2 (Toff314 ∷ CCZ014 ∷ []) (wp0698 c4) ▸
       at 4 2 (Toff314 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF314 (lit c4)) ▸ done

  b1 : Chain (Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ CZ02 ∷ CCZ014 ∷ CCZ023 ∷ CZ02 ∷ []) (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b1 = at 5 2 (CCZ014 ∷ CZ02 ∷ []) (sym (wp0699 c4)) ▸
       at 6 3 (CCZ023 ∷ []) (sym (wl0774 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Toff214 ∷ []) (wl0775 (lit c4)) ▸
       at 4 0 (CCZ023 ∷ CCZ023 ∷ []) (sym (wl0204 (lit c4))) ▸
       at 1 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-box-perm-1324-at0314213042 c4) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 0 1 (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ []) (sym (wl0776 (lit c4))) ▸ done

  b2 : Chain (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff214 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b2 = at 6 2 (CCZ034 ∷ K2⁻ ∷ []) (sym (wp0700 c4)) ▸
       at 5 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 4 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 3 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 1 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ K2 ∷ []) (sym (wp0701 c4)) ▸
       at 1 7 (Toff214 ∷ []) (wl0776 (lit c4)) ▸ done

  b3 : Chain (CCZ034 ∷ Toff214 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff312 ∷ K2 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b3 = at 1 2 (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) (wl0777 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0702 c4)) ▸
       at 2 1 (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ []) (sym (wl0776 (lit c4))) ▸
       at 8 2 (CCZ034 ∷ K2⁻ ∷ []) (sym (wp0700 c4)) ▸
       at 7 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 6 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸ done

  b4 : Chain (CCZ034 ∷ Toff312 ∷ K2 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b4 = at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ K2 ∷ []) (sym (wp0701 c4)) ▸
       at 3 7 (Toff214 ∷ []) (wl0776 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸ done

  b5 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (Bx3-4102 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b5 = at 5 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (Toff312 ∷ Toff314 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 3 2 (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) (wl0777 (lit c4)) ▸
       at 4 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 0 1 (Bx3-4102 ∷ []) (sym (lem-box-perm-1324-at0314213042 c4)) ▸
       at 2 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b6 : Chain (Bx3-4102 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (Bx3-4102 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  b6 = at 6 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CX04 ∷ []) (sym (wp0684 c4)) ▸
       at 4 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ CX04 ∷ []) (sym (wp0684 c4)) ▸
       at 2 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 3 2 (Toff214 ∷ CCZ014 ∷ []) (wp0686 c4) ▸
       at 4 2 [] (wp0161 c4) ▸ done

  b7 : Chain (Bx3-4102 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ [])
  b7 = at 1 4 (Bx2-4103 ∷ []) (sym (lem-box-tQ-at0214213043 c4)) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-box-perm-3124-at0314213042 c4) ▸
       at 1 1 (Bx2-3041 ∷ []) (lem-box-perm-4312-at0214213043 c4) ▸
       at 0 2 (Bx2-3041 ∷ Bx3-0412 ∷ []) (lem-box-box-4-at0310243142 c4) ▸
       at 0 1 (Bx2-4103 ∷ []) (lem-box-perm-3421-at0213203441 c4) ▸
       at 1 1 (Bx3-4102 ∷ []) (lem-box-perm-2314-at0310243142 c4) ▸ done


-- tP @0314213042: 7 steps
lem-tP-at0314213042 : Ws → ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-tP-at0314213042 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0781 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (sym (wl0782 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at0314213042 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff302 ∷ []) (wl0782 (lit c4)) ▸
       at 1 3 (Toff314 ∷ []) (wl0781 (lit c4)) ▸ done


-- VPQ @0314213042: 14 steps
lem-VPQ-at0314213042 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at0314213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (sym (wl0783 (lit c4))) ▸
       at 4 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (sym (wl0784 (lit c4))) ▸
       at 3 2 (CS02⁻ ∷ S3⁻ ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S))) ▸
       at 2 2 (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ S3 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S))) ▸
       at 0 2 (CS02⁻ ∷ CS14⁻ ∷ []) (sym (wp0703 c4)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213042 c4) ▸ done

  b1 : Chain (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS14⁻ ∷ []) (wl0785 (lit c4)) ▸
       at 2 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS14⁻ ∷ []) (wl0786 (lit c4)) ▸
       at 0 4 (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4)) ▸
       at 2 4 (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4)) ▸ done


-- QVQ @0314213042: 3 steps
lem-QVQ-at0314213042 : Ws → ⟪ (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-QVQ-at0314213042 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ [])
  b0 = at 0 0 (Toff302 ∷ Toff302 ∷ []) (sym (wl0787 (lit c4))) ▸
       at 1 4 (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at0314213042 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done

