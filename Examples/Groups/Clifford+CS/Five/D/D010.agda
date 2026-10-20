{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D010 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0159 ; wl0171 ; wl0173 ; wl0179 ; wl0199 ; wl0201 ; wl0202 ; wl0233 ; wl0327 ; wl0334 ; wl0482 ; wl0490 ; wl0492 ; wl0560 ; wl0611 ; wl0612 ; wl0613 ; wl0614 ; wl0616 ; wl0617 ; wl0620 ; wl0621 ; wl0629 ; wl0630 ; wl0631 ; wl0632 ; wl0633 ; wl0634 ; wl0644 ; wl0645 ; wl0646 ; wl0647 ; wl0648 ; wl0668 ; wl0669 ; wl0670 ; wl0671 ; wl0672 ; wl0673 ; wl0674 ; wl0675 ; wl0676 ; wl0677 ; wp0007 ; wp0028 ; wp0048 ; wp0050 ; wp0072 ; wp0077 ; wp0161 ; wp0299 ; wp0320 ; wp0392 ; wp0394 ; wp0395 ; wp0450 ; wp0454 ; wp0496 ; wp0497 ; wp0499 ; wp0502 ; wp0503 ; wp0505 ; wp0513 ; wp0514 ; wp0519 ; wp0520 ; wp0521 ; wp0522 ; wp0523 ; wp0524 ; wp0525 ; wp0526 ; wp0534 ; wp0535 ; wp0541 ; wp0542 ; wp0543 ; wp0544 ; wp0545 ; wp0546 ; wp0547 ; wp0548 ; wp0549 ; wp0550 ; wl0158 ; wl0162 ; wl0184 ; wl0207 ; wl0225 ; wl0227 ; wl0228 ; wl0254 ; wl0257 ; wl0270 ; wl0300 ; wl0305 ; wl0312 ; wl0315 ; wl0341 ; wl0420 ; wl0421 ; wl0424 ; wl0491 ; wl0508 ; wl0682 ; wl0683 ; wl0684 ; wl0694 ; wl0695 ; wl0696 ; wl0698 ; wl0699 ; wl0701 ; wl0702 ; wl0703 ; wl0704 ; wl0705 ; wl0706 ; wl0707 ; wp0001 ; wp0003 ; wp0005 ; wp0079 ; wp0120 ; wp0352 ; wp0357 ; wp0559 ; wp0560 ; wp0561 ; wp0562 ; wp0563 ; wp0564 ; wp0565 ; wp0566 ; wp0567 ; wp0568 ; wp0572 ; wp0573 ; wp0574 ; wp0575 ; wp0576 ; wp0577 ; wp0578 ; wp0579 ; wp0580 ; wp0581 ; wp0587 ; wp0588 ; wp0589 ; wp0590 ; wp0591 ; wp0592 ; wp0593 ; wl0193 ; wl0195 ; wl0196 ; wl0197 ; wl0441 ; wl0751 ; wl0752 ; wl0753 ; wl0754 ; wl0761 ; wl0766 ; wl0767 ; wl0768 ; wl0769 ; wl0770 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wp0021 ; wp0032 ; wp0034 ; wp0035 ; wp0036 ; wp0042 ; wp0653 ; wp0662 ; wp0663 ; wp0664 ; wp0665 ; wp0666 ; wp0667 ; wp0668 ; wp0669 ; wp0670 ; wp0688 ; wp0689 ; wp0690 ; wp0691 ; wp0692 ; wp0693 ; wp0703 ; wl0256 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0442 ; wl0803 ; wl0804 ; wl0805 ; wl0825 ; wl0826 ; wl0827 ; wl0828 ; wl0829 ; wl0830 ; wl0831 ; wl0832 ; wl0833 ; wl0834 ; wl0848 ; wl0849 ; wl0850 ; wl0851 ; wl0852 ; wl0853 ; wl0858 ; wl0859 ; wl0860 ; wl0861 ; wl0862 ; wl0863 ; wl0866 ; wl0867 ; wl0868 ; wl0872 ; wl0873 ; wl0874 ; wl0875 ; wp0038 ; wp0054 ; wp0062 ; wp0064 ; wp0075 ; wp0076 ; wp0090 ; wp0095 ; wp0109 ; wp0182 ; wp0186 ; wp0187 ; wp0189 ; wp0272 ; wp0285 ; wp0298 ; wp0707 ; wp0708 ; wp0709 ; wp0710 ; wp0711 ; wp0717 ; wp0718 ; wp0720 ; wp0721 ; wp0722 ; wp0723 ; wp0724 ; wp0725 ; wp0726 ; wp0727 ; wp0728 ; wp0735 ; wp0736 ; wp0737 ; wp0744 ; wp0745 ; wp0746 ; wp0747 ; wp0748 ; wp0749 ; wl0166 ; wl0323 ; wl0912 ; wl0913 ; wl0914 ; wl0917 ; wl0918 ; wl0919 ; wl0920 ; wl0921 ; wl0922 ; wl0942 ; wl0944 ; wl0945 ; wl0946 ; wl0947 ; wl0948 ; wp0039 ; wp0053 ; wp0115 ; wp0142 ; wp0179 ; wp0282 ; wp0283 ; wp0341 ; wp0756 ; wp0757 ; wp0758 ; wp0759 ; wp0760 ; wp0761 ; wp0762 ; wp0763 ; wp0768 ; wl0176 ; wl0177 ; wl0178 ; wl0271 ; wl0272 ; wl0274 ; wl0275 ; wl0277 ; wl0961 ; wl0987 ; wl0988 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0063 ; wp0066 ; wp0070 ; wp0124 ; wp0310 ; wp0778 ; wp0779 ; wp0780 ; wp0781 ; wp0782 ; wp0785 ; wp0792 ; wp0793 ; wp0794 ; wp0795 ; wl0221 ; wl0252 ; wl1007 ; wl1018 ; wl1019 ; wp0060 ; wp0067 ; wp0071 ; wp0082 ; wp0158 ; wp0159 ; wp0160 ; wp0263 ; wp0270 ; wp0807 ; wp0808 ; wp0809 ; wp0810 ; wp0811 ; wp0825 ; wp0826 ; wp0827 ; wp0899 ; wp0900 ; wl0289 ; wl1119 ; wl1120 ; wl1121 ; wl1132 ; wp0046 ; wp0047 ; wp0911 ; wp0912 ; wp0913 ; wp0914 ; wp0915 ; wp0920 ; wp0921 ; wp0922)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-CXbc-box-at0213243140 ; lem-CXcb-box-at0213243140 ; lem-VPQ-at0210213443 ; lem-VPQ-at0220 ; lem-VPQ-at032032 ; lem-VPQ-at14233241 ; lem-box-tQ-at0210233441 ; lem-box-tQ-at0210243143 ; lem-box-tQ-at0214203143 ; lem-box-tQ-at0214213043 ; lem-box-tQ-at022330 ; lem-box-tQ-at0312213440 ; lem-box-tQ-at0312243140 ; lem-box-tQ-at0314203142 ; lem-box-tQ-at0314213042 ; lem-box-tQ-at122331 ; lem-box-tQ-at12233441 ; lem-box-tQ-at122441 ; lem-box-tQ-at132132 ; lem-box-tQ-at1331 ; lem-box-tQ-at14213243 ; lem-box-tQ-at143143 ; lem-box-tQ-at1441 ; lem-box-tQ-at2332 ; lem-box-tQ-at243243 ; lem-tP-at0210233441 ; lem-tP-at0210243143 ; lem-tP-at0213203441 ; lem-tP-at0214213043 ; lem-tP-at0312243140 ; lem-tP-at0314213042 ; lem-tP-at12213443 ; lem-tP-at12233441 ; lem-tP-at122441 ; lem-tP-at143143 ; lem-tP-at233442 ; lem-tP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-CXbc-box-at0220 ; lem-CXbc-box-at03102132 ; lem-CXcb-box-at0220 ; lem-CXcb-box-at03102132 ; lem-VPQ-at0213243140 ; lem-box-tQ-at0213213440 ; lem-box-tQ-at02233440 ; lem-box-tQ-at022440 ; lem-tP-at0214203143 ; lem-tP-at022330 ; lem-tP-at022440 ; lem-tP-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-TOFF024 ; lem-comm-CS14-TOFF023 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd12-TOFF034 ; lem-comm-CSd13-TOFF024 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-TOFF014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX04-CCZ123 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-CX21-CCZ034 ; lem-comm-CX23-CCZ014 ; lem-comm-CX24-CCZ013 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014 ; lem-comm-CX42-CCZ013 ; lem-comm-CZ04-TOFF213 ; lem-comm-CZ14-TOFF023 ; lem-comm-TOFF013-CSd24 ; lem-comm-TOFF014-CSd23 ; lem-comm-TOFF024-CSd13 ; lem-comm-TOFF204-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS02-TOFF314 ; lem-comm-CS03-TOFF214 ; lem-comm-CS04-CCZ123 ; lem-comm-CS04-TOFF213 ; lem-comm-CS04-TOFF312 ; lem-comm-CS12-TOFF304 ; lem-comm-CS13-TOFF204 ; lem-comm-CS23-TOFF014 ; lem-comm-CSd02-TOFF314 ; lem-comm-CSd03-TOFF214 ; lem-comm-CSd04-CCZ123 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-TOFF304 ; lem-comm-CSd13-TOFF204 ; lem-comm-CSd14-TOFF203 ; lem-comm-CSd14-TOFF302 ; lem-comm-CSd24-TOFF301 ; lem-comm-CX40-CCZ123 ; lem-comm-CX41-CCZ023 ; lem-comm-CZ13-TOFF024 ; lem-comm-CZ13-TOFF204 ; lem-comm-CZ14-TOFF203 ; lem-comm-CZ14-TOFF302 ; lem-comm-CZ23-TOFF014 ; lem-comm-TOFF213-CSd04 ; lem-comm-TOFF214-CSd03 ; lem-comm-TOFF314-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CSd14 ; lem-comm-TOFF203-CSd14)

-- VPQ @0214213043: 14 steps
lem-VPQ-at0214213043 : Ws → ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at0214213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (sym (wl0629 (lit c4))) ▸
       at 4 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (sym (wl0630 (lit c4))) ▸
       at 3 2 (CS03⁻ ∷ S2⁻ ∷ []) (sym (wl0631 (lit c4))) ▸
       at 2 2 (CS03⁻ ∷ Toff214 ∷ []) (lem-comm-TOFF214-CSd03 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ S2 ∷ []) (sym (wl0632 (lit c4))) ▸
       at 0 2 (CS03⁻ ∷ CS14⁻ ∷ []) (sym (wp0514 c4)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at0214213043 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS14⁻ ∷ []) (wl0633 (lit c4)) ▸
       at 2 2 (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS14⁻ ∷ []) (wl0634 (lit c4)) ▸
       at 0 4 (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4)) ▸
       at 2 4 (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4)) ▸ done

-- VPQ @0210233441: 14 steps
lem-VPQ-at0210233441 : Ws → ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at0210233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (sym (wl0630 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (sym (wl0629 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S2⁻ ∷ []) (sym (wl0634 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff203 ∷ []) (lem-comm-TOFF203-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S2 ∷ []) (sym (wl0633 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS03⁻ ∷ []) (wp0514 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0210233441 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS03⁻ ∷ []) (wl0632 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS03⁻ ∷ []) (wl0631 (lit c4)) ▸
       at 0 4 (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4)) ▸
       at 2 4 (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4)) ▸ done

-- CXbc-box @122441: 17 steps
lem-CXbc-box-at122441 : Ws → ⟪ (CX43 ∷ Bx0-2431 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx0-2431 ∷ CX43 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX43 ∷ CCZ014 ∷ CS14 ∷ CX24 ∷ CS14⁻ ∷ CCZ013 ∷ CX24 ∷ CS12 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ CX43 ∷ []) (wp0519 c4) ▸
       at 1 2 (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (sym (wp0392 c4)) ▸
       at 3 2 (Toff024 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0520 c4) ▸
       at 2 2 (Toff024 ∷ CX43 ∷ []) (wp0519 c4) ▸
       at 5 1 (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (wl0644 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ CS12 ∷ []) (sym (wl0645 (lit c4))) ▸
       at 8 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX43 ∷ CCZ014 ∷ CS14 ∷ CX24 ∷ CS14⁻ ∷ CCZ013 ∷ CX24 ∷ CS12 ∷ CX43 ∷ []) (Bx0-2431 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS14⁻ ∷ []) (sym (wp0521 c4)) ▸
       at 6 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0644 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CCZ014 ∷ []) (sym (wp0394 c4)) ▸
       at 3 2 (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (sym (wp0392 c4)) ▸
       at 4 3 (CX43 ∷ []) (wp0395 c4) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done

  b2 : Chain (Bx0-2431 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ []) (Bx0-2431 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wl0646 (lit c4))) ▸ done

-- CXcb-box @122441: 18 steps
lem-CXcb-box-at122441 : Ws → ⟪ (CX34 ∷ Bx0-2431 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx0-2431 ∷ CX34 ∷ []) (Toff024 ∷ CCZ013 ∷ CX34 ∷ Toff023 ∷ CS13 ∷ CX23 ∷ Toff024 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ CCZ013 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ CX34 ∷ Toff023 ∷ []) (wp0522 c4) ▸
       at 2 2 (CCZ013 ∷ Toff023 ∷ CCZ123 ∷ []) (sym (wl0647 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸
       at 4 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 8 2 (Toff024 ∷ CS12 ∷ []) (wp0524 c4) ▸
       at 7 2 (Toff024 ∷ CX23 ∷ []) (wp0525 c4) ▸
       at 6 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CX34 ∷ Toff023 ∷ CS13 ∷ CX23 ∷ Toff024 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ CCZ013 ∷ CX34 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ [])
  b1 = at 5 2 (Toff024 ∷ CX23 ∷ []) (wp0525 c4) ▸
       at 4 2 (Toff024 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF024 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸
       at 3 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 2 2 (Toff024 ∷ CX34 ∷ Toff023 ∷ []) (wp0522 c4) ▸
       at 3 3 (CX34 ∷ []) (wp0526 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ123 ∷ []) (sym (wl0327 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0648 (lit c4))) ▸ done

-- VPQ @12233441: 14 steps
lem-VPQ-at12233441 : Ws → ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at12233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (sym (wl0201 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (sym (wp0050 c4)) ▸
       at 3 2 (CS14⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS14⁻ ∷ CS23⁻ ∷ []) (sym (wl0202 (lit c4))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at12233441 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS23⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑))) ▸
       at 2 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS23⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑))) ▸
       at 0 4 (Toff014 ∷ CCZ014 ∷ []) (wp0050 c4) ▸
       at 2 4 (Toff023 ∷ CCZ023 ∷ []) (wl0201 (lit c4)) ▸ done

-- CSu-box-2 @0210243143: 17 steps
lem-CSu-box-2-at0210243143 : Ws → ⟪ (CS24 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS24 ∷ []) ⟫ʷ
lem-CSu-box-2-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS24 ∷ Bx2-0413 ∷ []) (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ []) (wp0534 c4) ▸
       at 3 1 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp0450 c4) ▸
       at 7 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX20 ∷ []) (sym (wl0482 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ CX20 ∷ []) (sym (wl0482 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS24 ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (sym (wp0450 c4)) ▸
       at 2 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 4 2 (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) (wp0028 c4) ▸
       at 3 2 (Toff204 ∷ CS04 ∷ []) (wp0454 c4) ▸
       at 2 2 (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ []) (wp0534 c4) ▸
       at 3 6 (CS24 ∷ []) (wp0535 c4) ▸
       at 3 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS24 ∷ []) (Bx2-0413 ∷ CS24 ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done

-- CXbc-box @14213243: 17 steps
lem-CXbc-box-at14213243 : Ws → ⟪ (CX12 ∷ Bx0-4123 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at14213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx0-4123 ∷ CX12 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX12 ∷ CCZ013 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ023 ∷ CX41 ∷ CS34 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at14213243 c4) ▸
       at 0 2 (Toff014 ∷ CX12 ∷ []) (wp0541 c4) ▸
       at 1 2 (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (sym (wl0668 (lit c4))) ▸
       at 3 2 (Toff014 ∷ CCZ013 ∷ CCZ134 ∷ []) (wp0542 c4) ▸
       at 2 2 (Toff014 ∷ CX12 ∷ []) (wp0541 c4) ▸
       at 5 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS34 ∷ []) (sym (wp0543 c4)) ▸
       at 8 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX12 ∷ CCZ013 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ023 ∷ CX41 ∷ CS34 ∷ CX12 ∷ []) (Bx0-4123 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS13⁻ ∷ []) (sym (wl0669 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS13 ∷ []) (sym (wl0670 (lit c4))) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ CCZ013 ∷ []) (wl0671 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (sym (wl0668 (lit c4))) ▸
       at 4 3 (CX12 ∷ []) (wl0672 (lit c4)) ▸
       at 0 4 (Bx0-4123 ∷ []) (sym (lem-box-tQ-at14213243 c4)) ▸ done

  b2 : Chain (Bx0-4123 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ []) (Bx0-4123 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wl0673 (lit c4))) ▸ done

-- CXcb-box @14213243: 18 steps
lem-CXcb-box-at14213243 : Ws → ⟪ (CX21 ∷ Bx0-4123 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at14213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx0-4123 ∷ CX21 ∷ []) (Toff014 ∷ CCZ023 ∷ CX21 ∷ Toff024 ∷ CS23 ∷ CX42 ∷ Toff014 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ CCZ023 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at14213243 c4) ▸
       at 0 2 (Toff014 ∷ CX21 ∷ Toff024 ∷ []) (wp0544 c4) ▸
       at 2 2 (CCZ023 ∷ Toff024 ∷ CCZ234 ∷ []) (sym (wp0545 c4)) ▸
       at 1 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸
       at 4 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0675 (lit c4)) ▸
       at 8 2 (Toff014 ∷ CS34 ∷ []) (wp0546 c4) ▸
       at 7 2 (Toff014 ∷ CX42 ∷ []) (wp0547 c4) ▸
       at 6 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CX21 ∷ Toff024 ∷ CS23 ∷ CX42 ∷ Toff014 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ CCZ023 ∷ CX21 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ [])
  b1 = at 5 2 (Toff014 ∷ CX42 ∷ []) (wp0547 c4) ▸
       at 4 2 (Toff014 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF014 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0675 (lit c4))) ▸
       at 3 2 (Toff014 ∷ Toff024 ∷ []) (sym (wp0548 c4)) ▸
       at 2 2 (Toff014 ∷ CX21 ∷ Toff024 ∷ []) (wp0544 c4) ▸
       at 3 3 (CX21 ∷ []) (wp0549 c4) ▸
       at 4 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 3 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ []) (Bx0-4123 ∷ CCZ234 ∷ [])
  b2 = at 0 4 (Bx0-4123 ∷ []) (sym (lem-box-tQ-at14213243 c4)) ▸
       at 1 3 (CCZ234 ∷ []) (sym (wl0676 (lit c4))) ▸ done

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

-- QVQ @0210213443: 3 steps
lem-QVQ-at0210213443 : Ws → ⟪ (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-QVQ-at0210213443 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ [])
  b0 = at 0 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 1 4 (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at0210213443 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done

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

-- QVQ @14233241: 3 steps
lem-QVQ-at14233241 : Ws → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at14233241 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 1 4 (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at14233241 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done

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

-- t-cP @0314213042: 5 steps
lem-t-cP-at0314213042 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-t-cP-at0314213042 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ [])
  b0 = at 0 2 (CCZ134 ∷ Toff314 ∷ CZ14 ∷ []) (sym (wl0803 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF302 (lit c4)) ▸
       at 1 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213042 c4) ▸
       at 2 3 (CCZ134 ∷ Toff314 ∷ []) (sym (wl0804 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213042 c4) ▸ done

-- CXbc-box @0214213043: 17 steps
lem-CXbc-box-at0214213043 : Ws → ⟪ (CX10 ∷ Bx2-4103 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at0214213043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx2-4103 ∷ CX10 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CX10 ∷ CCZ123 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ023 ∷ CX41 ∷ CS34 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at0214213043 c4) ▸
       at 0 2 (Toff214 ∷ CX10 ∷ []) (wp0707 c4) ▸
       at 1 2 (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) (sym (wl0751 (lit c4))) ▸
       at 3 2 (Toff214 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0805 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CX10 ∷ []) (wp0707 c4) ▸
       at 5 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS34 ∷ []) (sym (wp0543 c4)) ▸
       at 8 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CX10 ∷ CCZ123 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ023 ∷ CX41 ∷ CS34 ∷ CX10 ∷ []) (Bx2-4103 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS13⁻ ∷ []) (sym (wl0669 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS13 ∷ []) (sym (wl0670 (lit c4))) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ CCZ123 ∷ []) (sym (wl0613 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) (sym (wl0751 (lit c4))) ▸
       at 4 3 (CX10 ∷ []) (wl0753 (lit c4)) ▸
       at 0 4 (Bx2-4103 ∷ []) (sym (lem-box-tQ-at0214213043 c4)) ▸ done

  b2 : Chain (Bx2-4103 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ []) (Bx2-4103 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wp0505 c4)) ▸ done

-- CXcb-box @0214213043: 18 steps
lem-CXcb-box-at0214213043 : Ws → ⟪ (CX01 ∷ Bx2-4103 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at0214213043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx2-4103 ∷ CX01 ∷ []) (Toff214 ∷ CCZ023 ∷ CX01 ∷ Toff204 ∷ CS03 ∷ CX40 ∷ Toff214 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CCZ023 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at0214213043 c4) ▸
       at 0 2 (Toff214 ∷ CX01 ∷ Toff204 ∷ []) (wp0708 c4) ▸
       at 2 2 (CCZ023 ∷ Toff204 ∷ CCZ034 ∷ []) (sym (wp0709 c4)) ▸
       at 1 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 4 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 8 2 (Toff214 ∷ CS34 ∷ []) (wl0761 (lit c4)) ▸
       at 7 2 (Toff214 ∷ CX40 ∷ []) (wp0710 c4) ▸
       at 6 2 (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 (lit c4)) ▸ done

  b1 : Chain (Toff214 ∷ CCZ023 ∷ CX01 ∷ Toff204 ∷ CS03 ∷ CX40 ∷ Toff214 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CCZ023 ∷ CX01 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ [])
  b1 = at 5 2 (Toff214 ∷ CX40 ∷ []) (wp0710 c4) ▸
       at 4 2 (Toff214 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF214 (lit c4)) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 3 2 (Toff214 ∷ Toff204 ∷ []) (wp0503 c4) ▸
       at 2 2 (Toff214 ∷ CX01 ∷ Toff204 ∷ []) (wp0708 c4) ▸
       at 3 3 (CX01 ∷ []) (wp0711 c4) ▸
       at 4 2 (CCZ023 ∷ CCZ034 ∷ []) (sym (wp0575 c4)) ▸
       at 3 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸ done

  b2 : Chain (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ []) (Bx2-4103 ∷ CCZ034 ∷ [])
  b2 = at 0 4 (Bx2-4103 ∷ []) (sym (lem-box-tQ-at0214213043 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (sym (wp0499 c4)) ▸ done

-- P-box @243243: 8 steps
lem-P-box-at243243 : Ws → ⟪ (Toff023 ∷ Bx0-1423 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-P-box-at243243 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Bx0-1423 ∷ Toff023 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (Toff014 ∷ Toff023 ∷ []) (sym (lem-tP-at243243 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ23 ∷ Toff023 ∷ []) (sym (wl0825 (lit c4))) ▸
       at 3 2 (Toff014 ∷ Toff023 ∷ []) (sym (lem-tP-at243243 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ23 ∷ []) (sym (wl0826 (lit c4))) ▸
       at 2 2 (Toff014 ∷ CZ23 ∷ []) (lem-comm-CZ23-TOFF014 (lit c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wl0827 (lit c4))) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸ done

-- CXbc-box @1331: 17 steps
lem-CXbc-box-at1331 : Ws → ⟪ (CX21 ∷ Bx0-3214 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at1331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx0-3214 ∷ CX21 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX21 ∷ CCZ024 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ014 ∷ CX32 ∷ CS34 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at1331 c4) ▸
       at 0 2 (Toff023 ∷ CX21 ∷ []) (wl0828 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) (sym (wp0720 c4)) ▸
       at 3 2 (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp0721 c4) ▸
       at 2 2 (Toff023 ∷ CX21 ∷ []) (wl0828 (lit c4)) ▸
       at 5 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0829 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 8 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX21 ∷ CCZ024 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ014 ∷ CX32 ∷ CS34 ∷ CX21 ∷ []) (Bx0-3214 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 6 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0829 (lit c4))) ▸
       at 4 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 3 2 (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) (sym (wp0720 c4)) ▸
       at 4 3 (CX21 ∷ []) (wp0723 c4) ▸
       at 0 4 (Bx0-3214 ∷ []) (sym (lem-box-tQ-at1331 c4)) ▸ done

  b2 : Chain (Bx0-3214 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ []) (Bx0-3214 ∷ CCZ234 ∷ [])
  b2 = at 1 3 (CCZ234 ∷ []) (sym (wl0676 (lit c4))) ▸ done

-- CXcb-box @1331: 18 steps
lem-CXcb-box-at1331 : Ws → ⟪ (CX12 ∷ Bx0-3214 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at1331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx0-3214 ∷ CX12 ∷ []) (Toff023 ∷ CCZ014 ∷ CX12 ∷ Toff013 ∷ CS14 ∷ CX31 ∷ Toff023 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ014 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at1331 c4) ▸
       at 0 2 (Toff023 ∷ CX12 ∷ Toff013 ∷ []) (wl0830 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ Toff013 ∷ CCZ134 ∷ []) (sym (wp0724 c4)) ▸
       at 1 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CS34 ∷ []) (wp0725 c4) ▸
       at 7 2 (Toff023 ∷ CX31 ∷ []) (wl0832 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4)) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ CX12 ∷ Toff013 ∷ CS14 ∷ CX31 ∷ Toff023 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ014 ∷ CX12 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ [])
  b1 = at 5 2 (Toff023 ∷ CX31 ∷ []) (wl0832 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 3 2 (Toff023 ∷ Toff013 ∷ []) (wl0833 (lit c4)) ▸
       at 2 2 (Toff023 ∷ CX12 ∷ Toff013 ∷ []) (wl0830 (lit c4)) ▸
       at 3 3 (CX12 ∷ []) (wl0834 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 3 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ []) (Bx0-3214 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-3214 ∷ []) (sym (lem-box-tQ-at1331 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wl0673 (lit c4))) ▸ done

-- QVQ @032032: 3 steps
lem-QVQ-at032032 : Ws → ⟪ (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-QVQ-at032032 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ [])
  b0 = at 0 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 1 4 (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at032032 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done

-- CXbc-box @0312243140: 17 steps
lem-CXbc-box-at0312243140 : Ws → ⟪ (CX41 ∷ Bx3-2410 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at0312243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx3-2410 ∷ CX41 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX41 ∷ CCZ034 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CCZ013 ∷ CX24 ∷ CS02 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243140 c4) ▸
       at 0 2 (Toff324 ∷ CX41 ∷ []) (wl0848 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) (sym (wp0182 c4)) ▸
       at 3 2 (Toff324 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0726 c4) ▸
       at 2 2 (Toff324 ∷ CX41 ∷ []) (wl0848 (lit c4)) ▸
       at 5 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0075 c4) ▸
       at 9 2 (CCZ013 ∷ CS02 ∷ []) (sym (wl0225 (lit c4))) ▸
       at 8 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX41 ∷ CCZ034 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CCZ013 ∷ CX24 ∷ CS02 ∷ CX41 ∷ []) (Bx3-2410 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS04⁻ ∷ []) (sym (wp0076 c4)) ▸
       at 6 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0075 c4)) ▸
       at 4 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 3 2 (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) (sym (wp0182 c4)) ▸
       at 4 3 (CX41 ∷ []) (wp0187 c4) ▸
       at 0 4 (Bx3-2410 ∷ []) (sym (lem-box-tQ-at0312243140 c4)) ▸ done

  b2 : Chain (Bx3-2410 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ []) (Bx3-2410 ∷ CCZ024 ∷ [])
  b2 = at 1 3 (CCZ024 ∷ []) (sym (wp0727 c4)) ▸ done

-- CXcb-box @0312243140: 18 steps
lem-CXcb-box-at0312243140 : Ws → ⟪ (CX14 ∷ Bx3-2410 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0312243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx3-2410 ∷ CX14 ∷ []) (Toff324 ∷ CCZ013 ∷ CX14 ∷ Toff312 ∷ CS01 ∷ CX21 ∷ Toff324 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ CCZ013 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243140 c4) ▸
       at 0 2 (Toff324 ∷ CX14 ∷ Toff312 ∷ []) (wl0849 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸
       at 4 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0270 (lit c4)) ▸
       at 8 2 (Toff324 ∷ CS02 ∷ []) (wp0298 c4) ▸
       at 7 2 (Toff324 ∷ CX21 ∷ []) (wl0851 (lit c4)) ▸
       at 6 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ CX14 ∷ Toff312 ∷ CS01 ∷ CX21 ∷ Toff324 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ CCZ013 ∷ CX14 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ [])
  b1 = at 5 2 (Toff324 ∷ CX21 ∷ []) (wl0851 (lit c4)) ▸
       at 4 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0270 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 2 2 (Toff324 ∷ CX14 ∷ Toff312 ∷ []) (wl0849 (lit c4)) ▸
       at 3 3 (CX14 ∷ []) (wl0853 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CCZ012 ∷ []) (wl0704 (lit c4)) ▸
       at 3 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸ done

  b2 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ []) (Bx3-2410 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-2410 ∷ []) (sym (lem-box-tQ-at0312243140 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wp0728 c4)) ▸ done

-- CXbc-box @0312213440: 17 steps
lem-CXbc-box-at0312213440 : Ws → ⟪ (CX14 ∷ Bx3-2140 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at0312213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx3-2140 ∷ CX14 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX14 ∷ CCZ013 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CCZ034 ∷ CX21 ∷ CS02 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0312213440 c4) ▸
       at 0 2 (Toff312 ∷ CX14 ∷ []) (wl0858 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) (sym (wp0735 c4)) ▸
       at 3 2 (Toff312 ∷ CCZ013 ∷ CCZ012 ∷ []) (wl0859 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CX14 ∷ []) (wl0858 (lit c4)) ▸
       at 5 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0270 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 8 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX14 ∷ CCZ013 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CCZ034 ∷ CX21 ∷ CS02 ∷ CX14 ∷ []) (Bx3-2140 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS01⁻ ∷ []) (sym (wp0120 c4)) ▸
       at 6 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0270 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ013 ∷ []) (wp0186 c4) ▸
       at 3 2 (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) (sym (wp0735 c4)) ▸
       at 4 3 (CX14 ∷ []) (wp0736 c4) ▸
       at 0 4 (Bx3-2140 ∷ []) (sym (lem-box-tQ-at0312213440 c4)) ▸ done

  b2 : Chain (Bx3-2140 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ []) (Bx3-2140 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (sym (wp0728 c4)) ▸ done

-- CXcb-box @0312213440: 18 steps
lem-CXcb-box-at0312213440 : Ws → ⟪ (CX41 ∷ Bx3-2140 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at0312213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx3-2140 ∷ CX41 ∷ []) (Toff312 ∷ CCZ034 ∷ CX41 ∷ Toff324 ∷ CS04 ∷ CX24 ∷ Toff312 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ CCZ034 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0312213440 c4) ▸
       at 0 2 (Toff312 ∷ CX41 ∷ Toff324 ∷ []) (wl0860 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) (sym (wp0737 c4)) ▸
       at 1 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 4 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0075 c4) ▸
       at 8 2 (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX24 ∷ []) (wl0862 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4)) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ CX41 ∷ Toff324 ∷ CS04 ∷ CX24 ∷ Toff312 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ CCZ034 ∷ CX41 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ [])
  b1 = at 5 2 (Toff312 ∷ CX24 ∷ []) (wl0862 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF312 (lit c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0075 c4)) ▸
       at 3 2 (Toff312 ∷ Toff324 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 2 2 (Toff312 ∷ CX41 ∷ Toff324 ∷ []) (wl0860 (lit c4)) ▸
       at 3 3 (CX41 ∷ []) (wl0863 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 3 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸ done

  b2 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ []) (Bx3-2140 ∷ CCZ024 ∷ [])
  b2 = at 0 4 (Bx3-2140 ∷ []) (sym (lem-box-tQ-at0312213440 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (sym (wp0727 c4)) ▸ done

-- P-box @0312243140: 8 steps
lem-P-box-at0312243140 : Ws → ⟪ (Toff301 ∷ Bx3-2410 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-P-box-at0312243140 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx3-2410 ∷ Toff301 ∷ []) (Bx3-2410 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243140 c4) ▸
       at 0 2 (Toff324 ∷ Toff301 ∷ []) (sym (lem-tP-at0312243140 c4)) ▸
       at 1 2 (CCZ013 ∷ CZ01 ∷ Toff301 ∷ []) (sym (wl0866 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (sym (lem-tP-at0312243140 c4)) ▸
       at 4 3 (CCZ013 ∷ CZ01 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 2 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 3 (CCZ013 ∷ []) (sym (wl0868 (lit c4))) ▸
       at 0 4 (Bx3-2410 ∷ []) (sym (lem-box-tQ-at0312243140 c4)) ▸ done

-- VPQ @0312243140: 14 steps
lem-VPQ-at0312243140 : Ws → ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0312243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (sym (wl0438 (lit c4))) ▸
       at 4 2 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (sym (wl0437 (lit c4))) ▸
       at 3 2 (CS01⁻ ∷ S3⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((S • S • S) ↑))) ▸
       at 2 2 (CS01⁻ ∷ Toff324 ∷ []) (sym (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 1 2 (CS01⁻ ∷ S3 ∷ []) (sym (c₂ (CS • CS • CS) (S ↑))) ▸
       at 0 2 (CS01⁻ ∷ CS24⁻ ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at0312243140 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS24⁻ ∷ []) (wl0440 (lit c4)) ▸
       at 2 2 (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS24⁻ ∷ []) (wl0439 (lit c4)) ▸
       at 0 4 (Toff301 ∷ CCZ013 ∷ []) (wl0437 (lit c4)) ▸
       at 2 4 (Toff324 ∷ CCZ234 ∷ []) (wl0438 (lit c4)) ▸ done

-- CXbc-box @132132: 17 steps
lem-CXbc-box-at132132 : Ws → ⟪ (CX12 ∷ Bx0-3124 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx0-3124 ∷ CX12 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX12 ∷ CCZ014 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at132132 c4) ▸
       at 0 2 (Toff013 ∷ CX12 ∷ []) (wl0872 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) (sym (wp0744 c4)) ▸
       at 3 2 (Toff013 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0745 c4) ▸
       at 2 2 (Toff013 ∷ CX12 ∷ []) (wl0872 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX12 ∷ CCZ014 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ CX12 ∷ []) (Bx0-3124 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 3 2 (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) (sym (wp0744 c4)) ▸
       at 4 3 (CX12 ∷ []) (wp0747 c4) ▸
       at 0 4 (Bx0-3124 ∷ []) (sym (lem-box-tQ-at132132 c4)) ▸ done

  b2 : Chain (Bx0-3124 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ []) (Bx0-3124 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wl0673 (lit c4))) ▸ done

-- CXcb-box @132132: 18 steps
lem-CXcb-box-at132132 : Ws → ⟪ (CX21 ∷ Bx0-3124 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx0-3124 ∷ CX21 ∷ []) (Toff013 ∷ CCZ024 ∷ CX21 ∷ Toff023 ∷ CS24 ∷ CX32 ∷ Toff013 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ CCZ024 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at132132 c4) ▸
       at 0 2 (Toff013 ∷ CX21 ∷ Toff023 ∷ []) (wl0873 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Toff023 ∷ CCZ234 ∷ []) (sym (wp0748 c4)) ▸
       at 1 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸
       at 4 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0829 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CS34 ∷ []) (wp0095 c4) ▸
       at 7 2 (Toff013 ∷ CX32 ∷ []) (wl0874 (lit c4)) ▸
       at 6 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ CX21 ∷ Toff023 ∷ CS24 ∷ CX32 ∷ Toff013 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ CCZ024 ∷ CX21 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ [])
  b1 = at 5 2 (Toff013 ∷ CX32 ∷ []) (wl0874 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0829 (lit c4))) ▸
       at 3 2 (Toff013 ∷ Toff023 ∷ []) (sym (wl0833 (lit c4))) ▸
       at 2 2 (Toff013 ∷ CX21 ∷ Toff023 ∷ []) (wl0873 (lit c4)) ▸
       at 3 3 (CX21 ∷ []) (wl0875 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 3 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸ done

  b2 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ []) (Bx0-3124 ∷ CCZ234 ∷ [])
  b2 = at 0 4 (Bx0-3124 ∷ []) (sym (lem-box-tQ-at132132 c4)) ▸
       at 1 3 (CCZ234 ∷ []) (sym (wl0676 (lit c4))) ▸ done

-- P-box @0210243143: 8 steps
lem-P-box-at0210243143 : Ws → ⟪ (Toff213 ∷ Bx2-0413 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-P-box-at0210243143 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Bx2-0413 ∷ Toff213 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at0210243143 c4)) ▸
       at 1 2 (CCZ123 ∷ CZ13 ∷ Toff213 ∷ []) (sym (wl0912 (lit c4))) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at0210243143 c4)) ▸
       at 4 3 (CCZ123 ∷ CZ13 ∷ []) (sym (wl0913 (lit c4))) ▸
       at 2 2 (Toff204 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF204 (lit c4)) ▸
       at 3 3 (CCZ123 ∷ []) (sym (wl0914 (lit c4))) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done

-- CXbc-box @022330: 17 steps
lem-CXbc-box-at022330 : Ws → ⟪ (CX30 ∷ Bx2-1304 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at022330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX30 ∷ Bx2-1304 ∷ CX30 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX30 ∷ CCZ234 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ CX30 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at022330 c4) ▸
       at 0 2 (Toff213 ∷ CX30 ∷ []) (wl0917 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) (sym (wp0757 c4)) ▸
       at 3 2 (Toff213 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0918 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CX30 ∷ []) (wl0917 (lit c4)) ▸
       at 5 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX30 ∷ CCZ234 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ CX30 ∷ []) (Bx2-1304 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 3 2 (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) (sym (wp0757 c4)) ▸
       at 4 3 (CX30 ∷ []) (wp0758 c4) ▸
       at 0 4 (Bx2-1304 ∷ []) (sym (lem-box-tQ-at022330 c4)) ▸ done

  b2 : Chain (Bx2-1304 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ []) (Bx2-1304 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wp0759 c4)) ▸ done

-- CXcb-box @022330: 18 steps
lem-CXcb-box-at022330 : Ws → ⟪ (CX03 ∷ Bx2-1304 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at022330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX03 ∷ Bx2-1304 ∷ CX03 ∷ []) (Toff213 ∷ CCZ024 ∷ CX03 ∷ Toff201 ∷ CS04 ∷ CX10 ∷ Toff213 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ CCZ024 ∷ CX03 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at022330 c4) ▸
       at 0 2 (Toff213 ∷ CX03 ∷ Toff201 ∷ []) (wl0919 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp0760 c4)) ▸
       at 1 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸
       at 4 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 8 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CX10 ∷ []) (wl0920 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ CX03 ∷ Toff201 ∷ CS04 ∷ CX10 ∷ Toff213 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ CCZ024 ∷ CX03 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ [])
  b1 = at 5 2 (Toff213 ∷ CX10 ∷ []) (wl0920 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 3 2 (Toff213 ∷ Toff201 ∷ []) (wl0921 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CX03 ∷ Toff201 ∷ []) (wl0919 (lit c4)) ▸
       at 3 3 (CX03 ∷ []) (wl0922 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 3 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ []) (Bx2-1304 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx2-1304 ∷ []) (sym (lem-box-tQ-at022330 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0761 c4)) ▸ done

-- QVQ @0220: 3 steps
lem-QVQ-at0220 : Ws → ⟪ (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-QVQ-at0220 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ [])
  b0 = at 0 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 1 4 (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at0220 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done

-- SWbc-box @0213243140: 11 steps
lem-SWbc-box-at0213243140 : Ws → ⟪ (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-SWbc-box-at0213243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) (CX41 ∷ Bx2-3410 ∷ CX41 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 2 3 (Bx2-3410 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0213243140 c4) ▸
       at 3 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0566 c4) ▸
       at 1 3 (Bx2-3410 ∷ CCZ013 ∷ []) (lem-CXcb-box-at0213243140 c4) ▸
       at 4 2 (CX41 ∷ CCZ034 ∷ []) (wp0357 c4) ▸
       at 3 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0567 c4) ▸
       at 2 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0567 c4) ▸ done

  b1 : Chain (CX41 ∷ Bx2-3410 ∷ CX41 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (Bx2-3410 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (wp0568 c4) ▸
       at 0 3 (Bx2-3410 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0213243140 c4) ▸
       at 1 2 [] (wp0007 c4) ▸ done

-- CXbc-box @0213213440: 17 steps
lem-CXbc-box-at0213213440 : Ws → ⟪ (CX14 ∷ Bx2-3140 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0213213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx2-3140 ∷ CX14 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX14 ∷ CCZ012 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CCZ024 ∷ CX31 ∷ CS03 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at0213213440 c4) ▸
       at 0 2 (Toff213 ∷ CX14 ∷ []) (wl0944 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (sym (wp0282 c4)) ▸
       at 3 2 (Toff213 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl0945 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CX14 ∷ []) (wl0944 (lit c4)) ▸
       at 5 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX14 ∷ CCZ012 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CCZ024 ∷ CX31 ∷ CS03 ∷ CX14 ∷ []) (Bx2-3140 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ012 ∷ []) (wp0142 c4) ▸
       at 3 2 (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (sym (wp0282 c4)) ▸
       at 4 3 (CX14 ∷ []) (wp0283 c4) ▸
       at 0 4 (Bx2-3140 ∷ []) (sym (lem-box-tQ-at0213213440 c4)) ▸ done

  b2 : Chain (Bx2-3140 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ []) (Bx2-3140 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wp0565 c4)) ▸ done

-- CXcb-box @0213213440: 18 steps
lem-CXcb-box-at0213213440 : Ws → ⟪ (CX41 ∷ Bx2-3140 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at0213213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx2-3140 ∷ CX41 ∷ []) (Toff213 ∷ CCZ024 ∷ CX41 ∷ Toff234 ∷ CS04 ∷ CX34 ∷ Toff213 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ CCZ024 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at0213213440 c4) ▸
       at 0 2 (Toff213 ∷ CX41 ∷ Toff234 ∷ []) (wl0946 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (sym (wp0768 c4)) ▸
       at 1 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 4 1 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (wp0115 c4) ▸
       at 8 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CX34 ∷ []) (wl0947 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ CX41 ∷ Toff234 ∷ CS04 ∷ CX34 ∷ Toff213 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ CCZ024 ∷ CX41 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ [])
  b1 = at 5 2 (Toff213 ∷ CX34 ∷ []) (wl0947 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4)) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0115 c4)) ▸
       at 3 2 (Toff213 ∷ Toff234 ∷ []) (sym (wl0942 (lit c4))) ▸
       at 2 2 (Toff213 ∷ CX41 ∷ Toff234 ∷ []) (wl0946 (lit c4)) ▸
       at 3 3 (CX41 ∷ []) (wl0948 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ034 ∷ []) (sym (wp0109 c4)) ▸
       at 3 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ []) (Bx2-3140 ∷ CCZ034 ∷ [])
  b2 = at 0 4 (Bx2-3140 ∷ []) (sym (lem-box-tQ-at0213213440 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (sym (wp0560 c4)) ▸ done

-- QVQ @0213243140: 3 steps
lem-QVQ-at0213243140 : Ws → ⟪ (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-QVQ-at0213243140 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Toff201 ∷ Toff201 ∷ []) (sym (wl0421 (lit c4))) ▸
       at 1 4 (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at0213243140 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done

-- SWbc-box @0220: 11 steps
lem-SWbc-box-at0220 : Ws → ⟪ (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-SWbc-box-at0220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) (CX03 ∷ Bx2-1034 ∷ CX03 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX03 ∷ CX30 ∷ CX03 ∷ []) (sym (wl0961 (lit c4))) ▸
       at 4 1 (CX03 ∷ CX30 ∷ CX03 ∷ []) (sym (wl0961 (lit c4))) ▸
       at 2 3 (Bx2-1034 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0220 c4) ▸
       at 3 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0763 c4) ▸
       at 1 3 (Bx2-1034 ∷ CCZ134 ∷ []) (lem-CXcb-box-at0220 c4) ▸
       at 4 2 (CX03 ∷ CCZ014 ∷ []) (wp0778 c4) ▸
       at 3 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0762 c4) ▸
       at 2 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0762 c4) ▸ done

  b1 : Chain (CX03 ∷ Bx2-1034 ∷ CX03 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ []) (Bx2-1034 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0779 c4) ▸
       at 0 3 (Bx2-1034 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0220 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done

-- P-box @022330: 8 steps
lem-P-box-at022330 : Ws → ⟪ (Toff204 ∷ Bx2-1304 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-P-box-at022330 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx2-1304 ∷ Toff204 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at022330 c4) ▸
       at 0 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at022330 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) (sym (wp0780 c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at022330 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ04 ∷ []) (sym (wp0781 c4)) ▸
       at 2 2 (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4)) ▸
       at 3 3 (CCZ024 ∷ []) (sym (wp0782 c4)) ▸
       at 0 4 (Bx2-1304 ∷ []) (sym (lem-box-tQ-at022330 c4)) ▸ done

-- VPQ @022330: 14 steps
lem-VPQ-at022330 : Ws → ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at022330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (sym (wl0176 (lit c4))) ▸
       at 4 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (sym (wp0015 c4)) ▸
       at 3 2 (CS04⁻ ∷ S2⁻ ∷ []) (sym (wp0018 c4)) ▸
       at 2 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ S2 ∷ []) (sym (wp0017 c4)) ▸
       at 0 2 (CS04⁻ ∷ CS13⁻ ∷ []) (sym (wp0016 c4)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at022330 c4) ▸ done

  b1 : Chain (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS13⁻ ∷ []) (wl0178 (lit c4)) ▸
       at 2 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS13⁻ ∷ []) (wl0177 (lit c4)) ▸
       at 0 4 (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4) ▸
       at 2 4 (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4)) ▸ done

-- CXbc-box @122331: 17 steps
lem-CXbc-box-at122331 : Ws → ⟪ (CX31 ∷ Bx0-2314 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx0-2314 ∷ CX31 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX31 ∷ CCZ034 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at122331 c4) ▸
       at 0 2 (Toff023 ∷ CX31 ∷ []) (wl0832 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) (sym (wp0792 c4)) ▸
       at 3 2 (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) (wp0793 c4) ▸
       at 2 2 (Toff023 ∷ CX31 ∷ []) (wl0832 (lit c4)) ▸
       at 5 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX31 ∷ CCZ034 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ CX31 ∷ []) (Bx0-2314 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 4 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 3 2 (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) (sym (wp0792 c4)) ▸
       at 4 3 (CX31 ∷ []) (wp0794 c4) ▸
       at 0 4 (Bx0-2314 ∷ []) (sym (lem-box-tQ-at122331 c4)) ▸ done

  b2 : Chain (Bx0-2314 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ [])
  b2 = at 1 3 (CCZ234 ∷ []) (sym (wl0277 (lit c4))) ▸ done

-- CXcb-box @122331: 18 steps
lem-CXcb-box-at122331 : Ws → ⟪ (CX13 ∷ Bx0-2314 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx0-2314 ∷ CX13 ∷ []) (Toff023 ∷ CCZ014 ∷ CX13 ∷ Toff012 ∷ CS14 ∷ CX21 ∷ Toff023 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ014 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at122331 c4) ▸
       at 0 2 (Toff023 ∷ CX13 ∷ Toff012 ∷ []) (wl0987 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (sym (wp0310 c4)) ▸
       at 1 2 (CCZ014 ∷ CX13 ∷ []) (sym (wp0795 c4)) ▸
       at 4 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸
       at 7 2 (Toff023 ∷ CX21 ∷ []) (wl0828 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4)) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ CX13 ∷ Toff012 ∷ CS14 ∷ CX21 ∷ Toff023 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ014 ∷ CX13 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ [])
  b1 = at 5 2 (Toff023 ∷ CX21 ∷ []) (wl0828 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸
       at 3 2 (Toff023 ∷ Toff012 ∷ []) (wl0275 (lit c4)) ▸
       at 2 2 (Toff023 ∷ CX13 ∷ Toff012 ∷ []) (wl0987 (lit c4)) ▸
       at 3 3 (CX13 ∷ []) (wl0988 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 3 2 (CCZ014 ∷ CX13 ∷ []) (sym (wp0795 c4)) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ []) (Bx0-2314 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-2314 ∷ []) (sym (lem-box-tQ-at122331 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wl0272 (lit c4))) ▸ done

-- P-box @14213243: 8 steps
lem-P-box-at14213243 : Ws → ⟪ (Toff023 ∷ Bx0-4123 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-P-box-at14213243 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Bx0-4123 ∷ Toff023 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at14213243 c4) ▸
       at 0 2 (Toff014 ∷ Toff023 ∷ []) (sym (lem-tP-at14213243 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ23 ∷ Toff023 ∷ []) (sym (wl0825 (lit c4))) ▸
       at 3 2 (Toff014 ∷ Toff023 ∷ []) (sym (lem-tP-at14213243 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ23 ∷ []) (sym (wl0826 (lit c4))) ▸
       at 2 2 (Toff014 ∷ CZ23 ∷ []) (lem-comm-CZ23-TOFF014 (lit c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wl0827 (lit c4))) ▸
       at 0 4 (Bx0-4123 ∷ []) (sym (lem-box-tQ-at14213243 c4)) ▸ done

-- VPQ @14213243: 14 steps
lem-VPQ-at14213243 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (sym (wp0050 c4)) ▸
       at 4 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (sym (wl0201 (lit c4))) ▸
       at 3 2 (CS23⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑)) ▸
       at 2 2 (CS23⁻ ∷ Toff014 ∷ []) (lem-comm-TOFF014-CSd23 (lit c4)) ▸
       at 1 2 (CS23⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑)) ▸
       at 0 2 (CS23⁻ ∷ CS14⁻ ∷ []) (wl0202 (lit c4)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at14213243 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS14⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS14⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff023 ∷ CCZ023 ∷ []) (wl0201 (lit c4)) ▸
       at 2 4 (Toff014 ∷ CCZ014 ∷ []) (wp0050 c4) ▸ done

-- CXbc-box @12233441: 17 steps
lem-CXbc-box-at12233441 : Ws → ⟪ (CX34 ∷ Bx0-2341 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at12233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx0-2341 ∷ CX34 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX34 ∷ CCZ013 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CCZ014 ∷ CX23 ∷ CS12 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4) ▸
       at 0 2 (Toff023 ∷ CX34 ∷ []) (wp0270 c4) ▸
       at 1 2 (CCZ014 ∷ CX34 ∷ CCZ013 ∷ []) (sym (wp0807 c4)) ▸
       at 3 2 (Toff023 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl1007 (lit c4)) ▸
       at 2 2 (Toff023 ∷ CX34 ∷ []) (wp0270 c4) ▸
       at 5 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX34 ∷ CCZ013 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CCZ014 ∷ CX23 ∷ CS12 ∷ CX34 ∷ []) (Bx0-2341 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸
       at 4 2 (CCZ014 ∷ CCZ013 ∷ []) (wp0394 c4) ▸
       at 3 2 (CCZ014 ∷ CX34 ∷ CCZ013 ∷ []) (sym (wp0807 c4)) ▸
       at 4 3 (CX34 ∷ []) (wp0808 c4) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸ done

  b2 : Chain (Bx0-2341 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ []) (Bx0-2341 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (sym (wl0648 (lit c4))) ▸ done

-- CXcb-box @12233441: 18 steps
lem-CXcb-box-at12233441 : Ws → ⟪ (CX43 ∷ Bx0-2341 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at12233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx0-2341 ∷ CX43 ∷ []) (Toff023 ∷ CCZ014 ∷ CX43 ∷ Toff024 ∷ CS14 ∷ CX24 ∷ Toff023 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ CCZ014 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4) ▸
       at 0 2 (Toff023 ∷ CX43 ∷ Toff024 ∷ []) (wp0809 c4) ▸
       at 2 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 1 2 (CCZ014 ∷ CX43 ∷ []) (sym (wp0810 c4)) ▸
       at 4 1 (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (wl0644 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CX24 ∷ []) (wp0263 c4) ▸
       at 6 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4)) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ CX43 ∷ Toff024 ∷ CS14 ∷ CX24 ∷ Toff023 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ CCZ014 ∷ CX43 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ [])
  b1 = at 5 2 (Toff023 ∷ CX24 ∷ []) (wp0263 c4) ▸
       at 4 2 (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0644 (lit c4))) ▸
       at 3 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 2 2 (Toff023 ∷ CX43 ∷ Toff024 ∷ []) (wp0809 c4) ▸
       at 3 3 (CX43 ∷ []) (wp0811 c4) ▸
       at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 3 2 (CCZ014 ∷ CX43 ∷ []) (sym (wp0810 c4)) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ []) (Bx0-2341 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wl0646 (lit c4))) ▸ done

-- P-box @12233441: 8 steps
lem-P-box-at12233441 : Ws → ⟪ (Toff014 ∷ Bx0-2341 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-P-box-at12233441 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Bx0-2341 ∷ Toff014 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4) ▸
       at 0 2 (Toff023 ∷ Toff014 ∷ []) (sym (lem-tP-at12233441 c4)) ▸
       at 1 2 (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) (sym (wp0158 c4)) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (sym (lem-tP-at12233441 c4)) ▸
       at 4 3 (CCZ014 ∷ CZ14 ∷ []) (sym (wp0159 c4)) ▸
       at 2 2 (Toff023 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF023 (lit c4)) ▸
       at 3 3 (CCZ014 ∷ []) (sym (wp0160 c4)) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸ done

-- P-box @122441: 8 steps
lem-P-box-at122441 : Ws → ⟪ (Toff013 ∷ Bx0-2431 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-P-box-at122441 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Bx0-2431 ∷ Toff013 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ Toff013 ∷ []) (sym (lem-tP-at122441 c4)) ▸
       at 1 2 (CCZ013 ∷ CZ13 ∷ Toff013 ∷ []) (sym (wl0682 (lit c4))) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (sym (lem-tP-at122441 c4)) ▸
       at 4 3 (CCZ013 ∷ CZ13 ∷ []) (sym (wl0683 (lit c4))) ▸
       at 2 2 (Toff024 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF024 (lit c4)) ▸
       at 3 3 (CCZ013 ∷ []) (sym (wl0684 (lit c4))) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done

-- CXbc-box @2332: 17 steps
lem-CXbc-box-at2332 : Ws → ⟪ (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at2332 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX32 ∷ CCZ034 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ CX32 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at2332 c4) ▸
       at 0 2 (Toff013 ∷ CX32 ∷ []) (wl0874 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (sym (wp0717 c4)) ▸
       at 3 2 (Toff013 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0825 c4) ▸
       at 2 2 (Toff013 ∷ CX32 ∷ []) (wl0874 (lit c4)) ▸
       at 5 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX32 ∷ CCZ034 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ CX32 ∷ []) (Bx0-1324 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ034 ∷ []) (sym (wp0109 c4)) ▸
       at 3 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (sym (wp0717 c4)) ▸
       at 4 3 (CX32 ∷ []) (wp0718 c4) ▸
       at 0 4 (Bx0-1324 ∷ []) (sym (lem-box-tQ-at2332 c4)) ▸ done

  b2 : Chain (Bx0-1324 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wl0254 (lit c4))) ▸ done

-- CXcb-box @2332: 18 steps
lem-CXcb-box-at2332 : Ws → ⟪ (CX23 ∷ Bx0-1324 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at2332 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx0-1324 ∷ CX23 ∷ []) (Toff013 ∷ CCZ024 ∷ CX23 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ CX23 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at2332 c4) ▸
       at 0 2 (Toff013 ∷ CX23 ∷ Toff012 ∷ []) (wl1018 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Toff012 ∷ CCZ124 ∷ []) (sym (wp0826 c4)) ▸
       at 1 2 (CCZ024 ∷ CX23 ∷ []) (sym (wp0082 c4)) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CS14 ∷ []) (wp0785 c4) ▸
       at 7 2 (Toff013 ∷ CX12 ∷ []) (wl0872 (lit c4)) ▸
       at 6 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ CX23 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ CX23 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ [])
  b1 = at 5 2 (Toff013 ∷ CX12 ∷ []) (wl0872 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (Toff013 ∷ Toff012 ∷ []) (wl0252 (lit c4)) ▸
       at 2 2 (Toff013 ∷ CX23 ∷ Toff012 ∷ []) (wl1018 (lit c4)) ▸
       at 3 3 (CX23 ∷ []) (wl1019 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ124 ∷ []) (sym (wp0827 c4)) ▸
       at 3 2 (CCZ024 ∷ CX23 ∷ []) (sym (wp0082 c4)) ▸ done

  b2 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ []) (Bx0-1324 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-1324 ∷ []) (sym (lem-box-tQ-at2332 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wl0257 (lit c4))) ▸ done

-- SWbc-box @03102132: 11 steps
lem-SWbc-box-at03102132 : Ws → ⟪ (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-SWbc-box-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) (CX12 ∷ Bx3-0124 ∷ CX12 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 4 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 2 3 (Bx3-0124 ∷ CCZ014 ∷ []) (lem-CXbc-box-at03102132 c4) ▸
       at 3 2 (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0899 c4) ▸
       at 1 3 (Bx3-0124 ∷ CCZ024 ∷ []) (lem-CXcb-box-at03102132 c4) ▸
       at 4 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 3 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 2 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸ done

  b1 : Chain (CX12 ∷ Bx3-0124 ∷ CX12 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) (Bx3-0124 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0900 c4) ▸
       at 0 3 (Bx3-0124 ∷ CCZ014 ∷ []) (lem-CXbc-box-at03102132 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done

-- P-box @0214203143: 8 steps
lem-P-box-at0214203143 : Ws → ⟪ (Toff213 ∷ Bx2-4013 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-P-box-at0214203143 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Bx2-4013 ∷ Toff213 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4) ▸
       at 0 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at0214203143 c4)) ▸
       at 1 2 (CCZ123 ∷ CZ13 ∷ Toff213 ∷ []) (sym (wl0912 (lit c4))) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at0214203143 c4)) ▸
       at 4 3 (CCZ123 ∷ CZ13 ∷ []) (sym (wl0913 (lit c4))) ▸
       at 2 2 (Toff204 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF204 (lit c4)) ▸
       at 3 3 (CCZ123 ∷ []) (sym (wl0914 (lit c4))) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-tQ-at0214203143 c4)) ▸ done

-- VPQ @0214203143: 14 steps
lem-VPQ-at0214203143 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at0214203143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (sym (wp0015 c4)) ▸
       at 4 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (sym (wl0176 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S2⁻ ∷ []) (sym (wl0177 (lit c4))) ▸
       at 2 2 (CS13⁻ ∷ Toff204 ∷ []) (lem-comm-TOFF204-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S2 ∷ []) (sym (wl0178 (lit c4))) ▸
       at 0 2 (CS13⁻ ∷ CS04⁻ ∷ []) (wp0016 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0214203143 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS04⁻ ∷ []) (wp0017 c4) ▸
       at 2 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS04⁻ ∷ []) (wp0018 c4) ▸
       at 0 4 (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4)) ▸
       at 2 4 (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4) ▸ done

-- CXbc-box @02233440: 17 steps
lem-CXbc-box-at02233440 : Ws → ⟪ (CX34 ∷ Bx2-1340 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at02233440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx2-1340 ∷ CX34 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX34 ∷ CCZ023 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4) ▸
       at 0 2 (Toff213 ∷ CX34 ∷ []) (wl0947 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) (sym (wp0911 c4)) ▸
       at 3 2 (Toff213 ∷ CCZ023 ∷ CCZ013 ∷ []) (wl1119 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CX34 ∷ []) (wl0947 (lit c4)) ▸
       at 5 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX34 ∷ CCZ023 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ CX34 ∷ []) (Bx2-1340 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 3 2 (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) (sym (wp0911 c4)) ▸
       at 4 3 (CX34 ∷ []) (wp0912 c4) ▸
       at 0 4 (Bx2-1340 ∷ []) (sym (lem-box-tQ-at02233440 c4)) ▸ done

  b2 : Chain (Bx2-1340 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ []) (Bx2-1340 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wp0913 c4)) ▸ done

-- CXcb-box @02233440: 18 steps
lem-CXcb-box-at02233440 : Ws → ⟪ (CX43 ∷ Bx2-1340 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at02233440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx2-1340 ∷ CX43 ∷ []) (Toff213 ∷ CCZ024 ∷ CX43 ∷ Toff214 ∷ CS04 ∷ CX14 ∷ Toff213 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ CCZ024 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4) ▸
       at 0 2 (Toff213 ∷ CX43 ∷ Toff214 ∷ []) (wl1120 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 1 2 (CCZ024 ∷ CX43 ∷ []) (sym (wp0914 c4)) ▸
       at 4 1 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (wp0046 c4) ▸
       at 8 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CX14 ∷ []) (wl0944 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ CX43 ∷ Toff214 ∷ CS04 ∷ CX14 ∷ Toff213 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ CCZ024 ∷ CX43 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ [])
  b1 = at 5 2 (Toff213 ∷ CX14 ∷ []) (wl0944 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0046 c4)) ▸
       at 3 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 2 2 (Toff213 ∷ CX43 ∷ Toff214 ∷ []) (wl1120 (lit c4)) ▸
       at 3 3 (CX43 ∷ []) (wl1121 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 3 2 (CCZ024 ∷ CX43 ∷ []) (sym (wp0914 c4)) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ []) (Bx2-1340 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx2-1340 ∷ []) (sym (lem-box-tQ-at02233440 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0915 c4)) ▸ done

-- VPQ @022440: 14 steps
lem-VPQ-at022440 : Ws → ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at022440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (sym (wl0629 (lit c4))) ▸
       at 4 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (sym (wl0630 (lit c4))) ▸
       at 3 2 (CS03⁻ ∷ S2⁻ ∷ []) (sym (wl0631 (lit c4))) ▸
       at 2 2 (CS03⁻ ∷ Toff214 ∷ []) (lem-comm-TOFF214-CSd03 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ S2 ∷ []) (sym (wl0632 (lit c4))) ▸
       at 0 2 (CS03⁻ ∷ CS14⁻ ∷ []) (sym (wp0514 c4)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at022440 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS14⁻ ∷ []) (wl0633 (lit c4)) ▸
       at 2 2 (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS14⁻ ∷ []) (wl0634 (lit c4)) ▸
       at 0 4 (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4)) ▸
       at 2 4 (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4)) ▸ done

-- CXbc-box @022440: 17 steps
lem-CXbc-box-at022440 : Ws → ⟪ (CX43 ∷ Bx2-1430 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at022440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx2-1430 ∷ CX43 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CX43 ∷ CCZ024 ∷ CS04 ∷ CX14 ∷ CS04⁻ ∷ CCZ023 ∷ CX14 ∷ CS01 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at022440 c4) ▸
       at 0 2 (Toff214 ∷ CX43 ∷ []) (wl1132 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CX43 ∷ CCZ024 ∷ []) (sym (wp0920 c4)) ▸
       at 3 2 (Toff214 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0921 c4) ▸
       at 2 2 (Toff214 ∷ CX43 ∷ []) (wl1132 (lit c4)) ▸
       at 5 1 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (wp0046 c4) ▸
       at 9 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 8 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CX43 ∷ CCZ024 ∷ CS04 ∷ CX14 ∷ CS04⁻ ∷ CCZ023 ∷ CX14 ∷ CS01 ∷ CX43 ∷ []) (Bx2-1430 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS04⁻ ∷ []) (sym (wp0047 c4)) ▸
       at 6 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0046 c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 3 2 (CCZ023 ∷ CX43 ∷ CCZ024 ∷ []) (sym (wp0920 c4)) ▸
       at 4 3 (CX43 ∷ []) (wp0922 c4) ▸
       at 0 4 (Bx2-1430 ∷ []) (sym (lem-box-tQ-at022440 c4)) ▸ done

  b2 : Chain (Bx2-1430 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ []) (Bx2-1430 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0915 c4)) ▸ done
