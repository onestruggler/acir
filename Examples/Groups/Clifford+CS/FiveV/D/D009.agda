{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D009 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0003 ; wl0006 ; wl0018 ; wl0182 ; wl0196 ; wl0203 ; wl0204 ; wl0207 ; wl0225 ; wl0230 ; wl0245 ; wl0256 ; wl0258 ; wl0263 ; wl0270 ; wl0300 ; wl0305 ; wl0306 ; wl0321 ; wl0324 ; wl0326 ; wl0341 ; wl0423 ; wl0434 ; wl0435 ; wl0436 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0448 ; wl0458 ; wl0473 ; wl0474 ; wl0499 ; wl0501 ; wl0518 ; wl0560 ; wl0610 ; wl0613 ; wl0617 ; wl0669 ; wl0670 ; wl0673 ; wl0676 ; wl0677 ; wl0678 ; wl0679 ; wl0680 ; wl0681 ; wl0704 ; wl0706 ; wl0751 ; wl0753 ; wl0755 ; wl0757 ; wl0761 ; wl0778 ; wl0779 ; wl0788 ; wl0789 ; wl0790 ; wl0791 ; wl0792 ; wl0793 ; wl0794 ; wl0795 ; wl0796 ; wl0797 ; wl0798 ; wl0799 ; wl0800 ; wl0801 ; wl0802 ; wl0803 ; wl0804 ; wl0805 ; wl0806 ; wl0807 ; wl0808 ; wl0809 ; wl0810 ; wl0811 ; wl0812 ; wl0813 ; wl0814 ; wl0815 ; wl0816 ; wl0817 ; wl0818 ; wl0819 ; wl0820 ; wl0821 ; wl0822 ; wl0823 ; wl0824 ; wl0825 ; wl0826 ; wl0827 ; wl0828 ; wl0829 ; wl0830 ; wl0831 ; wl0832 ; wl0833 ; wl0834 ; wl0835 ; wl0836 ; wl0837 ; wl0838 ; wl0839 ; wl0840 ; wl0841 ; wl0842 ; wl0843 ; wl0844 ; wl0845 ; wl0846 ; wl0847 ; wl0848 ; wl0849 ; wl0850 ; wl0851 ; wl0852 ; wl0853 ; wl0854 ; wl0855 ; wl0856 ; wl0857 ; wl0858 ; wl0859 ; wl0860 ; wl0861 ; wl0862 ; wl0863 ; wl0864 ; wl0865 ; wl0866 ; wl0867 ; wl0868 ; wl0869 ; wl0870 ; wl0871 ; wl0872 ; wl0873 ; wl0874 ; wl0875 ; wl0876 ; wl0877 ; wp0001 ; wp0003 ; wp0034 ; wp0036 ; wp0038 ; wp0041 ; wp0054 ; wp0062 ; wp0064 ; wp0075 ; wp0076 ; wp0077 ; wp0090 ; wp0095 ; wp0106 ; wp0107 ; wp0108 ; wp0109 ; wp0120 ; wp0135 ; wp0145 ; wp0153 ; wp0154 ; wp0155 ; wp0157 ; wp0182 ; wp0183 ; wp0184 ; wp0185 ; wp0186 ; wp0187 ; wp0189 ; wp0190 ; wp0215 ; wp0272 ; wp0285 ; wp0298 ; wp0299 ; wp0308 ; wp0312 ; wp0313 ; wp0314 ; wp0320 ; wp0352 ; wp0357 ; wp0499 ; wp0503 ; wp0505 ; wp0506 ; wp0507 ; wp0509 ; wp0511 ; wp0524 ; wp0543 ; wp0575 ; wp0587 ; wp0594 ; wp0661 ; wp0702 ; wp0704 ; wp0705 ; wp0706 ; wp0707 ; wp0708 ; wp0709 ; wp0710 ; wp0711 ; wp0712 ; wp0713 ; wp0714 ; wp0715 ; wp0716 ; wp0717 ; wp0718 ; wp0719 ; wp0720 ; wp0721 ; wp0722 ; wp0723 ; wp0724 ; wp0725 ; wp0726 ; wp0727 ; wp0728 ; wp0729 ; wp0730 ; wp0731 ; wp0732 ; wp0733 ; wp0734 ; wp0735 ; wp0736 ; wp0737 ; wp0738 ; wp0739 ; wp0740 ; wp0741 ; wp0742 ; wp0743 ; wp0744 ; wp0745 ; wp0746 ; wp0747 ; wp0748 ; wp0749)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at0210243143 ; lem-box-cP-at243243 ; lem-box-tQ-at243243 ; lem-tP-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-box-cP-at132132 ; lem-box-tQ-at122331 ; lem-box-tQ-at132132 ; lem-box-tQ-at1331 ; lem-pairs-at122331 ; lem-sym-ab-at122331)
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-pairs-at0330)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-box-cP-at0314203142 ; lem-box-tQ-at032032 ; lem-cQ-at032032 ; lem-pairs-at0310243142 ; lem-sym-ab-at03102132 ; lem-sym-ab-at032032 ; lem-sym-bc-at032032 ; lem-sym-bc-at0330)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-box-tQ-at0214213043)
open import Examples.Groups.Clifford+CS.FiveV.D.D008 using (lem-F0-B-at14213243 ; lem-QVQ-at0314213042 ; lem-box-perm-1324-at0314213042 ; lem-box-perm-2314-at0210243143 ; lem-box-tQ-at0314213042 ; lem-tP-at0314213042)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX04-TOFF213 ; lem-comm-CX12-CCZ034 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX21-CCZ034 ; lem-comm-CX24-CCZ013 ; lem-comm-CZ24-CCZ013)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS04-TOFF312 ; lem-comm-CS14-TOFF023 ; lem-comm-CS24-CCZ013 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd24-CCZ013 ; lem-comm-CSd24-TOFF301 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014 ; lem-comm-TOFF301-CSd24)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CS02-CCZ134 ; lem-comm-CS02-TOFF314 ; lem-comm-CS03-TOFF214 ; lem-comm-CSd02-CCZ134 ; lem-comm-CSd03-TOFF214 ; lem-comm-CX04-TOFF312 ; lem-comm-CX31-TOFF024 ; lem-comm-CX41-CCZ023 ; lem-comm-CZ14-TOFF302 ; lem-comm-CZ23-TOFF014 ; lem-comm-CZ24-TOFF301 ; lem-comm-SWAP14-BOX⟨3·20⟩ ; lem-comm-TOFF214-CS03)
-- box-cP @0314213042: 12 steps
lem-box-cP-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-box-cP-at0314213042 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 2 4 (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-QVQ-at0314213042 c4) ▸
       at 1 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213042 c4) ▸
       at 2 2 [] (wl0788 (lit c4)) ▸ done


-- CSdu-box-3 @0314213042: 17 steps
lem-CSdu-box-3-at0314213042 : Ws → ⟪ (CS03⁻ ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0314213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03⁻ ∷ Bx3-4102 ∷ []) (CCZ134 ∷ Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CS02 ∷ CCZ134 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Toff302 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213042 c4) ▸
       at 0 2 (CCZ134 ∷ CS03⁻ ∷ []) (sym (wp0704 c4)) ▸
       at 1 2 (Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ []) (wl0789 (lit c4)) ▸
       at 4 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0757 (lit c4)) ▸
       at 8 2 (CCZ134 ∷ CS23 ∷ []) (sym (wl0790 (lit c4))) ▸
       at 7 2 (CCZ134 ∷ CX30 ∷ []) (sym (wp0705 c4)) ▸
       at 6 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CX30 ∷ []) (sym (wp0705 c4)) ▸ done

  b1 : Chain (CCZ134 ∷ Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CS02 ∷ CCZ134 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Toff302 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS03⁻ ∷ [])
  b1 = at 4 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl0757 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS03⁻ ∷ []) (sym (wp0704 c4)) ▸
       at 5 2 (Toff302 ∷ CZ02 ∷ CCZ023 ∷ []) (wl0791 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CS02⁻ ∷ []) (wl0792 (lit c4)) ▸
       at 3 2 (Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ []) (wl0789 (lit c4)) ▸
       at 4 6 (CS03⁻ ∷ []) (wl0793 (lit c4)) ▸ done

  b2 : Chain (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS03⁻ ∷ []) (Bx3-4102 ∷ CS03⁻ ∷ [])
  b2 = at 0 4 (Bx3-4102 ∷ []) (sym (lem-box-cP-at0314213042 c4)) ▸ done


-- F0-R @14213243: 11 steps
lem-F0-R-at14213243 : Ws → ⟪ (CX23 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx3-4102 ∷ CX23 ∷ []) ⟫ʷ
lem-F0-R-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX23 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ [])
  b0 = at 0 2 (Toff314 ∷ CX23 ∷ []) (wl0794 (lit c4)) ▸
       at 1 2 (CS03 ∷ CS02 ∷ CCZ023 ∷ CX23 ∷ []) (sym (wl0795 (lit c4))) ▸
       at 4 2 (Toff314 ∷ CX23 ∷ []) (wl0794 (lit c4)) ▸
       at 5 2 (CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ CX23 ∷ []) (sym (wl0796 (lit c4))) ▸
       at 2 2 (CCZ023 ∷ CS02 ∷ []) (sym (wl0797 (lit c4))) ▸
       at 3 2 (Toff314 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF314 (lit c4)) ▸
       at 4 3 (CS03⁻ ∷ []) (wl0798 (lit c4)) ▸
       at 2 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0788 (lit c4))) ▸ done

  b1 : Chain (Toff314 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx3-4102 ∷ CX23 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ CS03⁻ ∷ []) (sym (wl0799 (lit c4))) ▸
       at 3 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸
       at 3 2 (CS03⁻ ∷ Bx3-4102 ∷ []) (sym (lem-CSdu-box-3-at0314213042 c4)) ▸ done


-- CSu-box-3 @0314213042: 17 steps
lem-CSu-box-3-at0314213042 : Ws → ⟪ (CS03 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CS03 ∷ []) ⟫ʷ
lem-CSu-box-3-at0314213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03 ∷ Bx3-4102 ∷ []) (CCZ134 ∷ Toff302 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CCZ134 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Toff302 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213042 c4) ▸
       at 0 2 (CCZ134 ∷ CS03 ∷ []) (sym (wp0706 c4)) ▸
       at 1 2 (Toff302 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ []) (wl0800 (lit c4)) ▸
       at 4 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0757 (lit c4)) ▸
       at 8 2 (CCZ134 ∷ CS23 ∷ []) (sym (wl0790 (lit c4))) ▸
       at 7 2 (CCZ134 ∷ CX30 ∷ []) (sym (wp0705 c4)) ▸
       at 6 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CX30 ∷ []) (sym (wp0705 c4)) ▸ done

  b1 : Chain (CCZ134 ∷ Toff302 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CCZ134 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Toff302 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS03 ∷ [])
  b1 = at 4 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl0757 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS03 ∷ []) (sym (wp0706 c4)) ▸
       at 5 2 (Toff302 ∷ CZ02 ∷ CCZ023 ∷ []) (wl0791 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CS02 ∷ []) (wl0801 (lit c4)) ▸
       at 3 2 (Toff302 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ []) (wl0800 (lit c4)) ▸
       at 4 6 (CS03 ∷ []) (wl0802 (lit c4)) ▸ done

  b2 : Chain (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS03 ∷ []) (Bx3-4102 ∷ CS03 ∷ [])
  b2 = at 0 4 (Bx3-4102 ∷ []) (sym (lem-box-cP-at0314213042 c4)) ▸ done


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


-- box2 @0314213042: 11 steps
lem-box2-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0314213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4102 ∷ Bx3-4102 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b0 = at 0 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4) ▸
       at 4 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213042 c4) ▸
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0788 (lit c4))) ▸
       at 5 5 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ []) (lem-t-cP-at0314213042 c4) ▸
       at 5 4 (Bx3-4102 ∷ []) (sym (lem-box-cP-at0314213042 c4)) ▸
       at 5 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4) ▸
       at 4 2 [] (wl0788 (lit c4)) ▸
       at 3 2 [] (wl0204 (lit c4)) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) []
  b1 = at 2 2 [] (wl0788 (lit c4)) ▸
       at 1 2 [] (wl0204 (lit c4)) ▸
       at 0 2 [] (wl0788 (lit c4)) ▸ done


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


-- SWbc-box @0214213043: 11 steps
lem-SWbc-box-at0214213043 : Ws → ⟪ (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-SWbc-box-at0214213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) (CX10 ∷ Bx2-4103 ∷ CX10 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 4 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 2 3 (Bx2-4103 ∷ CCZ134 ∷ []) (lem-CXbc-box-at0214213043 c4) ▸
       at 3 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0507 c4) ▸
       at 1 3 (Bx2-4103 ∷ CCZ034 ∷ []) (lem-CXcb-box-at0214213043 c4) ▸
       at 4 2 (CX10 ∷ CCZ134 ∷ []) (wp0712 c4) ▸
       at 3 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp0506 c4) ▸
       at 2 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp0506 c4) ▸ done

  b1 : Chain (CX10 ∷ Bx2-4103 ∷ CX10 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) (Bx2-4103 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wp0713 c4) ▸
       at 0 3 (Bx2-4103 ∷ CCZ134 ∷ []) (lem-CXbc-box-at0214213043 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done


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


-- sym-bc @0214213043: 2 steps
lem-sym-bc-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym-bc-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0214213043 c4)) ▸
       at 0 3 (Bx2-4013 ∷ []) (lem-nat-SWbc-at0214213043 c4) ▸ done


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


-- box-perm-3124 @0214213043: 2 steps
lem-box-perm-3124-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-3124-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-sym-bc-at0214213043 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4) ▸ done


-- CXuA-S @14213243: 44 steps
lem-CXuA-S-at14213243 : Ws → ⟪ (CX23 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CX23 ∷ []) ⟫ʷ
lem-CXuA-S-at14213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CX23 ∷ Sb2-0-41-3 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Bx3-4102 ∷ CS03⁻ ∷ CX23 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (Bx2-4103 ∷ []) (lem-box-perm-2314-at0210243143 c4) ▸
       at 2 0 (CX23 ∷ CX23 ∷ []) (sym (wl0806 (lit c4))) ▸
       at 0 3 (Bx2-4103 ∷ Bx3-4102 ∷ []) (lem-F0-B-at14213243 c4) ▸
       at 2 5 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx3-4102 ∷ CX23 ∷ []) (lem-F0-R-at14213243 c4) ▸
       at 5 2 (Bx3-4102 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3-at0314213042 c4) ▸ done

  b1 : Chain (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Bx3-4102 ∷ CS03⁻ ∷ CX23 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ CS03 ∷ CCZ034 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS03⁻ ∷ CX23 ∷ [])
  b1 = at 5 1 (Bx3-4012 ∷ []) (lem-box-perm-1324-at0314213042 c4) ▸
       at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 4 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0702 c4)) ▸
       at 6 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 10 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 9 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸ done

  b2 : Chain (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ CS03 ∷ CCZ034 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS03⁻ ∷ CX23 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ Bx3-4102 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ [])
  b2 = at 6 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 5 2 (Toff312 ∷ Toff314 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 6 3 (CCZ034 ∷ Toff314 ∷ []) (sym (wp0716 c4)) ▸
       at 7 2 (Toff312 ∷ Toff314 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 4 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 4 1 (Bx3-4102 ∷ []) (sym (lem-box-perm-1324-at0314213042 c4)) ▸
       at 3 2 (Bx3-4102 ∷ CS03 ∷ []) (lem-CSu-box-3-at0314213042 c4) ▸ done

  b3 : Chain (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ Bx3-4102 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ CCZ034 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ [])
  b3 = at 3 1 (Bx3-4012 ∷ []) (lem-box-perm-1324-at0314213042 c4) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 2 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0702 c4)) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 8 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸ done

  b4 : Chain (Bx2-4103 ∷ Bx3-4102 ∷ CCZ034 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ []) (Bx2-4103 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ [])
  b4 = at 4 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 3 2 (Toff312 ∷ Toff314 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 4 3 (CCZ034 ∷ Toff314 ∷ []) (sym (wp0716 c4)) ▸
       at 5 2 (Toff312 ∷ Toff314 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 2 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 2 1 (Bx3-4102 ∷ []) (sym (lem-box-perm-1324-at0314213042 c4)) ▸
       at 1 2 [] (lem-box2-at0314213042 c4) ▸ done

  b5 : Chain (Bx2-4103 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ []) (Sb2-0-41-3 ∷ CX23 ∷ [])
  b5 = at 0 1 (Bx2-0413 ∷ []) (lem-box-perm-3124-at0214213043 c4) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- CXu-box-4 @0210243143: 15 steps
lem-CXu-box-4-at0210243143 : Ws → ⟪ (CX32 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CX32 ∷ []) ⟫ʷ
lem-CXu-box-4-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX32 ∷ Bx2-0413 ∷ []) (CCZ024 ∷ CX32 ∷ Toff213 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (sym (wp0717 c4)) ▸
       at 2 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 6 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 5 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4)) ▸
       at 3 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸ done

  b1 : Chain (CCZ024 ∷ CX32 ∷ Toff213 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ []) (Bx2-0413 ∷ CX32 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 1 2 (Toff213 ∷ CX32 ∷ []) (wl0809 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CCZ034 ∷ []) (sym (wp0109 c4)) ▸
       at 2 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (sym (wp0717 c4)) ▸
       at 3 3 (CX32 ∷ []) (wp0718 c4) ▸
       at 3 2 (Toff213 ∷ CX32 ∷ []) (wl0809 (lit c4)) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done


-- CXAu-S @14213243: 12 steps
lem-CXAu-S-at14213243 : Ws → ⟪ (CX32 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CX32 ∷ []) ⟫ʷ
lem-CXAu-S-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX32 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CX32 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ CX32 ∷ []) (lem-CXu-box-4-at0210243143 c4) ▸
       at 1 2 (Toff314 ∷ CX32 ∷ Toff214 ∷ []) (wl0810 (lit c4)) ▸
       at 3 2 (CS03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CS03 (lit c4)) ▸
       at 2 2 (CS03 ∷ CX32 ∷ []) (sym (wl0811 (lit c4))) ▸
       at 3 3 (Toff314 ∷ CX32 ∷ []) (wl0812 (lit c4)) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CX32 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ CX32 ∷ [])
  b1 = at 4 2 (CS03⁻ ∷ CX32 ∷ []) (sym (wl0813 (lit c4))) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- SW-S @14213243: 5 steps
lem-SW-S-at14213243 : Ws → ⟪ (Sw23 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-SW-S-at14213243 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sw23 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 2 2 (Sb2-0-41-3 ∷ CX23 ∷ []) (lem-CXuA-S-at14213243 c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ CX32 ∷ []) (lem-CXAu-S-at14213243 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ CX23 ∷ []) (lem-CXuA-S-at14213243 c4) ▸
       at 1 3 (Sw23 ∷ []) (wl0258 (lit c4)) ▸ done


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


-- F0 @14213243: 3 steps
lem-F0-at14213243 : Ws → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ []) ⟫ʷ
lem-F0-at14213243 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-SW-S-at14213243 c4) ▸
       at 0 3 (Sb3-0-41-2 ∷ []) (lem-nat-S-at14213243 c4) ▸ done


-- CSdu-box-3 @243243: 17 steps
lem-CSdu-box-3-at243243 : Ws → ⟪ (CS02⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02⁻ ∷ Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff023 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ CS02⁻ ∷ []) (sym (wp0215 c4)) ▸
       at 1 2 (Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ []) (wl0818 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl0458 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 7 2 (CCZ014 ∷ CX02 ∷ []) (sym (wp0308 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX02 ∷ []) (sym (wp0308 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff023 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS02⁻ ∷ [])
  b1 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl0458 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS02⁻ ∷ []) (sym (wp0215 c4)) ▸
       at 5 2 (Toff023 ∷ CZ23 ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CS23⁻ ∷ []) (wl0820 (lit c4)) ▸
       at 3 2 (Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ []) (wl0818 (lit c4)) ▸
       at 4 6 (CS02⁻ ∷ []) (wl0821 (lit c4)) ▸ done

  b2 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS02⁻ ∷ []) (Bx0-1423 ∷ CS02⁻ ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done


-- CSu-box-3 @243243: 17 steps
lem-CSu-box-3-at243243 : Ws → ⟪ (CS02 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS02 ∷ []) ⟫ʷ
lem-CSu-box-3-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02 ∷ Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CS02 ∷ CS23 ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff023 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 1 2 (Toff023 ∷ CS02 ∷ CS23 ∷ CCZ023 ∷ []) (wl0822 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl0458 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 7 2 (CCZ014 ∷ CX02 ∷ []) (sym (wp0308 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX02 ∷ []) (sym (wp0308 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CS02 ∷ CS23 ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff023 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS02 ∷ [])
  b1 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl0458 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 5 2 (Toff023 ∷ CZ23 ∷ CCZ023 ∷ []) (wl0819 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CS23 ∷ []) (wl0823 (lit c4)) ▸
       at 3 2 (Toff023 ∷ CS02 ∷ CS23 ∷ CCZ023 ∷ []) (wl0822 (lit c4)) ▸
       at 4 6 (CS02 ∷ []) (wl0824 (lit c4)) ▸ done

  b2 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS02 ∷ []) (Bx0-1423 ∷ CS02 ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done


-- box-perm-1342 @0310243142: 3 steps
lem-box-perm-1342-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-1342-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-1204 ∷ []) (lem-pairs-at0310243142 c4) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-sym-bc-at0330 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸ done


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


-- pairs @243243: 4 steps
lem-pairs-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-pairs-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 1 (Toff023 ∷ Bx0-1423 ∷ Toff023 ∷ []) (sym (lem-P-box-at243243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 [] (wl0203 (lit c4)) ▸
       at 0 4 (Bx0-2314 ∷ []) (sym (lem-box-tQ-at122331 c4)) ▸ done


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


-- SWbc-box @1331: 11 steps
lem-SWbc-box-at1331 : Ws → ⟪ (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-SWbc-box-at1331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) (CX21 ∷ Bx0-3214 ∷ CX21 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 4 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 2 3 (Bx0-3214 ∷ CCZ234 ∷ []) (lem-CXbc-box-at1331 c4) ▸
       at 3 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl0680 (lit c4)) ▸
       at 1 3 (Bx0-3214 ∷ CCZ134 ∷ []) (lem-CXcb-box-at1331 c4) ▸
       at 4 2 (CX21 ∷ CCZ234 ∷ []) (wl0836 (lit c4)) ▸
       at 3 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0678 (lit c4)) ▸
       at 2 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0678 (lit c4)) ▸ done

  b1 : Chain (CX21 ∷ Bx0-3214 ∷ CX21 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ []) (Bx0-3214 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (wl0837 (lit c4)) ▸
       at 0 3 (Bx0-3214 ∷ CCZ234 ∷ []) (lem-CXbc-box-at1331 c4) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸ done


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


-- sym-bc @1331: 2 steps
lem-sym-bc-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym-bc-at1331 c4 = run b0
  where
  b0 : Chain (Bx0-3214 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at1331 c4)) ▸
       at 0 3 (Bx0-3124 ∷ []) (lem-nat-SWbc-at1331 c4) ▸ done


-- box-perm-4132 @243243: 3 steps
lem-box-perm-4132-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-box-perm-4132-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 1 (Bx0-2314 ∷ []) (lem-pairs-at243243 c4) ▸
       at 0 1 (Bx0-3214 ∷ []) (lem-sym-ab-at122331 c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-bc-at1331 c4) ▸ done


-- tP @032032: 7 steps
lem-tP-at032032 : Ws → ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-tP-at032032 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (sym (wl0434 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0435 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at032032 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff324 ∷ []) (wl0435 (lit c4)) ▸
       at 1 3 (Toff301 ∷ []) (wl0434 (lit c4)) ▸ done


-- P-box @032032: 8 steps
lem-P-box-at032032 : Ws → ⟪ (Toff324 ∷ Bx3-1024 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-P-box-at032032 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Bx3-1024 ∷ Toff324 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at032032 c4) ▸
       at 0 2 (Toff301 ∷ Toff324 ∷ []) (sym (lem-tP-at032032 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ24 ∷ Toff324 ∷ []) (sym (wl0842 (lit c4))) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (sym (lem-tP-at032032 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ24 ∷ []) (sym (wl0843 (lit c4))) ▸
       at 2 2 (Toff301 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF301 (lit c4)) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wl0844 (lit c4))) ▸
       at 0 4 (Bx3-1024 ∷ []) (sym (lem-box-tQ-at032032 c4)) ▸ done


-- VPQ @032032: 14 steps
lem-VPQ-at032032 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at032032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (CS24⁻ ∷ CS01⁻ ∷ S3 ∷ Toff324 ∷ Toff301 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (sym (wl0437 (lit c4))) ▸
       at 4 2 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (sym (wl0438 (lit c4))) ▸
       at 3 2 (CS24⁻ ∷ S3⁻ ∷ []) (sym (wl0439 (lit c4))) ▸
       at 2 2 (CS24⁻ ∷ Toff301 ∷ []) (lem-comm-TOFF301-CSd24 (lit c4)) ▸
       at 1 2 (CS24⁻ ∷ S3 ∷ []) (sym (wl0440 (lit c4))) ▸
       at 0 2 (CS24⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at032032 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS01⁻ ∷ S3 ∷ Toff324 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑)) ▸
       at 2 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 2 (S3⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑)) ▸
       at 0 4 (Toff324 ∷ CCZ234 ∷ []) (wl0438 (lit c4)) ▸
       at 2 4 (Toff301 ∷ CCZ013 ∷ []) (wl0437 (lit c4)) ▸ done


-- QVQ @032032: 3 steps
lem-QVQ-at032032 : Ws → ⟪ (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-QVQ-at032032 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ [])
  b0 = at 0 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 1 4 (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at032032 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done


-- box-cP @032032: 12 steps
lem-box-cP-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-box-cP-at032032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1024 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 2 4 (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-QVQ-at032032 c4) ▸
       at 1 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at032032 c4) ▸
       at 2 2 [] (wl0443 (lit c4)) ▸ done


-- cQ @0312243140: 7 steps
lem-cQ-at0312243140 : Ws → ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0312243140 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS34⁻ ∷ []) (sym (wp0184 c4)) ▸
       at 1 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done


-- box-tQ @0312243140: 13 steps
lem-box-tQ-at0312243140 : Ws → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at0312243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2410 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wl0845 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wl0845 (lit c4))) ▸
       at 0 2 (Toff324 ∷ CCZ234 ∷ CZ24 ∷ []) (wl0846 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at0312243140 c4) ▸
       at 2 4 (Toff324 ∷ []) (wl0847 (lit c4)) ▸ done


-- pairs @032032: 4 steps
lem-pairs-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-pairs-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-2410 ∷ [])
  b0 = at 0 1 (Toff324 ∷ Bx3-1024 ∷ Toff324 ∷ []) (sym (lem-P-box-at032032 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 4 2 [] (wl0442 (lit c4)) ▸
       at 0 4 (Bx3-2410 ∷ []) (sym (lem-box-tQ-at0312243140 c4)) ▸ done


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


-- SWbc-box @0312243140: 11 steps
lem-SWbc-box-at0312243140 : Ws → ⟪ (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-SWbc-box-at0312243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) (CX41 ∷ Bx3-2410 ∷ CX41 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 2 3 (Bx3-2410 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0312243140 c4) ▸
       at 3 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸
       at 1 3 (Bx3-2410 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0312243140 c4) ▸
       at 4 2 (CX41 ∷ CCZ024 ∷ []) (wp0285 c4) ▸
       at 3 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp0730 c4) ▸
       at 2 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp0730 c4) ▸ done

  b1 : Chain (CX41 ∷ Bx3-2410 ∷ CX41 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ []) (Bx3-2410 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (wp0731 c4) ▸
       at 0 3 (Bx3-2410 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0312243140 c4) ▸
       at 1 2 [] (wp0135 c4) ▸ done


-- nat-SWbc @0312243140: 23 steps
lem-nat-SWbc-at0312243140 : Ws → ⟪ (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ Sw14 ∷ CCZ123 ∷ Bx3-20 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 1 2 (Toff312 ∷ Sw14 ∷ []) (wl0855 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 3 2 (Toff234 ∷ Sw14 ∷ []) (wl0857 (lit c4)) ▸
       at 4 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸
       at 5 2 (Toff234 ∷ Sw14 ∷ []) (wl0857 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ Sw14 ∷ CCZ123 ∷ Bx3-20 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ Sw14 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Sw14 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 7 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸
       at 8 2 (Toff312 ∷ Sw14 ∷ []) (wl0855 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 11 2 (Toff234 ∷ Sw14 ∷ []) (wl0857 (lit c4)) ▸
       at 12 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Sw14 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ Sw14 ∷ []) (Bx3-2140 ∷ [])
  b2 = at 13 2 (Toff234 ∷ Sw14 ∷ []) (wl0857 (lit c4)) ▸
       at 14 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 15 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx2-340 ∷ []) (refl) ▸
       at 5 6 (Bx2-340 ∷ []) (refl) ▸
       at 0 6 (Bx3-2140 ∷ []) (refl) ▸ done


-- sym-bc @0312243140: 2 steps
lem-sym-bc-at0312243140 : Ws → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-sym-bc-at0312243140 c4 = run b0
  where
  b0 : Chain (Bx3-2410 ∷ []) (Bx3-2140 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0312243140 c4)) ▸
       at 0 3 (Bx3-2140 ∷ []) (lem-nat-SWbc-at0312243140 c4) ▸ done


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


-- box-perm-2341 @03102132: 4 steps
lem-box-perm-2341-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-box-perm-2341-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-1240 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸
       at 0 1 (Bx3-2410 ∷ []) (lem-pairs-at032032 c4) ▸
       at 0 1 (Bx3-2140 ∷ []) (lem-sym-bc-at0312243140 c4) ▸
       at 0 1 (Bx3-1240 ∷ []) (lem-sym-ab-at0312213440 c4) ▸ done


-- cQ @033440: 7 steps
lem-cQ-at033440 : Ws → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at033440 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸ done


-- box-tQ @033440: 13 steps
lem-box-tQ-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at033440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1240 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 0 2 (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) (wl0473 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ123 ∷ []) (lem-cQ-at033440 c4) ▸
       at 2 4 (Toff312 ∷ []) (wl0474 (lit c4)) ▸ done


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


-- cQ @0312213440: 7 steps
lem-cQ-at0312213440 : Ws → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at0312213440 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS13⁻ ∷ []) (sym (wp0734 c4)) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸ done


-- box-tQ @0312213440: 13 steps
lem-box-tQ-at0312213440 : Ws → ⟪ (Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at0312213440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2140 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 0 2 (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) (wl0473 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ123 ∷ []) (lem-cQ-at0312213440 c4) ▸
       at 2 4 (Toff312 ∷ []) (wl0474 (lit c4)) ▸ done


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


-- SWbc-box @0312213440: 11 steps
lem-SWbc-box-at0312213440 : Ws → ⟪ (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-SWbc-box-at0312213440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) (CX14 ∷ Bx3-2140 ∷ CX14 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 2 3 (Bx3-2140 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0312213440 c4) ▸
       at 3 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp0730 c4) ▸
       at 1 3 (Bx3-2140 ∷ CCZ024 ∷ []) (lem-CXcb-box-at0312213440 c4) ▸
       at 4 2 (CX14 ∷ CCZ012 ∷ []) (wp0145 c4) ▸
       at 3 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸
       at 2 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸ done

  b1 : Chain (CX14 ∷ Bx3-2140 ∷ CX14 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (Bx3-2140 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wp0738 c4) ▸
       at 0 3 (Bx3-2140 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0312213440 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done


-- nat-SWbc @0312213440: 23 steps
lem-nat-SWbc-at0312213440 : Ws → ⟪ (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ Sw14 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 1 2 (Toff324 ∷ Sw14 ∷ []) (wl0864 (lit c4)) ▸
       at 3 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 3 2 (Toff213 ∷ Sw14 ∷ []) (wl0865 (lit c4)) ▸
       at 4 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸
       at 5 2 (Toff213 ∷ Sw14 ∷ []) (wl0865 (lit c4)) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ Sw14 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ Sw14 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Sw14 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 7 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸
       at 8 2 (Toff324 ∷ Sw14 ∷ []) (wl0864 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 11 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 11 2 (Toff213 ∷ Sw14 ∷ []) (wl0865 (lit c4)) ▸
       at 12 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff324 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Sw14 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Sw14 ∷ []) (Bx3-2410 ∷ [])
  b2 = at 13 2 (Toff213 ∷ Sw14 ∷ []) (wl0865 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 15 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx2-310 ∷ []) (refl) ▸
       at 5 6 (Bx2-310 ∷ []) (refl) ▸
       at 0 6 (Bx3-2410 ∷ []) (refl) ▸ done


-- sym-bc @0312213440: 2 steps
lem-sym-bc-at0312213440 : Ws → ⟪ (Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-sym-bc-at0312213440 c4 = run b0
  where
  b0 : Chain (Bx3-2140 ∷ []) (Bx3-2410 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0312213440 c4)) ▸
       at 0 3 (Bx3-2410 ∷ []) (lem-nat-SWbc-at0312213440 c4) ▸ done


-- tP @0312243140: 7 steps
lem-tP-at0312243140 : Ws → ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ
lem-tP-at0312243140 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0435 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (sym (wl0434 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at0312243140 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff301 ∷ []) (wl0434 (lit c4)) ▸
       at 1 3 (Toff324 ∷ []) (wl0435 (lit c4)) ▸ done


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


-- QVQ @0312243140: 3 steps
lem-QVQ-at0312243140 : Ws → ⟪ (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-QVQ-at0312243140 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 1 4 (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at0312243140 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done


-- box-cP @0312243140: 12 steps
lem-box-cP-at0312243140 : Ws → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-box-cP-at0312243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2410 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wl0845 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wl0845 (lit c4))) ▸
       at 2 4 (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-QVQ-at0312243140 c4) ▸
       at 1 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at0312243140 c4) ▸
       at 2 2 [] (wl0442 (lit c4)) ▸ done


-- pairs @0312243140: 4 steps
lem-pairs-at0312243140 : Ws → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-pairs-at0312243140 c4 = run b0
  where
  b0 : Chain (Bx3-2410 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Toff301 ∷ Bx3-2410 ∷ Toff301 ∷ []) (sym (lem-P-box-at0312243140 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243140 c4) ▸
       at 4 2 [] (wl0443 (lit c4)) ▸
       at 0 4 (Bx3-1024 ∷ []) (sym (lem-box-tQ-at032032 c4)) ▸ done


-- box-perm-4123 @033440: 4 steps
lem-box-perm-4123-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-4123-at033440 c4 = run b0
  where
  b0 : Chain (Bx3-1240 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-2140 ∷ []) (lem-sym-ab-at033440 c4) ▸
       at 0 1 (Bx3-2410 ∷ []) (lem-sym-bc-at0312213440 c4) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-pairs-at0312243140 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸ done


-- box-box-1 @03102132: 105 steps
lem-box-box-1-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-box-box-1-at03102132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx3-0124 ∷ Bx0-3124 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ013 ∷ CX32 ∷ CS34 ∷ Toff024 ∷ [])
  b0 = at 0 1 (Bx3-1240 ∷ []) (lem-box-perm-2341-at03102132 c4) ▸
       at 0 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4) ▸
       at 4 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸
       at 3 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 4 2 (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) (wp0183 c4) ▸
       at 6 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0829 (lit c4)) ▸
       at 10 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 9 2 (CCZ013 ∷ CX32 ∷ []) (sym (wl0706 (lit c4))) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ013 ∷ CX32 ∷ CS34 ∷ Toff024 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ [])
  b1 = at 8 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 7 2 (CCZ013 ∷ CX32 ∷ []) (sym (wl0706 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 7 5 (CCZ234 ∷ []) (sym (wl0829 (lit c4))) ▸
       at 5 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 6 3 (Toff024 ∷ CCZ034 ∷ []) (wp0739 c4) ▸
       at 3 4 (Bx0-3124 ∷ []) (sym (lem-box-cP-at132132 c4)) ▸
       at 3 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸ done

  b2 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ Toff024 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ [])
  b2 = at 2 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 4 2 (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp0587 c4) ▸
       at 3 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (sym (wl0869 (lit c4))) ▸
       at 9 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 8 2 (Toff024 ∷ CS23 ∷ []) (wp0190 c4) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 6 2 (Toff024 ∷ CS12⁻ ∷ []) (wp0741 c4) ▸
       at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸ done

  b3 : Chain (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ Toff024 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ Toff024 ∷ Toff312 ∷ CCZ012 ∷ CS24 ∷ CCZ013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff024 ∷ CCZ034 ∷ [])
  b3 = at 4 2 (Toff024 ∷ CS12 ∷ []) (wp0524 c4) ▸
       at 3 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 4 7 (Toff312 ∷ []) (wl0869 (lit c4)) ▸
       at 6 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 10 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 9 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 8 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 7 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸ done

  b4 : Chain (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ Toff024 ∷ Toff312 ∷ CCZ012 ∷ CS24 ∷ CCZ013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff024 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff024 ∷ K3⁻ ∷ CCZ124 ∷ CCZ034 ∷ [])
  b4 = at 6 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 5 2 (CCZ013 ∷ CCZ012 ∷ []) (wl0704 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 5 3 (Toff312 ∷ []) (wl0870 (lit c4)) ▸
       at 6 2 (Toff024 ∷ CCZ124 ∷ []) (wp0743 c4) ▸
       at 5 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (sym (wl0869 (lit c4))) ▸
       at 11 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸ done

  b5 : Chain (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff024 ∷ K3⁻ ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ Bx0-3124 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b5 = at 10 2 (Toff024 ∷ CS23 ∷ []) (wp0190 c4) ▸
       at 9 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 8 2 (Toff024 ∷ CS12⁻ ∷ []) (wp0741 c4) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 6 2 (Toff024 ∷ CS12 ∷ []) (wp0524 c4) ▸
       at 5 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 6 7 (Toff312 ∷ []) (wl0869 (lit c4)) ▸
       at 2 4 (Bx0-3124 ∷ []) (sym (lem-box-cP-at132132 c4)) ▸ done

  b6 : Chain (Toff312 ∷ CCZ034 ∷ Bx0-3124 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ CS24 ∷ CCZ013 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ Toff024 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b6 = at 2 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸
       at 1 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 2 2 (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) (wp0183 c4) ▸
       at 4 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0829 (lit c4)) ▸
       at 8 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 7 2 (CCZ013 ∷ CX32 ∷ []) (sym (wl0706 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CX32 ∷ []) (sym (wl0706 (lit c4))) ▸ done

  b7 : Chain (Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ CS24 ∷ CCZ013 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ Toff024 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff312 ∷ Toff024 ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b7 = at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0829 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 4 3 (Toff024 ∷ CCZ034 ∷ []) (wp0739 c4) ▸
       at 1 4 (Bx0-3124 ∷ []) (sym (lem-box-cP-at132132 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸
       at 0 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 2 2 (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp0587 c4) ▸ done

  b8 : Chain (CCZ013 ∷ Toff312 ∷ Toff024 ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff024 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b8 = at 1 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (sym (wl0869 (lit c4))) ▸
       at 7 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 6 2 (Toff024 ∷ CS23 ∷ []) (wp0190 c4) ▸
       at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 4 2 (Toff024 ∷ CS12⁻ ∷ []) (wp0741 c4) ▸
       at 3 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 2 2 (Toff024 ∷ CS12 ∷ []) (wp0524 c4) ▸
       at 1 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸ done

  b9 : Chain (CCZ013 ∷ Toff024 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff024 ∷ Toff312 ∷ CCZ012 ∷ CCZ013 ∷ CCZ124 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b9 = at 2 7 (Toff312 ∷ []) (wl0869 (lit c4)) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 7 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸ done

  b10 : Chain (CCZ013 ∷ Toff024 ∷ Toff312 ∷ CCZ012 ∷ CCZ013 ∷ CCZ124 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ Toff024 ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b10 = at 3 2 (CCZ013 ∷ CCZ012 ∷ []) (wl0704 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 3 3 (Toff312 ∷ []) (wl0870 (lit c4)) ▸
       at 4 2 (Toff024 ∷ CCZ124 ∷ []) (wp0743 c4) ▸
       at 3 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (sym (wl0869 (lit c4))) ▸
       at 9 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 8 2 (Toff024 ∷ CS23 ∷ []) (wp0190 c4) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸ done

  b11 : Chain (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ Toff024 ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (Bx0-3124 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b11 = at 6 2 (Toff024 ∷ CS12⁻ ∷ []) (wp0741 c4) ▸
       at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 4 2 (Toff024 ∷ CS12 ∷ []) (wp0524 c4) ▸
       at 3 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 4 7 (Toff312 ∷ []) (wl0869 (lit c4)) ▸
       at 0 4 (Bx0-3124 ∷ []) (sym (lem-box-cP-at132132 c4)) ▸
       at 2 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸ done

  b12 : Chain (Bx0-3124 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (Bx0-3124 ∷ Bx3-1240 ∷ [])
  b12 = at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (Toff312 ∷ CCZ124 ∷ []) (wl0871 (lit c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸
       at 1 4 (Bx3-1240 ∷ []) (sym (lem-box-tQ-at033440 c4)) ▸ done

  b13 : Chain (Bx0-3124 ∷ Bx3-1240 ∷ []) (Bx0-3124 ∷ Bx3-0124 ∷ [])
  b13 = at 1 1 (Bx3-0124 ∷ []) (lem-box-perm-4123-at033440 c4) ▸ done


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


-- SWbc-box @132132: 11 steps
lem-SWbc-box-at132132 : Ws → ⟪ (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-SWbc-box-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) (CX12 ∷ Bx0-3124 ∷ CX12 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 4 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 2 3 (Bx0-3124 ∷ CCZ134 ∷ []) (lem-CXbc-box-at132132 c4) ▸
       at 3 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0678 (lit c4)) ▸
       at 1 3 (Bx0-3124 ∷ CCZ234 ∷ []) (lem-CXcb-box-at132132 c4) ▸
       at 4 2 (CX12 ∷ CCZ134 ∷ []) (wl0679 (lit c4)) ▸
       at 3 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl0680 (lit c4)) ▸
       at 2 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl0680 (lit c4)) ▸ done

  b1 : Chain (CX12 ∷ Bx0-3124 ∷ CX12 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ []) (Bx0-3124 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wl0681 (lit c4)) ▸
       at 0 3 (Bx0-3124 ∷ CCZ134 ∷ []) (lem-CXbc-box-at132132 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done


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


-- sym-bc @132132: 2 steps
lem-sym-bc-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym-bc-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at132132 c4)) ▸
       at 0 3 (Bx0-3214 ∷ []) (lem-nat-SWbc-at132132 c4) ▸ done


-- sym-ab @1331: 18 steps
lem-sym-ab-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym-ab-at1331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3214 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (wp0154 c4) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (sym (wp0153 c4)) ▸
       at 4 1 (Bx0-24 ∷ []) (refl) ▸
       at 7 1 (Bx0-24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ [])
  b1 = at 2 6 (Bx2-014 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (wp0154 c4) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (sym (wp0153 c4)) ▸
       at 7 1 (Bx0-24 ∷ []) (refl) ▸
       at 10 1 (Bx0-24 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (Bx0-2314 ∷ [])
  b2 = at 5 6 (Bx2-014 ∷ []) (refl) ▸
       at 0 6 (Bx0-2314 ∷ []) (refl) ▸ done


-- box-perm-2431 @132132: 3 steps
lem-box-perm-2431-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-2431-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-3214 ∷ []) (lem-sym-bc-at132132 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-ab-at1331 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-pairs-at122331 c4) ▸ done


-- box-perm-1423 @03102132: 3 steps
lem-box-perm-1423-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-1423-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-sym-bc-at032032 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-pairs-at0330 c4) ▸ done

