{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D012 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0003 ; wl0004 ; wl0157 ; wl0159 ; wl0166 ; wl0181 ; wl0185 ; wl0200 ; wl0201 ; wl0202 ; wl0203 ; wl0204 ; wl0205 ; wl0206 ; wl0207 ; wl0208 ; wl0209 ; wl0211 ; wl0217 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0229 ; wl0232 ; wl0233 ; wl0234 ; wl0235 ; wl0242 ; wl0252 ; wl0254 ; wl0256 ; wl0257 ; wl0259 ; wl0261 ; wl0263 ; wl0264 ; wl0266 ; wl0321 ; wl0547 ; wl0621 ; wl0644 ; wl0646 ; wl0648 ; wl0650 ; wl0652 ; wl0682 ; wl0683 ; wl0684 ; wl0735 ; wl0825 ; wl0826 ; wl0827 ; wl0832 ; wl0872 ; wl0874 ; wl0894 ; wl0896 ; wl0900 ; wl0907 ; wl0910 ; wl0975 ; wl0980 ; wl0984 ; wl0999 ; wl1000 ; wl1001 ; wl1002 ; wl1003 ; wl1004 ; wl1005 ; wl1006 ; wl1007 ; wl1008 ; wl1009 ; wl1010 ; wl1011 ; wl1012 ; wl1013 ; wl1014 ; wl1015 ; wl1016 ; wl1017 ; wl1018 ; wl1019 ; wl1020 ; wl1021 ; wl1022 ; wl1023 ; wl1024 ; wp0020 ; wp0023 ; wp0034 ; wp0035 ; wp0036 ; wp0049 ; wp0050 ; wp0051 ; wp0052 ; wp0053 ; wp0054 ; wp0055 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0067 ; wp0068 ; wp0069 ; wp0070 ; wp0071 ; wp0072 ; wp0074 ; wp0081 ; wp0082 ; wp0091 ; wp0092 ; wp0109 ; wp0130 ; wp0131 ; wp0158 ; wp0159 ; wp0160 ; wp0216 ; wp0263 ; wp0265 ; wp0270 ; wp0380 ; wp0381 ; wp0394 ; wp0513 ; wp0527 ; wp0529 ; wp0546 ; wp0669 ; wp0717 ; wp0718 ; wp0725 ; wp0785 ; wp0805 ; wp0806 ; wp0807 ; wp0808 ; wp0809 ; wp0810 ; wp0811 ; wp0812 ; wp0813 ; wp0814 ; wp0815 ; wp0816 ; wp0817 ; wp0818 ; wp0819 ; wp0820 ; wp0821 ; wp0822 ; wp0823 ; wp0824 ; wp0825 ; wp0826 ; wp0827)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box-tQ-at122441 ; lem-tP-at122441)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-box-tQ-at132132 ; lem-box-tQ-at2332)
open import Examples.Groups.Clifford+CS.FiveV.D.D003 using (lem-box-tQ-at12233441 ; lem-sym-ab-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-box-cP-at12233441 ; lem-box-perm-1324-at122441 ; lem-box-tQ-at14213243 ; lem-cQ-at14213243 ; lem-sym-bc-at122441 ; lem-tP-at12233441)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-TOFF014-CSd23)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX14-TOFF023 ; lem-comm-CX23-CCZ014 ; lem-comm-CZ14-TOFF023 ; lem-comm-SWAP23-BOX⟨0·14⟩)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS14-TOFF023 ; lem-comm-CS24-TOFF013)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CZ13-TOFF024 ; lem-comm-CZ23-TOFF014)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CCZ014-CX23 ; lem-comm-CX23-TOFF014 ; lem-comm-TOFF023-CX14)
-- F4-CS1-CS1: 286 steps
lem-F4-CS1-CS1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-CS1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 4 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 10 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 9 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 8 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 4 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (wl0208 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 5 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸ done

  b3 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 6 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 8 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 9 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸ done

  b4 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b5 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b5 = at 13 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 12 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 11 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 7 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b6 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b6 = at 6 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 9 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 8 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 12 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 11 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 10 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 9 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸ done

  b7 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b7 = at 9 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 7 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 8 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 3 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 4 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸ done

  b8 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b8 = at 5 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 6 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 8 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 7 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸ done

  b9 : Chain (X4 ∷ Bx0-1423 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b9 = at 5 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 4 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 2 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 3 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 11 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸ done

  b10 : Chain (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b10 = at 10 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 7 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 5 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 6 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸ done

  b11 : Chain (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b11 = at 7 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 6 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 10 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 7 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b12 : Chain (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b12 = at 5 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 6 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b13 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b13 = at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸ done

  b14 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b14 = at 3 3 (X4 ∷ []) (wl0208 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b15 : Chain (Bx0-1423 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b15 = at 4 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 2 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b16 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b16 = at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 8 (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) (wl0999 (lit c4)) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸ done

  b17 : Chain (Bx0-1423 ∷ X4 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b17 = at 3 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 5 2 [] (wl0263 (lit c4)) ▸
       at 4 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0894 (lit c4))) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸ done

  b18 : Chain (Bx0-1423 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b18 = at 6 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 6 (CX23 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1001 (lit c4))) ▸
       at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CX20 ∷ CX23 ∷ Toff023 ∷ []) (sym (wl1002 (lit c4))) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 4 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸ done

  b19 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b19 = at 10 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 10 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸ done

  b20 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b20 = at 9 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 2 (CX20 ∷ Toff023 ∷ []) (sym (wl1003 (lit c4))) ▸
       at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 4 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 5 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 8 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸ done

  b21 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ CX23 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff023 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b21 = at 4 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 5 2 (CX20 ∷ CX23 ∷ Toff023 ∷ []) (sym (wl1002 (lit c4))) ▸
       at 7 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 9 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 8 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 11 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸ done

  b22 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ CX23 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff023 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b22 = at 12 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 8 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 9 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 3 3 (CCZ124 ∷ []) (sym (wp0380 c4)) ▸
       at 5 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 3 4 (CX23 ∷ Toff324 ∷ []) (wl1004 (lit c4)) ▸
       at 2 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b23 : Chain (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CX23 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b23 = at 3 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 4 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 5 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 9 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 3 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b24 : Chain (Bx0-1423 ∷ X4 ∷ CX23 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS13 ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b24 = at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (Toff324 ∷ X4 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 4 2 (CS13 ∷ X4 ∷ []) (sym (wl0896 (lit c4))) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS13 ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b25 = at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 5 (CS13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1005 (lit c4))) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 3 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b26 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ [])
  b26 = at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X4 ∷ []) (sym (wl0896 (lit c4))) ▸
       at 5 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0894 (lit c4))) ▸
       at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b27 = at 5 6 (CX23 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1001 (lit c4))) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (CX20 ∷ CX23 ∷ Toff023 ∷ []) (sym (wl1002 (lit c4))) ▸
       at 9 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 6 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 12 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b28 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 12 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 15 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 16 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 11 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b29 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ Toff023 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b29 = at 5 2 (CX20 ∷ Toff023 ∷ []) (sym (wl1003 (lit c4))) ▸
       at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 6 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 10 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b30 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ Toff023 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ CX23 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b30 = at 7 2 (CX20 ∷ CX23 ∷ Toff023 ∷ []) (sym (wl1002 (lit c4))) ▸
       at 9 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 11 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 10 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 11 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 12 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 13 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 14 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸ done

  b31 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ CX23 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b31 = at 10 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 11 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 5 3 (CCZ124 ∷ []) (sym (wp0380 c4)) ▸
       at 7 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 5 4 (CX23 ∷ Toff324 ∷ []) (wl1004 (lit c4)) ▸
       at 4 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b32 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b32 = at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b33 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13⁻ ∷ X4 ∷ [])
  b33 = at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 3 (Toff324 ∷ X4 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ X4 ∷ []) (sym (wl0900 (lit c4))) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13⁻ ∷ X4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b34 = at 6 5 (CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1006 (lit c4))) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 6 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 5 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b35 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b35 = at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X4 ∷ []) (sym (wl0900 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- tP @14213243: 7 steps
lem-tP-at14213243 : Ws → ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-tP-at14213243 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (sym (wp0049 c4)) ▸
       at 3 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (sym (wl0200 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at14213243 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff023 ∷ []) (wl0200 (lit c4)) ▸
       at 1 3 (Toff014 ∷ []) (wp0049 c4) ▸ done


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


-- QVQ @14213243: 3 steps
lem-QVQ-at14213243 : Ws → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at14213243 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  b0 = at 0 0 (Toff023 ∷ Toff023 ∷ []) (sym (wl0203 (lit c4))) ▸
       at 1 4 (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at14213243 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done


-- box-cP @14213243: 12 steps
lem-box-cP-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4123 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 2 4 (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-QVQ-at14213243 c4) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at14213243 c4) ▸
       at 2 2 [] (wp0051 c4) ▸ done


-- pairs @14213243: 4 steps
lem-pairs-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-pairs-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 1 (Toff023 ∷ Bx0-4123 ∷ Toff023 ∷ []) (sym (lem-P-box-at14213243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at14213243 c4) ▸
       at 4 2 [] (wl0203 (lit c4)) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸ done


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


-- SWbc-box @12233441: 11 steps
lem-SWbc-box-at12233441 : Ws → ⟪ (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-SWbc-box-at12233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) (CX34 ∷ Bx0-2341 ∷ CX34 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 4 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 2 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-CXbc-box-at12233441 c4) ▸
       at 3 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl0652 (lit c4)) ▸
       at 1 3 (Bx0-2341 ∷ CCZ124 ∷ []) (lem-CXcb-box-at12233441 c4) ▸
       at 4 2 (CX34 ∷ CCZ123 ∷ []) (wl1008 (lit c4)) ▸
       at 3 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0650 (lit c4)) ▸
       at 2 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0650 (lit c4)) ▸ done

  b1 : Chain (CX34 ∷ Bx0-2341 ∷ CX34 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ []) (Bx0-2341 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl1009 (lit c4)) ▸
       at 0 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-CXbc-box-at12233441 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done


-- nat-SWbc @12233441: 23 steps
lem-nat-SWbc-at12233441 : Ws → ⟪ (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-nat-SWbc-at12233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ Sw34 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 1 2 (Toff024 ∷ Sw34 ∷ []) (wp0812 c4) ▸
       at 3 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 3 2 (Toff203 ∷ Sw34 ∷ []) (wp0813 c4) ▸
       at 4 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 5 2 (Toff203 ∷ Sw34 ∷ []) (wp0813 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ Sw34 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ Sw34 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Sw34 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 7 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 8 2 (Toff024 ∷ Sw34 ∷ []) (wp0812 c4) ▸
       at 9 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 11 2 (Toff203 ∷ Sw34 ∷ []) (wp0813 c4) ▸
       at 12 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Sw34 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Sw34 ∷ []) (Bx0-2431 ∷ [])
  b2 = at 13 2 (Toff203 ∷ Sw34 ∷ []) (wp0813 c4) ▸
       at 14 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 15 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx2-031 ∷ []) (refl) ▸
       at 5 6 (Bx2-031 ∷ []) (refl) ▸
       at 0 6 (Bx0-2431 ∷ []) (refl) ▸ done


-- sym-bc @12233441: 2 steps
lem-sym-bc-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-sym-bc-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at12233441 c4)) ▸
       at 0 3 (Bx0-2431 ∷ []) (lem-nat-SWbc-at12233441 c4) ▸ done


-- box-perm-3241 @243243: 3 steps
lem-box-perm-3241-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-3241-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-pairs-at14213243 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-sym-bc-at12233441 c4) ▸ done


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


-- pairs @12233441: 4 steps
lem-pairs-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-pairs-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 1 (Toff014 ∷ Bx0-2341 ∷ Toff014 ∷ []) (sym (lem-P-box-at12233441 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 4 2 [] (wp0051 c4) ▸
       at 0 4 (Bx0-4123 ∷ []) (sym (lem-box-tQ-at14213243 c4)) ▸ done


-- sym-ab @14213243: 18 steps
lem-sym-ab-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym-ab-at14213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-4123 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (sym (wl0205 (lit c4))) ▸
       at 4 1 (Bx0-13 ∷ []) (refl) ▸
       at 7 1 (Bx0-13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ [])
  b1 = at 2 6 (Bx1-023 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (sym (wl0205 (lit c4))) ▸
       at 7 1 (Bx0-13 ∷ []) (refl) ▸
       at 10 1 (Bx0-13 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (Bx0-1423 ∷ [])
  b2 = at 5 6 (Bx1-023 ∷ []) (refl) ▸
       at 0 6 (Bx0-1423 ∷ []) (refl) ▸ done


-- box-perm-4213 @122441: 3 steps
lem-box-perm-4213-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-4213-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-2341 ∷ []) (lem-sym-bc-at122441 c4) ▸
       at 0 1 (Bx0-4123 ∷ []) (lem-pairs-at12233441 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4) ▸ done


-- F4-CS1-CS2: 248 steps
lem-F4-CS1-CS2 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-CS2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (run b30))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 4 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl0232 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 6 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 4 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CCZ024 ∷ CS13⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 6 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 5 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CCZ024 ∷ CS13⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff324 ∷ Toff014 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 6 2 (Toff013 ∷ CS13⁻ ∷ []) (wl0907 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CS13⁻ ∷ []) (wl0907 (lit c4)) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 5 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 4 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (sym (wp0814 c4)) ▸
       at 6 2 (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0815 c4) ▸ done

  b4 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff324 ∷ Toff014 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 11 2 (Toff014 ∷ K3⁻ ∷ []) (wp0816 c4) ▸
       at 10 2 (Toff014 ∷ CS24 ∷ []) (wp0817 c4) ▸
       at 9 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸
       at 8 2 (Toff014 ∷ CS34⁻ ∷ []) (wp0818 c4) ▸
       at 7 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸
       at 6 2 (Toff014 ∷ CS34 ∷ []) (wp0546 c4) ▸
       at 5 2 (Toff014 ∷ K3 ∷ []) (wp0819 c4) ▸ done

  b5 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CCZ023 ∷ CCZ124 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b5 = at 6 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 8 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 12 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 11 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 10 2 (CCZ023 ∷ CS24⁻ ∷ []) (sym (wp0820 c4)) ▸
       at 9 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 8 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b6 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CCZ023 ∷ CCZ124 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ Toff014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b6 = at 7 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 6 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (sym (wp0814 c4)) ▸
       at 7 3 (Toff324 ∷ []) (wp0821 c4) ▸
       at 8 2 (Toff014 ∷ CCZ124 ∷ []) (wp0822 c4) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 13 2 (Toff014 ∷ K3⁻ ∷ []) (wp0816 c4) ▸
       at 12 2 (Toff014 ∷ CS24 ∷ []) (wp0817 c4) ▸
       at 11 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸ done

  b7 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ Toff014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b7 = at 10 2 (Toff014 ∷ CS34⁻ ∷ []) (wp0818 c4) ▸
       at 9 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸
       at 8 2 (Toff014 ∷ CS34 ∷ []) (wp0546 c4) ▸
       at 7 2 (Toff014 ∷ K3 ∷ []) (wp0819 c4) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 4 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 4 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸ done

  b8 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b8 = at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CS13 ∷ []) (wl0910 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 6 2 (Toff013 ∷ CS13 ∷ []) (wl0910 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 3 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸ done

  b9 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ Toff014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b9 = at 2 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (sym (wp0814 c4)) ▸
       at 4 2 (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0815 c4) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 9 2 (Toff014 ∷ K3⁻ ∷ []) (wp0816 c4) ▸
       at 8 2 (Toff014 ∷ CS24 ∷ []) (wp0817 c4) ▸
       at 7 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸
       at 6 2 (Toff014 ∷ CS34⁻ ∷ []) (wp0818 c4) ▸
       at 5 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸ done

  b10 : Chain (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ Toff014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CS24 ∷ CCZ023 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b10 = at 4 2 (Toff014 ∷ CS34 ∷ []) (wp0546 c4) ▸
       at 3 2 (Toff014 ∷ K3 ∷ []) (wp0819 c4) ▸
       at 4 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 10 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 9 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 8 2 (CCZ023 ∷ CS24⁻ ∷ []) (sym (wp0820 c4)) ▸
       at 7 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸ done

  b11 : Chain (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CS24 ∷ CCZ023 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b11 = at 6 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 4 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (sym (wp0814 c4)) ▸
       at 5 3 (Toff324 ∷ []) (wp0821 c4) ▸
       at 6 2 (Toff014 ∷ CCZ124 ∷ []) (wp0822 c4) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 11 2 (Toff014 ∷ K3⁻ ∷ []) (wp0816 c4) ▸ done

  b12 : Chain (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Bx0-2341 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b12 = at 10 2 (Toff014 ∷ CS24 ∷ []) (wp0817 c4) ▸
       at 9 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸
       at 8 2 (Toff014 ∷ CS34⁻ ∷ []) (wp0818 c4) ▸
       at 7 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸
       at 6 2 (Toff014 ∷ CS34 ∷ []) (wp0546 c4) ▸
       at 5 2 (Toff014 ∷ K3 ∷ []) (wp0819 c4) ▸
       at 6 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 2 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸ done

  b13 : Chain (X4 ∷ Bx0-1423 ∷ Bx0-2341 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b13 = at 2 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-box-perm-3241-at243243 c4) ▸
       at 2 1 (Bx0-1423 ∷ []) (lem-box-perm-4213-at122441 c4) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 2 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl0232 (lit c4)) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b14 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b14 = at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b15 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b15 = at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b16 : Chain (Bx0-2431 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b16 = at 4 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 2 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b17 : Chain (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b17 = at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 8 (Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) (wl1010 (lit c4)) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸ done

  b18 : Chain (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b18 = at 4 3 (CS13 ∷ Toff324 ∷ CCZ124 ∷ []) (wl1011 (lit c4)) ▸
       at 6 2 [] (wl0263 (lit c4)) ▸
       at 4 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0975 (lit c4))) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸ done

  b19 : Chain (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b19 = at 6 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 6 (CX31 ∷ Toff134 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1012 (lit c4))) ▸
       at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CX31 ∷ Toff023 ∷ []) (sym (wl0832 (lit c4))) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸
       at 6 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 7 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸ done

  b20 : Chain (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b20 = at 9 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 11 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 12 2 (K1⁻ ∷ Toff023 ∷ []) (sym (wl1014 (lit c4))) ▸
       at 6 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸
       at 4 3 (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) (wp0824 c4) ▸
       at 3 2 (CX31 ∷ Toff023 ∷ []) (sym (wl0832 (lit c4))) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸ done

  b21 : Chain (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b21 = at 4 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 5 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 9 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 10 2 (K1⁻ ∷ Toff023 ∷ []) (sym (wl1014 (lit c4))) ▸
       at 4 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸ done

  b22 : Chain (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b22 = at 2 3 (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) (wp0824 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (Toff134 ∷ X4 ∷ []) (sym (wl0235 (lit c4))) ▸
       at 4 2 (CS12 ∷ X4 ∷ []) (sym (wl0980 (lit c4))) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b23 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b23 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 5 (CS12 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1015 (lit c4))) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸
       at 4 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 3 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸ done

  b24 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ [])
  b24 = at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X4 ∷ []) (sym (wl0980 (lit c4))) ▸
       at 5 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0975 (lit c4))) ▸
       at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b25 = at 8 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 6 (CX31 ∷ Toff134 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1012 (lit c4))) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (CX31 ∷ Toff023 ∷ []) (sym (wl0832 (lit c4))) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸
       at 8 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 9 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸ done

  b26 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b26 = at 11 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 14 2 (K1⁻ ∷ Toff023 ∷ []) (sym (wl1014 (lit c4))) ▸
       at 8 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸
       at 6 3 (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) (wp0824 c4) ▸
       at 5 2 (CX31 ∷ Toff023 ∷ []) (sym (wl0832 (lit c4))) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸ done

  b27 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b27 = at 6 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 7 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 11 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 12 2 (K1⁻ ∷ Toff023 ∷ []) (sym (wl1014 (lit c4))) ▸
       at 6 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸ done

  b28 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS12⁻ ∷ X4 ∷ [])
  b28 = at 4 3 (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) (wp0824 c4) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 3 (Toff134 ∷ X4 ∷ []) (sym (wl0235 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0984 (lit c4))) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b29 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS12⁻ ∷ X4 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b29 = at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 5 (CS12⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1016 (lit c4))) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff023 ∷ []) (sym (wl1017 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CCZ014 ∷ []) (wp0265 c4) ▸
       at 6 2 (CS12⁻ ∷ Toff023 ∷ []) (sym (wl1017 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ CCZ014 ∷ []) (wp0265 c4) ▸ done

  b30 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b30 = at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0984 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


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


-- pairs @122441: 4 steps
lem-pairs-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-pairs-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 1 (Toff013 ∷ Bx0-2431 ∷ Toff013 ∷ []) (sym (lem-P-box-at122441 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 [] (wl0229 (lit c4)) ▸
       at 0 4 (Bx0-3124 ∷ []) (sym (lem-box-tQ-at132132 c4)) ▸ done


-- sym-ab @132132: 18 steps
lem-sym-ab-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym-ab-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3124 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (sym (wp0130 c4)) ▸
       at 4 1 (Bx0-14 ∷ []) (refl) ▸
       at 7 1 (Bx0-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ [])
  b1 = at 2 6 (Bx1-024 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (sym (wp0130 c4)) ▸
       at 7 1 (Bx0-14 ∷ []) (refl) ▸
       at 10 1 (Bx0-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (Bx0-1324 ∷ [])
  b2 = at 5 6 (Bx1-024 ∷ []) (refl) ▸
       at 0 6 (Bx0-1324 ∷ []) (refl) ▸ done


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


-- SWbc-box @2332: 11 steps
lem-SWbc-box-at2332 : Ws → ⟪ (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-SWbc-box-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) (CX32 ∷ Bx0-1324 ∷ CX32 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (sym (wl1020 (lit c4))) ▸
       at 4 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (sym (wl1020 (lit c4))) ▸
       at 2 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CXbc-box-at2332 c4) ▸
       at 3 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0261 (lit c4)) ▸
       at 1 3 (Bx0-1324 ∷ CCZ124 ∷ []) (lem-CXcb-box-at2332 c4) ▸
       at 4 2 (CX32 ∷ CCZ134 ∷ []) (wl1021 (lit c4)) ▸
       at 3 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl0259 (lit c4)) ▸
       at 2 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl0259 (lit c4)) ▸ done

  b1 : Chain (CX32 ∷ Bx0-1324 ∷ CX32 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) (Bx0-1324 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wl1022 (lit c4)) ▸
       at 0 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CXbc-box-at2332 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done


-- nat-SWbc @2332: 23 steps
lem-nat-SWbc-at2332 : Ws → ⟪ (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-nat-SWbc-at2332 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ Sw23 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (sym (wl0266 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (wl1023 (lit c4)) ▸
       at 3 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (wl1024 (lit c4)) ▸
       at 4 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸
       at 5 2 (Toff103 ∷ Sw23 ∷ []) (wl1024 (lit c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ Sw23 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ Sw23 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Sw23 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw23 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 7 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸
       at 8 2 (Toff012 ∷ Sw23 ∷ []) (wl1023 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ Sw23 ∷ []) (sym (wl0266 (lit c4))) ▸
       at 11 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw23 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 11 2 (Toff103 ∷ Sw23 ∷ []) (wl1024 (lit c4)) ▸
       at 12 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Sw23 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Sw23 ∷ []) (Bx0-1234 ∷ [])
  b2 = at 13 2 (Toff103 ∷ Sw23 ∷ []) (wl1024 (lit c4)) ▸
       at 14 2 (CCZ013 ∷ Sw23 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 15 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸
       at 16 2 [] (wl0003 (lit c4)) ▸
       at 2 6 (Bx1-034 ∷ []) (refl) ▸
       at 5 6 (Bx1-034 ∷ []) (refl) ▸
       at 0 6 (Bx0-1234 ∷ []) (refl) ▸ done


-- sym-bc @2332: 2 steps
lem-sym-bc-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym-bc-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at2332 c4)) ▸
       at 0 3 (Bx0-1234 ∷ []) (lem-nat-SWbc-at2332 c4) ▸ done


-- box-perm-4132 @122441: 3 steps
lem-box-perm-4132-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-4132-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-3124 ∷ []) (lem-pairs-at122441 c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym-ab-at132132 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym-bc-at2332 c4) ▸ done

