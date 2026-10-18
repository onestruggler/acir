{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D039 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0166 ; wl0217 ; wl0220 ; wl0246 ; wl0256 ; wl0263 ; wl0305 ; wl0321 ; wl0431 ; wl0450 ; wl0621 ; wl0743 ; wl0872 ; wl0907 ; wl0910 ; wl1037 ; wl1152 ; wl1375 ; wl1376 ; wl1377 ; wl1378 ; wp0034 ; wp0035 ; wp0036 ; wp0094 ; wp0095 ; wp0109 ; wp0293 ; wp0513 ; wp0546 ; wp0669 ; wp0785 ; wp0790 ; wp0816 ; wp0817 ; wp0818 ; wp0819 ; wp0820 ; wp0821 ; wp0827 ; wp0839 ; wp1046 ; wp1214 ; wp1215)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.FiveV.D.D003 using (lem-sym-ab-at1221)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-box-cP-at12233441 ; lem-box-perm-1324-at122441)
open import Examples.Groups.Clifford+CS.FiveV.D.D012 using (lem-box-perm-4132-at122441)
open import Examples.Groups.Clifford+CS.FiveV.D.D037 using (lem-L-CCZ-1-part0)
open import Examples.Groups.Clifford+CS.FiveV.D.D038 using (lem-L-CCZ-1-part1)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CCZ024-CX13)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CCZ023-CX14 ; lem-comm-CCZ024-CS13 ; lem-comm-CCZ024-CSd13 ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF014-CX23)
-- L-CCZ-1 part2: 500 steps
lem-L-CCZ-1-part2 : Ws → ⟪ (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-L-CCZ-1-part2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b0 = at 20 3 (Toff324 ∷ []) (wp0821 c4) ▸
       at 22 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 22 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 22 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 26 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 25 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 26 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 27 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸ done

  b1 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b1 = at 28 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 29 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 25 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 24 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 24 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 23 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 24 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 25 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ K2 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b2 = at 26 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 27 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 23 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 22 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 23 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 23 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 27 1 (K2 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl1376 (lit c4))) ▸
       at 26 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸ done

  b3 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ K2 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b3 = at 27 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 28 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 29 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 30 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 31 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 32 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl1375 (lit c4))) ▸
       at 26 7 (Toff234 ∷ []) (wl1376 (lit c4)) ▸
       at 25 2 (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0790 c4) ▸ done

  b4 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ K2 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ Toff013 ∷ CCZ034 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b4 = at 25 1 (K2 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl1376 (lit c4))) ▸
       at 24 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸
       at 25 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 26 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 27 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 28 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 29 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 30 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl1375 (lit c4))) ▸ done

  b5 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ K2 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ Toff013 ∷ CCZ034 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ034 ∷ CCZ034 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b5 = at 24 7 (Toff234 ∷ []) (wl1376 (lit c4)) ▸
       at 25 2 (CCZ034 ∷ CCZ134 ∷ Toff013 ∷ []) (sym (wp1214 c4)) ▸
       at 23 2 (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0790 c4) ▸
       at 25 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 27 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 26 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 27 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 28 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b6 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ034 ∷ CCZ034 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b6 = at 29 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 30 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 26 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 23 3 (Toff234 ∷ []) (wp1215 c4) ▸
       at 25 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 25 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 28 2 (CCZ134 ∷ Toff013 ∷ []) (sym (wp0293 c4)) ▸
       at 28 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸ done

  b7 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b7 = at 27 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 28 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 29 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 30 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 31 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 27 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 26 2 (CCZ134 ∷ Toff013 ∷ []) (sym (wp0293 c4)) ▸
       at 26 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸ done

  b8 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Bx0-2341 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b8 = at 25 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 26 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 27 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 28 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 29 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 25 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 26 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 26 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸ done

  b9 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Bx0-2341 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b9 = at 26 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 30 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 29 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 30 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 31 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 32 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 33 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 34 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸ done

  b10 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ Toff014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b10 = at 35 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 29 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 28 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 28 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 27 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 28 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 29 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 30 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸ done

  b11 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ Toff014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CCZ023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b11 = at 31 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 32 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸
       at 33 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 27 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 28 2 (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (sym (wp0839 c4)) ▸
       at 26 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 28 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 30 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸ done

  b12 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CCZ023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-2341 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b12 = at 29 2 (CS24 ∷ CCZ023 ∷ []) (wp0513 c4) ▸
       at 30 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 31 2 (CS24⁻ ∷ CCZ023 ∷ []) (wp0820 c4) ▸
       at 32 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 33 2 (CS12 ∷ CCZ023 ∷ []) (wl0621 (lit c4)) ▸
       at 29 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 26 3 (Toff324 ∷ []) (wp0821 c4) ▸
       at 28 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸ done

  b13 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-2341 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b13 = at 28 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 28 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 32 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 31 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 32 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 33 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 34 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 35 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸ done

  b14 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b14 = at 31 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 30 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 30 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 29 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 30 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 31 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 32 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 33 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸ done

  b15 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b15 = at 29 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 28 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 29 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 29 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 33 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 32 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 33 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 34 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸ done

  b16 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b16 = at 35 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 36 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 32 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 31 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 31 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 30 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 31 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 32 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸ done

  b17 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b17 = at 33 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 34 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 30 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 29 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 30 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 30 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 30 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 34 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b18 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff324 ∷ Toff014 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b18 = at 33 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 34 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 35 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 36 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 37 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 38 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸
       at 39 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 33 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b19 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff324 ∷ Toff014 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b19 = at 32 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 32 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 31 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 32 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 33 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 34 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 35 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 36 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸ done

  b20 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CS24 ∷ CX14 ∷ CCZ023 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b20 = at 37 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 31 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 32 2 (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (sym (wp0839 c4)) ▸
       at 30 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 32 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 34 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 33 2 (CS24 ∷ CCZ023 ∷ []) (wp0513 c4) ▸
       at 34 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸ done

  b21 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CS24 ∷ CX14 ∷ CCZ023 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b21 = at 35 2 (CS24⁻ ∷ CCZ023 ∷ []) (wp0820 c4) ▸
       at 36 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 37 2 (CS12 ∷ CCZ023 ∷ []) (wl0621 (lit c4)) ▸
       at 33 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 30 3 (Toff324 ∷ []) (wp0821 c4) ▸
       at 32 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 32 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 32 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b22 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b22 = at 36 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 35 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 36 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 37 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 38 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 39 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 35 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 34 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸ done

  b23 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b23 = at 34 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 33 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 34 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 35 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 36 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 37 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 33 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 32 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸ done

  b24 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b24 = at 33 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 33 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 36 2 (CS13 ∷ Toff013 ∷ []) (sym (wl0910 (lit c4))) ▸
       at 35 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4)) ▸
       at 34 2 (CS13 ∷ Toff013 ∷ []) (sym (wl0910 (lit c4))) ▸
       at 33 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4)) ▸
       at 34 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 34 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b25 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b25 = at 38 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 37 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 38 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 39 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 40 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 41 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 37 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 36 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸ done

  b26 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b26 = at 36 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 35 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 36 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 37 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 38 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 39 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 35 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 34 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸ done

  b27 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ Toff014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b27 = at 35 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 35 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 35 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 39 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 38 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 39 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 40 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 41 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸ done

  b28 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ Toff014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ Toff014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b28 = at 42 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 43 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸
       at 44 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 38 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 37 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 37 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 36 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 37 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸ done

  b29 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ Toff014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ023 ∷ CCZ024 ∷ CCZ124 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b29 = at 38 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 39 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 40 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 41 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸
       at 42 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 36 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 37 2 (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (sym (wp0839 c4)) ▸
       at 35 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸ done

  b30 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ023 ∷ CCZ024 ∷ CCZ124 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b30 = at 37 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 39 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 38 2 (CS24 ∷ CCZ023 ∷ []) (wp0513 c4) ▸
       at 39 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 40 2 (CS24⁻ ∷ CCZ023 ∷ []) (wp0820 c4) ▸
       at 41 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 42 2 (CS12 ∷ CCZ023 ∷ []) (wl0621 (lit c4)) ▸
       at 38 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b31 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b31 = at 35 3 (Toff324 ∷ []) (wp0821 c4) ▸
       at 37 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 37 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 37 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 41 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 40 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 41 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 42 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸ done

  b32 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b32 = at 43 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 44 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 40 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 39 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 39 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 38 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 39 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 40 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸ done

  b33 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CS13⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b33 = at 41 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 42 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 38 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 37 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 38 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 38 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 41 2 (CS13⁻ ∷ Toff013 ∷ []) (sym (wl0907 (lit c4))) ▸
       at 40 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸ done

  b34 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CS13⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b34 = at 39 2 (CS13⁻ ∷ Toff013 ∷ []) (sym (wl0907 (lit c4))) ▸
       at 38 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸
       at 39 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 39 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 43 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 42 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 43 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 44 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸ done

  b35 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b35 = at 45 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 46 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 42 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 41 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 41 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 40 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 41 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 42 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸ done

  b36 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b36 = at 43 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 44 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 40 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 39 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 40 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 40 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 40 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 44 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b37 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff324 ∷ Toff014 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b37 = at 43 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 44 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 45 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 46 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 47 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 48 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸
       at 49 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 43 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b38 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff324 ∷ Toff014 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b38 = at 42 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 42 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 41 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 42 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 43 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 44 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 45 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 46 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸ done

  b39 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CS24 ∷ CX14 ∷ CCZ023 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b39 = at 47 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 41 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 42 2 (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (sym (wp0839 c4)) ▸
       at 40 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 42 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 44 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 43 2 (CS24 ∷ CCZ023 ∷ []) (wp0513 c4) ▸
       at 44 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸ done

  b40 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CS24 ∷ CX14 ∷ CCZ023 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b40 = at 45 2 (CS24⁻ ∷ CCZ023 ∷ []) (wp0820 c4) ▸
       at 46 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 47 2 (CS12 ∷ CCZ023 ∷ []) (wl0621 (lit c4)) ▸
       at 43 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 40 3 (Toff324 ∷ []) (wp0821 c4) ▸
       at 42 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 42 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 42 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b41 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b41 = at 46 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 45 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 46 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 47 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 48 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 49 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 45 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 44 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸ done

  b42 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b42 = at 44 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 43 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 44 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 45 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 46 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 47 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 43 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 42 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸ done

  b43 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff013 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b43 = at 43 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 43 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 46 2 (CCZ134 ∷ Toff013 ∷ []) (sym (wp0293 c4)) ▸
       at 46 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 45 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 46 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 47 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 48 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b44 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff013 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b44 = at 49 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 45 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 44 2 (CCZ134 ∷ Toff013 ∷ []) (sym (wp0293 c4)) ▸
       at 44 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 43 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 44 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 45 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 46 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b45 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ K2 ∷ CS34 ∷ CX24 ∷ Toff013 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b45 = at 47 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 43 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 44 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 44 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 48 1 (K2 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl1376 (lit c4))) ▸
       at 47 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸
       at 48 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 49 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸ done

  b46 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ K2 ∷ CS34 ∷ CX24 ∷ Toff013 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ024 ∷ K2 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ CCZ034 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b46 = at 50 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 51 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 52 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 53 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl1375 (lit c4))) ▸
       at 47 7 (Toff234 ∷ []) (wl1376 (lit c4)) ▸
       at 46 2 (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0790 c4) ▸
       at 46 1 (K2 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl1376 (lit c4))) ▸
       at 45 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸ done

  b47 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ024 ∷ K2 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ CCZ034 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ024 ∷ Toff234 ∷ CCZ034 ∷ CCZ134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b47 = at 46 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 47 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 48 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 49 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 50 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 51 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl1375 (lit c4))) ▸
       at 45 7 (Toff234 ∷ []) (wl1376 (lit c4)) ▸
       at 46 2 (CCZ034 ∷ CCZ134 ∷ Toff013 ∷ []) (sym (wp1214 c4)) ▸ done

  b48 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ024 ∷ Toff234 ∷ CCZ034 ∷ CCZ134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ034 ∷ CCZ034 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b48 = at 44 2 (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0790 c4) ▸
       at 46 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 48 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 47 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 48 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 49 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 50 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 51 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b49 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ034 ∷ CCZ034 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b49 = at 47 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 44 3 (Toff234 ∷ []) (wp1215 c4) ▸
       at 46 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 46 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 49 2 (CCZ134 ∷ Toff013 ∷ []) (sym (wp0293 c4)) ▸
       at 49 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 48 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 49 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b50 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  b50 = at 50 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 51 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 52 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 48 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 47 2 (CCZ134 ∷ Toff013 ∷ []) (sym (wp0293 c4)) ▸
       at 47 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 46 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 47 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b51 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ Toff013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff324 ∷ CCZ124 ∷ [])
  b51 = at 48 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 49 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 50 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 46 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 47 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 47 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 51 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 50 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸ done

  b52 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ Toff013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ024 ∷ CS24 ∷ Toff013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ [])
  b52 = at 51 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 52 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 53 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 54 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 50 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 49 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 49 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 48 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸ done

  b53 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ024 ∷ CS24 ∷ Toff013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Bx0-2341 ∷ Toff324 ∷ CCZ124 ∷ [])
  b53 = at 49 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 50 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 51 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 52 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 48 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 47 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 48 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 48 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸ done

  b54 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Bx0-2341 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ124 ∷ [])
  b54 = at 48 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 52 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 51 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 52 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 53 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 54 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 55 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 56 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸ done

  b55 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ Toff014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ [])
  b55 = at 57 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 51 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 50 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 50 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 49 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 50 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 51 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 52 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸ done

  b56 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ Toff014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CCZ023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ [])
  b56 = at 53 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 54 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸
       at 55 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 49 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 50 2 (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (sym (wp0839 c4)) ▸
       at 48 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 50 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 52 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸ done

  b57 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CCZ023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ Bx0-2341 ∷ CCZ124 ∷ [])
  b57 = at 51 2 (CS24 ∷ CCZ023 ∷ []) (wp0513 c4) ▸
       at 52 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 53 2 (CS24⁻ ∷ CCZ023 ∷ []) (wp0820 c4) ▸
       at 54 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 55 2 (CS12 ∷ CCZ023 ∷ []) (wl0621 (lit c4)) ▸
       at 51 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 48 3 (Toff324 ∷ []) (wp0821 c4) ▸
       at 50 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸ done

  b58 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ Bx0-2341 ∷ CCZ124 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ [])
  b58 = at 50 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 50 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 54 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 53 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 54 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 55 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 56 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 57 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸ done

  b59 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b59 = at 53 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 52 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 52 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 51 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 52 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 53 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 54 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 55 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸ done

  b60 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ [])
  b60 = at 51 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 50 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 51 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 0 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 2 2 [] (wl0305 (lit c4)) ▸
       at 5 11 (CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ []) (wl1377 (lit c4)) ▸
       at 15 2 [] (wl0321 (lit c4)) ▸
       at 5 2 [] (wl0305 (lit c4)) ▸ done

  b61 : Chain (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ [])
  b61 = at 5 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 7 2 [] (wl0305 (lit c4)) ▸
       at 13 2 [] (wl0263 (lit c4)) ▸
       at 14 2 [] (wl0321 (lit c4)) ▸
       at 15 2 [] (wl0263 (lit c4)) ▸
       at 15 2 (Toff324 ∷ CCZ124 ∷ []) (wl0450 (lit c4)) ▸
       at 16 2 [] (wl0263 (lit c4)) ▸
       at 16 2 (CS13 ∷ CCZ124 ∷ []) (wl1152 (lit c4)) ▸ done

  b62 : Chain (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ [])
  b62 = at 17 2 [] (wl0263 (lit c4)) ▸
       at 18 2 [] (wl0263 (lit c4)) ▸
       at 19 2 (Toff324 ∷ CCZ124 ∷ []) (wl0450 (lit c4)) ▸
       at 20 2 [] (wl0263 (lit c4)) ▸ done


-- L-CCZ-1 part3: 6 steps
lem-L-CCZ-1-part3 : Ws → ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-L-CCZ-1-part3 c4 = run b0
  where
  b0 : Chain (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 21 2 (Toff234 ∷ CCZ134 ∷ []) (wl0431 (lit c4)) ▸
       at 22 2 [] (wl0321 (lit c4)) ▸
       at 23 2 (Toff324 ∷ CCZ124 ∷ []) (wl0450 (lit c4)) ▸
       at 24 2 [] (wl0263 (lit c4)) ▸
       at 0 25 [] (wl1378 (lit c4)) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-box-perm-4132-at122441 c4) ▸ done


-- L-CCZ-1: 4 steps
lem-L-CCZ-1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-L-CCZ-1 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 45 (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ134 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ Bx0-1423 ∷ []) (lem-L-CCZ-1-part0 c4) ▸
       at 0 46 (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (lem-L-CCZ-1-part1 c4) ▸
       at 0 50 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ []) (lem-L-CCZ-1-part2 c4) ▸
       at 0 30 (Bx0-1234 ∷ []) (lem-L-CCZ-1-part3 c4) ▸ done


-- box-perm-2134 @1221: 1 steps
lem-box-perm-2134-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-2134-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-sym-ab-at1221 c4) ▸ done

