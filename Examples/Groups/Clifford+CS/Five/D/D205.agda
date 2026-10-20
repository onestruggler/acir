{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D205 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0256 ; wl0341 ; wl0348 ; wl0499 ; wl0501 ; wl0503 ; wl0778 ; wl0779 ; wl0780 ; wl0861 ; wl0871 ; wl0888 ; wl1225 ; wl1226 ; wl1267 ; wl1268 ; wl1269 ; wp0002 ; wp0003 ; wp0041 ; wp0106 ; wp0107 ; wp0108 ; wp0124 ; wp0161 ; wp0205 ; wp0221 ; wp0700 ; wp0701 ; wp0716 ; wp0981 ; wp1030 ; wp1118 ; wp0686 ; wp1121 ; wp1122)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0310243142 ; lem-box-perm-1324-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-perm-1324-at0310243142 ; lem-box2-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-CKc-box-at0310213442 ; lem-CKc-box-at03103441 ; lem-S2-SBOX⟨3·0·41·2⟩ ; lem-S2-SBOX⟨3·1·42·0⟩ ; lem-box-perm-1342-at03103441 ; lem-box-perm-1423-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-F0-at01143043 ; lem-F0-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ034-CS12 ; lem-comm-CCZ034-CX12 ; lem-comm-TOFF312-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CCZ034-CSd12)

-- nf-rel-266@0: 163 steps
lem-nf-rel-266at0 : Ws → ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-nf-rel-266at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (run b20))))))))))))))))))))
  where
  b0 : Chain (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ [])
  b0 = at 1 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 2 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 6 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 7 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 10 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 12 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 13 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 17 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸ done

  b1 : Chain (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b1 = at 18 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 1 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 5 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 10 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 14 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 8 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 10 1 (CS02 ∷ []) (refl) ▸
       at 12 1 (CS02⁻ ∷ []) (refl) ▸ done

  b2 : Chain (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b2 = at 0 8 (Toff214 ∷ Toff124 ∷ []) (wl1267 (lit c4)) ▸
       at 2 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 5 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 5 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 4 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 5 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 6 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸ done

  b3 : Chain (Toff214 ∷ Toff124 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ Toff312 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b3 = at 8 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 10 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 4 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 5 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 3 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 5 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 7 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b4 : Chain (Toff214 ∷ Toff124 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ Toff312 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b4 = at 6 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 7 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 8 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 10 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 3 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 3 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸ done

  b5 : Chain (Toff214 ∷ Toff124 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ034 ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b5 = at 2 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 3 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 4 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 6 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 8 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 2 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸ done

  b6 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ034 ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Bx3-0412 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b6 = at 3 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 4 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 4 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 7 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 6 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 5 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 4 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 5 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done

  b7 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Bx3-0412 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b7 = at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 8 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 8 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 7 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 8 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 9 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b8 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b8 = at 12 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 13 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 7 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 8 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 6 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 8 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 10 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸ done

  b9 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CCZ034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b9 = at 10 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 11 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 12 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 13 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 9 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 6 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 6 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 5 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸ done

  b10 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CCZ034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b10 = at 6 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 9 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 11 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 5 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸ done

  b11 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0241 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b11 = at 7 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 7 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 10 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 9 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 8 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 7 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 8 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 8 1 (Bx3-0241 ∷ []) (lem-box-perm-1423-at0310243142 c4) ▸ done

  b12 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0241 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b12 = at 8 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) (lem-CKc-box-at03103441 c4) ▸
       at 11 1 (Bx3-0412 ∷ []) (lem-box-perm-1342-at03103441 c4) ▸
       at 11 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 14 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 14 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 14 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 15 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸ done

  b13 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b13 = at 16 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 17 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 13 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 12 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 12 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 11 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 12 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 13 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸ done

  b14 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b14 = at 14 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 15 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 11 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 12 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 12 1 (Bx3-0241 ∷ []) (lem-box-perm-1423-at0310243142 c4) ▸
       at 12 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) (lem-CKc-box-at03103441 c4) ▸
       at 15 1 (Bx3-0412 ∷ []) (lem-box-perm-1342-at03103441 c4) ▸
       at 15 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b15 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0412 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b15 = at 18 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 17 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 16 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 15 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 16 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 16 1 (Bx3-0142 ∷ []) (lem-box-perm-1324-at0310243142 c4) ▸
       at 16 2 (CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0142 ∷ []) (lem-CKc-box-at0310213442 c4) ▸
       at 19 1 (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4) ▸ done

  b16 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0412 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CK42 ∷ S4 ∷ [])
  b16 = at 19 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 22 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 22 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 21 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 22 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 23 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 24 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 25 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b17 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK42 ∷ S4 ∷ [])
  b17 = at 21 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 20 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 20 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 19 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 20 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 21 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 22 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 23 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b18 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ CCZ034 ∷ Toff312 ∷ [])
  b18 = at 19 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 20 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 20 1 (Bx3-0142 ∷ []) (lem-box-perm-1324-at0310243142 c4) ▸
       at 20 2 (CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0142 ∷ []) (lem-CKc-box-at0310213442 c4) ▸
       at 23 1 (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4) ▸
       at 23 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 26 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 25 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸ done

  b19 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ CCZ034 ∷ Toff312 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b19 = at 24 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 23 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 24 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 3 (CS02 ∷ Toff214 ∷ CCZ014 ∷ []) (wp1030 c4) ▸
       at 5 2 [] (wp0161 c4) ▸
       at 8 2 (CCZ124 ∷ CCZ012 ∷ []) (wp0205 c4) ▸
       at 9 2 [] (wl0341 (lit c4)) ▸
       at 10 2 (S4 ∷ CCZ012 ∷ []) (wl1269 (lit c4)) ▸ done

  b20 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b20 = at 11 2 [] (wl0341 (lit c4)) ▸
       at 12 2 (CCZ124 ∷ CCZ012 ∷ []) (wp0205 c4) ▸
       at 13 2 [] (wl0341 (lit c4)) ▸ done

-- nf-rel-267@0: 13 steps
lem-nf-rel-267at0 : Ws → ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
lem-nf-rel-267at0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ [])
  b0 = at 1 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 2 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 5 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 6 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 8 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 9 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 12 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 13 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸ done

  b1 : Chain (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ []) (CCZ024 ∷ [])
  b1 = at 1 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 4 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 6 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 9 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 0 10 (CCZ024 ∷ []) (sym (wp1118 c4)) ▸ done

-- nf-rel-268@0: 482 steps
lem-nf-rel-268at0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) ⟫ʷ
lem-nf-rel-268at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (run b60))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 0 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 2 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 3 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 6 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 7 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 8 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 10 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 11 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸ done

  b1 : Chain (Sb3-0-41-2 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b1 = at 2 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 5 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 8 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 0 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 2 1 (CS02 ∷ []) (refl) ▸
       at 4 1 (CS02⁻ ∷ []) (refl) ▸
       at 10 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 12 1 (CS02 ∷ []) (refl) ▸ done

  b2 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b2 = at 14 1 (CS02⁻ ∷ []) (refl) ▸
       at 10 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 13 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 13 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 12 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 13 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 14 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 15 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸ done

  b3 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ Toff312 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b3 = at 16 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 17 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 18 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 12 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 13 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 11 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 13 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 15 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b4 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ Toff312 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b4 = at 14 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 15 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 16 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 17 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 18 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 14 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 11 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 11 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸ done

  b5 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ034 ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b5 = at 10 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 11 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 12 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 13 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 14 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 15 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 16 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 10 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸ done

  b6 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ034 ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Bx3-0412 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b6 = at 11 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 12 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 12 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 15 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 14 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 13 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 12 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 13 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done

  b7 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Bx3-0412 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b7 = at 13 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 16 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 16 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 15 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 16 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 17 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 18 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 19 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b8 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b8 = at 20 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 21 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 15 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 16 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 14 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 16 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 18 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 17 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸ done

  b9 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CCZ034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b9 = at 18 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 19 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 20 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 21 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 17 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 14 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 14 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 13 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸ done

  b10 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CCZ034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b10 = at 14 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 15 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 16 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 17 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 18 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 19 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 13 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 14 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸ done

  b11 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0241 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b11 = at 15 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 15 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 18 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 17 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 16 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 15 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 16 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 16 1 (Bx3-0241 ∷ []) (lem-box-perm-1423-at0310243142 c4) ▸ done

  b12 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0241 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CK41 ∷ S4 ∷ [])
  b12 = at 16 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) (lem-CKc-box-at03103441 c4) ▸
       at 19 1 (Bx3-0412 ∷ []) (lem-box-perm-1342-at03103441 c4) ▸
       at 19 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 22 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 22 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 21 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 22 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 23 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸ done

  b13 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ S4 ∷ [])
  b13 = at 24 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 25 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 21 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 20 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 20 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 19 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 20 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 21 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸ done

  b14 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ [])
  b14 = at 22 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 23 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 19 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 20 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 20 1 (Bx3-0241 ∷ []) (lem-box-perm-1423-at0310243142 c4) ▸
       at 20 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) (lem-CKc-box-at03103441 c4) ▸
       at 23 1 (Bx3-0412 ∷ []) (lem-box-perm-1342-at03103441 c4) ▸
       at 23 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b15 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b15 = at 26 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 25 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 24 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 23 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 24 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 0 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 3 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 3 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸ done

  b16 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b16 = at 2 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 3 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 4 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 6 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 8 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 2 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸ done

  b17 : Chain (CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ Toff312 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b17 = at 3 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 1 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 4 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 5 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 6 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 7 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸ done

  b18 : Chain (CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ Toff312 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b18 = at 8 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 4 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 1 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 1 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 0 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 1 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 2 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 3 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸ done

  b19 : Chain (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS02 ∷ Toff312 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b19 = at 4 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 5 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 6 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 0 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 2 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 5 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸ done

  b20 : Chain (Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS02 ∷ Toff312 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CCZ034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b20 = at 4 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 3 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 2 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 3 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 6 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 6 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 5 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸ done

  b21 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CCZ034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ Toff314 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b21 = at 6 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 9 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 11 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 5 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 6 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸ done

  b22 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ Toff314 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b22 = at 4 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 6 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 8 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 7 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 8 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 9 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 10 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 11 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸ done

  b23 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b23 = at 7 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 4 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 3 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 4 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 5 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b24 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b24 = at 8 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 9 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 3 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 5 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 8 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 7 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸ done

  b25 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CCZ124 ∷ Toff312 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b25 = at 6 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 5 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 6 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 6 1 (Bx3-0241 ∷ []) (lem-box-perm-1423-at0310243142 c4) ▸
       at 6 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) (lem-CKc-box-at03103441 c4) ▸
       at 9 1 (Bx3-0412 ∷ []) (lem-box-perm-1342-at03103441 c4) ▸
       at 9 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 12 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸ done

  b26 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CCZ124 ∷ Toff312 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ CCZ124 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b26 = at 12 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 11 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 12 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 13 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 14 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 15 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 11 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 10 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸ done

  b27 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ CCZ124 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ Bx3-0412 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b27 = at 10 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 9 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 10 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 12 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 10 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done

  b28 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ Bx3-0412 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b28 = at 10 1 (Bx3-0241 ∷ []) (lem-box-perm-1423-at0310243142 c4) ▸
       at 10 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) (lem-CKc-box-at03103441 c4) ▸
       at 13 1 (Bx3-0412 ∷ []) (lem-box-perm-1342-at03103441 c4) ▸
       at 13 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 16 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 15 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 14 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 13 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸ done

  b29 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b29 = at 14 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 14 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 18 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 17 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 18 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 19 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 20 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 21 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸ done

  b30 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ034 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b30 = at 17 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 16 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 16 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 15 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 16 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 17 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 18 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 19 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸ done

  b31 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ034 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b31 = at 15 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 14 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 15 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 15 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 18 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 18 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 17 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 18 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b32 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff312 ∷ Toff314 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b32 = at 19 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 20 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 21 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 22 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 23 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 17 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 18 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 16 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸ done

  b33 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff312 ∷ Toff314 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b33 = at 18 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 20 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 19 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 20 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 21 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 22 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 23 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 19 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸ done

  b34 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b34 = at 16 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 16 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 15 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 16 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 17 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 18 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 19 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 20 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b35 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS14 ∷ CX04 ∷ Toff312 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b35 = at 21 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 15 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 16 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 17 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 17 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 21 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 20 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 21 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸ done

  b36 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS14 ∷ CX04 ∷ Toff312 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ CS14 ∷ CX04 ∷ Toff312 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b36 = at 22 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 23 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 24 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 20 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 19 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 19 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 18 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 19 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸ done

  b37 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ CS14 ∷ CX04 ∷ Toff312 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS02 ∷ Toff312 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b37 = at 20 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 21 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 22 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 18 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 17 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 18 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 18 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 21 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸ done

  b38 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS02 ∷ Toff312 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CCZ034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b38 = at 20 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 19 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 18 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 19 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 19 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 22 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 22 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 21 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸ done

  b39 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CCZ034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ Toff314 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b39 = at 22 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 23 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 24 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 25 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 26 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 27 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 21 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 22 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸ done

  b40 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ Toff314 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b40 = at 20 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 22 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 24 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 23 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 24 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 25 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 26 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 27 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸ done

  b41 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b41 = at 23 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 20 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 20 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 19 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 20 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 21 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 22 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 23 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b42 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b42 = at 24 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 25 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 19 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 20 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 21 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 21 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 25 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 24 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸ done

  b43 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b43 = at 25 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 26 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 27 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 28 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 24 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 23 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 23 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 22 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸ done

  b44 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b44 = at 23 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 24 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 25 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 26 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 22 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 21 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 22 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 22 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b45 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b45 = at 25 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 24 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 23 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 22 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 23 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 23 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 26 2 (CCZ012 ∷ Toff312 ∷ []) (sym (wl0503 (lit c4))) ▸
       at 26 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸ done

  b46 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b46 = at 25 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 26 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 27 2 (CS12⁻ ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CSd12 (lit c4)) ▸
       at 28 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 29 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 25 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 24 2 (CCZ012 ∷ Toff312 ∷ []) (sym (wl0503 (lit c4))) ▸
       at 24 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸ done

  b47 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ Bx3-0241 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b47 = at 23 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 24 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 25 2 (CS12⁻ ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CSd12 (lit c4)) ▸
       at 26 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 27 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 23 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 24 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 24 1 (Bx3-0241 ∷ []) (lem-box-perm-1423-at0310243142 c4) ▸ done

  b48 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ Bx3-0241 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ034 ∷ CX01 ∷ CS02 ∷ Toff312 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b48 = at 24 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) (lem-CKc-box-at03103441 c4) ▸
       at 27 1 (Bx3-0412 ∷ []) (lem-box-perm-1342-at03103441 c4) ▸
       at 27 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 30 2 (CCZ012 ∷ Toff312 ∷ []) (sym (wl0503 (lit c4))) ▸
       at 30 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 29 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 30 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 31 2 (CS12⁻ ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CSd12 (lit c4)) ▸ done

  b49 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ034 ∷ CX01 ∷ CS02 ∷ Toff312 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ034 ∷ CX01 ∷ CS02 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b49 = at 32 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 33 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 29 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 28 2 (CCZ012 ∷ Toff312 ∷ []) (sym (wl0503 (lit c4))) ▸
       at 28 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 27 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 28 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 29 2 (CS12⁻ ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CSd12 (lit c4)) ▸ done

  b50 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ034 ∷ CX01 ∷ CS02 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b50 = at 30 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 31 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 27 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 28 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 28 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 31 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 31 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 30 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b51 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b51 = at 31 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 32 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 33 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 34 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 30 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 29 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 29 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 28 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b52 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CCZ012 ∷ Toff312 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b52 = at 29 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 30 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 31 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 32 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 28 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 29 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 29 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 32 2 (CCZ012 ∷ Toff312 ∷ []) (sym (wl0503 (lit c4))) ▸ done

  b53 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CCZ012 ∷ Toff312 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ034 ∷ CCZ012 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b53 = at 32 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 31 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 32 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 33 2 (CS12⁻ ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CSd12 (lit c4)) ▸
       at 34 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 35 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 31 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 30 2 (CCZ012 ∷ Toff312 ∷ []) (sym (wl0503 (lit c4))) ▸ done

  b54 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ034 ∷ CCZ012 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ Bx3-0412 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b54 = at 30 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 29 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 30 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 31 2 (CS12⁻ ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CSd12 (lit c4)) ▸
       at 32 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 33 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 29 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 30 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done

  b55 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ Bx3-0412 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS12 ∷ CX01 ∷ CCZ034 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ S4 ∷ Bx3-0412 ∷ [])
  b55 = at 30 1 (Bx3-0241 ∷ []) (lem-box-perm-1423-at0310243142 c4) ▸
       at 30 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) (lem-CKc-box-at03103441 c4) ▸
       at 33 1 (Bx3-0412 ∷ []) (lem-box-perm-1342-at03103441 c4) ▸
       at 33 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 36 2 (CCZ012 ∷ Toff312 ∷ []) (sym (wl0503 (lit c4))) ▸
       at 36 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 35 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 36 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸ done

  b56 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS12 ∷ CX01 ∷ CCZ034 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS12 ∷ CX01 ∷ CCZ034 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ Bx3-0412 ∷ [])
  b56 = at 37 2 (CS12⁻ ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CSd12 (lit c4)) ▸
       at 38 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 39 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 35 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 34 2 (CCZ012 ∷ Toff312 ∷ []) (sym (wl0503 (lit c4))) ▸
       at 34 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 33 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 34 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸ done

  b57 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS12 ∷ CX01 ∷ CCZ034 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ CCZ034 ∷ Toff312 ∷ Bx3-0412 ∷ [])
  b57 = at 35 2 (CS12⁻ ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CSd12 (lit c4)) ▸
       at 36 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 37 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 33 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 34 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 34 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 37 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 36 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸ done

  b58 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ CCZ034 ∷ Toff312 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ [])
  b58 = at 35 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 34 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 35 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 35 2 [] (lem-box2-at0310243142 c4) ▸
       at 1 3 (CS02 ∷ Toff214 ∷ CCZ014 ∷ []) (wp1030 c4) ▸
       at 3 2 [] (wp0161 c4) ▸
       at 4 26 (CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ []) (wp1121 c4) ▸
       at 29 2 [] (wl0341 (lit c4)) ▸ done

  b59 : Chain (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ [])
  b59 = at 5 2 (CCZ124 ∷ CCZ012 ∷ []) (wp0205 c4) ▸
       at 6 2 [] (wl0341 (lit c4)) ▸
       at 7 11 (S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ []) (wp1122 c4) ▸
       at 17 2 [] (wl0341 (lit c4)) ▸
       at 8 2 (Toff214 ∷ CCZ014 ∷ []) (wp0686 c4) ▸
       at 9 2 [] (wp0161 c4) ▸
       at 9 3 (CS02 ∷ Toff214 ∷ CCZ014 ∷ []) (wp1030 c4) ▸
       at 11 2 [] (wp0161 c4) ▸ done

  b60 : Chain (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ [])
  b60 = at 15 2 [] (wl0341 (lit c4)) ▸
       at 16 2 [] (wl0341 (lit c4)) ▸ done
