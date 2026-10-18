{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D030 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0006 ; wl0181 ; wl0234 ; wl0241 ; wl0242 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0305 ; wl0458 ; wl0679 ; wl0774 ; wl0787 ; wl0790 ; wl0835 ; wl0838 ; wl0840 ; wl0876 ; wl0877 ; wl0960 ; wl1037 ; wl1100 ; wl1220 ; wl1221 ; wl1233 ; wl1235 ; wl1236 ; wl1237 ; wl1238 ; wl1239 ; wl1270 ; wl1297 ; wl1299 ; wl1300 ; wl1301 ; wl1302 ; wl1303 ; wl1304 ; wl1305 ; wl1306 ; wl1307 ; wl1308 ; wp0034 ; wp0035 ; wp0036 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0091 ; wp0092 ; wp0094 ; wp0095 ; wp0097 ; wp0135 ; wp0262 ; wp0272 ; wp0296 ; wp0301 ; wp0653 ; wp0655 ; wp0704 ; wp0706 ; wp0749 ; wp0842 ; wp0843 ; wp0845 ; wp0898 ; wp0899 ; wp0991 ; wp1003 ; wp1041 ; wp1126 ; wp1127 ; wp1128 ; wp1129)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at122441 ; lem-box-tQ ; lem-box2-at122441)
open import Examples.Groups.Clifford+CS.FiveV.D.D007 using (lem-box-perm-1423-at122441)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-S2-SBOX⟨0·1·42·3⟩ ; lem-S2-SBOX⟨2·0·41·3⟩)
open import Examples.Groups.Clifford+CS.FiveV.D.D019 using (lem-CKc-box-at12213443 ; lem-box-perm-1342-at12213443 ; lem-box-tQ-at03243240)
open import Examples.Groups.Clifford+CS.FiveV.D.D020 using (lem-box-cP-at03243240 ; lem-tP-at03243240)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CX02-CCZ134)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-CSd14-TOFF302 ; lem-comm-CZ02-TOFF314)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CS14-TOFF302 ; lem-comm-CX20-CCZ134 ; lem-comm-CZ02-CCZ134 ; lem-comm-SWAP12-BOX⟨3·04⟩ ; lem-comm-TOFF013-CX24)
-- nf-CS-K1@2: 284 steps
lem-nf-CS-K1at2 : Ws → ⟪ (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-nf-CS-K1at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸
       at 6 1 (CS12⁻ ∷ []) (refl) ▸
       at 8 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 10 1 (CS12 ∷ []) (refl) ▸
       at 12 1 (CS12⁻ ∷ []) (refl) ▸
       at 8 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 11 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b1 : Chain (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 10 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 13 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 12 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 13 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 14 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 15 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 16 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 17 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b2 : Chain (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ Toff013 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 18 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 12 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 9 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 11 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 10 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 11 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 13 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸ done

  b3 : Chain (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ Toff013 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 14 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 10 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 11 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 9 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 8 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 10 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 9 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 10 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b4 : Chain (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 15 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 9 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 10 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 10 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b5 : Chain (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b5 = at 13 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 12 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 11 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 10 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 11 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 14 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 13 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸ done

  b6 : Chain (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b6 = at 16 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 15 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 16 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 17 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 18 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 19 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 20 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 21 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸ done

  b7 : Chain (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b7 = at 15 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 12 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 14 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 13 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 14 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 15 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 16 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 17 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸ done

  b8 : Chain (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b8 = at 13 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 14 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 12 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 11 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 13 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 12 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 13 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 14 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b9 : Chain (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ [])
  b9 = at 15 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 16 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 17 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 18 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 12 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 13 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 13 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 16 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b10 : Chain (CS34 ∷ CK43 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ []) (CS34 ∷ CK43 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b10 = at 15 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 14 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 13 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 14 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 4 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b11 : Chain (CS34 ∷ CK43 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b11 = at 6 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 7 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 12 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 6 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b12 : Chain (CS34 ∷ CK43 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b12 = at 3 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 5 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 4 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 5 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 6 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 8 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 4 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done

  b13 : Chain (CS34 ∷ CK43 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b13 = at 5 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 2 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 3 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 4 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b14 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b14 = at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 9 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 3 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 6 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸ done

  b15 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b15 = at 5 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 4 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 7 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 10 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 9 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b16 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b16 = at 10 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 15 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 9 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b17 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b17 = at 8 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 7 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 8 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 10 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 11 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 7 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 8 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b18 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b18 = at 6 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 5 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 6 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 7 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b19 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b19 = at 11 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 12 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 6 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 7 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 10 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 9 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b20 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS34 ∷ Toff013 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b20 = at 7 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 8 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 8 1 (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4) ▸
       at 8 2 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ []) (lem-CKc-box-at12213443 c4) ▸
       at 11 1 (Bx0-2431 ∷ []) (lem-box-perm-1342-at12213443 c4) ▸
       at 11 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 15 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 14 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸ done

  b21 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS34 ∷ Toff013 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ CS34 ∷ Toff013 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b21 = at 15 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 16 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 17 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 18 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 14 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 13 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 13 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 12 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸ done

  b22 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ CS34 ∷ Toff013 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b22 = at 13 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 15 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 16 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 12 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 11 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 12 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 12 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b23 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b23 = at 15 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 14 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 17 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 16 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 17 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 18 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 19 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 20 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b24 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ Toff013 ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b24 = at 21 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 22 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 16 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 13 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 15 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 14 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 15 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 16 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸ done

  b25 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ Toff013 ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b25 = at 17 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 18 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 14 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 15 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 13 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 12 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 14 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 13 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b26 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ Bx0-2431 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b26 = at 14 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 17 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 18 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 19 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 13 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 14 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b27 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ Bx0-2431 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b27 = at 14 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 17 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 16 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 15 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 14 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 15 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 15 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 19 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸ done

  b28 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b28 = at 18 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 19 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 20 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 21 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 22 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 18 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 17 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 17 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸ done

  b29 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b29 = at 16 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 17 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 18 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 19 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 20 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 16 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 15 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 16 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b30 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b30 = at 16 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 19 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 18 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 21 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 20 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 21 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 22 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 23 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b31 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ Toff013 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b31 = at 24 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 25 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 26 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 20 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 17 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 19 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 18 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 19 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸ done

  b32 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ Toff013 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b32 = at 20 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 21 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 22 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 18 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 19 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 17 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 16 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 18 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b33 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b33 = at 17 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 18 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 19 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 20 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 21 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 22 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 23 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 17 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b34 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b34 = at 18 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 18 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 21 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 20 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 19 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 18 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 19 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 19 2 [] (lem-box2-at122441 c4) ▸ done

  b35 : Chain (CS34 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b35 = at 2 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸
       at 9 2 [] (wl0305 (lit c4)) ▸
       at 11 2 [] (wl0305 (lit c4)) ▸ done


-- F1-CS-K1@2: 343 steps
lem-F1-CS-K1at2 : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-CS-K1at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (run b42))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ [])
  b0 = at 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (CS12 ∷ []) (refl) ▸
       at 10 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 9 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ [])
  b1 = at 8 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 11 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 10 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 11 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 14 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 15 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ Toff013 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ [])
  b2 = at 16 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 10 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 7 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 9 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 8 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 11 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸ done

  b3 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ Toff013 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ [])
  b3 = at 12 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 8 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 9 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 7 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 6 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 8 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 7 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 8 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b4 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ [])
  b4 = at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 13 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 7 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 8 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 8 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b5 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ [])
  b5 = at 11 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 10 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 9 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 8 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 9 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 9 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 12 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 11 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸ done

  b6 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ [])
  b6 = at 14 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 13 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 14 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 17 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 18 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 19 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸ done

  b7 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ [])
  b7 = at 13 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 10 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 12 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 11 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 12 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 14 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 15 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸ done

  b8 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ [])
  b8 = at 11 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 12 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 10 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 9 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 11 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 10 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 11 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b9 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CK43 ∷ CS34 ∷ [])
  b9 = at 13 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 14 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 15 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 16 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 10 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 11 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 14 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b10 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CK43 ∷ CS34 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ [])
  b10 = at 13 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 12 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 11 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 12 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 12 1 (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4) ▸
       at 12 2 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ []) (lem-CKc-box-at12213443 c4) ▸
       at 15 1 (Bx0-2431 ∷ []) (lem-box-perm-1342-at12213443 c4) ▸
       at 15 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b11 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ []) (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b11 = at 18 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 17 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 16 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 15 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 16 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 0 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 3 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 2 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸ done

  b12 : Chain (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b12 = at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 4 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 10 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸ done

  b13 : Chain (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b13 = at 4 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 1 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 3 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 2 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 3 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 5 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 6 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸ done

  b14 : Chain (CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b14 = at 2 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 1 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 0 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 2 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 1 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 2 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 3 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b15 : Chain (CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b15 = at 4 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 7 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 1 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸ done

  b16 : Chain (CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b16 = at 4 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 3 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 2 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 5 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 8 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b17 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b17 = at 7 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 8 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 13 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 7 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b18 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b18 = at 4 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 6 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 5 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 8 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 9 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done

  b19 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b19 = at 6 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 4 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 3 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 4 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b20 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b20 = at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 10 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 4 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸ done

  b21 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CK43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b21 = at 6 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4) ▸
       at 6 2 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ []) (lem-CKc-box-at12213443 c4) ▸
       at 9 1 (Bx0-2431 ∷ []) (lem-box-perm-1342-at12213443 c4) ▸
       at 9 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 13 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸ done

  b22 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b22 = at 12 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 13 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 15 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 16 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 12 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 11 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 11 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸ done

  b23 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b23 = at 10 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 11 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 13 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 14 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 10 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 9 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 10 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b24 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b24 = at 10 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 13 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 12 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 15 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 14 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 15 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 16 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 17 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b25 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ Toff013 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b25 = at 18 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 19 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 20 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 14 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 11 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 13 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 12 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 13 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸ done

  b26 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ Toff013 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b26 = at 14 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 15 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 16 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 12 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 13 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 11 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 10 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 12 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b27 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b27 = at 11 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 12 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 17 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 11 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b28 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b28 = at 12 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 12 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 15 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 14 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 13 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 12 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 13 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 13 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b29 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b29 = at 17 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 16 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 17 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 18 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 19 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 20 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 16 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 15 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸ done

  b30 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b30 = at 15 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 14 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 15 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 16 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 17 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 18 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 14 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 13 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸ done

  b31 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b31 = at 14 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 14 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 17 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 16 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 19 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 18 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 19 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 20 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b32 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ Toff013 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b32 = at 21 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 22 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 23 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 24 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 18 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 15 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 17 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 16 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸ done

  b33 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ Toff013 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b33 = at 17 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 18 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 19 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 20 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 16 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 17 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 15 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 14 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸ done

  b34 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b34 = at 16 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 15 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 16 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 17 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 18 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 19 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 20 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 21 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸ done

  b35 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b35 = at 15 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 16 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 16 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 19 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 18 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 17 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 16 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 17 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b36 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b36 = at 17 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 20 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 20 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 19 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 20 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 21 2 (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4) ▸
       at 22 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 23 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸ done

  b37 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b37 = at 19 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 18 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 18 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 17 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 18 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 19 2 (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4) ▸
       at 20 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 21 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸ done

  b38 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff013 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b38 = at 17 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 18 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 18 1 (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4) ▸
       at 18 2 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ []) (lem-CKc-box-at12213443 c4) ▸
       at 21 1 (Bx0-2431 ∷ []) (lem-box-perm-1342-at12213443 c4) ▸
       at 21 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 24 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 24 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b39 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff013 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b39 = at 23 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 24 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 25 2 (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4) ▸
       at 26 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 27 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 23 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 22 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 22 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b40 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ Bx0-2431 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b40 = at 21 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 22 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 23 2 (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4) ▸
       at 24 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 25 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 21 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 22 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 22 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b41 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ Bx0-2431 ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ123 ∷ CS34 ∷ [])
  b41 = at 25 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 24 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 23 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 22 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 23 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 23 2 [] (lem-box2-at122441 c4) ▸
       at 0 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 2 2 [] (wl0305 (lit c4)) ▸ done

  b42 : Chain (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ123 ∷ CS34 ∷ []) (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ [])
  b42 = at 6 9 (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ []) (wl1297 (lit c4)) ▸
       at 14 2 [] (wl0181 (lit c4)) ▸
       at 6 2 [] (wl0305 (lit c4)) ▸
       at 8 2 [] (wl0305 (lit c4)) ▸
       at 12 2 [] (wl0181 (lit c4)) ▸
       at 0 13 (CS34 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1299 (lit c4))) ▸
       at 0 13 (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (sym (lem-nf-CS-K1at2 c4)) ▸ done


-- CK-box: 6 steps
lem-CK-box : Ws → ⟪ (CK34 ∷ Bx0-1234 ∷ CK34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff403 ∷ Toff012 ∷ Toff403 ∷ []) ⟫ʷ
lem-CK-box c4 = run b0
  where
  b0 : Chain (CK34 ∷ Bx0-1234 ∷ CK34⁻ ∷ []) (Toff012 ∷ Toff403 ∷ Toff012 ∷ Toff403 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CK34 ∷ []) (sym (c₃ (Toff) (CK₀₁))) ▸
       at 1 2 (Toff403 ∷ CK34 ∷ []) (wp1126 c4) ▸
       at 2 2 (Toff012 ∷ CK34 ∷ []) (sym (c₃ (Toff) (CK₀₁))) ▸
       at 3 2 (Toff403 ∷ CK34 ∷ []) (wp1126 c4) ▸
       at 4 2 [] (wl1300 (lit c4)) ▸ done


-- L-CX01-0: 2 steps
lem-L-CX01-0 : Ws → ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ []) ⟫ʷ
lem-L-CX01-0 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ [])
  b0 = at 1 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 0 4 (Toff104 ∷ []) (wp1127 c4) ▸ done


-- L-CX01-1: 2 steps
lem-L-CX01-1 : Ws → ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ []) ⟫ʷ
lem-L-CX01-1 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ [])
  b0 = at 1 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 0 4 (Toff214 ∷ []) (wl1301 (lit c4)) ▸ done


-- L-CX10-1: 2 steps
lem-L-CX10-1 : Ws → ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ []) ⟫ʷ
lem-L-CX10-1 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ [])
  b0 = at 1 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 0 4 (Toff124 ∷ []) (wl1302 (lit c4)) ▸ done


-- P-box @03243240: 8 steps
lem-P-box-at03243240 : Ws → ⟪ (Toff302 ∷ Bx3-1420 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-P-box-at03243240 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Bx3-1420 ∷ Toff302 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243240 c4) ▸
       at 0 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at03243240 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ02 ∷ Toff302 ∷ []) (sym (wl1235 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at03243240 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ02 ∷ []) (sym (wl1236 (lit c4))) ▸
       at 2 2 (Toff314 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF314 (lit c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wl0774 (lit c4))) ▸
       at 0 4 (Bx3-1420 ∷ []) (sym (lem-box-tQ-at03243240 c4)) ▸ done


-- cQ @03122031: 7 steps
lem-cQ-at03122031 : Ws → ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at03122031 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS23 ∷ []) (sym (wl0790 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS03⁻ ∷ []) (sym (wp0704 c4)) ▸
       at 1 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS03 ∷ []) (sym (wp0706 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸ done


-- box-tQ @03122031: 13 steps
lem-box-tQ-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at03122031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2014 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wl1303 (lit c4)) ▸
       at 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wl1303 (lit c4)) ▸
       at 0 2 (Toff302 ∷ CCZ023 ∷ CZ02 ∷ []) (wl1238 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ023 ∷ []) (lem-cQ-at03122031 c4) ▸
       at 2 4 (Toff302 ∷ []) (wl1239 (lit c4)) ▸ done


-- pairs @03243240: 4 steps
lem-pairs-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-pairs-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-2014 ∷ [])
  b0 = at 0 1 (Toff302 ∷ Bx3-1420 ∷ Toff302 ∷ []) (sym (lem-P-box-at03243240 c4)) ▸
       at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 4 2 [] (wl0787 (lit c4)) ▸
       at 0 4 (Bx3-2014 ∷ []) (sym (lem-box-tQ-at03122031 c4)) ▸ done


-- sym-ab @03122031: 18 steps
lem-sym-ab-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym-ab-at03122031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-2014 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wl1303 (lit c4)) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (sym (wp0262 c4)) ▸
       at 4 1 (Bx3-04 ∷ []) (refl) ▸
       at 7 1 (Bx3-04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ [])
  b1 = at 2 6 (Bx0-314 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ134 ∷ []) (wl1303 (lit c4)) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (sym (wp0262 c4)) ▸
       at 7 1 (Bx3-04 ∷ []) (refl) ▸
       at 10 1 (Bx3-04 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (Bx3-0214 ∷ [])
  b2 = at 5 6 (Bx0-314 ∷ []) (refl) ▸
       at 0 6 (Bx3-0214 ∷ []) (refl) ▸ done


-- cQ @031031: 7 steps
lem-cQ-at031031 : Ws → ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at031031 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl0458 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS03 ∷ []) (sym (wp0706 c4)) ▸
       at 3 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS23⁻ ∷ []) (sym (wl1237 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS23 ∷ []) (sym (wl0790 (lit c4))) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0458 (lit c4))) ▸ done


-- box-tQ @031031: 13 steps
lem-box-tQ-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at031031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0214 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 0 2 (Toff302 ∷ CCZ023 ∷ CZ02 ∷ []) (wl1238 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ023 ∷ []) (lem-cQ-at031031 c4) ▸
       at 2 4 (Toff302 ∷ []) (wl1239 (lit c4)) ▸ done


-- CXbc-box @031031: 17 steps
lem-CXbc-box-at031031 : Ws → ⟪ (CX21 ∷ Bx3-0214 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at031031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx3-0214 ∷ CX21 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX21 ∷ CCZ234 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at031031 c4) ▸
       at 0 2 (Toff302 ∷ CX21 ∷ []) (wl1304 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CX21 ∷ CCZ234 ∷ []) (sym (wl1305 (lit c4))) ▸
       at 3 2 (Toff302 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp1128 c4) ▸
       at 2 2 (Toff302 ∷ CX21 ∷ []) (wl1304 (lit c4)) ▸
       at 5 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 9 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 8 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX21 ∷ CCZ234 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ CX21 ∷ []) (Bx3-0214 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ [])
  b1 = at 7 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 4 2 (CCZ134 ∷ CCZ234 ∷ []) (sym (wl0960 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CX21 ∷ CCZ234 ∷ []) (sym (wl1305 (lit c4))) ▸
       at 4 3 (CX21 ∷ []) (wl1306 (lit c4)) ▸
       at 0 4 (Bx3-0214 ∷ []) (sym (lem-box-tQ-at031031 c4)) ▸ done

  b2 : Chain (Bx3-0214 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ []) (Bx3-0214 ∷ CCZ024 ∷ [])
  b2 = at 1 3 (CCZ024 ∷ []) (sym (wp0898 c4)) ▸ done


-- CXcb-box @031031: 18 steps
lem-CXcb-box-at031031 : Ws → ⟪ (CX12 ∷ Bx3-0214 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at031031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx3-0214 ∷ CX12 ∷ []) (Toff302 ∷ CCZ134 ∷ CX12 ∷ Toff301 ∷ CS14 ∷ CX01 ∷ Toff302 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ134 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at031031 c4) ▸
       at 0 2 (Toff302 ∷ CX12 ∷ Toff301 ∷ []) (wl1307 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Toff301 ∷ CCZ014 ∷ []) (sym (wp1129 c4)) ▸
       at 1 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 4 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 8 2 (Toff302 ∷ CS04 ∷ []) (wp1041 c4) ▸
       at 7 2 (Toff302 ∷ CX01 ∷ []) (wl1233 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ CX12 ∷ Toff301 ∷ CS14 ∷ CX01 ∷ Toff302 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ134 ∷ CX12 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ [])
  b1 = at 5 2 (Toff302 ∷ CX01 ∷ []) (wl1233 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF302 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 3 2 (Toff302 ∷ Toff301 ∷ []) (wl1100 (lit c4)) ▸
       at 2 2 (Toff302 ∷ CX12 ∷ Toff301 ∷ []) (wl1307 (lit c4)) ▸
       at 3 3 (CX12 ∷ []) (wl1308 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 3 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸ done

  b2 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ []) (Bx3-0214 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx3-0214 ∷ []) (sym (lem-box-tQ-at031031 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸ done


-- SWbc-box @031031: 11 steps
lem-SWbc-box-at031031 : Ws → ⟪ (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-SWbc-box-at031031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) (CX21 ∷ Bx3-0214 ∷ CX21 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 4 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 2 3 (Bx3-0214 ∷ CCZ024 ∷ []) (lem-CXbc-box-at031031 c4) ▸
       at 3 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 1 3 (Bx3-0214 ∷ CCZ014 ∷ []) (lem-CXcb-box-at031031 c4) ▸
       at 4 2 (CX21 ∷ CCZ024 ∷ []) (wp0749 c4) ▸
       at 3 2 (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0899 c4) ▸
       at 2 2 (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0899 c4) ▸ done

  b1 : Chain (CX21 ∷ Bx3-0214 ∷ CX21 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) (Bx3-0214 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (wp0991 c4) ▸
       at 0 3 (Bx3-0214 ∷ CCZ024 ∷ []) (lem-CXbc-box-at031031 c4) ▸
       at 1 2 [] (wp0135 c4) ▸ done


-- nat-SWbc @031031: 23 steps
lem-nat-SWbc-at031031 : Ws → ⟪ (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-nat-SWbc-at031031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ Sw12 ∷ CCZ013 ∷ Bx3-04 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (wl0877 (lit c4)) ▸
       at 3 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (wl0876 (lit c4)) ▸
       at 4 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸
       at 5 2 (Toff023 ∷ Sw12 ∷ []) (wl0876 (lit c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ Sw12 ∷ CCZ013 ∷ Bx3-04 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ Sw12 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Sw12 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 7 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸
       at 8 2 (Toff301 ∷ Sw12 ∷ []) (wl0877 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 11 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 11 2 (Toff023 ∷ Sw12 ∷ []) (wl0876 (lit c4)) ▸
       at 12 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Sw12 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ Sw12 ∷ []) (Bx3-0124 ∷ [])
  b2 = at 13 2 (Toff023 ∷ Sw12 ∷ []) (wl0876 (lit c4)) ▸
       at 14 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 15 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx0-324 ∷ []) (refl) ▸
       at 5 6 (Bx0-324 ∷ []) (refl) ▸
       at 0 6 (Bx3-0124 ∷ []) (refl) ▸ done


-- sym-bc @031031: 2 steps
lem-sym-bc-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym-bc-at031031 c4 = run b0
  where
  b0 : Chain (Bx3-0214 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at031031 c4)) ▸
       at 0 3 (Bx3-0124 ∷ []) (lem-nat-SWbc-at031031 c4) ▸ done


-- box-perm-4132 @03243240: 3 steps
lem-box-perm-4132-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-4132-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-2014 ∷ []) (lem-pairs-at03243240 c4) ▸
       at 0 1 (Bx3-0214 ∷ []) (lem-sym-ab-at03122031 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-bc-at031031 c4) ▸ done

