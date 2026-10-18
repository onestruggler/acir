{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D069 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0003 ; wl0004 ; wl0006 ; wl0013 ; wl0017 ; wl0018 ; wl1455 ; wl1456 ; wl1457 ; wl1458 ; wl1459 ; wl1460 ; wl1461 ; wp1306)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-F5-23)
open import Examples.Groups.Clifford+CS.FiveV.D.D067 using (lem-F4-I-CS2-at0213243140 ; lem-F4-S2-CS2-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.D068 using (lem-F4-CS2-CS2-at0213243140 ; lem-F4-CS2-I-at0213243140 ; lem-F4-CS2-K3-at0213243140 ; lem-F4-CS2-S2-at0213243140 ; lem-F4-I-K3-at0213243140 ; lem-F4-I-S2-at0213243140 ; lem-F4-K3-CS2-at0213243140 ; lem-F4-K3-I-at0213243140 ; lem-F4-K3-K3-at0213243140 ; lem-F4-K3-S2-at0213243140 ; lem-F4-S2-I-at0213243140 ; lem-F4-S2-K3-at0213243140 ; lem-F4-S2-S2-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R006 using (lem-comm-push-CS14-sw0-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R007 using (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R ; lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R)
open import Examples.Groups.Clifford+CS.FiveV.D.R008 using (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R ; lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R ; lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R ; lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R)
-- deb-CKS-split-a @0213243140 part0: 500 steps
lem-deb-CKS-split-a-at0213243140-part0 : Ws → ⟪ (CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) ⟫ʷ
lem-deb-CKS-split-a-at0213243140-part0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 0 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L (lit c4)) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 2 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 3 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b1 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 4 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 (lit c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 6 2 (Sw23 ∷ CS23 ∷ []) (wl1455 (lit c4)) ▸
       at 7 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸ done

  b2 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ X3 ∷ Sb0-4-32-1 ∷ X3 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b2 = at 6 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 7 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 8 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 9 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 10 2 [] (wl0003 (lit c4)) ▸
       at 5 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸
       at 6 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 7 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸ done

  b3 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ X3 ∷ Sb0-4-32-1 ∷ X3 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ X2 ∷ Sw23 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b3 = at 8 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 9 2 [] (wl0004 (lit c4)) ▸
       at 4 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 5 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 6 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 7 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 8 2 [] (wl0006 (lit c4)) ▸
       at 3 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸ done

  b4 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ X2 ∷ Sw23 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (Sw01 ∷ Sw12 ∷ X2 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b4 = at 4 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 5 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸
       at 6 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 7 2 [] (wl0003 (lit c4)) ▸
       at 2 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 3 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 4 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 5 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸ done

  b5 : Chain (Sw01 ∷ Sw12 ∷ X2 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ Sw01 ∷ X1 ∷ Sb2-4-10-3 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b5 = at 6 2 [] (wl0018 (lit c4)) ▸
       at 1 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸
       at 2 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 3 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸
       at 4 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 5 2 [] (wl0006 (lit c4)) ▸
       at 0 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸
       at 1 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸ done

  b6 : Chain (X0 ∷ Sb2-4-01-3 ∷ Sw01 ∷ X1 ∷ Sb2-4-10-3 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ CS04 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b6 = at 2 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸
       at 3 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 4 2 [] (wl0018 (lit c4)) ▸
       at 4 1 (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (wl1460 (lit c4)) ▸
       at 3 4 (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-K3-CS2-at0213243140 c4)) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 8 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L (lit c4)) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸ done

  b7 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ CS04 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS24 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b7 = at 9 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 10 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 11 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 13 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 12 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 14 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸ done

  b8 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS24 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ X4 ∷ Sb0-3-42-1 ∷ X4 ∷ Sw23 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b8 = at 13 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (wl0004 (lit c4)) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 14 2 (Sw23 ∷ CS23 ∷ []) (wl1455 (lit c4)) ▸
       at 15 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 14 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 15 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 16 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸ done

  b9 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ X4 ∷ Sb0-3-42-1 ∷ X4 ∷ Sw23 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sw12 ∷ Sb0-4-32-1 ∷ X3 ∷ Sb0-4-32-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b9 = at 17 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 18 2 [] (wl0003 (lit c4)) ▸
       at 13 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸
       at 14 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 15 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸
       at 16 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 17 2 [] (wl0004 (lit c4)) ▸
       at 12 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸ done

  b10 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sw12 ∷ Sb0-4-32-1 ∷ X3 ∷ Sb0-4-32-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X2 ∷ Sb0-4-21-3 ∷ X2 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b10 = at 13 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 14 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 15 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 11 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸
       at 12 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 13 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸
       at 14 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸ done

  b11 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X2 ∷ Sb0-4-21-3 ∷ X2 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ X1 ∷ Sb2-4-10-3 ∷ Sw12 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b11 = at 15 2 [] (wl0003 (lit c4)) ▸
       at 10 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 11 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 12 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 13 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 14 2 [] (wl0018 (lit c4)) ▸
       at 9 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸
       at 10 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸ done

  b12 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ X1 ∷ Sb2-4-10-3 ∷ Sw12 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b12 = at 11 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸
       at 12 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 13 2 [] (wl0006 (lit c4)) ▸
       at 8 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸
       at 9 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 10 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸
       at 11 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 12 2 [] (wl0018 (lit c4)) ▸ done

  b13 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ CS04 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b13 = at 7 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-CS2-K3-at0213243140 c4)) ▸
       at 6 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 12 1 (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (wl1460 (lit c4)) ▸
       at 11 4 (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-K3-CS2-at0213243140 c4)) ▸
       at 10 4 (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-K3-K3-at0213243140 c4)) ▸
       at 9 4 (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-K3-CS2-at0213243140 c4)) ▸
       at 17 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 16 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L (lit c4)) ▸ done

  b14 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ CS04 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b14 = at 18 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 17 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 19 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 18 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 19 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 21 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 20 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸ done

  b15 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ X4 ∷ Sb0-3-42-1 ∷ Sw23 ∷ X4 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b15 = at 22 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 21 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] (wl0004 (lit c4)) ▸
       at 23 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 22 2 (Sw23 ∷ CS23 ∷ []) (wl1455 (lit c4)) ▸
       at 23 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 22 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 23 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸ done

  b16 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ X4 ∷ Sb0-3-42-1 ∷ Sw23 ∷ X4 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ X3 ∷ Sb0-4-32-1 ∷ X3 ∷ Sb0-4-32-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b16 = at 24 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 25 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 26 2 [] (wl0003 (lit c4)) ▸
       at 21 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸
       at 22 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 23 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸
       at 24 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 25 2 [] (wl0004 (lit c4)) ▸ done

  b17 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ X3 ∷ Sb0-4-32-1 ∷ X3 ∷ Sb0-4-32-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X2 ∷ Sb0-4-21-3 ∷ X2 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b17 = at 20 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 21 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 22 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 23 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 24 2 [] (wl0006 (lit c4)) ▸
       at 19 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸
       at 20 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 21 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸ done

  b18 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X2 ∷ Sb0-4-21-3 ∷ X2 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ X1 ∷ Sw12 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b18 = at 22 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 23 2 [] (wl0003 (lit c4)) ▸
       at 18 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 19 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 20 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 21 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 22 2 [] (wl0018 (lit c4)) ▸
       at 17 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸ done

  b19 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ X1 ∷ Sw12 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b19 = at 18 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 19 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸
       at 20 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 21 2 [] (wl0006 (lit c4)) ▸
       at 16 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸
       at 17 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 18 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸
       at 19 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸ done

  b20 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw01 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b20 = at 20 2 [] (wl0018 (lit c4)) ▸
       at 15 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-CS2-K3-at0213243140 c4)) ▸
       at 14 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 13 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-CS2-K3-at0213243140 c4)) ▸
       at 12 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 20 1 (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (wp1306 c4) ▸
       at 19 4 (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-S2-CS2-at0213243140 c4)) ▸
       at 18 4 (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-S2-K3-at0213243140 c4)) ▸ done

  b21 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b21 = at 17 4 (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-S2-CS2-at0213243140 c4)) ▸
       at 16 4 (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-S2-K3-at0213243140 c4)) ▸
       at 15 4 (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-S2-CS2-at0213243140 c4)) ▸
       at 24 1 (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (wp1306 c4) ▸
       at 23 4 (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at0213243140 c4)) ▸
       at 22 4 (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-S2-CS2-at0213243140 c4)) ▸
       at 21 4 (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-S2-K3-at0213243140 c4)) ▸
       at 20 4 (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-S2-CS2-at0213243140 c4)) ▸ done

  b22 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b22 = at 19 4 (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-S2-K3-at0213243140 c4)) ▸
       at 18 4 (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-S2-CS2-at0213243140 c4)) ▸
       at 28 1 (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (wp1306 c4) ▸
       at 27 4 (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at0213243140 c4)) ▸
       at 26 4 (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at0213243140 c4)) ▸
       at 25 4 (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-S2-CS2-at0213243140 c4)) ▸
       at 24 4 (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-S2-K3-at0213243140 c4)) ▸
       at 23 4 (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-S2-CS2-at0213243140 c4)) ▸ done

  b23 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b23 = at 22 4 (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-S2-K3-at0213243140 c4)) ▸
       at 21 4 (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-S2-CS2-at0213243140 c4)) ▸
       at 32 1 (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (sym (wl1461 (lit c4))) ▸
       at 31 4 (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at0213243140 c4)) ▸
       at 30 4 (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at0213243140 c4)) ▸
       at 29 4 (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at0213243140 c4)) ▸
       at 28 4 (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-I-CS2-at0213243140 c4)) ▸
       at 27 4 (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-I-K3-at0213243140 c4)) ▸ done

  b24 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b24 = at 26 4 (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-I-CS2-at0213243140 c4)) ▸
       at 25 4 (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-I-K3-at0213243140 c4)) ▸
       at 24 4 (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-I-CS2-at0213243140 c4)) ▸
       at 36 1 (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (wp1306 c4) ▸
       at 35 4 (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) (sym (lem-F4-S2-I-at0213243140 c4)) ▸
       at 34 4 (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at0213243140 c4)) ▸
       at 33 4 (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at0213243140 c4)) ▸
       at 32 4 (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at0213243140 c4)) ▸ done

  b25 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sw01 ∷ CS04 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b25 = at 31 4 (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-S2-CS2-at0213243140 c4)) ▸
       at 30 4 (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-S2-K3-at0213243140 c4)) ▸
       at 29 4 (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-S2-CS2-at0213243140 c4)) ▸
       at 28 4 (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-S2-K3-at0213243140 c4)) ▸
       at 27 4 (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-S2-CS2-at0213243140 c4)) ▸
       at 41 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 40 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L (lit c4)) ▸
       at 42 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸ done

  b26 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sw01 ∷ CS04 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS24 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b26 = at 41 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 43 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 42 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 44 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 43 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 45 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 44 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 46 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸ done

  b27 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS24 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ X4 ∷ Sb0-3-42-1 ∷ X4 ∷ Sw23 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b27 = at 45 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 47 2 [] (wl0004 (lit c4)) ▸
       at 47 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 46 2 (Sw23 ∷ CS23 ∷ []) (wl1455 (lit c4)) ▸
       at 47 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 46 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 47 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 48 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸ done

  b28 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ X4 ∷ Sb0-3-42-1 ∷ X4 ∷ Sw23 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sw12 ∷ Sb0-4-32-1 ∷ X3 ∷ Sb0-4-32-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b28 = at 49 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 50 2 [] (wl0003 (lit c4)) ▸
       at 45 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸
       at 46 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 47 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸
       at 48 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 49 2 [] (wl0004 (lit c4)) ▸
       at 44 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸ done

  b29 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sw12 ∷ Sb0-4-32-1 ∷ X3 ∷ Sb0-4-32-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X2 ∷ Sb0-4-21-3 ∷ X2 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b29 = at 45 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 46 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 47 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 48 2 [] (wl0006 (lit c4)) ▸
       at 43 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸
       at 44 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 45 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸
       at 46 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸ done

  b30 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X2 ∷ Sb0-4-21-3 ∷ X2 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sw01 ∷ X1 ∷ Sb2-4-10-3 ∷ Sw12 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b30 = at 47 2 [] (wl0003 (lit c4)) ▸
       at 42 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 43 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 44 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 45 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 46 2 [] (wl0018 (lit c4)) ▸
       at 41 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸
       at 42 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸ done

  b31 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sw01 ∷ X1 ∷ Sb2-4-10-3 ∷ Sw12 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b31 = at 43 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸
       at 44 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 45 2 [] (wl0006 (lit c4)) ▸
       at 40 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸
       at 41 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 42 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸
       at 43 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 44 2 [] (wl0018 (lit c4)) ▸ done

  b32 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b32 = at 39 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 38 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) (sym (lem-F4-CS2-I-at0213243140 c4)) ▸
       at 37 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 36 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 35 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 34 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 33 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-CS2-K3-at0213243140 c4)) ▸
       at 32 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸ done

  b33 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b33 = at 31 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-CS2-K3-at0213243140 c4)) ▸
       at 30 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 45 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 44 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L (lit c4)) ▸
       at 46 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 45 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 47 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 46 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸ done

  b34 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS23 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b34 = at 48 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 47 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 49 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 48 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 50 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 49 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 51 2 [] (wl0004 (lit c4)) ▸
       at 51 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸ done

  b35 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS23 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ X3 ∷ Sw34 ∷ Sb0-3-42-1 ∷ X4 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b35 = at 50 2 (Sw23 ∷ CS23 ∷ []) (wl1455 (lit c4)) ▸
       at 51 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 50 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 51 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 52 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 53 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 54 2 [] (wl0003 (lit c4)) ▸
       at 49 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸ done

  b36 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ X3 ∷ Sw34 ∷ Sb0-3-42-1 ∷ X4 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b36 = at 50 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 51 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸
       at 52 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 53 2 [] (wl0004 (lit c4)) ▸
       at 48 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 49 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 50 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 51 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸ done

  b37 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw01 ∷ X2 ∷ Sb0-4-21-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b37 = at 52 2 [] (wl0006 (lit c4)) ▸
       at 47 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸
       at 48 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 49 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸
       at 50 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 51 2 [] (wl0003 (lit c4)) ▸
       at 46 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 47 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸ done

  b38 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw01 ∷ X2 ∷ Sb0-4-21-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sw01 ∷ X1 ∷ Sb2-4-10-3 ∷ X1 ∷ Sb2-4-10-3 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b38 = at 48 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 49 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 50 2 [] (wl0018 (lit c4)) ▸
       at 45 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸
       at 46 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 47 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸
       at 48 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 49 2 [] (wl0006 (lit c4)) ▸ done

  b39 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sw01 ∷ X1 ∷ Sb2-4-10-3 ∷ X1 ∷ Sb2-4-10-3 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b39 = at 44 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸
       at 45 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 46 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸
       at 47 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 48 2 [] (wl0018 (lit c4)) ▸
       at 43 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 42 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 41 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) (sym (lem-F4-CS2-I-at0213243140 c4)) ▸ done

  b40 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b40 = at 40 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 39 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 38 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 37 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 36 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-CS2-K3-at0213243140 c4)) ▸
       at 35 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 34 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-CS2-K3-at0213243140 c4)) ▸
       at 33 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸ done

  b41 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b41 = at 49 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 48 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L (lit c4)) ▸
       at 50 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 49 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 51 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 50 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 52 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 51 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸ done

  b42 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b42 = at 53 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 52 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 54 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 53 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 55 2 [] (wl0004 (lit c4)) ▸
       at 55 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 54 2 (Sw23 ∷ CS23 ∷ []) (wl1455 (lit c4)) ▸
       at 55 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸ done

  b43 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ X3 ∷ Sb0-4-32-1 ∷ X3 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b43 = at 54 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 55 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 56 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 57 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 58 2 [] (wl0003 (lit c4)) ▸
       at 53 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸
       at 54 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 55 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸ done

  b44 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ X3 ∷ Sb0-4-32-1 ∷ X3 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X2 ∷ Sw23 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b44 = at 56 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 57 2 [] (wl0004 (lit c4)) ▸
       at 52 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 53 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 54 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 55 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 56 2 [] (wl0006 (lit c4)) ▸
       at 51 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸ done

  b45 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X2 ∷ Sw23 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ X2 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b45 = at 52 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 53 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸
       at 54 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 55 2 [] (wl0003 (lit c4)) ▸
       at 50 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 51 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 52 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 53 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸ done

  b46 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ X2 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ Sw01 ∷ X1 ∷ Sb2-4-10-3 ∷ Sw01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b46 = at 54 2 [] (wl0018 (lit c4)) ▸
       at 49 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸
       at 50 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 51 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸
       at 52 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 53 2 [] (wl0006 (lit c4)) ▸
       at 48 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸
       at 49 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸ done

  b47 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ Sw01 ∷ X1 ∷ Sb2-4-10-3 ∷ Sw01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b47 = at 50 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸
       at 51 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 52 2 [] (wl0018 (lit c4)) ▸
       at 47 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 46 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 45 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 44 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) (sym (lem-F4-CS2-I-at0213243140 c4)) ▸
       at 43 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸ done

  b48 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CS14 ∷ Sw01 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b48 = at 42 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 41 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 40 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 39 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-CS2-K3-at0213243140 c4)) ▸
       at 38 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 37 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-CS2-K3-at0213243140 c4)) ▸
       at 36 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 53 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸ done

  b49 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CS14 ∷ Sw01 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CS14 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b49 = at 52 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L (lit c4)) ▸
       at 54 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 53 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 55 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 54 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 56 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 55 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 57 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸ done

  b50 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CS14 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ X4 ∷ Sw23 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b50 = at 56 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 58 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 57 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 59 2 [] (wl0004 (lit c4)) ▸
       at 59 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 58 2 (Sw23 ∷ CS23 ∷ []) (wl1455 (lit c4)) ▸
       at 59 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 58 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸ done

  b51 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ X4 ∷ Sw23 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ X3 ∷ Sb0-4-32-1 ∷ X3 ∷ Sb0-4-32-1 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b51 = at 59 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 60 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 61 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 62 2 [] (wl0003 (lit c4)) ▸
       at 57 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸
       at 58 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 59 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸
       at 60 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸ done

  b52 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ X3 ∷ Sb0-4-32-1 ∷ X3 ∷ Sb0-4-32-1 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X2 ∷ Sb0-4-21-3 ∷ Sw23 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b52 = at 61 2 [] (wl0004 (lit c4)) ▸
       at 56 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 57 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 58 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 59 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 60 2 [] (wl0006 (lit c4)) ▸
       at 55 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸
       at 56 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸ done

  b53 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X2 ∷ Sb0-4-21-3 ∷ Sw23 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ X2 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b53 = at 57 2 (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4)) ▸
       at 58 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 59 2 [] (wl0003 (lit c4)) ▸
       at 54 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 55 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 56 2 (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X)) ▸
       at 57 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 58 2 [] (wl0018 (lit c4)) ▸ done

  b54 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sw12 ∷ X2 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b54 = at 53 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸
       at 54 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 55 2 (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4)) ▸
       at 56 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 57 2 [] (wl0006 (lit c4)) ▸
       at 52 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸
       at 53 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 54 2 (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4)) ▸ done

  b55 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ Sw01 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b55 = at 55 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 56 2 [] (wl0018 (lit c4)) ▸
       at 51 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 50 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 49 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 48 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 47 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) (sym (lem-F4-CS2-I-at0213243140 c4)) ▸
       at 46 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸ done

  b56 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b56 = at 45 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 44 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at0213243140 c4)) ▸
       at 43 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 42 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-CS2-K3-at0213243140 c4)) ▸
       at 41 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 40 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-CS2-K3-at0213243140 c4)) ▸
       at 39 4 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-CS2-CS2-at0213243140 c4)) ▸
       at 56 1 (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (wl1460 (lit c4)) ▸ done

  b57 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b57 = at 55 4 (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-K3-CS2-at0213243140 c4)) ▸
       at 54 4 (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-K3-CS2-at0213243140 c4)) ▸
       at 53 4 (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-K3-CS2-at0213243140 c4)) ▸
       at 52 4 (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-K3-CS2-at0213243140 c4)) ▸
       at 51 4 (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-K3-S2-at0213243140 c4)) ▸
       at 50 4 (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (sym (lem-F4-K3-I-at0213243140 c4)) ▸
       at 49 4 (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-K3-S2-at0213243140 c4)) ▸
       at 48 4 (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-K3-S2-at0213243140 c4)) ▸ done

  b58 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ CS04 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b58 = at 47 4 (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) (sym (lem-F4-K3-S2-at0213243140 c4)) ▸
       at 46 4 (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-K3-CS2-at0213243140 c4)) ▸
       at 45 4 (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-K3-K3-at0213243140 c4)) ▸
       at 44 4 (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-K3-CS2-at0213243140 c4)) ▸
       at 43 4 (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (sym (lem-F4-K3-K3-at0213243140 c4)) ▸
       at 42 4 (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F4-K3-CS2-at0213243140 c4)) ▸
       at 61 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 60 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L (lit c4)) ▸ done

  b59 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ CS04 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b59 = at 62 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 61 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 63 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 62 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 64 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 63 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 65 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 64 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸ done

  b60 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ X4 ∷ Sb0-3-42-1 ∷ Sw23 ∷ X4 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b60 = at 66 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 65 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 67 2 [] (wl0004 (lit c4)) ▸
       at 67 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 66 2 (Sw23 ∷ CS23 ∷ []) (wl1455 (lit c4)) ▸
       at 67 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 66 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 67 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸ done

  b61 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ X4 ∷ Sb0-3-42-1 ∷ Sw23 ∷ X4 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ X3 ∷ Sb0-4-32-1 ∷ X3 ∷ Sb0-4-32-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b61 = at 68 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 69 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 70 2 [] (wl0003 (lit c4)) ▸
       at 65 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸
       at 66 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 67 2 (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4)) ▸
       at 68 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 69 2 [] (wl0004 (lit c4)) ▸ done

  b62 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ X3 ∷ Sb0-4-32-1 ∷ X3 ∷ Sb0-4-32-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  b62 = at 64 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 65 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 66 2 (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X)) ▸
       at 67 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸ done

