{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D072 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0003 ; wl0004 ; wl0006 ; wl0008 ; wl0011 ; wl0013 ; wl0018 ; wl0024 ; wl0046 ; wl0090 ; wl0095 ; wl0129 ; wl1424 ; wl1425 ; wl1426 ; wl1427 ; wl1428 ; wl1429 ; wl1462)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D067 using (lem-F4-I-CS2-at0213243140 ; lem-F4-S2-CS2-at0213243140 ; lem-S2-SBOX⟨0·2·43·1⟩-at0213243140 ; lem-deb-CKS-eps-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.D068 using (lem-F4-CS2-CS2-at0213243140 ; lem-F4-CS2-K3-at0213243140 ; lem-F4-I-K3-at0213243140 ; lem-F4-K3-CS2-at0213243140 ; lem-F4-K3-K3-at0213243140 ; lem-F4-S2-K3-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-push-CS04-sw0-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R006 using (lem-comm-push-CS14-sw0-R ; lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L ; lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R007 using (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R ; lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L ; lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R ; lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L ; lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L ; lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R008 using (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R ; lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R ; lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R ; lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R)
open import Examples.Groups.Clifford+CS.FiveV.TR2 using (lem-TR2-e425e28a)
-- deb-CKS @0213243140 part0: 500 steps
lem-deb-CKS-at0213243140-part0 : Ws → ⟪ (Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) ⟫ʷ
lem-deb-CKS-at0213243140-part0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ Sw01 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sw01 ∷ [])
  b0 = at 10 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 9 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 8 2 (Sw01 ∷ S1 ∷ []) (wl1424 (lit c4)) ▸
       at 7 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 6 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 5 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 4 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 3 2 (Sw01 ∷ CK10 ∷ []) (wl1425 (lit c4)) ▸ done

  b1 : Chain (Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ Sw01 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ [])
  b1 = at 2 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 1 2 (Sw01 ∷ CK10 ∷ []) (wl1425 (lit c4)) ▸
       at 0 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 10 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 9 2 (Sw12 ∷ S2 ∷ []) (wl1426 (lit c4)) ▸
       at 8 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 7 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸ done

  b2 : Chain (Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ [])
  b2 = at 6 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 5 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 5 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 3 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸ done

  b3 : Chain (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ Sw01 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b3 = at 12 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 11 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 10 2 (Sw01 ∷ S2 ∷ []) (sym (c₂ (Swap) (S))) ▸
       at 9 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 8 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 7 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 6 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 5 2 (Sw01 ∷ CK21 ∷ []) (wl1427 (lit c4)) ▸ done

  b4 : Chain (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ Sw01 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ Sw23 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b4 = at 4 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 3 2 (Sw01 ∷ CK21 ∷ []) (wl1427 (lit c4)) ▸
       at 2 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 12 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 11 2 (Sw23 ∷ S3 ∷ []) (wl1428 (lit c4)) ▸
       at 10 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 9 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸ done

  b5 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ Sw23 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b5 = at 8 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 7 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 7 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 5 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸ done

  b6 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ Sw12 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b6 = at 14 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 13 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 12 2 (Sw12 ∷ S3 ∷ []) (sym (c₃ (Swap ↑) (S))) ▸
       at 11 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 10 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 9 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 8 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 7 2 (Sw12 ∷ CK32 ∷ []) (wl0095 (lit c4)) ▸ done

  b7 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ Sw12 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ Sw34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b7 = at 6 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 5 2 (Sw12 ∷ CK32 ∷ []) (wl0095 (lit c4)) ▸
       at 4 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 15 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 14 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 13 2 (Sw34 ∷ S4 ∷ []) (wl1429 (lit c4)) ▸
       at 12 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 11 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸ done

  b8 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ Sw34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b8 = at 10 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 9 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 9 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 7 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸ done

  b9 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ Sw23 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b9 = at 16 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 15 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 14 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸
       at 13 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 12 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 11 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 10 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 9 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸ done

  b10 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ Sw23 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sw23 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b10 = at 8 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 7 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 6 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 7 10 (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ []) (lem-TR2-e425e28a c4) ▸
       at 6 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 7 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 8 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 9 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 (lit c4))) ▸ done

  b11 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sw23 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b11 = at 10 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 11 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 (lit c4))) ▸
       at 12 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 13 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 14 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 15 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 16 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 17 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸ done

  b12 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ Sw23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b12 = at 18 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 19 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 20 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 21 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 22 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 (lit c4))) ▸
       at 23 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 24 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 (lit c4))) ▸
       at 25 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸ done

  b13 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ Sw23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw23 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b13 = at 26 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 27 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 28 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 29 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 30 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 31 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 32 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 33 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸ done

  b14 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw23 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sw23 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b14 = at 34 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 35 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 (lit c4))) ▸
       at 36 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 37 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 (lit c4))) ▸
       at 38 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 39 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 40 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 41 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸ done

  b15 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sw23 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ Sw23 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b15 = at 42 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 43 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 44 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 45 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 (lit c4))) ▸
       at 46 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 47 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 (lit c4))) ▸
       at 48 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 49 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸ done

  b16 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ Sw23 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sw34 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b16 = at 50 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 51 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 52 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 53 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 54 2 [] (wl0003 (lit c4)) ▸
       at 5 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 6 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 7 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸ done

  b17 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sw34 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ Sw34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b17 = at 9 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 (lit c4)) ▸
       at 9 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 11 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0004 (lit c4)) ▸
       at 11 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 12 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 13 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸ done

  b18 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ Sw34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sw34 ∷ Sw34 ∷ CK32 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b18 = at 14 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 15 2 (S3 ∷ Sw34 ∷ []) (sym (wl1429 (lit c4))) ▸
       at 16 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 17 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 18 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 19 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 20 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 22 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sw34 ∷ Sw34 ∷ CK32 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sw34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b19 = at 21 2 [] (wl0004 (lit c4)) ▸
       at 22 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 24 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] (wl0004 (lit c4)) ▸
       at 24 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 25 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 26 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 27 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸ done

  b20 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sw34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b20 = at 28 2 (S3 ∷ Sw34 ∷ []) (sym (wl1429 (lit c4))) ▸
       at 29 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 31 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 [] (wl0004 (lit c4)) ▸
       at 32 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 31 2 [] (wl0004 (lit c4)) ▸
       at 33 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 [] (wl0004 (lit c4)) ▸ done

  b21 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ Sw34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b21 = at 33 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 35 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 34 2 [] (wl0004 (lit c4)) ▸
       at 35 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 37 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 36 2 [] (wl0004 (lit c4)) ▸
       at 37 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 38 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸ done

  b22 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ Sw34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ Sw34 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b22 = at 39 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 40 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 41 2 (S3 ∷ Sw34 ∷ []) (sym (wl1429 (lit c4))) ▸
       at 42 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 43 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 45 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 44 2 [] (wl0004 (lit c4)) ▸
       at 45 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸ done

  b23 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ Sw34 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw34 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b23 = at 47 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 46 2 [] (wl0004 (lit c4)) ▸
       at 47 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 48 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 49 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 50 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 51 2 (S3 ∷ Sw34 ∷ []) (sym (wl1429 (lit c4))) ▸
       at 53 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b24 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw34 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b24 = at 52 2 [] (wl0004 (lit c4)) ▸
       at 53 2 [] (wl0004 (lit c4)) ▸
       at 4 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 5 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 6 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 7 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 (lit c4))) ▸
       at 8 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 9 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 (lit c4))) ▸ done

  b25 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b25 = at 10 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 11 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 12 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 13 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 14 2 (S3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S)) ▸
       at 15 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 16 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 17 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸ done

  b26 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ Sw12 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b26 = at 18 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 19 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 20 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 (lit c4))) ▸
       at 21 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 22 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 (lit c4))) ▸
       at 23 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 24 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 25 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸ done

  b27 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ Sw12 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b27 = at 26 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 27 2 (S3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S)) ▸
       at 28 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 29 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 (lit c4))) ▸
       at 30 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 (lit c4))) ▸
       at 31 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 (lit c4))) ▸
       at 32 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 33 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 (lit c4))) ▸ done

  b28 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b28 = at 34 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 35 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 (lit c4))) ▸
       at 36 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 37 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 38 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 39 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 40 2 (S3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S)) ▸
       at 41 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸ done

  b29 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sw12 ∷ S3 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b29 = at 42 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 43 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 (lit c4))) ▸
       at 44 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 45 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 (lit c4))) ▸
       at 46 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 47 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 48 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 49 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸ done

  b30 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sw12 ∷ S3 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b30 = at 50 2 (S3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S)) ▸
       at 51 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 (lit c4))) ▸
       at 52 2 [] (wl0006 (lit c4)) ▸
       at 3 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 4 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 5 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 (lit c4)) ▸ done

  b31 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw23 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b31 = at 7 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 (lit c4)) ▸
       at 9 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 10 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 11 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 12 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 13 2 (S2 ∷ Sw23 ∷ []) (sym (wl1428 (lit c4))) ▸ done

  b32 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw23 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ Sw23 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b32 = at 14 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 15 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 16 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 17 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 18 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 20 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] (wl0003 (lit c4)) ▸
       at 20 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸ done

  b33 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ Sw23 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b33 = at 22 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] (wl0003 (lit c4)) ▸
       at 22 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 23 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 24 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 25 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 26 2 (S2 ∷ Sw23 ∷ []) (sym (wl1428 (lit c4))) ▸
       at 27 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸ done

  b34 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b34 = at 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 [] (wl0003 (lit c4)) ▸
       at 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 [] (wl0003 (lit c4)) ▸
       at 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 [] (wl0003 (lit c4)) ▸
       at 31 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 33 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b35 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw23 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b35 = at 32 2 [] (wl0003 (lit c4)) ▸
       at 33 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 35 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 34 2 [] (wl0003 (lit c4)) ▸
       at 35 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 36 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 37 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 38 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸ done

  b36 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw23 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b36 = at 39 2 (S2 ∷ Sw23 ∷ []) (sym (wl1428 (lit c4))) ▸
       at 40 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 41 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 43 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 42 2 [] (wl0003 (lit c4)) ▸
       at 43 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 45 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 44 2 [] (wl0003 (lit c4)) ▸ done

  b37 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS13 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS12 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b37 = at 45 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 46 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 47 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 48 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 49 2 (S2 ∷ Sw23 ∷ []) (sym (wl1428 (lit c4))) ▸
       at 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 50 2 [] (wl0003 (lit c4)) ▸
       at 51 2 [] (wl0003 (lit c4)) ▸ done

  b38 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS12 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ Sw01 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS12 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b38 = at 2 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 3 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 4 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 5 2 (CK20 ∷ Sw01 ∷ []) (sym (wl1427 (lit c4))) ▸
       at 6 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 7 2 (CK20 ∷ Sw01 ∷ []) (sym (wl1427 (lit c4))) ▸
       at 8 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 9 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b39 : Chain (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ Sw01 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS12 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sw01 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS12 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b39 = at 10 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 11 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 12 2 (S2 ∷ Sw01 ∷ []) (c₂ (Swap) (S)) ▸
       at 13 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 14 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 15 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 16 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 17 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸ done

  b40 : Chain (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sw01 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS12 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS12 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b40 = at 18 2 (CK20 ∷ Sw01 ∷ []) (sym (wl1427 (lit c4))) ▸
       at 19 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 20 2 (CK20 ∷ Sw01 ∷ []) (sym (wl1427 (lit c4))) ▸
       at 21 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 22 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 23 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 24 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 25 2 (S2 ∷ Sw01 ∷ []) (c₂ (Swap) (S)) ▸ done

  b41 : Chain (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ CS24 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS12 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS12 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b41 = at 26 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 27 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0024 (lit c4))) ▸
       at 28 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0024 (lit c4))) ▸
       at 29 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0024 (lit c4))) ▸
       at 30 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 31 2 (CK20 ∷ Sw01 ∷ []) (sym (wl1427 (lit c4))) ▸
       at 32 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 33 2 (CK20 ∷ Sw01 ∷ []) (sym (wl1427 (lit c4))) ▸ done

  b42 : Chain (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS12 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS12 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b42 = at 34 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 35 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 36 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 37 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 38 2 (S2 ∷ Sw01 ∷ []) (c₂ (Swap) (S)) ▸
       at 39 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 40 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 41 2 (CK20 ∷ Sw01 ∷ []) (sym (wl1427 (lit c4))) ▸ done

  b43 : Chain (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS12 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b43 = at 42 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 43 2 (CK20 ∷ Sw01 ∷ []) (sym (wl1427 (lit c4))) ▸
       at 44 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 45 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 46 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 47 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 48 2 (S2 ∷ Sw01 ∷ []) (c₂ (Swap) (S)) ▸
       at 49 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0024 (lit c4))) ▸ done

  b44 : Chain (Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ Sw12 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ [])
  b44 = at 50 2 [] (wl0018 (lit c4)) ▸
       at 1 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 2 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 3 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 5 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸
       at 5 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 7 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b45 : Chain (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ Sw12 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ [])
  b45 = at 6 2 [] (wl0006 (lit c4)) ▸
       at 7 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 8 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 9 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 10 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 11 2 (S1 ∷ Sw12 ∷ []) (sym (wl1426 (lit c4))) ▸
       at 12 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 13 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸ done

  b46 : Chain (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sw12 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ [])
  b46 = at 14 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 15 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 16 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 18 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (wl0006 (lit c4)) ▸
       at 18 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 20 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] (wl0006 (lit c4)) ▸ done

  b47 : Chain (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ Sw12 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ [])
  b47 = at 20 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 21 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 22 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 23 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 24 2 (S1 ∷ Sw12 ∷ []) (sym (wl1426 (lit c4))) ▸
       at 25 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] (wl0006 (lit c4)) ▸ done

  b48 : Chain (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ Sw12 ∷ CS02 ∷ CS02 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ Sw12 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ [])
  b48 = at 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 [] (wl0006 (lit c4)) ▸
       at 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 [] (wl0006 (lit c4)) ▸
       at 29 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 31 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 [] (wl0006 (lit c4)) ▸
       at 31 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸ done

  b49 : Chain (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ Sw12 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ [])
  b49 = at 33 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 [] (wl0006 (lit c4)) ▸
       at 33 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 34 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 35 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 36 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 37 2 (S1 ∷ Sw12 ∷ []) (sym (wl1426 (lit c4))) ▸
       at 38 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸ done

  b50 : Chain (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ [])
  b50 = at 39 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 41 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 40 2 [] (wl0006 (lit c4)) ▸
       at 41 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 43 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 42 2 [] (wl0006 (lit c4)) ▸
       at 43 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 44 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸ done

  b51 : Chain (Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ []) (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS01 ∷ Sw01 ∷ [])
  b51 = at 45 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 46 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 47 2 (S1 ∷ Sw12 ∷ []) (sym (wl1426 (lit c4))) ▸
       at 49 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 48 2 [] (wl0006 (lit c4)) ▸
       at 49 2 [] (wl0006 (lit c4)) ▸
       at 0 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 1 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸ done

  b52 : Chain (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS01 ∷ Sw01 ∷ []) (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS01 ∷ Sw01 ∷ [])
  b52 = at 2 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 3 2 (CK01 ∷ Sw01 ∷ []) (sym (wl1425 (lit c4))) ▸
       at 4 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 5 2 (CK01 ∷ Sw01 ∷ []) (sym (wl1425 (lit c4))) ▸
       at 6 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 7 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 8 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 9 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸ done

  b53 : Chain (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS01 ∷ Sw01 ∷ []) (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ Sw01 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS01 ∷ Sw01 ∷ [])
  b53 = at 10 2 (S0 ∷ Sw01 ∷ []) (sym (wl1424 (lit c4))) ▸
       at 11 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 12 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 13 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 14 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 15 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 16 2 (CK01 ∷ Sw01 ∷ []) (sym (wl1425 (lit c4))) ▸
       at 17 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸ done

  b54 : Chain (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ Sw01 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS01 ∷ Sw01 ∷ []) (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS01 ∷ Sw01 ∷ [])
  b54 = at 18 2 (CK01 ∷ Sw01 ∷ []) (sym (wl1425 (lit c4))) ▸
       at 19 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 20 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 21 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 22 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 23 2 (S0 ∷ Sw01 ∷ []) (sym (wl1424 (lit c4))) ▸
       at 24 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 25 2 (CS01 ∷ Sw01 ∷ []) (sym (wl1462 (lit c4))) ▸ done

  b55 : Chain (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS01 ∷ Sw01 ∷ []) (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS01 ∷ Sw01 ∷ [])
  b55 = at 26 2 (CS01 ∷ Sw01 ∷ []) (sym (wl1462 (lit c4))) ▸
       at 27 2 (CS01 ∷ Sw01 ∷ []) (sym (wl1462 (lit c4))) ▸
       at 28 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 29 2 (CK01 ∷ Sw01 ∷ []) (sym (wl1425 (lit c4))) ▸
       at 30 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 31 2 (CK01 ∷ Sw01 ∷ []) (sym (wl1425 (lit c4))) ▸
       at 32 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 33 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸ done

  b56 : Chain (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS01 ∷ Sw01 ∷ []) (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS01 ∷ Sw01 ∷ [])
  b56 = at 34 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 35 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 36 2 (S0 ∷ Sw01 ∷ []) (sym (wl1424 (lit c4))) ▸
       at 37 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 38 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 39 2 (CK01 ∷ Sw01 ∷ []) (sym (wl1425 (lit c4))) ▸
       at 40 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 41 2 (CK01 ∷ Sw01 ∷ []) (sym (wl1425 (lit c4))) ▸ done

  b57 : Chain (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS01 ∷ Sw01 ∷ []) (CCZ014 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ [])
  b57 = at 42 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 43 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 44 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 45 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 46 2 (S0 ∷ Sw01 ∷ []) (sym (wl1424 (lit c4))) ▸
       at 47 2 (CS01 ∷ Sw01 ∷ []) (sym (wl1462 (lit c4))) ▸
       at 48 2 [] (wl0018 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩-at0213243140 c4) ▸ done

  b58 : Chain (CCZ014 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ [])
  b58 = at 1 0 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (lem-deb-CKS-eps-at0213243140 c4)) ▸
       at 124 4 (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-CS2-at0213243140 c4) ▸
       at 121 4 (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-CS2-at0213243140 c4) ▸
       at 118 4 (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-CS2-at0213243140 c4) ▸
       at 115 4 (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-CS2-at0213243140 c4) ▸
       at 112 4 (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0213243140 c4) ▸
       at 109 4 (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-CS2-at0213243140 c4) ▸
       at 106 4 (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0213243140 c4) ▸ done

  b59 : Chain (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ [])
  b59 = at 103 4 (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-CS2-at0213243140 c4) ▸
       at 100 4 (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0213243140 c4) ▸
       at 97 4 (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0213243140 c4) ▸
       at 94 4 (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-CS2-at0213243140 c4) ▸
       at 91 4 (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-CS2-at0213243140 c4) ▸
       at 88 4 (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-CS2-at0213243140 c4) ▸
       at 85 4 (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-CS2-at0213243140 c4) ▸
       at 82 4 (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0213243140 c4) ▸ done

  b60 : Chain (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ [])
  b60 = at 79 4 (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-CS2-at0213243140 c4) ▸
       at 76 4 (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0213243140 c4) ▸
       at 73 4 (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-CS2-at0213243140 c4) ▸
       at 70 4 (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0213243140 c4) ▸
       at 125 4 (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-K3-at0213243140 c4) ▸
       at 122 4 (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-K3-at0213243140 c4) ▸
       at 119 4 (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-K3-at0213243140 c4) ▸
       at 116 4 (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-K3-at0213243140 c4) ▸ done

  b61 : Chain (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ [])
  b61 = at 113 4 (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-K3-at0213243140 c4) ▸
       at 110 4 (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-K3-at0213243140 c4) ▸
       at 107 4 (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-K3-at0213243140 c4) ▸
       at 104 4 (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-K3-at0213243140 c4) ▸
       at 101 4 (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-K3-at0213243140 c4) ▸
       at 98 4 (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-K3-at0213243140 c4) ▸
       at 95 4 (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-K3-at0213243140 c4) ▸
       at 92 4 (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-K3-at0213243140 c4) ▸ done

  b62 : Chain (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ [])
  b62 = at 89 4 (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-K3-at0213243140 c4) ▸
       at 86 4 (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-K3-at0213243140 c4) ▸
       at 83 4 (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-K3-at0213243140 c4) ▸
       at 80 4 (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-K3-at0213243140 c4) ▸ done

