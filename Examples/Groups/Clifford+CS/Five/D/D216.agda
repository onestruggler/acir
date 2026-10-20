{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D216 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0003 ; wl0004 ; wl0006 ; wl0008 ; wl0011 ; wl0013 ; wl0018 ; wl0090 ; wl0095 ; wl0129 ; wl1423 ; wl1424 ; wl1425 ; wl1426 ; wl1427 ; wl1428 ; wl1429)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-78b381c2)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3 ; lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F2-K1-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-F1-comm-CS-S0at2 ; lem-F2-K3-CS0 ; lem-F2-K3-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-F1-comm-CS-S1at2)
open import Examples.Groups.Clifford+CS.Five.D.D038 using (lem-F1-order-CSat2 ; lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D067 using (lem-F1-X-CS0at2 ; lem-F2-CS0-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D068 using (lem-F1-X-CS1at2)
open import Examples.Groups.Clifford+CS.Five.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2)
open import Examples.Groups.Clifford+CS.Five.D.D207 using (lem-deb-CKS-at0213243140)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw0-L)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-CS14-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R ; lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R ; lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L ; lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L ; lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R ; lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R ; lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L ; lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L ; lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L ; lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R)

-- ckt-A-R: 191 steps
lem-ckt-A-R : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-ckt-A-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (run b23)))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ X0 ∷ [])
  b0 = at 2 2 [] (wl1423 (lit c4)) ▸
       at 3 2 [] (wl1423 (lit c4)) ▸
       at 4 2 [] (wl1423 (lit c4)) ▸
       at 5 2 [] (wl1423 (lit c4)) ▸
       at 6 2 [] (wl1423 (lit c4)) ▸
       at 7 2 [] (wl1423 (lit c4)) ▸
       at 8 2 [] (wl1423 (lit c4)) ▸
       at 9 2 [] (wl1423 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sw01 ∷ X0 ∷ [])
  b1 = at 10 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 9 2 (Sw01 ∷ S1 ∷ []) (wl1424 (lit c4)) ▸
       at 8 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 7 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 6 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 5 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 4 2 (Sw01 ∷ CK10 ∷ []) (wl1425 (lit c4)) ▸
       at 3 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸ done

  b2 : Chain (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b2 = at 2 2 (Sw01 ∷ CK10 ∷ []) (wl1425 (lit c4)) ▸
       at 1 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 10 2 (Sw12 ∷ S2 ∷ []) (wl1426 (lit c4)) ▸
       at 9 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 8 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 7 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 6 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸ done

  b3 : Chain (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw01 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b3 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 6 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 4 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 12 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 11 2 (Sw01 ∷ S2 ∷ []) (sym (c₂ (Swap) (S))) ▸ done

  b4 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw01 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b4 = at 10 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 9 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 8 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 7 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 6 2 (Sw01 ∷ CK21 ∷ []) (wl1427 (lit c4)) ▸
       at 5 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 4 2 (Sw01 ∷ CK21 ∷ []) (wl1427 (lit c4)) ▸
       at 3 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸ done

  b5 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ Sw23 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b5 = at 13 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 12 2 (Sw23 ∷ S3 ∷ []) (wl1428 (lit c4)) ▸
       at 11 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 10 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 9 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 8 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 8 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ Sw23 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ Sw12 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b6 = at 6 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 6 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 14 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 13 2 (Sw12 ∷ S3 ∷ []) (sym (c₃ (Swap ↑) (S))) ▸
       at 12 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 11 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸ done

  b7 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ Sw12 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sw34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b7 = at 10 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 9 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 8 2 (Sw12 ∷ CK32 ∷ []) (wl0095 (lit c4)) ▸
       at 7 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 6 2 (Sw12 ∷ CK32 ∷ []) (wl0095 (lit c4)) ▸
       at 5 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 15 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 14 2 (Sw34 ∷ S4 ∷ []) (wl1429 (lit c4)) ▸ done

  b8 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sw34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sw34 ∷ Sw34 ∷ CK32 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b8 = at 13 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 12 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 11 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 10 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 10 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸ done

  b9 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sw34 ∷ Sw34 ∷ CK32 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sw23 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b9 = at 8 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 15 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸
       at 14 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 13 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 12 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 11 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸ done

  b10 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sw23 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ Sw23 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b10 = at 10 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 9 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 8 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 7 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 8 9 (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (lem-TR2-78b381c2 c4) ▸
       at 7 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 8 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 (lit c4))) ▸
       at 9 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸ done

  b11 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ Sw23 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sw23 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b11 = at 10 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 (lit c4))) ▸
       at 11 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 12 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 13 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 14 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 15 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 16 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 17 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸ done

  b12 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sw23 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ Sw34 ∷ Sw34 ∷ CK32 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b12 = at 18 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 19 2 (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4)) ▸
       at 20 2 [] (wl0003 (lit c4)) ▸
       at 6 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 8 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 (lit c4)) ▸
       at 8 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 10 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ Sw34 ∷ Sw34 ∷ CK32 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b13 = at 9 2 [] (wl0004 (lit c4)) ▸
       at 10 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 11 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 12 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 13 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 (lit c4))) ▸
       at 14 2 (S3 ∷ Sw34 ∷ []) (sym (wl1429 (lit c4))) ▸
       at 15 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 16 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸ done

  b14 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sw34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ Sw12 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b14 = at 17 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 18 2 (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4)) ▸
       at 19 2 [] (wl0004 (lit c4)) ▸
       at 5 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 6 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 (lit c4))) ▸
       at 7 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 8 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 (lit c4))) ▸
       at 9 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸ done

  b15 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ Sw12 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b15 = at 10 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 11 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 12 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 13 2 (S3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S)) ▸
       at 14 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 15 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 16 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸
       at 17 2 (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4)) ▸ done

  b16 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ Sw23 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b16 = at 18 2 [] (wl0006 (lit c4)) ▸
       at 4 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 (lit c4)) ▸
       at 6 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 (lit c4)) ▸
       at 8 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸ done

  b17 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ Sw23 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b17 = at 9 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 10 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 11 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 12 2 (S2 ∷ Sw23 ∷ []) (sym (wl1428 (lit c4))) ▸
       at 13 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 14 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 15 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸
       at 16 2 (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4)) ▸ done

  b18 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ Sw01 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b18 = at 17 2 [] (wl0003 (lit c4)) ▸
       at 3 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 4 2 (CK20 ∷ Sw01 ∷ []) (sym (wl1427 (lit c4))) ▸
       at 5 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 6 2 (CK20 ∷ Sw01 ∷ []) (sym (wl1427 (lit c4))) ▸
       at 7 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 8 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 9 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b19 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ Sw01 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ Sw12 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b19 = at 10 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 11 2 (S2 ∷ Sw01 ∷ []) (c₂ (Swap) (S)) ▸
       at 12 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 13 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 14 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 15 2 (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸ done

  b20 : Chain (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ Sw12 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b20 = at 4 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 (lit c4)) ▸
       at 4 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 6 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 (lit c4)) ▸
       at 6 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 7 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 8 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸ done

  b21 : Chain (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ Sw01 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sw01 ∷ X0 ∷ [])
  b21 = at 9 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 10 2 (S1 ∷ Sw12 ∷ []) (sym (wl1426 (lit c4))) ▸
       at 11 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 12 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 13 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 14 2 (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4)) ▸
       at 15 2 [] (wl0006 (lit c4)) ▸
       at 1 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸ done

  b22 : Chain (X0 ∷ Sb2-4-01-3 ∷ Sw01 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sw01 ∷ X0 ∷ [])
  b22 = at 2 2 (CK01 ∷ Sw01 ∷ []) (sym (wl1425 (lit c4))) ▸
       at 3 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 4 2 (CK01 ∷ Sw01 ∷ []) (sym (wl1425 (lit c4))) ▸
       at 5 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 6 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 7 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 8 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 9 2 (S0 ∷ Sw01 ∷ []) (sym (wl1424 (lit c4))) ▸ done

  b23 : Chain (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b23 = at 10 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 11 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 12 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 13 2 (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4)) ▸
       at 14 2 [] (wl0018 (lit c4)) ▸
       at 1 10 (CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ []) (lem-deb-CKS-at0213243140 c4) ▸
       at 48 0 (X0 ∷ X0 ∷ []) (sym (wl1423 (lit c4))) ▸ done
