{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D150 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0003 ; wl0004 ; wl0006 ; wl0008 ; wl0011 ; wl0013 ; wl0018 ; wl0090 ; wl0095 ; wl0129 ; wl1423 ; wl1424 ; wl1425 ; wl1426 ; wl1427 ; wl1428 ; wl1429)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-8fc9546c)
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
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw0-L)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L ; lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L ; lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L ; lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L)

-- deb-CKS-eps @0213243140: 375 steps
lem-deb-CKS-eps-at0213243140 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-CKS-eps-at0213243140 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (run b46))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b0 = at 2 2 [] (wl1423 (lit c4)) ▸
       at 3 2 [] (wl1423 (lit c4)) ▸
       at 4 2 [] (wl1423 (lit c4)) ▸
       at 5 2 [] (wl1423 (lit c4)) ▸
       at 6 2 [] (wl1423 (lit c4)) ▸
       at 7 2 [] (wl1423 (lit c4)) ▸
       at 8 2 [] (wl1423 (lit c4)) ▸
       at 9 2 [] (wl1423 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b1 = at 10 2 [] (wl1423 (lit c4)) ▸
       at 11 2 [] (wl1423 (lit c4)) ▸
       at 12 2 [] (wl1423 (lit c4)) ▸
       at 13 2 [] (wl1423 (lit c4)) ▸
       at 14 2 [] (wl1423 (lit c4)) ▸
       at 15 2 [] (wl1423 (lit c4)) ▸
       at 16 2 [] (wl1423 (lit c4)) ▸
       at 17 2 [] (wl1423 (lit c4)) ▸ done

  b2 : Chain (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b2 = at 18 2 [] (wl1423 (lit c4)) ▸
       at 19 2 [] (wl1423 (lit c4)) ▸
       at 20 2 [] (wl1423 (lit c4)) ▸
       at 21 2 [] (wl1423 (lit c4)) ▸
       at 22 2 [] (wl1423 (lit c4)) ▸
       at 23 2 [] (wl1423 (lit c4)) ▸
       at 24 2 [] (wl1423 (lit c4)) ▸
       at 25 2 [] (wl1423 (lit c4)) ▸ done

  b3 : Chain (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b3 = at 26 2 [] (wl1423 (lit c4)) ▸
       at 27 2 [] (wl1423 (lit c4)) ▸
       at 28 2 [] (wl1423 (lit c4)) ▸
       at 29 2 [] (wl1423 (lit c4)) ▸
       at 30 2 [] (wl1423 (lit c4)) ▸
       at 31 2 [] (wl1423 (lit c4)) ▸
       at 32 2 [] (wl1423 (lit c4)) ▸
       at 33 2 [] (wl1423 (lit c4)) ▸ done

  b4 : Chain (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b4 = at 34 2 [] (wl1423 (lit c4)) ▸
       at 35 2 [] (wl1423 (lit c4)) ▸
       at 36 2 [] (wl1423 (lit c4)) ▸
       at 37 2 [] (wl1423 (lit c4)) ▸
       at 38 2 [] (wl1423 (lit c4)) ▸
       at 39 2 [] (wl1423 (lit c4)) ▸
       at 40 2 [] (wl1423 (lit c4)) ▸
       at 41 2 [] (wl1423 (lit c4)) ▸ done

  b5 : Chain (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ Sw01 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sw01 ∷ X0 ∷ [])
  b5 = at 42 2 [] (wl1423 (lit c4)) ▸
       at 43 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 42 2 (Sw01 ∷ S1 ∷ []) (wl1424 (lit c4)) ▸
       at 41 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 40 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 39 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 38 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 37 2 (Sw01 ∷ CK10 ∷ []) (wl1425 (lit c4)) ▸ done

  b6 : Chain (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ Sw01 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sw01 ∷ X0 ∷ [])
  b6 = at 36 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 35 2 (Sw01 ∷ CK10 ∷ []) (wl1425 (lit c4)) ▸
       at 34 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 33 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 32 2 (Sw01 ∷ S1 ∷ []) (wl1424 (lit c4)) ▸
       at 31 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 30 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 29 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸ done

  b7 : Chain (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sw01 ∷ X0 ∷ [])
  b7 = at 28 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 27 2 (Sw01 ∷ CK10 ∷ []) (wl1425 (lit c4)) ▸
       at 26 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 25 2 (Sw01 ∷ CK10 ∷ []) (wl1425 (lit c4)) ▸
       at 24 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 23 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 22 2 (Sw01 ∷ S1 ∷ []) (wl1424 (lit c4)) ▸
       at 21 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸ done

  b8 : Chain (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sw01 ∷ X0 ∷ [])
  b8 = at 20 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 19 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 18 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 17 2 (Sw01 ∷ CK10 ∷ []) (wl1425 (lit c4)) ▸
       at 16 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 15 2 (Sw01 ∷ CK10 ∷ []) (wl1425 (lit c4)) ▸
       at 14 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 13 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸ done

  b9 : Chain (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sw01 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sw01 ∷ X0 ∷ [])
  b9 = at 12 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 11 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 10 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 9 2 (Sw01 ∷ S1 ∷ []) (wl1424 (lit c4)) ▸
       at 8 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 7 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 6 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 5 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸ done

  b10 : Chain (X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b10 = at 4 2 (Sw01 ∷ CK10 ∷ []) (wl1425 (lit c4)) ▸
       at 3 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 2 2 (Sw01 ∷ CK10 ∷ []) (wl1425 (lit c4)) ▸
       at 1 2 (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4)) ▸
       at 44 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 43 2 (Sw12 ∷ S2 ∷ []) (wl1426 (lit c4)) ▸
       at 42 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 41 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸ done

  b11 : Chain (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b11 = at 40 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 39 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 38 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 39 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸
       at 37 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 36 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 37 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸
       at 35 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸ done

  b12 : Chain (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ Sb2-4-10-3 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ Sw12 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b12 = at 34 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 33 2 (Sw12 ∷ S2 ∷ []) (wl1426 (lit c4)) ▸
       at 32 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 31 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 30 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 29 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 28 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 29 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ Sw12 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b13 = at 27 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 26 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 27 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 24 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 23 2 (Sw12 ∷ S2 ∷ []) (wl1426 (lit c4)) ▸
       at 22 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 21 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸ done

  b14 : Chain (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b14 = at 20 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 19 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 18 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 19 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 16 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 17 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸ done

  b15 : Chain (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S1 ∷ CS14 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sb2-4-10-3 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b15 = at 14 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 13 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 12 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 11 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 10 2 (Sw12 ∷ S2 ∷ []) (wl1426 (lit c4)) ▸
       at 9 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 8 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 7 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸ done

  b16 : Chain (X0 ∷ Sw01 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ CK10 ∷ Sb2-4-10-3 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b16 = at 6 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 6 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 4 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4)) ▸
       at 45 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸ done

  b17 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sw01 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b17 = at 44 2 (Sw01 ∷ S2 ∷ []) (sym (c₂ (Swap) (S))) ▸
       at 43 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 42 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 41 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 40 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 39 2 (Sw01 ∷ CK21 ∷ []) (wl1427 (lit c4)) ▸
       at 38 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 37 2 (Sw01 ∷ CK21 ∷ []) (wl1427 (lit c4)) ▸ done

  b18 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sw01 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ Sw01 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b18 = at 36 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 35 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 34 2 (Sw01 ∷ S2 ∷ []) (sym (c₂ (Swap) (S))) ▸
       at 33 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 32 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 31 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 30 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 29 2 (Sw01 ∷ CK21 ∷ []) (wl1427 (lit c4)) ▸ done

  b19 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ Sw01 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ Sw01 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b19 = at 28 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 27 2 (Sw01 ∷ CK21 ∷ []) (wl1427 (lit c4)) ▸
       at 26 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 25 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 24 2 (Sw01 ∷ S2 ∷ []) (sym (c₂ (Swap) (S))) ▸
       at 23 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 22 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 21 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸ done

  b20 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ Sw01 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b20 = at 20 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 19 2 (Sw01 ∷ CK21 ∷ []) (wl1427 (lit c4)) ▸
       at 18 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 17 2 (Sw01 ∷ CK21 ∷ []) (wl1427 (lit c4)) ▸
       at 16 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 15 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 14 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 13 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸ done

  b21 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sb1-4-20-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sw01 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b21 = at 12 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 11 2 (Sw01 ∷ S2 ∷ []) (sym (c₂ (Swap) (S))) ▸
       at 10 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 9 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 8 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 7 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 6 2 (Sw01 ∷ CK21 ∷ []) (wl1427 (lit c4)) ▸
       at 5 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸ done

  b22 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sb1-4-20-3 ∷ CK20 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b22 = at 4 2 (Sw01 ∷ CK21 ∷ []) (wl1427 (lit c4)) ▸
       at 3 2 (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4)) ▸
       at 46 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 45 2 (Sw23 ∷ S3 ∷ []) (wl1428 (lit c4)) ▸
       at 44 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 43 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 42 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 41 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸ done

  b23 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw23 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b23 = at 40 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 41 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 39 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 38 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 39 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 37 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 36 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 35 2 (Sw23 ∷ S3 ∷ []) (wl1428 (lit c4)) ▸ done

  b24 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw23 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b24 = at 34 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 33 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 32 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 31 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 30 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 31 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 28 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸ done

  b25 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b25 = at 29 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 26 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 25 2 (Sw23 ∷ S3 ∷ []) (wl1428 (lit c4)) ▸
       at 24 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 23 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 22 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 21 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸ done

  b26 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b26 = at 20 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 21 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 19 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 16 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 15 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸ done

  b27 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S2 ∷ CS24 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b27 = at 14 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 13 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 12 2 (Sw23 ∷ S3 ∷ []) (wl1428 (lit c4)) ▸
       at 11 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 10 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 9 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 8 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸ done

  b28 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sb0-4-21-3 ∷ CK21 ∷ Sb0-4-21-3 ∷ Sw23 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ Sw12 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b28 = at 8 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 6 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4)) ▸
       at 47 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 46 2 (Sw12 ∷ S3 ∷ []) (sym (c₃ (Swap ↑) (S))) ▸
       at 45 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸ done

  b29 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ Sw12 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b29 = at 44 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 43 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 42 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 41 2 (Sw12 ∷ CK32 ∷ []) (wl0095 (lit c4)) ▸
       at 40 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 39 2 (Sw12 ∷ CK32 ∷ []) (wl0095 (lit c4)) ▸
       at 38 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 37 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸ done

  b30 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sw12 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b30 = at 36 2 (Sw12 ∷ S3 ∷ []) (sym (c₃ (Swap ↑) (S))) ▸
       at 35 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 34 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 33 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 32 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 31 2 (Sw12 ∷ CK32 ∷ []) (wl0095 (lit c4)) ▸
       at 30 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 29 2 (Sw12 ∷ CK32 ∷ []) (wl0095 (lit c4)) ▸ done

  b31 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sw12 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ Sw12 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b31 = at 28 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 27 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 26 2 (Sw12 ∷ S3 ∷ []) (sym (c₃ (Swap ↑) (S))) ▸
       at 25 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 24 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 23 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 22 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 21 2 (Sw12 ∷ CK32 ∷ []) (wl0095 (lit c4)) ▸ done

  b32 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ Sw12 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sw12 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b32 = at 20 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 19 2 (Sw12 ∷ CK32 ∷ []) (wl0095 (lit c4)) ▸
       at 18 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 17 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 16 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 15 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 14 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 13 2 (Sw12 ∷ S3 ∷ []) (sym (c₃ (Swap ↑) (S))) ▸ done

  b33 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CK31 ∷ Sb0-4-31-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sw12 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b33 = at 12 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 11 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 10 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 9 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 8 2 (Sw12 ∷ CK32 ∷ []) (wl0095 (lit c4)) ▸
       at 7 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸
       at 6 2 (Sw12 ∷ CK32 ∷ []) (wl0095 (lit c4)) ▸
       at 5 2 (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4)) ▸ done

  b34 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ Sw34 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b34 = at 48 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 47 2 (Sw34 ∷ S4 ∷ []) (wl1429 (lit c4)) ▸
       at 46 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 45 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 44 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 43 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 42 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 43 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸ done

  b35 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ Sw34 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ Sw34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b35 = at 41 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 40 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 41 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 39 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 38 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 37 2 (Sw34 ∷ S4 ∷ []) (wl1429 (lit c4)) ▸
       at 36 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 35 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸ done

  b36 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ Sw34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b36 = at 34 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 33 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 32 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 33 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 31 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 30 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 31 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸ done

  b37 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ Sw34 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b37 = at 28 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 27 2 (Sw34 ∷ S4 ∷ []) (wl1429 (lit c4)) ▸
       at 26 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 25 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 24 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 23 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 22 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 23 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸ done

  b38 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ CS34 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ Sw34 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw34 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b38 = at 21 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 20 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 21 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 18 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 17 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 16 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 15 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸ done

  b39 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sb0-4-32-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S3 ∷ Sw34 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b39 = at 14 2 (Sw34 ∷ S4 ∷ []) (wl1429 (lit c4)) ▸
       at 13 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 12 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 11 2 (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4)) ▸
       at 10 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 10 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸ done

  b40 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-4-32-1 ∷ CK32 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ Sw23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b40 = at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 8 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4)) ▸
       at 49 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 48 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸
       at 47 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 46 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 45 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸ done

  b41 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ Sw23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ Sw23 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b41 = at 44 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 43 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 42 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 41 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 40 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 39 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 38 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸
       at 37 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸ done

  b42 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ Sw23 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw23 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b42 = at 36 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 35 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 34 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 33 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 32 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 31 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 30 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 29 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸ done

  b43 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sw23 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sw23 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b43 = at 28 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸
       at 27 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 26 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 25 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 24 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 23 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 22 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 21 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸ done

  b44 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sb0-3-42-1 ∷ Sw23 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ Sw23 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b44 = at 20 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 19 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 18 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 17 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 16 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 15 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸
       at 14 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 13 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸ done

  b45 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CK42 ∷ Sb0-3-42-1 ∷ CS34 ∷ Sw23 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ [])
  b45 = at 12 2 (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4)) ▸
       at 11 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 10 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 9 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 8 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 7 2 (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4)) ▸
       at 8 42 [] (lem-TR2-8fc9546c c4) ▸
       at 7 2 [] (wl0003 (lit c4)) ▸ done

  b46 : Chain (X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ X0 ∷ []) []
  b46 = at 6 2 [] (wl0004 (lit c4)) ▸
       at 5 2 [] (wl0006 (lit c4)) ▸
       at 4 2 [] (wl0003 (lit c4)) ▸
       at 3 2 [] (wl0018 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸
       at 1 2 [] (wl0018 (lit c4)) ▸
       at 0 2 [] (wl1423 (lit c4)) ▸ done
