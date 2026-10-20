{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D150 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0003 ; wl0004 ; wl0006 ; wl0008 ; wl0011 ; wl0013 ; wl0018 ; wl0090 ; wl0095 ; wl0129 ; wl1423 ; wl1424 ; wl1425 ; wl1426 ; wl1427 ; wl1428 ; wl1429)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
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

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl1423 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0018 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wl1424 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sb2-4-01-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ []) (wl1425 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0006 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) (wl1426 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sb2-4-10-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (c₂ (Swap) (S))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sb1-4-20-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wl1427 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0003 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (S2 ∷ Sw23 ∷ []) (Sw23 ∷ S3 ∷ []) (wl1428 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sb0-4-21-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sb0-4-31-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CK31 ∷ Sw12 ∷ []) (Sw12 ∷ CK32 ∷ []) (wl0095 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0004 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (S3 ∷ Sw34 ∷ []) (Sw34 ∷ S4 ∷ []) (wl1429 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ []) (wl0129 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sb0-4-32-1 ∷ Sw34 ∷ []) (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q28 : Ws → Eqn
  q28 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0008 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Sb0-3-42-1 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) [] (lem-TR2-8fc9546c c4)

-- deb-CKS-eps @0213243140: 375 steps
lem-deb-CKS-eps-at0213243140 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-CKS-eps-at0213243140 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) []
  (rw 2 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   rw 42 (q1 c4) ∷
   rw⁻ 43 (q2 c4) ∷
   rw 42 (q3 c4) ∷
   rw 41 (q4 c4) ∷
   rw 40 (q4 c4) ∷
   rw 39 (q4 c4) ∷
   rw 38 (q5 c4) ∷
   rw 37 (q6 c4) ∷
   rw 36 (q5 c4) ∷
   rw 35 (q6 c4) ∷
   rw 34 (q5 c4) ∷
   rw 33 (q5 c4) ∷
   rw 32 (q3 c4) ∷
   rw 31 (q4 c4) ∷
   rw 30 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   rw 28 (q5 c4) ∷
   rw 27 (q6 c4) ∷
   rw 26 (q5 c4) ∷
   rw 25 (q6 c4) ∷
   rw 24 (q5 c4) ∷
   rw 23 (q4 c4) ∷
   rw 22 (q3 c4) ∷
   rw 21 (q4 c4) ∷
   rw 20 (q4 c4) ∷
   rw 19 (q4 c4) ∷
   rw 18 (q5 c4) ∷
   rw 17 (q6 c4) ∷
   rw 16 (q5 c4) ∷
   rw 15 (q6 c4) ∷
   rw 14 (q5 c4) ∷
   rw 13 (q5 c4) ∷
   rw 12 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   rw 10 (q4 c4) ∷
   rw 9 (q3 c4) ∷
   rw 8 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 44 (q7 c4) ∷
   rw 43 (q8 c4) ∷
   rw 42 (q9 c4) ∷
   rw 41 (q9 c4) ∷
   rw 40 (q9 c4) ∷
   rw 39 (q10 c4) ∷
   rw⁻ 38 (q7 c4) ∷
   re 39 3 (CK20 ∷ []) ∷
   rw 37 (q10 c4) ∷
   rw⁻ 36 (q7 c4) ∷
   re 37 3 (CK20 ∷ []) ∷
   rw 35 (q10 c4) ∷
   rw 34 (q10 c4) ∷
   rw 33 (q8 c4) ∷
   rw 32 (q9 c4) ∷
   rw 31 (q9 c4) ∷
   rw 30 (q9 c4) ∷
   rw 29 (q10 c4) ∷
   rw⁻ 28 (q7 c4) ∷
   re 29 3 (CK20 ∷ []) ∷
   rw 27 (q10 c4) ∷
   rw⁻ 26 (q7 c4) ∷
   re 27 3 (CK20 ∷ []) ∷
   rw 25 (q10 c4) ∷
   rw 24 (q9 c4) ∷
   rw 23 (q8 c4) ∷
   rw 22 (q9 c4) ∷
   rw 21 (q9 c4) ∷
   rw 20 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw⁻ 18 (q7 c4) ∷
   re 19 3 (CK20 ∷ []) ∷
   rw 17 (q10 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   re 17 3 (CK20 ∷ []) ∷
   rw 15 (q10 c4) ∷
   rw 14 (q10 c4) ∷
   rw 13 (q10 c4) ∷
   rw 12 (q10 c4) ∷
   rw 11 (q9 c4) ∷
   rw 10 (q8 c4) ∷
   rw 9 (q9 c4) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q9 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 6 3 (CK20 ∷ []) ∷
   rw 4 (q10 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 4 3 (CK20 ∷ []) ∷
   rw 2 (q10 c4) ∷
   rw⁻ 45 (q2 c4) ∷
   rw⁻ 44 (q11 c4) ∷
   rw⁻ 43 (q12 c4) ∷
   rw⁻ 42 (q12 c4) ∷
   rw⁻ 41 (q12 c4) ∷
   rw 40 (q13 c4) ∷
   rw 39 (q14 c4) ∷
   rw 38 (q13 c4) ∷
   rw 37 (q14 c4) ∷
   rw 36 (q13 c4) ∷
   rw 35 (q13 c4) ∷
   rw⁻ 34 (q11 c4) ∷
   rw⁻ 33 (q12 c4) ∷
   rw⁻ 32 (q12 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw 30 (q13 c4) ∷
   rw 29 (q14 c4) ∷
   rw 28 (q13 c4) ∷
   rw 27 (q14 c4) ∷
   rw 26 (q13 c4) ∷
   rw⁻ 25 (q12 c4) ∷
   rw⁻ 24 (q11 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 22 (q12 c4) ∷
   rw⁻ 21 (q12 c4) ∷
   rw 20 (q13 c4) ∷
   rw 19 (q14 c4) ∷
   rw 18 (q13 c4) ∷
   rw 17 (q14 c4) ∷
   rw 16 (q13 c4) ∷
   rw 15 (q13 c4) ∷
   rw 14 (q13 c4) ∷
   rw 13 (q13 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw 7 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw 5 (q13 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 46 (q15 c4) ∷
   rw 45 (q16 c4) ∷
   rw 44 (q17 c4) ∷
   rw 43 (q17 c4) ∷
   rw 42 (q17 c4) ∷
   rw 41 (q18 c4) ∷
   rw⁻ 40 (q15 c4) ∷
   re 41 3 (CK31 ∷ []) ∷
   rw 39 (q18 c4) ∷
   rw⁻ 38 (q15 c4) ∷
   re 39 3 (CK31 ∷ []) ∷
   rw 37 (q18 c4) ∷
   rw 36 (q18 c4) ∷
   rw 35 (q16 c4) ∷
   rw 34 (q17 c4) ∷
   rw 33 (q17 c4) ∷
   rw 32 (q17 c4) ∷
   rw 31 (q18 c4) ∷
   rw⁻ 30 (q15 c4) ∷
   re 31 3 (CK31 ∷ []) ∷
   rw 29 (q18 c4) ∷
   rw⁻ 28 (q15 c4) ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 27 (q18 c4) ∷
   rw 26 (q17 c4) ∷
   rw 25 (q16 c4) ∷
   rw 24 (q17 c4) ∷
   rw 23 (q17 c4) ∷
   rw 22 (q17 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 20 (q15 c4) ∷
   re 21 3 (CK31 ∷ []) ∷
   rw 19 (q18 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   re 19 3 (CK31 ∷ []) ∷
   rw 17 (q18 c4) ∷
   rw 16 (q18 c4) ∷
   rw 15 (q18 c4) ∷
   rw 14 (q18 c4) ∷
   rw 13 (q17 c4) ∷
   rw 12 (q16 c4) ∷
   rw 11 (q17 c4) ∷
   rw 10 (q17 c4) ∷
   rw 9 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   re 8 3 (CK31 ∷ []) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   re 6 3 (CK31 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 47 (q7 c4) ∷
   rw⁻ 46 (q19 c4) ∷
   rw⁻ 45 (q20 c4) ∷
   rw⁻ 44 (q20 c4) ∷
   rw⁻ 43 (q20 c4) ∷
   rw 42 (q21 c4) ∷
   rw 41 (q22 c4) ∷
   rw 40 (q21 c4) ∷
   rw 39 (q22 c4) ∷
   rw 38 (q21 c4) ∷
   rw 37 (q21 c4) ∷
   rw⁻ 36 (q19 c4) ∷
   rw⁻ 35 (q20 c4) ∷
   rw⁻ 34 (q20 c4) ∷
   rw⁻ 33 (q20 c4) ∷
   rw 32 (q21 c4) ∷
   rw 31 (q22 c4) ∷
   rw 30 (q21 c4) ∷
   rw 29 (q22 c4) ∷
   rw 28 (q21 c4) ∷
   rw⁻ 27 (q20 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw⁻ 25 (q20 c4) ∷
   rw⁻ 24 (q20 c4) ∷
   rw⁻ 23 (q20 c4) ∷
   rw 22 (q21 c4) ∷
   rw 21 (q22 c4) ∷
   rw 20 (q21 c4) ∷
   rw 19 (q22 c4) ∷
   rw 18 (q21 c4) ∷
   rw 17 (q21 c4) ∷
   rw 16 (q21 c4) ∷
   rw 15 (q21 c4) ∷
   rw⁻ 14 (q20 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw⁻ 11 (q20 c4) ∷
   rw⁻ 10 (q20 c4) ∷
   rw 9 (q21 c4) ∷
   rw 8 (q22 c4) ∷
   rw 7 (q21 c4) ∷
   rw 6 (q22 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 48 (q23 c4) ∷
   rw 47 (q24 c4) ∷
   rw 46 (q25 c4) ∷
   rw 45 (q25 c4) ∷
   rw 44 (q25 c4) ∷
   rw 43 (q26 c4) ∷
   rw⁻ 42 (q23 c4) ∷
   re 43 3 (CK42 ∷ []) ∷
   rw 41 (q26 c4) ∷
   rw⁻ 40 (q23 c4) ∷
   re 41 3 (CK42 ∷ []) ∷
   rw 39 (q26 c4) ∷
   rw 38 (q26 c4) ∷
   rw 37 (q24 c4) ∷
   rw 36 (q25 c4) ∷
   rw 35 (q25 c4) ∷
   rw 34 (q25 c4) ∷
   rw 33 (q26 c4) ∷
   rw⁻ 32 (q23 c4) ∷
   re 33 3 (CK42 ∷ []) ∷
   rw 31 (q26 c4) ∷
   rw⁻ 30 (q23 c4) ∷
   re 31 3 (CK42 ∷ []) ∷
   rw 29 (q26 c4) ∷
   rw 28 (q25 c4) ∷
   rw 27 (q24 c4) ∷
   rw 26 (q25 c4) ∷
   rw 25 (q25 c4) ∷
   rw 24 (q25 c4) ∷
   rw 23 (q26 c4) ∷
   rw⁻ 22 (q23 c4) ∷
   re 23 3 (CK42 ∷ []) ∷
   rw 21 (q26 c4) ∷
   rw⁻ 20 (q23 c4) ∷
   re 21 3 (CK42 ∷ []) ∷
   rw 19 (q26 c4) ∷
   rw 18 (q26 c4) ∷
   rw 17 (q26 c4) ∷
   rw 16 (q26 c4) ∷
   rw 15 (q25 c4) ∷
   rw 14 (q24 c4) ∷
   rw 13 (q25 c4) ∷
   rw 12 (q25 c4) ∷
   rw 11 (q25 c4) ∷
   rw 10 (q26 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   re 10 3 (CK42 ∷ []) ∷
   rw 8 (q26 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   re 8 3 (CK42 ∷ []) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 49 (q15 c4) ∷
   rw⁻ 48 (q27 c4) ∷
   rw 47 (q28 c4) ∷
   rw 46 (q28 c4) ∷
   rw 45 (q28 c4) ∷
   rw 44 (q29 c4) ∷
   rw 43 (q30 c4) ∷
   rw 42 (q29 c4) ∷
   rw 41 (q30 c4) ∷
   rw 40 (q29 c4) ∷
   rw 39 (q29 c4) ∷
   rw⁻ 38 (q27 c4) ∷
   rw 37 (q28 c4) ∷
   rw 36 (q28 c4) ∷
   rw 35 (q28 c4) ∷
   rw 34 (q29 c4) ∷
   rw 33 (q30 c4) ∷
   rw 32 (q29 c4) ∷
   rw 31 (q30 c4) ∷
   rw 30 (q29 c4) ∷
   rw 29 (q28 c4) ∷
   rw⁻ 28 (q27 c4) ∷
   rw 27 (q28 c4) ∷
   rw 26 (q28 c4) ∷
   rw 25 (q28 c4) ∷
   rw 24 (q29 c4) ∷
   rw 23 (q30 c4) ∷
   rw 22 (q29 c4) ∷
   rw 21 (q30 c4) ∷
   rw 20 (q29 c4) ∷
   rw 19 (q29 c4) ∷
   rw 18 (q29 c4) ∷
   rw 17 (q29 c4) ∷
   rw 16 (q28 c4) ∷
   rw⁻ 15 (q27 c4) ∷
   rw 14 (q28 c4) ∷
   rw 13 (q28 c4) ∷
   rw 12 (q28 c4) ∷
   rw 11 (q29 c4) ∷
   rw 10 (q30 c4) ∷
   rw 9 (q29 c4) ∷
   rw 8 (q30 c4) ∷
   rw 7 (q29 c4) ∷
   rw 8 (q31 c4) ∷
   rw 7 (q15 c4) ∷
   rw 6 (q23 c4) ∷
   rw 5 (q7 c4) ∷
   rw 4 (q15 c4) ∷
   rw 3 (q2 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q2 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl
