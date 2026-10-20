{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D151 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.FiveV.TR2 using (lem-TR2-4726ca8d)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3 ; lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2)
open import Examples.Groups.Clifford+CS.FiveV.D.D003 using (lem-F4-I-I-at0213243140 ; lem-F4-I-S2-at0213243140 ; lem-F4-I-S3-at0213243140 ; lem-F4-K3-I-at0213243140 ; lem-F4-K3-S2-at0213243140 ; lem-F4-K3-S3-at0213243140 ; lem-F4-S2-I-at0213243140 ; lem-F4-S2-S2-at0213243140 ; lem-F4-S2-S3-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1)
open import Examples.Groups.Clifford+CS.FiveV.D.D023 using (lem-F4-CS2-I-at0213243140 ; lem-F4-CS2-S2-at0213243140 ; lem-F4-CS2-S3-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.D025 using (lem-F2-K1-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D026 using (lem-F1-comm-CS-S0at2 ; lem-F2-K3-CS0 ; lem-F2-K3-CS1)
open import Examples.Groups.Clifford+CS.FiveV.D.D027 using (lem-F1-comm-CS-S1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D038 using (lem-F1-order-CSat2 ; lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D054 using (lem-deb-CKS-split-b-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.D067 using (lem-F1-X-CS0at2 ; lem-F2-CS0-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D068 using (lem-F1-X-CS1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D075 using (lem-deb-CKS-split-a-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R010 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-S2-at0213243140 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-S2-at0213243140 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-S2-at0213243140 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-S2-at0213243140 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-I-at0213243140 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-I-at0213243140 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-I-at0213243140 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-I-at0213243140 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CS01 ∷ []) (CS01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-S3-at0213243140 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ CS01 ∷ []) (CS01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-S3-at0213243140 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS01 ∷ []) (CS01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-S3-at0213243140 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ CS01 ∷ []) (CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-S3-at0213243140 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ []) (lem-deb-CKS-split-a-at0213243140 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ []) (lem-deb-CKS-split-b-at0213243140 c4)

-- deb-CKS @0213243140 part3: 115 steps
lem-deb-CKS-at0213243140-part3 : Ws → ⟪ (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ S0 ∷ X0 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ []) ⟫ʷ
lem-deb-CKS-at0213243140-part3 c4 = derive (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ S0 ∷ X0 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) (CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ [])
  (rw 141 (q1 c4) ∷
   rw 138 (q1 c4) ∷
   rw 135 (q1 c4) ∷
   rw 132 (q2 c4) ∷
   rw 129 (q3 c4) ∷
   rw 126 (q2 c4) ∷
   rw 123 (q3 c4) ∷
   rw 120 (q2 c4) ∷
   rw 117 (q2 c4) ∷
   rw 114 (q4 c4) ∷
   rw 111 (q1 c4) ∷
   rw 108 (q1 c4) ∷
   rw 105 (q1 c4) ∷
   rw 102 (q2 c4) ∷
   rw 99 (q3 c4) ∷
   rw 96 (q2 c4) ∷
   rw 93 (q3 c4) ∷
   rw 90 (q2 c4) ∷
   rw 145 (q5 c4) ∷
   rw 142 (q6 c4) ∷
   rw 139 (q6 c4) ∷
   rw 136 (q6 c4) ∷
   rw 133 (q7 c4) ∷
   rw 130 (q8 c4) ∷
   rw 127 (q7 c4) ∷
   rw 124 (q8 c4) ∷
   rw 121 (q7 c4) ∷
   rw 118 (q7 c4) ∷
   rw 115 (q5 c4) ∷
   rw 112 (q6 c4) ∷
   rw 109 (q6 c4) ∷
   rw 106 (q6 c4) ∷
   rw 103 (q7 c4) ∷
   rw 100 (q8 c4) ∷
   rw 97 (q7 c4) ∷
   rw 94 (q8 c4) ∷
   rw 91 (q7 c4) ∷
   rw 146 (q4 c4) ∷
   rw 143 (q1 c4) ∷
   rw 140 (q1 c4) ∷
   rw 137 (q1 c4) ∷
   rw 134 (q2 c4) ∷
   rw 131 (q3 c4) ∷
   rw 128 (q2 c4) ∷
   rw 125 (q3 c4) ∷
   rw 122 (q2 c4) ∷
   rw 119 (q2 c4) ∷
   rw 116 (q4 c4) ∷
   rw 113 (q1 c4) ∷
   rw 110 (q1 c4) ∷
   rw 107 (q1 c4) ∷
   rw 104 (q2 c4) ∷
   rw 101 (q3 c4) ∷
   rw 98 (q2 c4) ∷
   rw 95 (q3 c4) ∷
   rw 92 (q2 c4) ∷
   rw 147 (q9 c4) ∷
   rw 144 (q10 c4) ∷
   rw 141 (q10 c4) ∷
   rw 138 (q10 c4) ∷
   rw 135 (q11 c4) ∷
   rw 132 (q12 c4) ∷
   rw 129 (q11 c4) ∷
   rw 126 (q12 c4) ∷
   rw 123 (q11 c4) ∷
   rw 120 (q11 c4) ∷
   rw 117 (q9 c4) ∷
   rw 114 (q10 c4) ∷
   rw 111 (q10 c4) ∷
   rw 108 (q10 c4) ∷
   rw 105 (q11 c4) ∷
   rw 102 (q12 c4) ∷
   rw 99 (q11 c4) ∷
   rw 96 (q12 c4) ∷
   rw 93 (q11 c4) ∷
   rw 148 (q9 c4) ∷
   rw 145 (q10 c4) ∷
   rw 142 (q10 c4) ∷
   rw 139 (q10 c4) ∷
   rw 136 (q11 c4) ∷
   rw 133 (q12 c4) ∷
   rw 130 (q11 c4) ∷
   rw 127 (q12 c4) ∷
   rw 124 (q11 c4) ∷
   rw 121 (q11 c4) ∷
   rw 118 (q9 c4) ∷
   rw 115 (q10 c4) ∷
   rw 112 (q10 c4) ∷
   rw 109 (q10 c4) ∷
   rw 106 (q11 c4) ∷
   rw 103 (q12 c4) ∷
   rw 100 (q11 c4) ∷
   rw 97 (q12 c4) ∷
   rw 94 (q11 c4) ∷
   rw 149 (q9 c4) ∷
   rw 146 (q10 c4) ∷
   rw 143 (q10 c4) ∷
   rw 140 (q10 c4) ∷
   rw 137 (q11 c4) ∷
   rw 134 (q12 c4) ∷
   rw 131 (q11 c4) ∷
   rw 128 (q12 c4) ∷
   rw 125 (q11 c4) ∷
   rw 122 (q11 c4) ∷
   rw 119 (q9 c4) ∷
   rw 116 (q10 c4) ∷
   rw 113 (q10 c4) ∷
   rw 110 (q10 c4) ∷
   rw 107 (q11 c4) ∷
   rw 104 (q12 c4) ∷
   rw 101 (q11 c4) ∷
   rw 98 (q12 c4) ∷
   rw 95 (q11 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   rw⁻ 27 (q14 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl 1083 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sb2-0-41-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS04 ∷ Sw12 ∷ []) (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl 87 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sb1-0-42-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sb0-1-42-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q29 : Ws → Eqn
  q29 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl 17 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl 90 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sb0-1-43-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))
  q34 : Ws → Eqn
  q34 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) [] (lem-TR2-4726ca8d c4)

-- deb-AD-eps @02132031: 144 steps
lem-deb-AD-eps-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-AD-eps-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) []
  (rw 2 (q15 c4) ∷
   rw 3 (q15 c4) ∷
   rw 4 (q15 c4) ∷
   rw 5 (q15 c4) ∷
   rw 6 (q15 c4) ∷
   rw 7 (q15 c4) ∷
   rw 8 (q15 c4) ∷
   rw 9 (q15 c4) ∷
   rw 10 (q15 c4) ∷
   rw 11 (q15 c4) ∷
   rw 12 (q15 c4) ∷
   rw 13 (q15 c4) ∷
   rw 14 (q15 c4) ∷
   rw 15 (q15 c4) ∷
   rw 16 (q15 c4) ∷
   rw 17 (q15 c4) ∷
   rw 18 (q15 c4) ∷
   rw 19 (q15 c4) ∷
   rw 20 (q15 c4) ∷
   rw 21 (q15 c4) ∷
   rw 22 (q15 c4) ∷
   rw 23 (q15 c4) ∷
   rw 24 (q15 c4) ∷
   rw 25 (q15 c4) ∷
   rw 26 (q15 c4) ∷
   rw 27 (q15 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   rw 27 (q17 c4) ∷
   rw 26 (q17 c4) ∷
   rw⁻ 25 (q18 c4) ∷
   rw 24 (q19 c4) ∷
   rw 23 (q19 c4) ∷
   rw 22 (q19 c4) ∷
   rw 21 (q17 c4) ∷
   rw 20 (q20 c4) ∷
   rw 19 (q17 c4) ∷
   rw 18 (q20 c4) ∷
   rw 17 (q17 c4) ∷
   rw 16 (q19 c4) ∷
   rw⁻ 15 (q18 c4) ∷
   rw 14 (q19 c4) ∷
   rw 13 (q19 c4) ∷
   rw 12 (q19 c4) ∷
   rw 11 (q17 c4) ∷
   rw 10 (q20 c4) ∷
   rw 9 (q17 c4) ∷
   rw 8 (q20 c4) ∷
   rw 7 (q17 c4) ∷
   rw 6 (q17 c4) ∷
   rw 5 (q17 c4) ∷
   rw 4 (q17 c4) ∷
   rw 3 (q17 c4) ∷
   rw 2 (q17 c4) ∷
   rw 1 (q17 c4) ∷
   rw⁻ 29 (q21 c4) ∷
   rw 28 (q22 c4) ∷
   rw 27 (q22 c4) ∷
   rw⁻ 26 (q23 c4) ∷
   rw 25 (q24 c4) ∷
   rw 24 (q24 c4) ∷
   rw 23 (q24 c4) ∷
   rw 22 (q22 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw 20 (q22 c4) ∷
   rw⁻ 19 (q25 c4) ∷
   rw 18 (q22 c4) ∷
   rw 17 (q24 c4) ∷
   rw⁻ 16 (q23 c4) ∷
   rw 15 (q24 c4) ∷
   rw 14 (q24 c4) ∷
   rw 13 (q24 c4) ∷
   rw 12 (q22 c4) ∷
   rw⁻ 11 (q25 c4) ∷
   rw 10 (q22 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw 8 (q22 c4) ∷
   rw 7 (q22 c4) ∷
   rw 6 (q22 c4) ∷
   rw 5 (q22 c4) ∷
   rw 4 (q22 c4) ∷
   rw 3 (q22 c4) ∷
   rw 2 (q22 c4) ∷
   rw⁻ 30 (q26 c4) ∷
   rw 29 (q27 c4) ∷
   rw 28 (q27 c4) ∷
   rw⁻ 27 (q28 c4) ∷
   rw 26 (q29 c4) ∷
   rw 25 (q29 c4) ∷
   rw 24 (q29 c4) ∷
   rw 23 (q27 c4) ∷
   rw 22 (q30 c4) ∷
   rw 21 (q27 c4) ∷
   rw 20 (q30 c4) ∷
   rw 19 (q27 c4) ∷
   rw 18 (q29 c4) ∷
   rw⁻ 17 (q28 c4) ∷
   rw 16 (q29 c4) ∷
   rw 15 (q29 c4) ∷
   rw 14 (q29 c4) ∷
   rw 13 (q27 c4) ∷
   rw 12 (q30 c4) ∷
   rw 11 (q27 c4) ∷
   rw 10 (q30 c4) ∷
   rw 9 (q27 c4) ∷
   rw 8 (q27 c4) ∷
   rw 7 (q27 c4) ∷
   rw 6 (q27 c4) ∷
   rw 5 (q27 c4) ∷
   rw 4 (q27 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 31 (q16 c4) ∷
   rw 30 (q31 c4) ∷
   rw 29 (q31 c4) ∷
   rw⁻ 28 (q18 c4) ∷
   rw 27 (q32 c4) ∷
   rw 26 (q32 c4) ∷
   rw 25 (q32 c4) ∷
   rw 24 (q31 c4) ∷
   rw⁻ 23 (q33 c4) ∷
   rw 22 (q31 c4) ∷
   rw⁻ 21 (q33 c4) ∷
   rw 20 (q31 c4) ∷
   rw 19 (q32 c4) ∷
   rw⁻ 18 (q18 c4) ∷
   rw 17 (q32 c4) ∷
   rw 16 (q32 c4) ∷
   rw 15 (q32 c4) ∷
   rw 14 (q31 c4) ∷
   rw⁻ 13 (q33 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 11 (q33 c4) ∷
   rw 10 (q31 c4) ∷
   rw 9 (q31 c4) ∷
   rw 8 (q31 c4) ∷
   rw 7 (q31 c4) ∷
   rw 6 (q31 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q31 c4) ∷
   rw 5 (q34 c4) ∷
   rw 4 (q16 c4) ∷
   rw 3 (q26 c4) ∷
   rw 2 (q21 c4) ∷
   rw 1 (q16 c4) ∷
   rw 0 (q15 c4) ∷ []) Eq.refl
