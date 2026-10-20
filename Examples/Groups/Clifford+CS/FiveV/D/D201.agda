{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D201 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.FiveV.TR2 using (lem-TR2-e425e28a)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3 ; lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2)
open import Examples.Groups.Clifford+CS.FiveV.D.D003 using (lem-F4-I-K3-at0213243140 ; lem-F4-K3-K3-at0213243140 ; lem-F4-S2-K3-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1)
open import Examples.Groups.Clifford+CS.FiveV.D.D022 using (lem-F4-I-CS2-at0213243140 ; lem-F4-S2-CS2-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.D023 using (lem-F4-CS2-CS2-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.D025 using (lem-F2-K1-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D026 using (lem-F1-comm-CS-S0at2 ; lem-F2-K3-CS0 ; lem-F2-K3-CS1)
open import Examples.Groups.Clifford+CS.FiveV.D.D027 using (lem-F1-comm-CS-S1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D032 using (lem-F4-CS2-K3-at0213243140 ; lem-F4-K3-CS2-at0213243140 ; lem-S2-SBOX⟨0·2·43·1⟩-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.D038 using (lem-F1-order-CSat2 ; lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D067 using (lem-F1-X-CS0at2 ; lem-F2-CS0-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D068 using (lem-F1-X-CS1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D150 using (lem-deb-CKS-eps-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-push-CS04-sw0-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-push-CS14-sw0-R)
open import Examples.Groups.Clifford+CS.FiveV.D.R009 using (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R ; lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R010 using (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R ; lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L ; lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L ; lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R)
open import Examples.Groups.Clifford+CS.FiveV.D.R011 using (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R ; lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R ; lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L ; lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L ; lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L ; lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb2-4-01-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wl 1424 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ []) (wl 1425 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sb2-4-10-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) (wl 1426 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sb1-4-20-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (c₂ (Swap) (S))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q13 : Ws → Eqn
  q13 c4 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wl 1427 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sb0-4-21-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (S2 ∷ Sw23 ∷ []) (Sw23 ∷ S3 ∷ []) (wl 1428 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl 11 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sb0-4-31-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q21 : Ws → Eqn
  q21 c4 = eqn (CK31 ∷ Sw12 ∷ []) (Sw12 ∷ CK32 ∷ []) (wl 95 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl 4 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sb0-4-32-1 ∷ Sw34 ∷ []) (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (S3 ∷ Sw34 ∷ []) (Sw34 ∷ S4 ∷ []) (wl 1429 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ []) (wl 129 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sb0-3-42-1 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q28 : Ws → Eqn
  q28 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl 8 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl 90 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ []) (lem-TR2-e425e28a c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Sw23 ∷ Sb0-2-43-1 ∷ []) (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw34 ∷ Sb0-3-42-1 ∷ []) (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw12 ∷ Sb0-4-32-1 ∷ []) (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl 46 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw23 ∷ Sb0-4-31-2 ∷ []) (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (Sw01 ∷ Sb0-4-21-3 ∷ []) (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl 24 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Sw12 ∷ Sb1-4-20-3 ∷ []) (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (Sw01 ∷ Sb2-4-10-3 ∷ []) (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wl 1462 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ []) (CCZ014 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩-at0213243140 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) [] (lem-deb-CKS-eps-at0213243140 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-CS2-at0213243140 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-CS2-at0213243140 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0213243140 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-CS2-at0213243140 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-K3-at0213243140 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-K3-at0213243140 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-K3-at0213243140 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-K3-at0213243140 c4)

-- deb-CKS @0213243140 part0: 500 steps
lem-deb-CKS-at0213243140-part0 : Ws → ⟪ (Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) ⟫ʷ
lem-deb-CKS-at0213243140-part0 c4 = derive (Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ []) (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ [])
  (rw⁻ 10 (q1 c4) ∷
   rw 9 (q2 c4) ∷
   rw 8 (q3 c4) ∷
   rw 7 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 5 (q4 c4) ∷
   rw 4 (q2 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw 10 (q7 c4) ∷
   rw 9 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q9 c4) ∷
   rw 6 (q9 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 5 3 (CK20 ∷ []) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   re 3 3 (CK20 ∷ []) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw 11 (q10 c4) ∷
   rw⁻ 10 (q11 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw 6 (q10 c4) ∷
   rw 5 (q13 c4) ∷
   rw 4 (q10 c4) ∷
   rw 3 (q13 c4) ∷
   rw 2 (q10 c4) ∷
   rw⁻ 13 (q14 c4) ∷
   rw 12 (q15 c4) ∷
   rw 11 (q16 c4) ∷
   rw 10 (q17 c4) ∷
   rw 9 (q17 c4) ∷
   rw 8 (q17 c4) ∷
   rw 7 (q15 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   re 7 3 (CK31 ∷ []) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 14 (q6 c4) ∷
   rw 13 (q18 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw⁻ 11 (q20 c4) ∷
   rw⁻ 10 (q20 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   rw 8 (q18 c4) ∷
   rw 7 (q21 c4) ∷
   rw 6 (q18 c4) ∷
   rw 5 (q21 c4) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 15 (q22 c4) ∷
   rw 14 (q23 c4) ∷
   rw 13 (q24 c4) ∷
   rw 12 (q25 c4) ∷
   rw 11 (q25 c4) ∷
   rw 10 (q25 c4) ∷
   rw 9 (q23 c4) ∷
   rw⁻ 8 (q22 c4) ∷
   re 9 3 (CK42 ∷ []) ∷
   rw 7 (q23 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   re 7 3 (CK42 ∷ []) ∷
   rw 5 (q23 c4) ∷
   rw⁻ 16 (q14 c4) ∷
   rw 15 (q26 c4) ∷
   rw⁻ 14 (q27 c4) ∷
   rw 13 (q28 c4) ∷
   rw 12 (q28 c4) ∷
   rw 11 (q28 c4) ∷
   rw 10 (q26 c4) ∷
   rw 9 (q29 c4) ∷
   rw 8 (q26 c4) ∷
   rw 7 (q29 c4) ∷
   rw 6 (q26 c4) ∷
   rw 7 (q30 c4) ∷
   rw 6 (q31 c4) ∷
   rw 7 (q31 c4) ∷
   rw 8 (q31 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 10 (q31 c4) ∷
   rw⁻ 11 (q29 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 13 (q28 c4) ∷
   rw⁻ 14 (q28 c4) ∷
   rw⁻ 15 (q28 c4) ∷
   rw 16 (q27 c4) ∷
   rw⁻ 17 (q28 c4) ∷
   rw 18 (q31 c4) ∷
   rw 19 (q31 c4) ∷
   rw 20 (q31 c4) ∷
   rw 21 (q31 c4) ∷
   rw⁻ 22 (q29 c4) ∷
   rw 23 (q31 c4) ∷
   rw⁻ 24 (q29 c4) ∷
   rw 25 (q31 c4) ∷
   rw⁻ 26 (q28 c4) ∷
   rw⁻ 27 (q28 c4) ∷
   rw⁻ 28 (q28 c4) ∷
   rw 29 (q27 c4) ∷
   rw⁻ 30 (q28 c4) ∷
   rw⁻ 31 (q17 c4) ∷
   rw⁻ 32 (q17 c4) ∷
   rw⁻ 33 (q17 c4) ∷
   rw 34 (q31 c4) ∷
   rw⁻ 35 (q29 c4) ∷
   rw 36 (q31 c4) ∷
   rw⁻ 37 (q29 c4) ∷
   rw 38 (q31 c4) ∷
   rw⁻ 39 (q28 c4) ∷
   rw⁻ 40 (q28 c4) ∷
   rw⁻ 41 (q28 c4) ∷
   rw 42 (q27 c4) ∷
   rw 43 (q31 c4) ∷
   rw 44 (q31 c4) ∷
   rw⁻ 45 (q29 c4) ∷
   rw 46 (q31 c4) ∷
   rw⁻ 47 (q29 c4) ∷
   rw 48 (q31 c4) ∷
   rw⁻ 49 (q28 c4) ∷
   rw⁻ 50 (q28 c4) ∷
   rw⁻ 51 (q28 c4) ∷
   rw 52 (q27 c4) ∷
   rw⁻ 53 (q17 c4) ∷
   rw 54 (q14 c4) ∷
   rw 5 (q32 c4) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q32 c4) ∷
   re 9 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 8 (q22 c4) ∷
   rw 9 (q32 c4) ∷
   re 11 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 10 (q22 c4) ∷
   rw 11 (q32 c4) ∷
   rw⁻ 12 (q25 c4) ∷
   rw⁻ 13 (q25 c4) ∷
   rw⁻ 14 (q25 c4) ∷
   rw⁻ 15 (q24 c4) ∷
   rw⁻ 16 (q25 c4) ∷
   rw 17 (q32 c4) ∷
   rw 18 (q32 c4) ∷
   rw 19 (q32 c4) ∷
   rw 20 (q32 c4) ∷
   re 22 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 21 (q22 c4) ∷
   rw 22 (q32 c4) ∷
   re 24 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 23 (q22 c4) ∷
   rw 24 (q32 c4) ∷
   rw⁻ 25 (q25 c4) ∷
   rw⁻ 26 (q25 c4) ∷
   rw⁻ 27 (q25 c4) ∷
   rw⁻ 28 (q24 c4) ∷
   rw⁻ 29 (q25 c4) ∷
   re 31 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 30 (q22 c4) ∷
   re 32 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 31 (q22 c4) ∷
   re 33 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 32 (q22 c4) ∷
   rw 33 (q32 c4) ∷
   re 35 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 34 (q22 c4) ∷
   rw 35 (q32 c4) ∷
   re 37 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 36 (q22 c4) ∷
   rw 37 (q32 c4) ∷
   rw⁻ 38 (q25 c4) ∷
   rw⁻ 39 (q25 c4) ∷
   rw⁻ 40 (q25 c4) ∷
   rw⁻ 41 (q24 c4) ∷
   rw 42 (q32 c4) ∷
   rw 43 (q32 c4) ∷
   re 45 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 44 (q22 c4) ∷
   rw 45 (q32 c4) ∷
   re 47 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 46 (q22 c4) ∷
   rw 47 (q32 c4) ∷
   rw⁻ 48 (q25 c4) ∷
   rw⁻ 49 (q25 c4) ∷
   rw⁻ 50 (q25 c4) ∷
   rw⁻ 51 (q24 c4) ∷
   re 53 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 52 (q22 c4) ∷
   rw 53 (q22 c4) ∷
   rw 4 (q33 c4) ∷
   rw 5 (q33 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw 10 (q33 c4) ∷
   rw 11 (q20 c4) ∷
   rw 12 (q20 c4) ∷
   rw 13 (q20 c4) ∷
   rw 14 (q19 c4) ∷
   rw 15 (q20 c4) ∷
   rw 16 (q33 c4) ∷
   rw 17 (q33 c4) ∷
   rw 18 (q33 c4) ∷
   rw 19 (q33 c4) ∷
   rw⁻ 20 (q21 c4) ∷
   rw 21 (q33 c4) ∷
   rw⁻ 22 (q21 c4) ∷
   rw 23 (q33 c4) ∷
   rw 24 (q20 c4) ∷
   rw 25 (q20 c4) ∷
   rw 26 (q20 c4) ∷
   rw 27 (q19 c4) ∷
   rw 28 (q20 c4) ∷
   rw⁻ 29 (q34 c4) ∷
   rw⁻ 30 (q34 c4) ∷
   rw⁻ 31 (q34 c4) ∷
   rw 32 (q33 c4) ∷
   rw⁻ 33 (q21 c4) ∷
   rw 34 (q33 c4) ∷
   rw⁻ 35 (q21 c4) ∷
   rw 36 (q33 c4) ∷
   rw 37 (q20 c4) ∷
   rw 38 (q20 c4) ∷
   rw 39 (q20 c4) ∷
   rw 40 (q19 c4) ∷
   rw 41 (q33 c4) ∷
   rw 42 (q33 c4) ∷
   rw⁻ 43 (q21 c4) ∷
   rw 44 (q33 c4) ∷
   rw⁻ 45 (q21 c4) ∷
   rw 46 (q33 c4) ∷
   rw 47 (q20 c4) ∷
   rw 48 (q20 c4) ∷
   rw 49 (q20 c4) ∷
   rw 50 (q19 c4) ∷
   rw⁻ 51 (q34 c4) ∷
   rw 52 (q6 c4) ∷
   rw 3 (q35 c4) ∷
   rw 4 (q35 c4) ∷
   rw 5 (q35 c4) ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 6 (q14 c4) ∷
   rw 7 (q35 c4) ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 (q14 c4) ∷
   rw 9 (q35 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   rw⁻ 12 (q17 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw⁻ 14 (q17 c4) ∷
   rw 15 (q35 c4) ∷
   rw 16 (q35 c4) ∷
   rw 17 (q35 c4) ∷
   rw 18 (q35 c4) ∷
   re 20 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 19 (q14 c4) ∷
   rw 20 (q35 c4) ∷
   re 22 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q35 c4) ∷
   rw⁻ 23 (q17 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw⁻ 25 (q17 c4) ∷
   rw⁻ 26 (q16 c4) ∷
   rw⁻ 27 (q17 c4) ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 (q14 c4) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 (q14 c4) ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 (q14 c4) ∷
   rw 31 (q35 c4) ∷
   re 33 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 32 (q14 c4) ∷
   rw 33 (q35 c4) ∷
   re 35 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 34 (q14 c4) ∷
   rw 35 (q35 c4) ∷
   rw⁻ 36 (q17 c4) ∷
   rw⁻ 37 (q17 c4) ∷
   rw⁻ 38 (q17 c4) ∷
   rw⁻ 39 (q16 c4) ∷
   rw 40 (q35 c4) ∷
   rw 41 (q35 c4) ∷
   re 43 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 42 (q14 c4) ∷
   rw 43 (q35 c4) ∷
   re 45 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 44 (q14 c4) ∷
   rw 45 (q35 c4) ∷
   rw⁻ 46 (q17 c4) ∷
   rw⁻ 47 (q17 c4) ∷
   rw⁻ 48 (q17 c4) ∷
   rw⁻ 49 (q16 c4) ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 (q14 c4) ∷
   rw 51 (q14 c4) ∷
   rw 2 (q36 c4) ∷
   rw 3 (q36 c4) ∷
   rw 4 (q36 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q36 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 8 (q36 c4) ∷
   rw 9 (q12 c4) ∷
   rw 10 (q12 c4) ∷
   rw 11 (q12 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q12 c4) ∷
   rw 14 (q36 c4) ∷
   rw 15 (q36 c4) ∷
   rw 16 (q36 c4) ∷
   rw 17 (q36 c4) ∷
   rw⁻ 18 (q13 c4) ∷
   rw 19 (q36 c4) ∷
   rw⁻ 20 (q13 c4) ∷
   rw 21 (q36 c4) ∷
   rw 22 (q12 c4) ∷
   rw 23 (q12 c4) ∷
   rw 24 (q12 c4) ∷
   rw 25 (q11 c4) ∷
   rw 26 (q12 c4) ∷
   rw⁻ 27 (q37 c4) ∷
   rw⁻ 28 (q37 c4) ∷
   rw⁻ 29 (q37 c4) ∷
   rw 30 (q36 c4) ∷
   rw⁻ 31 (q13 c4) ∷
   rw 32 (q36 c4) ∷
   rw⁻ 33 (q13 c4) ∷
   rw 34 (q36 c4) ∷
   rw 35 (q12 c4) ∷
   rw 36 (q12 c4) ∷
   rw 37 (q12 c4) ∷
   rw 38 (q11 c4) ∷
   rw 39 (q36 c4) ∷
   rw 40 (q36 c4) ∷
   rw⁻ 41 (q13 c4) ∷
   rw 42 (q36 c4) ∷
   rw⁻ 43 (q13 c4) ∷
   rw 44 (q36 c4) ∷
   rw 45 (q12 c4) ∷
   rw 46 (q12 c4) ∷
   rw 47 (q12 c4) ∷
   rw 48 (q11 c4) ∷
   rw⁻ 49 (q37 c4) ∷
   rw 50 (q1 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q38 c4) ∷
   rw 3 (q38 c4) ∷
   re 5 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw 5 (q38 c4) ∷
   re 7 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q38 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw⁻ 11 (q8 c4) ∷
   rw⁻ 12 (q9 c4) ∷
   rw 13 (q38 c4) ∷
   rw 14 (q38 c4) ∷
   rw 15 (q38 c4) ∷
   rw 16 (q38 c4) ∷
   re 18 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 17 (q6 c4) ∷
   rw 18 (q38 c4) ∷
   re 20 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 19 (q6 c4) ∷
   rw 20 (q38 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw⁻ 24 (q8 c4) ∷
   rw⁻ 25 (q9 c4) ∷
   re 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 (q6 c4) ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 27 (q6 c4) ∷
   re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 28 (q6 c4) ∷
   rw 29 (q38 c4) ∷
   re 31 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 30 (q6 c4) ∷
   rw 31 (q38 c4) ∷
   re 33 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 32 (q6 c4) ∷
   rw 33 (q38 c4) ∷
   rw⁻ 34 (q9 c4) ∷
   rw⁻ 35 (q9 c4) ∷
   rw⁻ 36 (q9 c4) ∷
   rw⁻ 37 (q8 c4) ∷
   rw 38 (q38 c4) ∷
   rw 39 (q38 c4) ∷
   re 41 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 40 (q6 c4) ∷
   rw 41 (q38 c4) ∷
   re 43 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 42 (q6 c4) ∷
   rw 43 (q38 c4) ∷
   rw⁻ 44 (q9 c4) ∷
   rw⁻ 45 (q9 c4) ∷
   rw⁻ 46 (q9 c4) ∷
   rw⁻ 47 (q8 c4) ∷
   re 49 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 48 (q6 c4) ∷
   rw 49 (q6 c4) ∷
   rw 0 (q39 c4) ∷
   rw 1 (q39 c4) ∷
   rw 2 (q39 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 6 (q39 c4) ∷
   rw 7 (q40 c4) ∷
   rw 8 (q40 c4) ∷
   rw 9 (q40 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw 11 (q40 c4) ∷
   rw 12 (q39 c4) ∷
   rw 13 (q39 c4) ∷
   rw 14 (q39 c4) ∷
   rw 15 (q39 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw 17 (q39 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw 19 (q39 c4) ∷
   rw 20 (q40 c4) ∷
   rw 21 (q40 c4) ∷
   rw 22 (q40 c4) ∷
   rw⁻ 23 (q3 c4) ∷
   rw 24 (q40 c4) ∷
   rw⁻ 25 (q41 c4) ∷
   rw⁻ 26 (q41 c4) ∷
   rw⁻ 27 (q41 c4) ∷
   rw 28 (q39 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw 30 (q39 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw 32 (q39 c4) ∷
   rw 33 (q40 c4) ∷
   rw 34 (q40 c4) ∷
   rw 35 (q40 c4) ∷
   rw⁻ 36 (q3 c4) ∷
   rw 37 (q39 c4) ∷
   rw 38 (q39 c4) ∷
   rw⁻ 39 (q5 c4) ∷
   rw 40 (q39 c4) ∷
   rw⁻ 41 (q5 c4) ∷
   rw 42 (q39 c4) ∷
   rw 43 (q40 c4) ∷
   rw 44 (q40 c4) ∷
   rw 45 (q40 c4) ∷
   rw⁻ 46 (q3 c4) ∷
   rw⁻ 47 (q41 c4) ∷
   rw 48 (q1 c4) ∷
   rw 0 (q42 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   rw 124 (q44 c4) ∷
   rw 121 (q45 c4) ∷
   rw 118 (q45 c4) ∷
   rw 115 (q45 c4) ∷
   rw 112 (q46 c4) ∷
   rw 109 (q47 c4) ∷
   rw 106 (q46 c4) ∷
   rw 103 (q47 c4) ∷
   rw 100 (q46 c4) ∷
   rw 97 (q46 c4) ∷
   rw 94 (q44 c4) ∷
   rw 91 (q45 c4) ∷
   rw 88 (q45 c4) ∷
   rw 85 (q45 c4) ∷
   rw 82 (q46 c4) ∷
   rw 79 (q47 c4) ∷
   rw 76 (q46 c4) ∷
   rw 73 (q47 c4) ∷
   rw 70 (q46 c4) ∷
   rw 125 (q48 c4) ∷
   rw 122 (q49 c4) ∷
   rw 119 (q49 c4) ∷
   rw 116 (q49 c4) ∷
   rw 113 (q50 c4) ∷
   rw 110 (q51 c4) ∷
   rw 107 (q50 c4) ∷
   rw 104 (q51 c4) ∷
   rw 101 (q50 c4) ∷
   rw 98 (q50 c4) ∷
   rw 95 (q48 c4) ∷
   rw 92 (q49 c4) ∷
   rw 89 (q49 c4) ∷
   rw 86 (q49 c4) ∷
   rw 83 (q50 c4) ∷
   rw 80 (q51 c4) ∷ []) Eq.refl
