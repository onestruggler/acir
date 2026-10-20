{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D216 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.FiveV.TR2 using (lem-TR2-78b381c2)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3 ; lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1)
open import Examples.Groups.Clifford+CS.FiveV.D.D025 using (lem-F2-K1-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D026 using (lem-F1-comm-CS-S0at2 ; lem-F2-K3-CS0 ; lem-F2-K3-CS1)
open import Examples.Groups.Clifford+CS.FiveV.D.D027 using (lem-F1-comm-CS-S1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D038 using (lem-F1-order-CSat2 ; lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D067 using (lem-F1-X-CS0at2 ; lem-F2-CS0-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D068 using (lem-F1-X-CS1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D207 using (lem-deb-CKS-at0213243140)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-push-CS04-sw0-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-push-CS14-sw0-R)
open import Examples.Groups.Clifford+CS.FiveV.D.R009 using (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R ; lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R010 using (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R ; lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L ; lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L ; lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R)
open import Examples.Groups.Clifford+CS.FiveV.D.R011 using (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R ; lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R ; lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L ; lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L ; lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L ; lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X0 ∷ X0 ∷ []) [] (wl 1423 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wl 1424 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sb2-4-01-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb2-4-10-3 ∷ []) (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ []) (wl 1425 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) (wl 1426 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sb2-4-10-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-4-20-3 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (c₂ (Swap) (S))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sb1-4-20-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-4-21-3 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wl 1427 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (S2 ∷ Sw23 ∷ []) (Sw23 ∷ S3 ∷ []) (wl 1428 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl 11 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sb0-4-21-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-4-31-2 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sb0-4-31-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-4-32-1 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CK31 ∷ Sw12 ∷ []) (Sw12 ∷ CK32 ∷ []) (wl 95 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl 4 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (S3 ∷ Sw34 ∷ []) (Sw34 ∷ S4 ∷ []) (wl 1429 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ []) (wl 129 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sb0-4-32-1 ∷ Sw34 ∷ []) (Sw34 ∷ Sb0-3-42-1 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q28 : Ws → Eqn
  q28 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl 8 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Sb0-3-42-1 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl 90 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (lem-TR2-78b381c2 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw23 ∷ Sb0-2-43-1 ∷ []) (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw34 ∷ Sb0-3-42-1 ∷ []) (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (Sw12 ∷ Sb0-4-32-1 ∷ []) (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw23 ∷ Sb0-4-31-2 ∷ []) (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (Sw01 ∷ Sb0-4-21-3 ∷ []) (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw12 ∷ Sb1-4-20-3 ∷ []) (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Sw01 ∷ Sb2-4-10-3 ∷ []) (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ []) (CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ []) (lem-deb-CKS-at0213243140 c4)

-- ckt-A-R: 191 steps
lem-ckt-A-R : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-ckt-A-R c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (rw 2 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   rw 9 (q3 c4) ∷
   rw 8 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 11 (q7 c4) ∷
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
   rw⁻ 12 (q2 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw 7 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw 5 (q13 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 13 (q15 c4) ∷
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
   rw⁻ 14 (q7 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw⁻ 11 (q20 c4) ∷
   rw⁻ 10 (q20 c4) ∷
   rw 9 (q21 c4) ∷
   rw 8 (q22 c4) ∷
   rw 7 (q21 c4) ∷
   rw 6 (q22 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 15 (q23 c4) ∷
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
   rw⁻ 16 (q15 c4) ∷
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
   rw 7 (q32 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   rw 11 (q32 c4) ∷
   rw⁻ 12 (q28 c4) ∷
   rw⁻ 13 (q28 c4) ∷
   rw⁻ 14 (q28 c4) ∷
   rw 15 (q27 c4) ∷
   rw 16 (q32 c4) ∷
   rw 17 (q32 c4) ∷
   rw 18 (q32 c4) ∷
   rw 19 (q32 c4) ∷
   rw 20 (q15 c4) ∷
   rw 6 (q33 c4) ∷
   re 8 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 7 (q23 c4) ∷
   rw 8 (q33 c4) ∷
   re 10 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 9 (q23 c4) ∷
   rw 10 (q33 c4) ∷
   rw⁻ 11 (q25 c4) ∷
   rw⁻ 12 (q25 c4) ∷
   rw⁻ 13 (q25 c4) ∷
   rw⁻ 14 (q24 c4) ∷
   rw 15 (q33 c4) ∷
   rw 16 (q33 c4) ∷
   rw 17 (q33 c4) ∷
   rw 18 (q33 c4) ∷
   rw 19 (q23 c4) ∷
   rw 5 (q34 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw 7 (q34 c4) ∷
   rw⁻ 8 (q22 c4) ∷
   rw 9 (q34 c4) ∷
   rw 10 (q20 c4) ∷
   rw 11 (q20 c4) ∷
   rw 12 (q20 c4) ∷
   rw 13 (q19 c4) ∷
   rw 14 (q34 c4) ∷
   rw 15 (q34 c4) ∷
   rw 16 (q34 c4) ∷
   rw 17 (q34 c4) ∷
   rw 18 (q7 c4) ∷
   rw 4 (q35 c4) ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 (q15 c4) ∷
   rw 6 (q35 c4) ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 (q15 c4) ∷
   rw 8 (q35 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw 13 (q35 c4) ∷
   rw 14 (q35 c4) ∷
   rw 15 (q35 c4) ∷
   rw 16 (q35 c4) ∷
   rw 17 (q15 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 5 (q36 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 7 (q36 c4) ∷
   rw 8 (q12 c4) ∷
   rw 9 (q12 c4) ∷
   rw 10 (q12 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q36 c4) ∷
   rw 13 (q36 c4) ∷
   rw 14 (q36 c4) ∷
   rw 15 (q36 c4) ∷
   rw 16 (q2 c4) ∷
   rw 2 (q37 c4) ∷
   re 4 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q37 c4) ∷
   re 6 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q37 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw 11 (q37 c4) ∷
   rw 12 (q37 c4) ∷
   rw 13 (q37 c4) ∷
   rw 14 (q37 c4) ∷
   rw 15 (q7 c4) ∷
   rw 1 (q38 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 3 (q38 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 5 (q38 c4) ∷
   rw 6 (q39 c4) ∷
   rw 7 (q39 c4) ∷
   rw 8 (q39 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   rw 10 (q38 c4) ∷
   rw 11 (q38 c4) ∷
   rw 12 (q38 c4) ∷
   rw 13 (q38 c4) ∷
   rw 14 (q2 c4) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 48 (q1 c4) ∷ []) Eq.refl
