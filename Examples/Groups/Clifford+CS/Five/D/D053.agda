{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD053 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D053 (Sᴰ : SD053) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-CS14-sw0-L)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R ; lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R ; lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R ; lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-I-I-at0213243140 : Ws → St 1422
  lem-F4-I-I-at0213243140 = pickᴰ 0 Sᴰ
  lem-F4-I-K3-at0213243140 : Ws → St 1407
  lem-F4-I-K3-at0213243140 = pickᴰ 1 Sᴰ
  lem-F4-I-S2-at0213243140 : Ws → St 1408
  lem-F4-I-S2-at0213243140 = pickᴰ 2 Sᴰ
  lem-F4-K3-I-at0213243140 : Ws → St 1409
  lem-F4-K3-I-at0213243140 = pickᴰ 3 Sᴰ
  lem-F4-K3-K3-at0213243140 : Ws → St 1410
  lem-F4-K3-K3-at0213243140 = pickᴰ 4 Sᴰ
  lem-F4-K3-S2-at0213243140 : Ws → St 1411
  lem-F4-K3-S2-at0213243140 = pickᴰ 5 Sᴰ
  lem-F4-S2-I-at0213243140 : Ws → St 1412
  lem-F4-S2-I-at0213243140 = pickᴰ 6 Sᴰ
  lem-F4-S2-K3-at0213243140 : Ws → St 1413
  lem-F4-S2-K3-at0213243140 = pickᴰ 7 Sᴰ
  lem-F4-S2-S2-at0213243140 : Ws → St 1414
  lem-F4-S2-S2-at0213243140 = pickᴰ 8 Sᴰ
  lem-F4-I-CS2-at0213243140 : Ws → St 1415
  lem-F4-I-CS2-at0213243140 = pickᴰ 9 Sᴰ
  lem-F4-S2-CS2-at0213243140 : Ws → St 1416
  lem-F4-S2-CS2-at0213243140 = pickᴰ 10 Sᴰ
  lem-F4-CS2-CS2-at0213243140 : Ws → St 1417
  lem-F4-CS2-CS2-at0213243140 = pickᴰ 11 Sᴰ
  lem-F4-CS2-I-at0213243140 : Ws → St 1418
  lem-F4-CS2-I-at0213243140 = pickᴰ 12 Sᴰ
  lem-F4-CS2-S2-at0213243140 : Ws → St 1419
  lem-F4-CS2-S2-at0213243140 = pickᴰ 13 Sᴰ
  lem-F5-23 : Ws → St 1377
  lem-F5-23 = pickᴰ 14 Sᴰ
  lem-F4-CS2-K3-at0213243140 : Ws → St 1420
  lem-F4-CS2-K3-at0213243140 = pickᴰ 15 Sᴰ
  lem-F4-K3-CS2-at0213243140 : Ws → St 1421
  lem-F4-K3-CS2-at0213243140 = pickᴰ 16 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 6 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 1457 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw23 ∷ Sb0-4-31-2 ∷ []) (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4))
  q4 : Ws → Eqn
  q4 c4 = wlE 3 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw01 ∷ Sb0-4-21-3 ∷ []) (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4))
  q7 : Ws → Eqn
  q7 c4 = wlE 18 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = wlE 1458 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw12 ∷ Sb1-4-20-3 ∷ []) (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4))
  q10 : Ws → Eqn
  q10 c4 = wlE 1459 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw01 ∷ Sb2-4-10-3 ∷ []) (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4))
  q12 : Ws → Eqn
  q12 c4 = sE 1420 (lem-F4-CS2-K3-at0213243140 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1417 (lem-F4-CS2-CS2-at0213243140 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1419 (lem-F4-CS2-S2-at0213243140 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1418 (lem-F4-CS2-I-at0213243140 c4)
  q16 : Ws → Eqn
  q16 c4 = wlE 1460 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1421 (lem-F4-K3-CS2-at0213243140 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1410 (lem-F4-K3-K3-at0213243140 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1411 (lem-F4-K3-S2-at0213243140 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1409 (lem-F4-K3-I-at0213243140 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS14 ∷ Sw01 ∷ []) (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CS04 ∷ Sw12 ∷ []) (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4))
  q24 : Ws → Eqn
  q24 c4 = wlE 17 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = wlE 13 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 4 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = wlE 1455 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1377 (lem-F5-23 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q30 : Ws → Eqn
  q30 c4 = eqn (Sw23 ∷ Sb0-2-43-1 ∷ []) (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4))
  q31 : Ws → Eqn
  q31 c4 = wlE 1456 (lit c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw34 ∷ Sb0-3-42-1 ∷ []) (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw12 ∷ X3 ∷ []) (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X))
  q34 : Ws → Eqn
  q34 c4 = eqn (Sw12 ∷ Sb0-4-32-1 ∷ []) (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4))
  q35 : Ws → Eqn
  q35 c4 = wpE 1306 c4
  q36 : Ws → Eqn
  q36 c4 = sE 1416 (lem-F4-S2-CS2-at0213243140 c4)
  q37 : Ws → Eqn
  q37 c4 = sE 1413 (lem-F4-S2-K3-at0213243140 c4)
  q38 : Ws → Eqn
  q38 c4 = sE 1414 (lem-F4-S2-S2-at0213243140 c4)
  q39 : Ws → Eqn
  q39 c4 = sE 1412 (lem-F4-S2-I-at0213243140 c4)
  q40 : Ws → Eqn
  q40 c4 = wlE 1461 (lit c4)
  q41 : Ws → Eqn
  q41 c4 = sE 1408 (lem-F4-I-S2-at0213243140 c4)
  q42 : Ws → Eqn
  q42 c4 = sE 1415 (lem-F4-I-CS2-at0213243140 c4)
  q43 : Ws → Eqn
  q43 c4 = sE 1407 (lem-F4-I-K3-at0213243140 c4)
  q44 : Ws → Eqn
  q44 c4 = sE 1422 (lem-F4-I-I-at0213243140 c4)

-- deb-CKS-split-a @0213243140 part1: 226 steps
lem-deb-CKS-split-a-at0213243140-part1 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ []) ⟫ʷ
lem-deb-CKS-split-a-at0213243140-part1 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ [])
  (rw 68 (q1 c4) ∷
   rw 63 (q2 c4) ∷
   rw 64 (q3 c4) ∷
   rw 65 (q2 c4) ∷
   rw 66 (q3 c4) ∷
   rw 67 (q4 c4) ∷
   rw 62 (q5 c4) ∷
   rw 63 (q6 c4) ∷
   rw 64 (q5 c4) ∷
   rw 65 (q6 c4) ∷
   rw 66 (q7 c4) ∷
   rw 61 (q8 c4) ∷
   rw 62 (q9 c4) ∷
   rw 63 (q8 c4) ∷
   rw 64 (q9 c4) ∷
   rw 65 (q1 c4) ∷
   rw 60 (q10 c4) ∷
   rw 61 (q11 c4) ∷
   rw 62 (q10 c4) ∷
   rw 63 (q11 c4) ∷
   rw 64 (q7 c4) ∷
   rw⁻ 59 (q12 c4) ∷
   rw⁻ 58 (q13 c4) ∷
   rw⁻ 57 (q13 c4) ∷
   rw⁻ 56 (q13 c4) ∷
   rw⁻ 55 (q13 c4) ∷
   rw⁻ 54 (q14 c4) ∷
   rw⁻ 53 (q15 c4) ∷
   rw⁻ 52 (q14 c4) ∷
   rw⁻ 51 (q14 c4) ∷
   rw⁻ 50 (q14 c4) ∷
   rw⁻ 49 (q13 c4) ∷
   rw⁻ 48 (q12 c4) ∷
   rw⁻ 47 (q13 c4) ∷
   rw⁻ 46 (q12 c4) ∷
   rw⁻ 45 (q13 c4) ∷
   rw 64 (q16 c4) ∷
   rw⁻ 63 (q17 c4) ∷
   rw⁻ 62 (q18 c4) ∷
   rw⁻ 61 (q17 c4) ∷
   rw⁻ 60 (q17 c4) ∷
   rw⁻ 59 (q17 c4) ∷
   rw⁻ 58 (q17 c4) ∷
   rw⁻ 57 (q19 c4) ∷
   rw⁻ 56 (q20 c4) ∷
   rw⁻ 55 (q19 c4) ∷
   rw⁻ 54 (q19 c4) ∷
   rw⁻ 53 (q19 c4) ∷
   rw⁻ 52 (q17 c4) ∷
   rw⁻ 51 (q18 c4) ∷
   rw⁻ 50 (q17 c4) ∷
   rw⁻ 49 (q18 c4) ∷
   rw⁻ 48 (q17 c4) ∷
   rw⁻ 69 (q7 c4) ∷
   rw 68 (q21 c4) ∷
   rw⁻ 70 (q1 c4) ∷
   rw 69 (q22 c4) ∷
   rw⁻ 71 (q7 c4) ∷
   rw 70 (q23 c4) ∷
   rw⁻ 72 (q4 c4) ∷
   rw 71 (q24 c4) ∷
   rw⁻ 73 (q1 c4) ∷
   rw 72 (q25 c4) ∷
   rw⁻ 74 (q26 c4) ∷
   re 73 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 75 (q26 c4) ∷
   rw⁻ 75 (q4 c4) ∷
   rw 74 (q27 c4) ∷
   rw⁻ 75 (q28 c4) ∷
   rw 74 (q29 c4) ∷
   rw 75 (q30 c4) ∷
   rw 76 (q29 c4) ∷
   rw 77 (q30 c4) ∷
   rw 78 (q4 c4) ∷
   rw 73 (q31 c4) ∷
   rw 74 (q32 c4) ∷
   rw 75 (q31 c4) ∷
   rw 76 (q32 c4) ∷
   rw 77 (q26 c4) ∷
   rw 72 (q33 c4) ∷
   rw 73 (q34 c4) ∷
   rw 74 (q33 c4) ∷
   rw 75 (q34 c4) ∷
   rw 76 (q1 c4) ∷
   rw 71 (q2 c4) ∷
   rw 72 (q3 c4) ∷
   rw 73 (q2 c4) ∷
   rw 74 (q3 c4) ∷
   rw 75 (q4 c4) ∷
   rw 70 (q5 c4) ∷
   rw 71 (q6 c4) ∷
   rw 72 (q5 c4) ∷
   rw 73 (q6 c4) ∷
   rw 74 (q7 c4) ∷
   rw 69 (q8 c4) ∷
   rw 70 (q9 c4) ∷
   rw 71 (q8 c4) ∷
   rw 72 (q9 c4) ∷
   rw 73 (q1 c4) ∷
   rw 68 (q10 c4) ∷
   rw 69 (q11 c4) ∷
   rw 70 (q10 c4) ∷
   rw 71 (q11 c4) ∷
   rw 72 (q7 c4) ∷
   rw⁻ 67 (q12 c4) ∷
   rw⁻ 66 (q13 c4) ∷
   rw⁻ 65 (q12 c4) ∷
   rw⁻ 64 (q13 c4) ∷
   rw⁻ 63 (q13 c4) ∷
   rw⁻ 62 (q13 c4) ∷
   rw⁻ 61 (q13 c4) ∷
   rw⁻ 60 (q14 c4) ∷
   rw⁻ 59 (q15 c4) ∷
   rw⁻ 58 (q14 c4) ∷
   rw⁻ 57 (q14 c4) ∷
   rw⁻ 56 (q14 c4) ∷
   rw⁻ 55 (q13 c4) ∷
   rw⁻ 54 (q12 c4) ∷
   rw⁻ 53 (q13 c4) ∷
   rw⁻ 52 (q12 c4) ∷
   rw⁻ 51 (q13 c4) ∷
   rw 72 (q35 c4) ∷
   rw⁻ 71 (q36 c4) ∷
   rw⁻ 70 (q37 c4) ∷
   rw⁻ 69 (q36 c4) ∷
   rw⁻ 68 (q37 c4) ∷
   rw⁻ 67 (q36 c4) ∷
   rw⁻ 66 (q36 c4) ∷
   rw⁻ 65 (q36 c4) ∷
   rw⁻ 64 (q36 c4) ∷
   rw⁻ 63 (q38 c4) ∷
   rw⁻ 62 (q39 c4) ∷
   rw⁻ 61 (q38 c4) ∷
   rw⁻ 60 (q38 c4) ∷
   rw⁻ 59 (q38 c4) ∷
   rw⁻ 58 (q36 c4) ∷
   rw⁻ 57 (q37 c4) ∷
   rw⁻ 56 (q36 c4) ∷
   rw⁻ 55 (q37 c4) ∷
   rw⁻ 54 (q36 c4) ∷
   rw 76 (q35 c4) ∷
   rw⁻ 75 (q38 c4) ∷
   rw⁻ 74 (q36 c4) ∷
   rw⁻ 73 (q37 c4) ∷
   rw⁻ 72 (q36 c4) ∷
   rw⁻ 71 (q37 c4) ∷
   rw⁻ 70 (q36 c4) ∷
   rw⁻ 69 (q36 c4) ∷
   rw⁻ 68 (q36 c4) ∷
   rw⁻ 67 (q36 c4) ∷
   rw⁻ 66 (q38 c4) ∷
   rw⁻ 65 (q39 c4) ∷
   rw⁻ 64 (q38 c4) ∷
   rw⁻ 63 (q38 c4) ∷
   rw⁻ 62 (q38 c4) ∷
   rw⁻ 61 (q36 c4) ∷
   rw⁻ 60 (q37 c4) ∷
   rw⁻ 59 (q36 c4) ∷
   rw⁻ 58 (q37 c4) ∷
   rw⁻ 57 (q36 c4) ∷
   rw 80 (q35 c4) ∷
   rw⁻ 79 (q38 c4) ∷
   rw⁻ 78 (q38 c4) ∷
   rw⁻ 77 (q36 c4) ∷
   rw⁻ 76 (q37 c4) ∷
   rw⁻ 75 (q36 c4) ∷
   rw⁻ 74 (q37 c4) ∷
   rw⁻ 73 (q36 c4) ∷
   rw⁻ 72 (q36 c4) ∷
   rw⁻ 71 (q36 c4) ∷
   rw⁻ 70 (q36 c4) ∷
   rw⁻ 69 (q38 c4) ∷
   rw⁻ 68 (q39 c4) ∷
   rw⁻ 67 (q38 c4) ∷
   rw⁻ 66 (q38 c4) ∷
   rw⁻ 65 (q38 c4) ∷
   rw⁻ 64 (q36 c4) ∷
   rw⁻ 63 (q37 c4) ∷
   rw⁻ 62 (q36 c4) ∷
   rw⁻ 61 (q37 c4) ∷
   rw⁻ 60 (q36 c4) ∷
   rw⁻ 84 (q40 c4) ∷
   rw⁻ 83 (q41 c4) ∷
   rw⁻ 82 (q41 c4) ∷
   rw⁻ 81 (q41 c4) ∷
   rw⁻ 80 (q42 c4) ∷
   rw⁻ 79 (q43 c4) ∷
   rw⁻ 78 (q42 c4) ∷
   rw⁻ 77 (q43 c4) ∷
   rw⁻ 76 (q42 c4) ∷
   rw⁻ 75 (q42 c4) ∷
   rw⁻ 74 (q42 c4) ∷
   rw⁻ 73 (q42 c4) ∷
   rw⁻ 72 (q41 c4) ∷
   rw⁻ 71 (q44 c4) ∷
   rw⁻ 70 (q41 c4) ∷
   rw⁻ 69 (q41 c4) ∷
   rw⁻ 68 (q41 c4) ∷
   rw⁻ 67 (q42 c4) ∷
   rw⁻ 66 (q43 c4) ∷
   rw⁻ 65 (q42 c4) ∷
   rw⁻ 64 (q43 c4) ∷
   rw⁻ 63 (q42 c4) ∷
   rw 88 (q35 c4) ∷
   rw⁻ 87 (q39 c4) ∷
   rw⁻ 86 (q38 c4) ∷
   rw⁻ 85 (q38 c4) ∷
   rw⁻ 84 (q38 c4) ∷
   rw⁻ 83 (q36 c4) ∷
   rw⁻ 82 (q37 c4) ∷
   rw⁻ 81 (q36 c4) ∷
   rw⁻ 80 (q37 c4) ∷
   rw⁻ 79 (q36 c4) ∷
   rw⁻ 78 (q36 c4) ∷
   rw⁻ 77 (q36 c4) ∷
   rw⁻ 76 (q36 c4) ∷
   rw⁻ 75 (q38 c4) ∷
   rw⁻ 74 (q39 c4) ∷
   rw⁻ 73 (q38 c4) ∷
   rw⁻ 72 (q38 c4) ∷
   rw⁻ 71 (q38 c4) ∷
   rw⁻ 70 (q36 c4) ∷
   rw⁻ 69 (q37 c4) ∷
   rw⁻ 68 (q36 c4) ∷
   rw⁻ 67 (q37 c4) ∷
   rw⁻ 66 (q36 c4) ∷ []) Eq.refl
