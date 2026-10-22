{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD050 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D050 (Sᴰ : SD050) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-I-I : Ws → St 1183
  lem-F4-I-I = pickᴰ 0 Sᴰ
  lem-F4-I-K3 : Ws → St 1208
  lem-F4-I-K3 = pickᴰ 1 Sᴰ
  lem-F4-I-S2 : Ws → St 1382
  lem-F4-I-S2 = pickᴰ 2 Sᴰ
  lem-F4-K3-I : Ws → St 1405
  lem-F4-K3-I = pickᴰ 3 Sᴰ
  lem-F4-K3-K3 : Ws → St 1383
  lem-F4-K3-K3 = pickᴰ 4 Sᴰ
  lem-F4-K3-S2 : Ws → St 1406
  lem-F4-K3-S2 = pickᴰ 5 Sᴰ
  lem-F4-S2-I : Ws → St 1384
  lem-F4-S2-I = pickᴰ 6 Sᴰ
  lem-F4-S2-K3 : Ws → St 1385
  lem-F4-S2-K3 = pickᴰ 7 Sᴰ
  lem-F4-S2-S2 : Ws → St 1386
  lem-F4-S2-S2 = pickᴰ 8 Sᴰ
  lem-F4-CS2-I : Ws → St 1363
  lem-F4-CS2-I = pickᴰ 9 Sᴰ
  lem-F4-CS2-S2 : Ws → St 1393
  lem-F4-CS2-S2 = pickᴰ 10 Sᴰ
  lem-F4-I-CS2 : Ws → St 1230
  lem-F4-I-CS2 = pickᴰ 11 Sᴰ
  lem-F4-S2-CS2 : Ws → St 1394
  lem-F4-S2-CS2 = pickᴰ 12 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1368
  lem-F4-CS2-CS2 = pickᴰ 13 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1402
  lem-F4-CS2-K3 = pickᴰ 14 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1403
  lem-F4-K3-CS2 = pickᴰ 15 Sᴰ
  lem-F5-23 : Ws → St 1377
  lem-F5-23 = pickᴰ 16 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ []) (lem-F5-23 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (K3 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl 1419 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-CS2 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K3 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-K3 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (S2 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl 1418 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-CS2 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-K3 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S2 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl 1411 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K3 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-I c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-I c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-S2 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-I c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I c4)

-- deb-CKS-split-b: 190 steps
lem-deb-CKS-split-b : Ws → ⟪ (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) ⟫ʷ
lem-deb-CKS-split-b c4 = derive (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 12 (q2 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q10 c4) ∷
   rw⁻ 26 (q10 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 24 (q9 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw⁻ 26 (q13 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw⁻ 24 (q13 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 35 (q15 c4) ∷
   rw⁻ 34 (q16 c4) ∷
   rw⁻ 33 (q16 c4) ∷
   rw⁻ 32 (q16 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 27 (q5 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 39 (q5 c4) ∷
   rw⁻ 38 (q15 c4) ∷
   rw⁻ 37 (q16 c4) ∷
   rw⁻ 36 (q16 c4) ∷
   rw⁻ 35 (q16 c4) ∷
   rw⁻ 34 (q5 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw 44 (q2 c4) ∷
   rw⁻ 43 (q3 c4) ∷
   rw⁻ 42 (q3 c4) ∷
   rw⁻ 41 (q17 c4) ∷
   rw⁻ 40 (q18 c4) ∷
   rw⁻ 39 (q18 c4) ∷
   rw⁻ 38 (q18 c4) ∷
   rw⁻ 37 (q3 c4) ∷
   rw⁻ 36 (q6 c4) ∷
   rw⁻ 35 (q3 c4) ∷
   rw⁻ 34 (q6 c4) ∷
   rw⁻ 33 (q3 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw⁻ 47 (q4 c4) ∷
   rw⁻ 46 (q5 c4) ∷
   rw⁻ 45 (q5 c4) ∷
   rw⁻ 44 (q15 c4) ∷
   rw⁻ 43 (q16 c4) ∷
   rw⁻ 42 (q16 c4) ∷
   rw⁻ 41 (q16 c4) ∷
   rw⁻ 40 (q5 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw⁻ 38 (q5 c4) ∷
   rw⁻ 37 (q4 c4) ∷
   rw⁻ 36 (q5 c4) ∷
   rw 52 (q2 c4) ∷
   rw⁻ 51 (q3 c4) ∷
   rw⁻ 50 (q6 c4) ∷
   rw⁻ 49 (q3 c4) ∷
   rw⁻ 48 (q3 c4) ∷
   rw⁻ 47 (q17 c4) ∷
   rw⁻ 46 (q18 c4) ∷
   rw⁻ 45 (q18 c4) ∷
   rw⁻ 44 (q18 c4) ∷
   rw⁻ 43 (q3 c4) ∷
   rw⁻ 42 (q6 c4) ∷
   rw⁻ 41 (q3 c4) ∷
   rw⁻ 40 (q6 c4) ∷
   rw⁻ 39 (q3 c4) ∷
   rw⁻ 56 (q1 c4) ∷
   rw⁻ 55 (q4 c4) ∷
   rw⁻ 54 (q5 c4) ∷
   rw⁻ 53 (q4 c4) ∷
   rw⁻ 52 (q5 c4) ∷
   rw⁻ 51 (q5 c4) ∷
   rw⁻ 50 (q15 c4) ∷
   rw⁻ 49 (q16 c4) ∷
   rw⁻ 48 (q16 c4) ∷
   rw⁻ 47 (q16 c4) ∷
   rw⁻ 46 (q5 c4) ∷
   rw⁻ 45 (q4 c4) ∷
   rw⁻ 44 (q5 c4) ∷
   rw⁻ 43 (q4 c4) ∷
   rw⁻ 42 (q5 c4) ∷
   rw 60 (q7 c4) ∷
   rw⁻ 59 (q8 c4) ∷
   rw⁻ 58 (q9 c4) ∷
   rw⁻ 57 (q8 c4) ∷
   rw⁻ 56 (q9 c4) ∷
   rw⁻ 55 (q8 c4) ∷
   rw⁻ 54 (q8 c4) ∷
   rw⁻ 53 (q19 c4) ∷
   rw⁻ 52 (q10 c4) ∷
   rw⁻ 51 (q10 c4) ∷
   rw⁻ 50 (q10 c4) ∷
   rw⁻ 49 (q8 c4) ∷
   rw⁻ 48 (q9 c4) ∷
   rw⁻ 47 (q8 c4) ∷
   rw⁻ 46 (q9 c4) ∷
   rw⁻ 45 (q8 c4) ∷
   rw 64 (q7 c4) ∷
   rw⁻ 63 (q10 c4) ∷
   rw⁻ 62 (q8 c4) ∷
   rw⁻ 61 (q9 c4) ∷
   rw⁻ 60 (q8 c4) ∷
   rw⁻ 59 (q9 c4) ∷
   rw⁻ 58 (q8 c4) ∷
   rw⁻ 57 (q8 c4) ∷
   rw⁻ 56 (q19 c4) ∷
   rw⁻ 55 (q10 c4) ∷
   rw⁻ 54 (q10 c4) ∷
   rw⁻ 53 (q10 c4) ∷
   rw⁻ 52 (q8 c4) ∷
   rw⁻ 51 (q9 c4) ∷
   rw⁻ 50 (q8 c4) ∷
   rw⁻ 49 (q9 c4) ∷
   rw⁻ 48 (q8 c4) ∷
   rw 68 (q7 c4) ∷
   rw⁻ 67 (q10 c4) ∷
   rw⁻ 66 (q10 c4) ∷
   rw⁻ 65 (q8 c4) ∷
   rw⁻ 64 (q9 c4) ∷
   rw⁻ 63 (q8 c4) ∷
   rw⁻ 62 (q9 c4) ∷
   rw⁻ 61 (q8 c4) ∷
   rw⁻ 60 (q8 c4) ∷
   rw⁻ 59 (q19 c4) ∷
   rw⁻ 58 (q10 c4) ∷
   rw⁻ 57 (q10 c4) ∷
   rw⁻ 56 (q10 c4) ∷
   rw⁻ 55 (q8 c4) ∷
   rw⁻ 54 (q9 c4) ∷
   rw⁻ 53 (q8 c4) ∷
   rw⁻ 52 (q9 c4) ∷
   rw⁻ 51 (q8 c4) ∷
   rw⁻ 72 (q11 c4) ∷
   rw⁻ 71 (q12 c4) ∷
   rw⁻ 70 (q12 c4) ∷
   rw⁻ 69 (q12 c4) ∷
   rw⁻ 68 (q13 c4) ∷
   rw⁻ 67 (q14 c4) ∷
   rw⁻ 66 (q13 c4) ∷
   rw⁻ 65 (q14 c4) ∷
   rw⁻ 64 (q13 c4) ∷
   rw⁻ 63 (q13 c4) ∷
   rw⁻ 62 (q20 c4) ∷
   rw⁻ 61 (q12 c4) ∷
   rw⁻ 60 (q12 c4) ∷
   rw⁻ 59 (q12 c4) ∷
   rw⁻ 58 (q13 c4) ∷
   rw⁻ 57 (q14 c4) ∷
   rw⁻ 56 (q13 c4) ∷
   rw⁻ 55 (q14 c4) ∷
   rw⁻ 54 (q13 c4) ∷ []) Eq.refl
