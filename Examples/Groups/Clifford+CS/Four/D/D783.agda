{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD783 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D783 (W : Ws) (Sᴰ : SD783) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-ROT-gad : St 2261
  lem-ROT-gad = pickᴰ 0 Sᴰ
  lem-PP-flip : St 2473
  lem-PP-flip = pickᴰ 1 Sᴰ
  lem-h-gad-at1023 : St 3478
  lem-h-gad-at1023 = pickᴰ 2 Sᴰ
  lem-a1-a0i : St 3401
  lem-a1-a0i = pickᴰ 3 Sᴰ
  lem-a0-Ri-≡-Ri-a0ᵖ-1-at1023 : St 3479
  lem-a0-Ri-≡-Ri-a0ᵖ-1-at1023 = pickᴰ 4 Sᴰ
  lem-F7a-gad-inv-at1023 : St 3480
  lem-F7a-gad-inv-at1023 = pickᴰ 5 Sᴰ
  lem-R0-P--⟶-P-Q : St 3481
  lem-R0-P--⟶-P-Q = pickᴰ 6 Sᴰ

private
  q1 : Eqn
  q1 = eqn (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-PP-flip)
  q2 : Eqn
  q2 = eqn (X1 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ X1 ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (lem-h-gad-at1023)
  q3 : Eqn
  q3 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (lem-a0-Ri-≡-Ri-a0ᵖ-1-at1023)
  q4 : Eqn
  q4 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-F7a-gad-inv-at1023)
  q5 : Eqn
  q5 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-a1-a0i)
  q6 : Eqn
  q6 = eqn (CS13⁻ ∷ CS13 ∷ []) [] (wn 1379 W)
  q7 : Eqn
  q7 = eqn (Toff102 ∷ Toff102 ∷ []) [] (wn 1380 W)
  q8 : Eqn
  q8 = eqn (CS13 ∷ CS13⁻ ∷ []) [] (wn 1381 W)
  q9 : Eqn
  q9 = eqn (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) lem-PP-flip
  q10 : Eqn
  q10 = eqn (X1 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ X1 ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) lem-h-gad-at1023

-- F7b: 11 steps
lem-F7b : ⟪ (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ X1 ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ
lem-F7b = derive (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ X1 ∷ []) (X1 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ X1 ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ [])
  (rw 0 q1 ∷
   rw 8 q2 ∷
   rw 4 q3 ∷
   rw 0 q4 ∷
   rw 8 q5 ∷
   rw 15 q6 ∷
   rw 14 q7 ∷
   rw 13 q8 ∷
   rw 12 q7 ∷
   rw⁻ 8 q9 ∷
   rw⁻ 0 q10 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = eqn (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (lem-ROT-gad)
  q12 : Eqn
  q12 = eqn [] (S0 ∷ S0⁻ ∷ []) (wn 1732 W)
  q13 : Eqn
  q13 = eqn [] (K0 ∷ K0⁻ ∷ []) (wn 116 W)
  q14 : Eqn
  q14 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q15 : Eqn
  q15 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q16 : Eqn
  q16 = eqn [] (CS02 ∷ CS02⁻ ∷ []) (wn 1357 W)
  q17 : Eqn
  q17 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q18 : Eqn
  q18 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)
  q19 : Eqn
  q19 = eqn [] (K0⁻ ∷ K0 ∷ []) (wn 54 W)
  q20 : Eqn
  q20 = eqn [] (S0⁻ ∷ S0 ∷ []) (wn 1726 W)
  q21 : Eqn
  q21 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (lem-R0-P--⟶-P-Q)
  q22 : Eqn
  q22 = eqn (S0⁻ ∷ S0 ∷ []) [] (wn 2487 W)
  q23 : Eqn
  q23 = eqn (K0⁻ ∷ K0 ∷ []) [] (wn 1339 W)
  q24 : Eqn
  q24 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)
  q25 : Eqn
  q25 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)
  q26 : Eqn
  q26 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)
  q27 : Eqn
  q27 = eqn (K0 ∷ K0⁻ ∷ []) [] (wn 1846 W)
  q28 : Eqn
  q28 = eqn (S0 ∷ S0⁻ ∷ []) [] (wn 1728 W)
  q29 : Eqn
  q29 = eqn (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) lem-ROT-gad

-- F10: 47 steps
lem-F10 : ⟪ (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X1 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ X1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ X1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X1 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ X1 ∷ []) ⟫ʷ
lem-F10 = derive (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X1 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ X1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (X1 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ X1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X1 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ X1 ∷ [])
  (rw 0 q11 ∷
   rw 25 q11 ∷
   rw 8 q2 ∷
   rw 0 q12 ∷
   rw 1 q13 ∷
   rw 2 q14 ∷
   rw 3 q15 ∷
   rw 4 q16 ∷
   rw 5 q15 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q15 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   rw 5 q17 ∷
   rw 4 q14 ∷
   rw 5 q15 ∷
   rw 6 q18 ∷
   rw 7 q15 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 8 q15 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q17 ∷
   rw 6 q19 ∷
   rw 7 q20 ∷
   rw 8 q21 ∷
   rw 7 q22 ∷
   rw 6 q23 ∷
   rw 7 q15 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   rw 6 q24 ∷
   rw 5 q17 ∷
   rw 4 q25 ∷
   rw 5 q15 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   rw 4 q26 ∷
   rw 3 q17 ∷
   rw 2 q25 ∷
   rw 1 q27 ∷
   rw 0 q28 ∷
   rw⁻ 0 q10 ∷
   rw⁻ 17 q29 ∷
   rw⁻ 32 q10 ∷ []) Eq.refl
