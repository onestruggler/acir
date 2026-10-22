{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD703 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D703 (W : Ws) (Sᴰ : SD703) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-S2-at0213 : St 1917
  lem-S2-at0213 = pickᴰ 0 Sᴰ
  lem-S2-at1023 : St 1918
  lem-S2-at1023 = pickᴰ 1 Sᴰ
  lem-S2-at1203 : St 1945
  lem-S2-at1203 = pickᴰ 2 Sᴰ
  lem-S2-at2013 : St 1942
  lem-S2-at2013 = pickᴰ 3 Sᴰ
  lem-S2-at2103 : St 1946
  lem-S2-at2103 = pickᴰ 4 Sᴰ
  lem-S2-ᵖ-1 : St 1931
  lem-S2-ᵖ-1 = pickᴰ 5 Sᴰ
  lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 1947
  lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 6 Sᴰ
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : St 1948
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = pickᴰ 7 Sᴰ
  lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 1949
  lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 8 Sᴰ
  lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CS03 : St 1950
  lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CS03 = pickᴰ 9 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 : St 1951
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 = pickᴰ 10 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 : St 1952
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 = pickᴰ 11 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = wE 2051 W
  q3 : Eqn
  q3 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q5 : Eqn
  q5 = wE 30 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 122 W
  q10 : Eqn
  q10 = wE 24 W
  q11 : Eqn
  q11 = wE 25 W
  q12 : Eqn
  q12 = wE 124 W
  q13 : Eqn
  q13 = wE 334 W
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = wE 2052 W
  q16 : Eqn
  q16 = wE 2053 W
  q17 : Eqn
  q17 = sE 1942 lem-S2-at2013
  q18 : Eqn
  q18 = wE 1524 W
  q19 : Eqn
  q19 = wE 1523 W
  q20 : Eqn
  q20 = wE 1525 W

-- S2 @2013 ^-1: 129 steps
lem-S2-at2013-ᵖ-1 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) ⟫ʷ
lem-S2-at2013-ᵖ-1 = derive (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ [])
  (rw 4 q1 ∷
   rw 5 q2 ∷
   re 5 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q6 ∷
   rw 8 q5 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 10 q8 ∷
   rw 11 q7 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q3 ∷
   rw 11 q9 ∷
   rw 4 q1 ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q10 ∷
   rw 8 q6 ∷
   rw 9 q10 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 11 q11 ∷
   rw 12 q7 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 11 q3 ∷
   rw 12 q12 ∷
   rw 5 q13 ∷
   re 5 8 (Toff213 ∷ []) ∷
   re 4 3 (Toff203 ∷ []) ∷
   re 6 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q6 ∷
   rw 9 q5 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 11 q8 ∷
   rw 12 q7 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q3 ∷
   rw 12 q9 ∷
   rw 5 q1 ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q10 ∷
   rw 9 q6 ∷
   rw 10 q10 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q11 ∷
   rw 13 q7 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q12 ∷
   rw 6 q13 ∷
   re 6 8 (Toff213 ∷ []) ∷
   re 5 3 (Toff203 ∷ []) ∷
   rw 6 q14 ∷
   rw 5 q15 ∷
   rw 6 q1 ∷
   rw 7 q2 ∷
   re 7 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q6 ∷
   rw 10 q5 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q8 ∷
   rw 13 q7 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q9 ∷
   rw 6 q1 ∷
   rw 7 q3 ∷
   rw 8 q4 ∷
   rw 9 q10 ∷
   rw 10 q6 ∷
   rw 11 q10 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 13 q11 ∷
   rw 14 q7 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 13 q3 ∷
   rw 14 q12 ∷
   rw 7 q13 ∷
   re 7 8 (Toff213 ∷ []) ∷
   re 6 3 (Toff203 ∷ []) ∷
   re 8 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 7 q3 ∷
   rw 8 q4 ∷
   rw 9 q5 ∷
   rw 10 q6 ∷
   rw 11 q5 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 13 q8 ∷
   rw 14 q7 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q3 ∷
   rw 14 q9 ∷
   rw 7 q1 ∷
   rw 8 q3 ∷
   rw 9 q4 ∷
   rw 10 q10 ∷
   rw 11 q6 ∷
   rw 12 q10 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   rw 14 q11 ∷
   rw 15 q7 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 14 q3 ∷
   rw 15 q12 ∷
   rw 8 q13 ∷
   re 8 8 (Toff213 ∷ []) ∷
   re 7 3 (Toff203 ∷ []) ∷
   rw 8 q14 ∷
   rw 7 q16 ∷
   rw⁻ 4 q17 ∷
   rw 3 q18 ∷
   rw 2 q19 ∷
   rw 1 q18 ∷
   rw 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 1 W
  q22 : Eqn
  q22 = wE 1377 W
  q23 : Eqn
  q23 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q24 : Eqn
  q24 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q25 : Eqn
  q25 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q26 : Eqn
  q26 = wE 3 W
  q27 : Eqn
  q27 = wE 196 W
  q28 : Eqn
  q28 = sE 1918 lem-S2-at1023
  q29 : Eqn
  q29 = wE 1380 W
  q30 : Eqn
  q30 = wE 1379 W
  q31 : Eqn
  q31 = wE 1381 W

-- S2 @1023 ^-1: 121 steps
lem-S2-at1023-ᵖ-1 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) ⟫ʷ
lem-S2-at1023-ᵖ-1 = derive (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ [])
  (rw 4 q21 ∷
   rw 5 q22 ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 q23 ∷
   rw 7 q21 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 9 q21 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q24 ∷
   rw 11 q21 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q23 ∷
   rw⁻ 11 q25 ∷
   rw 4 q21 ∷
   rw⁻ 5 q23 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q26 ∷
   rw⁻ 7 q24 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q26 ∷
   rw⁻ 9 q24 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q26 ∷
   rw⁻ 11 q23 ∷
   rw⁻ 12 q25 ∷
   rw 5 q27 ∷
   re 5 8 (Toff102 ∷ []) ∷
   re 4 3 (Toff103 ∷ []) ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 5 q23 ∷
   rw 8 q21 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q24 ∷
   rw 10 q21 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q24 ∷
   rw 12 q21 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q23 ∷
   rw⁻ 12 q25 ∷
   rw 5 q21 ∷
   rw⁻ 6 q23 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q26 ∷
   rw⁻ 8 q24 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q26 ∷
   rw⁻ 10 q24 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q26 ∷
   rw⁻ 12 q23 ∷
   rw⁻ 13 q25 ∷
   rw 6 q27 ∷
   re 6 8 (Toff102 ∷ []) ∷
   re 5 3 (Toff103 ∷ []) ∷
   rw 6 q26 ∷
   rw 5 q15 ∷
   rw 6 q21 ∷
   rw 7 q22 ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 6 q23 ∷
   rw 9 q21 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q24 ∷
   rw 11 q21 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q24 ∷
   rw 13 q21 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q23 ∷
   rw⁻ 13 q25 ∷
   rw 6 q21 ∷
   rw⁻ 7 q23 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q26 ∷
   rw⁻ 9 q24 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q26 ∷
   rw⁻ 11 q24 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q26 ∷
   rw⁻ 13 q23 ∷
   rw⁻ 14 q25 ∷
   rw 7 q27 ∷
   re 7 8 (Toff102 ∷ []) ∷
   re 6 3 (Toff103 ∷ []) ∷
   re 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 7 q23 ∷
   rw 10 q21 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q24 ∷
   rw 12 q21 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q24 ∷
   rw 14 q21 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q23 ∷
   rw⁻ 14 q25 ∷
   rw 7 q21 ∷
   rw⁻ 8 q23 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q26 ∷
   rw⁻ 10 q24 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q26 ∷
   rw⁻ 12 q24 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q26 ∷
   rw⁻ 14 q23 ∷
   rw⁻ 15 q25 ∷
   rw 8 q27 ∷
   re 8 8 (Toff102 ∷ []) ∷
   re 7 3 (Toff103 ∷ []) ∷
   rw 8 q26 ∷
   rw 7 q16 ∷
   rw⁻ 4 q28 ∷
   rw 3 q29 ∷
   rw 2 q30 ∷
   rw 1 q29 ∷
   rw 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 1947 lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw⁻ 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = sE 1949 lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  (rw⁻ 0 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = sE 1950 lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CS03

-- pass [CS03] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 1 steps
lem-pass-CS03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = derive (CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ [])
  (rw⁻ 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = wE 173 W
  q36 : Eqn
  q36 = wE 1962 W
  q37 : Eqn
  q37 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q38 : Eqn
  q38 = wE 175 W
  q39 : Eqn
  q39 = eqn (Toff012 ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ []) (low₃-comm (Toff) (X))
  q40 : Eqn
  q40 = wE 1963 W
  q41 : Eqn
  q41 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q42 : Eqn
  q42 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q43 : Eqn
  q43 = wE 76 W
  q44 : Eqn
  q44 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q45 : Eqn
  q45 = wE 258 W
  q46 : Eqn
  q46 = wE 29 W
  q47 : Eqn
  q47 = wE 2016 W
  q48 : Eqn
  q48 = eqn (S0⁻ ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑)))
  q49 : Eqn
  q49 = wE 7 W
  q50 : Eqn
  q50 = wE 257 W
  q51 : Eqn
  q51 = wE 1965 W
  q52 : Eqn
  q52 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q53 : Eqn
  q53 = wE 1966 W
  q54 : Eqn
  q54 = wE 153 W
  q55 : Eqn
  q55 = wE 2054 W
  q56 : Eqn
  q56 = wE 1970 W
  q57 : Eqn
  q57 = wE 2055 W
  q58 : Eqn
  q58 = wE 151 W
  q59 : Eqn
  q59 = sE 1948 lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2
  q60 : Eqn
  q60 = eqn (ι ∷ []) (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑)))))
  q61 : Eqn
  q61 = wE 1967 W
  q62 : Eqn
  q62 = eqn (ι3 ∷ []) (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI))))
  q63 : Eqn
  q63 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q64 : Eqn
  q64 = wE 1968 W
  q65 : Eqn
  q65 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q66 : Eqn
  q66 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q67 : Eqn
  q67 = wE 2056 W
  q68 : Eqn
  q68 = wE 1999 W
  q69 : Eqn
  q69 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q70 : Eqn
  q70 = wE 2017 W
  q71 : Eqn
  q71 = eqn (X2 ∷ S3⁻ ∷ []) (S3⁻ ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) ((S • S • S)))
  q72 : Eqn
  q72 = wE 1969 W
  q73 : Eqn
  q73 = eqn (X0 ∷ S3 ∷ []) (S3 ∷ X0 ∷ []) (low₁-comm (X) ((S ↑ ↑)))
  q74 : Eqn
  q74 = wE 2057 W
  q75 : Eqn
  q75 = eqn (X0 ∷ S3⁻ ∷ []) (S3⁻ ∷ X0 ∷ []) (low₁-comm (X) (((S • S • S) ↑ ↑)))
  q76 : Eqn
  q76 = wE 689 W
  q77 : Eqn
  q77 = wE 464 W
  q78 : Eqn
  q78 = wE 1971 W
  q79 : Eqn
  q79 = wE 2058 W

-- pass [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3] [CS03 TOFF012 CSd03 TOFF012]: 247 steps
lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  (rw 11 q21 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q26 ∷
   rw 9 q35 ∷
   rw 10 q36 ∷
   rw⁻ 9 q37 ∷
   rw 12 q21 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   rw 11 q38 ∷
   rw 12 q26 ∷
   rw⁻ 11 q39 ∷
   rw 14 q21 ∷
   re 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q26 ∷
   rw 12 q35 ∷
   rw 13 q40 ∷
   rw⁻ 12 q41 ∷
   rw 15 q21 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q38 ∷
   rw 15 q26 ∷
   rw⁻ 14 q39 ∷
   rw⁻ 8 q42 ∷
   rw 11 q1 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q7 ∷
   rw 11 q43 ∷
   rw⁻ 10 q7 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q44 ∷
   rw 10 q45 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 10 q46 ∷
   rw 11 q7 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q44 ∷
   rw 11 q14 ∷
   rw 10 q47 ∷
   rw⁻ 13 q48 ∷
   rw 16 q1 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q7 ∷
   rw 16 q49 ∷
   rw⁻ 15 q7 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw⁻ 14 q44 ∷
   rw 15 q50 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   rw 15 q8 ∷
   rw 16 q7 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q44 ∷
   rw 16 q14 ∷
   rw 15 q47 ∷
   rw 7 q51 ∷
   rw 11 q21 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q26 ∷
   rw 9 q52 ∷
   rw 10 q53 ∷
   rw 9 q54 ∷
   rw 12 q21 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q52 ∷
   rw 12 q26 ∷
   rw 11 q55 ∷
   rw 14 q56 ∷
   rw 20 q21 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q26 ∷
   rw 18 q52 ∷
   rw 19 q57 ∷
   rw 18 q58 ∷
   rw 21 q21 ∷
   re 19 3 (CS03⁻ ∷ []) ∷
   rw⁻ 20 q52 ∷
   rw 21 q26 ∷
   rw 20 q55 ∷
   rw 3 q59 ∷
   rw 3 q60 ∷
   rw 2 q61 ∷
   rw 2 q62 ∷
   rw⁻ 3 q63 ∷
   rw 4 q64 ∷
   rw 4 q62 ∷
   rw 5 q62 ∷
   rw 6 q62 ∷
   rw 10 q21 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q26 ∷
   rw 8 q35 ∷
   rw 9 q36 ∷
   rw⁻ 8 q37 ∷
   rw 11 q21 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q38 ∷
   rw 11 q26 ∷
   rw⁻ 10 q65 ∷
   rw⁻ 11 q39 ∷
   rw⁻ 12 q65 ∷
   rw 14 q60 ∷
   rw 13 q61 ∷
   rw 13 q62 ∷
   rw 15 q60 ∷
   rw 14 q61 ∷
   rw 14 q62 ∷
   rw 16 q60 ∷
   rw 15 q61 ∷
   rw 15 q62 ∷
   rw⁻ 16 q66 ∷
   rw 17 q67 ∷
   rw 17 q62 ∷
   rw 21 q21 ∷
   re 20 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q26 ∷
   rw 19 q35 ∷
   rw 20 q40 ∷
   rw⁻ 19 q41 ∷
   rw 22 q21 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q38 ∷
   rw 22 q26 ∷
   rw⁻ 21 q65 ∷
   rw⁻ 22 q39 ∷
   rw⁻ 23 q65 ∷
   rw 1 q68 ∷
   rw⁻ 2 q48 ∷
   rw 3 q68 ∷
   rw 4 q68 ∷
   rw 5 q68 ∷
   rw 6 q69 ∷
   rw⁻ 7 q42 ∷
   rw 10 q1 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q7 ∷
   rw 10 q43 ∷
   rw⁻ 9 q7 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q44 ∷
   rw 9 q45 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q46 ∷
   rw 10 q7 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q44 ∷
   rw 10 q14 ∷
   rw 9 q70 ∷
   rw 10 q68 ∷
   rw 11 q68 ∷
   rw 12 q68 ∷
   rw⁻ 13 q42 ∷
   rw 14 q68 ∷
   rw 15 q71 ∷
   rw⁻ 16 q48 ∷
   rw 19 q1 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q7 ∷
   rw 19 q49 ∷
   rw⁻ 18 q7 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw⁻ 17 q44 ∷
   rw 18 q50 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q7 ∷
   rw 18 q8 ∷
   rw 19 q7 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q44 ∷
   rw 19 q14 ∷
   rw 18 q70 ∷
   rw 0 q72 ∷
   rw 1 q56 ∷
   rw 5 q72 ∷
   rw 6 q72 ∷
   rw 7 q72 ∷
   rw 8 q73 ∷
   rw 9 q51 ∷
   rw 13 q21 ∷
   re 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q26 ∷
   rw 11 q52 ∷
   rw 12 q53 ∷
   rw 11 q54 ∷
   rw 14 q21 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q52 ∷
   rw 14 q26 ∷
   rw 13 q74 ∷
   rw 14 q72 ∷
   rw 15 q72 ∷
   rw 16 q72 ∷
   rw 17 q51 ∷
   rw 19 q72 ∷
   rw 20 q75 ∷
   rw 21 q56 ∷
   rw 27 q21 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q26 ∷
   rw 25 q52 ∷
   rw 26 q57 ∷
   rw 25 q58 ∷
   rw 28 q21 ∷
   re 26 3 (CS03⁻ ∷ []) ∷
   rw⁻ 27 q52 ∷
   rw 28 q26 ∷
   rw 27 q74 ∷
   rw 13 q21 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q26 ∷
   rw 11 q76 ∷
   rw 10 q41 ∷
   rw 9 q25 ∷
   rw 8 q77 ∷
   rw 7 q25 ∷
   rw 6 q25 ∷
   rw 5 q25 ∷
   rw 4 q37 ∷
   rw 3 q25 ∷
   rw 2 q25 ∷
   rw 1 q25 ∷
   rw 0 q25 ∷
   rw 1 q78 ∷
   rw 2 q21 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q26 ∷
   rw 15 q21 ∷
   re 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q26 ∷
   rw 13 q77 ∷
   rw 12 q37 ∷
   rw 11 q25 ∷
   rw 10 q25 ∷
   rw 9 q25 ∷
   rw 8 q76 ∷
   rw 7 q25 ∷
   rw 6 q41 ∷
   rw 5 q25 ∷
   rw 4 q25 ∷
   rw 3 q25 ∷
   rw 2 q25 ∷
   rw 3 q79 ∷
   rw 4 q21 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q26 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = sE 1945 lem-S2-at1203

-- resp TOFF123 CS01 TOFF123 CSd01: 1 steps
lem-resp-TOFF123-CS01-TOFF123-CSd01 : ⟪ (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-resp-TOFF123-CS01-TOFF123-CSd01 = derive (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q80 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = sE 1917 lem-S2-at0213

-- resp TOFF023 CS01 TOFF023 CSd01: 1 steps
lem-resp-TOFF023-CS01-TOFF023-CSd01 : ⟪ (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-resp-TOFF023-CS01-TOFF023-CSd01 = derive (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q81 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 2041 W
  q83 : Eqn
  q83 = wE 2042 W
  q84 : Eqn
  q84 = wE 1694 W

-- S2 @1203 ^-1: 9 steps
lem-S2-at1203-ᵖ-1 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) ⟫ʷ
lem-S2-at1203-ᵖ-1 = derive (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ [])
  (rw 4 q82 ∷
   rw 5 q83 ∷
   rw 6 q82 ∷
   rw 7 q84 ∷
   rw⁻ 4 q80 ∷
   rw 3 q29 ∷
   rw 2 q30 ∷
   rw 1 q29 ∷
   rw 0 q31 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = sE 1931 lem-S2-ᵖ-1

-- resp S0 K0 CS02 TOFF013 CSd02 TOFF013 Kd0 Sd0: 1 steps
lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 : ⟪ (S0 ∷ K0 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 = derive (S0 ∷ K0 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ [])
  (rw⁻ 2 q85 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = wE 1357 W
  q87 : Eqn
  q87 = wE 231 W
  q88 : Eqn
  q88 = sE 1946 lem-S2-at2103

-- S2 @2103 ^-1: 9 steps
lem-S2-at2103-ᵖ-1 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) ⟫ʷ
lem-S2-at2103-ᵖ-1 = derive (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ [])
  (rw 4 q2 ∷
   rw 5 q86 ∷
   rw 6 q2 ∷
   rw 7 q87 ∷
   rw⁻ 4 q88 ∷
   rw 3 q18 ∷
   rw 2 q19 ∷
   rw 1 q18 ∷
   rw 0 q20 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = sE 1951 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3

-- Bar(SSKSKK;3,2->0) passes factors of X3 CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01 X3: 1 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 0 q89 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = sE 1952 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3

-- Bar(SSSKSS;3,2->0) passes factors of X3 CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01 X3: 1 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  (rw 0 q90 ∷ []) Eq.refl
