{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD715 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D715 (W : Ws) (Sᴰ : SD715) where

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
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 840
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 0 Sᴰ
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 869
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 1 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : St 2061
  lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = pickᴰ 2 Sᴰ
  lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : St 2062
  lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = pickᴰ 3 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : St 2063
  lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = pickᴰ 4 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS12-TOFF203-CSd12-TOFF203 : St 2064
  lem-pass-X3-CK30-X3-vs-CS12-TOFF203-CSd12-TOFF203 = pickᴰ 5 Sᴰ
  lem-pass-X3-CK32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : St 2065
  lem-pass-X3-CK32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = pickᴰ 6 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS12-TOFF203-CSd12-TOFF203 : St 2066
  lem-pass-X3-CKd30-X3-vs-CS12-TOFF203-CSd12-TOFF203 = pickᴰ 7 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS12-TOFF203-CSd12-TOFF203 : St 2067
  lem-pass-X3-CS30-X3-vs-CS12-TOFF203-CSd12-TOFF203 = pickᴰ 8 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS12-TOFF203-CSd12-TOFF203 : St 2068
  lem-pass-X3-CSd30-X3-vs-CS12-TOFF203-CSd12-TOFF203 = pickᴰ 9 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS12-TOFF103-CSd12-TOFF103 : St 2069
  lem-pass-X3-CK30-X3-vs-CS12-TOFF103-CSd12-TOFF103 = pickᴰ 10 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS12-TOFF103-CSd12-TOFF103 : St 2070
  lem-pass-X3-CKd30-X3-vs-CS12-TOFF103-CSd12-TOFF103 = pickᴰ 11 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS12-TOFF103-CSd12-TOFF103 : St 2071
  lem-pass-X3-CS30-X3-vs-CS12-TOFF103-CSd12-TOFF103 = pickᴰ 12 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS12-TOFF103-CSd12-TOFF103 : St 2072
  lem-pass-X3-CSd30-X3-vs-CS12-TOFF103-CSd12-TOFF103 = pickᴰ 13 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 14 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 1146
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 15 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1 : St 2073
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1 = pickᴰ 16 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1 : St 2074
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1 = pickᴰ 17 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02 : St 2075
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02 = pickᴰ 18 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02 : St 2076
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02 = pickᴰ 19 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-S2 : St 2077
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-S2 = pickᴰ 20 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-Sd2 : St 2078
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-Sd2 = pickᴰ 21 Sᴰ
  lem-S2 : St 1778
  lem-S2 = pickᴰ 22 Sᴰ
  lem-S2-at0213-ᵖ-1 : St 2024
  lem-S2-at0213-ᵖ-1 = pickᴰ 23 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2034
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 24 Sᴰ
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 2079
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 25 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2038
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 26 Sᴰ
  lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2048
  lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 27 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2049
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 28 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13 : St 2054
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13 = pickᴰ 29 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13 : St 2055
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13 = pickᴰ 30 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2 : St 2056
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2 = pickᴰ 31 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3 : St 2080
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3 = pickᴰ 32 Sᴰ
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2058
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 33 Sᴰ
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2059
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 34 Sᴰ
  lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : St 2081
  lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 35 Sᴰ
  lem-pass-X3-CSd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : St 2082
  lem-pass-X3-CSd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 36 Sᴰ
  lem-S2-at1023-ᵖ-1 : St 2083
  lem-S2-at1023-ᵖ-1 = pickᴰ 37 Sᴰ
  lem-S2-at1203-ᵖ-1 : St 2084
  lem-S2-at1203-ᵖ-1 = pickᴰ 38 Sᴰ
  lem-S2-at2013-ᵖ-1 : St 2085
  lem-S2-at2013-ᵖ-1 = pickᴰ 39 Sᴰ
  lem-S2-at2103-ᵖ-1 : St 2086
  lem-S2-at2103-ᵖ-1 = pickᴰ 40 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 2087
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 41 Sᴰ
  lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2088
  lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 42 Sᴰ

private
  q1 : Eqn
  q1 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2)
  q2 : Eqn
  q2 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1 ∷ []) (S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1)
  q3 : Eqn
  q3 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13)
  q4 : Eqn
  q4 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ []) (S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1)
  q5 : Eqn
  q5 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS13 ∷ []) (CS13 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13)

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 TOFF102 X2 S1 CSd13 X2 TOFF102 X2 Sd1 CS13]: 6 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 0 q1 ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   rw 5 q1 ∷
   rw 8 q4 ∷
   rw 9 q5 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1499 W)
  q7 : Eqn
  q7 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ S1 ∷ K1 ∷ []) (S1 ∷ K1 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 2130 W)
  q8 : Eqn
  q8 = eqn (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
  q9 : Eqn
  q9 = eqn (X2 ∷ CK21 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
  q10 : Eqn
  q10 = eqn (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 2131 W)

-- pass [X2 CSd21 X2] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 7 steps
lem-pass-X2-CSd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 0 q6 ∷
   rw 1 q7 ∷
   rw 9 q8 ∷
   rw 6 q9 ∷
   rw 3 q8 ∷
   rw 7 q10 ∷
   rw 9 q6 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = eqn (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1495 W)
  q12 : Eqn
  q12 = eqn (X2 ∷ CK21 ∷ X2 ∷ S1 ∷ K1 ∷ []) (S1 ∷ K1 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 2132 W)
  q13 : Eqn
  q13 = eqn (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 2133 W)

-- pass [X2 CK21 X2] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 9 steps
lem-pass-X2-CK21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  (rw 0 q11 ∷
   rw 1 q12 ∷
   rw 15 q9 ∷
   rw 12 q8 ∷
   rw 9 q8 ∷
   rw 6 q9 ∷
   rw 3 q8 ∷
   rw 7 q13 ∷
   rw 9 q11 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q14 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn [] (CS23 ∷ CS23⁻ ∷ []) (wn 1520 W)
  q16 : Eqn
  q16 = eqn [] (Toff201 ∷ Toff201 ∷ []) (wn 1521 W)
  q17 : Eqn
  q17 = eqn [] (CS23⁻ ∷ CS23 ∷ []) (wn 1522 W)
  q18 : Eqn
  q18 = eqn (X3 ∷ CS23 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23
  q19 : Eqn
  q19 = eqn (CS23⁻ ∷ CS23 ∷ []) [] (wn 1523 W)
  q20 : Eqn
  q20 = eqn (Toff201 ∷ Toff201 ∷ []) [] (wn 1524 W)
  q21 : Eqn
  q21 = eqn (CS23 ∷ CS23⁻ ∷ []) [] (wn 1525 W)

-- pass [X3 CS32 X3] [CS23 TOFF201 CSd23 TOFF201]: 9 steps
lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (X3 ∷ CS23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  (rw 0 q15 ∷
   rw 1 q16 ∷
   rw 2 q17 ∷
   rw 3 q16 ∷
   rw⁻ 4 q18 ∷
   rw 10 q19 ∷
   rw 9 q20 ∷
   rw 8 q21 ∷
   rw 7 q20 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = eqn (X3 ∷ CS23⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) lem-pass-X3-CSd32-X3-vs-TOFF201-CS23-TOFF201-CSd23

-- pass [X3 CSd32 X3] [CS23 TOFF201 CSd23 TOFF201]: 9 steps
lem-pass-X3-CSd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 0 q15 ∷
   rw 1 q16 ∷
   rw 2 q17 ∷
   rw 3 q16 ∷
   rw⁻ 4 q22 ∷
   rw 10 q19 ∷
   rw 9 q20 ∷
   rw 8 q21 ∷
   rw 7 q20 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = eqn (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3)
  q24 : Eqn
  q24 = eqn (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02 ∷ []) (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02)
  q25 : Eqn
  q25 = eqn (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02)

-- pass [TOFF201 CS23 TOFF201 CSd23] [X3 TOFF013 X3 CS02 X3 TOFF013 X3 CSd02]: 4 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = derive (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  (rw 0 q23 ∷
   rw 3 q24 ∷
   rw 4 q23 ∷
   rw 7 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn [] (CS13 ∷ CS13⁻ ∷ []) (wn 1376 W)
  q27 : Eqn
  q27 = eqn [] (Toff102 ∷ Toff102 ∷ []) (wn 1377 W)
  q28 : Eqn
  q28 = eqn [] (CS13⁻ ∷ CS13 ∷ []) (wn 1378 W)
  q29 : Eqn
  q29 = eqn (X3 ∷ CS13 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q30 : Eqn
  q30 = eqn (CS13⁻ ∷ CS13 ∷ []) [] (wn 1379 W)
  q31 : Eqn
  q31 = eqn (Toff102 ∷ Toff102 ∷ []) [] (wn 1380 W)
  q32 : Eqn
  q32 = eqn (CS13 ∷ CS13⁻ ∷ []) [] (wn 1381 W)

-- pass [X3 CS31 X3] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X3 ∷ CS13 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw 0 q26 ∷
   rw 1 q27 ∷
   rw 2 q28 ∷
   rw 3 q27 ∷
   rw⁻ 4 q29 ∷
   rw 10 q30 ∷
   rw 9 q31 ∷
   rw 8 q32 ∷
   rw 7 q31 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q34 : Eqn
  q34 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q35 : Eqn
  q35 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q36 : Eqn
  q36 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q37 : Eqn
  q37 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q38 : Eqn
  q38 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q39 : Eqn
  q39 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2134 W)
  q40 : Eqn
  q40 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q41 : Eqn
  q41 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q42 : Eqn
  q42 = eqn (X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q43 : Eqn
  q43 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q44 : Eqn
  q44 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2135 W)

-- pass [X3 CSd30 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 57 steps
lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 7 q33 ∷
   rw 6 q34 ∷
   rw 5 q34 ∷
   rw 4 q35 ∷
   rw 3 q36 ∷
   rw 2 q37 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q38 ∷
   rw 0 q37 ∷
   rw 1 q39 ∷
   rw⁻ 0 q36 ∷
   rw⁻ 1 q35 ∷
   rw⁻ 2 q34 ∷
   rw⁻ 3 q34 ∷
   rw 4 q40 ∷
   rw 7 q33 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 6 q40 ∷
   rw 7 q40 ∷
   rw 10 q33 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q40 ∷
   rw 10 q40 ∷
   rw 13 q33 ∷
   re 11 3 (CS03⁻ ∷ []) ∷
   rw 12 q40 ∷
   rw 13 q38 ∷
   rw 10 q41 ∷
   rw 7 q42 ∷
   rw 4 q41 ∷
   rw 21 q33 ∷
   rw 20 q34 ∷
   rw 19 q43 ∷
   rw 18 q36 ∷
   rw 17 q36 ∷
   rw 16 q37 ∷
   re 15 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q38 ∷
   rw 14 q37 ∷
   rw 13 q37 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 14 q38 ∷
   rw 11 q37 ∷
   rw 10 q37 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q38 ∷
   rw 8 q37 ∷
   rw 9 q44 ∷
   rw⁻ 8 q36 ∷
   rw⁻ 9 q36 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 11 q34 ∷
   rw 12 q40 ∷
   rw 15 q33 ∷
   re 13 3 (CS03⁻ ∷ []) ∷
   rw 14 q40 ∷
   rw 15 q38 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2136 W)
  q46 : Eqn
  q46 = eqn (X3 ∷ CS03 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q47 : Eqn
  q47 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2137 W)

-- pass [X3 CKd30 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 75 steps
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 7 q33 ∷
   rw 6 q34 ∷
   rw 5 q34 ∷
   rw 4 q35 ∷
   rw 3 q36 ∷
   rw 2 q37 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q38 ∷
   rw 0 q37 ∷
   rw 1 q45 ∷
   rw⁻ 0 q36 ∷
   rw⁻ 1 q35 ∷
   rw⁻ 2 q34 ∷
   rw⁻ 3 q34 ∷
   rw 4 q40 ∷
   rw 7 q33 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 6 q40 ∷
   rw 7 q40 ∷
   rw 10 q33 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q40 ∷
   rw 10 q40 ∷
   rw 13 q33 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q40 ∷
   rw 13 q40 ∷
   rw 16 q33 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q40 ∷
   rw 16 q40 ∷
   rw 19 q33 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q40 ∷
   rw 19 q38 ∷
   rw 16 q42 ∷
   rw 13 q46 ∷
   rw 10 q46 ∷
   rw 7 q42 ∷
   rw 4 q41 ∷
   rw 27 q33 ∷
   rw 26 q34 ∷
   rw 25 q43 ∷
   rw 24 q36 ∷
   rw 23 q36 ∷
   rw 22 q37 ∷
   re 21 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 23 q38 ∷
   rw 20 q37 ∷
   rw 19 q37 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q38 ∷
   rw 17 q37 ∷
   rw 16 q37 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q38 ∷
   rw 14 q37 ∷
   rw 13 q37 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 14 q38 ∷
   rw 11 q37 ∷
   rw 10 q37 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q38 ∷
   rw 8 q37 ∷
   rw 9 q47 ∷
   rw⁻ 8 q36 ∷
   rw⁻ 9 q36 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 11 q34 ∷
   rw 12 q40 ∷
   rw 15 q33 ∷
   re 13 3 (CK30⁻ ∷ []) ∷
   rw 14 q40 ∷
   rw 15 q38 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = eqn (X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 2138 W)
  q49 : Eqn
  q49 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q50 : Eqn
  q50 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2139 W)

-- pass [X3 CK30 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 75 steps
lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (X3 ∷ CK30 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 7 q33 ∷
   rw 6 q34 ∷
   rw 5 q34 ∷
   rw 4 q35 ∷
   rw 3 q36 ∷
   rw 2 q37 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q38 ∷
   rw 0 q37 ∷
   rw 1 q48 ∷
   rw⁻ 0 q36 ∷
   rw⁻ 1 q35 ∷
   rw⁻ 2 q34 ∷
   rw⁻ 3 q34 ∷
   rw 4 q40 ∷
   rw 7 q33 ∷
   re 5 3 (CK30⁻ ∷ []) ∷
   rw 6 q40 ∷
   rw 7 q40 ∷
   rw 10 q33 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q40 ∷
   rw 10 q40 ∷
   rw 13 q33 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q40 ∷
   rw 13 q40 ∷
   rw 16 q33 ∷
   re 14 3 (CK30⁻ ∷ []) ∷
   rw 15 q40 ∷
   rw 16 q40 ∷
   rw 19 q33 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q40 ∷
   rw 19 q38 ∷
   rw 16 q46 ∷
   rw 13 q49 ∷
   rw 10 q46 ∷
   rw 7 q46 ∷
   rw 4 q49 ∷
   rw 27 q33 ∷
   rw 26 q34 ∷
   rw 25 q43 ∷
   rw 24 q36 ∷
   rw 23 q36 ∷
   rw 22 q37 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q38 ∷
   rw 20 q37 ∷
   rw 19 q37 ∷
   re 18 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q38 ∷
   rw 17 q37 ∷
   rw 16 q37 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q38 ∷
   rw 14 q37 ∷
   rw 13 q37 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q38 ∷
   rw 11 q37 ∷
   rw 10 q37 ∷
   re 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q38 ∷
   rw 8 q37 ∷
   rw 9 q50 ∷
   rw⁻ 8 q36 ∷
   rw⁻ 9 q36 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 11 q34 ∷
   rw 12 q40 ∷
   rw 15 q33 ∷
   re 13 3 (CK30 ∷ []) ∷
   rw 14 q40 ∷
   rw 15 q38 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = eqn (X2 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 2140 W)
  q52 : Eqn
  q52 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 2141 W)

-- pass [X3 CS30 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 57 steps
lem-pass-X3-CS30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (X3 ∷ CS03 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 7 q33 ∷
   rw 6 q34 ∷
   rw 5 q34 ∷
   rw 4 q35 ∷
   rw 3 q36 ∷
   rw 2 q37 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q38 ∷
   rw 0 q37 ∷
   rw 1 q51 ∷
   rw⁻ 0 q36 ∷
   rw⁻ 1 q35 ∷
   rw⁻ 2 q34 ∷
   rw⁻ 3 q34 ∷
   rw 4 q40 ∷
   rw 7 q33 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q40 ∷
   rw 7 q40 ∷
   rw 10 q33 ∷
   re 8 3 (CK30⁻ ∷ []) ∷
   rw 9 q40 ∷
   rw 10 q40 ∷
   rw 13 q33 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q40 ∷
   rw 13 q38 ∷
   rw 10 q46 ∷
   rw 7 q49 ∷
   rw 4 q46 ∷
   rw 21 q33 ∷
   rw 20 q34 ∷
   rw 19 q43 ∷
   rw 18 q36 ∷
   rw 17 q36 ∷
   rw 16 q37 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q38 ∷
   rw 14 q37 ∷
   rw 13 q37 ∷
   re 12 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q38 ∷
   rw 11 q37 ∷
   rw 10 q37 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q38 ∷
   rw 8 q37 ∷
   rw 9 q52 ∷
   rw⁻ 8 q36 ∷
   rw⁻ 9 q36 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 11 q34 ∷
   rw 12 q40 ∷
   rw 15 q33 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q40 ∷
   rw 15 q38 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (lem-S2-at0213-ᵖ-1)
  q54 : Eqn
  q54 = eqn (X3 ∷ CS23⁻ ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023)
  q55 : Eqn
  q55 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) lem-S2-at0213-ᵖ-1

-- pass [X3 CSd32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 3 q53 ∷
   rw 0 q54 ∷
   rw⁻ 0 q55 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023)

-- pass [X3 CKd32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CKd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X3 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  (rw 3 q53 ∷
   rw 0 q56 ∷
   rw⁻ 0 q55 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (X3 ∷ CS23 ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023)

-- pass [X3 CS32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X3 ∷ CS23 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  (rw 3 q53 ∷
   rw 0 q57 ∷
   rw⁻ 0 q55 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ S2 ∷ []) (S2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-S2)
  q59 : Eqn
  q59 = eqn (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-Sd2)

-- pass [TOFF201 CS23 TOFF201 CSd23] [X3 TOFF013 X3 S2 CSd02 X3 TOFF013 X3 Sd2 CS02]: 6 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 = derive (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  (rw 0 q23 ∷
   rw 3 q58 ∷
   rw 4 q25 ∷
   rw 5 q23 ∷
   rw 8 q59 ∷
   rw 9 q24 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (X3 ∷ CK32 ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-CS01-TOFF023-CSd01-TOFF023)

-- pass [X3 CK32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CK32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X3 ∷ CK32 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  (rw 3 q53 ∷
   rw 0 q60 ∷
   rw⁻ 0 q55 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) (lem-S2-at2013-ᵖ-1)
  q62 : Eqn
  q62 = eqn (X3 ∷ CK30 ∷ X3 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS12-TOFF203-CSd12-TOFF203)
  q63 : Eqn
  q63 = eqn (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) lem-S2-at2013-ᵖ-1

-- pass [X3 CK30 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (X3 ∷ CK30 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 3 q61 ∷
   rw 0 q62 ∷
   rw⁻ 0 q63 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = eqn (X3 ∷ CS03 ∷ X3 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS12-TOFF203-CSd12-TOFF203)

-- pass [X3 CS30 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CS30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (X3 ∷ CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 3 q61 ∷
   rw 0 q64 ∷
   rw⁻ 0 q63 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS12-TOFF203-CSd12-TOFF203)

-- pass [X3 CSd30 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 3 q61 ∷
   rw 0 q65 ∷
   rw⁻ 0 q63 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS12-TOFF203-CSd12-TOFF203)

-- pass [X3 CKd30 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 3 q61 ∷
   rw 0 q66 ∷
   rw⁻ 0 q63 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q68 : Eqn
  q68 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q69 : Eqn
  q69 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q70 : Eqn
  q70 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q71 : Eqn
  q71 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q72 : Eqn
  q72 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q73 : Eqn
  q73 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 2102 W)
  q74 : Eqn
  q74 = eqn (X2 ∷ CS02 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q75 : Eqn
  q75 = eqn (X2 ∷ CK20 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q76 : Eqn
  q76 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2103 W)

-- pass [X2 CSd20 X2] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 27 steps
lem-pass-X2-CSd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 4 q67 ∷
   rw⁻ 3 q68 ∷
   rw⁻ 2 q69 ∷
   rw 1 q70 ∷
   rw⁻ 0 q69 ∷
   rw 1 q6 ∷
   rw 0 q68 ∷
   rw 1 q69 ∷
   rw 2 q71 ∷
   rw 3 q69 ∷
   rw 4 q72 ∷
   rw 1 q73 ∷
   rw 9 q74 ∷
   rw 6 q75 ∷
   rw 3 q74 ∷
   rw 7 q76 ∷
   rw 13 q67 ∷
   rw⁻ 12 q68 ∷
   rw⁻ 11 q69 ∷
   rw 10 q70 ∷
   rw⁻ 9 q69 ∷
   rw 10 q6 ∷
   rw 9 q68 ∷
   rw 10 q69 ∷
   rw 11 q71 ∷
   rw 12 q69 ∷
   rw 13 q72 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q78 : Eqn
  q78 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q79 : Eqn
  q79 = eqn (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2045 W)
  q80 : Eqn
  q80 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2046 W)

-- pass [X2 CK20 X2] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 29 steps
lem-pass-X2-CK20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw 4 q67 ∷
   rw⁻ 3 q68 ∷
   rw⁻ 2 q69 ∷
   rw 1 q77 ∷
   rw⁻ 0 q69 ∷
   rw 1 q11 ∷
   rw 0 q68 ∷
   rw 1 q69 ∷
   rw 2 q78 ∷
   rw 3 q69 ∷
   rw 4 q72 ∷
   rw 1 q79 ∷
   rw 15 q75 ∷
   rw 12 q74 ∷
   rw 9 q74 ∷
   rw 6 q75 ∷
   rw 3 q74 ∷
   rw 7 q80 ∷
   rw 13 q67 ∷
   rw⁻ 12 q68 ∷
   rw⁻ 11 q69 ∷
   rw 10 q77 ∷
   rw⁻ 9 q69 ∷
   rw 10 q11 ∷
   rw 9 q68 ∷
   rw 10 q69 ∷
   rw 11 q78 ∷
   rw 12 q69 ∷
   rw 13 q72 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = eqn (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) (lem-S2-at1023-ᵖ-1)
  q82 : Eqn
  q82 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS12-TOFF103-CSd12-TOFF103)
  q83 : Eqn
  q83 = eqn (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) lem-S2-at1023-ᵖ-1

-- pass [X3 CSd30 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 3 q81 ∷
   rw 0 q82 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS12-TOFF103-CSd12-TOFF103)

-- pass [X3 CKd30 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 3 q81 ∷
   rw 0 q84 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = eqn (X3 ∷ CK30 ∷ X3 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS12-TOFF103-CSd12-TOFF103)

-- pass [X3 CK30 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X3 ∷ CK30 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 3 q81 ∷
   rw 0 q85 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = eqn (X3 ∷ CS03 ∷ X3 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS12-TOFF103-CSd12-TOFF103)

-- pass [X3 CS30 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X3 ∷ CS03 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 3 q81 ∷
   rw 0 q86 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = eqn [] (X1 ∷ X1 ∷ []) (wn 872 W)
  q88 : Eqn
  q88 = eqn [] (CK10 ∷ CK10⁻ ∷ []) (wn 2142 W)
  q89 : Eqn
  q89 = eqn (X1 ∷ CK10 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q90 : Eqn
  q90 = eqn (X1 ∷ X1 ∷ []) [] (wn 388 W)
  q91 : Eqn
  q91 = eqn (CK10⁻ ∷ CK10 ∷ []) [] (wn 2143 W)

-- pass [X1 CKd10 X1] [TOFF012 CS03 TOFF012 CSd03]: 7 steps
lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X1 ∷ CK10⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  (rw 7 q87 ∷
   rw 8 q88 ∷
   rw 9 q87 ∷
   rw⁻ 3 q89 ∷
   rw 2 q90 ∷
   rw 1 q91 ∷
   rw 0 q90 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-S2)
  q93 : Eqn
  q93 = eqn (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3)
  q94 : Eqn
  q94 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) lem-S2

-- pass [TOFF012 CS03 TOFF012 CSd03] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q92 ∷
   rw 0 q93 ∷
   rw⁻ 10 q94 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = eqn (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw⁻ 0 q95 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = eqn (X2 ∷ CK21 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [X2 CK21 X2] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X2-CK21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X2 ∷ CK21 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  (rw 0 q26 ∷
   rw 1 q27 ∷
   rw 2 q28 ∷
   rw 3 q27 ∷
   rw⁻ 4 q96 ∷
   rw 10 q30 ∷
   rw 9 q31 ∷
   rw 8 q32 ∷
   rw 7 q31 ∷ []) Eq.refl

-- resp S0 K0 CS01 TOFF023 CSd01 TOFF023 Kd0 Sd0: 1 steps
lem-resp-S0-K0-CS01-TOFF023-CSd01-TOFF023-Kd0-Sd0 : ⟪ (S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-resp-S0-K0-CS01-TOFF023-CSd01-TOFF023-Kd0-Sd0 = derive (S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ [])
  (rw⁻ 2 q55 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = eqn (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) lem-S2-at1203-ᵖ-1

-- resp S1 K1 CS01 TOFF123 CSd01 TOFF123 Kd1 Sd1: 1 steps
lem-resp-S1-K1-CS01-TOFF123-CSd01-TOFF123-Kd1-Sd1 : ⟪ (S1 ∷ K1 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-resp-S1-K1-CS01-TOFF123-CSd01-TOFF123-Kd1-Sd1 = derive (S1 ∷ K1 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ [])
  (rw⁻ 2 q97 ∷ []) Eq.refl

-- resp S2 K2 CS12 TOFF203 CSd12 TOFF203 Kd2 Sd2: 1 steps
lem-resp-S2-K2-CS12-TOFF203-CSd12-TOFF203-Kd2-Sd2 : ⟪ (S2 ∷ K2 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ K2⁻ ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ []) ⟫ʷ
lem-resp-S2-K2-CS12-TOFF203-CSd12-TOFF203-Kd2-Sd2 = derive (S2 ∷ K2 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ K2⁻ ∷ S2⁻ ∷ []) (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ [])
  (rw⁻ 2 q63 ∷ []) Eq.refl

private
  q98 : Eqn
  q98 = eqn (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) lem-S2-at2103-ᵖ-1

-- resp S2 K2 CS02 TOFF213 CSd02 TOFF213 Kd2 Sd2: 1 steps
lem-resp-S2-K2-CS02-TOFF213-CSd02-TOFF213-Kd2-Sd2 : ⟪ (S2 ∷ K2 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ K2⁻ ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ []) ⟫ʷ
lem-resp-S2-K2-CS02-TOFF213-CSd02-TOFF213-Kd2-Sd2 = derive (S2 ∷ K2 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ K2⁻ ∷ S2⁻ ∷ []) (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ [])
  (rw⁻ 2 q98 ∷ []) Eq.refl

-- resp S1 K1 CS12 TOFF103 CSd12 TOFF103 Kd1 Sd1: 1 steps
lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 : ⟪ (S1 ∷ K1 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 = derive (S1 ∷ K1 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ [])
  (rw⁻ 2 q83 ∷ []) Eq.refl
