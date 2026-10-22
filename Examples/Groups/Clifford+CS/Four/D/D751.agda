{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD751 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D751 (W : Ws) (Sᴰ : SD751) where

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
  lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 : St 1117
  lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 0 Sᴰ
  lem-X0-ROT : St 2668
  lem-X0-ROT = pickᴰ 1 Sᴰ
  lem-S2 : St 1778
  lem-S2 = pickᴰ 2 Sᴰ
  lem-C⟨SU'S⟩ : St 2669
  lem-C⟨SU'S⟩ = pickᴰ 3 Sᴰ
  lem-C⟨U'SU'⟩ : St 2670
  lem-C⟨U'SU'⟩ = pickᴰ 4 Sᴰ
  lem-PP-flip-ᵖ-1 : St 2671
  lem-PP-flip-ᵖ-1 = pickᴰ 5 Sᴰ
  lem-PP4 : St 2672
  lem-PP4 = pickᴰ 6 Sᴰ
  lem-ROT2≡E : St 2673
  lem-ROT2≡E = pickᴰ 7 Sᴰ
  lem-merge3 : St 2674
  lem-merge3 = pickᴰ 8 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 : St 2675
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 = pickᴰ 9 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : St 2676
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = pickᴰ 10 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 : St 2677
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 = pickᴰ 11 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2678
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 12 Sᴰ
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : St 2679
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = pickᴰ 13 Sᴰ

private
  q1 : Eqn
  q1 = eqn (X0 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X0 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CCZ123 ∷ []) (lem-X0-ROT)
  q2 : Eqn
  q2 = eqn (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ123 ∷ []) (lem-ROT2≡E)
  q3 : Eqn
  q3 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)

-- ROT-inv: 3 steps
lem-ROT-inv : ⟪ (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X0 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-ROT-inv = derive (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X0 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X0 ∷ []) []
  (rw 15 q1 ∷
   rw 0 q2 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) [] lem-PP4
  q5 : Eqn
  q5 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)
  q6 : Eqn
  q6 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q7 : Eqn
  q7 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q8 : Eqn
  q8 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)
  q9 : Eqn
  q9 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)

-- PPi=PP3^3: 17 steps
lem-PPi≡PP3ᵖ3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-PPi≡PP3ᵖ3 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw⁻ 4 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 3 q8 ∷
   rw 2 q7 ∷
   rw 1 q5 ∷
   rw 2 q6 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q9 ∷
   rw 0 q7 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-S2)
  q11 : Eqn
  q11 = eqn (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3)
  q12 : Eqn
  q12 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) lem-S2

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q10 ∷
   rw 0 q11 ∷
   rw⁻ 6 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = eqn (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3)

-- pass [TOFF012 CS03 TOFF012 CSd03] [X1 X3 TOFF102 CS13 TOFF102 CSd13 X1 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q10 ∷
   rw 0 q13 ∷
   rw⁻ 8 q12 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3)

-- pass [TOFF012 CS03 TOFF012 CSd03] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q10 ∷
   rw 0 q14 ∷
   rw⁻ 8 q12 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3)

-- pass [TOFF012 CS03 TOFF012 CSd03] [X0 X1 X3 TOFF102 CS13 TOFF102 CSd13 X0 X1 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q10 ∷
   rw 0 q15 ∷
   rw⁻ 10 q12 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q18 : Eqn
  q18 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q19 : Eqn
  q19 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q20 : Eqn
  q20 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q21 : Eqn
  q21 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q22 : Eqn
  q22 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q23 : Eqn
  q23 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q24 : Eqn
  q24 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q25 : Eqn
  q25 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q26 : Eqn
  q26 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (CS12 ∷ CCZ012 ∷ []) (lem-merge3)
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q29 : Eqn
  q29 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q30 : Eqn
  q30 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q31 : Eqn
  q31 = eqn (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 11 W)
  q32 : Eqn
  q32 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- merge3 @1023: 78 steps
lem-merge3-at1023 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ012 ∷ []) ⟫ʷ
lem-merge3-at1023 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (CS02 ∷ CCZ012 ∷ [])
  (rw 10 q16 ∷
   rw⁻ 9 q17 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q18 ∷
   rw 9 q19 ∷
   rw⁻ 8 q18 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 14 q20 ∷
   rw 13 q21 ∷
   rw 12 q22 ∷
   rw 11 q23 ∷
   rw 10 q19 ∷
   rw 9 q23 ∷
   rw 8 q24 ∷
   rw 7 q21 ∷
   rw 8 q25 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q18 ∷
   rw 7 q24 ∷
   rw⁻ 6 q18 ∷
   re 7 3 (CS03 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 12 q20 ∷
   rw 11 q21 ∷
   rw 10 q22 ∷
   rw 9 q23 ∷
   rw 8 q19 ∷
   rw 7 q23 ∷
   rw 6 q24 ∷
   rw 5 q21 ∷
   rw 6 q25 ∷
   re 6 8 (Toff012 ∷ []) ∷
   rw⁻ 4 q17 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q18 ∷
   rw 4 q19 ∷
   rw⁻ 3 q18 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 9 q20 ∷
   rw 8 q21 ∷
   rw 7 q22 ∷
   rw 6 q23 ∷
   rw 5 q19 ∷
   rw 4 q23 ∷
   rw 3 q24 ∷
   rw 2 q21 ∷
   rw 3 q25 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q18 ∷
   rw 2 q24 ∷
   rw⁻ 1 q18 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 0 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 7 q20 ∷
   rw 6 q21 ∷
   rw 5 q22 ∷
   rw 4 q23 ∷
   rw 3 q19 ∷
   rw 2 q23 ∷
   rw 1 q24 ∷
   rw 0 q21 ∷
   rw 1 q25 ∷
   re 1 8 (Toff012 ∷ []) ∷
   rw 1 q26 ∷
   rw 0 q27 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 1 q27 ∷
   rw 2 q28 ∷
   rw 3 q29 ∷
   rw 4 q28 ∷
   rw 5 q30 ∷
   rw 1 q31 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 2 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn [] (X3 ∷ X3 ∷ []) (wn 225 W)
  q34 : Eqn
  q34 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q35 : Eqn
  q35 = eqn [] (CS02 ∷ CS02⁻ ∷ []) (wn 1357 W)
  q36 : Eqn
  q36 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)

-- PP-g: 19 steps
lem-PP-g : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ
lem-PP-g = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (CS12 ∷ CCZ012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ [])
  (rw 4 q33 ∷
   rw 5 q34 ∷
   rw 6 q6 ∷
   rw 7 q35 ∷
   rw 8 q6 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q6 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q7 ∷
   rw 7 q34 ∷
   rw 8 q6 ∷
   rw 9 q36 ∷
   rw 10 q6 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 11 q6 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q7 ∷
   rw 9 q33 ∷
   rw 0 q26 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0
  q38 : Eqn
  q38 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [Kd0 TOFF012 CS03 TOFF012 CSd03 K0]: 37 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = derive (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ [])
  (rw 12 q33 ∷
   rw 13 q34 ∷
   rw 14 q6 ∷
   rw 15 q35 ∷
   rw 16 q6 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q6 ∷
   re 15 3 (CS03⁻ ∷ []) ∷
   rw 16 q7 ∷
   rw 15 q34 ∷
   rw 16 q6 ∷
   rw 17 q36 ∷
   rw 18 q6 ∷
   re 16 3 (CS03⁻ ∷ []) ∷
   rw 19 q6 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q7 ∷
   rw 17 q33 ∷
   rw⁻ 6 q37 ∷
   rw 5 q38 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 4 q8 ∷
   rw 3 q7 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 2 q9 ∷
   rw 1 q7 ∷
   rw 0 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ []) lem-C⟨SU'S⟩
  q40 : Eqn
  q40 = eqn (CS02 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CS02 ∷ []) (CK20⁻ ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ []) (wn 2473 W)
  q41 : Eqn
  q41 = eqn (CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02⁻ ∷ []) (CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ []) (wn 2474 W)
  q42 : Eqn
  q42 = eqn (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (lem-C⟨U'SU'⟩)

-- REL0: 56 steps
lem-REL0 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ
lem-REL0 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ [])
  (rw⁻ 0 q39 ∷
   rw 6 q6 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   re 2 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 2 q40 ∷
   rw 3 q6 ∷
   re 1 3 (CK30⁻ ∷ []) ∷
   rw 4 q6 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 5 q6 ∷
   re 3 3 (CK30 ∷ []) ∷
   rw 6 q6 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q6 ∷
   re 5 3 (CK30⁻ ∷ []) ∷
   rw 8 q6 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q6 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q7 ∷
   rw 14 q6 ∷
   re 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q7 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   re 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 10 q41 ∷
   rw 11 q6 ∷
   re 9 3 (CK30⁻ ∷ []) ∷
   rw 12 q6 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   rw 13 q6 ∷
   re 11 3 (CK30 ∷ []) ∷
   rw 14 q6 ∷
   re 12 3 (CS03⁻ ∷ []) ∷
   rw 15 q6 ∷
   re 13 3 (CK30⁻ ∷ []) ∷
   rw 16 q6 ∷
   re 14 3 (CS03⁻ ∷ []) ∷
   rw 17 q6 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q7 ∷
   rw 0 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = eqn (S0 ∷ K0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (wn 2475 W)
  q44 : Eqn
  q44 = eqn (K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (wn 2476 W)
  q45 : Eqn
  q45 = eqn (S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (X0 ∷ S0 ∷ S0 ∷ S0 ∷ []) (wn 2477 W)
  q46 : Eqn
  q46 = eqn (S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012)
  q47 : Eqn
  q47 = eqn (S0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (X0 ∷ []) (wn 2478 W)
  q48 : Eqn
  q48 = eqn (X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-PP-flip-ᵖ-1)

-- spell Gad(t=0, W=(), d=SK, e=-1) -> Gad(t=0, W=(), d=SdKdSd, e=1): 8 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ : ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ = derive (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ [])
  (rw 0 q43 ∷
   rw 12 q44 ∷
   rw 3 q45 ∷
   rw 6 q46 ∷
   rw 5 q46 ∷
   rw 4 q46 ∷
   rw 8 q47 ∷
   rw 3 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (S0 ∷ K0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (wn 2479 W)
  q50 : Eqn
  q50 = eqn (K0⁻ ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (wn 2480 W)
  q51 : Eqn
  q51 = eqn (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (X0 ∷ S0 ∷ S0 ∷ ι ∷ ι ∷ []) (wn 2481 W)
  q52 : Eqn
  q52 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q53 : Eqn
  q53 = eqn (ι ∷ CS02 ∷ []) (CS02 ∷ ι ∷ []) (wn 1739 W)
  q54 : Eqn
  q54 = eqn (ι ∷ Toff012 ∷ []) (Toff012 ∷ ι ∷ []) (wn 1738 W)
  q55 : Eqn
  q55 = eqn (ι ∷ CS02⁻ ∷ []) (CS02⁻ ∷ ι ∷ []) (wn 1740 W)
  q56 : Eqn
  q56 = eqn (S0 ∷ S0 ∷ ι ∷ ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (X0 ∷ []) (wn 2482 W)

-- spell Gad(t=0, W=(), d=SK, e=-1) -> Gad(t=0, W=(), d=SdKSS, e=1): 47 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡1⟩ : ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡1⟩ = derive (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ [])
  (rw 0 q49 ∷
   rw 14 q50 ∷
   rw 4 q51 ∷
   rw 10 q6 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 8 q52 ∷
   rw 9 q53 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q52 ∷
   rw 10 q7 ∷
   rw 9 q54 ∷
   rw 12 q6 ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   rw 10 q52 ∷
   rw 11 q55 ∷
   rw 12 q6 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   rw⁻ 11 q52 ∷
   rw 12 q7 ∷
   rw 11 q54 ∷
   rw 9 q6 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 7 q52 ∷
   rw 8 q53 ∷
   rw 9 q6 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q52 ∷
   rw 9 q7 ∷
   rw 8 q54 ∷
   rw 11 q6 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 9 q52 ∷
   rw 10 q55 ∷
   rw 11 q6 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw⁻ 10 q52 ∷
   rw 11 q7 ∷
   rw 10 q54 ∷
   rw 6 q46 ∷
   rw 5 q46 ∷
   rw 9 q56 ∷
   rw 4 q48 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn [] (K0 ∷ S0 ∷ S0 ∷ K0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (wn 2483 W)
  q58 : Eqn
  q58 = eqn [] (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (wn 2484 W)
  q59 : Eqn
  q59 = eqn (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (X0 ∷ ι ∷ []) (wn 2485 W)
  q60 : Eqn
  q60 = eqn (ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) (X0 ∷ []) (wn 2486 W)

-- spell Gad(t=0, W=(), d=1, e=-1) -> Gad(t=0, W=(), d=KSSK, e=1): 25 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ [])
  (rw 0 q57 ∷
   rw 12 q58 ∷
   rw 4 q59 ∷
   rw 7 q6 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 5 q52 ∷
   rw 6 q53 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q52 ∷
   rw 7 q7 ∷
   rw 6 q54 ∷
   rw 9 q6 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 7 q52 ∷
   rw 8 q55 ∷
   rw 9 q6 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw⁻ 8 q52 ∷
   rw 9 q7 ∷
   rw 8 q54 ∷
   rw 9 q60 ∷
   rw 4 q48 ∷ []) Eq.refl
