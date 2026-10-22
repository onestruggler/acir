{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD781 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D781 (W : Ws) (Sᴰ : SD781) where

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
  lem-conjF : St 3462
  lem-conjF = pickᴰ 0 Sᴰ
  lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X2-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X2-X3-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X3-X2-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3-X2-X2-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3-X3-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X2-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X2-X3-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3 : St 3463
  lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X2-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X2-X3-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X3-X2-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3-X2-X2-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3-X3-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X2-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X2-X3-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3 = pickᴰ 1 Sᴰ
  lem-P-krk : St 3464
  lem-P-krk = pickᴰ 2 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (X3 ∷ X3 ∷ []) (wn 225 W)
  q2 : Eqn
  q2 = eqn [] (S0 ∷ S0⁻ ∷ []) (wn 1732 W)
  q3 : Eqn
  q3 = eqn [] (K0 ∷ K0⁻ ∷ []) (wn 116 W)
  q4 : Eqn
  q4 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q5 : Eqn
  q5 = eqn [] (CS02 ∷ CS02⁻ ∷ []) (wn 1357 W)
  q6 : Eqn
  q6 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q7 : Eqn
  q7 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q8 : Eqn
  q8 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)
  q9 : Eqn
  q9 = eqn [] (K0⁻ ∷ K0 ∷ []) (wn 54 W)
  q10 : Eqn
  q10 = eqn [] (S0⁻ ∷ S0 ∷ []) (wn 1726 W)
  q11 : Eqn
  q11 = eqn [] (X2 ∷ X2 ∷ []) (wn 871 W)
  q12 : Eqn
  q12 = eqn [] (S1 ∷ S1⁻ ∷ []) (wn 2578 W)
  q13 : Eqn
  q13 = eqn [] (K1 ∷ K1⁻ ∷ []) (wn 2579 W)
  q14 : Eqn
  q14 = eqn [] (Toff102 ∷ Toff102 ∷ []) (wn 1377 W)
  q15 : Eqn
  q15 = eqn [] (CS13 ∷ CS13⁻ ∷ []) (wn 1376 W)
  q16 : Eqn
  q16 = eqn [] (CS13⁻ ∷ CS13 ∷ []) (wn 1378 W)
  q17 : Eqn
  q17 = eqn [] (K1⁻ ∷ K1 ∷ []) (wn 1510 W)
  q18 : Eqn
  q18 = eqn [] (S1⁻ ∷ S1 ∷ []) (wn 2580 W)
  q19 : Eqn
  q19 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (CZ01 ∷ Sw01 ∷ []) (lem-P-krk)
  q20 : Eqn
  q20 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ CZ01 ∷ Sw01 ∷ []) (CZ01 ∷ Sw01 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (lem-conjF)
  q21 : Eqn
  q21 = eqn (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X3 ∷ X2 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ X2 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X3 ∷ X2 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ X2 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X2-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X2-X3-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X3-X2-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3-X2-X2-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3-X3-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X2-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X2-X3-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3)
  q22 : Eqn
  q22 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (CZ01 ∷ Sw01 ∷ []) lem-P-krk
  q23 : Eqn
  q23 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)
  q24 : Eqn
  q24 = eqn (X2 ∷ X2 ∷ []) [] (wn 389 W)
  q25 : Eqn
  q25 = eqn (S0⁻ ∷ S0 ∷ []) [] (wn 2487 W)
  q26 : Eqn
  q26 = eqn (K0⁻ ∷ K0 ∷ []) [] (wn 1339 W)
  q27 : Eqn
  q27 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)
  q28 : Eqn
  q28 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)
  q29 : Eqn
  q29 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)
  q30 : Eqn
  q30 = eqn (K0 ∷ K0⁻ ∷ []) [] (wn 1846 W)
  q31 : Eqn
  q31 = eqn (S0 ∷ S0⁻ ∷ []) [] (wn 1728 W)
  q32 : Eqn
  q32 = eqn (S1⁻ ∷ S1 ∷ []) [] (wn 2581 W)
  q33 : Eqn
  q33 = eqn (K1⁻ ∷ K1 ∷ []) [] (wn 1509 W)
  q34 : Eqn
  q34 = eqn (CS13⁻ ∷ CS13 ∷ []) [] (wn 1379 W)
  q35 : Eqn
  q35 = eqn (Toff102 ∷ Toff102 ∷ []) [] (wn 1380 W)
  q36 : Eqn
  q36 = eqn (CS13 ∷ CS13⁻ ∷ []) [] (wn 1381 W)
  q37 : Eqn
  q37 = eqn (K1 ∷ K1⁻ ∷ []) [] (wn 2582 W)
  q38 : Eqn
  q38 = eqn (S1 ∷ S1⁻ ∷ []) [] (wn 2583 W)

-- R0 P -> P Q: 340 steps
lem-R0-P--⟶-P-Q : ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-R0-P--⟶-P-Q = derive (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ [])
  (rw 32 q1 ∷
   rw 33 q2 ∷
   rw 34 q3 ∷
   rw 35 q4 ∷
   rw 36 q5 ∷
   rw 37 q4 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q4 ∷
   re 36 3 (CS03⁻ ∷ []) ∷
   rw 37 q6 ∷
   rw 36 q7 ∷
   rw 37 q4 ∷
   rw 38 q8 ∷
   rw 39 q4 ∷
   re 37 3 (CS03⁻ ∷ []) ∷
   rw 40 q4 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q6 ∷
   rw 38 q7 ∷
   rw 39 q9 ∷
   rw 40 q10 ∷
   rw 41 q1 ∷
   rw 42 q11 ∷
   rw 43 q2 ∷
   rw 44 q3 ∷
   rw 45 q4 ∷
   rw 46 q5 ∷
   rw 47 q4 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 48 q4 ∷
   re 46 3 (CS03⁻ ∷ []) ∷
   rw 47 q6 ∷
   rw 46 q7 ∷
   rw 47 q4 ∷
   rw 48 q8 ∷
   rw 49 q4 ∷
   re 47 3 (CS03⁻ ∷ []) ∷
   rw 50 q4 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 49 q6 ∷
   rw 48 q7 ∷
   rw 49 q9 ∷
   rw 50 q10 ∷
   rw 51 q11 ∷
   rw 52 q11 ∷
   rw 53 q1 ∷
   rw 54 q2 ∷
   rw 55 q3 ∷
   rw 56 q4 ∷
   rw 57 q5 ∷
   rw 58 q4 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 59 q4 ∷
   re 57 3 (CS03⁻ ∷ []) ∷
   rw 58 q6 ∷
   rw 57 q7 ∷
   rw 58 q4 ∷
   rw 59 q8 ∷
   rw 60 q4 ∷
   re 58 3 (CS03⁻ ∷ []) ∷
   rw 61 q4 ∷
   re 59 3 (CS03 ∷ []) ∷
   rw 60 q6 ∷
   rw 59 q7 ∷
   rw 60 q9 ∷
   rw 61 q10 ∷
   rw 62 q11 ∷
   rw 63 q1 ∷
   rw 64 q1 ∷
   rw 65 q12 ∷
   rw 66 q13 ∷
   rw 67 q14 ∷
   rw 68 q15 ∷
   rw 69 q14 ∷
   rw 70 q16 ∷
   rw 71 q17 ∷
   rw 72 q18 ∷
   rw 73 q1 ∷
   rw 74 q11 ∷
   rw 75 q12 ∷
   rw 76 q13 ∷
   rw 77 q14 ∷
   rw 78 q15 ∷
   rw 79 q14 ∷
   rw 80 q16 ∷
   rw 81 q17 ∷
   rw 82 q18 ∷
   rw 83 q11 ∷
   rw 84 q11 ∷
   rw 85 q1 ∷
   rw 86 q12 ∷
   rw 87 q13 ∷
   rw 88 q14 ∷
   rw 89 q15 ∷
   rw 90 q14 ∷
   rw 91 q16 ∷
   rw 92 q17 ∷
   rw 93 q18 ∷
   rw 94 q11 ∷
   rw 95 q1 ∷
   rw 96 q1 ∷
   rw 97 q2 ∷
   rw 98 q3 ∷
   rw 99 q4 ∷
   rw 100 q5 ∷
   rw 101 q4 ∷
   re 99 3 (CS03 ∷ []) ∷
   rw 102 q4 ∷
   re 100 3 (CS03⁻ ∷ []) ∷
   rw 101 q6 ∷
   rw 100 q7 ∷
   rw 101 q4 ∷
   rw 102 q8 ∷
   rw 103 q4 ∷
   re 101 3 (CS03⁻ ∷ []) ∷
   rw 104 q4 ∷
   re 102 3 (CS03 ∷ []) ∷
   rw 103 q6 ∷
   rw 102 q7 ∷
   rw 103 q9 ∷
   rw 104 q10 ∷
   rw 105 q1 ∷
   rw 106 q11 ∷
   rw 107 q2 ∷
   rw 108 q3 ∷
   rw 109 q4 ∷
   rw 110 q5 ∷
   rw 111 q4 ∷
   re 109 3 (CS03 ∷ []) ∷
   rw 112 q4 ∷
   re 110 3 (CS03⁻ ∷ []) ∷
   rw 111 q6 ∷
   rw 110 q7 ∷
   rw 111 q4 ∷
   rw 112 q8 ∷
   rw 113 q4 ∷
   re 111 3 (CS03⁻ ∷ []) ∷
   rw 114 q4 ∷
   re 112 3 (CS03 ∷ []) ∷
   rw 113 q6 ∷
   rw 112 q7 ∷
   rw 113 q9 ∷
   rw 114 q10 ∷
   rw 115 q11 ∷
   rw 116 q11 ∷
   rw 117 q1 ∷
   rw 118 q2 ∷
   rw 119 q3 ∷
   rw 120 q4 ∷
   rw 121 q5 ∷
   rw 122 q4 ∷
   re 120 3 (CS03 ∷ []) ∷
   rw 123 q4 ∷
   re 121 3 (CS03⁻ ∷ []) ∷
   rw 122 q6 ∷
   rw 121 q7 ∷
   rw 122 q4 ∷
   rw 123 q8 ∷
   rw 124 q4 ∷
   re 122 3 (CS03⁻ ∷ []) ∷
   rw 125 q4 ∷
   re 123 3 (CS03 ∷ []) ∷
   rw 124 q6 ∷
   rw 123 q7 ∷
   rw 124 q9 ∷
   rw 125 q10 ∷
   rw 126 q11 ∷
   rw 127 q1 ∷
   rw 8 q19 ∷
   rw 0 q20 ∷
   rw 2 q21 ∷
   rw⁻ 0 q22 ∷
   rw 119 q23 ∷
   rw 118 q24 ∷
   rw 117 q25 ∷
   rw 116 q26 ∷
   rw 115 q27 ∷
   rw 116 q4 ∷
   re 115 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 117 q6 ∷
   re 114 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 116 q6 ∷
   rw 115 q28 ∷
   rw 114 q6 ∷
   rw 113 q27 ∷
   rw 114 q4 ∷
   re 113 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 115 q6 ∷
   re 112 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 114 q6 ∷
   rw 113 q29 ∷
   rw 112 q6 ∷
   rw 111 q30 ∷
   rw 110 q31 ∷
   rw 109 q23 ∷
   rw 108 q24 ∷
   rw 107 q24 ∷
   rw 106 q25 ∷
   rw 105 q26 ∷
   rw 104 q27 ∷
   rw 105 q4 ∷
   re 104 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 106 q6 ∷
   re 103 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 105 q6 ∷
   rw 104 q28 ∷
   rw 103 q6 ∷
   rw 102 q27 ∷
   rw 103 q4 ∷
   re 102 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 104 q6 ∷
   re 101 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 103 q6 ∷
   rw 102 q29 ∷
   rw 101 q6 ∷
   rw 100 q30 ∷
   rw 99 q31 ∷
   rw 98 q24 ∷
   rw 97 q23 ∷
   rw 96 q25 ∷
   rw 95 q26 ∷
   rw 94 q27 ∷
   rw 95 q4 ∷
   re 94 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 96 q6 ∷
   re 93 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 95 q6 ∷
   rw 94 q28 ∷
   rw 93 q6 ∷
   rw 92 q27 ∷
   rw 93 q4 ∷
   re 92 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 94 q6 ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 93 q6 ∷
   rw 92 q29 ∷
   rw 91 q6 ∷
   rw 90 q30 ∷
   rw 89 q31 ∷
   rw 88 q23 ∷
   rw 87 q23 ∷
   rw 86 q24 ∷
   rw 85 q32 ∷
   rw 84 q33 ∷
   rw 83 q34 ∷
   rw 82 q35 ∷
   rw 81 q36 ∷
   rw 80 q35 ∷
   rw 79 q37 ∷
   rw 78 q38 ∷
   rw 77 q23 ∷
   rw 76 q24 ∷
   rw 75 q24 ∷
   rw 74 q32 ∷
   rw 73 q33 ∷
   rw 72 q34 ∷
   rw 71 q35 ∷
   rw 70 q36 ∷
   rw 69 q35 ∷
   rw 68 q37 ∷
   rw 67 q38 ∷
   rw 66 q24 ∷
   rw 65 q23 ∷
   rw 64 q32 ∷
   rw 63 q33 ∷
   rw 62 q34 ∷
   rw 61 q35 ∷
   rw 60 q36 ∷
   rw 59 q35 ∷
   rw 58 q37 ∷
   rw 57 q38 ∷
   rw 56 q23 ∷
   rw 55 q23 ∷
   rw 54 q24 ∷
   rw 53 q25 ∷
   rw 52 q26 ∷
   rw 51 q27 ∷
   rw 52 q4 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q6 ∷
   re 50 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 52 q6 ∷
   rw 51 q28 ∷
   rw 50 q6 ∷
   rw 49 q27 ∷
   rw 50 q4 ∷
   re 49 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 51 q6 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q6 ∷
   rw 49 q29 ∷
   rw 48 q6 ∷
   rw 47 q30 ∷
   rw 46 q31 ∷
   rw 45 q23 ∷
   rw 44 q24 ∷
   rw 43 q24 ∷
   rw 42 q25 ∷
   rw 41 q26 ∷
   rw 40 q27 ∷
   rw 41 q4 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   re 39 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   rw 40 q28 ∷
   rw 39 q6 ∷
   rw 38 q27 ∷
   rw 39 q4 ∷
   re 38 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 40 q6 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q6 ∷
   rw 38 q29 ∷
   rw 37 q6 ∷
   rw 36 q30 ∷
   rw 35 q31 ∷
   rw 34 q24 ∷
   rw 33 q23 ∷
   rw 32 q25 ∷
   rw 31 q26 ∷
   rw 30 q27 ∷
   rw 31 q4 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   re 29 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   rw 30 q28 ∷
   rw 29 q6 ∷
   rw 28 q27 ∷
   rw 29 q4 ∷
   re 28 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   rw 28 q29 ∷
   rw 27 q6 ∷
   rw 26 q30 ∷
   rw 25 q31 ∷
   rw 24 q23 ∷ []) Eq.refl
