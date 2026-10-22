{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD510 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D510 (W : Ws) (Sᴰ : SD510) where

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
  lem-CCZ023-T : St 0
  lem-CCZ023-T = pickᴰ 0 Sᴰ
  lem-CCZ123-CX30 : St 1
  lem-CCZ123-CX30 = pickᴰ 1 Sᴰ
  lem-CCZ312-CCZ012 : St 2
  lem-CCZ312-CCZ012 = pickᴰ 2 Sᴰ
  lem-CS13-passes-T : St 3
  lem-CS13-passes-T = pickᴰ 3 Sᴰ
  lem-N23-T : St 4
  lem-N23-T = pickᴰ 4 Sᴰ
  lem-comm-CCZ012-CCZ013 : St 5
  lem-comm-CCZ012-CCZ013 = pickᴰ 5 Sᴰ
  lem-CS12-passes-T : St 6
  lem-CS12-passes-T = pickᴰ 6 Sᴰ
  lem-comm-CCZ012-CSd03 : St 7
  lem-comm-CCZ012-CSd03 = pickᴰ 7 Sᴰ
  lem-comm-CCZ123-CCZ023 : St 8
  lem-comm-CCZ123-CCZ023 = pickᴰ 8 Sᴰ
  lem-comm-CCZ123-CSd02 : St 9
  lem-comm-CCZ123-CSd02 = pickᴰ 9 Sᴰ
  lem-comm-CCZ123-CSd03 : St 10
  lem-comm-CCZ123-CSd03 = pickᴰ 10 Sᴰ
  lem-CZ13-passes-T : St 11
  lem-CZ13-passes-T = pickᴰ 11 Sᴰ
  lem-comm-CCZ012-CS03 : St 12
  lem-comm-CCZ012-CS03 = pickᴰ 12 Sᴰ
  lem-comm-CCZ013-CCZ012 : St 13
  lem-comm-CCZ013-CCZ012 = pickᴰ 13 Sᴰ
  lem-comm-CCZ013-CS02 : St 14
  lem-comm-CCZ013-CS02 = pickᴰ 14 Sᴰ
  lem-comm-CCZ013-CS12 : St 15
  lem-comm-CCZ013-CS12 = pickᴰ 15 Sᴰ
  lem-CCZ023-passes-CX31 : St 16
  lem-CCZ023-passes-CX31 = pickᴰ 16 Sᴰ
  lem-comm-CCZ023-CCZ012 : St 17
  lem-comm-CCZ023-CCZ012 = pickᴰ 17 Sᴰ
  lem-Rk : St 18
  lem-Rk = pickᴰ 18 Sᴰ
  lem-SW13-Rk : St 19
  lem-SW13-Rk = pickᴰ 19 Sᴰ
  lem-PUinv : St 20
  lem-PUinv = pickᴰ 20 Sᴰ
  lem-pass-CS12-vs-CS03 : St 21
  lem-pass-CS12-vs-CS03 = pickᴰ 21 Sᴰ
  lem-pass-CSd13-vs-CS02 : St 22
  lem-pass-CSd13-vs-CS02 = pickᴰ 22 Sᴰ
  lem-comm-CCZ012-CS13 : St 23
  lem-comm-CCZ012-CS13 = pickᴰ 23 Sᴰ
  lem-comm-CCZ012-CSd13 : St 24
  lem-comm-CCZ012-CSd13 = pickᴰ 24 Sᴰ
  lem-comm-CCZ013-CSd12 : St 25
  lem-comm-CCZ013-CSd12 = pickᴰ 25 Sᴰ
  lem-comm-CCZ013-CZ02 : St 26
  lem-comm-CCZ013-CZ02 = pickᴰ 26 Sᴰ
  lem-pass-CS13-vs-CS02 : St 27
  lem-pass-CS13-vs-CS02 = pickᴰ 27 Sᴰ
  lem-pass-CSd02-vs-CS13 : St 28
  lem-pass-CSd02-vs-CS13 = pickᴰ 28 Sᴰ
  lem-pass-CSd02-vs-CSd13 : St 29
  lem-pass-CSd02-vs-CSd13 = pickᴰ 29 Sᴰ
  lem-pass-S2-vs-CS13 : St 30
  lem-pass-S2-vs-CS13 = pickᴰ 30 Sᴰ
  lem-pass-S2-vs-CSd13 : St 31
  lem-pass-S2-vs-CSd13 = pickᴰ 31 Sᴰ
  lem-pass-Sd2-vs-CS13 : St 32
  lem-pass-Sd2-vs-CS13 = pickᴰ 32 Sᴰ
  lem-pass-Sd2-vs-CSd13 : St 33
  lem-pass-Sd2-vs-CSd13 = pickᴰ 33 Sᴰ
  lem-pass-CS12-vs-CSd03 : St 34
  lem-pass-CS12-vs-CSd03 = pickᴰ 34 Sᴰ
  lem-pass-CS12-vs-K0 : St 35
  lem-pass-CS12-vs-K0 = pickᴰ 35 Sᴰ
  lem-pass-CS12-vs-Kd0 : St 36
  lem-pass-CS12-vs-Kd0 = pickᴰ 36 Sᴰ
  lem-pass-CS12-vs-TOFF012 : St 37
  lem-pass-CS12-vs-TOFF012 = pickᴰ 37 Sᴰ
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 38
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 38 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS02 : St 39
  lem-pass-X3-CS30-X3-vs-CS02 = pickᴰ 39 Sᴰ
  lem-pass-X3-CS30-X3-vs-CSd02 : St 40
  lem-pass-X3-CS30-X3-vs-CSd02 = pickᴰ 40 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF013 : St 41
  lem-pass-X3-CS30-X3-vs-TOFF013 = pickᴰ 41 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS12 : St 42
  lem-pass-X3-CK30-X3-vs-CS12 = pickᴰ 42 Sᴰ
  lem-pass-X3-CK30-X3-vs-CSd12 : St 43
  lem-pass-X3-CK30-X3-vs-CSd12 = pickᴰ 43 Sᴰ
  lem-pass-X3-CK30-X3-vs-TOFF103 : St 44
  lem-pass-X3-CK30-X3-vs-TOFF103 = pickᴰ 44 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS12 : St 45
  lem-pass-X3-CKd30-X3-vs-CS12 = pickᴰ 45 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CSd12 : St 46
  lem-pass-X3-CKd30-X3-vs-CSd12 = pickᴰ 46 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF103 : St 47
  lem-pass-X3-CKd30-X3-vs-TOFF103 = pickᴰ 47 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS12 : St 48
  lem-pass-X3-CS30-X3-vs-CS12 = pickᴰ 48 Sᴰ
  lem-pass-X3-CS30-X3-vs-CSd12 : St 49
  lem-pass-X3-CS30-X3-vs-CSd12 = pickᴰ 49 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF103 : St 50
  lem-pass-X3-CS30-X3-vs-TOFF103 = pickᴰ 50 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS12 : St 51
  lem-pass-X3-CSd30-X3-vs-CS12 = pickᴰ 51 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CSd12 : St 52
  lem-pass-X3-CSd30-X3-vs-CSd12 = pickᴰ 52 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF103 : St 53
  lem-pass-X3-CSd30-X3-vs-TOFF103 = pickᴰ 53 Sᴰ

private
  q1 : Eqn
  q1 = eqn (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (wn 53 W)
  q2 : Eqn
  q2 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q3 : Eqn
  q3 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q5 : Eqn
  q5 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q6 : Eqn
  q6 = eqn (K0⁻ ∷ CZ02 ∷ K0 ∷ []) (CX20 ∷ []) (wn 1336 W)
  q7 : Eqn
  q7 = eqn [] (CX20 ∷ CX20 ∷ []) (wn 2 W)
  q8 : Eqn
  q8 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q10 : Eqn
  q10 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q11 : Eqn
  q11 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q12 : Eqn
  q12 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q13 : Eqn
  q13 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q14 : Eqn
  q14 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q15 : Eqn
  q15 = eqn (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 11 W)
  q16 : Eqn
  q16 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q17 : Eqn
  q17 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q18 : Eqn
  q18 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q19 : Eqn
  q19 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q20 : Eqn
  q20 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q21 : Eqn
  q21 = eqn (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 17 W)
  q22 : Eqn
  q22 = eqn (CX32 ∷ CCZ012 ∷ CX32 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz)
  q23 : Eqn
  q23 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q24 : Eqn
  q24 = eqn (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) (wn 19 W)
  q25 : Eqn
  q25 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q26 : Eqn
  q26 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q27 : Eqn
  q27 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q28 : Eqn
  q28 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q29 : Eqn
  q29 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q30 : Eqn
  q30 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q31 : Eqn
  q31 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q32 : Eqn
  q32 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q33 : Eqn
  q33 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q34 : Eqn
  q34 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q35 : Eqn
  q35 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q36 : Eqn
  q36 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q37 : Eqn
  q37 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q38 : Eqn
  q38 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q39 : Eqn
  q39 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q41 : Eqn
  q41 = eqn (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ []) lem-CCZ312-CCZ012
  q42 : Eqn
  q42 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wn 32 W)
  q43 : Eqn
  q43 = eqn (CCZ123 ∷ []) (CCZ123 ∷ []) (wn 1337 W)
  q44 : Eqn
  q44 = eqn (CCZ123 ∷ CX30 ∷ []) (CX30 ∷ CCZ123 ∷ []) lem-CCZ123-CX30
  q45 : Eqn
  q45 = eqn (K0 ∷ CCZ123 ∷ []) (CCZ123 ∷ K0 ∷ []) (low₁-comm (K) (CCZ))
  q46 : Eqn
  q46 = eqn (K0 ∷ CX20 ∷ K0⁻ ∷ []) (CZ02 ∷ []) (wn 1338 W)

-- T-CZ03-T: 145 steps
lem-T-CZ03-T : ⟪ (Toff012 ∷ CZ03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CZ03 ∷ []) ⟫ʷ
lem-T-CZ03-T = derive (Toff012 ∷ CZ03 ∷ Toff012 ∷ []) (CCZ123 ∷ CZ03 ∷ [])
  (rw 0 q1 ∷
   rw 4 q1 ∷
   rw 5 q2 ∷
   rw 4 q3 ∷
   re 3 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q2 ∷
   re 2 3 (CX30 ∷ []) ∷
   rw 3 q4 ∷
   rw 1 q2 ∷
   rw 2 q7 ∷
   rw 3 q2 ∷
   re 1 3 (CX30 ∷ []) ∷
   rw 4 q2 ∷
   re 2 3 (CX30 ∷ []) ∷
   rw 3 q4 ∷
   rw 5 q8 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q9 ∷
   rw 5 q10 ∷
   rw⁻ 4 q9 ∷
   re 5 3 (CX31 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q11 ∷
   rw 6 q12 ∷
   rw 5 q13 ∷
   rw 4 q12 ∷
   rw 3 q14 ∷
   rw 4 q15 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q9 ∷
   rw 3 q10 ∷
   rw⁻ 2 q9 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 6 q16 ∷
   rw 5 q17 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q18 ∷
   rw 7 q16 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q19 ∷
   rw 5 q16 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q20 ∷
   rw 5 q21 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   rw 3 q17 ∷
   rw 4 q22 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q23 ∷
   rw 6 q16 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q24 ∷
   rw 8 q16 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q18 ∷
   rw 3 q21 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q2 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q25 ∷
   rw 9 q2 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q25 ∷
   rw 11 q2 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q4 ∷
   rw 4 q26 ∷
   rw 7 q16 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q27 ∷
   rw 9 q16 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q28 ∷
   rw⁻ 10 q29 ∷
   rw 11 q30 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 4 q8 ∷
   rw 5 q31 ∷
   rw 6 q32 ∷
   rw 7 q33 ∷
   rw 8 q32 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q9 ∷
   rw 10 q34 ∷
   rw 11 q9 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q35 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   rw 5 q18 ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q36 ∷
   rw 3 q37 ∷
   rw 4 q38 ∷
   rw 5 q37 ∷
   rw 6 q34 ∷
   rw 2 q15 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q31 ∷
   rw 5 q39 ∷
   rw 6 q33 ∷
   rw 7 q39 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q9 ∷
   rw 9 q36 ∷
   rw 10 q9 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q40 ∷
   rw 3 q31 ∷
   rw 4 q32 ∷
   rw 5 q33 ∷
   rw 6 q32 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q34 ∷
   rw 9 q9 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q35 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   rw 4 q40 ∷
   rw⁻ 2 q41 ∷
   rw 3 q42 ∷
   rw 2 q43 ∷
   rw⁻ 1 q44 ∷
   rw 0 q45 ∷
   rw 4 q2 ∷
   rw 3 q5 ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw 1 q3 ∷
   rw 2 q46 ∷
   rw 3 q2 ∷
   re 1 3 (CZ03 ∷ []) ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ []) (lem-CCZ312-CCZ012)
  q48 : Eqn
  q48 = eqn (K0⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (CCZ))
  q49 : Eqn
  q49 = eqn (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wn 55 W)

-- E-T: 5 steps
lem-E-T : ⟪ (CCZ123 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-E-T = derive (CCZ123 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ123 ∷ [])
  (rw 1 q1 ∷
   rw⁻ 0 q45 ∷
   rw 1 q47 ∷
   rw⁻ 2 q48 ∷
   rw 0 q49 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q51 : Eqn
  q51 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q52 : Eqn
  q52 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q53 : Eqn
  q53 = eqn (K0⁻ ∷ K0 ∷ []) [] (wn 1339 W)
  q54 : Eqn
  q54 = eqn (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CCZ013)
  q55 : Eqn
  q55 = eqn [] (K0⁻ ∷ K0 ∷ []) (wn 54 W)

-- T-T13: 111 steps
lem-T-T13 : ⟪ (Toff012 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff012 ∷ []) ⟫ʷ
lem-T-T13 = derive (Toff012 ∷ Toff013 ∷ []) (Toff013 ∷ Toff012 ∷ [])
  (rw 0 q1 ∷
   rw 4 q2 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q25 ∷
   rw 8 q2 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q25 ∷
   rw 10 q2 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q50 ∷
   rw 11 q4 ∷
   rw 10 q50 ∷
   rw 9 q3 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   rw 7 q25 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   rw 5 q25 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw 3 q3 ∷
   rw 4 q51 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 4 q1 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q25 ∷
   rw 8 q2 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q25 ∷
   rw 10 q2 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 4 q2 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   rw⁻ 6 q25 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   rw⁻ 8 q25 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   rw 5 q52 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   rw⁻ 5 q5 ∷
   rw 6 q4 ∷
   rw 2 q53 ∷
   rw 1 q54 ∷
   rw 2 q55 ∷
   rw 3 q2 ∷
   rw 2 q5 ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q25 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q25 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   rw 4 q25 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   rw 2 q25 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 2 q52 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   rw 0 q3 ∷
   rw 1 q49 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q3 ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q25 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q25 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q50 ∷
   rw 0 q2 ∷
   rw⁻ 1 q3 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw⁻ 3 q25 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw⁻ 5 q25 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q50 ∷
   rw 1 q51 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw 1 q4 ∷
   rw 1 q49 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn [] (CX23 ∷ CX23 ∷ []) (wn 42 W)
  q57 : Eqn
  q57 = eqn (CX23 ∷ Toff012 ∷ CX23 ∷ []) (Toff012 ∷ []) (lem-N23-T)
  q58 : Eqn
  q58 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q59 : Eqn
  q59 = eqn (CX23 ∷ CS13 ∷ CX23 ∷ []) (CS13 ∷ CS12 ∷ CCZ123 ∷ []) (wn 1340 W)
  q60 : Eqn
  q60 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q61 : Eqn
  q61 = eqn (CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CCZ123 ∷ CS12⁻ ∷ CS13⁻ ∷ []) (wn 1341 W)
  q62 : Eqn
  q62 = eqn (CCZ023 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ023 ∷ CCZ123 ∷ []) (lem-CCZ023-T)
  q63 : Eqn
  q63 = eqn (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ []) lem-comm-CCZ123-CCZ023
  q64 : Eqn
  q64 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q65 : Eqn
  q65 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)
  q66 : Eqn
  q66 = eqn (CS02 ∷ Toff012 ∷ []) (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (wn 469 W)
  q67 : Eqn
  q67 = eqn (CCZ123 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CSd02)
  q68 : Eqn
  q68 = eqn (CCZ012 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ012 ∷ []) (wn 254 W)
  q69 : Eqn
  q69 = eqn (CS12 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS12 ∷ []) (wn 80 W)
  q70 : Eqn
  q70 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)
  q71 : Eqn
  q71 = eqn (CCZ123 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CSd03)
  q72 : Eqn
  q72 = eqn (CCZ012 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CSd03)
  q73 : Eqn
  q73 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wn 65 W)
  q74 : Eqn
  q74 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q75 : Eqn
  q75 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)

-- N23-PP3: 150 steps
lem-N23-PP3 : ⟪ (CX23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-N23-PP3 = derive (CX23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ CCZ012 ∷ CCZ123 ∷ [])
  (rw 4 q56 ∷
   rw 3 q56 ∷
   rw 2 q56 ∷
   rw 0 q57 ∷
   rw 4 q8 ∷
   rw⁻ 3 q58 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q9 ∷
   rw 3 q11 ∷
   rw⁻ 2 q9 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 1 q58 ∷
   rw 2 q59 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q9 ∷
   rw 2 q36 ∷
   rw 3 q9 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q36 ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q31 ∷
   rw 4 q39 ∷
   rw 5 q33 ∷
   rw 6 q39 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q36 ∷
   rw 9 q9 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q8 ∷
   rw 4 q31 ∷
   rw 5 q32 ∷
   rw 6 q33 ∷
   rw 7 q32 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q9 ∷
   rw 9 q34 ∷
   rw 10 q9 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q35 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   rw 4 q40 ∷
   rw 4 q57 ∷
   rw 8 q8 ∷
   rw⁻ 7 q58 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q9 ∷
   rw 7 q60 ∷
   rw⁻ 6 q9 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q58 ∷
   rw 6 q61 ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q31 ∷
   rw 6 q39 ∷
   rw 7 q33 ∷
   rw 8 q39 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q9 ∷
   rw 10 q36 ∷
   rw 11 q9 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 5 q8 ∷
   rw 6 q31 ∷
   rw 7 q32 ∷
   rw 8 q33 ∷
   rw 9 q32 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q9 ∷
   rw 11 q34 ∷
   rw 12 q9 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 6 q35 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 5 3 (CCZ023 ∷ []) ∷
   rw 6 q38 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q38 ∷
   rw 9 q9 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q40 ∷
   rw 3 q62 ∷
   rw⁻ 4 q63 ∷
   rw 7 q8 ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q31 ∷
   rw 7 q39 ∷
   rw 8 q33 ∷
   rw 9 q39 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q9 ∷
   rw 11 q36 ∷
   rw 12 q9 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q40 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q9 ∷
   rw 11 q11 ∷
   rw⁻ 10 q9 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q64 ∷
   rw⁻ 8 q33 ∷
   rw 7 q64 ∷
   rw⁻ 6 q31 ∷
   rw 7 q35 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q31 ∷
   rw 6 q39 ∷
   rw 7 q33 ∷
   rw 8 q39 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q9 ∷
   rw 10 q36 ∷
   rw 11 q9 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q40 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q9 ∷
   rw 10 q11 ∷
   rw⁻ 9 q9 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q64 ∷
   rw⁻ 7 q33 ∷
   rw 6 q64 ∷
   rw⁻ 5 q31 ∷
   rw 6 q35 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   rw 6 q65 ∷
   rw 5 q40 ∷
   rw 2 q66 ∷
   rw 6 q67 ∷
   rw 5 q68 ∷
   rw 4 q69 ∷
   rw 3 q70 ∷
   rw 5 q71 ∷
   rw 4 q72 ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q73 ∷
   rw⁻ 5 q74 ∷
   rw 6 q75 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   re 3 5 (CS03⁻ ∷ []) ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = eqn (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) (lem-CS12-passes-T)
  q77 : Eqn
  q77 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))

-- CS12 passes PP3: 20 steps
lem-CS12-passes-PP3 : ⟪ (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ []) ⟫ʷ
lem-CS12-passes-PP3 = derive (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ [])
  (rw 0 q76 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q73 ∷
   rw⁻ 3 q77 ∷
   rw 4 q75 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   re 1 5 (CS03 ∷ []) ∷
   rw 2 q76 ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q73 ∷
   rw⁻ 5 q74 ∷
   rw 6 q75 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   re 3 5 (CS03⁻ ∷ []) ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = eqn (CS13 ∷ Toff012 ∷ []) (Toff012 ∷ CS13 ∷ []) (lem-CS13-passes-T)
  q79 : Eqn
  q79 = eqn (CS12 ∷ CS02 ∷ []) (CS02 ∷ CS12 ∷ []) (wn 205 W)

-- CS13 passes PP3: 24 steps
lem-CS13-passes-PP3 : ⟪ (CS13 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS13 ∷ []) ⟫ʷ
lem-CS13-passes-PP3 = derive (CS13 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS13 ∷ [])
  (rw 0 q78 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 2 q79 ∷
   rw 3 q2 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 3 q4 ∷
   rw 2 q78 ∷
   rw 5 q2 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   rw 4 q69 ∷
   rw 5 q2 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 6 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 5 q4 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = eqn (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (wn 1343 W)
  q81 : Eqn
  q81 = eqn (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) (wn 96 W)
  q82 : Eqn
  q82 = eqn (CS01 ∷ CZ23 ∷ []) (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ))
  q83 : Eqn
  q83 = eqn (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) (wn 97 W)
  q84 : Eqn
  q84 = eqn (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CS03)
  q85 : Eqn
  q85 = eqn (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ []) (wn 1344 W)

-- CCZ012 passes PP3: 13 steps
lem-CCZ012-passes-PP3 : ⟪ (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-CCZ012-passes-PP3 = derive (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ [])
  (rw 0 q80 ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   re 3 3 (CZ13 ∷ []) ∷
   rw 3 q81 ∷
   rw⁻ 4 q82 ∷
   rw 5 q83 ∷
   re 6 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   re 2 5 (CS03 ∷ []) ∷
   rw 1 q84 ∷
   rw 2 q85 ∷
   rw 3 q72 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = eqn (CZ13 ∷ Toff012 ∷ []) (Toff012 ∷ CZ13 ∷ []) (lem-CZ13-passes-T)
  q87 : Eqn
  q87 = eqn (CZ12 ∷ CS02 ∷ []) (CS02 ∷ CZ12 ∷ []) (wn 1345 W)
  q88 : Eqn
  q88 = eqn (CZ12 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CZ12 ∷ []) (wn 1346 W)

-- CZ13 passes PP3: 24 steps
lem-CZ13-passes-PP3 : ⟪ (CZ13 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ13 ∷ []) ⟫ʷ
lem-CZ13-passes-PP3 = derive (CZ13 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ13 ∷ [])
  (rw 0 q86 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   re 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 2 q87 ∷
   rw 3 q2 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 4 q2 ∷
   re 2 3 (CZ13 ∷ []) ∷
   rw 3 q4 ∷
   rw 2 q86 ∷
   rw 5 q2 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   re 3 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   rw 4 q88 ∷
   rw 5 q2 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 6 q2 ∷
   re 4 3 (CZ13 ∷ []) ∷
   rw 5 q4 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = eqn (Toff102 ∷ []) (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (wn 1347 W)
  q90 : Eqn
  q90 = eqn (K1⁻ ∷ CZ13 ∷ K1 ∷ []) (CX31 ∷ []) (wn 1348 W)
  q91 : Eqn
  q91 = eqn [] (CX31 ∷ CX31 ∷ []) (wn 111 W)
  q92 : Eqn
  q92 = eqn (CCZ023 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CCZ012)
  q93 : Eqn
  q93 = eqn (CCZ023 ∷ CX31 ∷ []) (CX31 ∷ CCZ023 ∷ []) lem-CCZ023-passes-CX31
  q94 : Eqn
  q94 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q95 : Eqn
  q95 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q96 : Eqn
  q96 = eqn (K1 ∷ CX31 ∷ K1⁻ ∷ []) (CZ13 ∷ []) (wn 1349 W)

-- T1-CZ13-T1: 75 steps
lem-T1-CZ13-T1 : ⟪ (Toff102 ∷ CZ13 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CZ13 ∷ []) ⟫ʷ
lem-T1-CZ13-T1 = derive (Toff102 ∷ CZ13 ∷ Toff102 ∷ []) (CCZ023 ∷ CZ13 ∷ [])
  (rw 0 q89 ∷
   rw 4 q89 ∷
   rw 2 q90 ∷
   rw 1 q91 ∷
   rw 5 q16 ∷
   rw 4 q17 ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q18 ∷
   rw 6 q16 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q19 ∷
   rw 4 q16 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 3 q20 ∷
   rw 4 q21 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   rw 2 q17 ∷
   rw 3 q22 ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q23 ∷
   rw 5 q16 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 q24 ∷
   rw 7 q16 ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 6 q18 ∷
   rw 2 q21 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q25 ∷
   rw 8 q2 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q25 ∷
   rw 10 q2 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q4 ∷
   rw 3 q26 ∷
   rw 6 q16 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q27 ∷
   rw 8 q16 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q28 ∷
   rw⁻ 9 q29 ∷
   rw 10 q30 ∷
   re 7 5 (CS03 ∷ []) ∷
   rw 3 q8 ∷
   rw 4 q31 ∷
   rw 5 q32 ∷
   rw 6 q33 ∷
   rw 7 q32 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q9 ∷
   rw 9 q34 ∷
   rw 10 q9 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q35 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   rw 4 q18 ∷
   rw 3 q92 ∷
   rw 2 q42 ∷
   rw⁻ 1 q93 ∷
   re 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   rw 0 q94 ∷
   rw 1 q45 ∷
   rw 2 q95 ∷
   re 0 3 (CCZ023 ∷ []) ∷
   rw 1 q96 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = eqn [] (K0 ∷ K0⁻ ∷ []) (wn 116 W)
  q98 : Eqn
  q98 = eqn (K0⁻ ∷ CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ K0 ∷ []) (CK10 ∷ Toff023 ∷ CK10⁻ ∷ Toff023 ∷ []) (lem-Rk)
  q99 : Eqn
  q99 = eqn [] (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 1350 W)
  q100 : Eqn
  q100 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Toff023 ∷ CK10⁻ ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (CK30 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ []) (lem-SW13-Rk)
  q101 : Eqn
  q101 = eqn (K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (CK30 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ []) lem-PUinv

-- ROT-form: 7 steps
lem-ROT-form : ⟪ (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ []) ⟫ʷ
lem-ROT-form = derive (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ [])
  (rw 0 q97 ∷
   rw 6 q97 ∷
   rw 1 q98 ∷
   rw 5 q99 ∷
   rw 1 q99 ∷
   rw 4 q100 ∷
   rw⁻ 4 q101 ∷ []) Eq.refl

private
  q102 : Eqn
  q102 = eqn (CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CCZ012)

-- pass [CCZ013] [CCZ012]: 1 steps
lem-pass-CCZ013-vs-CCZ012 : ⟪ (CCZ013 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CCZ012 = derive (CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ013 ∷ [])
  (rw 0 q102 ∷ []) Eq.refl

-- pass [CCZ023] [CCZ012]: 1 steps
lem-pass-CCZ023-vs-CCZ012 : ⟪ (CCZ023 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-CCZ012 = derive (CCZ023 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ023 ∷ [])
  (rw 0 q92 ∷ []) Eq.refl

-- pass [CCZ012] [CS03]: 1 steps
lem-pass-CCZ012-vs-CS03 : ⟪ (CCZ012 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CS03 = derive (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ [])
  (rw 0 q84 ∷ []) Eq.refl

private
  q103 : Eqn
  q103 = eqn (CCZ013 ∷ CS02 ∷ []) (CS02 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS02)

-- pass [CCZ013] [CS02]: 1 steps
lem-pass-CCZ013-vs-CS02 : ⟪ (CCZ013 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CS02 = derive (CCZ013 ∷ CS02 ∷ []) (CS02 ∷ CCZ013 ∷ [])
  (rw 0 q103 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = eqn (CCZ013 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CZ02)

-- pass [CCZ013] [CZ02]: 1 steps
lem-pass-CCZ013-vs-CZ02 : ⟪ (CCZ013 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CZ02 = derive (CCZ013 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ013 ∷ [])
  (rw 0 q104 ∷ []) Eq.refl

private
  q105 : Eqn
  q105 = eqn (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS12)

-- pass [CCZ013] [CS12]: 1 steps
lem-pass-CCZ013-vs-CS12 : ⟪ (CCZ013 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CS12 = derive (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ [])
  (rw 0 q105 ∷ []) Eq.refl

private
  q106 : Eqn
  q106 = eqn (CCZ013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CSd12)

-- pass [CCZ013] [CSd12]: 1 steps
lem-pass-CCZ013-vs-CSd12 : ⟪ (CCZ013 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CSd12 = derive (CCZ013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ013 ∷ [])
  (rw 0 q106 ∷ []) Eq.refl

private
  q107 : Eqn
  q107 = eqn (CS02 ∷ Toff102 ∷ []) (Toff102 ∷ CS02 ∷ []) (wn 1351 W)
  q108 : Eqn
  q108 = eqn (CS13 ∷ CS02 ∷ []) (CS02 ∷ CS13 ∷ []) lem-pass-CS13-vs-CS02
  q109 : Eqn
  q109 = eqn (CS13⁻ ∷ CS02 ∷ []) (CS02 ∷ CS13⁻ ∷ []) lem-pass-CSd13-vs-CS02

-- pass [CS02] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-CS02-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-TOFF102-CS13-TOFF102-CSd13 = derive (CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02 ∷ [])
  (rw 0 q107 ∷
   rw⁻ 1 q108 ∷
   rw 2 q107 ∷
   rw⁻ 3 q109 ∷ []) Eq.refl

private
  q110 : Eqn
  q110 = eqn (CS02⁻ ∷ Toff102 ∷ []) (Toff102 ∷ CS02⁻ ∷ []) (wn 1352 W)
  q111 : Eqn
  q111 = eqn (CS02⁻ ∷ CS13 ∷ []) (CS13 ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CS13)
  q112 : Eqn
  q112 = eqn (CS02⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CSd13)

-- pass [CSd02] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-CSd02-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-TOFF102-CS13-TOFF102-CSd13 = derive (CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02⁻ ∷ [])
  (rw 0 q110 ∷
   rw 1 q111 ∷
   rw 2 q110 ∷
   rw 3 q112 ∷ []) Eq.refl

-- pass [CCZ012] [CSd03]: 1 steps
lem-pass-CCZ012-vs-CSd03 : ⟪ (CCZ012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CSd03 = derive (CCZ012 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ012 ∷ [])
  (rw 0 q72 ∷ []) Eq.refl

private
  q113 : Eqn
  q113 = eqn (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CS13)

-- pass [CCZ012] [CS13]: 1 steps
lem-pass-CCZ012-vs-CS13 : ⟪ (CCZ012 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CS13 = derive (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ [])
  (rw 0 q113 ∷ []) Eq.refl

private
  q114 : Eqn
  q114 = eqn (CCZ012 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CSd13)

-- pass [CCZ012] [CSd13]: 1 steps
lem-pass-CCZ012-vs-CSd13 : ⟪ (CCZ012 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CSd13 = derive (CCZ012 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ012 ∷ [])
  (rw 0 q114 ∷ []) Eq.refl

private
  q115 : Eqn
  q115 = eqn (S2 ∷ Toff102 ∷ []) (Toff102 ∷ S2 ∷ []) (wn 1353 W)
  q116 : Eqn
  q116 = eqn (S2 ∷ CS13 ∷ []) (CS13 ∷ S2 ∷ []) (lem-pass-S2-vs-CS13)
  q117 : Eqn
  q117 = eqn (S2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S2 ∷ []) (lem-pass-S2-vs-CSd13)

-- pass [S2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-S2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (S2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2 ∷ []) ⟫ʷ
lem-pass-S2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (S2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2 ∷ [])
  (rw 0 q115 ∷
   rw 1 q116 ∷
   rw 2 q115 ∷
   rw 3 q117 ∷ []) Eq.refl

private
  q118 : Eqn
  q118 = eqn (S2⁻ ∷ Toff102 ∷ []) (Toff102 ∷ S2⁻ ∷ []) (wn 1354 W)
  q119 : Eqn
  q119 = eqn (S2⁻ ∷ CS13 ∷ []) (CS13 ∷ S2⁻ ∷ []) (lem-pass-Sd2-vs-CS13)
  q120 : Eqn
  q120 = eqn (S2⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S2⁻ ∷ []) (lem-pass-Sd2-vs-CSd13)

-- pass [Sd2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-Sd2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (S2⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2⁻ ∷ []) ⟫ʷ
lem-pass-Sd2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (S2⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2⁻ ∷ [])
  (rw 0 q118 ∷
   rw 1 q119 ∷
   rw 2 q118 ∷
   rw 3 q120 ∷ []) Eq.refl

private
  q121 : Eqn
  q121 = eqn (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) (wn 90 W)
  q122 : Eqn
  q122 = eqn (CS12 ∷ CS03 ∷ []) (CS03 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CS03)

-- pass [CS12] [TOFF012 CS03 TOFF012]: 3 steps
lem-pass-CS12-vs-TOFF012-CS03-TOFF012 : ⟪ (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-TOFF012-CS03-TOFF012 = derive (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS12 ∷ [])
  (rw 0 q121 ∷
   rw 1 q122 ∷
   rw 2 q121 ∷ []) Eq.refl

private
  q123 : Eqn
  q123 = eqn [] (X3 ∷ X3 ∷ []) (wn 225 W)
  q124 : Eqn
  q124 = eqn [] (CK20 ∷ CK20⁻ ∷ []) (wn 1355 W)
  q125 : Eqn
  q125 = eqn (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q126 : Eqn
  q126 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)
  q127 : Eqn
  q127 = eqn (CK20⁻ ∷ CK20 ∷ []) [] (wn 1356 W)

-- pass [X3 CKd30 X3] [TOFF012 CS03 TOFF012 CSd03]: 19 steps
lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 7 q123 ∷
   rw 8 q2 ∷
   rw 9 q124 ∷
   rw 10 q2 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 11 q2 ∷
   re 9 3 (CK30⁻ ∷ []) ∷
   rw 10 q4 ∷
   rw 9 q123 ∷
   rw⁻ 3 q125 ∷
   rw 2 q126 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 2 q127 ∷
   rw 1 q4 ∷
   rw 0 q126 ∷ []) Eq.refl

private
  q128 : Eqn
  q128 = eqn (CS12 ∷ K0⁻ ∷ []) (K0⁻ ∷ CS12 ∷ []) (lem-pass-CS12-vs-Kd0)
  q129 : Eqn
  q129 = eqn (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) (lem-pass-CS12-vs-TOFF012)
  q130 : Eqn
  q130 = eqn (CS12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS12 ∷ []) (lem-pass-CS12-vs-CSd03)
  q131 : Eqn
  q131 = eqn (CS12 ∷ K0 ∷ []) (K0 ∷ CS12 ∷ []) (lem-pass-CS12-vs-K0)

-- pass [CS12] [Kd0 TOFF012 CS03 TOFF012 CSd03 K0]: 6 steps
lem-pass-CS12-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : ⟪ (CS12 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = derive (CS12 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ CS12 ∷ [])
  (rw 0 q128 ∷
   rw 1 q129 ∷
   rw 2 q122 ∷
   rw 3 q129 ∷
   rw 4 q130 ∷
   rw 5 q131 ∷ []) Eq.refl

-- pass [CS12] [Kd0 CS03 TOFF012 CSd03 TOFF012 K0]: 6 steps
lem-pass-CS12-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 : ⟪ (CS12 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 = derive (CS12 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ []) (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ CS12 ∷ [])
  (rw 0 q128 ∷
   rw 1 q122 ∷
   rw 2 q129 ∷
   rw 3 q130 ∷
   rw 4 q129 ∷
   rw 5 q131 ∷ []) Eq.refl

private
  q132 : Eqn
  q132 = eqn (X3 ∷ CS03 ∷ X3 ∷ Toff013 ∷ []) (Toff013 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF013)
  q133 : Eqn
  q133 = eqn (X3 ∷ CS03 ∷ X3 ∷ CS02 ∷ []) (CS02 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS02)
  q134 : Eqn
  q134 = eqn (X3 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CSd02)

-- pass [X3 CS30 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CS30-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X3 ∷ CS03 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 0 q132 ∷
   rw 1 q133 ∷
   rw 2 q132 ∷
   rw 3 q134 ∷ []) Eq.refl

-- pass [CCZ123] [CSd03]: 1 steps
lem-pass-CCZ123-vs-CSd03 : ⟪ (CCZ123 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-CSd03 = derive (CCZ123 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ123 ∷ [])
  (rw 0 q71 ∷ []) Eq.refl

private
  q135 : Eqn
  q135 = eqn [] (CS02 ∷ CS02⁻ ∷ []) (wn 1357 W)
  q136 : Eqn
  q136 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q137 : Eqn
  q137 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)
  q138 : Eqn
  q138 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)
  q139 : Eqn
  q139 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)

-- pass [X3 CK30 X3] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 0 q2 ∷
   rw 1 q135 ∷
   rw 2 q2 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q136 ∷
   rw 2 q2 ∷
   rw 3 q137 ∷
   rw 4 q2 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 5 q2 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q4 ∷
   rw 3 q136 ∷
   rw⁻ 4 q125 ∷
   rw 12 q2 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q4 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   rw 11 q138 ∷
   rw 10 q4 ∷
   rw 9 q139 ∷
   rw 10 q2 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   rw 9 q70 ∷
   rw 8 q4 ∷
   rw 7 q139 ∷ []) Eq.refl

private
  q140 : Eqn
  q140 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ []) (Toff103 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF103)
  q141 : Eqn
  q141 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS12)
  q142 : Eqn
  q142 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CSd12)

-- pass [X3 CSd30 X3] [TOFF103 CS12 TOFF103 CSd12]: 4 steps
lem-pass-X3-CSd30-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-TOFF103-CS12-TOFF103-CSd12 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 0 q140 ∷
   rw 1 q141 ∷
   rw 2 q140 ∷
   rw 3 q142 ∷ []) Eq.refl

private
  q143 : Eqn
  q143 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ Toff103 ∷ []) (Toff103 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF103)
  q144 : Eqn
  q144 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS12)
  q145 : Eqn
  q145 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CSd12)

-- pass [X3 CKd30 X3] [TOFF103 CS12 TOFF103 CSd12]: 4 steps
lem-pass-X3-CKd30-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-TOFF103-CS12-TOFF103-CSd12 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 0 q143 ∷
   rw 1 q144 ∷
   rw 2 q143 ∷
   rw 3 q145 ∷ []) Eq.refl

private
  q146 : Eqn
  q146 = eqn (X3 ∷ CK30 ∷ X3 ∷ Toff103 ∷ []) (Toff103 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF103)
  q147 : Eqn
  q147 = eqn (X3 ∷ CK30 ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS12)
  q148 : Eqn
  q148 = eqn (X3 ∷ CK30 ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CSd12)

-- pass [X3 CK30 X3] [TOFF103 CS12 TOFF103 CSd12]: 4 steps
lem-pass-X3-CK30-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-TOFF103-CS12-TOFF103-CSd12 = derive (X3 ∷ CK30 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 0 q146 ∷
   rw 1 q147 ∷
   rw 2 q146 ∷
   rw 3 q148 ∷ []) Eq.refl

private
  q149 : Eqn
  q149 = eqn (X3 ∷ CS03 ∷ X3 ∷ Toff103 ∷ []) (Toff103 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF103)
  q150 : Eqn
  q150 = eqn (X3 ∷ CS03 ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS12)
  q151 : Eqn
  q151 = eqn (X3 ∷ CS03 ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CSd12)

-- pass [X3 CS30 X3] [TOFF103 CS12 TOFF103 CSd12]: 4 steps
lem-pass-X3-CS30-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-TOFF103-CS12-TOFF103-CSd12 = derive (X3 ∷ CS03 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 0 q149 ∷
   rw 1 q150 ∷
   rw 2 q149 ∷
   rw 3 q151 ∷ []) Eq.refl
