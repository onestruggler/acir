{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD732 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D732 (W : Ws) (Sᴰ : SD732) where

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
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 : St 2271
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 = pickᴰ 0 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2272
  lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 1 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2273
  lem-pass-X3-CS30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 2 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q3 : Eqn
  q3 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q7 : Eqn
  q7 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q8 : Eqn
  q8 = eqn (X2 ∷ Toff012 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) (wn 2016 W)
  q9 : Eqn
  q9 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q10 : Eqn
  q10 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q11 : Eqn
  q11 = eqn (CS02⁻ ∷ X3 ∷ []) (X3 ∷ CS02⁻ ∷ []) (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (X))
  q12 : Eqn
  q12 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q13 : Eqn
  q13 = eqn (X0 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ X0 ∷ []) (wn 2054 W)
  q14 : Eqn
  q14 = eqn (X0 ∷ CS02 ∷ []) (S2 ∷ CS02⁻ ∷ X0 ∷ []) (wn 2055 W)
  q15 : Eqn
  q15 = eqn (X0 ∷ CS02⁻ ∷ []) (S2⁻ ∷ CS02 ∷ X0 ∷ []) (wn 1966 W)
  q16 : Eqn
  q16 = eqn (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02)
  q17 : Eqn
  q17 = eqn (X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (Toff012 ∷ X2 ∷ []) (wn 2017 W)
  q18 : Eqn
  q18 = eqn (S2 ∷ X3 ∷ []) (X3 ∷ S2 ∷ []) (low₃-comm ((S ↑ ↑)) (X))
  q19 : Eqn
  q19 = eqn (S2⁻ ∷ X3 ∷ []) (X3 ∷ S2⁻ ∷ []) (low₃-comm (((S • S • S) ↑ ↑)) (X))
  q20 : Eqn
  q20 = eqn (X0 ∷ Toff012 ∷ []) (Toff012 ∷ X0 ∷ []) (wn 2057 W)
  q21 : Eqn
  q21 = eqn (X0 ∷ S2 ∷ []) (S2 ∷ X0 ∷ []) (low₁-comm (X) ((S ↑)))
  q22 : Eqn
  q22 = eqn (X0 ∷ S2⁻ ∷ []) (S2⁻ ∷ X0 ∷ []) (low₁-comm (X) (((S • S • S) ↑)))
  q23 : Eqn
  q23 = eqn (S2 ∷ S2⁻ ∷ CS02 ∷ []) (CS02 ∷ []) (wn 2219 W)
  q24 : Eqn
  q24 = eqn (S2⁻ ∷ S2 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ []) (wn 2220 W)

-- pass [X0 X3 TOFF201 CS23 TOFF201 CSd23 X0 X3] [TOFF013 CS02 TOFF013 CSd02]: 503 steps
lem-pass-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ [])
  (rw 9 q1 ∷
   re 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 16 q5 ∷
   rw 15 q4 ∷
   rw 14 q2 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q2 ∷
   rw 9 q6 ∷
   re 9 8 (Toff012 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 7 q9 ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 8 q1 ∷
   rw⁻ 9 q2 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 11 q3 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw⁻ 13 q3 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw⁻ 15 q2 ∷
   rw⁻ 16 q4 ∷
   rw 9 q6 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 8 3 (Toff013 ∷ []) ∷
   rw 9 q9 ∷
   rw 10 q9 ∷
   rw 11 q5 ∷
   rw⁻ 10 q10 ∷
   rw 13 q1 ∷
   re 12 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 13 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw 15 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw⁻ 19 q4 ∷
   rw 20 q5 ∷
   rw 19 q4 ∷
   rw 18 q2 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   rw 16 q3 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw 14 q3 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q2 ∷
   rw 13 q6 ∷
   re 13 8 (Toff012 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q8 ∷
   rw 11 q9 ∷
   re 13 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw 15 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw⁻ 19 q4 ∷
   rw 12 q1 ∷
   rw⁻ 13 q2 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw⁻ 15 q3 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   rw⁻ 17 q3 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   rw⁻ 19 q2 ∷
   rw⁻ 20 q4 ∷
   rw 13 q6 ∷
   re 13 8 (Toff012 ∷ []) ∷
   re 12 3 (Toff013 ∷ []) ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 15 q5 ∷
   rw⁻ 14 q11 ∷
   rw 10 q1 ∷
   rw 9 q7 ∷
   re 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 16 q5 ∷
   rw 15 q4 ∷
   rw 14 q2 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q2 ∷
   rw 9 q6 ∷
   re 9 8 (Toff012 ∷ []) ∷
   rw 7 q7 ∷
   rw 6 q12 ∷
   rw 7 q13 ∷
   rw 6 q9 ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 7 q2 ∷
   rw 10 q1 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw 12 q1 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q3 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q2 ∷
   rw⁻ 14 q4 ∷
   rw 7 q1 ∷
   rw⁻ 8 q2 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw⁻ 10 q3 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw⁻ 12 q3 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 8 q6 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 7 3 (Toff013 ∷ []) ∷
   rw 8 q9 ∷
   rw⁻ 9 q12 ∷
   rw 10 q5 ∷
   rw 9 q14 ∷
   rw 15 q1 ∷
   rw 14 q7 ∷
   re 13 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 14 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 13 q2 ∷
   rw 16 q1 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw⁻ 15 q3 ∷
   rw 18 q1 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw⁻ 17 q3 ∷
   rw 20 q1 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw⁻ 19 q2 ∷
   rw⁻ 20 q4 ∷
   rw 21 q5 ∷
   rw 20 q4 ∷
   rw 19 q2 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   rw 17 q3 ∷
   re 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   rw 15 q3 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   rw 13 q2 ∷
   rw 14 q6 ∷
   re 14 8 (Toff012 ∷ []) ∷
   rw 12 q7 ∷
   rw 11 q12 ∷
   rw 12 q13 ∷
   rw 11 q9 ∷
   re 13 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw 15 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw⁻ 19 q4 ∷
   rw 12 q1 ∷
   rw⁻ 13 q2 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw⁻ 15 q3 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   rw⁻ 17 q3 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   rw⁻ 19 q2 ∷
   rw⁻ 20 q4 ∷
   rw 13 q6 ∷
   re 13 8 (Toff012 ∷ []) ∷
   re 12 3 (Toff013 ∷ []) ∷
   rw 13 q9 ∷
   rw⁻ 14 q12 ∷
   rw 15 q5 ∷
   rw 14 q15 ∷
   rw 2 q16 ∷
   rw 5 q1 ∷
   rw 4 q7 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   rw 10 q4 ∷
   rw 9 q2 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q2 ∷
   rw 4 q6 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q7 ∷
   rw 2 q17 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 1 q1 ∷
   rw⁻ 2 q2 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q4 ∷
   rw 2 q6 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q9 ∷
   rw 3 q5 ∷
   rw⁻ 2 q18 ∷
   rw⁻ 3 q11 ∷
   rw 8 q1 ∷
   rw 7 q7 ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw⁻ 13 q4 ∷
   rw 14 q5 ∷
   rw 13 q4 ∷
   rw 12 q2 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q2 ∷
   rw 7 q6 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 5 q7 ∷
   rw 4 q7 ∷
   rw 5 q17 ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q2 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 4 q1 ∷
   rw⁻ 5 q2 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q3 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q4 ∷
   rw 5 q6 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 4 3 (Toff013 ∷ []) ∷
   rw 5 q9 ∷
   rw 6 q5 ∷
   rw⁻ 5 q19 ∷
   rw⁻ 6 q10 ∷
   rw 2 q1 ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 9 q5 ∷
   rw 8 q4 ∷
   rw 7 q2 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q3 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q2 ∷
   rw 2 q6 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 0 q12 ∷
   rw 1 q20 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw⁻ 7 q4 ∷
   rw 0 q1 ∷
   rw⁻ 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 1 q6 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw⁻ 1 q12 ∷
   rw 2 q5 ∷
   rw 1 q21 ∷
   rw 2 q15 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q4 ∷
   rw 13 q5 ∷
   rw 12 q4 ∷
   rw 11 q2 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw 9 q3 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q2 ∷
   rw 6 q6 ∷
   re 6 8 (Toff012 ∷ []) ∷
   rw 4 q12 ∷
   rw 5 q20 ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q2 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 4 q1 ∷
   rw⁻ 5 q2 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q3 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q4 ∷
   rw 5 q6 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 4 3 (Toff013 ∷ []) ∷
   rw⁻ 5 q12 ∷
   rw 6 q5 ∷
   rw 5 q22 ∷
   rw 6 q14 ∷
   rw 1 q23 ∷
   rw 3 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2246 W)
  q26 : Eqn
  q26 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q27 : Eqn
  q27 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q28 : Eqn
  q28 = eqn (Sw01 ∷ K2⁻ ∷ []) (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI)))
  q29 : Eqn
  q29 = eqn (Sw01 ∷ S2⁻ ∷ []) (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S)))
  q30 : Eqn
  q30 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q31 : Eqn
  q31 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q32 : Eqn
  q32 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q33 : Eqn
  q33 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q34 : Eqn
  q34 = eqn (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (wn 2247 W)
  q35 : Eqn
  q35 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q36 : Eqn
  q36 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q37 : Eqn
  q37 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q38 : Eqn
  q38 = eqn (X3 ∷ CK30 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201)
  q39 : Eqn
  q39 = eqn (X3 ∷ CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS23-TOFF201-CSd23-TOFF201)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q41 : Eqn
  q41 = eqn (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (wn 2248 W)
  q42 : Eqn
  q42 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2249 W)

-- pass [X3 CSd30 X3] [X0 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0]: 151 steps
lem-pass-X3-CSd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ []) (X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   rw 3 q12 ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 1 q25 ∷
   rw⁻ 0 q12 ∷
   rw 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q9 ∷
   rw 7 q1 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q9 ∷
   rw 7 q9 ∷
   rw 10 q1 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q9 ∷
   rw 10 q5 ∷
   rw 14 q26 ∷
   rw⁻ 13 q27 ∷
   rw⁻ 12 q27 ∷
   rw⁻ 11 q28 ∷
   rw⁻ 10 q29 ∷
   rw⁻ 9 q30 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q31 ∷
   rw 9 q32 ∷
   rw⁻ 8 q31 ∷
   re 9 3 (CK31 ∷ []) ∷
   rw⁻ 7 q30 ∷
   rw⁻ 6 q30 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q31 ∷
   rw 6 q32 ∷
   rw⁻ 5 q31 ∷
   re 6 3 (CK31 ∷ []) ∷
   rw⁻ 4 q30 ∷
   rw⁻ 3 q30 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q31 ∷
   rw 3 q33 ∷
   rw⁻ 2 q31 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 1 q30 ∷
   rw 2 q34 ∷
   rw 1 q29 ∷
   rw 2 q28 ∷
   rw 3 q27 ∷
   rw 4 q27 ∷
   rw 5 q30 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q31 ∷
   rw 7 q35 ∷
   rw 8 q31 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q30 ∷
   rw 8 q30 ∷
   re 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q31 ∷
   rw 10 q36 ∷
   rw 11 q31 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q30 ∷
   rw 11 q30 ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q31 ∷
   rw 13 q36 ∷
   rw 14 q31 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 13 q30 ∷
   rw 14 q37 ∷
   rw 11 q38 ∷
   rw 8 q38 ∷
   rw 5 q39 ∷
   rw 22 q26 ∷
   rw⁻ 21 q27 ∷
   rw⁻ 20 q40 ∷
   rw⁻ 19 q29 ∷
   rw⁻ 18 q29 ∷
   rw⁻ 17 q30 ∷
   re 16 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q31 ∷
   rw 17 q32 ∷
   rw⁻ 16 q31 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw⁻ 15 q30 ∷
   rw⁻ 14 q30 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q31 ∷
   rw 14 q32 ∷
   rw⁻ 13 q31 ∷
   re 14 3 (CK31 ∷ []) ∷
   rw⁻ 12 q30 ∷
   rw⁻ 11 q30 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q31 ∷
   rw 11 q33 ∷
   rw⁻ 10 q31 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 9 q30 ∷
   rw 10 q41 ∷
   rw 9 q29 ∷
   rw 10 q29 ∷
   rw 11 q40 ∷
   rw 12 q27 ∷
   rw 13 q30 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q31 ∷
   rw 15 q35 ∷
   rw 16 q31 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q30 ∷
   rw 16 q30 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q31 ∷
   rw 18 q36 ∷
   rw 19 q31 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q30 ∷
   rw 19 q30 ∷
   re 21 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 20 q31 ∷
   rw 21 q36 ∷
   rw 22 q31 ∷
   re 20 3 (CK30 ∷ []) ∷
   rw 21 q30 ∷
   rw 22 q37 ∷
   rw 23 q1 ∷
   rw 22 q12 ∷
   rw 21 q7 ∷
   re 20 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 22 q5 ∷
   rw 19 q7 ∷
   rw 18 q7 ∷
   re 17 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   rw 16 q7 ∷
   rw 15 q7 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   rw 13 q7 ∷
   rw 14 q42 ∷
   rw⁻ 13 q12 ∷
   rw 14 q9 ∷
   rw 17 q1 ∷
   re 15 3 (CS03⁻ ∷ []) ∷
   rw 16 q9 ∷
   rw 17 q5 ∷ []) Eq.refl
