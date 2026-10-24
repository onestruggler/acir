{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD650 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D650 (W : Ws) (Sᴰ : SD650) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-TOFF201-vs-X0-TOFF201-X0 : St 1604
  lem-pass-TOFF201-vs-X0-TOFF201-X0 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-X0 : St 806
  lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-X0 = pickᴰ 1 Sᴰ
  lem-AXIOM-LF-at3012 : St 1605
  lem-AXIOM-LF-at3012 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 : St 1407
  lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 = pickᴰ 3 Sᴰ
  lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-TOFF201-X0 : St 1409
  lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-TOFF201-X0 = pickᴰ 4 Sᴰ
  lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 : St 1408
  lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 = pickᴰ 5 Sᴰ
  lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-TOFF201-X0 : St 1410
  lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-TOFF201-X0 = pickᴰ 6 Sᴰ
  lem-pass-TOFF201-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 : St 1606
  lem-pass-TOFF201-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 = pickᴰ 7 Sᴰ
  lem-pass-TOFF201-vs-X0-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-X0 : St 1607
  lem-pass-TOFF201-vs-X0-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-X0 = pickᴰ 8 Sᴰ

private
  q1 : Eqn
  q1 = sE 1605 lem-AXIOM-LF-at3012
  q2 : Eqn
  q2 = wE 873 W
  q3 : Eqn
  q3 = sE 1407 lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0
  q4 : Eqn
  q4 = sE 1606 lem-pass-TOFF201-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0
  q5 : Eqn
  q5 = sE 1408 lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0
  q6 : Eqn
  q6 = sE 1409 lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-TOFF201-X0
  q7 : Eqn
  q7 = sE 1604 lem-pass-TOFF201-vs-X0-TOFF201-X0
  q8 : Eqn
  q8 = sE 1410 lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-TOFF201-X0
  q9 : Eqn
  q9 = sE 806 lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-X0
  q10 : Eqn
  q10 = sE 1607 lem-pass-TOFF201-vs-X0-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-X0
  q11 : Eqn
  q11 = wE 1 W
  q12 : Eqn
  q12 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q13 : Eqn
  q13 = wE 3 W
  q14 : Eqn
  q14 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q15 : Eqn
  q15 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q16 : Eqn
  q16 = wE 1951 W
  q17 : Eqn
  q17 = wE 1952 W
  q18 : Eqn
  q18 = wE 5 W
  q19 : Eqn
  q19 = wE 1106 W
  q20 : Eqn
  q20 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q21 : Eqn
  q21 = eqn (ℓ "並乍") (ℓ "乍並") (low-comm (Swap) (CK₀₁))
  q22 : Eqn
  q22 = wE 74 W
  q23 : Eqn
  q23 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q24 : Eqn
  q24 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q25 : Eqn
  q25 = wE 7 W
  q26 : Eqn
  q26 = wE 772 W
  q27 : Eqn
  q27 = wE 1955 W
  q28 : Eqn
  q28 = wE 31 W
  q29 : Eqn
  q29 = wE 1956 W

-- L87 merge-k CS03 CS03 CK03 CS03 CX01 CS13 CS13 CS13  0: 403 steps
lem-L87-merge-k-CS03-CS03-CK03-CS03-CX01-CS13-CS13-CS13--0 : ⟪ (ℓ "中中丱中丣丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乍丽丽丽与乁丽丽丽丽丽丽丣丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽与与与与乁丽丽丽丽丽丽丽丽丽丣中中中丈丱中中中中中中且乍丌中中丱中丣丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乍丽丽丽与乁丽丽丽丽丽丽丣丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽与与与与乁丽丽丽丽丽丽丽丽丽丣中中中丈丱中中中中中中且乍丌") ⟫ʷ ≈ ⟪ (ℓ "丽丽乁丽乁乁丽丽乁丽乁乁丹义义义乍义义义义义乍义义丹义义乍义乍乍义义乍义乍乍") ⟫ʷ
lem-L87-merge-k-CS03-CS03-CK03-CS03-CX01-CS13-CS13-CS13--0 = derive (ℓ "中中丱中丣丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乍丽丽丽与乁丽丽丽丽丽丽丣丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽与与与与乁丽丽丽丽丽丽丽丽丽丣中中中丈丱中中中中中中且乍丌中中丱中丣丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乍丽丽丽与乁丽丽丽丽丽丽丣丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽与与与与乁丽丽丽丽丽丽丽丽丽丣中中中丈丱中中中中中中且乍丌") (ℓ "丽丽乁丽乁乁丽丽乁丽乁乁丹义义义乍义义义义义乍义义丹义义乍义乍乍义义乍义乍乍")
  (rw 0 q1 ∷
   rw 92 q1 ∷
   rw 121 q2 ∷
   rw 124 q2 ∷
   rw 157 q2 ∷
   rw 160 q2 ∷
   rw 62 q3 ∷
   rw 61 q4 ∷
   rw 30 q5 ∷
   rw 29 q4 ∷
   rw 93 q6 ∷
   rw 92 q7 ∷
   rw 61 q8 ∷
   rw 96 q9 ∷
   rw 95 q10 ∷
   rw 129 q6 ∷
   rw 60 q11 ∷
   rw 59 q12 ∷
   re 58 1 (ℓ "乏为乏") ∷
   rw 60 q13 ∷
   re 57 1 (ℓ "乏为乏") ∷
   rw 59 q13 ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 58 q13 ∷
   re 55 1 (ℓ "乏为乏") ∷
   rw 57 q13 ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 56 q13 ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 55 q13 ∷
   rw 52 q14 ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 53 q13 ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 52 q13 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 51 q13 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 50 q13 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 49 q13 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 48 q13 ∷
   rw 45 q15 ∷
   re 44 1 (ℓ "乏为乏") ∷
   rw 46 q13 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 45 q13 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 44 q13 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 43 q13 ∷
   rw 40 q15 ∷
   re 39 1 (ℓ "乏为乏") ∷
   rw 41 q13 ∷
   rw 38 q15 ∷
   re 37 1 (ℓ "乏为乏") ∷
   rw 39 q13 ∷
   rw 36 q14 ∷
   re 35 1 (ℓ "乏丫乏") ∷
   rw 37 q13 ∷
   re 34 1 (ℓ "乏丫乏") ∷
   rw 36 q13 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q13 ∷
   re 32 1 (ℓ "乏丫乏") ∷
   rw 34 q13 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q13 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q13 ∷
   rw 29 q12 ∷
   re 28 1 (ℓ "乏为乏") ∷
   rw 30 q13 ∷
   re 27 1 (ℓ "乏为乏") ∷
   rw 29 q13 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q13 ∷
   re 25 1 (ℓ "乏为乏") ∷
   rw 27 q13 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q13 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q13 ∷
   rw 22 q14 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q13 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 22 q13 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 21 q13 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q13 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q13 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q13 ∷
   rw 15 q15 ∷
   re 14 1 (ℓ "乏为乏") ∷
   rw 16 q13 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q13 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q13 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q13 ∷
   rw 10 q15 ∷
   re 9 1 (ℓ "乏为乏") ∷
   rw 11 q13 ∷
   rw 8 q15 ∷
   re 7 1 (ℓ "乏为乏") ∷
   rw 9 q13 ∷
   rw 6 q14 ∷
   re 5 1 (ℓ "乏丫乏") ∷
   rw 7 q13 ∷
   re 4 1 (ℓ "乏丫乏") ∷
   rw 6 q13 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q13 ∷
   re 2 1 (ℓ "乏丫乏") ∷
   rw 4 q13 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q13 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q13 ∷
   rw 1 q16 ∷
   rw 2 q11 ∷
   re 0 3 (ℓ "丽") ∷
   rw 3 q11 ∷
   re 1 3 (ℓ "丽") ∷
   rw 4 q11 ∷
   re 2 3 (ℓ "乁") ∷
   rw 5 q11 ∷
   re 3 3 (ℓ "丽") ∷
   rw 6 q11 ∷
   re 4 3 (ℓ "乁") ∷
   rw 7 q11 ∷
   re 5 3 (ℓ "乁") ∷
   rw 8 q11 ∷
   re 6 3 (ℓ "丽") ∷
   rw 9 q11 ∷
   re 7 3 (ℓ "丽") ∷
   rw 10 q11 ∷
   re 8 3 (ℓ "乁") ∷
   rw 11 q11 ∷
   re 9 3 (ℓ "丽") ∷
   rw 12 q11 ∷
   re 10 3 (ℓ "乁") ∷
   rw 13 q11 ∷
   re 11 3 (ℓ "乁") ∷
   rw 12 q13 ∷
   rw 12 q17 ∷
   rw 77 q18 ∷
   rw 76 q19 ∷
   rw⁻ 75 q20 ∷
   rw⁻ 74 q20 ∷
   rw⁻ 73 q21 ∷
   rw⁻ 72 q20 ∷
   rw⁻ 71 q20 ∷
   rw⁻ 70 q20 ∷
   rw 69 q22 ∷
   rw⁻ 68 q20 ∷
   rw⁻ 67 q20 ∷
   rw⁻ 66 q20 ∷
   rw⁻ 65 q20 ∷
   rw⁻ 64 q20 ∷
   rw⁻ 63 q20 ∷
   rw⁻ 62 q20 ∷
   rw⁻ 61 q20 ∷
   rw⁻ 60 q20 ∷
   rw⁻ 59 q23 ∷
   rw⁻ 58 q21 ∷
   rw⁻ 57 q20 ∷
   rw⁻ 56 q20 ∷
   rw⁻ 55 q20 ∷
   rw⁻ 54 q20 ∷
   rw⁻ 53 q20 ∷
   rw⁻ 52 q20 ∷
   rw 51 q22 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q24 ∷
   rw 51 q25 ∷
   rw⁻ 50 q24 ∷
   re 51 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q24 ∷
   rw 50 q25 ∷
   rw⁻ 49 q24 ∷
   re 50 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏丫乏") ∷
   rw⁻ 50 q24 ∷
   rw 49 q26 ∷
   rw⁻ 48 q24 ∷
   re 49 3 (ℓ "乁") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q24 ∷
   rw 48 q25 ∷
   rw⁻ 47 q24 ∷
   re 48 3 (ℓ "丽") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q24 ∷
   rw 47 q25 ∷
   rw⁻ 46 q24 ∷
   re 47 3 (ℓ "丽") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q24 ∷
   rw 46 q25 ∷
   rw⁻ 45 q24 ∷
   re 46 3 (ℓ "丽") ∷
   rw 44 q19 ∷
   rw⁻ 43 q20 ∷
   rw⁻ 42 q20 ∷
   rw⁻ 41 q21 ∷
   rw⁻ 40 q20 ∷
   rw⁻ 39 q20 ∷
   rw⁻ 38 q20 ∷
   rw 37 q22 ∷
   rw⁻ 36 q20 ∷
   rw⁻ 35 q20 ∷
   rw⁻ 34 q20 ∷
   rw⁻ 33 q20 ∷
   rw⁻ 32 q20 ∷
   rw⁻ 31 q20 ∷
   rw⁻ 30 q20 ∷
   rw⁻ 29 q20 ∷
   rw⁻ 28 q20 ∷
   rw⁻ 27 q23 ∷
   rw⁻ 26 q21 ∷
   rw⁻ 25 q20 ∷
   rw⁻ 24 q20 ∷
   rw⁻ 23 q20 ∷
   rw⁻ 22 q20 ∷
   rw⁻ 21 q20 ∷
   rw⁻ 20 q20 ∷
   rw 19 q22 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q24 ∷
   rw 19 q25 ∷
   rw⁻ 18 q24 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q24 ∷
   rw 18 q25 ∷
   rw⁻ 17 q24 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丫乏") ∷
   rw⁻ 18 q24 ∷
   rw 17 q26 ∷
   rw⁻ 16 q24 ∷
   re 17 3 (ℓ "乁") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q24 ∷
   rw 16 q25 ∷
   rw⁻ 15 q24 ∷
   re 16 3 (ℓ "丽") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q24 ∷
   rw 15 q25 ∷
   rw⁻ 14 q24 ∷
   re 15 3 (ℓ "丽") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q24 ∷
   rw 14 q25 ∷
   rw⁻ 13 q24 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q27 ∷
   rw 13 q20 ∷
   rw 14 q20 ∷
   rw 15 q20 ∷
   rw 16 q21 ∷
   rw 17 q20 ∷
   rw 18 q20 ∷
   rw 19 q20 ∷
   rw 20 q20 ∷
   rw 21 q20 ∷
   rw 22 q21 ∷
   rw 23 q20 ∷
   rw 24 q20 ∷
   rw 25 q28 ∷
   rw 25 q17 ∷
   rw 86 q18 ∷
   rw 85 q19 ∷
   rw⁻ 84 q21 ∷
   rw⁻ 83 q21 ∷
   rw⁻ 82 q20 ∷
   rw⁻ 81 q21 ∷
   rw⁻ 80 q20 ∷
   rw⁻ 79 q20 ∷
   rw 78 q22 ∷
   rw⁻ 77 q20 ∷
   rw⁻ 76 q20 ∷
   rw⁻ 75 q20 ∷
   rw⁻ 74 q20 ∷
   rw⁻ 73 q20 ∷
   rw⁻ 72 q20 ∷
   rw⁻ 71 q23 ∷
   rw⁻ 70 q21 ∷
   rw⁻ 69 q20 ∷
   rw⁻ 68 q20 ∷
   rw⁻ 67 q20 ∷
   rw⁻ 66 q23 ∷
   rw⁻ 65 q21 ∷
   rw⁻ 64 q23 ∷
   rw⁻ 63 q21 ∷
   rw 62 q22 ∷
   re 61 1 (ℓ "乏丫乏") ∷
   rw⁻ 63 q24 ∷
   rw 62 q26 ∷
   rw⁻ 61 q24 ∷
   re 62 3 (ℓ "乁") ∷
   re 60 1 (ℓ "乏丫乏") ∷
   rw⁻ 62 q24 ∷
   rw 61 q26 ∷
   rw⁻ 60 q24 ∷
   re 61 3 (ℓ "乁") ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw⁻ 61 q24 ∷
   rw 60 q25 ∷
   rw⁻ 59 q24 ∷
   re 60 3 (ℓ "丽") ∷
   re 58 1 (ℓ "乏丫乏") ∷
   rw⁻ 60 q24 ∷
   rw 59 q26 ∷
   rw⁻ 58 q24 ∷
   re 59 3 (ℓ "乁") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q24 ∷
   rw 58 q25 ∷
   rw⁻ 57 q24 ∷
   re 58 3 (ℓ "丽") ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw⁻ 58 q24 ∷
   rw 57 q25 ∷
   rw⁻ 56 q24 ∷
   re 57 3 (ℓ "丽") ∷
   rw 55 q19 ∷
   rw⁻ 54 q21 ∷
   rw⁻ 53 q21 ∷
   rw⁻ 52 q20 ∷
   rw⁻ 51 q21 ∷
   rw⁻ 50 q20 ∷
   rw⁻ 49 q20 ∷
   rw 48 q22 ∷
   rw⁻ 47 q20 ∷
   rw⁻ 46 q20 ∷
   rw⁻ 45 q20 ∷
   rw⁻ 44 q20 ∷
   rw⁻ 43 q20 ∷
   rw⁻ 42 q20 ∷
   rw⁻ 41 q23 ∷
   rw⁻ 40 q21 ∷
   rw⁻ 39 q20 ∷
   rw⁻ 38 q20 ∷
   rw⁻ 37 q20 ∷
   rw⁻ 36 q23 ∷
   rw⁻ 35 q21 ∷
   rw⁻ 34 q23 ∷
   rw⁻ 33 q21 ∷
   rw 32 q22 ∷
   re 31 1 (ℓ "乏丫乏") ∷
   rw⁻ 33 q24 ∷
   rw 32 q26 ∷
   rw⁻ 31 q24 ∷
   re 32 3 (ℓ "乁") ∷
   re 30 1 (ℓ "乏丫乏") ∷
   rw⁻ 32 q24 ∷
   rw 31 q26 ∷
   rw⁻ 30 q24 ∷
   re 31 3 (ℓ "乁") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q24 ∷
   rw 30 q25 ∷
   rw⁻ 29 q24 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丫乏") ∷
   rw⁻ 30 q24 ∷
   rw 29 q26 ∷
   rw⁻ 28 q24 ∷
   re 29 3 (ℓ "乁") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q24 ∷
   rw 28 q25 ∷
   rw⁻ 27 q24 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q24 ∷
   rw 27 q25 ∷
   rw⁻ 26 q24 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q29 ∷
   rw 26 q20 ∷
   rw 27 q20 ∷
   rw 28 q21 ∷
   rw 29 q20 ∷
   rw 30 q21 ∷
   rw 31 q21 ∷
   rw 32 q20 ∷
   rw 33 q20 ∷
   rw 34 q21 ∷
   rw 35 q20 ∷
   rw 36 q21 ∷
   rw 37 q21 ∷
   rw 38 q28 ∷ []) Eq.refl
