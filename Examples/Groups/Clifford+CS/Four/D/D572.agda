{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD572 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D572 (W : Ws) (Sᴰ : SD572) where

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
  lem-AXIOM-LF-at2301 : St 969
  lem-AXIOM-LF-at2301 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q3 : Eqn
  q3 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q4 : Eqn
  q4 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 74 W
  q6 : Eqn
  q6 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = wE 7 W
  q8 : Eqn
  q8 = wE 772 W
  q9 : Eqn
  q9 = wE 1636 W
  q10 : Eqn
  q10 = wE 39 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 329 W
  q13 : Eqn
  q13 = wE 315 W
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = wE 481 W
  q16 : Eqn
  q16 = wE 1637 W
  q17 : Eqn
  q17 = sE 969 lem-AXIOM-LF-at2301

-- LF CS02 CS02 CK02 CS02 CX03 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK12 CS23 CS23 CS23 S3 CK32 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 S3 S3 S3 S3 CK32 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS02 CS02 CS02 S0 CK02 CS02 CS02 CS02 CS02 CS02 CS02 S1 CK12 at 3: 193 steps
lem-LF-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK12-CS23-CS23-CS23-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-S3-S3-S3-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS02-CS02-CS02-S0-CK02-CS02-CS02-CS02-CS02-CS02-CS02-S1-CK12-at-3 : ⟪ (ℓ "丧丧丫丧丰义义义乗业义义义义义义丰义义乗义为义义义业乗义义义义义义丰义义义义义义义义义义义义义义义义义义业业业业乗义义义义义义义义义丰丧丧丧丈丫丧丧丧丧丧丧与为") ⟫ʷ ≈ ⟪ (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫乡义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶乡义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为") ⟫ʷ
lem-LF-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK12-CS23-CS23-CS23-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-S3-S3-S3-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS02-CS02-CS02-S0-CK02-CS02-CS02-CS02-CS02-CS02-CS02-S1-CK12-at-3 = derive (ℓ "丧丧丫丧丰义义义乗业义义义义义义丰义义乗义为义义义业乗义义义义义义丰义义义义义义义义义义义义义义义义义义业业业业乗义义义义义义义义义丰丧丧丧丈丫丧丧丧丧丧丧与为") (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫乡义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶乡义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为")
  (rw 21 q1 ∷
   rw⁻ 20 q2 ∷
   rw⁻ 19 q3 ∷
   rw⁻ 18 q2 ∷
   rw⁻ 17 q2 ∷
   re 16 1 (ℓ "乏个乏") ∷
   rw⁻ 18 q4 ∷
   rw 17 q5 ∷
   rw⁻ 16 q4 ∷
   re 17 3 (ℓ "乀") ∷
   rw⁻ 15 q2 ∷
   rw⁻ 14 q2 ∷
   rw⁻ 13 q2 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 10 q2 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 7 q2 ∷
   rw⁻ 6 q2 ∷
   rw⁻ 5 q2 ∷
   re 4 1 (ℓ "乏个乏") ∷
   rw⁻ 6 q4 ∷
   rw 5 q5 ∷
   rw⁻ 4 q4 ∷
   re 5 3 (ℓ "乀") ∷
   rw 3 q7 ∷
   rw 2 q8 ∷
   rw 1 q7 ∷
   rw 0 q7 ∷
   rw 1 q9 ∷
   rw 0 q2 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q2 ∷
   re 5 1 (ℓ "乏乆乏") ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "乐") ∷
   rw 5 q11 ∷
   rw 6 q11 ∷
   rw 7 q11 ∷
   rw 8 q12 ∷
   rw 9 q13 ∷
   rw 10 q11 ∷
   rw 11 q11 ∷
   rw 12 q11 ∷
   rw 13 q11 ∷
   rw 14 q11 ∷
   rw 15 q11 ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q4 ∷
   rw 17 q10 ∷
   rw 18 q4 ∷
   re 16 3 (ℓ "乐") ∷
   rw 17 q11 ∷
   rw 18 q11 ∷
   rw 19 q12 ∷
   rw 20 q11 ∷
   rw 21 q14 ∷
   rw 78 q1 ∷
   rw 77 q7 ∷
   rw 76 q7 ∷
   rw 75 q7 ∷
   rw 74 q7 ∷
   rw 73 q7 ∷
   rw 72 q7 ∷
   rw 71 q8 ∷
   rw 70 q15 ∷
   rw 69 q7 ∷
   rw 68 q7 ∷
   rw 67 q7 ∷
   re 66 1 (ℓ "乏个乏") ∷
   rw⁻ 68 q4 ∷
   rw 67 q5 ∷
   rw⁻ 66 q4 ∷
   re 67 3 (ℓ "乀") ∷
   rw⁻ 65 q2 ∷
   rw⁻ 64 q2 ∷
   rw⁻ 63 q2 ∷
   rw⁻ 62 q2 ∷
   rw⁻ 61 q2 ∷
   rw⁻ 60 q2 ∷
   rw⁻ 59 q2 ∷
   rw⁻ 58 q2 ∷
   rw⁻ 57 q2 ∷
   rw⁻ 56 q3 ∷
   rw⁻ 55 q6 ∷
   rw⁻ 54 q6 ∷
   rw⁻ 53 q6 ∷
   rw⁻ 52 q6 ∷
   rw⁻ 51 q2 ∷
   rw⁻ 50 q2 ∷
   rw⁻ 49 q2 ∷
   rw⁻ 48 q2 ∷
   rw⁻ 47 q2 ∷
   rw⁻ 46 q2 ∷
   rw⁻ 45 q2 ∷
   rw⁻ 44 q2 ∷
   rw⁻ 43 q2 ∷
   rw⁻ 42 q2 ∷
   rw⁻ 41 q2 ∷
   rw⁻ 40 q2 ∷
   rw⁻ 39 q2 ∷
   rw⁻ 38 q2 ∷
   rw⁻ 37 q2 ∷
   rw⁻ 36 q2 ∷
   rw⁻ 35 q2 ∷
   rw⁻ 34 q2 ∷
   re 33 1 (ℓ "乏个乏") ∷
   rw⁻ 35 q4 ∷
   rw 34 q5 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (ℓ "乀") ∷
   rw⁻ 32 q2 ∷
   rw⁻ 31 q2 ∷
   rw⁻ 30 q2 ∷
   rw⁻ 29 q2 ∷
   rw⁻ 28 q2 ∷
   rw⁻ 27 q2 ∷
   rw⁻ 26 q3 ∷
   rw⁻ 25 q6 ∷
   rw⁻ 24 q2 ∷
   rw⁻ 23 q2 ∷
   rw⁻ 22 q2 ∷
   rw 23 q16 ∷
   rw 22 q11 ∷
   rw 23 q11 ∷
   rw 24 q11 ∷
   rw 25 q13 ∷
   rw 26 q12 ∷
   rw 27 q11 ∷
   rw 28 q11 ∷
   rw 29 q11 ∷
   rw 30 q11 ∷
   rw 31 q11 ∷
   rw 32 q11 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q4 ∷
   rw 34 q10 ∷
   rw 35 q4 ∷
   re 33 3 (ℓ "乐") ∷
   rw 34 q11 ∷
   rw 35 q11 ∷
   rw 36 q11 ∷
   rw 37 q11 ∷
   rw 38 q11 ∷
   rw 39 q11 ∷
   rw 40 q11 ∷
   rw 41 q11 ∷
   rw 42 q11 ∷
   rw 43 q11 ∷
   rw 44 q11 ∷
   rw 45 q11 ∷
   rw 46 q11 ∷
   rw 47 q11 ∷
   rw 48 q11 ∷
   rw 49 q11 ∷
   rw 50 q11 ∷
   rw 51 q11 ∷
   rw 52 q13 ∷
   rw 53 q13 ∷
   rw 54 q13 ∷
   rw 55 q13 ∷
   rw 56 q12 ∷
   rw 57 q11 ∷
   rw 58 q11 ∷
   rw 59 q11 ∷
   rw 60 q11 ∷
   rw 61 q11 ∷
   rw 62 q11 ∷
   rw 63 q11 ∷
   rw 64 q11 ∷
   rw 65 q11 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q4 ∷
   rw 67 q10 ∷
   rw 68 q4 ∷
   re 66 3 (ℓ "乐") ∷
   rw 67 q2 ∷
   rw 68 q2 ∷
   rw 69 q2 ∷
   rw 70 q6 ∷
   rw 71 q3 ∷
   rw 72 q2 ∷
   rw 73 q2 ∷
   rw 74 q2 ∷
   rw 75 q2 ∷
   rw 76 q2 ∷
   rw 77 q2 ∷
   rw 78 q14 ∷
   rw 0 q17 ∷ []) Eq.refl
