{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD572 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D572 (W : Ws) (Sᴰ : SD572) where

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
  lem-AXIOM-LF-at2301 : St 969
  lem-AXIOM-LF-at2301 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q8 : Eqn
  q8 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q9 : Eqn
  q9 = eqn (CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ []) (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ []) (wn 1636 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q15 : Eqn
  q15 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q16 : Eqn
  q16 = eqn (CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ []) (wn 1637 W)
  q17 : Eqn
  q17 = eqn (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S1 ∷ CK12 ∷ []) (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Toff103 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ Toff103 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (lem-AXIOM-LF-at2301)

-- LF CS02 CS02 CK02 CS02 CX03 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK12 CS23 CS23 CS23 S3 CK32 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 S3 S3 S3 S3 CK32 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS02 CS02 CS02 S0 CK02 CS02 CS02 CS02 CS02 CS02 CS02 S1 CK12 at 3: 193 steps
lem-LF-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK12-CS23-CS23-CS23-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-S3-S3-S3-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS02-CS02-CS02-S0-CK02-CS02-CS02-CS02-CS02-CS02-CS02-S1-CK12-at-3 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK12 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Toff103 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ Toff103 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) ⟫ʷ
lem-LF-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK12-CS23-CS23-CS23-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-S3-S3-S3-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS02-CS02-CS02-S0-CK02-CS02-CS02-CS02-CS02-CS02-CS02-S1-CK12-at-3 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK12 ∷ []) (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Toff103 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ Toff103 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  (rw 21 q1 ∷
   rw⁻ 20 q2 ∷
   rw⁻ 19 q3 ∷
   rw⁻ 18 q2 ∷
   rw⁻ 17 q2 ∷
   re 16 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q4 ∷
   rw 17 q5 ∷
   rw⁻ 16 q4 ∷
   re 17 3 (CX13 ∷ []) ∷
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
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 5 q5 ∷
   rw⁻ 4 q4 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw 3 q7 ∷
   rw 2 q8 ∷
   rw 1 q7 ∷
   rw 0 q7 ∷
   rw 1 q9 ∷
   rw 0 q2 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q2 ∷
   re 5 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   rw 6 q4 ∷
   re 4 3 (CX30 ∷ []) ∷
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
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw 17 q10 ∷
   rw 18 q4 ∷
   re 16 3 (CX30 ∷ []) ∷
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
   re 66 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q4 ∷
   rw 67 q5 ∷
   rw⁻ 66 q4 ∷
   re 67 3 (CX13 ∷ []) ∷
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
   re 33 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q4 ∷
   rw 34 q5 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (CX13 ∷ []) ∷
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
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 33 q4 ∷
   rw 34 q10 ∷
   rw 35 q4 ∷
   re 33 3 (CX30 ∷ []) ∷
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
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q4 ∷
   rw 67 q10 ∷
   rw 68 q4 ∷
   re 66 3 (CX30 ∷ []) ∷
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
