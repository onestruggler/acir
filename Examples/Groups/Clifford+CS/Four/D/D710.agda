{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D710 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D677 W using (lem-S2-at1023)
open import Examples.Groups.Clifford+CS.Four.D.D678 W using (lem-S2-at2013)
open import Examples.Groups.Clifford+CS.Four.D.D700 W using (lem-hyb-sym-23-at2310)

private
  q1 : Eqn
  q1 = eqn (CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ []) (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ []) (wn 1636 W)
  q2 : Eqn
  q2 = eqn (CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ []) (wn 1637 W)
  q3 : Eqn
  q3 = eqn (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S0 ∷ CK02 ∷ []) (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S1 ∷ CK12 ∷ []) (lem-hyb-sym-23-at2310)
  q4 : Eqn
  q4 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q5 : Eqn
  q5 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q6 : Eqn
  q6 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q9 : Eqn
  q9 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q12 : Eqn
  q12 = eqn (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ []) (CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ []) (wn 1212 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q17 : Eqn
  q17 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q18 : Eqn
  q18 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ []) (CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (wn 1213 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)

-- respell hyb CS12 CS12 CK12 CS12 CX13 CS23 CS23 CS23  -> CS02 CS02 CK02 CS02 CX03 CS23 CS23 CS23 : 195 steps
lem-respell-hyb-CS12-CS12-CK12-CS12-CX13-CS23-CS23-CS23---⟶-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23- : ⟪ (CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK12 ∷ []) ⟫ʷ
lem-respell-hyb-CS12-CS12-CK12-CS12-CX13-CS23-CS23-CS23---⟶-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23- = derive (CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S0 ∷ CK02 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK12 ∷ [])
  (rw 0 q1 ∷
   rw 22 q2 ∷
   rw 0 q3 ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   re 16 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q7 ∷
   rw 17 q8 ∷
   rw⁻ 16 q7 ∷
   re 17 3 (CX31 ∷ []) ∷
   rw 15 q5 ∷
   rw 14 q5 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw 9 q9 ∷
   rw 8 q6 ∷
   rw 7 q5 ∷
   rw 6 q5 ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 5 q8 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (CX31 ∷ []) ∷
   rw⁻ 3 q10 ∷
   rw⁻ 2 q11 ∷
   rw⁻ 1 q10 ∷
   rw⁻ 0 q10 ∷
   rw 1 q12 ∷
   rw 0 q13 ∷
   rw 1 q13 ∷
   rw 2 q14 ∷
   rw 3 q13 ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 5 q15 ∷
   rw 6 q7 ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 5 q10 ∷
   rw 6 q10 ∷
   rw 7 q10 ∷
   rw 8 q11 ∷
   rw 9 q16 ∷
   rw 10 q10 ∷
   rw 11 q10 ∷
   rw 12 q10 ∷
   rw 13 q10 ∷
   rw 14 q10 ∷
   rw 15 q10 ∷
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 16 q7 ∷
   rw 17 q15 ∷
   rw 18 q7 ∷
   re 16 3 (CX03 ∷ []) ∷
   rw 17 q10 ∷
   rw 18 q10 ∷
   rw 19 q11 ∷
   rw 20 q10 ∷
   rw 21 q17 ∷
   rw 78 q4 ∷
   rw⁻ 77 q10 ∷
   rw⁻ 76 q10 ∷
   rw⁻ 75 q10 ∷
   rw⁻ 74 q10 ∷
   rw⁻ 73 q10 ∷
   rw⁻ 72 q10 ∷
   rw⁻ 71 q11 ∷
   rw⁻ 70 q16 ∷
   rw⁻ 69 q10 ∷
   rw⁻ 68 q10 ∷
   rw⁻ 67 q10 ∷
   re 66 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q7 ∷
   rw 67 q8 ∷
   rw⁻ 66 q7 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 65 q5 ∷
   rw 64 q5 ∷
   rw 63 q5 ∷
   rw 62 q5 ∷
   rw 61 q5 ∷
   rw 60 q5 ∷
   rw 59 q5 ∷
   rw 58 q5 ∷
   rw 57 q5 ∷
   rw 56 q6 ∷
   rw 55 q9 ∷
   rw 54 q9 ∷
   rw 53 q9 ∷
   rw 52 q9 ∷
   rw 51 q5 ∷
   rw 50 q5 ∷
   rw 49 q5 ∷
   rw 48 q5 ∷
   rw 47 q5 ∷
   rw 46 q5 ∷
   rw 45 q5 ∷
   rw 44 q5 ∷
   rw 43 q5 ∷
   rw 42 q5 ∷
   rw 41 q5 ∷
   rw 40 q5 ∷
   rw 39 q5 ∷
   rw 38 q5 ∷
   rw 37 q5 ∷
   rw 36 q5 ∷
   rw 35 q5 ∷
   rw 34 q5 ∷
   re 33 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q7 ∷
   rw 34 q8 ∷
   rw⁻ 33 q7 ∷
   re 34 3 (CX31 ∷ []) ∷
   rw 32 q5 ∷
   rw 31 q5 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q5 ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   rw 25 q9 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   rw 22 q5 ∷
   rw 23 q18 ∷
   rw 22 q10 ∷
   rw 23 q10 ∷
   rw 24 q10 ∷
   rw 25 q16 ∷
   rw 26 q11 ∷
   rw 27 q10 ∷
   rw 28 q10 ∷
   rw 29 q10 ∷
   rw 30 q10 ∷
   rw 31 q10 ∷
   rw 32 q10 ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q7 ∷
   rw 34 q15 ∷
   rw 35 q7 ∷
   re 33 3 (CX03 ∷ []) ∷
   rw 34 q10 ∷
   rw 35 q10 ∷
   rw 36 q10 ∷
   rw 37 q10 ∷
   rw 38 q10 ∷
   rw 39 q10 ∷
   rw 40 q10 ∷
   rw 41 q10 ∷
   rw 42 q10 ∷
   rw 43 q10 ∷
   rw 44 q10 ∷
   rw 45 q10 ∷
   rw 46 q10 ∷
   rw 47 q10 ∷
   rw 48 q10 ∷
   rw 49 q10 ∷
   rw 50 q10 ∷
   rw 51 q10 ∷
   rw 52 q16 ∷
   rw 53 q16 ∷
   rw 54 q16 ∷
   rw 55 q16 ∷
   rw 56 q11 ∷
   rw 57 q10 ∷
   rw 58 q10 ∷
   rw 59 q10 ∷
   rw 60 q10 ∷
   rw 61 q10 ∷
   rw 62 q10 ∷
   rw 63 q10 ∷
   rw 64 q10 ∷
   rw 65 q10 ∷
   re 67 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 66 q7 ∷
   rw 67 q15 ∷
   rw 68 q7 ∷
   re 66 3 (CX03 ∷ []) ∷
   rw 67 q13 ∷
   rw 68 q13 ∷
   rw 69 q13 ∷
   rw 70 q19 ∷
   rw 71 q14 ∷
   rw 72 q13 ∷
   rw 73 q13 ∷
   rw 74 q13 ∷
   rw 75 q13 ∷
   rw 76 q13 ∷
   rw 77 q13 ∷
   rw 78 q17 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) lem-S2-at2013

-- resp TOFF203 CS12 TOFF203 CSd12: 1 steps
lem-resp-TOFF203-CS12-TOFF203-CSd12 : ⟪ (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-resp-TOFF203-CS12-TOFF203-CSd12 = derive (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  (rw⁻ 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) lem-S2-at1023

-- resp TOFF103 CS12 TOFF103 CSd12: 1 steps
lem-resp-TOFF103-CS12-TOFF103-CSd12 : ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-resp-TOFF103-CS12-TOFF103-CSd12 = derive (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q21 ∷ []) Eq.refl
