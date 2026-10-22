{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD709 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D709 (W : Ws) (Sᴰ : SD709) where

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
  lem-hyb-sym-23-at0321 : St 2004
  lem-hyb-sym-23-at0321 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q4 : Eqn
  q4 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ []) (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ []) (wn 1208 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q13 : Eqn
  q13 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ []) (wn 1209 W)
  q14 : Eqn
  q14 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S1 ∷ CK10 ∷ []) (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK20 ∷ []) (lem-hyb-sym-23-at0321)
  q15 : Eqn
  q15 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q16 : Eqn
  q16 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q17 : Eqn
  q17 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q18 : Eqn
  q18 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q19 : Eqn
  q19 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q20 : Eqn
  q20 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ []) (wn 1199 W)
  q21 : Eqn
  q21 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q22 : Eqn
  q22 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q23 : Eqn
  q23 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 1200 W)

-- respell hyb CS02 CS02 CK20 CS02 CX23 CS03 CS03 CS03  -> CS01 CS01 CK10 CS01 CX13 CS03 CS03 CS03 : 659 steps
lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) ⟫ʷ
lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ [])
  (rw 21 q1 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q2 ∷
   rw 21 q3 ∷
   rw⁻ 20 q2 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q2 ∷
   rw 20 q4 ∷
   rw⁻ 19 q2 ∷
   re 20 3 (CK31 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q2 ∷
   rw 19 q3 ∷
   rw⁻ 18 q2 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q2 ∷
   rw 18 q3 ∷
   rw⁻ 17 q2 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw⁻ 16 q5 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q2 ∷
   rw 16 q3 ∷
   rw⁻ 15 q2 ∷
   re 16 3 (CS13 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw 15 q3 ∷
   rw⁻ 14 q2 ∷
   re 15 3 (CS13 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw 14 q3 ∷
   rw⁻ 13 q2 ∷
   re 14 3 (CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 13 q3 ∷
   rw⁻ 12 q2 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q2 ∷
   rw 12 q3 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw 11 q3 ∷
   rw⁻ 10 q2 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 9 q6 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw 9 q4 ∷
   rw⁻ 8 q2 ∷
   re 9 3 (CK31 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw 8 q3 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (CS13 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 7 q3 ∷
   rw⁻ 6 q2 ∷
   re 7 3 (CS13 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q2 ∷
   rw 6 q3 ∷
   rw⁻ 5 q2 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 4 q5 ∷
   rw 3 q3 ∷
   rw 2 q4 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q7 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q8 ∷
   rw 2 q2 ∷
   re 0 3 (CS03 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q8 ∷
   rw 3 q2 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q9 ∷
   rw 4 q2 ∷
   re 2 3 (CK30 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   rw 4 q8 ∷
   rw 5 q2 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q10 ∷
   rw 5 q8 ∷
   rw 6 q8 ∷
   rw 7 q8 ∷
   rw 8 q9 ∷
   rw 9 q11 ∷
   rw 10 q8 ∷
   rw 11 q8 ∷
   rw 12 q8 ∷
   rw 13 q8 ∷
   rw 14 q8 ∷
   rw 15 q8 ∷
   rw 16 q10 ∷
   rw 17 q8 ∷
   rw 18 q8 ∷
   rw 19 q9 ∷
   rw 20 q8 ∷
   rw 21 q12 ∷
   rw 78 q1 ∷
   rw 77 q3 ∷
   rw 76 q3 ∷
   rw 75 q3 ∷
   rw 74 q3 ∷
   rw 73 q3 ∷
   rw 72 q3 ∷
   rw 71 q4 ∷
   rw⁻ 70 q11 ∷
   rw 69 q3 ∷
   rw 68 q3 ∷
   rw 67 q3 ∷
   rw⁻ 66 q5 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q2 ∷
   rw 66 q3 ∷
   rw⁻ 65 q2 ∷
   re 66 3 (CS13 ∷ []) ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q2 ∷
   rw 65 q3 ∷
   rw⁻ 64 q2 ∷
   re 65 3 (CS13 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q2 ∷
   rw 64 q3 ∷
   rw⁻ 63 q2 ∷
   re 64 3 (CS13 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 64 q2 ∷
   rw 63 q3 ∷
   rw⁻ 62 q2 ∷
   re 63 3 (CS13 ∷ []) ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 63 q2 ∷
   rw 62 q3 ∷
   rw⁻ 61 q2 ∷
   re 62 3 (CS13 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 62 q2 ∷
   rw 61 q3 ∷
   rw⁻ 60 q2 ∷
   re 61 3 (CS13 ∷ []) ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 61 q2 ∷
   rw 60 q3 ∷
   rw⁻ 59 q2 ∷
   re 60 3 (CS13 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q2 ∷
   rw 59 q3 ∷
   rw⁻ 58 q2 ∷
   re 59 3 (CS13 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q2 ∷
   rw 58 q3 ∷
   rw⁻ 57 q2 ∷
   re 58 3 (CS13 ∷ []) ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q2 ∷
   rw 57 q4 ∷
   rw⁻ 56 q2 ∷
   re 57 3 (CK31 ∷ []) ∷
   rw⁻ 55 q6 ∷
   rw⁻ 54 q6 ∷
   rw⁻ 53 q6 ∷
   rw⁻ 52 q6 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q2 ∷
   rw 52 q3 ∷
   rw⁻ 51 q2 ∷
   re 52 3 (CS13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q2 ∷
   rw 51 q3 ∷
   rw⁻ 50 q2 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q2 ∷
   rw 50 q3 ∷
   rw⁻ 49 q2 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q2 ∷
   rw 49 q3 ∷
   rw⁻ 48 q2 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q2 ∷
   rw 48 q3 ∷
   rw⁻ 47 q2 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q2 ∷
   rw 47 q3 ∷
   rw⁻ 46 q2 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q2 ∷
   rw 46 q3 ∷
   rw⁻ 45 q2 ∷
   re 46 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q2 ∷
   rw 45 q3 ∷
   rw⁻ 44 q2 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q2 ∷
   rw 44 q3 ∷
   rw⁻ 43 q2 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q2 ∷
   rw 43 q3 ∷
   rw⁻ 42 q2 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q2 ∷
   rw 42 q3 ∷
   rw⁻ 41 q2 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q2 ∷
   rw 41 q3 ∷
   rw⁻ 40 q2 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q2 ∷
   rw 40 q3 ∷
   rw⁻ 39 q2 ∷
   re 40 3 (CS13 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q2 ∷
   rw 39 q3 ∷
   rw⁻ 38 q2 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q2 ∷
   rw 38 q3 ∷
   rw⁻ 37 q2 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q2 ∷
   rw 37 q3 ∷
   rw⁻ 36 q2 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q2 ∷
   rw 36 q3 ∷
   rw⁻ 35 q2 ∷
   re 36 3 (CS13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q2 ∷
   rw 35 q3 ∷
   rw⁻ 34 q2 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw⁻ 33 q5 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q2 ∷
   rw 33 q3 ∷
   rw⁻ 32 q2 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q2 ∷
   rw 32 q3 ∷
   rw⁻ 31 q2 ∷
   re 32 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q2 ∷
   rw 31 q3 ∷
   rw⁻ 30 q2 ∷
   re 31 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q2 ∷
   rw 30 q3 ∷
   rw⁻ 29 q2 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q2 ∷
   rw 29 q3 ∷
   rw⁻ 28 q2 ∷
   re 29 3 (CS13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q2 ∷
   rw 28 q3 ∷
   rw⁻ 27 q2 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q2 ∷
   rw 27 q4 ∷
   rw⁻ 26 q2 ∷
   re 27 3 (CK31 ∷ []) ∷
   rw⁻ 25 q6 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q2 ∷
   rw 25 q3 ∷
   rw⁻ 24 q2 ∷
   re 25 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q2 ∷
   rw 24 q3 ∷
   rw⁻ 23 q2 ∷
   re 24 3 (CS13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q2 ∷
   rw 23 q3 ∷
   rw⁻ 22 q2 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 23 q13 ∷
   rw 22 q8 ∷
   rw 23 q8 ∷
   rw 24 q8 ∷
   rw 25 q11 ∷
   rw 26 q9 ∷
   rw 27 q8 ∷
   rw 28 q8 ∷
   rw 29 q8 ∷
   rw 30 q8 ∷
   rw 31 q8 ∷
   rw 32 q8 ∷
   rw 33 q10 ∷
   rw 34 q8 ∷
   rw 35 q8 ∷
   rw 36 q8 ∷
   rw 37 q8 ∷
   rw 38 q8 ∷
   rw 39 q8 ∷
   rw 40 q8 ∷
   rw 41 q8 ∷
   rw 42 q8 ∷
   rw 43 q8 ∷
   rw 44 q8 ∷
   rw 45 q8 ∷
   rw 46 q8 ∷
   rw 47 q8 ∷
   rw 48 q8 ∷
   rw 49 q8 ∷
   rw 50 q8 ∷
   rw 51 q8 ∷
   rw 52 q11 ∷
   rw 53 q11 ∷
   rw 54 q11 ∷
   rw 55 q11 ∷
   rw 56 q9 ∷
   rw 57 q8 ∷
   rw 58 q8 ∷
   rw 59 q8 ∷
   rw 60 q8 ∷
   rw 61 q8 ∷
   rw 62 q8 ∷
   rw 63 q8 ∷
   rw 64 q8 ∷
   rw 65 q8 ∷
   rw 66 q10 ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q2 ∷
   rw 68 q8 ∷
   rw 69 q2 ∷
   re 67 3 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 68 q2 ∷
   rw 69 q8 ∷
   rw 70 q2 ∷
   re 68 3 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 69 q2 ∷
   rw 70 q8 ∷
   rw 71 q2 ∷
   re 69 3 (CS03 ∷ []) ∷
   rw 70 q6 ∷
   re 72 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 71 q2 ∷
   rw 72 q9 ∷
   rw 73 q2 ∷
   re 71 3 (CK30 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 72 q2 ∷
   rw 73 q8 ∷
   rw 74 q2 ∷
   re 72 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   rw 74 q8 ∷
   rw 75 q2 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   rw 75 q8 ∷
   rw 76 q2 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q2 ∷
   rw 76 q8 ∷
   rw 77 q2 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 76 q2 ∷
   rw 77 q8 ∷
   rw 78 q2 ∷
   re 76 3 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q2 ∷
   rw 78 q8 ∷
   rw 79 q2 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 78 q12 ∷
   rw 0 q14 ∷
   rw 21 q15 ∷
   rw 20 q16 ∷
   rw 19 q17 ∷
   rw 18 q16 ∷
   rw 17 q16 ∷
   re 16 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q18 ∷
   rw 15 q16 ∷
   rw 14 q16 ∷
   rw 13 q16 ∷
   rw 12 q16 ∷
   rw 11 q16 ∷
   rw 10 q16 ∷
   rw 9 q19 ∷
   rw 8 q17 ∷
   rw 7 q16 ∷
   rw 6 q16 ∷
   rw 5 q16 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q18 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q18 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q18 ∷
   rw 1 q20 ∷
   rw⁻ 0 q16 ∷
   rw⁻ 1 q16 ∷
   rw⁻ 2 q17 ∷
   rw⁻ 3 q16 ∷
   rw 6 q15 ∷
   re 4 3 (CX13 ∷ []) ∷
   rw 7 q15 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 8 q15 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q15 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 10 q15 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q21 ∷
   rw 12 q15 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 13 q15 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q15 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q15 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q15 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q15 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q15 ∷
   re 16 3 (CX13 ∷ []) ∷
   rw 19 q15 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q15 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q15 ∷
   re 19 3 (CK30 ∷ []) ∷
   rw 22 q15 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q18 ∷
   rw 78 q15 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q18 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q18 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q18 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q18 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q18 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q18 ∷
   re 71 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 73 q18 ∷
   rw 70 q22 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q18 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q18 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q18 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 68 q18 ∷
   rw 65 q16 ∷
   rw 64 q16 ∷
   rw 63 q16 ∷
   rw 62 q16 ∷
   rw 61 q16 ∷
   rw 60 q16 ∷
   rw 59 q16 ∷
   rw 58 q16 ∷
   rw 57 q16 ∷
   rw 56 q17 ∷
   rw 55 q19 ∷
   rw 54 q19 ∷
   rw 53 q19 ∷
   rw 52 q19 ∷
   rw 51 q16 ∷
   rw 50 q16 ∷
   rw 49 q16 ∷
   rw 48 q16 ∷
   rw 47 q16 ∷
   rw 46 q16 ∷
   rw 45 q16 ∷
   rw 44 q16 ∷
   rw 43 q16 ∷
   rw 42 q16 ∷
   rw 41 q16 ∷
   rw 40 q16 ∷
   rw 39 q16 ∷
   rw 38 q16 ∷
   rw 37 q16 ∷
   rw 36 q16 ∷
   rw 35 q16 ∷
   rw 34 q16 ∷
   re 33 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q18 ∷
   rw 32 q16 ∷
   rw 31 q16 ∷
   rw 30 q16 ∷
   rw 29 q16 ∷
   rw 28 q16 ∷
   rw 27 q16 ∷
   rw 26 q17 ∷
   rw 25 q19 ∷
   rw 24 q16 ∷
   rw 23 q16 ∷
   rw 22 q16 ∷
   rw 23 q23 ∷
   rw 24 q15 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q15 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q15 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q21 ∷
   rw 28 q15 ∷
   re 26 3 (CK30 ∷ []) ∷
   rw 29 q15 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q15 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q15 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q15 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q15 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q15 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q15 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 36 q15 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q15 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q15 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q15 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 40 q15 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 41 q15 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q15 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 43 q15 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 44 q15 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 45 q15 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 46 q15 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 47 q15 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 48 q15 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 49 q15 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 50 q15 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 51 q15 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 52 q15 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 53 q15 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q21 ∷
   rw 53 q21 ∷
   rw 54 q21 ∷
   rw 55 q21 ∷
   rw 58 q15 ∷
   re 56 3 (CK30 ∷ []) ∷
   rw 59 q15 ∷
   re 57 3 (CS03 ∷ []) ∷
   rw 60 q15 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 61 q15 ∷
   re 59 3 (CS03 ∷ []) ∷
   rw 62 q15 ∷
   re 60 3 (CS03 ∷ []) ∷
   rw 63 q15 ∷
   re 61 3 (CS03 ∷ []) ∷
   rw 64 q15 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 65 q15 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 66 q15 ∷
   re 64 3 (CS03 ∷ []) ∷
   rw 67 q15 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 68 q15 ∷
   re 66 3 (CX13 ∷ []) ∷
   rw⁻ 67 q16 ∷
   rw⁻ 68 q16 ∷
   rw⁻ 69 q16 ∷
   rw⁻ 70 q19 ∷
   rw⁻ 71 q17 ∷
   rw⁻ 72 q16 ∷
   rw⁻ 73 q16 ∷
   rw⁻ 74 q16 ∷
   rw⁻ 75 q16 ∷
   rw⁻ 76 q16 ∷
   rw⁻ 77 q16 ∷
   rw 78 q18 ∷ []) Eq.refl
