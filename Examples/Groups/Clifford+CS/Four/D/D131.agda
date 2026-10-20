{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D131 (W : Ws) where

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

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = eqn (CK21 ∷ Sw01 ∷ []) (Sw01 ∷ CK20 ∷ []) (wn 273 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q5 : Eqn
  q5 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q7 : Eqn
  q7 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q8 : Eqn
  q8 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wn 216 W)
  q9 : Eqn
  q9 = eqn (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ []) (wn 480 W)
  q10 : Eqn
  q10 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q11 : Eqn
  q11 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q12 : Eqn
  q12 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q13 : Eqn
  q13 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q14 : Eqn
  q14 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q15 : Eqn
  q15 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q16 : Eqn
  q16 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q17 : Eqn
  q17 = eqn (S2 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ []) (wn 477 W)
  q18 : Eqn
  q18 = eqn (CX21 ∷ Sw12 ∷ []) (Sw12 ∷ CX12 ∷ []) (wn 478 W)
  q19 : Eqn
  q19 = eqn (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) (wn 479 W)
  q20 : Eqn
  q20 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q21 : Eqn
  q21 = eqn (Sw12 ∷ CX12 ∷ []) (CX21 ∷ Sw12 ∷ []) (wn 50 W)
  q22 : Eqn
  q22 = eqn (Sw12 ∷ S2 ∷ []) (S1 ∷ Sw12 ∷ []) (wn 343 W)
  q23 : Eqn
  q23 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K))
  q24 : Eqn
  q24 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q25 : Eqn
  q25 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q26 : Eqn
  q26 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q27 : Eqn
  q27 = eqn (Sw12 ∷ ι1 ∷ []) (ι2 ∷ Sw12 ∷ []) (wn 364 W)
  q28 : Eqn
  q28 = eqn (K3 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K3 ∷ ι2 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wn 369 W)
  q29 : Eqn
  q29 = eqn (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) (wn 157 W)
  q30 : Eqn
  q30 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q31 : Eqn
  q31 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q32 : Eqn
  q32 = eqn (Sw01 ∷ CK20 ∷ []) (CK21 ∷ Sw01 ∷ []) (wn 275 W)
  q33 : Eqn
  q33 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q34 : Eqn
  q34 = eqn (Sw01 ∷ CK10 ∷ []) (CK01 ∷ Sw01 ∷ []) (wn 327 W)
  q35 : Eqn
  q35 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q36 : Eqn
  q36 = eqn (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) (wn 219 W)
  q37 : Eqn
  q37 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑)))
  q38 : Eqn
  q38 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q39 : Eqn
  q39 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q41 : Eqn
  q41 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q42 : Eqn
  q42 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q43 : Eqn
  q43 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q44 : Eqn
  q44 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q45 : Eqn
  q45 = eqn (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wn 337 W)
  q46 : Eqn
  q46 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q47 : Eqn
  q47 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- AXIOM LF @1203: 861 steps
lem-AXIOM-LF-at1203 : ⟪ (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S3 ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ Toff302 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ Toff302 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) ⟫ʷ
lem-AXIOM-LF-at1203 = derive (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S3 ∷ CK31 ∷ []) (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ Toff302 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ Toff302 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ [])
  (rw 80 q1 ∷
   re 79 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q2 ∷
   rw 80 q3 ∷
   rw⁻ 79 q2 ∷
   re 80 3 (CK30 ∷ []) ∷
   rw⁻ 78 q4 ∷
   rw 77 q5 ∷
   rw 76 q5 ∷
   rw 75 q5 ∷
   rw 74 q5 ∷
   rw 73 q5 ∷
   rw 72 q5 ∷
   rw 71 q3 ∷
   rw⁻ 70 q6 ∷
   rw 69 q5 ∷
   rw 68 q5 ∷
   rw 67 q5 ∷
   rw 66 q7 ∷
   rw 65 q8 ∷
   rw 64 q8 ∷
   rw 63 q8 ∷
   rw 62 q8 ∷
   rw 61 q8 ∷
   rw 60 q8 ∷
   rw 59 q8 ∷
   rw 58 q8 ∷
   rw 57 q8 ∷
   rw 56 q9 ∷
   rw 55 q10 ∷
   rw 54 q10 ∷
   rw 53 q10 ∷
   rw 52 q10 ∷
   rw 51 q8 ∷
   rw 50 q8 ∷
   rw 49 q8 ∷
   rw 48 q8 ∷
   rw 47 q8 ∷
   rw 46 q8 ∷
   rw 45 q8 ∷
   rw 44 q8 ∷
   rw 43 q8 ∷
   rw 42 q8 ∷
   rw 41 q8 ∷
   rw 40 q8 ∷
   rw 39 q8 ∷
   rw 38 q8 ∷
   rw 37 q8 ∷
   rw 36 q8 ∷
   rw 35 q8 ∷
   rw 34 q8 ∷
   rw 33 q7 ∷
   rw 32 q8 ∷
   rw 31 q8 ∷
   rw 30 q8 ∷
   rw 29 q8 ∷
   rw 28 q8 ∷
   rw 27 q8 ∷
   rw 26 q9 ∷
   rw 25 q10 ∷
   rw 24 q8 ∷
   rw 23 q8 ∷
   rw 22 q8 ∷
   re 21 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q2 ∷
   rw 22 q3 ∷
   rw⁻ 21 q2 ∷
   re 22 3 (CK30 ∷ []) ∷
   rw 20 q8 ∷
   rw 19 q9 ∷
   rw 18 q8 ∷
   rw 17 q8 ∷
   rw 16 q7 ∷
   rw 15 q8 ∷
   rw 14 q8 ∷
   rw 13 q8 ∷
   rw 12 q8 ∷
   rw 11 q8 ∷
   rw 10 q8 ∷
   rw 9 q10 ∷
   rw 8 q9 ∷
   rw 7 q8 ∷
   rw 6 q8 ∷
   rw 5 q8 ∷
   rw 4 q7 ∷
   rw 3 q5 ∷
   rw 2 q3 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 81 q11 ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q12 ∷
   rw 82 q13 ∷
   rw 80 q14 ∷
   re 81 5 (CK30 ∷ []) ∷
   rw⁻ 79 q15 ∷
   re 78 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 80 q16 ∷
   re 77 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 79 q16 ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 78 q16 ∷
   re 75 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 77 q16 ∷
   re 74 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 76 q16 ∷
   re 73 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 75 q16 ∷
   re 72 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 74 q16 ∷
   rw 71 q17 ∷
   re 70 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 72 q16 ∷
   re 69 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 71 q16 ∷
   re 68 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 70 q16 ∷
   rw 67 q18 ∷
   rw 66 q11 ∷
   re 67 3 (CS02 ∷ []) ∷
   rw 65 q11 ∷
   re 66 3 (CS02 ∷ []) ∷
   rw 64 q11 ∷
   re 65 3 (CS02 ∷ []) ∷
   rw 63 q11 ∷
   re 64 3 (CS02 ∷ []) ∷
   rw 62 q11 ∷
   re 63 3 (CS02 ∷ []) ∷
   rw 61 q11 ∷
   re 62 3 (CS02 ∷ []) ∷
   rw 60 q11 ∷
   re 61 3 (CS02 ∷ []) ∷
   rw 59 q11 ∷
   re 60 3 (CS02 ∷ []) ∷
   rw 58 q11 ∷
   re 59 3 (CS02 ∷ []) ∷
   rw 57 q11 ∷
   re 58 3 (CK20 ∷ []) ∷
   rw 56 q19 ∷
   rw 55 q19 ∷
   rw 54 q19 ∷
   rw 53 q19 ∷
   rw 52 q11 ∷
   re 53 3 (CS02 ∷ []) ∷
   rw 51 q11 ∷
   re 52 3 (CS02 ∷ []) ∷
   rw 50 q11 ∷
   re 51 3 (CS02 ∷ []) ∷
   rw 49 q11 ∷
   re 50 3 (CS02 ∷ []) ∷
   rw 48 q11 ∷
   re 49 3 (CS02 ∷ []) ∷
   rw 47 q11 ∷
   re 48 3 (CS02 ∷ []) ∷
   rw 46 q11 ∷
   re 47 3 (CS02 ∷ []) ∷
   rw 45 q11 ∷
   re 46 3 (CS02 ∷ []) ∷
   rw 44 q11 ∷
   re 45 3 (CS02 ∷ []) ∷
   rw 43 q11 ∷
   re 44 3 (CS02 ∷ []) ∷
   rw 42 q11 ∷
   re 43 3 (CS02 ∷ []) ∷
   rw 41 q11 ∷
   re 42 3 (CS02 ∷ []) ∷
   rw 40 q11 ∷
   re 41 3 (CS02 ∷ []) ∷
   rw 39 q11 ∷
   re 40 3 (CS02 ∷ []) ∷
   rw 38 q11 ∷
   re 39 3 (CS02 ∷ []) ∷
   rw 37 q11 ∷
   re 38 3 (CS02 ∷ []) ∷
   rw 36 q11 ∷
   re 37 3 (CS02 ∷ []) ∷
   rw 35 q11 ∷
   re 36 3 (CS02 ∷ []) ∷
   rw 34 q18 ∷
   rw 33 q11 ∷
   re 34 3 (CS02 ∷ []) ∷
   rw 32 q11 ∷
   re 33 3 (CS02 ∷ []) ∷
   rw 31 q11 ∷
   re 32 3 (CS02 ∷ []) ∷
   rw 30 q11 ∷
   re 31 3 (CS02 ∷ []) ∷
   rw 29 q11 ∷
   re 30 3 (CS02 ∷ []) ∷
   rw 28 q11 ∷
   re 29 3 (CS02 ∷ []) ∷
   rw 27 q11 ∷
   re 28 3 (CK20 ∷ []) ∷
   rw 26 q19 ∷
   rw 25 q11 ∷
   re 26 3 (CS02 ∷ []) ∷
   rw 24 q11 ∷
   re 25 3 (CS02 ∷ []) ∷
   rw 23 q11 ∷
   re 24 3 (CS02 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q12 ∷
   rw 24 q13 ∷
   rw 22 q14 ∷
   re 23 5 (CK30 ∷ []) ∷
   rw 21 q11 ∷
   re 22 3 (CS02 ∷ []) ∷
   rw 20 q11 ∷
   re 21 3 (CK20 ∷ []) ∷
   rw 19 q11 ∷
   re 20 3 (CS02 ∷ []) ∷
   rw 18 q11 ∷
   re 19 3 (CS02 ∷ []) ∷
   rw 17 q18 ∷
   rw 16 q11 ∷
   re 17 3 (CS02 ∷ []) ∷
   rw 15 q11 ∷
   re 16 3 (CS02 ∷ []) ∷
   rw 14 q11 ∷
   re 15 3 (CS02 ∷ []) ∷
   rw 13 q11 ∷
   re 14 3 (CS02 ∷ []) ∷
   rw 12 q11 ∷
   re 13 3 (CS02 ∷ []) ∷
   rw 11 q11 ∷
   re 12 3 (CS02 ∷ []) ∷
   rw 10 q19 ∷
   rw 9 q11 ∷
   re 10 3 (CK20 ∷ []) ∷
   rw 8 q11 ∷
   re 9 3 (CS02 ∷ []) ∷
   rw 7 q11 ∷
   re 8 3 (CS02 ∷ []) ∷
   rw 6 q11 ∷
   re 7 3 (CS02 ∷ []) ∷
   rw 5 q18 ∷
   re 4 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 6 q16 ∷
   re 3 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 5 q16 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 4 q16 ∷
   re 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 3 q16 ∷
   rw 2 q20 ∷
   rw 3 q11 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw 4 q11 ∷
   re 2 3 (CS02 ∷ []) ∷
   rw 5 q11 ∷
   re 3 3 (CK20 ∷ []) ∷
   rw 6 q11 ∷
   re 4 3 (CS02 ∷ []) ∷
   rw 7 q11 ∷
   re 5 3 (CK20 ∷ []) ∷
   rw 8 q11 ∷
   re 6 3 (CK20 ∷ []) ∷
   rw 7 q21 ∷
   re 9 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 8 q16 ∷
   rw 9 q22 ∷
   re 11 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 10 q16 ∷
   rw 11 q22 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q16 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q16 ∷
   re 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q16 ∷
   re 16 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 15 q16 ∷
   rw 16 q22 ∷
   re 18 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q16 ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 18 q16 ∷
   re 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 q16 ∷
   re 21 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 20 q16 ∷
   re 22 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q16 ∷
   re 23 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 22 q16 ∷
   rw 23 q21 ∷
   re 25 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 24 q16 ∷
   re 26 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 25 q16 ∷
   re 27 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 26 q16 ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 27 q16 ∷
   re 29 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 28 q16 ∷
   re 30 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 29 q16 ∷
   re 31 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 30 q23 ∷
   rw 31 q24 ∷
   rw 32 q21 ∷
   rw 33 q25 ∷
   rw 34 q21 ∷
   rw 35 q26 ∷
   rw 36 q23 ∷
   rw 37 q27 ∷
   rw 30 q28 ∷
   re 30 8 (Toff312 ∷ []) ∷
   rw 33 q11 ∷
   re 31 3 (CS02 ∷ []) ∷
   rw 34 q11 ∷
   re 32 3 (CS02 ∷ []) ∷
   rw 35 q11 ∷
   re 33 3 (CS02 ∷ []) ∷
   rw 36 q11 ∷
   re 34 3 (CK20 ∷ []) ∷
   rw 37 q11 ∷
   re 35 3 (CS02 ∷ []) ∷
   rw 38 q11 ∷
   re 36 3 (CS02 ∷ []) ∷
   rw 37 q29 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q12 ∷
   rw⁻ 40 q30 ∷
   rw 41 q14 ∷
   re 38 5 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q12 ∷
   rw⁻ 41 q30 ∷
   rw 42 q14 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q12 ∷
   rw⁻ 42 q30 ∷
   rw 43 q14 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q12 ∷
   rw⁻ 43 q30 ∷
   rw 44 q14 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q12 ∷
   rw⁻ 44 q30 ∷
   rw 45 q14 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q12 ∷
   rw⁻ 45 q30 ∷
   rw 46 q14 ∷
   re 43 5 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q12 ∷
   rw⁻ 46 q13 ∷
   rw 47 q14 ∷
   re 44 5 (CK30 ∷ []) ∷
   rw 45 q15 ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q12 ∷
   rw⁻ 48 q30 ∷
   rw 49 q14 ∷
   re 46 5 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q12 ∷
   rw⁻ 49 q30 ∷
   rw 50 q14 ∷
   re 47 5 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q12 ∷
   rw⁻ 50 q30 ∷
   rw 51 q14 ∷
   re 48 5 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q12 ∷
   rw⁻ 51 q30 ∷
   rw 52 q14 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q12 ∷
   rw⁻ 52 q30 ∷
   rw 53 q14 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q12 ∷
   rw⁻ 53 q30 ∷
   rw 54 q14 ∷
   re 51 5 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q12 ∷
   rw⁻ 54 q30 ∷
   rw 55 q14 ∷
   re 52 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q12 ∷
   rw⁻ 55 q30 ∷
   rw 56 q14 ∷
   re 53 5 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q12 ∷
   rw⁻ 56 q30 ∷
   rw 57 q14 ∷
   re 54 5 (CS03 ∷ []) ∷
   rw 55 q29 ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q12 ∷
   rw⁻ 58 q30 ∷
   rw 59 q14 ∷
   re 56 5 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q12 ∷
   rw⁻ 59 q30 ∷
   rw 60 q14 ∷
   re 57 5 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q12 ∷
   rw⁻ 60 q30 ∷
   rw 61 q14 ∷
   re 58 5 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q12 ∷
   rw⁻ 61 q13 ∷
   rw 62 q14 ∷
   re 59 5 (CK30 ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q12 ∷
   rw⁻ 62 q30 ∷
   rw 63 q14 ∷
   re 60 5 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q12 ∷
   rw⁻ 63 q30 ∷
   rw 64 q14 ∷
   re 61 5 (CS03 ∷ []) ∷
   re 63 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 62 q23 ∷
   rw 63 q24 ∷
   rw 64 q21 ∷
   rw 65 q25 ∷
   rw 66 q21 ∷
   rw 67 q26 ∷
   rw 68 q23 ∷
   rw 69 q27 ∷
   rw 62 q28 ∷
   re 62 8 (Toff312 ∷ []) ∷
   rw 65 q11 ∷
   re 63 3 (CS02 ∷ []) ∷
   rw 66 q11 ∷
   re 64 3 (CS02 ∷ []) ∷
   rw 67 q11 ∷
   re 65 3 (CK20 ∷ []) ∷
   rw 68 q11 ∷
   re 66 3 (CS02 ∷ []) ∷
   rw 69 q11 ∷
   re 67 3 (CK20 ∷ []) ∷
   rw 70 q11 ∷
   re 68 3 (CK20 ∷ []) ∷
   rw 69 q29 ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q12 ∷
   rw⁻ 72 q13 ∷
   rw 73 q14 ∷
   re 70 5 (CK30 ∷ []) ∷
   rw 71 q15 ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q12 ∷
   rw⁻ 74 q13 ∷
   rw 75 q14 ∷
   re 72 5 (CK30 ∷ []) ∷
   rw 73 q15 ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q12 ∷
   rw⁻ 76 q30 ∷
   rw 77 q14 ∷
   re 74 5 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q12 ∷
   rw⁻ 77 q30 ∷
   rw 78 q14 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q12 ∷
   rw⁻ 78 q30 ∷
   rw 79 q14 ∷
   re 76 5 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q12 ∷
   rw⁻ 79 q13 ∷
   rw 80 q14 ∷
   re 77 5 (CK30 ∷ []) ∷
   rw 78 q15 ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q12 ∷
   rw⁻ 81 q30 ∷
   rw 82 q14 ∷
   re 79 5 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q12 ∷
   rw⁻ 82 q30 ∷
   rw 83 q14 ∷
   re 80 5 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q12 ∷
   rw⁻ 83 q30 ∷
   rw 84 q14 ∷
   re 81 5 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q12 ∷
   rw⁻ 84 q30 ∷
   rw 85 q14 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q12 ∷
   rw⁻ 85 q30 ∷
   rw 86 q14 ∷
   re 83 5 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q12 ∷
   rw⁻ 86 q30 ∷
   rw 87 q14 ∷
   re 84 5 (CS03 ∷ []) ∷
   rw 85 q29 ∷
   re 87 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q12 ∷
   rw⁻ 88 q30 ∷
   rw 89 q14 ∷
   re 86 5 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q12 ∷
   rw⁻ 89 q30 ∷
   rw 90 q14 ∷
   re 87 5 (CS03 ∷ []) ∷
   re 89 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q12 ∷
   rw⁻ 90 q13 ∷
   rw 91 q14 ∷
   re 88 5 (CK30 ∷ []) ∷
   re 90 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q12 ∷
   rw⁻ 91 q30 ∷
   rw 92 q14 ∷
   re 89 5 (CS03 ∷ []) ∷
   re 91 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 90 q12 ∷
   rw⁻ 92 q13 ∷
   rw 93 q14 ∷
   re 90 5 (CK30 ∷ []) ∷
   re 92 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 91 q12 ∷
   rw⁻ 93 q13 ∷
   rw 94 q14 ∷
   re 91 5 (CK30 ∷ []) ∷
   rw 92 q16 ∷
   rw 0 q31 ∷
   rw 1 q31 ∷
   rw 2 q32 ∷
   rw 3 q31 ∷
   rw 4 q32 ∷
   rw 5 q32 ∷
   rw 6 q33 ∷
   rw 7 q34 ∷
   rw 8 q35 ∷
   rw 9 q34 ∷
   rw 10 q35 ∷
   rw 11 q36 ∷
   rw 12 q36 ∷
   rw 13 q36 ∷
   rw 14 q34 ∷
   rw 15 q35 ∷
   rw 16 q36 ∷
   rw 17 q36 ∷
   rw 18 q36 ∷
   rw 19 q36 ∷
   rw 20 q36 ∷
   rw 21 q36 ∷
   rw 22 q33 ∷
   rw 23 q36 ∷
   rw 24 q36 ∷
   rw 25 q34 ∷
   rw 26 q36 ∷
   rw 27 q34 ∷
   rw 28 q34 ∷
   re 30 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 29 q37 ∷
   rw 30 q38 ∷
   rw 31 q39 ∷
   rw 32 q40 ∷
   rw 33 q39 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   rw 35 q41 ∷
   rw 36 q2 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q37 ∷
   rw 36 q42 ∷
   rw 29 q1 ∷
   rw 30 q37 ∷
   rw 31 q38 ∷
   rw 32 q43 ∷
   rw 33 q40 ∷
   rw 34 q43 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   rw 36 q31 ∷
   rw 37 q2 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 36 q37 ∷
   rw 37 q44 ∷
   rw 30 q45 ∷
   re 30 8 (Toff312 ∷ []) ∷
   re 29 3 (Toff302 ∷ []) ∷
   rw 30 q31 ∷
   rw 31 q31 ∷
   rw 32 q31 ∷
   rw 33 q32 ∷
   rw 34 q31 ∷
   rw 35 q31 ∷
   rw 36 q46 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   rw 38 q31 ∷
   rw 39 q2 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   rw 39 q31 ∷
   rw 40 q2 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   rw 40 q31 ∷
   rw 41 q2 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   rw 41 q31 ∷
   rw 42 q2 ∷
   re 40 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   rw 42 q31 ∷
   rw 43 q2 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   rw 43 q31 ∷
   rw 44 q2 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   rw 44 q32 ∷
   rw 45 q2 ∷
   re 43 3 (CK31 ∷ []) ∷
   rw 44 q4 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   rw 46 q31 ∷
   rw 47 q2 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   rw 47 q31 ∷
   rw 48 q2 ∷
   re 46 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   rw 48 q31 ∷
   rw 49 q2 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   rw 49 q31 ∷
   rw 50 q2 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   rw 50 q31 ∷
   rw 51 q2 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q2 ∷
   rw 51 q31 ∷
   rw 52 q2 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   rw 52 q31 ∷
   rw 53 q2 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   rw 53 q31 ∷
   rw 54 q2 ∷
   re 52 3 (CS13 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   rw 54 q31 ∷
   rw 55 q2 ∷
   re 53 3 (CS13 ∷ []) ∷
   rw 54 q46 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   rw 56 q31 ∷
   rw 57 q2 ∷
   re 55 3 (CS13 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   rw 57 q31 ∷
   rw 58 q2 ∷
   re 56 3 (CS13 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q2 ∷
   rw 58 q31 ∷
   rw 59 q2 ∷
   re 57 3 (CS13 ∷ []) ∷
   re 59 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 58 q2 ∷
   rw 59 q32 ∷
   rw 60 q2 ∷
   re 58 3 (CK31 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q2 ∷
   rw 60 q31 ∷
   rw 61 q2 ∷
   re 59 3 (CS13 ∷ []) ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q2 ∷
   rw 61 q31 ∷
   rw 62 q2 ∷
   re 60 3 (CS13 ∷ []) ∷
   re 62 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 61 q37 ∷
   rw 62 q38 ∷
   rw 63 q39 ∷
   rw 64 q40 ∷
   rw 65 q39 ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 66 q2 ∷
   rw 67 q41 ∷
   rw 68 q2 ∷
   re 66 3 (CS03 ∷ []) ∷
   rw 67 q37 ∷
   rw 68 q42 ∷
   rw 61 q1 ∷
   rw 62 q37 ∷
   rw 63 q38 ∷
   rw 64 q43 ∷
   rw 65 q40 ∷
   rw 66 q43 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q2 ∷
   rw 68 q31 ∷
   rw 69 q2 ∷
   re 67 3 (CS13 ∷ []) ∷
   rw 68 q37 ∷
   rw 69 q44 ∷
   rw 62 q45 ∷
   re 62 8 (Toff312 ∷ []) ∷
   re 61 3 (Toff302 ∷ []) ∷
   rw 62 q31 ∷
   rw 63 q31 ∷
   rw 64 q32 ∷
   rw 65 q31 ∷
   rw 66 q32 ∷
   rw 67 q32 ∷
   rw 68 q46 ∷
   re 70 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 69 q2 ∷
   rw 70 q32 ∷
   rw 71 q2 ∷
   re 69 3 (CK31 ∷ []) ∷
   rw 70 q4 ∷
   re 72 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 71 q2 ∷
   rw 72 q32 ∷
   rw 73 q2 ∷
   re 71 3 (CK31 ∷ []) ∷
   rw 72 q4 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   rw 74 q31 ∷
   rw 75 q2 ∷
   re 73 3 (CS13 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   rw 75 q31 ∷
   rw 76 q2 ∷
   re 74 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q2 ∷
   rw 76 q31 ∷
   rw 77 q2 ∷
   re 75 3 (CS13 ∷ []) ∷
   re 77 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 76 q2 ∷
   rw 77 q32 ∷
   rw 78 q2 ∷
   re 76 3 (CK31 ∷ []) ∷
   rw 77 q4 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q2 ∷
   rw 79 q31 ∷
   rw 80 q2 ∷
   re 78 3 (CS13 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q2 ∷
   rw 80 q31 ∷
   rw 81 q2 ∷
   re 79 3 (CS13 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   rw 81 q31 ∷
   rw 82 q2 ∷
   re 80 3 (CS13 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   rw 82 q31 ∷
   rw 83 q2 ∷
   re 81 3 (CS13 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   rw 83 q31 ∷
   rw 84 q2 ∷
   re 82 3 (CS13 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q2 ∷
   rw 84 q31 ∷
   rw 85 q2 ∷
   re 83 3 (CS13 ∷ []) ∷
   rw 84 q46 ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q2 ∷
   rw 86 q31 ∷
   rw 87 q2 ∷
   re 85 3 (CS13 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q2 ∷
   rw 87 q31 ∷
   rw 88 q2 ∷
   re 86 3 (CS13 ∷ []) ∷
   re 88 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 87 q2 ∷
   rw 88 q32 ∷
   rw 89 q2 ∷
   re 87 3 (CK31 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q2 ∷
   rw 89 q31 ∷
   rw 90 q2 ∷
   re 88 3 (CS13 ∷ []) ∷
   re 90 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 89 q2 ∷
   rw 90 q32 ∷
   rw 91 q2 ∷
   re 89 3 (CK31 ∷ []) ∷
   re 91 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 90 q2 ∷
   rw 91 q32 ∷
   rw 92 q2 ∷
   re 90 3 (CK31 ∷ []) ∷
   rw 91 q47 ∷ []) Eq.refl
