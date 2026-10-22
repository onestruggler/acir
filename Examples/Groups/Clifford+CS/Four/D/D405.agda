{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D405 (W : Ws) where

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
  q1 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = wE 7 W
  q3 : Eqn
  q3 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 1137 W
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = wE 142 W
  q8 : Eqn
  q8 = wE 31 W
  q9 : Eqn
  q9 = wE 36 W
  q10 : Eqn
  q10 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q11 : Eqn
  q11 = wE 37 W
  q12 : Eqn
  q12 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q13 : Eqn
  q13 = wE 846 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] part2: 149 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-part2 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-part2 = derive (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw⁻ 45 q1 ∷
   rw 44 q2 ∷
   rw⁻ 43 q1 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q1 ∷
   rw 43 q2 ∷
   rw⁻ 42 q1 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q1 ∷
   rw 42 q2 ∷
   rw⁻ 41 q1 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw⁻ 40 q3 ∷
   re 39 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q1 ∷
   rw 40 q4 ∷
   rw⁻ 39 q1 ∷
   re 40 3 (CK31 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q1 ∷
   rw 39 q2 ∷
   rw⁻ 38 q1 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q1 ∷
   rw 38 q2 ∷
   rw⁻ 37 q1 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q1 ∷
   rw 37 q2 ∷
   rw⁻ 36 q1 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw⁻ 35 q3 ∷
   re 34 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q1 ∷
   rw 35 q4 ∷
   rw⁻ 34 q1 ∷
   re 35 3 (CK31 ∷ []) ∷
   rw⁻ 33 q3 ∷
   re 32 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q1 ∷
   rw 33 q4 ∷
   rw⁻ 32 q1 ∷
   re 33 3 (CK31 ∷ []) ∷
   rw 33 q5 ∷
   rw 32 q6 ∷
   rw 33 q6 ∷
   rw 34 q6 ∷
   rw 35 q7 ∷
   rw 36 q6 ∷
   rw 37 q6 ∷
   re 39 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   rw 39 q7 ∷
   rw 40 q1 ∷
   re 38 3 (CK30 ∷ []) ∷
   rw 39 q3 ∷
   re 41 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   rw 41 q7 ∷
   rw 42 q1 ∷
   re 40 3 (CK30 ∷ []) ∷
   rw 41 q3 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   rw 43 q6 ∷
   rw 44 q1 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   rw 44 q6 ∷
   rw 45 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   rw 45 q6 ∷
   rw 46 q1 ∷
   re 44 3 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   rw 46 q7 ∷
   rw 47 q1 ∷
   re 45 3 (CK30 ∷ []) ∷
   rw 46 q3 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   rw 48 q6 ∷
   rw 49 q1 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   rw 49 q6 ∷
   rw 50 q1 ∷
   re 48 3 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   rw 50 q6 ∷
   rw 51 q1 ∷
   re 49 3 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   rw 51 q6 ∷
   rw 52 q1 ∷
   re 50 3 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   rw 52 q6 ∷
   rw 53 q1 ∷
   re 51 3 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   rw 53 q6 ∷
   rw 54 q1 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q8 ∷
   re 32 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 31 q9 ∷
   rw⁻ 32 q10 ∷
   rw 33 q11 ∷
   re 31 3 (CS02 ∷ []) ∷
   re 33 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 32 q9 ∷
   rw⁻ 33 q10 ∷
   rw 34 q11 ∷
   re 32 3 (CS02 ∷ []) ∷
   re 34 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 33 q9 ∷
   rw⁻ 34 q10 ∷
   rw 35 q11 ∷
   re 33 3 (CS02 ∷ []) ∷
   re 35 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 34 q9 ∷
   rw⁻ 35 q12 ∷
   rw 36 q11 ∷
   re 34 3 (CK20 ∷ []) ∷
   re 36 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 35 q9 ∷
   rw⁻ 36 q10 ∷
   rw 37 q11 ∷
   re 35 3 (CS02 ∷ []) ∷
   re 37 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 36 q9 ∷
   rw⁻ 37 q10 ∷
   rw 38 q11 ∷
   re 36 3 (CS02 ∷ []) ∷
   rw 25 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 1 W
  q15 : Eqn
  q15 = wE 352 W
  q16 : Eqn
  q16 = eqn (CS01⁻ ∷ CK23 ∷ []) (CK23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CK₀₁))
  q17 : Eqn
  q17 = wE 357 W
  q18 : Eqn
  q18 = wE 3 W
  q19 : Eqn
  q19 = wE 1138 W
  q20 : Eqn
  q20 = eqn (CS01 ∷ CK23 ∷ []) (CK23 ∷ CS01 ∷ []) (low-comm (CS) (CK₀₁))
  q21 : Eqn
  q21 = wE 599 W
  q22 : Eqn
  q22 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q23 : Eqn
  q23 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q24 : Eqn
  q24 = wE 1139 W
  q25 : Eqn
  q25 = wE 20 W
  q26 : Eqn
  q26 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q27 : Eqn
  q27 = wE 49 W
  q28 : Eqn
  q28 = wE 1140 W
  q29 : Eqn
  q29 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q30 : Eqn
  q30 = wE 607 W
  q31 : Eqn
  q31 = wE 5 W
  q32 : Eqn
  q32 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q33 : Eqn
  q33 = wE 76 W
  q34 : Eqn
  q34 = wE 1141 W
  q35 : Eqn
  q35 = wE 29 W
  q36 : Eqn
  q36 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q37 : Eqn
  q37 = wE 894 W
  q38 : Eqn
  q38 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q39 : Eqn
  q39 = wE 21 W
  q40 : Eqn
  q40 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS)))
  q41 : Eqn
  q41 = wE 51 W
  q42 : Eqn
  q42 = wE 1142 W
  q43 : Eqn
  q43 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q44 : Eqn
  q44 = wE 609 W
  q45 : Eqn
  q45 = wE 353 W
  q46 : Eqn
  q46 = eqn (CS01⁻ ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((S • CK₀₁)))
  q47 : Eqn
  q47 = wE 358 W
  q48 : Eqn
  q48 = wE 1143 W
  q49 : Eqn
  q49 = eqn (CS01 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S • CK₀₁)))
  q50 : Eqn
  q50 = wE 604 W

-- groups [CK10 CS03 CKd10 CSd03] [CK12 CS13 CS12 CX32 CSd12 CX32 CKd12]: 163 steps
lem-groups-CK10-CS03-CKd10-CSd03-vs-CK12-CS13-CS12-CX32-CSd12-CX32-CKd12 : ⟪ (CK10 ∷ CS03 ∷ CK10⁻ ∷ CS03⁻ ∷ CK12 ∷ CS13 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CK12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ CS13 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CK12⁻ ∷ CK10 ∷ CS03 ∷ CK10⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
lem-groups-CK10-CS03-CKd10-CSd03-vs-CK12-CS13-CS12-CX32-CSd12-CX32-CKd12 = derive (CK10 ∷ CS03 ∷ CK10⁻ ∷ CS03⁻ ∷ CK12 ∷ CS13 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CK12⁻ ∷ []) (CK12 ∷ CS13 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CK12⁻ ∷ CK10 ∷ CS03 ∷ CK10⁻ ∷ CS03⁻ ∷ [])
  (re 3 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q14 ∷
   re 7 3 (CK13 ∷ []) ∷
   rw 6 q15 ∷
   rw 5 q16 ∷
   rw 4 q17 ∷
   re 4 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 3 q18 ∷
   re 4 5 (CS03⁻ ∷ []) ∷
   rw 2 q19 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q14 ∷
   re 5 3 (CK13 ∷ []) ∷
   rw 4 q15 ∷
   rw 3 q20 ∷
   rw 2 q17 ∷
   re 2 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 1 q18 ∷
   re 2 5 (CS03 ∷ []) ∷
   rw 0 q21 ∷
   rw 6 q14 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   rw 3 q22 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q18 ∷
   rw 1 q23 ∷
   rw 2 q24 ∷
   rw 3 q14 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q23 ∷
   rw 5 q14 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q14 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 6 q18 ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q14 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 8 q25 ∷
   rw 7 q26 ∷
   rw 6 q27 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   re 6 5 (CS03⁻ ∷ []) ∷
   rw 4 q28 ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q14 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 6 q25 ∷
   rw 5 q29 ∷
   rw 4 q27 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q18 ∷
   re 4 5 (CS03 ∷ []) ∷
   rw 2 q30 ∷
   rw 8 q31 ∷
   rw⁻ 7 q32 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q1 ∷
   rw 7 q33 ∷
   rw⁻ 6 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw 7 q34 ∷
   rw 6 q32 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   rw 8 q35 ∷
   rw 9 q1 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q36 ∷
   rw 6 q31 ∷
   rw⁻ 5 q32 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q1 ∷
   rw 5 q2 ∷
   rw⁻ 4 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 5 q37 ∷
   rw 4 q32 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q1 ∷
   rw 6 q6 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q8 ∷
   rw 3 q38 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q14 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw 10 q39 ∷
   rw 9 q40 ∷
   rw 8 q41 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   re 8 5 (CS03⁻ ∷ []) ∷
   rw 6 q42 ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q14 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw 8 q39 ∷
   rw 7 q43 ∷
   rw 6 q41 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw 4 q44 ∷
   rw 10 q31 ∷
   rw⁻ 9 q32 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q1 ∷
   rw 9 q33 ∷
   rw⁻ 8 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw 9 q34 ∷
   rw 8 q32 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q1 ∷
   rw 10 q35 ∷
   rw 11 q1 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q8 ∷
   rw 7 q36 ∷
   rw 8 q31 ∷
   rw⁻ 7 q32 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q1 ∷
   rw 7 q2 ∷
   rw⁻ 6 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 7 q37 ∷
   rw 6 q32 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   rw 8 q6 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q38 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q14 ∷
   re 13 3 (CK13⁻ ∷ []) ∷
   rw 12 q45 ∷
   rw 11 q46 ∷
   rw 10 q47 ∷
   re 10 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   re 10 5 (CS03⁻ ∷ []) ∷
   rw 8 q48 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q14 ∷
   re 11 3 (CK13⁻ ∷ []) ∷
   rw 10 q45 ∷
   rw 9 q49 ∷
   rw 8 q47 ∷
   re 8 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 6 q50 ∷ []) Eq.refl
