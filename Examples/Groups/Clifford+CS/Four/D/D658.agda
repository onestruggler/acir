{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D658 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D012 W using (lem-pass-CCZ123-vs-CS13 ; lem-pass-CCZ123-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D370 W using (lem-pass-CZ02-vs-CSd13 ; lem-pass-CZ12-vs-CS13 ; lem-pass-CZ12-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D372 W using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D373 W using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D374 W using (lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D375 W using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D376 W using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-CCZ023-vs-CSd13 ; lem-pass-CCZ123-vs-CCZ023)
open import Examples.Groups.Clifford+CS.Four.D.D623 W using (lem-pass-CCZ023-vs-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D633 W using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2)
open import Examples.Groups.Clifford+CS.Four.D.D635 W using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2)
open import Examples.Groups.Clifford+CS.Four.D.D642 W using (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-Z1-CZ12-CZ13-CCZ123)

private
  q1 : Eqn
  q1 = eqn (CCZ123 ∷ CS13 ∷ []) (CS13 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CS13)
  q2 : Eqn
  q2 = eqn (CZ12 ∷ CS13 ∷ []) (CS13 ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CS13)
  q3 : Eqn
  q3 = eqn [] (Toff102 ∷ Toff102 ∷ []) (wn 1377 W)
  q4 : Eqn
  q4 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q5 : Eqn
  q5 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q6 : Eqn
  q6 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q7 : Eqn
  q7 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q8 : Eqn
  q8 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q9 : Eqn
  q9 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q10 : Eqn
  q10 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q11 : Eqn
  q11 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = eqn (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ []) (wn 253 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q18 : Eqn
  q18 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q19 : Eqn
  q19 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q20 : Eqn
  q20 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q21 : Eqn
  q21 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q22 : Eqn
  q22 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q23 : Eqn
  q23 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q24 : Eqn
  q24 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q25 : Eqn
  q25 = eqn (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 46 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q29 : Eqn
  q29 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q30 : Eqn
  q30 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q31 : Eqn
  q31 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q32 : Eqn
  q32 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q33 : Eqn
  q33 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q34 : Eqn
  q34 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q35 : Eqn
  q35 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q36 : Eqn
  q36 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q37 : Eqn
  q37 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q38 : Eqn
  q38 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)
  q39 : Eqn
  q39 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q40 : Eqn
  q40 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q41 : Eqn
  q41 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q42 : Eqn
  q42 = eqn (Sw12 ∷ CX12 ∷ []) (CX21 ∷ Sw12 ∷ []) (wn 50 W)
  q43 : Eqn
  q43 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q44 : Eqn
  q44 = eqn (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 52 W)
  q45 : Eqn
  q45 = eqn (CZ12 ∷ Toff102 ∷ []) (Toff102 ∷ CZ02 ∷ CZ12 ∷ []) (wn 1806 W)
  q46 : Eqn
  q46 = eqn (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CCZ023)
  q47 : Eqn
  q47 = eqn (CCZ123 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd13)
  q48 : Eqn
  q48 = eqn (CCZ023 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CSd13)
  q49 : Eqn
  q49 = eqn (CZ12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CSd13)
  q50 : Eqn
  q50 = eqn (CZ02 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CZ02 ∷ []) (lem-pass-CZ02-vs-CSd13)
  q51 : Eqn
  q51 = eqn (CCZ023 ∷ Toff102 ∷ []) (Toff102 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-TOFF102)
  q52 : Eqn
  q52 = eqn (CZ02 ∷ Toff102 ∷ []) (Toff102 ∷ CZ02 ∷ []) (wn 1984 W)
  q53 : Eqn
  q53 = eqn (CZ02 ∷ CZ02 ∷ []) [] (wn 1808 W)
  q54 : Eqn
  q54 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q55 : Eqn
  q55 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)

-- pass [CZ12 CCZ123] [CS13 TOFF102 CSd13 TOFF102]: 468 steps
lem-pass-CZ12-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (CZ12 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CZ12 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CZ12-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 = derive (CZ12 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CZ12 ∷ CCZ123 ∷ [])
  (rw 1 q1 ∷
   rw 0 q2 ∷
   rw 2 q3 ∷
   rw 6 q4 ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 12 q5 ∷
   rw 11 q6 ∷
   rw 10 q7 ∷
   rw 9 q8 ∷
   rw 8 q9 ∷
   rw 7 q8 ∷
   rw 6 q10 ∷
   rw 5 q6 ∷
   rw 6 q11 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q12 ∷
   rw 9 q10 ∷
   rw⁻ 8 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 7 q13 ∷
   rw⁻ 6 q14 ∷
   rw 5 q13 ∷
   rw⁻ 4 q15 ∷
   rw 5 q4 ∷
   rw 6 q15 ∷
   rw 7 q16 ∷
   rw 8 q14 ∷
   rw 9 q16 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q17 ∷
   rw 12 q12 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 6 q18 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 5 3 (CCZ023 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 10 q5 ∷
   rw 9 q6 ∷
   rw 8 q7 ∷
   rw 7 q8 ∷
   rw 6 q9 ∷
   rw 5 q8 ∷
   rw 4 q10 ∷
   rw 3 q6 ∷
   rw 4 q11 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 7 q19 ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 13 q20 ∷
   rw 12 q21 ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q22 ∷
   rw 10 q19 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q23 ∷
   rw 8 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q24 ∷
   rw 6 q21 ∷
   rw 7 q25 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q15 ∷
   rw 6 q26 ∷
   rw 7 q14 ∷
   rw 8 q26 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q27 ∷
   rw 11 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q28 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q29 ∷
   rw 11 q30 ∷
   rw 9 q31 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 10 q22 ∷
   rw 7 q32 ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 q22 ∷
   rw 5 q33 ∷
   rw 6 q34 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q35 ∷
   rw⁻ 8 q36 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw⁻ 10 q36 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q35 ∷
   rw 7 q37 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   re 6 3 (CCZ013 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 11 q20 ∷
   rw 10 q21 ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q22 ∷
   rw 8 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q23 ∷
   rw 6 q19 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q24 ∷
   rw 4 q21 ∷
   rw 5 q25 ∷
   re 5 8 (Toff012 ∷ []) ∷
   rw 5 q38 ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q34 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q36 ∷
   rw 9 q34 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q36 ∷
   rw 11 q34 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q35 ∷
   rw 4 q39 ∷
   rw 7 q19 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q40 ∷
   rw 9 q19 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q29 ∷
   rw⁻ 10 q30 ∷
   rw 11 q31 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 4 q4 ∷
   rw 5 q15 ∷
   rw 6 q16 ∷
   rw 7 q14 ∷
   rw 8 q16 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q17 ∷
   rw 11 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q18 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q41 ∷
   rw 6 q42 ∷
   rw 7 q43 ∷
   rw 8 q42 ∷
   rw 9 q39 ∷
   rw 5 q44 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw 6 q22 ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q15 ∷
   rw 5 q26 ∷
   rw 6 q14 ∷
   rw 7 q26 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q27 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q28 ∷
   rw 3 q15 ∷
   rw 4 q16 ∷
   rw 5 q14 ∷
   rw 6 q16 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q17 ∷
   rw 9 q12 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q18 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q15 ∷
   rw 5 q26 ∷
   rw 6 q14 ∷
   rw 7 q26 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q27 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 4 q4 ∷
   rw 5 q15 ∷
   rw 6 q16 ∷
   rw 7 q14 ∷
   rw 8 q16 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q17 ∷
   rw 11 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q18 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   rw 5 q28 ∷
   rw 1 q45 ∷
   rw 4 q46 ∷
   rw 5 q47 ∷
   rw 4 q48 ∷
   rw 3 q49 ∷
   rw 2 q50 ∷
   rw 6 q3 ∷
   rw 10 q4 ∷
   re 9 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q7 ∷
   rw 13 q8 ∷
   rw 12 q9 ∷
   rw 11 q8 ∷
   rw 10 q10 ∷
   rw 9 q6 ∷
   rw 10 q11 ∷
   re 10 8 (Toff012 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q12 ∷
   rw 13 q10 ∷
   rw⁻ 12 q12 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 11 q13 ∷
   rw⁻ 10 q14 ∷
   rw 9 q13 ∷
   rw⁻ 8 q15 ∷
   rw 9 q4 ∷
   rw 10 q15 ∷
   rw 11 q16 ∷
   rw 12 q14 ∷
   rw 13 q16 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q12 ∷
   rw 15 q17 ∷
   rw 16 q12 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 10 q18 ∷
   re 10 5 (CCZ123 ∷ []) ∷
   re 9 3 (CCZ023 ∷ []) ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 14 q5 ∷
   rw 13 q6 ∷
   rw 12 q7 ∷
   rw 11 q8 ∷
   rw 10 q9 ∷
   rw 9 q8 ∷
   rw 8 q10 ∷
   rw 7 q6 ∷
   rw 8 q11 ∷
   re 8 8 (Toff012 ∷ []) ∷
   rw 11 q19 ∷
   re 10 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 17 q20 ∷
   rw 16 q21 ∷
   re 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q22 ∷
   rw 14 q19 ∷
   re 15 3 (CX02 ∷ []) ∷
   rw 13 q23 ∷
   rw 12 q19 ∷
   re 13 3 (CX02 ∷ []) ∷
   rw 11 q24 ∷
   rw 10 q21 ∷
   rw 11 q25 ∷
   re 11 8 (Toff012 ∷ []) ∷
   re 9 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 9 q15 ∷
   rw 10 q26 ∷
   rw 11 q14 ∷
   rw 12 q26 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q12 ∷
   rw 14 q27 ∷
   rw 15 q12 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q28 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q29 ∷
   rw 15 q30 ∷
   rw 13 q31 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 12 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 14 q22 ∷
   rw 11 q32 ∷
   re 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 12 q22 ∷
   rw 9 q33 ∷
   rw 10 q34 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q35 ∷
   rw⁻ 12 q36 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q35 ∷
   rw⁻ 14 q36 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q35 ∷
   rw 11 q37 ∷
   re 11 5 (CCZ012 ∷ []) ∷
   re 10 3 (CCZ013 ∷ []) ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 15 q20 ∷
   rw 14 q21 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q22 ∷
   rw 12 q19 ∷
   re 13 3 (CX02 ∷ []) ∷
   rw 11 q23 ∷
   rw 10 q19 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q24 ∷
   rw 8 q21 ∷
   rw 9 q25 ∷
   re 9 8 (Toff012 ∷ []) ∷
   rw 9 q38 ∷
   re 9 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 11 q34 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q36 ∷
   rw 13 q34 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q36 ∷
   rw 15 q34 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q35 ∷
   rw 8 q39 ∷
   rw 11 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 10 q40 ∷
   rw 13 q19 ∷
   re 11 3 (CX02 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q29 ∷
   rw⁻ 14 q30 ∷
   rw 15 q31 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw 8 q4 ∷
   rw 9 q15 ∷
   rw 10 q16 ∷
   rw 11 q14 ∷
   rw 12 q16 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q12 ∷
   rw 14 q17 ∷
   rw 15 q12 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 9 q18 ∷
   re 9 5 (CCZ123 ∷ []) ∷
   re 8 3 (CCZ023 ∷ []) ∷
   re 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 9 q41 ∷
   rw 10 q42 ∷
   rw 11 q43 ∷
   rw 12 q42 ∷
   rw 13 q39 ∷
   rw 9 q44 ∷
   re 9 5 (CCZ123 ∷ []) ∷
   rw 10 q22 ∷
   re 8 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 8 q15 ∷
   rw 9 q26 ∷
   rw 10 q14 ∷
   rw 11 q26 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   rw 13 q27 ∷
   rw 14 q12 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q28 ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 9 q14 ∷
   rw 10 q16 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   rw 12 q17 ∷
   rw 13 q12 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q18 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 8 q15 ∷
   rw 9 q26 ∷
   rw 10 q14 ∷
   rw 11 q26 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   rw 13 q27 ∷
   rw 14 q12 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 8 q4 ∷
   rw 9 q15 ∷
   rw 10 q16 ∷
   rw 11 q14 ∷
   rw 12 q16 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q12 ∷
   rw 14 q17 ∷
   rw 15 q12 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 9 q18 ∷
   re 9 5 (CCZ123 ∷ []) ∷
   re 8 3 (CCZ023 ∷ []) ∷
   rw 9 q28 ∷
   rw 5 q51 ∷
   rw 4 q45 ∷
   rw 3 q52 ∷
   rw 8 q46 ∷
   rw 4 q53 ∷
   rw 7 q4 ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q15 ∷
   rw 7 q26 ∷
   rw 8 q14 ∷
   rw 9 q26 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q27 ∷
   rw 12 q12 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q28 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q12 ∷
   rw 11 q7 ∷
   rw⁻ 10 q12 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q54 ∷
   rw⁻ 8 q14 ∷
   rw 7 q54 ∷
   rw⁻ 6 q15 ∷
   rw 7 q18 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q15 ∷
   rw 6 q26 ∷
   rw 7 q14 ∷
   rw 8 q26 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q27 ∷
   rw 11 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q28 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q12 ∷
   rw 10 q7 ∷
   rw⁻ 9 q12 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q54 ∷
   rw⁻ 7 q14 ∷
   rw 6 q54 ∷
   rw⁻ 5 q15 ∷
   rw 6 q18 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   rw 6 q55 ∷
   rw 5 q28 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn [] (X2 ∷ X3 ∷ X2 ∷ X3 ∷ []) (wn 1018 W)
  q57 : Eqn
  q57 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q58 : Eqn
  q58 = eqn (X2 ∷ CS13 ∷ []) (CS13 ∷ X2 ∷ []) (wn 257 W)
  q59 : Eqn
  q59 = eqn (X2 ∷ X2 ∷ []) [] (wn 389 W)
  q60 : Eqn
  q60 = eqn (Toff102 ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ []) (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q61 : Eqn
  q61 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)
  q62 : Eqn
  q62 = eqn (X2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X2 ∷ []) (wn 258 W)
  q63 : Eqn
  q63 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3)
  q64 : Eqn
  q64 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2)
  q65 : Eqn
  q65 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3)
  q66 : Eqn
  q66 = eqn (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 20 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 32 q56 ∷
   rw 37 q56 ∷
   rw 42 q56 ∷
   rw 29 q57 ∷
   rw 30 q58 ∷
   rw 31 q59 ∷
   rw⁻ 33 q60 ∷
   rw⁻ 34 q57 ∷
   rw 35 q61 ∷
   rw 35 q57 ∷
   rw 36 q62 ∷
   rw 37 q59 ∷
   rw⁻ 39 q60 ∷
   rw⁻ 40 q57 ∷
   rw 41 q61 ∷
   rw 0 q63 ∷
   rw 3 q64 ∷
   rw 6 q65 ∷
   rw 9 q64 ∷
   rw⁻ 0 q66 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = eqn (X3 ∷ CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (wn 1985 W)
  q68 : Eqn
  q68 = eqn (X2 ∷ CZ12 ∷ []) (Z1 ∷ CZ12 ∷ X2 ∷ []) (wn 1986 W)
  q69 : Eqn
  q69 = eqn (X2 ∷ CCZ123 ∷ []) (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (wn 1987 W)
  q70 : Eqn
  q70 = eqn (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-Z1-CZ12-CZ13-CCZ123)
  q71 : Eqn
  q71 = eqn (Z1 ∷ X3 ∷ []) (X3 ∷ Z1 ∷ []) (low-comm ((Z ↑)) ((X ↑)))
  q72 : Eqn
  q72 = eqn (CZ12 ∷ X3 ∷ []) (X3 ∷ CZ12 ∷ []) (low₃-comm ((CZ ↑)) (X))
  q73 : Eqn
  q73 = eqn (X3 ∷ CZ13 ∷ []) (Z1 ∷ CZ13 ∷ X3 ∷ []) (wn 1988 W)
  q74 : Eqn
  q74 = eqn (Z1 ∷ X2 ∷ []) (X2 ∷ Z1 ∷ []) (low-comm ((Z ↑)) (X))
  q75 : Eqn
  q75 = eqn (X2 ∷ CZ13 ∷ []) (CZ13 ∷ X2 ∷ []) (wn 1989 W)
  q76 : Eqn
  q76 = eqn (Z1 ∷ Z1 ∷ CZ12 ∷ Z1 ∷ CZ13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) (wn 1990 W)

-- pass [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3] [CCZ123]: 15 steps
lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CCZ123 : ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CCZ123 = derive (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  (rw 7 q67 ∷
   rw 6 q68 ∷
   rw 8 q69 ∷
   rw 2 q70 ∷
   rw⁻ 1 q71 ∷
   rw⁻ 2 q72 ∷
   rw 3 q73 ∷
   rw 5 q67 ∷
   rw⁻ 0 q74 ∷
   rw 1 q68 ∷
   rw⁻ 3 q74 ∷
   rw 4 q75 ∷
   rw 5 q68 ∷
   rw 7 q69 ∷
   rw 0 q76 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3)
  q78 : Eqn
  q78 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2)
  q79 : Eqn
  q79 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3)

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 20 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 34 q56 ∷
   rw 39 q56 ∷
   rw 44 q56 ∷
   rw 31 q57 ∷
   rw 32 q58 ∷
   rw 33 q59 ∷
   rw⁻ 35 q60 ∷
   rw⁻ 36 q57 ∷
   rw 37 q61 ∷
   rw 37 q57 ∷
   rw 38 q62 ∷
   rw 39 q59 ∷
   rw⁻ 41 q60 ∷
   rw⁻ 42 q57 ∷
   rw 43 q61 ∷
   rw 0 q77 ∷
   rw 3 q78 ∷
   rw 6 q79 ∷
   rw 9 q78 ∷
   rw⁻ 0 q66 ∷ []) Eq.refl
