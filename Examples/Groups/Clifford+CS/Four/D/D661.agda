{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D661 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D370 W using (lem-pass-CZ12-vs-CS13 ; lem-pass-CZ12-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D372 W using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D373 W using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D375 W using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D376 W using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D387 W using (lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-CZ02-vs-CS13)
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-CCZ123-vs-CCZ023)
open import Examples.Groups.Clifford+CS.Four.D.D515 W using (lem-pass-CCZ023-vs-CS13)
open import Examples.Groups.Clifford+CS.Four.D.D623 W using (lem-pass-CCZ023-vs-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D633 W using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2)
open import Examples.Groups.Clifford+CS.Four.D.D635 W using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2)
open import Examples.Groups.Clifford+CS.Four.D.D642 W using (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Z1-CZ12-CZ13-CCZ123)

private
  q1 : Eqn
  q1 = eqn [] (Toff102 ∷ Toff102 ∷ []) (wn 1377 W)
  q2 : Eqn
  q2 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q3 : Eqn
  q3 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q4 : Eqn
  q4 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q5 : Eqn
  q5 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q6 : Eqn
  q6 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q7 : Eqn
  q7 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q8 : Eqn
  q8 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q9 : Eqn
  q9 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = eqn (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ []) (wn 253 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q16 : Eqn
  q16 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q17 : Eqn
  q17 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q18 : Eqn
  q18 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q19 : Eqn
  q19 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q20 : Eqn
  q20 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q21 : Eqn
  q21 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q22 : Eqn
  q22 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q23 : Eqn
  q23 = eqn (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 46 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q27 : Eqn
  q27 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q28 : Eqn
  q28 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q29 : Eqn
  q29 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q30 : Eqn
  q30 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q31 : Eqn
  q31 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q32 : Eqn
  q32 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q33 : Eqn
  q33 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q34 : Eqn
  q34 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q35 : Eqn
  q35 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q36 : Eqn
  q36 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)
  q37 : Eqn
  q37 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q38 : Eqn
  q38 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q39 : Eqn
  q39 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q40 : Eqn
  q40 = eqn (Sw12 ∷ CX12 ∷ []) (CX21 ∷ Sw12 ∷ []) (wn 50 W)
  q41 : Eqn
  q41 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q42 : Eqn
  q42 = eqn (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 52 W)
  q43 : Eqn
  q43 = eqn (CZ12 ∷ Toff102 ∷ []) (Toff102 ∷ CZ02 ∷ CZ12 ∷ []) (wn 1806 W)
  q44 : Eqn
  q44 = eqn (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CCZ023)
  q45 : Eqn
  q45 = eqn (CCZ123 ∷ CS13 ∷ []) (CS13 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CS13)
  q46 : Eqn
  q46 = eqn (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CS13)
  q47 : Eqn
  q47 = eqn (CZ12 ∷ CS13 ∷ []) (CS13 ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CS13)
  q48 : Eqn
  q48 = eqn (CZ02 ∷ CS13 ∷ []) (CS13 ∷ CZ02 ∷ []) (lem-pass-CZ02-vs-CS13)
  q49 : Eqn
  q49 = eqn (CCZ023 ∷ Toff102 ∷ []) (Toff102 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-TOFF102)
  q50 : Eqn
  q50 = eqn (CZ02 ∷ Toff102 ∷ []) (Toff102 ∷ CZ02 ∷ []) (wn 1984 W)
  q51 : Eqn
  q51 = eqn (CZ02 ∷ CZ02 ∷ []) [] (wn 1808 W)
  q52 : Eqn
  q52 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q53 : Eqn
  q53 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)
  q54 : Eqn
  q54 = eqn (CCZ123 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd13)
  q55 : Eqn
  q55 = eqn (CZ12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CSd13)

-- pass [CZ12 CCZ123] [TOFF102 CS13 TOFF102 CSd13]: 468 steps
lem-pass-CZ12-CCZ123-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (CZ12 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CZ12 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CZ12-CCZ123-vs-TOFF102-CS13-TOFF102-CSd13 = derive (CZ12 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CZ12 ∷ CCZ123 ∷ [])
  (rw 1 q1 ∷
   rw 5 q2 ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 11 q3 ∷
   rw 10 q4 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 6 q6 ∷
   rw 5 q8 ∷
   rw 4 q4 ∷
   rw 5 q9 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q10 ∷
   rw 8 q8 ∷
   rw⁻ 7 q10 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 6 q11 ∷
   rw⁻ 5 q12 ∷
   rw 4 q11 ∷
   rw⁻ 3 q13 ∷
   rw 4 q2 ∷
   rw 5 q13 ∷
   rw 6 q14 ∷
   rw 7 q12 ∷
   rw 8 q14 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q10 ∷
   rw 10 q15 ∷
   rw 11 q10 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q16 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 9 q3 ∷
   rw 8 q4 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q6 ∷
   rw 3 q8 ∷
   rw 2 q4 ∷
   rw 3 q9 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 6 q17 ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 12 q18 ∷
   rw 11 q19 ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q20 ∷
   rw 9 q17 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q21 ∷
   rw 7 q17 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q22 ∷
   rw 5 q19 ∷
   rw 6 q23 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q13 ∷
   rw 5 q24 ∷
   rw 6 q12 ∷
   rw 7 q24 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q25 ∷
   rw 10 q10 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q26 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q27 ∷
   rw 10 q28 ∷
   rw 8 q29 ∷
   re 9 5 (CS03 ∷ []) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 9 q20 ∷
   rw 6 q30 ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 q20 ∷
   rw 4 q31 ∷
   rw 5 q32 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q33 ∷
   rw⁻ 7 q34 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q33 ∷
   rw⁻ 9 q34 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q33 ∷
   rw 6 q35 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 5 3 (CCZ013 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 10 q18 ∷
   rw 9 q19 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q20 ∷
   rw 7 q17 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q21 ∷
   rw 5 q17 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q22 ∷
   rw 3 q19 ∷
   rw 4 q23 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 4 q36 ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q32 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q34 ∷
   rw 8 q32 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q34 ∷
   rw 10 q32 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q33 ∷
   rw 3 q37 ∷
   rw 6 q17 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q38 ∷
   rw 8 q17 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q27 ∷
   rw⁻ 9 q28 ∷
   rw 10 q29 ∷
   re 7 5 (CS03 ∷ []) ∷
   rw 3 q2 ∷
   rw 4 q13 ∷
   rw 5 q14 ∷
   rw 6 q12 ∷
   rw 7 q14 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q15 ∷
   rw 10 q10 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q16 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q39 ∷
   rw 5 q40 ∷
   rw 6 q41 ∷
   rw 7 q40 ∷
   rw 8 q37 ∷
   rw 4 q42 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   rw 5 q20 ∷
   re 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q13 ∷
   rw 4 q24 ∷
   rw 5 q12 ∷
   rw 6 q24 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q10 ∷
   rw 8 q25 ∷
   rw 9 q10 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q26 ∷
   rw 2 q13 ∷
   rw 3 q14 ∷
   rw 4 q12 ∷
   rw 5 q14 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q10 ∷
   rw 7 q15 ∷
   rw 8 q10 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q16 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q13 ∷
   rw 4 q24 ∷
   rw 5 q12 ∷
   rw 6 q24 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q10 ∷
   rw 8 q25 ∷
   rw 9 q10 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q2 ∷
   rw 4 q13 ∷
   rw 5 q14 ∷
   rw 6 q12 ∷
   rw 7 q14 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q15 ∷
   rw 10 q10 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q16 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   rw 4 q26 ∷
   rw 0 q43 ∷
   rw 3 q44 ∷
   rw 4 q45 ∷
   rw 3 q46 ∷
   rw 2 q47 ∷
   rw 1 q48 ∷
   rw 5 q1 ∷
   rw 9 q2 ∷
   re 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 15 q3 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   rw 11 q7 ∷
   rw 10 q6 ∷
   rw 9 q8 ∷
   rw 8 q4 ∷
   rw 9 q9 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q10 ∷
   rw 12 q8 ∷
   rw⁻ 11 q10 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 10 q11 ∷
   rw⁻ 9 q12 ∷
   rw 8 q11 ∷
   rw⁻ 7 q13 ∷
   rw 8 q2 ∷
   rw 9 q13 ∷
   rw 10 q14 ∷
   rw 11 q12 ∷
   rw 12 q14 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q10 ∷
   rw 14 q15 ∷
   rw 15 q10 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 9 q16 ∷
   re 9 5 (CCZ123 ∷ []) ∷
   re 8 3 (CCZ023 ∷ []) ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 13 q3 ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q7 ∷
   rw 8 q6 ∷
   rw 7 q8 ∷
   rw 6 q4 ∷
   rw 7 q9 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 10 q17 ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 16 q18 ∷
   rw 15 q19 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 16 q20 ∷
   rw 13 q17 ∷
   re 14 3 (CX02 ∷ []) ∷
   rw 12 q21 ∷
   rw 11 q17 ∷
   re 12 3 (CX02 ∷ []) ∷
   rw 10 q22 ∷
   rw 9 q19 ∷
   rw 10 q23 ∷
   re 10 8 (Toff012 ∷ []) ∷
   re 8 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 8 q13 ∷
   rw 9 q24 ∷
   rw 10 q12 ∷
   rw 11 q24 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q10 ∷
   rw 13 q25 ∷
   rw 14 q10 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q26 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q27 ∷
   rw 14 q28 ∷
   rw 12 q29 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 11 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 13 q20 ∷
   rw 10 q30 ∷
   re 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 11 q20 ∷
   rw 8 q31 ∷
   rw 9 q32 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q33 ∷
   rw⁻ 11 q34 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q33 ∷
   rw⁻ 13 q34 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q33 ∷
   rw 10 q35 ∷
   re 10 5 (CCZ012 ∷ []) ∷
   re 9 3 (CCZ013 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q20 ∷
   rw 11 q17 ∷
   re 12 3 (CX02 ∷ []) ∷
   rw 10 q21 ∷
   rw 9 q17 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q22 ∷
   rw 7 q19 ∷
   rw 8 q23 ∷
   re 8 8 (Toff012 ∷ []) ∷
   rw 8 q36 ∷
   re 8 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 10 q32 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q34 ∷
   rw 12 q32 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q34 ∷
   rw 14 q32 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q33 ∷
   rw 7 q37 ∷
   rw 10 q17 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 9 q38 ∷
   rw 12 q17 ∷
   re 10 3 (CX02 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q27 ∷
   rw⁻ 13 q28 ∷
   rw 14 q29 ∷
   re 11 5 (CS03 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q13 ∷
   rw 9 q14 ∷
   rw 10 q12 ∷
   rw 11 q14 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q10 ∷
   rw 13 q15 ∷
   rw 14 q10 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 8 q16 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   re 7 3 (CCZ023 ∷ []) ∷
   re 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 8 q39 ∷
   rw 9 q40 ∷
   rw 10 q41 ∷
   rw 11 q40 ∷
   rw 12 q37 ∷
   rw 8 q42 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   rw 9 q20 ∷
   re 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q13 ∷
   rw 8 q24 ∷
   rw 9 q12 ∷
   rw 10 q24 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q10 ∷
   rw 12 q25 ∷
   rw 13 q10 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q26 ∷
   rw 6 q13 ∷
   rw 7 q14 ∷
   rw 8 q12 ∷
   rw 9 q14 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q10 ∷
   rw 11 q15 ∷
   rw 12 q10 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 6 q16 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q13 ∷
   rw 8 q24 ∷
   rw 9 q12 ∷
   rw 10 q24 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q10 ∷
   rw 12 q25 ∷
   rw 13 q10 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q13 ∷
   rw 9 q14 ∷
   rw 10 q12 ∷
   rw 11 q14 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q10 ∷
   rw 13 q15 ∷
   rw 14 q10 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 8 q16 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   re 7 3 (CCZ023 ∷ []) ∷
   rw 8 q26 ∷
   rw 4 q49 ∷
   rw 3 q43 ∷
   rw 2 q50 ∷
   rw 7 q44 ∷
   rw 3 q51 ∷
   rw 6 q2 ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q13 ∷
   rw 6 q24 ∷
   rw 7 q12 ∷
   rw 8 q24 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q10 ∷
   rw 10 q25 ∷
   rw 11 q10 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q26 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q10 ∷
   rw 10 q5 ∷
   rw⁻ 9 q10 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q52 ∷
   rw⁻ 7 q12 ∷
   rw 6 q52 ∷
   rw⁻ 5 q13 ∷
   rw 6 q16 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q13 ∷
   rw 5 q24 ∷
   rw 6 q12 ∷
   rw 7 q24 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q25 ∷
   rw 10 q10 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q26 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q10 ∷
   rw 9 q5 ∷
   rw⁻ 8 q10 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q52 ∷
   rw⁻ 6 q12 ∷
   rw 5 q52 ∷
   rw⁻ 4 q13 ∷
   rw 5 q16 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw 5 q53 ∷
   rw 4 q26 ∷
   rw 4 q54 ∷
   rw 3 q55 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn [] (X2 ∷ X3 ∷ X2 ∷ X3 ∷ []) (wn 1018 W)
  q57 : Eqn
  q57 = eqn (Toff102 ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ []) (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q58 : Eqn
  q58 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q59 : Eqn
  q59 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)
  q60 : Eqn
  q60 = eqn (X2 ∷ CS13 ∷ []) (CS13 ∷ X2 ∷ []) (wn 257 W)
  q61 : Eqn
  q61 = eqn (X2 ∷ X2 ∷ []) [] (wn 389 W)
  q62 : Eqn
  q62 = eqn (X2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X2 ∷ []) (wn 258 W)
  q63 : Eqn
  q63 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2)
  q64 : Eqn
  q64 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3)
  q65 : Eqn
  q65 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3)
  q66 : Eqn
  q66 = eqn (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 20 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 32 q56 ∷
   rw 37 q56 ∷
   rw 42 q56 ∷
   rw⁻ 30 q57 ∷
   rw⁻ 31 q58 ∷
   rw 32 q59 ∷
   rw 32 q58 ∷
   rw 33 q60 ∷
   rw 34 q61 ∷
   rw⁻ 36 q57 ∷
   rw⁻ 37 q58 ∷
   rw 38 q59 ∷
   rw 38 q58 ∷
   rw 39 q62 ∷
   rw 40 q61 ∷
   rw 0 q63 ∷
   rw 3 q64 ∷
   rw 6 q63 ∷
   rw 9 q65 ∷
   rw⁻ 0 q66 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = eqn (X3 ∷ CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (wn 1985 W)
  q68 : Eqn
  q68 = eqn (X2 ∷ CZ12 ∷ []) (Z1 ∷ CZ12 ∷ X2 ∷ []) (wn 1986 W)
  q69 : Eqn
  q69 = eqn (X2 ∷ CCZ123 ∷ []) (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (wn 1987 W)
  q70 : Eqn
  q70 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Z1-CZ12-CZ13-CCZ123)
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

-- pass [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3] [CCZ123]: 15 steps
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CCZ123 : ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CCZ123 = derive (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ [])
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
  q77 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2)
  q78 : Eqn
  q78 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3)
  q79 : Eqn
  q79 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3)

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 20 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 34 q56 ∷
   rw 39 q56 ∷
   rw 44 q56 ∷
   rw⁻ 32 q57 ∷
   rw⁻ 33 q58 ∷
   rw 34 q59 ∷
   rw 34 q58 ∷
   rw 35 q60 ∷
   rw 36 q61 ∷
   rw⁻ 38 q57 ∷
   rw⁻ 39 q58 ∷
   rw 40 q59 ∷
   rw 40 q58 ∷
   rw 41 q62 ∷
   rw 42 q61 ∷
   rw 0 q77 ∷
   rw 3 q78 ∷
   rw 6 q77 ∷
   rw 9 q79 ∷
   rw⁻ 0 q66 ∷ []) Eq.refl
