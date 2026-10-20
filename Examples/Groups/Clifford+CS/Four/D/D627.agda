{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D627 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D598 W using (lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~32-⟶1⟩ ; lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSSKSS~32-⟶1⟩ ; lem-Bar⟨SSKSKK31-⟶0⟩-passes-III-units-2 ; lem-Bar⟨SSSKSS32-⟶0⟩-passes-III-units-1 ; lem-pass-TOFF203-vs-X3-TOFF213-X3)

private
  q1 : Eqn
  q1 = eqn (Toff213 ∷ []) (X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ []) (wn 1389 W)
  q2 : Eqn
  q2 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q3 : Eqn
  q3 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q12 : Eqn
  q12 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q13 : Eqn
  q13 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q14 : Eqn
  q14 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q15 : Eqn
  q15 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wn 334 W)
  q16 : Eqn
  q16 = eqn (X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) (Toff213 ∷ X3 ∷ []) (wn 1888 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q20 : Eqn
  q20 = eqn (Toff203 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) (X3 ∷ Toff213 ∷ X3 ∷ Toff203 ∷ []) lem-pass-TOFF203-vs-X3-TOFF213-X3
  q21 : Eqn
  q21 = eqn (X3 ∷ Toff213 ∷ []) (X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ []) (wn 1889 W)
  q22 : Eqn
  q22 = eqn (X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ []) (Toff213 ∷ []) (wn 1392 W)

-- pass [TOFF213] [X3 TOFF203 X3]: 133 steps
lem-pass-TOFF213-vs-X3-TOFF203-X3 : ⟪ (Toff213 ∷ X3 ∷ Toff203 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff203 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ
lem-pass-TOFF213-vs-X3-TOFF203-X3 = derive (Toff213 ∷ X3 ∷ Toff203 ∷ X3 ∷ []) (X3 ∷ Toff203 ∷ X3 ∷ Toff213 ∷ [])
  (rw 0 q1 ∷
   rw 8 q2 ∷
   rw⁻ 7 q3 ∷
   re 6 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 7 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   rw 12 q9 ∷
   rw 13 q8 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q4 ∷
   rw 13 q10 ∷
   rw 14 q11 ∷
   rw 13 q12 ∷
   rw⁻ 12 q4 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q8 ∷
   rw 12 q13 ∷
   rw⁻ 11 q8 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 10 q14 ∷
   rw⁻ 9 q7 ∷
   rw 8 q14 ∷
   rw⁻ 7 q5 ∷
   rw⁻ 6 q4 ∷
   rw 7 q15 ∷
   re 7 8 (Toff213 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw⁻ 4 q3 ∷
   rw 5 q16 ∷
   re 5 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q7 ∷
   rw 8 q6 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 10 q9 ∷
   rw 11 q8 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q4 ∷
   rw 11 q10 ∷
   rw 4 q2 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q17 ∷
   rw 8 q7 ∷
   rw 9 q17 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw 11 q18 ∷
   rw 12 q8 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 11 q4 ∷
   rw 12 q19 ∷
   rw 5 q15 ∷
   re 5 8 (Toff213 ∷ []) ∷
   re 4 3 (Toff203 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q11 ∷
   rw⁻ 1 q20 ∷
   rw 2 q2 ∷
   re 1 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 1 q4 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q7 ∷
   rw 5 q6 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 7 q9 ∷
   rw 8 q8 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q4 ∷
   rw 8 q10 ∷
   rw 9 q11 ∷
   rw 8 q12 ∷
   rw⁻ 7 q4 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q8 ∷
   rw 7 q13 ∷
   rw⁻ 6 q8 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 5 q14 ∷
   rw⁻ 4 q7 ∷
   rw 3 q14 ∷
   rw⁻ 2 q5 ∷
   rw⁻ 1 q4 ∷
   rw 2 q15 ∷
   re 2 8 (Toff213 ∷ []) ∷
   rw⁻ 0 q3 ∷
   rw 1 q21 ∷
   rw 0 q3 ∷
   re 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 1 q4 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q7 ∷
   rw 5 q6 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 7 q9 ∷
   rw 8 q8 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q4 ∷
   rw 8 q10 ∷
   rw 1 q2 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q17 ∷
   rw 5 q7 ∷
   rw 6 q17 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   rw 8 q18 ∷
   rw 9 q8 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q4 ∷
   rw 9 q19 ∷
   rw 2 q15 ∷
   re 2 8 (Toff213 ∷ []) ∷
   re 1 3 (Toff203 ∷ []) ∷
   rw 2 q3 ∷
   rw 3 q3 ∷
   rw 4 q11 ∷
   rw 3 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q24 : Eqn
  q24 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q25 : Eqn
  q25 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q26 : Eqn
  q26 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q27 : Eqn
  q27 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q28 : Eqn
  q28 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q29 : Eqn
  q29 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 196 W)
  q30 : Eqn
  q30 = eqn (X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1884 W)
  q31 : Eqn
  q31 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q32 : Eqn
  q32 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q33 : Eqn
  q33 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q34 : Eqn
  q34 = eqn (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (lem-Bar⟨SSSKSS32-⟶0⟩-passes-III-units-1)
  q35 : Eqn
  q35 = eqn (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ []) (wn 1885 W)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 TOFF103 X3]: 155 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF103-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF103-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  (rw 34 q23 ∷
   rw 33 q24 ∷
   re 32 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 33 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 32 q25 ∷
   rw 35 q23 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw⁻ 34 q26 ∷
   rw 37 q23 ∷
   re 35 3 (CS13⁻ ∷ []) ∷
   rw⁻ 36 q26 ∷
   rw 39 q23 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw⁻ 38 q25 ∷
   rw⁻ 39 q27 ∷
   rw 40 q28 ∷
   rw 39 q27 ∷
   rw 38 q25 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q28 ∷
   rw 36 q26 ∷
   re 35 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 37 q28 ∷
   rw 34 q26 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q28 ∷
   rw 32 q25 ∷
   rw 33 q29 ∷
   re 33 8 (Toff102 ∷ []) ∷
   rw 31 q24 ∷
   rw 32 q30 ∷
   rw 31 q31 ∷
   rw 34 q23 ∷
   re 32 3 (CK31 ∷ []) ∷
   rw 33 q31 ∷
   rw 34 q31 ∷
   rw 37 q23 ∷
   re 35 3 (CK30 ∷ []) ∷
   rw 36 q31 ∷
   rw 37 q31 ∷
   re 39 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 38 q32 ∷
   rw 41 q23 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw⁻ 40 q26 ∷
   rw 43 q23 ∷
   re 41 3 (CS13⁻ ∷ []) ∷
   rw⁻ 42 q26 ∷
   rw 45 q23 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw⁻ 44 q32 ∷
   rw⁻ 45 q27 ∷
   rw 38 q23 ∷
   rw⁻ 39 q32 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q28 ∷
   rw⁻ 41 q26 ∷
   re 43 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q28 ∷
   rw⁻ 43 q26 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q28 ∷
   rw⁻ 45 q32 ∷
   rw⁻ 46 q27 ∷
   rw 39 q33 ∷
   re 39 8 (Toff012 ∷ []) ∷
   re 38 3 (Toff013 ∷ []) ∷
   rw 39 q31 ∷
   rw 40 q31 ∷
   rw 43 q23 ∷
   re 41 3 (CK30⁻ ∷ []) ∷
   rw 42 q31 ∷
   rw 43 q31 ∷
   rw 46 q23 ∷
   re 44 3 (CK31⁻ ∷ []) ∷
   rw 45 q31 ∷
   rw 46 q28 ∷
   rw 0 q34 ∷
   rw 15 q23 ∷
   rw 14 q24 ∷
   re 13 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q28 ∷
   rw 12 q24 ∷
   rw 11 q24 ∷
   re 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q28 ∷
   rw 9 q24 ∷
   rw 8 q24 ∷
   re 7 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 7 q32 ∷
   rw 10 q23 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q26 ∷
   rw 12 q23 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q26 ∷
   rw 14 q23 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q32 ∷
   rw⁻ 14 q27 ∷
   rw 15 q28 ∷
   rw 14 q27 ∷
   rw 13 q32 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q28 ∷
   rw 11 q26 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q28 ∷
   rw 9 q26 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q28 ∷
   rw 7 q32 ∷
   rw 8 q33 ∷
   re 8 8 (Toff012 ∷ []) ∷
   rw 6 q24 ∷
   rw 5 q24 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q28 ∷
   rw 3 q24 ∷
   rw 2 q24 ∷
   re 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q24 ∷
   rw 1 q35 ∷
   rw 0 q31 ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q25 ∷
   rw 4 q23 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q26 ∷
   rw 6 q23 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q23 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q25 ∷
   rw⁻ 8 q27 ∷
   rw 1 q23 ∷
   rw⁻ 2 q25 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q28 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q28 ∷
   rw⁻ 8 q25 ∷
   rw⁻ 9 q27 ∷
   rw 2 q29 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q31 ∷
   rw 3 q28 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (X3 ∷ Toff213 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (wn 1886 W)
  q37 : Eqn
  q37 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q38 : Eqn
  q38 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q39 : Eqn
  q39 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q41 : Eqn
  q41 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q42 : Eqn
  q42 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q43 : Eqn
  q43 = eqn (Sw01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀)))
  q44 : Eqn
  q44 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-Bar⟨SSKSKK31-⟶0⟩-passes-III-units-2)
  q45 : Eqn
  q45 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q46 : Eqn
  q46 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q47 : Eqn
  q47 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q48 : Eqn
  q48 = eqn (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ Toff213 ∷ X3 ∷ []) (wn 1887 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 TOFF203 X3]: 171 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff203 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff203 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff203 ∷ X3 ∷ []) (X3 ∷ Toff203 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 32 q2 ∷
   rw⁻ 31 q3 ∷
   re 30 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 31 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 30 q4 ∷
   rw 31 q5 ∷
   rw 32 q6 ∷
   rw 33 q7 ∷
   rw 34 q6 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q8 ∷
   rw 36 q9 ∷
   rw 37 q8 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q4 ∷
   rw 37 q10 ∷
   rw 38 q11 ∷
   rw 37 q12 ∷
   rw⁻ 36 q4 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q8 ∷
   rw 36 q13 ∷
   rw⁻ 35 q8 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 34 q14 ∷
   rw⁻ 33 q7 ∷
   rw 32 q14 ∷
   rw⁻ 31 q5 ∷
   rw⁻ 30 q4 ∷
   rw 31 q15 ∷
   re 31 8 (Toff213 ∷ []) ∷
   rw⁻ 29 q3 ∷
   rw 30 q36 ∷
   rw 29 q3 ∷
   rw 30 q37 ∷
   rw 31 q3 ∷
   rw 32 q3 ∷
   re 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 33 q8 ∷
   rw 34 q38 ∷
   rw 35 q8 ∷
   re 33 3 (CK30 ∷ []) ∷
   rw 34 q3 ∷
   rw 35 q3 ∷
   re 37 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 36 q39 ∷
   rw 37 q5 ∷
   rw 38 q6 ∷
   rw 39 q7 ∷
   rw 40 q6 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q8 ∷
   rw 42 q9 ∷
   rw 43 q8 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q39 ∷
   rw 43 q10 ∷
   rw 36 q2 ∷
   rw 37 q40 ∷
   rw 38 q5 ∷
   rw 39 q17 ∷
   rw 40 q7 ∷
   rw 41 q17 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q8 ∷
   rw 43 q18 ∷
   rw 44 q8 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 43 q40 ∷
   rw 44 q19 ∷
   rw 37 q41 ∷
   re 37 8 (Toff123 ∷ []) ∷
   re 36 3 (Toff023 ∷ []) ∷
   rw 37 q3 ∷
   rw 38 q3 ∷
   re 40 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 39 q8 ∷
   rw 40 q42 ∷
   rw 41 q8 ∷
   re 39 3 (CK30⁻ ∷ []) ∷
   rw 40 q3 ∷
   rw 41 q3 ∷
   rw 42 q43 ∷
   rw 43 q3 ∷
   rw 44 q11 ∷
   rw 0 q44 ∷
   rw 15 q2 ∷
   rw⁻ 14 q3 ∷
   rw⁻ 13 q43 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 11 q3 ∷
   re 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q8 ∷
   rw 11 q45 ∷
   rw⁻ 10 q8 ∷
   re 11 3 (CK31⁻ ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw⁻ 8 q3 ∷
   re 7 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 8 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 7 q39 ∷
   rw 8 q5 ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q8 ∷
   rw 13 q9 ∷
   rw 14 q8 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q39 ∷
   rw 14 q10 ∷
   rw 15 q11 ∷
   rw 14 q12 ∷
   rw 13 q46 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q8 ∷
   rw 13 q13 ∷
   rw⁻ 12 q8 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 11 q14 ∷
   rw⁻ 10 q7 ∷
   rw 9 q14 ∷
   rw⁻ 8 q5 ∷
   rw 7 q46 ∷
   rw 8 q41 ∷
   re 8 8 (Toff123 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw⁻ 5 q3 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q8 ∷
   rw 5 q47 ∷
   rw⁻ 4 q8 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw⁻ 2 q3 ∷
   rw⁻ 1 q37 ∷
   rw⁻ 0 q3 ∷
   rw 1 q48 ∷
   rw 0 q3 ∷
   re 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 1 q4 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q7 ∷
   rw 5 q6 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 7 q9 ∷
   rw 8 q8 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q4 ∷
   rw 8 q10 ∷
   rw 1 q2 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q17 ∷
   rw 5 q7 ∷
   rw 6 q17 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   rw 8 q18 ∷
   rw 9 q8 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q4 ∷
   rw 9 q19 ∷
   rw 2 q15 ∷
   re 2 8 (Toff213 ∷ []) ∷
   re 1 3 (Toff203 ∷ []) ∷
   rw 2 q3 ∷
   rw 3 q11 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (wn 1890 W)
  q50 : Eqn
  q50 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSSKSS~32-⟶1⟩)
  q51 : Eqn
  q51 = eqn (X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (wn 1891 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS13 CS13 CS13 CK31 CS13 CS13 CX32 CS12 CS12 CS12 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CS12 CK21 CS12 CS12 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 29 q49 ∷
   rw 0 q50 ∷
   rw 0 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (wn 1892 W)
  q53 : Eqn
  q53 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~32-⟶1⟩)
  q54 : Eqn
  q54 = eqn (X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) (wn 1893 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS13 CS13 CK31 CS13 CK31 CK31 CX32 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CK21 CS12 CK21 CK21 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 29 q52 ∷
   rw 0 q53 ∷
   rw 0 q54 ∷ []) Eq.refl
