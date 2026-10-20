{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D686 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D652 W using (lem-Bar⟨SSSKSS32-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶1⟩)

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q3 : Eqn
  q3 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q7 : Eqn
  q7 = eqn (X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ Toff102 ∷ X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ Toff102 ∷ X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (wn 2022 W)
  q8 : Eqn
  q8 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q9 : Eqn
  q9 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q10 : Eqn
  q10 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q11 : Eqn
  q11 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q12 : Eqn
  q12 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q13 : Eqn
  q13 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q14 : Eqn
  q14 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 196 W)
  q15 : Eqn
  q15 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q16 : Eqn
  q16 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q17 : Eqn
  q17 = eqn (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (lem-Bar⟨SSSKSS32-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶1⟩)
  q18 : Eqn
  q18 = eqn (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ Toff102 ∷ X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ Toff102 ∷ X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ []) (wn 2023 W)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01 X3]: 511 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  (rw 62 q1 ∷
   rw 61 q2 ∷
   rw 60 q3 ∷
   rw 59 q3 ∷
   rw 58 q4 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q4 ∷
   re 54 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 56 q5 ∷
   rw 53 q4 ∷
   rw 52 q4 ∷
   rw 51 q4 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   rw 47 q6 ∷
   rw 46 q3 ∷
   rw 45 q4 ∷
   rw 44 q4 ∷
   rw 43 q4 ∷
   rw 42 q6 ∷
   rw 41 q3 ∷
   rw 40 q6 ∷
   rw 39 q3 ∷
   re 38 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 40 q5 ∷
   re 37 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 39 q5 ∷
   re 36 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   re 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   rw 31 q2 ∷
   rw 32 q7 ∷
   rw 31 q8 ∷
   re 33 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 32 q9 ∷
   rw 35 q1 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw⁻ 34 q10 ∷
   rw 37 q1 ∷
   re 35 3 (CS13⁻ ∷ []) ∷
   rw⁻ 36 q10 ∷
   rw 39 q1 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw⁻ 38 q9 ∷
   rw⁻ 39 q11 ∷
   rw 32 q1 ∷
   rw⁻ 33 q9 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   rw⁻ 35 q10 ∷
   re 37 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   rw⁻ 37 q10 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   rw⁻ 39 q9 ∷
   rw⁻ 40 q11 ∷
   rw 33 q12 ∷
   re 33 8 (Toff012 ∷ []) ∷
   re 32 3 (Toff013 ∷ []) ∷
   rw 33 q8 ∷
   rw 34 q8 ∷
   re 36 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 35 q13 ∷
   rw 38 q1 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw⁻ 37 q10 ∷
   rw 40 q1 ∷
   re 38 3 (CS13⁻ ∷ []) ∷
   rw⁻ 39 q10 ∷
   rw 42 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw⁻ 41 q13 ∷
   rw⁻ 42 q11 ∷
   rw 35 q1 ∷
   rw⁻ 36 q13 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   rw⁻ 38 q10 ∷
   re 40 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 39 q5 ∷
   rw⁻ 40 q10 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   rw⁻ 42 q13 ∷
   rw⁻ 43 q11 ∷
   rw 36 q14 ∷
   re 36 8 (Toff102 ∷ []) ∷
   re 35 3 (Toff103 ∷ []) ∷
   rw 36 q8 ∷
   rw 37 q8 ∷
   re 39 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 38 q9 ∷
   rw 41 q1 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw⁻ 40 q10 ∷
   rw 43 q1 ∷
   re 41 3 (CS13⁻ ∷ []) ∷
   rw⁻ 42 q10 ∷
   rw 45 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw⁻ 44 q9 ∷
   rw⁻ 45 q11 ∷
   rw 38 q1 ∷
   rw⁻ 39 q9 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q5 ∷
   rw⁻ 41 q10 ∷
   re 43 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q5 ∷
   rw⁻ 43 q10 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   rw⁻ 45 q9 ∷
   rw⁻ 46 q11 ∷
   rw 39 q12 ∷
   re 39 8 (Toff012 ∷ []) ∷
   re 38 3 (Toff013 ∷ []) ∷
   rw 39 q8 ∷
   rw 40 q8 ∷
   rw 43 q1 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 44 q1 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 45 q1 ∷
   re 43 3 (CK30 ∷ []) ∷
   rw 46 q1 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 47 q1 ∷
   re 45 3 (CK30 ∷ []) ∷
   rw 48 q1 ∷
   re 46 3 (CK30 ∷ []) ∷
   rw 49 q1 ∷
   re 47 3 (CX31 ∷ []) ∷
   rw⁻ 48 q15 ∷
   rw⁻ 49 q16 ∷
   rw⁻ 50 q15 ∷
   rw⁻ 51 q16 ∷
   rw⁻ 52 q4 ∷
   rw⁻ 53 q4 ∷
   rw⁻ 54 q4 ∷
   rw⁻ 55 q15 ∷
   rw⁻ 56 q16 ∷
   rw⁻ 57 q4 ∷
   rw⁻ 58 q4 ∷
   rw⁻ 59 q4 ∷
   rw⁻ 60 q4 ∷
   rw⁻ 61 q4 ∷
   rw⁻ 62 q4 ∷
   rw 65 q1 ∷
   re 63 3 (CX31 ∷ []) ∷
   rw⁻ 64 q4 ∷
   rw⁻ 65 q4 ∷
   rw⁻ 66 q15 ∷
   rw⁻ 67 q4 ∷
   rw⁻ 68 q15 ∷
   rw⁻ 69 q15 ∷
   rw 70 q8 ∷
   rw 71 q8 ∷
   re 73 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 72 q9 ∷
   rw 75 q1 ∷
   re 73 3 (CS13 ∷ []) ∷
   rw⁻ 74 q10 ∷
   rw 77 q1 ∷
   re 75 3 (CS13⁻ ∷ []) ∷
   rw⁻ 76 q10 ∷
   rw 79 q1 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw⁻ 78 q9 ∷
   rw⁻ 79 q11 ∷
   rw 72 q1 ∷
   rw⁻ 73 q9 ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q5 ∷
   rw⁻ 75 q10 ∷
   re 77 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 76 q5 ∷
   rw⁻ 77 q10 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q5 ∷
   rw⁻ 79 q9 ∷
   rw⁻ 80 q11 ∷
   rw 73 q12 ∷
   re 73 8 (Toff012 ∷ []) ∷
   re 72 3 (Toff013 ∷ []) ∷
   rw 73 q8 ∷
   rw 74 q8 ∷
   re 76 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 75 q13 ∷
   rw 78 q1 ∷
   re 76 3 (CS13 ∷ []) ∷
   rw⁻ 77 q10 ∷
   rw 80 q1 ∷
   re 78 3 (CS13⁻ ∷ []) ∷
   rw⁻ 79 q10 ∷
   rw 82 q1 ∷
   re 80 3 (CS03 ∷ []) ∷
   rw⁻ 81 q13 ∷
   rw⁻ 82 q11 ∷
   rw 75 q1 ∷
   rw⁻ 76 q13 ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q5 ∷
   rw⁻ 78 q10 ∷
   re 80 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 79 q5 ∷
   rw⁻ 80 q10 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q5 ∷
   rw⁻ 82 q13 ∷
   rw⁻ 83 q11 ∷
   rw 76 q14 ∷
   re 76 8 (Toff102 ∷ []) ∷
   re 75 3 (Toff103 ∷ []) ∷
   rw 76 q8 ∷
   rw 77 q8 ∷
   re 79 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 78 q9 ∷
   rw 81 q1 ∷
   re 79 3 (CS13 ∷ []) ∷
   rw⁻ 80 q10 ∷
   rw 83 q1 ∷
   re 81 3 (CS13⁻ ∷ []) ∷
   rw⁻ 82 q10 ∷
   rw 85 q1 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw⁻ 84 q9 ∷
   rw⁻ 85 q11 ∷
   rw 78 q1 ∷
   rw⁻ 79 q9 ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q5 ∷
   rw⁻ 81 q10 ∷
   re 83 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 82 q5 ∷
   rw⁻ 83 q10 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q5 ∷
   rw⁻ 85 q9 ∷
   rw⁻ 86 q11 ∷
   rw 79 q12 ∷
   re 79 8 (Toff012 ∷ []) ∷
   re 78 3 (Toff013 ∷ []) ∷
   rw 79 q8 ∷
   rw 80 q5 ∷
   rw 0 q17 ∷
   rw 49 q1 ∷
   rw 48 q2 ∷
   re 47 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 48 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 47 q9 ∷
   rw 50 q1 ∷
   re 48 3 (CS13 ∷ []) ∷
   rw⁻ 49 q10 ∷
   rw 52 q1 ∷
   re 50 3 (CS13⁻ ∷ []) ∷
   rw⁻ 51 q10 ∷
   rw 54 q1 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw⁻ 53 q9 ∷
   rw⁻ 54 q11 ∷
   rw 55 q5 ∷
   rw 54 q11 ∷
   rw 53 q9 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q5 ∷
   rw 51 q10 ∷
   re 50 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 52 q5 ∷
   rw 49 q10 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q5 ∷
   rw 47 q9 ∷
   rw 48 q12 ∷
   re 48 8 (Toff012 ∷ []) ∷
   rw 46 q2 ∷
   rw 45 q2 ∷
   re 44 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 45 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 44 q13 ∷
   rw 47 q1 ∷
   re 45 3 (CS13 ∷ []) ∷
   rw⁻ 46 q10 ∷
   rw 49 q1 ∷
   re 47 3 (CS13⁻ ∷ []) ∷
   rw⁻ 48 q10 ∷
   rw 51 q1 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw⁻ 50 q13 ∷
   rw⁻ 51 q11 ∷
   rw 52 q5 ∷
   rw 51 q11 ∷
   rw 50 q13 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q5 ∷
   rw 48 q10 ∷
   re 47 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 49 q5 ∷
   rw 46 q10 ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q5 ∷
   rw 44 q13 ∷
   rw 45 q14 ∷
   re 45 8 (Toff102 ∷ []) ∷
   rw 43 q2 ∷
   rw 42 q2 ∷
   re 41 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 42 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 41 q9 ∷
   rw 44 q1 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw⁻ 43 q10 ∷
   rw 46 q1 ∷
   re 44 3 (CS13⁻ ∷ []) ∷
   rw⁻ 45 q10 ∷
   rw 48 q1 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw⁻ 47 q9 ∷
   rw⁻ 48 q11 ∷
   rw 49 q5 ∷
   rw 48 q11 ∷
   rw 47 q9 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q5 ∷
   rw 45 q10 ∷
   re 44 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 46 q5 ∷
   rw 43 q10 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   rw 41 q9 ∷
   rw 42 q12 ∷
   re 42 8 (Toff012 ∷ []) ∷
   rw 40 q2 ∷
   rw 39 q2 ∷
   rw 38 q15 ∷
   rw 37 q15 ∷
   rw 36 q4 ∷
   rw 35 q15 ∷
   rw 34 q4 ∷
   rw 33 q4 ∷
   re 32 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   rw 31 q4 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw 25 q16 ∷
   rw 24 q15 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q16 ∷
   rw 19 q15 ∷
   rw 18 q16 ∷
   rw 17 q15 ∷
   re 16 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw 9 q2 ∷
   rw 8 q2 ∷
   re 7 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 7 q9 ∷
   rw 10 q1 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q10 ∷
   rw 12 q1 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q10 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q9 ∷
   rw⁻ 14 q11 ∷
   rw 15 q5 ∷
   rw 14 q11 ∷
   rw 13 q9 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw 11 q10 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw 9 q10 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q9 ∷
   rw 8 q12 ∷
   re 8 8 (Toff012 ∷ []) ∷
   rw 6 q2 ∷
   rw 5 q2 ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 q13 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q10 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q10 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q13 ∷
   rw⁻ 11 q11 ∷
   rw 12 q5 ∷
   rw 11 q11 ∷
   rw 10 q13 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q10 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q10 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q13 ∷
   rw 5 q14 ∷
   re 5 8 (Toff102 ∷ []) ∷
   rw 3 q2 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q10 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q10 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q9 ∷
   rw⁻ 8 q11 ∷
   rw 9 q5 ∷
   rw 8 q11 ∷
   rw 7 q9 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q10 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q10 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q9 ∷
   rw 2 q12 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q18 ∷
   rw 0 q8 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CK31 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CK31 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CX30 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q3 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 18 q4 ∷
   rw⁻ 19 q4 ∷
   rw⁻ 20 q4 ∷
   rw⁻ 21 q4 ∷
   rw⁻ 22 q4 ∷
   rw 25 q1 ∷
   re 23 3 (CX30 ∷ []) ∷
   rw⁻ 24 q4 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 26 q3 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 28 q3 ∷
   rw⁻ 29 q3 ∷
   rw 30 q8 ∷
   rw 31 q5 ∷ []) Eq.refl
