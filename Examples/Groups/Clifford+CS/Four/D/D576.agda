{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD576 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D576 (W : Ws) (Sᴰ : SD576) where

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
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X0-X3-TOFF103-X0-X3 : St 1007
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X0-X3-TOFF103-X0-X3 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q5 : Eqn
  q5 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q6 : Eqn
  q6 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 196 W
  q9 : Eqn
  q9 = wE 1640 W
  q10 : Eqn
  q10 = wE 175 W
  q11 : Eqn
  q11 = sE 1007 lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X0-X3-TOFF103-X0-X3
  q12 : Eqn
  q12 = wE 1641 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X0 X3 TOFF103 X0 X3]: 135 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF103-X0-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF103-X0-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 36 q1 ∷
   rw 35 q2 ∷
   rw 34 q3 ∷
   re 33 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 34 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 33 q4 ∷
   rw 36 q1 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw⁻ 35 q5 ∷
   rw 38 q1 ∷
   re 36 3 (CS13⁻ ∷ []) ∷
   rw⁻ 37 q5 ∷
   rw 40 q1 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw⁻ 39 q4 ∷
   rw⁻ 40 q6 ∷
   rw 41 q7 ∷
   rw 40 q6 ∷
   rw 39 q4 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q7 ∷
   rw 37 q5 ∷
   re 36 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 38 q7 ∷
   rw 35 q5 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q7 ∷
   rw 33 q4 ∷
   rw 34 q8 ∷
   re 34 8 (Toff102 ∷ []) ∷
   rw 32 q2 ∷
   rw 31 q3 ∷
   rw 32 q9 ∷
   rw 31 q10 ∷
   rw 34 q1 ∷
   re 32 3 (CX31 ∷ []) ∷
   rw 33 q10 ∷
   rw 34 q10 ∷
   re 36 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 35 q4 ∷
   rw 38 q1 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw⁻ 37 q5 ∷
   rw 40 q1 ∷
   re 38 3 (CS13⁻ ∷ []) ∷
   rw⁻ 39 q5 ∷
   rw 42 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw⁻ 41 q4 ∷
   rw⁻ 42 q6 ∷
   rw 35 q1 ∷
   rw⁻ 36 q4 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q7 ∷
   rw⁻ 38 q5 ∷
   re 40 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 39 q7 ∷
   rw⁻ 40 q5 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q7 ∷
   rw⁻ 42 q4 ∷
   rw⁻ 43 q6 ∷
   rw 36 q8 ∷
   re 36 8 (Toff102 ∷ []) ∷
   re 35 3 (Toff103 ∷ []) ∷
   rw 36 q10 ∷
   rw 37 q7 ∷
   rw 0 q11 ∷
   rw 6 q1 ∷
   rw 5 q2 ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q6 ∷
   rw 12 q7 ∷
   rw 11 q6 ∷
   rw 10 q4 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 8 q5 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 6 q5 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 4 q4 ∷
   rw 5 q8 ∷
   re 5 8 (Toff102 ∷ []) ∷
   rw 3 q2 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 0 q2 ∷
   rw 1 q12 ∷
   rw⁻ 0 q3 ∷
   rw 1 q10 ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q5 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q6 ∷
   rw 2 q1 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw⁻ 5 q5 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw⁻ 7 q5 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q6 ∷
   rw 3 q8 ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 4 q10 ∷
   rw 5 q7 ∷ []) Eq.refl
