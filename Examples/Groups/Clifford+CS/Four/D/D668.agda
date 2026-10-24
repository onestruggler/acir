{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD668 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D668 (W : Ws) (Sᴰ : SD668) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-hyb-sym-23 : St 1758
  lem-hyb-sym-23 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = sE 1758 lem-hyb-sym-23
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 464 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = wE 1203 W
  q8 : Eqn
  q8 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q9 : Eqn
  q9 = wE 1204 W
  q10 : Eqn
  q10 = wE 151 W

-- respell hyb CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02  -> CS03 CS03 CK30 CS03 CX31 CS01 CS01 CS01 : 235 steps
lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- : ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") ⟫ʷ ≈ ⟪ (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄") ⟫ʷ
lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- = derive (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄")
  (rw 0 q1 ∷
   rw 21 q2 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q3 ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw 21 q3 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q3 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q3 ∷
   re 16 1 (ℓ "乏丹乏") ∷
   rw 18 q3 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q3 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q3 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q3 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q3 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q3 ∷
   rw 9 q4 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw 10 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q3 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q3 ∷
   re 4 1 (ℓ "乏丹乏") ∷
   rw 6 q3 ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q7 ∷
   rw 2 q2 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "乑") ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "乓") ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q5 ∷
   rw⁻ 7 q5 ∷
   rw⁻ 8 q6 ∷
   rw⁻ 9 q8 ∷
   rw⁻ 10 q5 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q5 ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "乓") ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q6 ∷
   rw⁻ 20 q5 ∷
   rw 21 q3 ∷
   rw 78 q2 ∷
   rw 77 q5 ∷
   rw 76 q5 ∷
   rw 75 q5 ∷
   rw 74 q5 ∷
   rw 73 q5 ∷
   rw 72 q5 ∷
   rw 71 q6 ∷
   rw 70 q8 ∷
   rw 69 q5 ∷
   rw 68 q5 ∷
   rw 67 q5 ∷
   re 66 1 (ℓ "乏丹乏") ∷
   rw 68 q3 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q3 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q3 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q3 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q3 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q3 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q3 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q3 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q3 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q3 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q3 ∷
   rw 55 q4 ∷
   rw 54 q4 ∷
   rw 53 q4 ∷
   rw 52 q4 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q3 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q3 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q3 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q3 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q3 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q3 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q3 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q3 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q3 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q3 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q3 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q3 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q3 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q3 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q3 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q3 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q3 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q3 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 35 q3 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q3 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q3 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q3 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q3 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q3 ∷
   re 26 1 (ℓ "乏乄乏") ∷
   rw 28 q3 ∷
   rw 25 q4 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q3 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q3 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q3 ∷
   rw 23 q9 ∷
   rw⁻ 22 q5 ∷
   rw⁻ 23 q5 ∷
   rw⁻ 24 q5 ∷
   rw⁻ 25 q8 ∷
   rw⁻ 26 q6 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 29 q5 ∷
   rw⁻ 30 q5 ∷
   rw⁻ 31 q5 ∷
   rw⁻ 32 q5 ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "乓") ∷
   rw⁻ 34 q5 ∷
   rw⁻ 35 q5 ∷
   rw⁻ 36 q5 ∷
   rw⁻ 37 q5 ∷
   rw⁻ 38 q5 ∷
   rw⁻ 39 q5 ∷
   rw⁻ 40 q5 ∷
   rw⁻ 41 q5 ∷
   rw⁻ 42 q5 ∷
   rw⁻ 43 q5 ∷
   rw⁻ 44 q5 ∷
   rw⁻ 45 q5 ∷
   rw⁻ 46 q5 ∷
   rw⁻ 47 q5 ∷
   rw⁻ 48 q5 ∷
   rw⁻ 49 q5 ∷
   rw⁻ 50 q5 ∷
   rw⁻ 51 q5 ∷
   rw⁻ 52 q8 ∷
   rw⁻ 53 q8 ∷
   rw⁻ 54 q8 ∷
   rw⁻ 55 q8 ∷
   rw⁻ 56 q6 ∷
   rw⁻ 57 q5 ∷
   rw⁻ 58 q5 ∷
   rw⁻ 59 q5 ∷
   rw⁻ 60 q5 ∷
   rw⁻ 61 q5 ∷
   rw⁻ 62 q5 ∷
   rw⁻ 63 q5 ∷
   rw⁻ 64 q5 ∷
   rw⁻ 65 q5 ∷
   rw 68 q2 ∷
   re 66 3 (ℓ "乓") ∷
   rw 69 q2 ∷
   re 67 3 (ℓ "中") ∷
   rw 70 q2 ∷
   re 68 3 (ℓ "中") ∷
   rw 71 q2 ∷
   re 69 3 (ℓ "中") ∷
   rw 70 q10 ∷
   rw 73 q2 ∷
   re 71 3 (ℓ "乑") ∷
   rw 74 q2 ∷
   re 72 3 (ℓ "中") ∷
   rw 75 q2 ∷
   re 73 3 (ℓ "中") ∷
   rw 76 q2 ∷
   re 74 3 (ℓ "中") ∷
   rw 77 q2 ∷
   re 75 3 (ℓ "中") ∷
   rw 78 q2 ∷
   re 76 3 (ℓ "中") ∷
   rw 79 q2 ∷
   re 77 3 (ℓ "中") ∷
   rw 78 q3 ∷ []) Eq.refl
