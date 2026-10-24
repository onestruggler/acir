{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D435 (W : Ws) where

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

private
  q1 : Eqn
  q1 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = wE 27 W
  q3 : Eqn
  q3 = wE 31 W
  q4 : Eqn
  q4 = wE 36 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q6 : Eqn
  q6 = wE 37 W
  q7 : Eqn
  q7 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 1124 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02] part2: 33 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-part2 : ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丠丠临丠临临乀丧丧乄丧乑业乑业中中中乑业中中中乏丧乏並丽丽並乀中中乑中乑乑") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-part2 = derive (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丠丠临丠临临乀丧丧乄丧乑业乑业中中中乑业中中中乏丧乏並丽丽並乀中中乑中乑乑") (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (re 40 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q1 ∷
   rw 42 q2 ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q1 ∷
   rw 43 q2 ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q3 ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 23 q4 ∷
   rw⁻ 24 q5 ∷
   rw 25 q6 ∷
   re 23 3 (ℓ "丧") ∷
   re 25 1 (ℓ "丼丠丼") ∷
   rw 24 q4 ∷
   rw⁻ 25 q5 ∷
   rw 26 q6 ∷
   re 24 3 (ℓ "丧") ∷
   re 26 1 (ℓ "丼临丼") ∷
   rw 25 q4 ∷
   rw⁻ 26 q7 ∷
   rw 27 q6 ∷
   re 25 3 (ℓ "乄") ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q4 ∷
   rw⁻ 27 q5 ∷
   rw 28 q6 ∷
   re 26 3 (ℓ "丧") ∷
   rw 17 q8 ∷ []) Eq.refl
