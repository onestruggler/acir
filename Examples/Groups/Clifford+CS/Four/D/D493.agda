{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D493 (W : Ws) where

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
  q1 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 335 W
  q4 : Eqn
  q4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 336 W
  q7 : Eqn
  q7 = wE 368 W
  q8 : Eqn
  q8 = wE 382 W
  q9 : Eqn
  q9 = wE 372 W
  q10 : Eqn
  q10 = wE 71 W

-- AXIOM LF @3012 part2: 58 steps
lem-AXIOM-LF-at3012-part2 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ Toff201 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ Sw23 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ Toff201 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ Toff201 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
lem-AXIOM-LF-at3012-part2 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ Toff201 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ Sw23 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw23 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ Toff201 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ Toff201 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  (re 65 3 (CS13⁻ ∷ []) ∷
   rw⁻ 66 q1 ∷
   rw 69 q2 ∷
   re 67 3 (CS03 ∷ []) ∷
   rw 68 q3 ∷
   rw⁻ 69 q4 ∷
   rw 70 q5 ∷
   rw 61 q6 ∷
   re 63 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 62 q5 ∷
   rw⁻ 63 q1 ∷
   re 65 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 64 q5 ∷
   rw⁻ 65 q1 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q5 ∷
   rw 67 q6 ∷
   rw⁻ 68 q4 ∷
   rw 61 q7 ∷
   re 61 8 (Toff201 ∷ []) ∷
   rw 64 q2 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 65 q2 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 66 q2 ∷
   re 64 3 (CK03 ∷ []) ∷
   rw 67 q2 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 68 q2 ∷
   re 66 3 (CK03 ∷ []) ∷
   rw 69 q2 ∷
   re 67 3 (CK03 ∷ []) ∷
   re 69 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   rw 69 q8 ∷
   rw 70 q9 ∷
   rw 71 q8 ∷
   rw 72 q9 ∷
   rw 73 q10 ∷
   rw 74 q10 ∷
   rw 75 q10 ∷
   rw 76 q8 ∷
   rw 77 q9 ∷
   rw 78 q10 ∷
   rw 79 q10 ∷
   rw 80 q10 ∷
   rw 81 q10 ∷
   rw 82 q10 ∷
   rw 83 q10 ∷
   re 85 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 84 q5 ∷
   rw 85 q10 ∷
   rw 86 q10 ∷
   rw 87 q8 ∷
   rw 88 q10 ∷
   rw 89 q8 ∷
   rw 90 q8 ∷
   rw 91 q5 ∷ []) Eq.refl
