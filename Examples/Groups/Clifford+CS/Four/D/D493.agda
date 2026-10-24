{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D493 (W : Ws) where

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
  q1 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 335 W
  q4 : Eqn
  q4 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
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
lem-AXIOM-LF-at3012-part2 : ⟪ (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁乣中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义乏东丽丣乏丷乏乏丣丧世一乏丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗乏") ⟫ʷ ≈ ⟪ (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁乣中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义乣中中丱中丱丱个乍且乍且义义义乍且义义义义义义个义义乍义乍乍") ⟫ʷ
lem-AXIOM-LF-at3012-part2 = derive (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁乣中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义乏东丽丣乏丷乏乏丣丧世一乏丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗乏") (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁乣中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义乣中中丱中丱丱个乍且乍且义义义乍且义义义义义义个义义乍义乍乍")
  (re 65 3 (ℓ "举") ∷
   rw⁻ 66 q1 ∷
   rw 69 q2 ∷
   re 67 3 (ℓ "中") ∷
   rw 68 q3 ∷
   rw⁻ 69 q4 ∷
   rw 70 q5 ∷
   rw 61 q6 ∷
   re 63 1 (ℓ "乏丶乏") ∷
   rw 62 q5 ∷
   rw⁻ 63 q1 ∷
   re 65 1 (ℓ "乏丷乏") ∷
   rw 64 q5 ∷
   rw⁻ 65 q1 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 66 q5 ∷
   rw 67 q6 ∷
   rw⁻ 68 q4 ∷
   rw 61 q7 ∷
   re 61 8 (ℓ "乣") ∷
   rw 64 q2 ∷
   re 62 3 (ℓ "中") ∷
   rw 65 q2 ∷
   re 63 3 (ℓ "中") ∷
   rw 66 q2 ∷
   re 64 3 (ℓ "丱") ∷
   rw 67 q2 ∷
   re 65 3 (ℓ "中") ∷
   rw 68 q2 ∷
   re 66 3 (ℓ "丱") ∷
   rw 69 q2 ∷
   re 67 3 (ℓ "丱") ∷
   re 69 1 (ℓ "乏个乏") ∷
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
   re 85 1 (ℓ "乏个乏") ∷
   rw 84 q5 ∷
   rw 85 q10 ∷
   rw 86 q10 ∷
   rw 87 q8 ∷
   rw 88 q10 ∷
   rw 89 q8 ∷
   rw 90 q8 ∷
   rw 91 q5 ∷ []) Eq.refl
