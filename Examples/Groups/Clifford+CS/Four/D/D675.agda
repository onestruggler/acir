{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD675 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D675 (W : Ws) (Sᴰ : SD675) where

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
  lem-L87-merge-k-CS02-CS02-CK02-CS02-CX01-CS12-CS12-CS12--0 : St 1776
  lem-L87-merge-k-CS02-CS02-CK02-CS02-CX01-CS12-CS12-CS12--0 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 387 W
  q2 : Eqn
  q2 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q3 : Eqn
  q3 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q4 : Eqn
  q4 = wE 390 W
  q5 : Eqn
  q5 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q6 : Eqn
  q6 = wE 389 W
  q7 : Eqn
  q7 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q8 : Eqn
  q8 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q9 : Eqn
  q9 = eqn (ℓ "丌丒") (ℓ "丒丌") (low₁-comm (X) (X))
  q10 : Eqn
  q10 = wE 388 W
  q11 : Eqn
  q11 = sE 1776 lem-L87-merge-k-CS02-CS02-CK02-CS02-CX01-CS12-CS12-CS12--0
  q12 : Eqn
  q12 = wE 2010 W

-- L87 K2: 84 steps
lem-L87-K2 : ⟪ (ℓ "丌丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丌丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丒丌丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丌丒丒丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丒丞丌丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丌丞丞丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丞丒丞丌丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丌丞丒丒丞丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丞丒丘且丘") ⟫ʷ ≈ ⟪ (ℓ "世") ⟫ʷ
lem-L87-K2 = derive (ℓ "丌丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丌丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丒丌丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丌丒丒丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丒丞丌丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丌丞丞丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丞丒丞丌丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丌丞丒丒丞丌丘丞丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丘丞丞丒丘且丘") (ℓ "世")
  (rw 0 q1 ∷
   rw⁻ 84 q2 ∷
   rw⁻ 85 q2 ∷
   rw⁻ 86 q3 ∷
   rw 87 q4 ∷
   rw⁻ 83 q5 ∷
   rw⁻ 84 q5 ∷
   rw 85 q6 ∷
   rw 82 q1 ∷
   rw⁻ 165 q7 ∷
   rw⁻ 166 q2 ∷
   rw⁻ 167 q2 ∷
   rw⁻ 168 q3 ∷
   rw 169 q4 ∷
   rw⁻ 164 q8 ∷
   rw⁻ 165 q5 ∷
   rw⁻ 166 q5 ∷
   rw 167 q6 ∷
   rw⁻ 164 q9 ∷
   rw⁻ 165 q9 ∷
   rw 163 q1 ∷
   rw⁻ 247 q2 ∷
   rw⁻ 248 q7 ∷
   rw⁻ 249 q7 ∷
   rw⁻ 250 q2 ∷
   rw⁻ 251 q3 ∷
   rw 252 q4 ∷
   rw⁻ 246 q5 ∷
   rw⁻ 247 q8 ∷
   rw⁻ 248 q8 ∷
   rw⁻ 249 q5 ∷
   rw 250 q6 ∷
   rw 245 q1 ∷
   rw 245 q10 ∷
   rw⁻ 328 q7 ∷
   rw 329 q4 ∷
   rw⁻ 327 q8 ∷
   rw⁻ 328 q5 ∷
   rw⁻ 329 q5 ∷
   rw 330 q6 ∷
   rw⁻ 327 q9 ∷
   rw⁻ 328 q9 ∷
   rw 326 q1 ∷
   rw⁻ 411 q2 ∷
   rw 412 q4 ∷
   rw⁻ 410 q5 ∷
   rw⁻ 412 q2 ∷
   rw⁻ 413 q3 ∷
   rw 414 q4 ∷
   rw 409 q1 ∷
   rw⁻ 409 q5 ∷
   rw 410 q6 ∷
   rw 492 q4 ∷
   rw⁻ 491 q8 ∷
   rw⁻ 493 q2 ∷
   rw⁻ 494 q2 ∷
   rw⁻ 495 q3 ∷
   rw 496 q4 ∷
   rw⁻ 492 q5 ∷
   rw⁻ 493 q5 ∷
   rw 494 q6 ∷
   rw⁻ 491 q9 ∷
   rw⁻ 492 q9 ∷
   rw 490 q1 ∷
   rw⁻ 574 q2 ∷
   rw 575 q4 ∷
   rw⁻ 573 q5 ∷
   rw⁻ 574 q8 ∷
   rw⁻ 575 q8 ∷
   rw⁻ 577 q2 ∷
   rw⁻ 578 q3 ∷
   rw 579 q4 ∷
   rw 572 q1 ∷
   rw 572 q10 ∷
   rw⁻ 572 q5 ∷
   rw 573 q6 ∷
   rw 655 q4 ∷
   rw⁻ 654 q8 ∷
   rw 655 q6 ∷
   rw 2 q11 ∷
   rw 41 q11 ∷
   rw 81 q11 ∷
   rw 120 q11 ∷
   rw 0 q12 ∷ []) Eq.refl
