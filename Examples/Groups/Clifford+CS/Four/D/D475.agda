{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D475 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 464 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q7 : Eqn
  q7 = wE 1241 W
  q8 : Eqn
  q8 = wE 151 W

-- pass [CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13] [X0 CKd03 X0]: 121 steps
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-CKd03-X0 : ⟪ (ℓ "丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌串丌") ⟫ʷ ≈ ⟪ (ℓ "丌串丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-CKd03-X0 = derive (ℓ "丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌串丌") (ℓ "丌串丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽")
  (rw 34 q1 ∷
   rw 33 q2 ∷
   re 32 1 (ℓ "乏丬乏") ∷
   rw 34 q3 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 32 q3 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 31 q3 ∷
   re 28 1 (ℓ "乏乇乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 29 q3 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q3 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 27 q3 ∷
   re 24 1 (ℓ "乏个乏") ∷
   rw 26 q3 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q3 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 24 q3 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q3 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 17 q3 ∷
   rw 14 q4 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 15 q3 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q3 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q3 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 12 q3 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 11 q3 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q3 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q3 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 8 q3 ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q5 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q7 ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "串") ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q6 ∷
   rw⁻ 7 q5 ∷
   rw⁻ 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丰") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "丽") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "丽") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "丽") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "乔") ∷
   rw 17 q8 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "丽") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "丽") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "丽") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "丽") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "丽") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "丽") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丽") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "丽") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丰") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "丽") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "丽") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "丽") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "乔") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "丽") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "丽") ∷
   rw 34 q3 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = wE 1242 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX03 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CK31 CS13 CK31 CK31] [X0 CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13 X0]: 215 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-X0 : ⟪ (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌") ⟫ʷ ≈ ⟪ (ℓ "丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔") ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-X0 = derive (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌") (ℓ "丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔")
  (rw 62 q1 ∷
   rw 61 q2 ∷
   re 60 1 (ℓ "乏丶乏") ∷
   rw 62 q3 ∷
   re 59 1 (ℓ "乏丶乏") ∷
   rw 61 q3 ∷
   re 58 1 (ℓ "乏乇乏") ∷
   rw 60 q3 ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 59 q3 ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 58 q3 ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 57 q3 ∷
   re 54 1 (ℓ "乏个乏") ∷
   rw 56 q3 ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 55 q3 ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 54 q3 ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 53 q3 ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 52 q3 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 51 q3 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 50 q3 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 49 q3 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 48 q3 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 47 q3 ∷
   rw 44 q4 ∷
   re 43 1 (ℓ "乏乇乏") ∷
   rw 45 q3 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 44 q3 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 43 q3 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 42 q3 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 41 q3 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 40 q3 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 39 q3 ∷
   re 36 1 (ℓ "乏个乏") ∷
   rw 38 q3 ∷
   rw 35 q5 ∷
   rw 34 q5 ∷
   rw 33 q6 ∷
   rw 32 q5 ∷
   rw 31 q5 ∷
   rw 30 q5 ∷
   rw 29 q2 ∷
   re 28 1 (ℓ "乏乇乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏乇乏") ∷
   rw 29 q3 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q3 ∷
   re 25 1 (ℓ "乏乇乏") ∷
   rw 27 q3 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q3 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q3 ∷
   re 22 1 (ℓ "乏个乏") ∷
   rw 24 q3 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q3 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   rw 15 q4 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 16 q3 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q3 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q3 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q3 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 11 q3 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 9 q3 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 8 q3 ∷
   rw 5 q6 ∷
   rw 4 q6 ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q5 ∷
   rw⁻ 2 q5 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丰") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丽") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丽") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "丽") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "乔") ∷
   rw 15 q8 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "丽") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "丽") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "丽") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "丽") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "丽") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "丽") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "丽") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丰") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "丽") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丽") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "丽") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "乔") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "丽") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "丽") ∷
   rw⁻ 32 q2 ∷
   rw⁻ 33 q5 ∷
   rw⁻ 34 q5 ∷
   rw⁻ 35 q6 ∷
   rw⁻ 36 q5 ∷
   rw⁻ 37 q6 ∷
   rw⁻ 38 q6 ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "丰") ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "乔") ∷
   rw 41 q8 ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "乔") ∷
   rw 43 q8 ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "丽") ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "丽") ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "丽") ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "乔") ∷
   rw 48 q8 ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "丽") ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "丽") ∷
   rw 53 q1 ∷
   re 51 3 (ℓ "丽") ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "丽") ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "丽") ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "丽") ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "丰") ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "丽") ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "丽") ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "乔") ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "丽") ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "乔") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "乔") ∷
   rw 62 q3 ∷ []) Eq.refl
