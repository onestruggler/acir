{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD673 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D673 (W : Ws) (Sᴰ : SD673) where

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
  lem-L87-merge-k-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02--1 : St 1774
  lem-L87-merge-k-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02--1 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = eqn (X0 ∷ X1 ∷ []) (X1 ∷ X0 ∷ []) (low₁-comm (X) (X))
  q2 : Eqn
  q2 = wE 388 W
  q3 : Eqn
  q3 = eqn (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑)))
  q4 : Eqn
  q4 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q5 : Eqn
  q5 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q6 : Eqn
  q6 = wE 390 W
  q7 : Eqn
  q7 = eqn (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X))
  q8 : Eqn
  q8 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))
  q9 : Eqn
  q9 = wE 389 W
  q10 : Eqn
  q10 = wE 387 W
  q11 : Eqn
  q11 = sE 1774 lem-L87-merge-k-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02--1
  q12 : Eqn
  q12 = wE 5 W
  q13 : Eqn
  q13 = wE 1106 W
  q14 : Eqn
  q14 = wE 481 W
  q15 : Eqn
  q15 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = wE 140 W
  q17 : Eqn
  q17 = wE 7 W
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q19 : Eqn
  q19 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q20 : Eqn
  q20 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q21 : Eqn
  q21 = wE 2009 W
  q22 : Eqn
  q22 = wE 121 W
  q23 : Eqn
  q23 = wE 31 W

-- L87 K0: 646 steps
lem-L87-K0 : ⟪ (X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ X2 ∷ X2 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ X3 ∷ X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ X3 ∷ X3 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X3 ∷ X2 ∷ X3 ∷ X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ X3 ∷ X2 ∷ X2 ∷ X3 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X3 ∷ X2 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ []) ⟫ʷ
lem-L87-K0 = derive (X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ X2 ∷ X2 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ X3 ∷ X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ X3 ∷ X3 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X3 ∷ X2 ∷ X3 ∷ X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ X3 ∷ X2 ∷ X2 ∷ X3 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ X3 ∷ X2 ∷ X0 ∷ S0 ∷ X0 ∷ []) (K0 ∷ [])
  (rw 1 q1 ∷
   rw 0 q2 ∷
   rw 83 q1 ∷
   rw⁻ 86 q3 ∷
   rw⁻ 87 q4 ∷
   rw⁻ 88 q3 ∷
   rw⁻ 89 q5 ∷
   rw 90 q6 ∷
   rw⁻ 85 q7 ∷
   rw⁻ 86 q8 ∷
   rw⁻ 87 q7 ∷
   rw 88 q9 ∷
   rw 84 q1 ∷
   rw 85 q10 ∷
   rw 83 q2 ∷
   rw 164 q1 ∷
   rw⁻ 167 q5 ∷
   rw⁻ 168 q3 ∷
   rw⁻ 169 q4 ∷
   rw⁻ 170 q3 ∷
   rw⁻ 171 q5 ∷
   rw 172 q6 ∷
   rw 166 q9 ∷
   rw 165 q1 ∷
   rw 166 q10 ∷
   rw 164 q2 ∷
   rw 246 q1 ∷
   rw⁻ 249 q3 ∷
   rw⁻ 250 q5 ∷
   rw⁻ 251 q5 ∷
   rw⁻ 252 q4 ∷
   rw⁻ 253 q3 ∷
   rw⁻ 254 q5 ∷
   rw 255 q6 ∷
   rw⁻ 248 q7 ∷
   rw 249 q9 ∷
   rw 247 q1 ∷
   rw⁻ 249 q8 ∷
   rw⁻ 250 q7 ∷
   rw 251 q9 ∷
   rw 246 q2 ∷
   rw 246 q10 ∷
   rw 327 q1 ∷
   rw⁻ 330 q5 ∷
   rw 331 q6 ∷
   rw 329 q9 ∷
   rw 328 q1 ∷
   rw 329 q10 ∷
   rw 327 q2 ∷
   rw 410 q1 ∷
   rw⁻ 413 q3 ∷
   rw 414 q6 ∷
   rw⁻ 412 q7 ∷
   rw⁻ 414 q4 ∷
   rw⁻ 415 q3 ∷
   rw⁻ 416 q5 ∷
   rw 417 q6 ∷
   rw 411 q1 ∷
   rw⁻ 413 q8 ∷
   rw⁻ 414 q7 ∷
   rw 415 q9 ∷
   rw 410 q2 ∷
   rw 410 q10 ∷
   rw 491 q1 ∷
   rw 494 q6 ∷
   rw 493 q9 ∷
   rw⁻ 493 q3 ∷
   rw⁻ 494 q4 ∷
   rw⁻ 495 q3 ∷
   rw⁻ 496 q5 ∷
   rw 497 q6 ∷
   rw 492 q1 ∷
   rw 493 q10 ∷
   rw 491 q2 ∷
   rw 573 q1 ∷
   rw⁻ 576 q3 ∷
   rw 577 q6 ∷
   rw⁻ 575 q7 ∷
   rw 576 q9 ∷
   rw 574 q1 ∷
   rw⁻ 577 q4 ∷
   rw⁻ 578 q3 ∷
   rw⁻ 579 q5 ∷
   rw 580 q6 ∷
   rw 573 q2 ∷
   rw⁻ 574 q8 ∷
   rw⁻ 575 q7 ∷
   rw 576 q9 ∷
   rw 573 q10 ∷
   rw 654 q1 ∷
   rw 657 q6 ∷
   rw 656 q9 ∷
   rw 655 q10 ∷
   rw 3 q11 ∷
   rw 42 q11 ∷
   rw 82 q11 ∷
   rw 121 q11 ∷
   rw 161 q12 ∷
   rw 160 q13 ∷
   rw 159 q14 ∷
   re 158 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 160 q15 ∷
   rw 159 q16 ∷
   rw⁻ 158 q15 ∷
   re 159 3 (CK31 ∷ []) ∷
   re 157 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 159 q15 ∷
   rw 158 q16 ∷
   rw⁻ 157 q15 ∷
   re 158 3 (CK31 ∷ []) ∷
   re 156 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 158 q15 ∷
   rw 157 q17 ∷
   rw⁻ 156 q15 ∷
   re 157 3 (CS13 ∷ []) ∷
   re 155 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 157 q15 ∷
   rw 156 q16 ∷
   rw⁻ 155 q15 ∷
   re 156 3 (CK31 ∷ []) ∷
   re 154 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 156 q15 ∷
   rw 155 q17 ∷
   rw⁻ 154 q15 ∷
   re 155 3 (CS13 ∷ []) ∷
   re 153 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 155 q15 ∷
   rw 154 q17 ∷
   rw⁻ 153 q15 ∷
   re 154 3 (CS13 ∷ []) ∷
   re 152 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 154 q15 ∷
   rw 153 q16 ∷
   rw⁻ 152 q15 ∷
   re 153 3 (CK31 ∷ []) ∷
   re 151 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 153 q15 ∷
   rw 152 q16 ∷
   rw⁻ 151 q15 ∷
   re 152 3 (CK31 ∷ []) ∷
   re 150 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 152 q15 ∷
   rw 151 q17 ∷
   rw⁻ 150 q15 ∷
   re 151 3 (CS13 ∷ []) ∷
   re 149 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 151 q15 ∷
   rw 150 q16 ∷
   rw⁻ 149 q15 ∷
   re 150 3 (CK31 ∷ []) ∷
   re 148 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 150 q15 ∷
   rw 149 q17 ∷
   rw⁻ 148 q15 ∷
   re 149 3 (CS13 ∷ []) ∷
   re 147 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 149 q15 ∷
   rw 148 q17 ∷
   rw⁻ 147 q15 ∷
   re 148 3 (CS13 ∷ []) ∷
   rw⁻ 146 q18 ∷
   re 145 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 147 q15 ∷
   rw 146 q17 ∷
   rw⁻ 145 q15 ∷
   re 146 3 (CS13 ∷ []) ∷
   re 144 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 146 q15 ∷
   rw 145 q17 ∷
   rw⁻ 144 q15 ∷
   re 145 3 (CS13 ∷ []) ∷
   re 143 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 145 q15 ∷
   rw 144 q16 ∷
   rw⁻ 143 q15 ∷
   re 144 3 (CK31 ∷ []) ∷
   re 142 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 144 q15 ∷
   rw 143 q17 ∷
   rw⁻ 142 q15 ∷
   re 143 3 (CS13 ∷ []) ∷
   re 141 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 143 q15 ∷
   rw 142 q17 ∷
   rw⁻ 141 q15 ∷
   re 142 3 (CS13 ∷ []) ∷
   re 140 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 142 q15 ∷
   rw 141 q17 ∷
   rw⁻ 140 q15 ∷
   re 141 3 (CS13 ∷ []) ∷
   re 139 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 141 q15 ∷
   rw 140 q17 ∷
   rw⁻ 139 q15 ∷
   re 140 3 (CS13 ∷ []) ∷
   re 138 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 140 q15 ∷
   rw 139 q17 ∷
   rw⁻ 138 q15 ∷
   re 139 3 (CS13 ∷ []) ∷
   re 137 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 139 q15 ∷
   rw 138 q16 ∷
   rw⁻ 137 q15 ∷
   re 138 3 (CK31 ∷ []) ∷
   re 136 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 138 q15 ∷
   rw 137 q17 ∷
   rw⁻ 136 q15 ∷
   re 137 3 (CS13 ∷ []) ∷
   re 135 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 137 q15 ∷
   rw 136 q17 ∷
   rw⁻ 135 q15 ∷
   re 136 3 (CS13 ∷ []) ∷
   re 134 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 136 q15 ∷
   rw 135 q17 ∷
   rw⁻ 134 q15 ∷
   re 135 3 (CS13 ∷ []) ∷
   rw⁻ 133 q18 ∷
   rw 132 q16 ∷
   rw 131 q16 ∷
   rw 130 q17 ∷
   rw 129 q16 ∷
   rw 128 q17 ∷
   rw 127 q17 ∷
   rw 126 q16 ∷
   rw 125 q16 ∷
   rw 124 q17 ∷
   rw 123 q16 ∷
   rw 122 q17 ∷
   rw 121 q17 ∷
   rw⁻ 120 q19 ∷
   re 119 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 121 q15 ∷
   rw 120 q16 ∷
   rw⁻ 119 q15 ∷
   re 120 3 (CK31 ∷ []) ∷
   re 118 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 120 q15 ∷
   rw 119 q16 ∷
   rw⁻ 118 q15 ∷
   re 119 3 (CK31 ∷ []) ∷
   re 117 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 119 q15 ∷
   rw 118 q17 ∷
   rw⁻ 117 q15 ∷
   re 118 3 (CS13 ∷ []) ∷
   re 116 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 118 q15 ∷
   rw 117 q16 ∷
   rw⁻ 116 q15 ∷
   re 117 3 (CK31 ∷ []) ∷
   re 115 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 117 q15 ∷
   rw 116 q17 ∷
   rw⁻ 115 q15 ∷
   re 116 3 (CS13 ∷ []) ∷
   re 114 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 116 q15 ∷
   rw 115 q17 ∷
   rw⁻ 114 q15 ∷
   re 115 3 (CS13 ∷ []) ∷
   re 113 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 115 q15 ∷
   rw 114 q16 ∷
   rw⁻ 113 q15 ∷
   re 114 3 (CK31 ∷ []) ∷
   re 112 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 114 q15 ∷
   rw 113 q16 ∷
   rw⁻ 112 q15 ∷
   re 113 3 (CK31 ∷ []) ∷
   re 111 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 113 q15 ∷
   rw 112 q17 ∷
   rw⁻ 111 q15 ∷
   re 112 3 (CS13 ∷ []) ∷
   re 110 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 112 q15 ∷
   rw 111 q16 ∷
   rw⁻ 110 q15 ∷
   re 111 3 (CK31 ∷ []) ∷
   re 109 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 111 q15 ∷
   rw 110 q17 ∷
   rw⁻ 109 q15 ∷
   re 110 3 (CS13 ∷ []) ∷
   re 108 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 110 q15 ∷
   rw 109 q17 ∷
   rw⁻ 108 q15 ∷
   re 109 3 (CS13 ∷ []) ∷
   rw⁻ 107 q18 ∷
   re 106 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 108 q15 ∷
   rw 107 q17 ∷
   rw⁻ 106 q15 ∷
   re 107 3 (CS13 ∷ []) ∷
   re 105 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 107 q15 ∷
   rw 106 q17 ∷
   rw⁻ 105 q15 ∷
   re 106 3 (CS13 ∷ []) ∷
   re 104 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 106 q15 ∷
   rw 105 q16 ∷
   rw⁻ 104 q15 ∷
   re 105 3 (CK31 ∷ []) ∷
   re 103 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 105 q15 ∷
   rw 104 q17 ∷
   rw⁻ 103 q15 ∷
   re 104 3 (CS13 ∷ []) ∷
   re 102 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 104 q15 ∷
   rw 103 q17 ∷
   rw⁻ 102 q15 ∷
   re 103 3 (CS13 ∷ []) ∷
   re 101 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 103 q15 ∷
   rw 102 q17 ∷
   rw⁻ 101 q15 ∷
   re 102 3 (CS13 ∷ []) ∷
   re 100 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 102 q15 ∷
   rw 101 q17 ∷
   rw⁻ 100 q15 ∷
   re 101 3 (CS13 ∷ []) ∷
   re 99 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 101 q15 ∷
   rw 100 q17 ∷
   rw⁻ 99 q15 ∷
   re 100 3 (CS13 ∷ []) ∷
   re 98 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 100 q15 ∷
   rw 99 q16 ∷
   rw⁻ 98 q15 ∷
   re 99 3 (CK31 ∷ []) ∷
   re 97 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 99 q15 ∷
   rw 98 q17 ∷
   rw⁻ 97 q15 ∷
   re 98 3 (CS13 ∷ []) ∷
   re 96 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 98 q15 ∷
   rw 97 q17 ∷
   rw⁻ 96 q15 ∷
   re 97 3 (CS13 ∷ []) ∷
   re 95 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 97 q15 ∷
   rw 96 q17 ∷
   rw⁻ 95 q15 ∷
   re 96 3 (CS13 ∷ []) ∷
   rw⁻ 94 q18 ∷
   rw 93 q16 ∷
   rw 92 q16 ∷
   rw 91 q17 ∷
   rw 90 q16 ∷
   rw 89 q17 ∷
   rw 88 q17 ∷
   rw 87 q16 ∷
   rw 86 q16 ∷
   rw 85 q17 ∷
   rw 84 q16 ∷
   rw 83 q17 ∷
   rw 82 q17 ∷
   rw⁻ 81 q20 ∷
   rw⁻ 80 q19 ∷
   re 79 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q15 ∷
   rw 80 q16 ∷
   rw⁻ 79 q15 ∷
   re 80 3 (CK31 ∷ []) ∷
   re 78 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q15 ∷
   rw 79 q16 ∷
   rw⁻ 78 q15 ∷
   re 79 3 (CK31 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q15 ∷
   rw 78 q17 ∷
   rw⁻ 77 q15 ∷
   re 78 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q15 ∷
   rw 77 q16 ∷
   rw⁻ 76 q15 ∷
   re 77 3 (CK31 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q15 ∷
   rw 76 q17 ∷
   rw⁻ 75 q15 ∷
   re 76 3 (CS13 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q15 ∷
   rw 75 q17 ∷
   rw⁻ 74 q15 ∷
   re 75 3 (CS13 ∷ []) ∷
   re 73 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q15 ∷
   rw 74 q16 ∷
   rw⁻ 73 q15 ∷
   re 74 3 (CK31 ∷ []) ∷
   re 72 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q15 ∷
   rw 73 q16 ∷
   rw⁻ 72 q15 ∷
   re 73 3 (CK31 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q15 ∷
   rw 72 q17 ∷
   rw⁻ 71 q15 ∷
   re 72 3 (CS13 ∷ []) ∷
   re 70 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q15 ∷
   rw 71 q16 ∷
   rw⁻ 70 q15 ∷
   re 71 3 (CK31 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q15 ∷
   rw 70 q17 ∷
   rw⁻ 69 q15 ∷
   re 70 3 (CS13 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q15 ∷
   rw 69 q17 ∷
   rw⁻ 68 q15 ∷
   re 69 3 (CS13 ∷ []) ∷
   rw⁻ 67 q18 ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q15 ∷
   rw 67 q17 ∷
   rw⁻ 66 q15 ∷
   re 67 3 (CS13 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q15 ∷
   rw 66 q17 ∷
   rw⁻ 65 q15 ∷
   re 66 3 (CS13 ∷ []) ∷
   re 64 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q15 ∷
   rw 65 q16 ∷
   rw⁻ 64 q15 ∷
   re 65 3 (CK31 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q15 ∷
   rw 64 q17 ∷
   rw⁻ 63 q15 ∷
   re 64 3 (CS13 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 64 q15 ∷
   rw 63 q17 ∷
   rw⁻ 62 q15 ∷
   re 63 3 (CS13 ∷ []) ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 63 q15 ∷
   rw 62 q17 ∷
   rw⁻ 61 q15 ∷
   re 62 3 (CS13 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 62 q15 ∷
   rw 61 q17 ∷
   rw⁻ 60 q15 ∷
   re 61 3 (CS13 ∷ []) ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 61 q15 ∷
   rw 60 q17 ∷
   rw⁻ 59 q15 ∷
   re 60 3 (CS13 ∷ []) ∷
   re 58 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q15 ∷
   rw 59 q16 ∷
   rw⁻ 58 q15 ∷
   re 59 3 (CK31 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q15 ∷
   rw 58 q17 ∷
   rw⁻ 57 q15 ∷
   re 58 3 (CS13 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q15 ∷
   rw 57 q17 ∷
   rw⁻ 56 q15 ∷
   re 57 3 (CS13 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q15 ∷
   rw 56 q17 ∷
   rw⁻ 55 q15 ∷
   re 56 3 (CS13 ∷ []) ∷
   rw⁻ 54 q18 ∷
   rw 53 q16 ∷
   rw 52 q16 ∷
   rw 51 q17 ∷
   rw 50 q16 ∷
   rw 49 q17 ∷
   rw 48 q17 ∷
   rw 47 q16 ∷
   rw 46 q16 ∷
   rw 45 q17 ∷
   rw 44 q16 ∷
   rw 43 q17 ∷
   rw 42 q17 ∷
   rw⁻ 41 q19 ∷
   re 40 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q15 ∷
   rw 41 q16 ∷
   rw⁻ 40 q15 ∷
   re 41 3 (CK31 ∷ []) ∷
   re 39 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q15 ∷
   rw 40 q16 ∷
   rw⁻ 39 q15 ∷
   re 40 3 (CK31 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q15 ∷
   rw 39 q17 ∷
   rw⁻ 38 q15 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q15 ∷
   rw 38 q16 ∷
   rw⁻ 37 q15 ∷
   re 38 3 (CK31 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q15 ∷
   rw 37 q17 ∷
   rw⁻ 36 q15 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q15 ∷
   rw 36 q17 ∷
   rw⁻ 35 q15 ∷
   re 36 3 (CS13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q15 ∷
   rw 35 q16 ∷
   rw⁻ 34 q15 ∷
   re 35 3 (CK31 ∷ []) ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q15 ∷
   rw 34 q16 ∷
   rw⁻ 33 q15 ∷
   re 34 3 (CK31 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q15 ∷
   rw 33 q17 ∷
   rw⁻ 32 q15 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q15 ∷
   rw 32 q16 ∷
   rw⁻ 31 q15 ∷
   re 32 3 (CK31 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q15 ∷
   rw 31 q17 ∷
   rw⁻ 30 q15 ∷
   re 31 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q15 ∷
   rw 30 q17 ∷
   rw⁻ 29 q15 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw⁻ 28 q18 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q15 ∷
   rw 28 q17 ∷
   rw⁻ 27 q15 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q15 ∷
   rw 27 q17 ∷
   rw⁻ 26 q15 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q15 ∷
   rw 26 q16 ∷
   rw⁻ 25 q15 ∷
   re 26 3 (CK31 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q15 ∷
   rw 25 q17 ∷
   rw⁻ 24 q15 ∷
   re 25 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q15 ∷
   rw 24 q17 ∷
   rw⁻ 23 q15 ∷
   re 24 3 (CS13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q15 ∷
   rw 23 q17 ∷
   rw⁻ 22 q15 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q15 ∷
   rw 22 q17 ∷
   rw⁻ 21 q15 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q15 ∷
   rw 21 q17 ∷
   rw⁻ 20 q15 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q15 ∷
   rw 20 q16 ∷
   rw⁻ 19 q15 ∷
   re 20 3 (CK31 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q15 ∷
   rw 19 q17 ∷
   rw⁻ 18 q15 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q15 ∷
   rw 18 q17 ∷
   rw⁻ 17 q15 ∷
   re 18 3 (CS13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q15 ∷
   rw 17 q17 ∷
   rw⁻ 16 q15 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 15 q18 ∷
   rw 14 q16 ∷
   rw 13 q16 ∷
   rw 12 q17 ∷
   rw 11 q16 ∷
   rw 10 q17 ∷
   rw 9 q17 ∷
   rw 8 q16 ∷
   rw 7 q16 ∷
   rw 6 q17 ∷
   rw 5 q16 ∷
   rw 4 q17 ∷
   rw 3 q17 ∷
   rw⁻ 2 q20 ∷
   rw⁻ 1 q19 ∷
   rw 0 q13 ∷
   rw 1 q21 ∷
   rw 0 q22 ∷
   rw 1 q23 ∷ []) Eq.refl
