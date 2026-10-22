{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD676 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D676 (W : Ws) (Sᴰ : SD676) where

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
  lem-L87-merge-k-CS03-CS03-CK03-CS03-CX01-CS13-CS13-CS13--0 : St 1777
  lem-L87-merge-k-CS03-CS03-CK03-CS03-CX01-CS13-CS13-CS13--0 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = eqn (X0 ∷ X0 ∷ []) [] (wn 387 W)
  q2 : Eqn
  q2 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q3 : Eqn
  q3 = eqn (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑)))
  q4 : Eqn
  q4 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)
  q5 : Eqn
  q5 = eqn (X0 ∷ X1 ∷ []) (X1 ∷ X0 ∷ []) (low₁-comm (X) (X))
  q6 : Eqn
  q6 = eqn (X1 ∷ X1 ∷ []) [] (wn 388 W)
  q7 : Eqn
  q7 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q8 : Eqn
  q8 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))
  q9 : Eqn
  q9 = eqn (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X))
  q10 : Eqn
  q10 = eqn (X2 ∷ X2 ∷ []) [] (wn 389 W)
  q11 : Eqn
  q11 = eqn (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (lem-L87-merge-k-CS03-CS03-CK03-CS03-CX01-CS13-CS13-CS13--0)
  q12 : Eqn
  q12 = eqn (X1 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X1 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X1 ∷ X2 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X1 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X2 ∷ S3 ∷ X3 ∷ []) (K3 ∷ []) (wn 2011 W)

-- L87 K3: 86 steps
lem-L87-K3 : ⟪ (X0 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X1 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X2 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X2 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X2 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X2 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X3 ∷ S3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ []) ⟫ʷ
lem-L87-K3 = derive (X0 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X1 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X2 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X2 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X2 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X2 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X3 ∷ S3 ∷ X3 ∷ []) (K3 ∷ [])
  (rw 0 q1 ∷
   rw⁻ 84 q2 ∷
   rw⁻ 85 q2 ∷
   rw⁻ 86 q3 ∷
   rw 87 q4 ∷
   rw⁻ 83 q5 ∷
   rw⁻ 84 q5 ∷
   rw 85 q6 ∷
   rw 82 q1 ∷
   rw⁻ 165 q3 ∷
   rw⁻ 166 q2 ∷
   rw⁻ 167 q2 ∷
   rw⁻ 168 q3 ∷
   rw 169 q4 ∷
   rw 164 q6 ∷
   rw 163 q1 ∷
   rw⁻ 247 q2 ∷
   rw⁻ 248 q3 ∷
   rw⁻ 249 q3 ∷
   rw⁻ 250 q2 ∷
   rw⁻ 251 q3 ∷
   rw 252 q4 ∷
   rw⁻ 246 q5 ∷
   rw 247 q6 ∷
   rw 245 q1 ∷
   rw⁻ 245 q5 ∷
   rw 246 q6 ∷
   rw⁻ 328 q3 ∷
   rw⁻ 329 q7 ∷
   rw⁻ 330 q2 ∷
   rw⁻ 331 q2 ∷
   rw⁻ 332 q3 ∷
   rw 333 q4 ∷
   rw 327 q6 ∷
   rw⁻ 327 q8 ∷
   rw⁻ 328 q8 ∷
   rw⁻ 329 q9 ∷
   rw 326 q1 ∷
   rw⁻ 411 q2 ∷
   rw⁻ 412 q7 ∷
   rw⁻ 413 q7 ∷
   rw⁻ 414 q2 ∷
   rw⁻ 415 q3 ∷
   rw 416 q4 ∷
   rw⁻ 410 q5 ∷
   rw 412 q10 ∷
   rw 409 q1 ∷
   rw⁻ 409 q5 ∷
   rw 410 q6 ∷
   rw⁻ 492 q7 ∷
   rw⁻ 493 q3 ∷
   rw⁻ 494 q7 ∷
   rw⁻ 495 q2 ∷
   rw⁻ 496 q2 ∷
   rw⁻ 497 q3 ∷
   rw 498 q4 ∷
   rw⁻ 492 q9 ∷
   rw 493 q10 ∷
   rw 491 q6 ∷
   rw 490 q1 ∷
   rw⁻ 574 q2 ∷
   rw⁻ 575 q7 ∷
   rw⁻ 576 q3 ∷
   rw⁻ 577 q3 ∷
   rw⁻ 578 q7 ∷
   rw⁻ 579 q2 ∷
   rw⁻ 580 q3 ∷
   rw 581 q4 ∷
   rw⁻ 573 q5 ∷
   rw⁻ 575 q9 ∷
   rw⁻ 576 q9 ∷
   rw 577 q10 ∷
   rw 572 q1 ∷
   rw 572 q6 ∷
   rw⁻ 572 q5 ∷
   rw 573 q6 ∷
   rw⁻ 655 q7 ∷
   rw⁻ 656 q3 ∷
   rw 657 q4 ∷
   rw⁻ 655 q9 ∷
   rw 654 q6 ∷
   rw 2 q11 ∷
   rw 41 q11 ∷
   rw 81 q11 ∷
   rw 120 q11 ∷
   rw 0 q12 ∷ []) Eq.refl
