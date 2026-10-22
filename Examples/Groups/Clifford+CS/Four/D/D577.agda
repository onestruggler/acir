{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD577 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D577 (W : Ws) (Sᴰ : SD577) where

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
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X0-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-X3 : St 1008
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X0-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-X3 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q4 : Eqn
  q4 = eqn (X0 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ []) (wn 1106 W)
  q5 : Eqn
  q5 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q6 : Eqn
  q6 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q9 : Eqn
  q9 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q12 : Eqn
  q12 = eqn (X1 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ []) (wn 1642 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀)))
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q21 : Eqn
  q21 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X0-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-X3)
  q22 : Eqn
  q22 = eqn (X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X1 ∷ X2 ∷ X3 ∷ []) (wn 1643 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wn 317 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X0 X2 X3 CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02 X0 X2 X3]: 297 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 64 q1 ∷
   rw⁻ 63 q2 ∷
   rw⁻ 62 q3 ∷
   rw 61 q4 ∷
   rw 60 q5 ∷
   rw 59 q5 ∷
   rw 58 q6 ∷
   rw 57 q5 ∷
   rw 56 q6 ∷
   rw 55 q6 ∷
   re 54 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q7 ∷
   rw 55 q8 ∷
   rw⁻ 54 q7 ∷
   re 55 3 (CX31 ∷ []) ∷
   rw 53 q6 ∷
   rw 52 q6 ∷
   rw 51 q6 ∷
   rw 50 q6 ∷
   rw 49 q6 ∷
   rw 48 q6 ∷
   rw 47 q9 ∷
   rw 46 q5 ∷
   rw 45 q6 ∷
   rw 44 q6 ∷
   rw 43 q6 ∷
   rw 42 q9 ∷
   rw 41 q5 ∷
   rw 40 q9 ∷
   rw 39 q5 ∷
   re 38 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q7 ∷
   rw 39 q8 ∷
   rw⁻ 38 q7 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw⁻ 37 q10 ∷
   rw⁻ 36 q10 ∷
   rw⁻ 35 q11 ∷
   rw⁻ 34 q10 ∷
   rw⁻ 33 q11 ∷
   rw⁻ 32 q11 ∷
   rw⁻ 31 q2 ∷
   rw⁻ 30 q3 ∷
   rw 29 q4 ∷
   rw 30 q12 ∷
   rw 29 q2 ∷
   rw 30 q10 ∷
   rw 31 q11 ∷
   rw 32 q11 ∷
   rw 33 q13 ∷
   rw 34 q2 ∷
   rw 35 q2 ∷
   rw 36 q14 ∷
   rw 37 q13 ∷
   rw 38 q11 ∷
   rw 39 q11 ∷
   rw 40 q2 ∷
   rw 41 q2 ∷
   rw 42 q10 ∷
   rw 43 q15 ∷
   rw 44 q10 ∷
   rw 45 q15 ∷
   rw 46 q11 ∷
   rw 47 q11 ∷
   rw 48 q11 ∷
   rw 49 q10 ∷
   rw 50 q15 ∷
   rw 51 q11 ∷
   rw 52 q11 ∷
   rw 53 q11 ∷
   rw 54 q11 ∷
   rw 55 q11 ∷
   rw 56 q11 ∷
   re 58 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q7 ∷
   rw 58 q16 ∷
   rw 59 q7 ∷
   re 57 3 (CX30 ∷ []) ∷
   rw 58 q17 ∷
   rw 59 q17 ∷
   rw 60 q17 ∷
   rw 61 q17 ∷
   rw 62 q17 ∷
   rw 63 q17 ∷
   rw 64 q17 ∷
   rw 65 q17 ∷
   rw 66 q17 ∷
   rw 67 q17 ∷
   rw 68 q17 ∷
   rw 69 q17 ∷
   rw 70 q17 ∷
   rw 71 q17 ∷
   rw 72 q17 ∷
   rw 73 q17 ∷
   rw 74 q17 ∷
   rw 75 q17 ∷
   rw 76 q18 ∷
   rw 77 q18 ∷
   rw 78 q18 ∷
   rw 79 q19 ∷
   rw 80 q18 ∷
   rw 81 q17 ∷
   rw 82 q17 ∷
   rw 83 q17 ∷
   rw 84 q17 ∷
   rw 85 q17 ∷
   rw 86 q17 ∷
   rw 87 q17 ∷
   rw 88 q17 ∷
   rw 89 q17 ∷
   rw 90 q18 ∷
   rw 91 q18 ∷
   rw 92 q18 ∷
   rw 93 q19 ∷
   rw 94 q18 ∷
   rw 95 q18 ∷
   rw 96 q18 ∷
   rw 97 q18 ∷
   rw 98 q19 ∷
   rw 99 q18 ∷
   re 101 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 100 q7 ∷
   rw 101 q16 ∷
   rw 102 q7 ∷
   re 100 3 (CX30 ∷ []) ∷
   rw 101 q19 ∷
   rw 102 q18 ∷
   rw 103 q19 ∷
   rw 104 q18 ∷
   rw 105 q17 ∷
   rw 106 q17 ∷
   rw 107 q17 ∷
   rw 108 q19 ∷
   rw 109 q18 ∷
   rw 110 q17 ∷
   rw 111 q17 ∷
   rw 112 q17 ∷
   rw 113 q17 ∷
   rw 114 q17 ∷
   rw 115 q17 ∷
   rw 116 q2 ∷
   rw 117 q2 ∷
   rw 118 q10 ∷
   rw 119 q11 ∷
   rw 120 q11 ∷
   rw 121 q13 ∷
   rw 122 q2 ∷
   rw 123 q20 ∷
   rw 0 q21 ∷
   rw 94 q1 ∷
   rw⁻ 93 q2 ∷
   rw⁻ 92 q13 ∷
   rw⁻ 91 q11 ∷
   rw⁻ 90 q11 ∷
   rw⁻ 89 q10 ∷
   rw⁻ 88 q2 ∷
   rw⁻ 87 q2 ∷
   rw 86 q6 ∷
   rw 85 q6 ∷
   rw 84 q6 ∷
   rw 83 q6 ∷
   rw 82 q6 ∷
   rw 81 q6 ∷
   rw 80 q9 ∷
   rw 79 q5 ∷
   rw 78 q6 ∷
   rw 77 q6 ∷
   rw 76 q6 ∷
   rw 75 q9 ∷
   rw 74 q5 ∷
   rw 73 q9 ∷
   rw 72 q5 ∷
   re 71 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q7 ∷
   rw 72 q8 ∷
   rw⁻ 71 q7 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 70 q9 ∷
   rw 69 q5 ∷
   rw 68 q9 ∷
   rw 67 q9 ∷
   rw 66 q9 ∷
   rw 65 q9 ∷
   rw 64 q5 ∷
   rw 63 q9 ∷
   rw 62 q9 ∷
   rw 61 q9 ∷
   rw 60 q6 ∷
   rw 59 q6 ∷
   rw 58 q6 ∷
   rw 57 q6 ∷
   rw 56 q6 ∷
   rw 55 q6 ∷
   rw 54 q6 ∷
   rw 53 q6 ∷
   rw 52 q6 ∷
   rw 51 q9 ∷
   rw 50 q5 ∷
   rw 49 q9 ∷
   rw 48 q9 ∷
   rw 47 q9 ∷
   rw 46 q6 ∷
   rw 45 q6 ∷
   rw 44 q6 ∷
   rw 43 q6 ∷
   rw 42 q6 ∷
   rw 41 q6 ∷
   rw 40 q6 ∷
   rw 39 q6 ∷
   rw 38 q6 ∷
   rw 37 q6 ∷
   rw 36 q6 ∷
   rw 35 q6 ∷
   rw 34 q6 ∷
   rw 33 q6 ∷
   rw 32 q6 ∷
   rw 31 q6 ∷
   rw 30 q6 ∷
   rw 29 q6 ∷
   re 28 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q7 ∷
   rw 29 q8 ∷
   rw⁻ 28 q7 ∷
   re 29 3 (CX31 ∷ []) ∷
   rw⁻ 27 q11 ∷
   rw⁻ 26 q11 ∷
   rw⁻ 25 q11 ∷
   rw⁻ 24 q11 ∷
   rw⁻ 23 q11 ∷
   rw⁻ 22 q11 ∷
   rw⁻ 21 q15 ∷
   rw⁻ 20 q10 ∷
   rw⁻ 19 q11 ∷
   rw⁻ 18 q11 ∷
   rw⁻ 17 q11 ∷
   rw⁻ 16 q15 ∷
   rw⁻ 15 q10 ∷
   rw⁻ 14 q15 ∷
   rw⁻ 13 q10 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 10 q11 ∷
   rw⁻ 9 q11 ∷
   rw⁻ 8 q13 ∷
   rw⁻ 7 q14 ∷
   rw⁻ 6 q2 ∷
   rw⁻ 5 q2 ∷
   rw⁻ 4 q13 ∷
   rw⁻ 3 q11 ∷
   rw⁻ 2 q11 ∷
   rw⁻ 1 q10 ∷
   rw⁻ 0 q2 ∷
   rw 1 q22 ∷
   rw 0 q23 ∷
   rw 1 q3 ∷
   rw 2 q2 ∷
   rw 3 q11 ∷
   rw 4 q11 ∷
   rw 5 q10 ∷
   rw 6 q11 ∷
   rw 7 q10 ∷
   rw 8 q10 ∷
   re 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 10 q16 ∷
   rw 11 q7 ∷
   re 9 3 (CX30 ∷ []) ∷
   rw 10 q19 ∷
   rw 11 q18 ∷
   rw 12 q19 ∷
   rw 13 q18 ∷
   rw 14 q17 ∷
   rw 15 q17 ∷
   rw 16 q17 ∷
   rw 17 q19 ∷
   rw 18 q18 ∷
   rw 19 q17 ∷
   rw 20 q17 ∷
   rw 21 q17 ∷
   rw 22 q17 ∷
   rw 23 q17 ∷
   rw 24 q17 ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q7 ∷
   rw 26 q16 ∷
   rw 27 q7 ∷
   re 25 3 (CX30 ∷ []) ∷
   rw 26 q17 ∷
   rw 27 q17 ∷
   rw 28 q19 ∷
   rw 29 q17 ∷
   rw 30 q19 ∷
   rw 31 q19 ∷
   rw 32 q23 ∷
   rw 33 q3 ∷
   rw 34 q2 ∷
   rw 35 q20 ∷ []) Eq.refl
