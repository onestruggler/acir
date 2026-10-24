{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD786 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D786 (W : Ws) (Sᴰ : SD786) where

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
  lem-ROT-gad : St 2261
  lem-ROT-gad = pickᴰ 0 Sᴰ
  lem-ROT-gad-at1023 : St 3484
  lem-ROT-gad-at1023 = pickᴰ 1 Sᴰ
  lem-F10 : St 3485
  lem-F10 = pickᴰ 2 Sᴰ
  lem-F7b : St 3486
  lem-F7b = pickᴰ 3 Sᴰ

private
  q1 : Eqn
  q1 = sE 3484 lem-ROT-gad-at1023
  q2 : Eqn
  q2 = sE 3486 lem-F7b
  q3 : Eqn
  q3 = sE 3484 lem-ROT-gad-at1023

-- cls 1000PP0 0000PP1 0100R1 = 0100R1 1000PP0: 3 steps
lem-cls-1000PP0-0000PP1-0100R1-≡-0100R1-1000PP0 : ⟪ (ℓ "丌九中九丮丌习丽习举丒与丐丽习举习丑丏丒") ⟫ʷ ≈ ⟪ (ℓ "丒与丐丽习举习丑丏丒丌九中九丮丌") ⟫ʷ
lem-cls-1000PP0-0000PP1-0100R1-≡-0100R1-1000PP0 = derive (ℓ "丌九中九丮丌习丽习举丒与丐丽习举习丑丏丒") (ℓ "丒与丐丽习举习丑丏丒丌九中九丮丌")
  (rw⁻ 11 q1 ∷
   rw 0 q2 ∷
   rw 1 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = sE 2261 lem-ROT-gad
  q5 : Eqn
  q5 = sE 3485 lem-F10
  q6 : Eqn
  q6 = sE 2261 lem-ROT-gad

-- cls 0000R0 0100R1 0000R0 = 0100R1 0000R0 0100R1: 7 steps
lem-cls-0000R0-0100R1-0000R0-≡-0100R1-0000R0-0100R1 : ⟪ (ℓ "丈上中九丮九下三丒与丐丽习举习丑丏丒丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丒与丐丽习举习丑丏丒丈上中九丮九下三丒与丐丽习举习丑丏丒") ⟫ʷ
lem-cls-0000R0-0100R1-0000R0-≡-0100R1-0000R0-0100R1 = derive (ℓ "丈上中九丮九下三丒与丐丽习举习丑丏丒丈上中九丮九下三") (ℓ "丒与丐丽习举习丑丏丒丈上中九丮九下三丒与丐丽习举习丑丏丒")
  (rw⁻ 0 q4 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 16 q1 ∷
   rw 0 q5 ∷
   rw 1 q3 ∷
   rw 26 q3 ∷
   rw 10 q6 ∷ []) Eq.refl
