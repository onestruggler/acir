{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD564 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D564 (W : Ws) (Sᴰ : SD564) where

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
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-II/IV-units-1-2 : St 977
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-II/IV-units-1-2 = pickᴰ 0 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-II/IV-units-2-1 : St 978
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-II/IV-units-2-1 = pickᴰ 1 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 : St 979
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 = pickᴰ 2 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-comm-WBar⟨SSKSKK~31-⟶2⟩ : St 980
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-comm-WBar⟨SSKSKK~31-⟶2⟩ = pickᴰ 3 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-comm-WBar⟨SSSKSS~31-⟶2⟩ : St 981
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-comm-WBar⟨SSSKSS~31-⟶2⟩ = pickᴰ 4 Sᴰ
  lem-LF-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK31-CS12-CS12-CS12-S2-CK21-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-S2-S2-S2-CK21-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS01-CS01-CS01-S0-CK01-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK31-at-2 : St 982
  lem-LF-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK31-CS12-CS12-CS12-S2-CK21-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-S2-S2-S2-CK21-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS01-CS01-CS01-S0-CK01-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK31-at-2 = pickᴰ 5 Sᴰ

private
  q1 : Eqn
  q1 = wE 1579 W
  q2 : Eqn
  q2 = sE 981 lem-Bar⟨SSSKSS31-⟶0⟩-passes-comm-WBar⟨SSSKSS~31-⟶2⟩
  q3 : Eqn
  q3 = wE 1580 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CS23 CS23 CS23 CK32 CS23 CS23 CX31 CS12 CS12 CS12 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CS12 CK12 CS12 CS12 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 31 q1 ∷
   rw 0 q2 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = wE 1581 W
  q5 : Eqn
  q5 = sE 980 lem-Bar⟨SSSKSS31-⟶0⟩-passes-comm-WBar⟨SSKSKK~31-⟶2⟩
  q6 : Eqn
  q6 = wE 1582 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CS23 CS23 CK32 CS23 CK32 CK32 CX31 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CK12 CS12 CK12 CK12 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 31 q4 ∷
   rw 0 q5 ∷
   rw 0 q6 ∷ []) Eq.refl

private
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q9 : Eqn
  q9 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q10 : Eqn
  q10 = wE 772 W
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = wE 6 W
  q14 : Eqn
  q14 = wE 481 W
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q17 : Eqn
  q17 = wE 1618 W
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀)))
  q19 : Eqn
  q19 = wE 39 W
  q20 : Eqn
  q20 = wE 329 W
  q21 : Eqn
  q21 = wE 315 W
  q22 : Eqn
  q22 = wE 27 W
  q23 : Eqn
  q23 = wE 31 W
  q24 : Eqn
  q24 = sE 979 lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3
  q25 : Eqn
  q25 = wE 1619 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X2 X3 CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02 X2 X3]: 191 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X2 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X2 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 62 q7 ∷
   rw⁻ 61 q8 ∷
   rw⁻ 60 q9 ∷
   rw 59 q10 ∷
   rw 58 q10 ∷
   rw 57 q11 ∷
   rw 56 q10 ∷
   rw 55 q11 ∷
   rw 54 q11 ∷
   re 53 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q12 ∷
   rw 54 q13 ∷
   rw⁻ 53 q12 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 52 q11 ∷
   rw 51 q11 ∷
   rw 50 q11 ∷
   rw 49 q11 ∷
   rw 48 q11 ∷
   rw 47 q11 ∷
   rw 46 q14 ∷
   rw 45 q10 ∷
   rw 44 q11 ∷
   rw 43 q11 ∷
   rw 42 q11 ∷
   rw 41 q14 ∷
   rw 40 q10 ∷
   rw 39 q14 ∷
   rw 38 q10 ∷
   re 37 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q12 ∷
   rw 38 q13 ∷
   rw⁻ 37 q12 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw⁻ 36 q15 ∷
   rw⁻ 35 q15 ∷
   rw⁻ 34 q16 ∷
   rw⁻ 33 q15 ∷
   rw⁻ 32 q16 ∷
   rw⁻ 31 q16 ∷
   rw⁻ 30 q8 ∷
   rw⁻ 29 q9 ∷
   rw 30 q17 ∷
   rw 29 q8 ∷
   rw 30 q15 ∷
   rw 31 q16 ∷
   rw 32 q16 ∷
   rw 33 q18 ∷
   rw 34 q8 ∷
   rw 35 q8 ∷
   rw 36 q16 ∷
   rw 37 q16 ∷
   rw 38 q15 ∷
   rw 39 q16 ∷
   rw 40 q15 ∷
   rw 41 q15 ∷
   re 43 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 42 q12 ∷
   rw 43 q19 ∷
   rw 44 q12 ∷
   re 42 3 (CX30 ∷ []) ∷
   rw 43 q20 ∷
   rw 44 q21 ∷
   rw 45 q20 ∷
   rw 46 q21 ∷
   rw 47 q22 ∷
   rw 48 q22 ∷
   rw 49 q22 ∷
   rw 50 q20 ∷
   rw 51 q21 ∷
   rw 52 q22 ∷
   rw 53 q22 ∷
   rw 54 q22 ∷
   rw 55 q22 ∷
   rw 56 q22 ∷
   rw 57 q22 ∷
   re 59 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 58 q12 ∷
   rw 59 q19 ∷
   rw 60 q12 ∷
   re 58 3 (CX30 ∷ []) ∷
   rw 59 q22 ∷
   rw 60 q22 ∷
   rw 61 q20 ∷
   rw 62 q22 ∷
   rw 63 q20 ∷
   rw 64 q20 ∷
   rw 65 q8 ∷
   rw 66 q8 ∷
   rw 67 q15 ∷
   rw 68 q16 ∷
   rw 69 q16 ∷
   rw 70 q18 ∷
   rw 71 q8 ∷
   rw 72 q23 ∷
   rw 0 q24 ∷
   rw 43 q7 ∷
   rw⁻ 42 q8 ∷
   rw⁻ 41 q18 ∷
   rw⁻ 40 q16 ∷
   rw⁻ 39 q16 ∷
   rw⁻ 38 q15 ∷
   rw⁻ 37 q8 ∷
   rw⁻ 36 q8 ∷
   rw 35 q10 ∷
   rw 34 q10 ∷
   rw 33 q11 ∷
   rw 32 q10 ∷
   rw 31 q11 ∷
   rw 30 q11 ∷
   re 29 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q12 ∷
   rw 30 q13 ∷
   rw⁻ 29 q12 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 28 q11 ∷
   rw 27 q11 ∷
   rw 26 q11 ∷
   rw 25 q11 ∷
   rw 24 q11 ∷
   rw 23 q11 ∷
   rw 22 q14 ∷
   rw 21 q10 ∷
   rw 20 q11 ∷
   rw 19 q11 ∷
   rw 18 q11 ∷
   rw 17 q14 ∷
   rw 16 q10 ∷
   rw 15 q14 ∷
   rw 14 q10 ∷
   re 13 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q12 ∷
   rw 14 q13 ∷
   rw⁻ 13 q12 ∷
   re 14 3 (CX31 ∷ []) ∷
   rw⁻ 12 q15 ∷
   rw⁻ 11 q15 ∷
   rw⁻ 10 q16 ∷
   rw⁻ 9 q15 ∷
   rw⁻ 8 q16 ∷
   rw⁻ 7 q16 ∷
   rw⁻ 6 q8 ∷
   rw⁻ 5 q8 ∷
   rw⁻ 4 q18 ∷
   rw⁻ 3 q16 ∷
   rw⁻ 2 q16 ∷
   rw⁻ 1 q15 ∷
   rw⁻ 0 q8 ∷
   rw 1 q25 ∷
   rw 0 q9 ∷
   rw 1 q8 ∷
   rw 2 q16 ∷
   rw 3 q16 ∷
   rw 4 q15 ∷
   rw 5 q16 ∷
   rw 6 q15 ∷
   rw 7 q15 ∷
   re 9 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q19 ∷
   rw 10 q12 ∷
   re 8 3 (CX30 ∷ []) ∷
   rw 9 q20 ∷
   rw 10 q21 ∷
   rw 11 q20 ∷
   rw 12 q21 ∷
   rw 13 q22 ∷
   rw 14 q22 ∷
   rw 15 q22 ∷
   rw 16 q20 ∷
   rw 17 q21 ∷
   rw 18 q22 ∷
   rw 19 q22 ∷
   rw 20 q22 ∷
   rw 21 q22 ∷
   rw 22 q22 ∷
   rw 23 q22 ∷
   re 25 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q12 ∷
   rw 25 q19 ∷
   rw 26 q12 ∷
   re 24 3 (CX30 ∷ []) ∷
   rw 25 q22 ∷
   rw 26 q22 ∷
   rw 27 q20 ∷
   rw 28 q22 ∷
   rw 29 q20 ∷
   rw 30 q20 ∷
   rw 31 q9 ∷
   rw 32 q8 ∷
   rw 33 q23 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1620 W
  q27 : Eqn
  q27 = sE 978 lem-Bar⟨SSKSKK32-⟶0⟩-passes-II/IV-units-2-1
  q28 : Eqn
  q28 = wE 1621 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 TOFF213 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF213-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff213 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF213-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) (X3 ∷ Toff213 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 29 q26 ∷
   rw 0 q27 ∷
   rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 1622 W
  q30 : Eqn
  q30 = sE 977 lem-Bar⟨SSKSKK32-⟶0⟩-passes-II/IV-units-1-2
  q31 : Eqn
  q31 = wE 1623 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 TOFF123 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF123-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF123-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 29 q29 ∷
   rw 0 q30 ∷
   rw 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 982 lem-LF-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK31-CS12-CS12-CS12-S2-CK21-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-S2-S2-S2-CK21-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS01-CS01-CS01-S0-CK01-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK31-at-2
  q33 : Eqn
  q33 = wE 225 W
  q34 : Eqn
  q34 = wE 871 W
  q35 : Eqn
  q35 = wE 872 W
  q36 : Eqn
  q36 = eqn (CS12 ∷ X3 ∷ []) (X3 ∷ CS12 ∷ []) (low₃-comm ((CS ↑)) (X))
  q37 : Eqn
  q37 = eqn (CK21 ∷ X3 ∷ []) (X3 ∷ CK21 ∷ []) (low₃-comm ((CK₁₀ ↑)) (X))
  q38 : Eqn
  q38 = eqn (CX20 ∷ X3 ∷ []) (X3 ∷ CX20 ∷ []) (low₃-comm ((Swap ↑ • CX₁₀ • Swap ↑)) (X))
  q39 : Eqn
  q39 = eqn (CK01 ∷ X3 ∷ []) (X3 ∷ CK01 ∷ []) (low-comm (CK₀₁) ((X ↑)))
  q40 : Eqn
  q40 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q41 : Eqn
  q41 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q42 : Eqn
  q42 = wE 390 W
  q43 : Eqn
  q43 = eqn (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X))
  q44 : Eqn
  q44 = eqn (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑)))
  q45 : Eqn
  q45 = wE 217 W
  q46 : Eqn
  q46 = eqn (X0 ∷ Toff312 ∷ []) (Toff312 ∷ X0 ∷ []) (low₁-comm (X) (Toffᵗ))
  q47 : Eqn
  q47 = wE 1106 W
  q48 : Eqn
  q48 = wE 388 W
  q49 : Eqn
  q49 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))

-- kk pieces X1 X2 X3 CS01 CS01 CK01 CS01 CX02 CS12 CS12 CS12 CK21 S2 CS1 at 2: 69 steps
lem-kk-pieces-X1-X2-X3-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12-CK21-S2-CS1-at-2 : ⟪ (X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X1 ∷ X2 ∷ X2 ∷ X3 ∷ Toff302 ∷ X2 ∷ X3 ∷ X1 ∷ X2 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ X3 ∷ Toff302 ∷ X2 ∷ X3 ∷ X1 ∷ X2 ∷ X3 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-kk-pieces-X1-X2-X3-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12-CK21-S2-CS1-at-2 = derive (X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X1 ∷ X2 ∷ X2 ∷ X3 ∷ Toff302 ∷ X2 ∷ X3 ∷ X1 ∷ X2 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ X3 ∷ Toff302 ∷ X2 ∷ X3 ∷ X1 ∷ X2 ∷ X3 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw 3 q32 ∷
   rw 32 q33 ∷
   rw 33 q34 ∷
   rw 34 q35 ∷
   rw 39 q33 ∷
   rw 40 q34 ∷
   rw 41 q35 ∷
   rw 76 q33 ∷
   rw 77 q34 ∷
   rw 78 q35 ∷
   rw 83 q33 ∷
   rw 84 q34 ∷
   rw 85 q35 ∷
   rw⁻ 2 q36 ∷
   rw⁻ 3 q36 ∷
   rw⁻ 4 q37 ∷
   rw⁻ 5 q36 ∷
   rw⁻ 6 q37 ∷
   rw⁻ 7 q37 ∷
   rw⁻ 8 q38 ∷
   rw⁻ 9 q39 ∷
   rw⁻ 10 q40 ∷
   rw⁻ 11 q39 ∷
   rw⁻ 12 q40 ∷
   rw⁻ 13 q41 ∷
   rw⁻ 14 q41 ∷
   rw⁻ 15 q41 ∷
   rw⁻ 16 q39 ∷
   rw⁻ 17 q40 ∷
   rw⁻ 18 q41 ∷
   rw⁻ 19 q41 ∷
   rw⁻ 20 q41 ∷
   rw⁻ 21 q41 ∷
   rw⁻ 22 q41 ∷
   rw⁻ 23 q41 ∷
   rw⁻ 24 q38 ∷
   rw⁻ 25 q41 ∷
   rw⁻ 26 q41 ∷
   rw⁻ 27 q39 ∷
   rw⁻ 28 q41 ∷
   rw⁻ 29 q39 ∷
   rw⁻ 30 q39 ∷
   rw 31 q42 ∷
   rw⁻ 31 q43 ∷
   rw 33 q43 ∷
   rw 34 q44 ∷
   re 36 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   rw 35 q45 ∷
   rw 36 q46 ∷
   rw 37 q47 ∷
   re 35 3 (Toff302 ∷ []) ∷
   rw 36 q44 ∷
   rw 37 q43 ∷
   rw 38 q48 ∷
   rw⁻ 36 q49 ∷
   rw⁻ 72 q49 ∷
   rw⁻ 73 q44 ∷
   rw⁻ 72 q43 ∷
   rw 75 q43 ∷
   rw 76 q44 ∷
   re 78 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   rw 77 q45 ∷
   rw 78 q46 ∷
   rw 79 q47 ∷
   re 77 3 (Toff302 ∷ []) ∷
   rw 78 q44 ∷
   rw 79 q43 ∷
   rw 80 q48 ∷
   rw⁻ 78 q49 ∷ []) Eq.refl
