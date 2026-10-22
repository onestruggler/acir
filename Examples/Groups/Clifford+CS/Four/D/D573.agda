{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD573 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D573 (W : Ws) (Sᴰ : SD573) where

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
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩ : St 1003
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩ = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q5 : Eqn
  q5 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q9 : Eqn
  q9 = eqn (X3 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ X3 ∷ CX32 ∷ X3 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (wn 1638 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q13 : Eqn
  q13 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X3 ∷ CX32 ∷ X3 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X3 ∷ CX32 ∷ X3 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩)
  q14 : Eqn
  q14 = eqn (X3 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ X3 ∷ CX32 ∷ X3 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (X3 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (wn 1639 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S2 S2 S2 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S2 S2 S2 CK20 S2 S2 S2 S2 CK20 S2 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 X3]: 511 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ []) (X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 105 q1 ∷
   rw⁻ 104 q2 ∷
   rw 103 q3 ∷
   rw 102 q3 ∷
   rw 101 q3 ∷
   rw 100 q3 ∷
   rw 99 q3 ∷
   rw 98 q3 ∷
   rw⁻ 97 q4 ∷
   rw 96 q5 ∷
   rw 95 q3 ∷
   rw 94 q3 ∷
   rw 93 q3 ∷
   rw⁻ 92 q4 ∷
   rw 91 q5 ∷
   rw⁻ 90 q4 ∷
   rw 89 q5 ∷
   rw⁻ 88 q6 ∷
   rw⁻ 87 q4 ∷
   rw 86 q5 ∷
   rw⁻ 85 q4 ∷
   rw⁻ 84 q4 ∷
   rw⁻ 83 q4 ∷
   rw⁻ 82 q4 ∷
   rw 81 q5 ∷
   rw⁻ 80 q4 ∷
   rw⁻ 79 q4 ∷
   rw⁻ 78 q4 ∷
   rw 77 q3 ∷
   rw 76 q3 ∷
   rw 75 q3 ∷
   rw 74 q3 ∷
   rw 73 q3 ∷
   rw 72 q3 ∷
   rw 71 q3 ∷
   rw 70 q3 ∷
   rw 69 q3 ∷
   rw⁻ 68 q4 ∷
   rw 67 q5 ∷
   rw⁻ 66 q4 ∷
   rw⁻ 65 q4 ∷
   rw⁻ 64 q4 ∷
   rw 63 q3 ∷
   rw 62 q3 ∷
   rw 61 q3 ∷
   rw 60 q3 ∷
   rw 59 q3 ∷
   rw 58 q3 ∷
   rw 57 q3 ∷
   rw 56 q3 ∷
   rw 55 q3 ∷
   rw 54 q3 ∷
   rw 53 q3 ∷
   rw 52 q3 ∷
   rw 51 q3 ∷
   rw 50 q3 ∷
   rw 49 q3 ∷
   rw 48 q3 ∷
   rw 47 q3 ∷
   rw 46 q3 ∷
   rw⁻ 45 q6 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q7 ∷
   rw 45 q3 ∷
   rw⁻ 44 q7 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q7 ∷
   rw 44 q3 ∷
   rw⁻ 43 q7 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q7 ∷
   rw 43 q3 ∷
   rw⁻ 42 q7 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q7 ∷
   rw 42 q3 ∷
   rw⁻ 41 q7 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q7 ∷
   rw 41 q3 ∷
   rw⁻ 40 q7 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q7 ∷
   rw 40 q3 ∷
   rw⁻ 39 q7 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw⁻ 38 q8 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q7 ∷
   rw 38 q5 ∷
   rw⁻ 37 q7 ∷
   re 38 3 (CK31 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q7 ∷
   rw 37 q3 ∷
   rw⁻ 36 q7 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q7 ∷
   rw 36 q3 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (CS13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q7 ∷
   rw 35 q3 ∷
   rw⁻ 34 q7 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw⁻ 33 q8 ∷
   re 32 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q7 ∷
   rw 33 q5 ∷
   rw⁻ 32 q7 ∷
   re 33 3 (CK31 ∷ []) ∷
   rw⁻ 31 q8 ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q7 ∷
   rw 31 q5 ∷
   rw⁻ 30 q7 ∷
   re 31 3 (CK31 ∷ []) ∷
   rw⁻ 29 q2 ∷
   rw 30 q9 ∷
   rw 29 q2 ∷
   re 31 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q7 ∷
   rw 31 q10 ∷
   rw 32 q7 ∷
   re 30 3 (CK30 ∷ []) ∷
   rw 31 q8 ∷
   re 33 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 32 q7 ∷
   rw 33 q10 ∷
   rw 34 q7 ∷
   re 32 3 (CK30 ∷ []) ∷
   rw 33 q8 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q7 ∷
   rw 35 q11 ∷
   rw 36 q7 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q7 ∷
   rw 36 q11 ∷
   rw 37 q7 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q7 ∷
   rw 37 q11 ∷
   rw 38 q7 ∷
   re 36 3 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 37 q7 ∷
   rw 38 q10 ∷
   rw 39 q7 ∷
   re 37 3 (CK30 ∷ []) ∷
   rw 38 q8 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q7 ∷
   rw 40 q11 ∷
   rw 41 q7 ∷
   re 39 3 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q7 ∷
   rw 41 q11 ∷
   rw 42 q7 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q7 ∷
   rw 42 q11 ∷
   rw 43 q7 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q7 ∷
   rw 43 q11 ∷
   rw 44 q7 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q7 ∷
   rw 44 q11 ∷
   rw 45 q7 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q7 ∷
   rw 45 q11 ∷
   rw 46 q7 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q2 ∷
   rw 46 q2 ∷
   rw 47 q6 ∷
   rw 48 q2 ∷
   rw 49 q11 ∷
   rw 50 q11 ∷
   rw 51 q11 ∷
   rw 52 q11 ∷
   rw 53 q11 ∷
   rw 54 q11 ∷
   rw 55 q11 ∷
   rw 56 q11 ∷
   rw 57 q11 ∷
   rw 58 q11 ∷
   rw 59 q11 ∷
   rw 60 q11 ∷
   rw 61 q11 ∷
   rw 62 q11 ∷
   rw 63 q11 ∷
   rw 64 q11 ∷
   rw 65 q11 ∷
   rw 66 q11 ∷
   rw 67 q4 ∷
   rw 68 q4 ∷
   rw 69 q4 ∷
   rw 70 q10 ∷
   rw 71 q4 ∷
   rw 72 q11 ∷
   rw 73 q11 ∷
   rw 74 q11 ∷
   rw 75 q11 ∷
   rw 76 q11 ∷
   rw 77 q11 ∷
   rw 78 q11 ∷
   rw 79 q11 ∷
   rw 80 q11 ∷
   rw 81 q4 ∷
   rw 82 q4 ∷
   rw 83 q4 ∷
   rw 84 q10 ∷
   rw 85 q4 ∷
   rw 86 q4 ∷
   rw 87 q4 ∷
   rw 88 q4 ∷
   rw 89 q10 ∷
   rw 90 q4 ∷
   rw 91 q2 ∷
   rw 92 q6 ∷
   rw 93 q2 ∷
   rw 94 q10 ∷
   rw 95 q4 ∷
   rw 96 q10 ∷
   rw 97 q4 ∷
   rw 98 q11 ∷
   rw 99 q11 ∷
   rw 100 q11 ∷
   rw 101 q10 ∷
   rw 102 q4 ∷
   rw 103 q11 ∷
   rw 104 q11 ∷
   rw 105 q11 ∷
   rw 106 q11 ∷
   rw 107 q11 ∷
   rw 108 q11 ∷
   rw 109 q12 ∷
   rw 0 q13 ∷
   rw 80 q1 ∷
   rw 79 q3 ∷
   rw 78 q3 ∷
   rw 77 q3 ∷
   rw 76 q3 ∷
   rw 75 q3 ∷
   rw 74 q3 ∷
   rw⁻ 73 q4 ∷
   rw 72 q5 ∷
   rw 71 q3 ∷
   rw 70 q3 ∷
   rw 69 q3 ∷
   rw⁻ 68 q4 ∷
   rw 67 q5 ∷
   rw⁻ 66 q4 ∷
   rw 65 q5 ∷
   rw⁻ 64 q2 ∷
   rw⁻ 63 q6 ∷
   rw⁻ 62 q2 ∷
   rw⁻ 61 q4 ∷
   rw 60 q5 ∷
   rw⁻ 59 q4 ∷
   rw⁻ 58 q4 ∷
   rw⁻ 57 q4 ∷
   rw⁻ 56 q4 ∷
   rw 55 q5 ∷
   rw⁻ 54 q4 ∷
   rw⁻ 53 q4 ∷
   rw⁻ 52 q4 ∷
   rw 51 q3 ∷
   rw 50 q3 ∷
   rw 49 q3 ∷
   rw 48 q3 ∷
   rw 47 q3 ∷
   rw 46 q3 ∷
   rw 45 q3 ∷
   rw 44 q3 ∷
   rw 43 q3 ∷
   rw⁻ 42 q4 ∷
   rw 41 q5 ∷
   rw⁻ 40 q4 ∷
   rw⁻ 39 q4 ∷
   rw⁻ 38 q4 ∷
   rw 37 q3 ∷
   rw 36 q3 ∷
   rw 35 q3 ∷
   rw 34 q3 ∷
   rw 33 q3 ∷
   rw 32 q3 ∷
   rw 31 q3 ∷
   rw 30 q3 ∷
   rw 29 q3 ∷
   rw 28 q3 ∷
   rw 27 q3 ∷
   rw 26 q3 ∷
   rw 25 q3 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   rw 22 q3 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw⁻ 19 q2 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 17 q2 ∷
   rw⁻ 16 q2 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q7 ∷
   rw 16 q3 ∷
   rw⁻ 15 q7 ∷
   re 16 3 (CS13 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q7 ∷
   rw 15 q3 ∷
   rw⁻ 14 q7 ∷
   re 15 3 (CS13 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q7 ∷
   rw 14 q3 ∷
   rw⁻ 13 q7 ∷
   re 14 3 (CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q7 ∷
   rw 13 q3 ∷
   rw⁻ 12 q7 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q7 ∷
   rw 12 q3 ∷
   rw⁻ 11 q7 ∷
   re 12 3 (CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q7 ∷
   rw 11 q3 ∷
   rw⁻ 10 q7 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 9 q8 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q7 ∷
   rw 9 q5 ∷
   rw⁻ 8 q7 ∷
   re 9 3 (CK31 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q7 ∷
   rw 8 q3 ∷
   rw⁻ 7 q7 ∷
   re 8 3 (CS13 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q7 ∷
   rw 7 q3 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (CS13 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q7 ∷
   rw 6 q3 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 4 q8 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q7 ∷
   rw 4 q5 ∷
   rw⁻ 3 q7 ∷
   re 4 3 (CK31 ∷ []) ∷
   rw⁻ 2 q8 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q7 ∷
   rw 2 q5 ∷
   rw⁻ 1 q7 ∷
   re 2 3 (CK31 ∷ []) ∷
   rw⁻ 0 q2 ∷
   rw 1 q14 ∷
   rw 0 q2 ∷
   re 2 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 1 q7 ∷
   rw 2 q10 ∷
   rw 3 q7 ∷
   re 1 3 (CK30 ∷ []) ∷
   rw 2 q8 ∷
   re 4 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 4 q10 ∷
   rw 5 q7 ∷
   re 3 3 (CK30 ∷ []) ∷
   rw 4 q8 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q11 ∷
   rw 7 q7 ∷
   re 5 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q11 ∷
   rw 8 q7 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q11 ∷
   rw 9 q7 ∷
   re 7 3 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q10 ∷
   rw 10 q7 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q8 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 11 q11 ∷
   rw 12 q7 ∷
   re 10 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q11 ∷
   rw 13 q7 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 13 q11 ∷
   rw 14 q7 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   rw 14 q11 ∷
   rw 15 q7 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   rw 15 q11 ∷
   rw 16 q7 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q7 ∷
   rw 16 q11 ∷
   rw 17 q7 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q6 ∷
   rw 17 q11 ∷
   rw 18 q11 ∷
   rw 19 q11 ∷
   rw 20 q11 ∷
   rw 21 q11 ∷
   rw 22 q11 ∷
   rw 23 q11 ∷
   rw 24 q11 ∷
   rw 25 q11 ∷
   rw 26 q11 ∷
   rw 27 q11 ∷
   rw 28 q11 ∷
   rw 29 q11 ∷
   rw 30 q11 ∷
   rw 31 q11 ∷
   rw 32 q11 ∷
   rw 33 q11 ∷
   rw 34 q11 ∷
   rw 35 q4 ∷
   rw 36 q4 ∷
   rw 37 q4 ∷
   rw 38 q10 ∷
   rw 39 q4 ∷
   rw 40 q11 ∷
   rw 41 q11 ∷
   rw 42 q11 ∷
   rw 43 q11 ∷
   rw 44 q11 ∷
   rw 45 q11 ∷
   rw 46 q11 ∷
   rw 47 q11 ∷
   rw 48 q11 ∷
   rw 49 q4 ∷
   rw 50 q4 ∷
   rw 51 q4 ∷
   rw 52 q10 ∷
   rw 53 q4 ∷
   rw 54 q4 ∷
   rw 55 q4 ∷
   rw 56 q4 ∷
   rw 57 q10 ∷
   rw 58 q4 ∷
   rw 59 q6 ∷
   rw 60 q10 ∷
   rw 61 q4 ∷
   rw 62 q10 ∷
   rw 63 q4 ∷
   rw 64 q11 ∷
   rw 65 q11 ∷
   rw 66 q11 ∷
   rw 67 q10 ∷
   rw 68 q4 ∷
   rw 69 q11 ∷
   rw 70 q11 ∷
   rw 71 q11 ∷
   rw 72 q11 ∷
   rw 73 q11 ∷
   rw 74 q11 ∷
   rw 75 q2 ∷
   rw 76 q12 ∷ []) Eq.refl
