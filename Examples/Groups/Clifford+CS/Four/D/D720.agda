{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D720 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00007 ; wn00027 ; wn00029 ; wn00031 ; wn00076 ; wn00173 ; wn00175)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00225 ; wn00387 ; wn00390)
open import Examples.Groups.Clifford+CS.Four.Wins.W28 using (wn01482 ; wn01490)
open import Examples.Groups.Clifford+CS.Four.Wins.W34 using (wn01660 ; wn01661 ; wn01681 ; wn01682)
open import Examples.Groups.Clifford+CS.Four.Wins.W43 using (wn02059 ; wn02060 ; wn02061 ; wn02062 ; wn02063 ; wn02064 ; wn02065 ; wn02067 ; wn02068 ; wn02070 ; wn02071)
open import Examples.Groups.Clifford+CS.Four.Wins.W44 using (wn02144 ; wn02145 ; wn02146 ; wn02147)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)
open import Examples.Groups.Clifford+CS.Four.D.D369 using (lem-pass-CCZ123-vs-X3-CK30-X3 ; lem-pass-CCZ123-vs-X3-CKd30-X3 ; lem-pass-CCZ123-vs-X3-CS03-X3 ; lem-pass-CCZ123-vs-X3-CSd03-X3)
open import Examples.Groups.Clifford+CS.Four.D.D510 using (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D529 using (lem-pass-X2-CK23-X2-vs-CS01-TOFF123-CSd01-TOFF123 ; lem-pass-X2-CKd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 ; lem-pass-X2-CS23-X2-vs-CS01-TOFF123-CSd01-TOFF123 ; lem-pass-X2-CSd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 ; lem-pass-X3-CK31-X3-vs-CS02-TOFF213-CSd02-TOFF213 ; lem-pass-X3-CK32-X3-vs-CS01-TOFF123-CSd01-TOFF123 ; lem-pass-X3-CKd31-X3-vs-CS02-TOFF213-CSd02-TOFF213 ; lem-pass-X3-CKd32-X3-vs-CS01-TOFF123-CSd01-TOFF123)
open import Examples.Groups.Clifford+CS.Four.D.D541 using (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D701 using (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D703 using (lem-S2-at1023-ᵖ-1 ; lem-S2-at1203-ᵖ-1 ; lem-S2-at2013-ᵖ-1 ; lem-S2-at2103-ᵖ-1)
open import Examples.Groups.Clifford+CS.Four.D.D704 using (lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2)
open import Examples.Groups.Clifford+CS.Four.D.D705 using (lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 ; lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 ; lem-pass-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3-vs-CCZ123 ; lem-pass-X1-CK13-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CCZ123 ; lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CCZ123)

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X0 X1 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = run b0
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  b0 = at 29 35 (X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ []) wn01660 ▸
       at 0 123 (X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2) ▸
       at 0 94 (X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ []) wn01661 ▸ done

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X0 X1 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = run b0
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  b0 = at 31 35 (X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ []) wn01660 ▸
       at 0 125 (X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2) ▸
       at 0 94 (X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ []) wn01661 ▸ done

-- pass [X3 CKd30 X3] [Sd0 CS03 TOFF012 CSd03 TOFF012 S0]: 45 steps
lem-pass-X3-CKd30-X3-vs-Sd0-CS03-TOFF012-CSd03-TOFF012-S0 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd0-CS03-TOFF012-CSd03-TOFF012-S0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (S0⁻ ∷ Sw23 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 4 (S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) wn02059 ▸
       at 0 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸ done

  b1 : Chain (S0⁻ ∷ Sw23 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (S0⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ [])
  b1 = at 1 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸ done

  b2 : Chain (S0⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ S0 ∷ [])
  b2 = at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 2 [] wn00003 ▸
       at 7 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

  b3 : Chain (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ S0 ∷ []) (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S0 ∷ Sw23 ∷ [])
  b3 = at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 13 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 10 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ Sw23 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ [])
  b4 = at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 7 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 6 10 (S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) wn02060 ▸
       at 5 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸ done

  b5 : Chain (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ Sw23 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ []) (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b5 = at 6 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 9 2 [] wn00003 ▸ done

-- CCZ(3,1,2) passes split Gad(t=0, W=(3,), d=SK, e=-1): 5 steps
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ : ⟪ (CCZ123 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ = run b0
  where
  b0 : Chain (CCZ123 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 4 (X3 ∷ CS03 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X3-CS03-X3) ▸
       at 3 4 (X3 ∷ CK30 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X3-CK30-X3) ▸
       at 6 7 (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3) ▸
       at 12 4 (X3 ∷ CK30⁻ ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X3-CKd30-X3) ▸
       at 15 4 (X3 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X3-CSd03-X3) ▸ done

-- pass [X3 CSd30 X3] [Kd0 CS03 TOFF012 CSd03 TOFF012 K0]: 45 steps
lem-pass-X3-CSd30-X3-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ []) (K0⁻ ∷ Sw23 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 4 (K0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn02061 ▸
       at 0 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸ done

  b1 : Chain (K0⁻ ∷ Sw23 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ []) (K0⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ [])
  b1 = at 1 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸ done

  b2 : Chain (K0⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ []) (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ K0 ∷ [])
  b2 = at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 2 [] wn00003 ▸
       at 7 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

  b3 : Chain (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ K0 ∷ []) (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ K0 ∷ Sw23 ∷ [])
  b3 = at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 13 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 10 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ K0 ∷ Sw23 ∷ []) (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ [])
  b4 = at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 7 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 6 10 (K0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) wn02062 ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b5 : Chain (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ []) (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  b5 = at 6 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 9 2 [] wn00003 ▸ done

-- distribute Gad(t=1, W=(3,), d=1, e=-1) CS12 TOFF103 CSd12 TOFF103: 8 steps
lem-distribute-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 : ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 = run b0
  where
  b0 : Chain (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ [])
  b0 = at 1 4 (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) (lem-S2-at1023-ᵖ-1) ▸
       at 2 0 (X3 ∷ X3 ∷ []) wn00225 ▸
       at 5 0 (X3 ∷ X3 ∷ []) wn00225 ▸
       at 8 0 (X3 ∷ X3 ∷ []) wn00225 ▸
       at 0 2 (CS12 ∷ X3 ∷ []) (sym (low₃-comm ((CS ↑)) (X))) ▸
       at 1 2 [] wn00390 ▸
       at 4 2 (CS12⁻ ∷ X3 ∷ []) (sym (low₃-comm (((CS • CS • CS) ↑)) (X))) ▸
       at 5 2 [] wn00390 ▸ done

-- pass [X3 CKd32 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CKd32-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (X3 ∷ CK32⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (lem-S2-at1203-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-CS01-TOFF123-CSd01-TOFF123) ▸
       at 0 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1203-ᵖ-1) ▸ done

-- pass [CCZ123] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (CCZ123 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 7 (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CCZ123 ∷ []) (sym lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CCZ123) ▸ done

-- pass [X3 CK32 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CK32-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (X3 ∷ CK32 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (lem-S2-at1203-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-CS01-TOFF123-CSd01-TOFF123) ▸
       at 0 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1203-ᵖ-1) ▸ done

-- pass [X2 CS23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (X2 ∷ CS23 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23 ∷ X2 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (lem-S2-at1203-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (lem-pass-X2-CS23-X2-vs-CS01-TOFF123-CSd01-TOFF123) ▸
       at 0 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1203-ᵖ-1) ▸ done

-- pass [X2 CK23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (X2 ∷ CK23 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23 ∷ X2 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (lem-S2-at1203-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (lem-pass-X2-CK23-X2-vs-CS01-TOFF123-CSd01-TOFF123) ▸
       at 0 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1203-ᵖ-1) ▸ done

-- pass [X2 CSd23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (X2 ∷ CS23⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (lem-S2-at1203-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-CS01-TOFF123-CSd01-TOFF123) ▸
       at 0 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1203-ᵖ-1) ▸ done

-- pass [X2 CKd23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (lem-S2-at1203-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-CS01-TOFF123-CSd01-TOFF123) ▸
       at 0 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1203-ᵖ-1) ▸ done

-- distribute Gad(t=2, W=(3,), d=1, e=-1) CS12 TOFF203 CSd12 TOFF203: 8 steps
lem-distribute-Gad⟨t≡2-W≡⟨3⟩-d≡1-e≡-1⟩-CS12-TOFF203-CSd12-TOFF203 : ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ Toff203 ∷ X3 ∷ CS12⁻ ∷ X3 ∷ Toff203 ∷ X3 ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡2-W≡⟨3⟩-d≡1-e≡-1⟩-CS12-TOFF203-CSd12-TOFF203 = run b0
  where
  b0 : Chain (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (CS12 ∷ X3 ∷ Toff203 ∷ X3 ∷ CS12⁻ ∷ X3 ∷ Toff203 ∷ X3 ∷ [])
  b0 = at 1 4 (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) (lem-S2-at2013-ᵖ-1) ▸
       at 2 0 (X3 ∷ X3 ∷ []) wn00225 ▸
       at 5 0 (X3 ∷ X3 ∷ []) wn00225 ▸
       at 8 0 (X3 ∷ X3 ∷ []) wn00225 ▸
       at 0 2 (CS12 ∷ X3 ∷ []) (sym (low₃-comm ((CS ↑)) (X))) ▸
       at 1 2 [] wn00390 ▸
       at 4 2 (CS12⁻ ∷ X3 ∷ []) (sym (low₃-comm (((CS • CS • CS) ↑)) (X))) ▸
       at 5 2 [] wn00390 ▸ done

-- pass [X3 CKd31 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CKd31-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-CS23-TOFF201-CSd23-TOFF201 = run b0
  where
  b0 : Chain (X3 ∷ CK31⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  b0 = at 3 4 (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) (lem-S2-at2103-ᵖ-1) ▸
       at 0 7 (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-CS02-TOFF213-CSd02-TOFF213) ▸
       at 0 4 (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-S2-at2103-ᵖ-1) ▸ done

-- pass [CCZ123] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (CCZ123 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 7 (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CCZ123 ∷ []) (sym lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CCZ123) ▸ done

-- pass [X3 CK31 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CK31-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-CS23-TOFF201-CSd23-TOFF201 = run b0
  where
  b0 : Chain (X3 ∷ CK31 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  b0 = at 3 4 (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) (lem-S2-at2103-ᵖ-1) ▸
       at 0 7 (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-CS02-TOFF213-CSd02-TOFF213) ▸
       at 0 4 (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-S2-at2103-ᵖ-1) ▸ done

-- pass [X3 CSd30 X3] [X1 X2 CS03 TOFF012 CSd03 TOFF012 X1 X2]: 87 steps
lem-pass-X3-CSd30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 4 (X1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) wn01681 ▸
       at 0 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b1 : Chain (X1 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X3 ∷ CS03⁻ ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ [])
  b1 = at 1 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 2 [] wn00003 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 3 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸ done

  b2 : Chain (X1 ∷ X3 ∷ CS03⁻ ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Sw01 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ [])
  b2 = at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 2 4 (X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) wn02063 ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b3 : Chain (X1 ∷ X2 ∷ Sw01 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ [])
  b3 = at 2 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 5 2 [] wn00031 ▸ done

  b4 : Chain (X1 ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ [])
  b4 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 3 3 (X2 ∷ CS02⁻ ∷ X2 ∷ []) wn01482 ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b5 : Chain (X1 ∷ X2 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ X1 ∷ X2 ∷ [])
  b5 = at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 5 2 [] wn00003 ▸
       at 2 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸ done

  b6 : Chain (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ [])
  b6 = at 6 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 7 3 (X2 ∷ CS02⁻ ∷ X2 ∷ []) wn01482 ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 9 2 [] wn00003 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b7 : Chain (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ X2 ∷ [])
  b7 = at 9 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 7 4 (X1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) wn01681 ▸
       at 6 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸ done

  b8 : Chain (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ X2 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ [])
  b8 = at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 2 [] wn00003 ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 10 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 9 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ [])
  b9 = at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 8 4 (X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) wn02063 ▸
       at 7 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 8 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸ done

  b10 : Chain (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  b10 = at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 11 2 [] wn00031 ▸ done

-- pass [X3 CS30 X3] [X1 X2 CS03 TOFF012 CSd03 TOFF012 X1 X2]: 87 steps
lem-pass-X3-CS30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (X3 ∷ CS03 ∷ X3 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ Sw23 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 4 (X1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn01682 ▸
       at 0 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b1 : Chain (X1 ∷ Sw23 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X3 ∷ CS03 ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ [])
  b1 = at 1 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 2 [] wn00003 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 3 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸ done

  b2 : Chain (X1 ∷ X3 ∷ CS03 ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Sw01 ∷ X3 ∷ CS13 ∷ X3 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ [])
  b2 = at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 2 4 (X2 ∷ X3 ∷ CS13 ∷ X3 ∷ []) wn02064 ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b3 : Chain (X1 ∷ X2 ∷ Sw01 ∷ X3 ∷ CS13 ∷ X3 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ [])
  b3 = at 2 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 5 2 [] wn00031 ▸ done

  b4 : Chain (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ [])
  b4 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 3 3 (X2 ∷ CS02 ∷ X2 ∷ []) wn01490 ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b5 : Chain (X1 ∷ X2 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ Sw23 ∷ X1 ∷ X2 ∷ [])
  b5 = at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 5 2 [] wn00003 ▸
       at 2 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸ done

  b6 : Chain (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ Sw23 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ [])
  b6 = at 6 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 7 3 (X2 ∷ CS02 ∷ X2 ∷ []) wn01490 ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 9 2 [] wn00003 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b7 : Chain (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ Sw23 ∷ X2 ∷ [])
  b7 = at 9 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 7 4 (X1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn01682 ▸
       at 6 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸ done

  b8 : Chain (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ Sw23 ∷ X2 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ [])
  b8 = at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 2 [] wn00003 ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 10 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 9 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ CS13 ∷ X3 ∷ Sw01 ∷ [])
  b9 = at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 8 4 (X2 ∷ X3 ∷ CS13 ∷ X3 ∷ []) wn02064 ▸
       at 7 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 8 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸ done

  b10 : Chain (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ CS13 ∷ X3 ∷ Sw01 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  b10 = at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 11 2 [] wn00031 ▸ done

-- pass [X1 CKd13 X1] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 101 steps
lem-pass-X1-CKd13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 5 (X2 ∷ X3 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ []) wn02065 ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 18 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 17 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 16 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] wn00003 ▸
       at 14 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b1 = at 13 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 12 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 10 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b2 : Chain (X2 ∷ X3 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b2 = at 7 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b3 : Chain (X2 ∷ X3 ∷ Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ Sw23 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b3 = at 3 17 (S0 ∷ K0 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ []) wn02144 ▸
       at 2 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 7 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b4 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ Sw23 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b4 = at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 10 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 13 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b5 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b5 = at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 16 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 17 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 19 2 [] wn00003 ▸ done

  b6 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b6 = at 16 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13 ∷ X1 ∷ []) (lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 13 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (lem-pass-X1-CK13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 10 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (lem-pass-X1-CK13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13 ∷ X1 ∷ []) (lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 25 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 24 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 23 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸ done

  b7 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b7 = at 22 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] wn00003 ▸
       at 20 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 19 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 18 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] wn00003 ▸
       at 17 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b8 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13 ∷ X1 ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b8 = at 16 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] wn00003 ▸
       at 14 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 13 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 12 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b9 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13 ∷ X1 ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ Sw23 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b9 = at 10 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 9 17 (K0⁻ ∷ S0⁻ ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ []) wn02145 ▸
       at 8 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 9 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 10 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b10 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ Sw23 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ Sw23 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b10 = at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 13 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 16 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b11 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ Sw23 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ Sw23 ∷ CS12 ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b11 = at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 17 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 19 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 20 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 22 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b12 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ Sw23 ∷ CS12 ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  b12 = at 25 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 23 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 25 2 [] wn00003 ▸
       at 10 17 (X2 ∷ X3 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) wn02067 ▸ done

-- pass [X1 CK13 X1] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 101 steps
lem-pass-X1-CK13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (X1 ∷ CK13 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 5 (X2 ∷ X3 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) wn02068 ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 18 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 17 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 16 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] wn00003 ▸
       at 14 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b1 = at 13 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 12 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 10 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b2 : Chain (X2 ∷ X3 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b2 = at 7 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 6 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b3 : Chain (X2 ∷ X3 ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b3 = at 3 17 (S0 ∷ K0 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ []) wn02146 ▸
       at 2 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 7 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b4 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ Sw23 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b4 = at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 10 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 13 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b5 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ Sw23 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b5 = at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 16 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 17 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 19 2 [] wn00003 ▸ done

  b6 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b6 = at 16 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 13 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 10 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13 ∷ X1 ∷ []) (lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 25 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 24 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 23 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸ done

  b7 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b7 = at 22 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] wn00003 ▸
       at 20 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 19 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 18 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] wn00003 ▸
       at 17 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b8 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b8 = at 16 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] wn00003 ▸
       at 14 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 13 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 12 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b9 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ Sw23 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b9 = at 10 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 9 17 (K0⁻ ∷ S0⁻ ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ []) wn02147 ▸
       at 8 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 9 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 10 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b10 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ Sw23 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b10 = at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 13 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 16 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b11 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b11 = at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 17 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 19 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 20 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 22 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b12 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  b12 = at 25 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 23 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 25 2 [] wn00003 ▸
       at 10 17 (X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ []) wn02070 ▸ done

-- distribute Gad(t=1, W=(0, 3), d=1, e=-1) CS12 TOFF103 CSd12 TOFF103: 14 steps
lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 : ⟪ (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) (CS12 ∷ X3 ∷ X3 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ [])
  b0 = at 2 4 (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) (lem-S2-at1023-ᵖ-1) ▸
       at 3 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) wn02071 ▸
       at 8 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) wn02071 ▸
       at 13 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) wn02071 ▸
       at 0 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 1 2 (CS12 ∷ X0 ∷ []) (low₁-comm (X) (CS)) ▸
       at 2 2 [] wn00387 ▸
       at 0 2 (CS12 ∷ X3 ∷ []) (sym (low₃-comm ((CS ↑)) (X))) ▸ done

  b1 : Chain (CS12 ∷ X3 ∷ X3 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ []) (CS12 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ [])
  b1 = at 1 2 [] wn00390 ▸
       at 6 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 7 2 (CS12⁻ ∷ X0 ∷ []) (low₁-comm (X) ((CS • CS • CS))) ▸
       at 8 2 [] wn00387 ▸
       at 6 2 (CS12⁻ ∷ X3 ∷ []) (sym (low₃-comm (((CS • CS • CS) ↑)) (X))) ▸
       at 7 2 [] wn00390 ▸ done

-- pass [CCZ123] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 1 steps
lem-pass-CCZ123-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (CCZ123 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 9 (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) (sym lem-pass-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3-vs-CCZ123) ▸ done
