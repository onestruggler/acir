{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D720 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)
open import Examples.Groups.Clifford+CS.Four.D.D369 W using (lem-pass-CCZ123-vs-X3-CK30-X3 ; lem-pass-CCZ123-vs-X3-CKd30-X3 ; lem-pass-CCZ123-vs-X3-CS03-X3 ; lem-pass-CCZ123-vs-X3-CSd03-X3)
open import Examples.Groups.Clifford+CS.Four.D.D510 W using (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D529 W using (lem-pass-X2-CK23-X2-vs-CS01-TOFF123-CSd01-TOFF123 ; lem-pass-X2-CKd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 ; lem-pass-X2-CS23-X2-vs-CS01-TOFF123-CSd01-TOFF123 ; lem-pass-X2-CSd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 ; lem-pass-X3-CK31-X3-vs-CS02-TOFF213-CSd02-TOFF213 ; lem-pass-X3-CK32-X3-vs-CS01-TOFF123-CSd01-TOFF123 ; lem-pass-X3-CKd31-X3-vs-CS02-TOFF213-CSd02-TOFF213 ; lem-pass-X3-CKd32-X3-vs-CS01-TOFF123-CSd01-TOFF123)
open import Examples.Groups.Clifford+CS.Four.D.D541 W using (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D701 W using (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D703 W using (lem-S2-at1023-ᵖ-1 ; lem-S2-at1203-ᵖ-1 ; lem-S2-at2013-ᵖ-1 ; lem-S2-at2103-ᵖ-1)
open import Examples.Groups.Clifford+CS.Four.D.D704 W using (lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2)
open import Examples.Groups.Clifford+CS.Four.D.D705 W using (lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 ; lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 ; lem-pass-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3-vs-CCZ123 ; lem-pass-X1-CK13-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CCZ123 ; lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CCZ123)

private
  q1 : Eqn
  q1 = eqn (X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1660 W)
  q2 : Eqn
  q2 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2)
  q3 : Eqn
  q3 = eqn (X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ []) (wn 1661 W)

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X0 X1 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 29 q1 ∷
   rw 0 q2 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2)

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X0 X1 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X1 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 31 q1 ∷
   rw 0 q4 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q6 : Eqn
  q6 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q7 : Eqn
  q7 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q8 : Eqn
  q8 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q9 : Eqn
  q9 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ []) (S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2059 W)
  q10 : Eqn
  q10 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q11 : Eqn
  q11 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q12 : Eqn
  q12 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q13 : Eqn
  q13 = eqn (X3 ∷ CS03 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q14 : Eqn
  q14 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q15 : Eqn
  q15 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S0 ∷ []) (S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2060 W)

-- pass [X3 CKd30 X3] [Sd0 CS03 TOFF012 CSd03 TOFF012 S0]: 45 steps
lem-pass-X3-CKd30-X3-vs-Sd0-CS03-TOFF012-CSd03-TOFF012-S0 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd0-CS03-TOFF012-CSd03-TOFF012-S0 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw 0 q7 ∷
   rw 1 q9 ∷
   rw⁻ 0 q6 ∷
   rw 1 q10 ∷
   rw 4 q5 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q10 ∷
   rw 4 q10 ∷
   rw 7 q5 ∷
   re 5 3 (CK30⁻ ∷ []) ∷
   rw 6 q10 ∷
   rw 7 q10 ∷
   rw 10 q5 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q10 ∷
   rw 10 q8 ∷
   rw 7 q11 ∷
   rw 4 q12 ∷
   rw 1 q13 ∷
   rw 15 q5 ∷
   rw 14 q14 ∷
   rw 13 q7 ∷
   re 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   rw 11 q7 ∷
   rw 10 q7 ∷
   re 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   rw 8 q7 ∷
   rw 7 q7 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q7 ∷
   rw 6 q15 ∷
   rw⁻ 5 q14 ∷
   rw 6 q10 ∷
   rw 9 q5 ∷
   re 7 3 (CK30⁻ ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q8 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = eqn (CCZ123 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X3-CS03-X3)
  q17 : Eqn
  q17 = eqn (CCZ123 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (X3 ∷ CK30 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X3-CK30-X3)
  q18 : Eqn
  q18 = eqn (CCZ123 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
  q19 : Eqn
  q19 = eqn (CCZ123 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (X3 ∷ CK30⁻ ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X3-CKd30-X3)
  q20 : Eqn
  q20 = eqn (CCZ123 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X3-CSd03-X3)

-- CCZ(3,1,2) passes split Gad(t=0, W=(3,), d=SK, e=-1): 5 steps
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ : ⟪ (CCZ123 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ = derive (CCZ123 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ [])
  (rw 0 q16 ∷
   rw 3 q17 ∷
   rw 6 q18 ∷
   rw 12 q19 ∷
   rw 15 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q22 : Eqn
  q22 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ K0⁻ ∷ []) (K0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 2061 W)
  q23 : Eqn
  q23 = eqn (X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q24 : Eqn
  q24 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q25 : Eqn
  q25 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ K0 ∷ []) (K0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2062 W)

-- pass [X3 CSd30 X3] [Kd0 CS03 TOFF012 CSd03 TOFF012 K0]: 45 steps
lem-pass-X3-CSd30-X3-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ []) (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q5 ∷
   rw 3 q21 ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw 0 q7 ∷
   rw 1 q22 ∷
   rw⁻ 0 q21 ∷
   rw 1 q10 ∷
   rw 4 q5 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q10 ∷
   rw 4 q10 ∷
   rw 7 q5 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q10 ∷
   rw 7 q10 ∷
   rw 10 q5 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q10 ∷
   rw 10 q8 ∷
   rw 7 q13 ∷
   rw 4 q23 ∷
   rw 1 q13 ∷
   rw 15 q5 ∷
   rw 14 q24 ∷
   rw 13 q7 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   rw 11 q7 ∷
   rw 10 q7 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   rw 8 q7 ∷
   rw 7 q7 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q7 ∷
   rw 6 q25 ∷
   rw⁻ 5 q24 ∷
   rw 6 q10 ∷
   rw 9 q5 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q8 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) (lem-S2-at1023-ᵖ-1)
  q27 : Eqn
  q27 = eqn [] (X3 ∷ X3 ∷ []) (wn 225 W)
  q28 : Eqn
  q28 = eqn (CS12 ∷ X3 ∷ []) (X3 ∷ CS12 ∷ []) (low₃-comm ((CS ↑)) (X))
  q29 : Eqn
  q29 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)
  q30 : Eqn
  q30 = eqn (CS12⁻ ∷ X3 ∷ []) (X3 ∷ CS12⁻ ∷ []) (low₃-comm (((CS • CS • CS) ↑)) (X))

-- distribute Gad(t=1, W=(3,), d=1, e=-1) CS12 TOFF103 CSd12 TOFF103: 8 steps
lem-distribute-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 : ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 = derive (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ [])
  (rw 1 q26 ∷
   rw 2 q27 ∷
   rw 5 q27 ∷
   rw 8 q27 ∷
   rw⁻ 0 q28 ∷
   rw 1 q29 ∷
   rw⁻ 4 q30 ∷
   rw 5 q29 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (lem-S2-at1203-ᵖ-1)
  q32 : Eqn
  q32 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-CS01-TOFF123-CSd01-TOFF123)
  q33 : Eqn
  q33 = eqn (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) lem-S2-at1203-ᵖ-1

-- pass [X3 CKd32 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CKd32-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X3 ∷ CK32⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  (rw 3 q31 ∷
   rw 0 q32 ∷
   rw⁻ 0 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = eqn (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CCZ123

-- pass [CCZ123] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (CCZ123 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (CCZ123 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = eqn (X3 ∷ CK32 ∷ X3 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-CS01-TOFF123-CSd01-TOFF123)

-- pass [X3 CK32 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CK32-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X3 ∷ CK32 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  (rw 3 q31 ∷
   rw 0 q35 ∷
   rw⁻ 0 q33 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (X2 ∷ CS23 ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (lem-pass-X2-CS23-X2-vs-CS01-TOFF123-CSd01-TOFF123)

-- pass [X2 CS23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X2 ∷ CS23 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23 ∷ X2 ∷ [])
  (rw 3 q31 ∷
   rw 0 q36 ∷
   rw⁻ 0 q33 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (X2 ∷ CK23 ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (lem-pass-X2-CK23-X2-vs-CS01-TOFF123-CSd01-TOFF123)

-- pass [X2 CK23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X2 ∷ CK23 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23 ∷ X2 ∷ [])
  (rw 3 q31 ∷
   rw 0 q37 ∷
   rw⁻ 0 q33 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = eqn (X2 ∷ CS23⁻ ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-CS01-TOFF123-CSd01-TOFF123)

-- pass [X2 CSd23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X2 ∷ CS23⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ [])
  (rw 3 q31 ∷
   rw 0 q38 ∷
   rw⁻ 0 q33 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (X2 ∷ CK23⁻ ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-CS01-TOFF123-CSd01-TOFF123)

-- pass [X2 CKd23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X2 ∷ CK23⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  (rw 3 q31 ∷
   rw 0 q39 ∷
   rw⁻ 0 q33 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = eqn (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) (lem-S2-at2013-ᵖ-1)

-- distribute Gad(t=2, W=(3,), d=1, e=-1) CS12 TOFF203 CSd12 TOFF203: 8 steps
lem-distribute-Gad⟨t≡2-W≡⟨3⟩-d≡1-e≡-1⟩-CS12-TOFF203-CSd12-TOFF203 : ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ Toff203 ∷ X3 ∷ CS12⁻ ∷ X3 ∷ Toff203 ∷ X3 ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡2-W≡⟨3⟩-d≡1-e≡-1⟩-CS12-TOFF203-CSd12-TOFF203 = derive (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (CS12 ∷ X3 ∷ Toff203 ∷ X3 ∷ CS12⁻ ∷ X3 ∷ Toff203 ∷ X3 ∷ [])
  (rw 1 q40 ∷
   rw 2 q27 ∷
   rw 5 q27 ∷
   rw 8 q27 ∷
   rw⁻ 0 q28 ∷
   rw 1 q29 ∷
   rw⁻ 4 q30 ∷
   rw 5 q29 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = eqn (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) (lem-S2-at2103-ᵖ-1)
  q42 : Eqn
  q42 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-CS02-TOFF213-CSd02-TOFF213)
  q43 : Eqn
  q43 = eqn (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) lem-S2-at2103-ᵖ-1

-- pass [X3 CKd31 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CKd31-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 3 q41 ∷
   rw 0 q42 ∷
   rw⁻ 0 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = eqn (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CCZ123

-- pass [CCZ123] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (CCZ123 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = derive (CCZ123 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = eqn (X3 ∷ CK31 ∷ X3 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-CS02-TOFF213-CSd02-TOFF213)

-- pass [X3 CK31 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CK31-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (X3 ∷ CK31 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 3 q41 ∷
   rw 0 q45 ∷
   rw⁻ 0 q43 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q47 : Eqn
  q47 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1681 W)
  q48 : Eqn
  q48 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q49 : Eqn
  q49 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q50 : Eqn
  q50 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q51 : Eqn
  q51 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q52 : Eqn
  q52 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q53 : Eqn
  q53 = eqn (X3 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (wn 2063 W)
  q54 : Eqn
  q54 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q55 : Eqn
  q55 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q56 : Eqn
  q56 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1482 W)

-- pass [X3 CSd30 X3] [X1 X2 CS03 TOFF012 CSd03 TOFF012 X1 X2]: 87 steps
lem-pass-X3-CSd30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q5 ∷
   rw 3 q46 ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw 0 q7 ∷
   rw 1 q47 ∷
   rw⁻ 0 q46 ∷
   rw 1 q10 ∷
   rw 4 q5 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q10 ∷
   rw 4 q8 ∷
   rw 5 q48 ∷
   rw⁻ 4 q49 ∷
   rw⁻ 3 q50 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q51 ∷
   rw 3 q52 ∷
   rw⁻ 2 q51 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 1 q50 ∷
   rw 2 q53 ∷
   rw 1 q49 ∷
   rw 2 q50 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q51 ∷
   rw 4 q54 ∷
   rw 5 q51 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q50 ∷
   rw 5 q55 ∷
   rw 5 q5 ∷
   rw 4 q7 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw 2 q7 ∷
   rw 3 q56 ∷
   rw 2 q10 ∷
   rw 5 q5 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q10 ∷
   rw 5 q8 ∷
   rw 2 q11 ∷
   rw 9 q5 ∷
   rw 8 q7 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 6 q7 ∷
   rw 7 q56 ∷
   rw 6 q10 ∷
   rw 9 q5 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q8 ∷
   rw 10 q5 ∷
   rw 9 q46 ∷
   rw 8 q7 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 6 q7 ∷
   rw 7 q47 ∷
   rw⁻ 6 q46 ∷
   rw 7 q10 ∷
   rw 10 q5 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q10 ∷
   rw 10 q8 ∷
   rw 11 q48 ∷
   rw⁻ 10 q49 ∷
   rw⁻ 9 q50 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q51 ∷
   rw 9 q52 ∷
   rw⁻ 8 q51 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q50 ∷
   rw 8 q53 ∷
   rw 7 q49 ∷
   rw 8 q50 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q51 ∷
   rw 10 q54 ∷
   rw 11 q51 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q50 ∷
   rw 11 q55 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (X2 ∷ CS02 ∷ X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1682 W)
  q58 : Eqn
  q58 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q59 : Eqn
  q59 = eqn (X3 ∷ CS13 ∷ X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (wn 2064 W)
  q60 : Eqn
  q60 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q61 : Eqn
  q61 = eqn (X2 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ []) (wn 1490 W)

-- pass [X3 CS30 X3] [X1 X2 CS03 TOFF012 CSd03 TOFF012 X1 X2]: 87 steps
lem-pass-X3-CS30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 = derive (X3 ∷ CS03 ∷ X3 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 4 q5 ∷
   rw 3 q46 ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw 0 q7 ∷
   rw 1 q57 ∷
   rw⁻ 0 q46 ∷
   rw 1 q10 ∷
   rw 4 q5 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q10 ∷
   rw 4 q8 ∷
   rw 5 q48 ∷
   rw⁻ 4 q49 ∷
   rw⁻ 3 q50 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q51 ∷
   rw 3 q58 ∷
   rw⁻ 2 q51 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 1 q50 ∷
   rw 2 q59 ∷
   rw 1 q49 ∷
   rw 2 q50 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q51 ∷
   rw 4 q60 ∷
   rw 5 q51 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q50 ∷
   rw 5 q55 ∷
   rw 5 q5 ∷
   rw 4 q7 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw 2 q7 ∷
   rw 3 q61 ∷
   rw 2 q10 ∷
   rw 5 q5 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q10 ∷
   rw 5 q8 ∷
   rw 2 q13 ∷
   rw 9 q5 ∷
   rw 8 q7 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 6 q7 ∷
   rw 7 q61 ∷
   rw 6 q10 ∷
   rw 9 q5 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q8 ∷
   rw 10 q5 ∷
   rw 9 q46 ∷
   rw 8 q7 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 6 q7 ∷
   rw 7 q57 ∷
   rw⁻ 6 q46 ∷
   rw 7 q10 ∷
   rw 10 q5 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q10 ∷
   rw 10 q8 ∷
   rw 11 q48 ∷
   rw⁻ 10 q49 ∷
   rw⁻ 9 q50 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q51 ∷
   rw 9 q58 ∷
   rw⁻ 8 q51 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 7 q50 ∷
   rw 8 q59 ∷
   rw 7 q49 ∷
   rw 8 q50 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q51 ∷
   rw 10 q60 ∷
   rw 11 q51 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q50 ∷
   rw 11 q55 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (X1 ∷ CK13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ []) (wn 2065 W)
  q63 : Eqn
  q63 = eqn (X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ []) (wn 2144 W)
  q64 : Eqn
  q64 = eqn (X1 ∷ CS13 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13 ∷ X1 ∷ []) (lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012)
  q65 : Eqn
  q65 = eqn (X1 ∷ CK13 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (lem-pass-X1-CK13-X1-vs-CS03-TOFF012-CSd03-TOFF012)
  q66 : Eqn
  q66 = eqn (X1 ∷ CS13⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012)
  q67 : Eqn
  q67 = eqn (X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ []) (wn 2145 W)
  q68 : Eqn
  q68 = eqn (X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (wn 2067 W)

-- pass [X1 CKd13 X1] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 101 steps
lem-pass-X1-CKd13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (X1 ∷ CK13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  (rw 0 q62 ∷
   rw 19 q5 ∷
   rw 18 q24 ∷
   rw 17 q14 ∷
   rw 16 q46 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q8 ∷
   rw 14 q46 ∷
   rw 13 q46 ∷
   re 12 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   rw 11 q46 ∷
   rw 10 q46 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   rw 8 q46 ∷
   rw 7 q46 ∷
   re 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q46 ∷
   rw 4 q46 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw 2 q46 ∷
   rw 3 q63 ∷
   rw⁻ 2 q14 ∷
   rw⁻ 3 q24 ∷
   rw⁻ 4 q46 ∷
   rw 7 q5 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q46 ∷
   rw⁻ 7 q46 ∷
   rw 10 q5 ∷
   re 8 3 (CK13 ∷ []) ∷
   rw⁻ 9 q46 ∷
   rw⁻ 10 q46 ∷
   rw 13 q5 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q46 ∷
   rw⁻ 13 q46 ∷
   rw 16 q5 ∷
   re 14 3 (CK13 ∷ []) ∷
   rw⁻ 15 q46 ∷
   rw⁻ 16 q46 ∷
   rw 19 q5 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 18 q46 ∷
   rw 19 q8 ∷
   rw 16 q64 ∷
   rw 13 q65 ∷
   rw 10 q66 ∷
   rw 7 q65 ∷
   rw 4 q64 ∷
   rw 25 q5 ∷
   rw 24 q6 ∷
   rw 23 q21 ∷
   rw 22 q46 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q8 ∷
   rw 20 q46 ∷
   rw 19 q46 ∷
   re 18 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 20 q8 ∷
   rw 17 q46 ∷
   rw 16 q46 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q8 ∷
   rw 14 q46 ∷
   rw 13 q46 ∷
   re 12 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   rw 11 q46 ∷
   rw 10 q46 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   rw 8 q46 ∷
   rw 9 q67 ∷
   rw⁻ 8 q21 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q46 ∷
   rw 13 q5 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q46 ∷
   rw⁻ 13 q46 ∷
   rw 16 q5 ∷
   re 14 3 (CK13 ∷ []) ∷
   rw⁻ 15 q46 ∷
   rw⁻ 16 q46 ∷
   rw 19 q5 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw⁻ 18 q46 ∷
   rw⁻ 19 q46 ∷
   rw 22 q5 ∷
   re 20 3 (CK13 ∷ []) ∷
   rw⁻ 21 q46 ∷
   rw⁻ 22 q46 ∷
   rw 25 q5 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw⁻ 24 q46 ∷
   rw 25 q8 ∷
   rw 10 q68 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = eqn (X1 ∷ CK13 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (wn 2068 W)
  q70 : Eqn
  q70 = eqn (X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ []) (wn 2146 W)
  q71 : Eqn
  q71 = eqn (X1 ∷ CK13⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012)
  q72 : Eqn
  q72 = eqn (X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ []) (wn 2147 W)
  q73 : Eqn
  q73 = eqn (X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (wn 2070 W)

-- pass [X1 CK13 X1] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 101 steps
lem-pass-X1-CK13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (X1 ∷ CK13 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  (rw 0 q69 ∷
   rw 19 q5 ∷
   rw 18 q24 ∷
   rw 17 q14 ∷
   rw 16 q46 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q8 ∷
   rw 14 q46 ∷
   rw 13 q46 ∷
   re 12 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   rw 11 q46 ∷
   rw 10 q46 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   rw 8 q46 ∷
   rw 7 q46 ∷
   re 6 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q46 ∷
   rw 4 q46 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw 2 q46 ∷
   rw 3 q70 ∷
   rw⁻ 2 q14 ∷
   rw⁻ 3 q24 ∷
   rw⁻ 4 q46 ∷
   rw 7 q5 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q46 ∷
   rw⁻ 7 q46 ∷
   rw 10 q5 ∷
   re 8 3 (CK13⁻ ∷ []) ∷
   rw⁻ 9 q46 ∷
   rw⁻ 10 q46 ∷
   rw 13 q5 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q46 ∷
   rw⁻ 13 q46 ∷
   rw 16 q5 ∷
   re 14 3 (CK13⁻ ∷ []) ∷
   rw⁻ 15 q46 ∷
   rw⁻ 16 q46 ∷
   rw 19 q5 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw⁻ 18 q46 ∷
   rw 19 q8 ∷
   rw 16 q66 ∷
   rw 13 q71 ∷
   rw 10 q64 ∷
   rw 7 q71 ∷
   rw 4 q66 ∷
   rw 25 q5 ∷
   rw 24 q6 ∷
   rw 23 q21 ∷
   rw 22 q46 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q8 ∷
   rw 20 q46 ∷
   rw 19 q46 ∷
   re 18 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q8 ∷
   rw 17 q46 ∷
   rw 16 q46 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q8 ∷
   rw 14 q46 ∷
   rw 13 q46 ∷
   re 12 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   rw 11 q46 ∷
   rw 10 q46 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   rw 8 q46 ∷
   rw 9 q72 ∷
   rw⁻ 8 q21 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q46 ∷
   rw 13 q5 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q46 ∷
   rw⁻ 13 q46 ∷
   rw 16 q5 ∷
   re 14 3 (CK13⁻ ∷ []) ∷
   rw⁻ 15 q46 ∷
   rw⁻ 16 q46 ∷
   rw 19 q5 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 18 q46 ∷
   rw⁻ 19 q46 ∷
   rw 22 q5 ∷
   re 20 3 (CK13⁻ ∷ []) ∷
   rw⁻ 21 q46 ∷
   rw⁻ 22 q46 ∷
   rw 25 q5 ∷
   re 23 3 (CS13⁻ ∷ []) ∷
   rw⁻ 24 q46 ∷
   rw 25 q8 ∷
   rw 10 q73 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = eqn [] (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) (wn 2071 W)
  q75 : Eqn
  q75 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q76 : Eqn
  q76 = eqn (X0 ∷ CS12 ∷ []) (CS12 ∷ X0 ∷ []) (low₁-comm (X) (CS))
  q77 : Eqn
  q77 = eqn (X0 ∷ X0 ∷ []) [] (wn 387 W)
  q78 : Eqn
  q78 = eqn (X0 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X0 ∷ []) (low₁-comm (X) ((CS • CS • CS)))

-- distribute Gad(t=1, W=(0, 3), d=1, e=-1) CS12 TOFF103 CSd12 TOFF103: 14 steps
lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 : ⟪ (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 = derive (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) (CS12 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ [])
  (rw 2 q26 ∷
   rw 3 q74 ∷
   rw 8 q74 ∷
   rw 13 q74 ∷
   rw 0 q75 ∷
   rw 1 q76 ∷
   rw 2 q77 ∷
   rw⁻ 0 q28 ∷
   rw 1 q29 ∷
   rw 6 q75 ∷
   rw 7 q78 ∷
   rw 8 q77 ∷
   rw⁻ 6 q30 ∷
   rw 7 q29 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = eqn (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) lem-pass-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3-vs-CCZ123

-- pass [CCZ123] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 1 steps
lem-pass-CCZ123-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (CCZ123 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (CCZ123 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q79 ∷ []) Eq.refl
