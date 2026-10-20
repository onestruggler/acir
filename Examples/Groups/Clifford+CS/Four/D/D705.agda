{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D705 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D010 W using (lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D372 W using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D373 W using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D374 W using (lem-pass-CCZ123-vs-X2-CK21-X2 ; lem-pass-CCZ123-vs-X2-CKd21-X2 ; lem-pass-CCZ123-vs-X2-CS12-X2 ; lem-pass-CCZ123-vs-X2-CSd12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D375 W using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D376 W using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D380 W using (lem-pass-CCZ123-vs-X1-CK10-X1 ; lem-pass-CCZ123-vs-X1-CKd10-X1 ; lem-pass-CCZ123-vs-X1-CS01-X1 ; lem-pass-CCZ123-vs-X1-CSd01-X1)
open import Examples.Groups.Clifford+CS.Four.D.D385 W using (lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D510 W using (lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D525 W using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-CS12-CS12-CKd21-X2 ; lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-CKd21-CS12-CS12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D529 W using (lem-pass-X1-CK13-X1-vs-CS02-TOFF013-CSd02-TOFF013 ; lem-pass-X1-CKd13-X1-vs-CS02-TOFF013-CSd02-TOFF013 ; lem-pass-X1-CS13-X1-vs-CS02-TOFF013-CSd02-TOFF013 ; lem-pass-X1-CSd13-X1-vs-CS02-TOFF013-CSd02-TOFF013 ; lem-pass-X2-CK23-X2-vs-TOFF123-CS01-TOFF123-CSd01 ; lem-pass-X2-CKd23-X2-vs-TOFF123-CS01-TOFF123-CSd01 ; lem-pass-X2-CS23-X2-vs-TOFF123-CS01-TOFF123-CSd01 ; lem-pass-X2-CSd23-X2-vs-TOFF123-CS01-TOFF123-CSd01 ; lem-pass-X3-CK31-X3-vs-TOFF213-CS02-TOFF213-CSd02 ; lem-pass-X3-CK32-X3-vs-TOFF123-CS01-TOFF123-CSd01 ; lem-pass-X3-CKd31-X3-vs-TOFF213-CS02-TOFF213-CSd02 ; lem-pass-X3-CKd32-X3-vs-TOFF123-CS01-TOFF123-CSd01)
open import Examples.Groups.Clifford+CS.Four.D.D677 W using (lem-S2-at1023)
open import Examples.Groups.Clifford+CS.Four.D.D678 W using (lem-S2-at1203 ; lem-S2-at2013)
open import Examples.Groups.Clifford+CS.Four.D.D679 W using (lem-S2-at2103)
open import Examples.Groups.Clifford+CS.Four.D.D681 W using (lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D682 W using (lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D683 W using (lem-S2-ᵖ-1)
open import Examples.Groups.Clifford+CS.Four.D.D696 W using (lem-pass-CCZ123-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 ; lem-pass-CCZ123-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 ; lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2 ; lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ12-CCZ123 ; lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CZ12-CCZ123 ; lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CCZ123)
open import Examples.Groups.Clifford+CS.Four.D.D697 W using (lem-pass-CCZ123-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 ; lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 ; lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-TOFF102-X0-X2 ; lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-TOFF102-X0-X2 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CZ12-CCZ123 ; lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CZ12-CCZ123 ; lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CCZ123 ; lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CCZ123)

private
  q1 : Eqn
  q1 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-CS12-CS12-CKd21-X2)
  q2 : Eqn
  q2 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-CKd21-CS12-CS12-X2)
  q3 : Eqn
  q3 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2)

-- Bar(SSSKSS;2,3->0) passes factors of X0 X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X0 X1 X2: 4 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 0 q1 ∷
   rw 6 q2 ∷
   rw 12 q3 ∷
   rw 88 q1 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = eqn (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CCZ123

-- pass [CCZ123] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (CCZ123 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (CCZ123 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q4 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = eqn (X3 ∷ CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (wn 1985 W)
  q6 : Eqn
  q6 = eqn (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CZ12 ∷ CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ12-CCZ123)
  q7 : Eqn
  q7 = eqn (CZ12 ∷ X3 ∷ []) (X3 ∷ CZ12 ∷ []) (low₃-comm ((CZ ↑)) (X))
  q8 : Eqn
  q8 = eqn (CZ12 ∷ CZ12 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) (wn 2036 W)

-- pass [X3 CS13 TOFF102 CSd13 TOFF102 X3] [CCZ123]: 5 steps
lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CCZ123 : ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CCZ123 = derive (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ [])
  (rw 5 q5 ∷
   rw 1 q6 ∷
   rw⁻ 0 q7 ∷
   rw 1 q5 ∷
   rw 0 q8 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = eqn (CCZ123 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CS12-X2)
  q10 : Eqn
  q10 = eqn (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CK21-X2)
  q11 : Eqn
  q11 = eqn (CCZ123 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3)
  q12 : Eqn
  q12 = eqn (CCZ123 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CKd21-X2)
  q13 : Eqn
  q13 = eqn (CCZ123 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CSd12-X2)

-- CCZ(2,1,3) passes split Gad(t=1, W=(2, 3), d=SK, e=-1): 5 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ : ⟪ (CCZ123 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ = derive (CCZ123 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ [])
  (rw 0 q9 ∷
   rw 3 q10 ∷
   rw 6 q11 ∷
   rw 14 q12 ∷
   rw 17 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CZ12-CCZ123)

-- pass [X3 CS23 TOFF201 CSd23 TOFF201 X3] [CCZ123]: 5 steps
lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CCZ123 : ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CCZ123 = derive (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ [])
  (rw 5 q5 ∷
   rw 1 q14 ∷
   rw⁻ 0 q7 ∷
   rw 1 q5 ∷
   rw 0 q8 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (lem-S2-ᵖ-1)
  q16 : Eqn
  q16 = eqn (X1 ∷ CS13 ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CS13 ∷ X1 ∷ []) (lem-pass-X1-CS13-X1-vs-CS02-TOFF013-CSd02-TOFF013)
  q17 : Eqn
  q17 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) lem-S2-ᵖ-1

-- pass [X1 CS13 X1] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X1 ∷ CS13 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X1 ∷ CS13 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13 ∷ X1 ∷ [])
  (rw 3 q15 ∷
   rw 0 q16 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = eqn (X1 ∷ CK13 ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (lem-pass-X1-CK13-X1-vs-CS02-TOFF013-CSd02-TOFF013)

-- pass [X1 CK13 X1] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X1-CK13-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X1 ∷ CK13 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  (rw 3 q15 ∷
   rw 0 q18 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (X1 ∷ CS13⁻ ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd13-X1-vs-CS02-TOFF013-CSd02-TOFF013)

-- pass [X1 CSd13 X1] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X1 ∷ CS13⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X1 ∷ CS13⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ [])
  (rw 3 q15 ∷
   rw 0 q19 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-CS01-X1)
  q21 : Eqn
  q21 = eqn (CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-CK10-X1)
  q22 : Eqn
  q22 = eqn (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3)
  q23 : Eqn
  q23 = eqn (CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-CKd10-X1)
  q24 : Eqn
  q24 = eqn (CCZ123 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-CSd01-X1)

-- CCZ(1,2,3) passes split Gad(t=0, W=(1, 2, 3), d=SK, e=-1): 5 steps
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ : ⟪ (CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ = derive (CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CCZ123 ∷ [])
  (rw 0 q20 ∷
   rw 3 q21 ∷
   rw 6 q22 ∷
   rw 16 q23 ∷
   rw 19 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (X1 ∷ CK13⁻ ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-CS02-TOFF013-CSd02-TOFF013)

-- pass [X1 CKd13 X1] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X1 ∷ CK13⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  (rw 3 q15 ∷
   rw 0 q25 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

-- CCZ(2,3,1) passes split Gad(t=1, W=(2, 3), d=SdKdSS, e=-1): 9 steps
lem-CCZ⟨231⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (CCZ123 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨231⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (CCZ123 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ [])
  (rw 0 q13 ∷
   rw 3 q12 ∷
   rw 6 q9 ∷
   rw 9 q9 ∷
   rw 12 q11 ∷
   rw 20 q13 ∷
   rw 23 q13 ∷
   rw 26 q10 ∷
   rw 29 q9 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (X0 ∷ CZ12 ∷ []) (CZ12 ∷ X0 ∷ []) (low₁-comm (X) (CZ))
  q27 : Eqn
  q27 = eqn (X0 ∷ CCZ123 ∷ []) (CCZ123 ∷ X0 ∷ []) (low₁-comm (X) (CCZ))

-- pass [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3] [CCZ123]: 10 steps
lem-pass-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3-vs-CCZ123 : ⟪ (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3-vs-CCZ123 = derive (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ [])
  (rw 7 q5 ∷
   rw 6 q26 ∷
   rw 7 q27 ∷
   rw 2 q6 ∷
   rw⁻ 1 q7 ∷
   rw 2 q5 ∷
   rw 0 q26 ∷
   rw 1 q26 ∷
   rw 2 q27 ∷
   rw 0 q8 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CCZ123

-- pass [CCZ123] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (CCZ123 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (CCZ123 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn [] (X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) (wn 1102 W)
  q30 : Eqn
  q30 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))
  q31 : Eqn
  q31 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q32 : Eqn
  q32 = eqn (X0 ∷ CS13 ∷ []) (CS13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))
  q33 : Eqn
  q33 = eqn (X0 ∷ X0 ∷ []) [] (wn 387 W)
  q34 : Eqn
  q34 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q35 : Eqn
  q35 = eqn (X2 ∷ CS13 ∷ []) (CS13 ∷ X2 ∷ []) (wn 257 W)
  q36 : Eqn
  q36 = eqn (X2 ∷ X2 ∷ []) [] (wn 389 W)
  q37 : Eqn
  q37 = eqn (Toff102 ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ []) (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q38 : Eqn
  q38 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)
  q39 : Eqn
  q39 = eqn (X0 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • (CS • CS • CS) • Swap ↑)))
  q40 : Eqn
  q40 = eqn (X2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X2 ∷ []) (wn 258 W)
  q41 : Eqn
  q41 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3)
  q42 : Eqn
  q42 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-TOFF102-X0-X2)
  q43 : Eqn
  q43 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3)
  q44 : Eqn
  q44 = eqn (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ []) lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 30 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 33 q29 ∷
   rw 40 q29 ∷
   rw 47 q29 ∷
   rw 29 q30 ∷
   rw 30 q31 ∷
   rw 31 q32 ∷
   rw 32 q33 ∷
   rw 29 q34 ∷
   rw 30 q35 ∷
   rw 31 q36 ∷
   rw⁻ 34 q37 ∷
   rw⁻ 35 q31 ∷
   rw⁻ 36 q34 ∷
   rw 37 q38 ∷
   rw 37 q30 ∷
   rw 38 q31 ∷
   rw 39 q39 ∷
   rw 40 q33 ∷
   rw 37 q34 ∷
   rw 38 q40 ∷
   rw 39 q36 ∷
   rw⁻ 42 q37 ∷
   rw⁻ 43 q31 ∷
   rw⁻ 44 q34 ∷
   rw 45 q38 ∷
   rw 0 q41 ∷
   rw 3 q42 ∷
   rw 8 q43 ∷
   rw 11 q42 ∷
   rw⁻ 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = eqn (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3)

-- CCZ(2,1,3) passes split Gad(t=1, W=(0, 2, 3), d=SK, e=-1): 5 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ : ⟪ (CCZ123 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ = derive (CCZ123 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ [])
  (rw 0 q9 ∷
   rw 3 q10 ∷
   rw 6 q45 ∷
   rw 16 q12 ∷
   rw 19 q13 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3)
  q47 : Eqn
  q47 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-TOFF102-X0-X2)
  q48 : Eqn
  q48 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3)

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 30 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 35 q29 ∷
   rw 42 q29 ∷
   rw 49 q29 ∷
   rw 31 q30 ∷
   rw 32 q31 ∷
   rw 33 q32 ∷
   rw 34 q33 ∷
   rw 31 q34 ∷
   rw 32 q35 ∷
   rw 33 q36 ∷
   rw⁻ 36 q37 ∷
   rw⁻ 37 q31 ∷
   rw⁻ 38 q34 ∷
   rw 39 q38 ∷
   rw 39 q30 ∷
   rw 40 q31 ∷
   rw 41 q39 ∷
   rw 42 q33 ∷
   rw 39 q34 ∷
   rw 40 q40 ∷
   rw 41 q36 ∷
   rw⁻ 44 q37 ∷
   rw⁻ 45 q31 ∷
   rw⁻ 46 q34 ∷
   rw 47 q38 ∷
   rw 0 q46 ∷
   rw 3 q47 ∷
   rw 8 q48 ∷
   rw 11 q47 ∷
   rw⁻ 0 q44 ∷ []) Eq.refl

-- pass [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3] [CCZ123]: 10 steps
lem-pass-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3-vs-CCZ123 : ⟪ (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3-vs-CCZ123 = derive (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ [])
  (rw 7 q5 ∷
   rw 6 q26 ∷
   rw 7 q27 ∷
   rw 2 q14 ∷
   rw⁻ 1 q7 ∷
   rw 2 q5 ∷
   rw 0 q26 ∷
   rw 1 q26 ∷
   rw 2 q27 ∷
   rw 0 q8 ∷ []) Eq.refl

-- CCZ(2,1,3) passes split Gad(t=1, W=(0, 2, 3), d=SdKdSS, e=-1): 9 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (CCZ123 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (CCZ123 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ [])
  (rw 0 q13 ∷
   rw 3 q12 ∷
   rw 6 q9 ∷
   rw 9 q9 ∷
   rw 12 q45 ∷
   rw 22 q13 ∷
   rw 25 q13 ∷
   rw 28 q10 ∷
   rw 31 q9 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q50 : Eqn
  q50 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q51 : Eqn
  q51 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q52 : Eqn
  q52 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q53 : Eqn
  q53 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ []) (S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2059 W)
  q54 : Eqn
  q54 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q55 : Eqn
  q55 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q56 : Eqn
  q56 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q57 : Eqn
  q57 = eqn (X3 ∷ CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q58 : Eqn
  q58 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q59 : Eqn
  q59 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S0 ∷ []) (S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2060 W)

-- pass [X3 CKd30 X3] [Sd0 TOFF012 CS03 TOFF012 CSd03 S0]: 45 steps
lem-pass-X3-CKd30-X3-vs-Sd0-TOFF012-CS03-TOFF012-CSd03-S0 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd0-TOFF012-CS03-TOFF012-CSd03-S0 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) (S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 4 q49 ∷
   rw 3 q50 ∷
   rw 2 q51 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q52 ∷
   rw 0 q51 ∷
   rw 1 q53 ∷
   rw⁻ 0 q50 ∷
   rw 1 q54 ∷
   rw 4 q49 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q54 ∷
   rw 4 q54 ∷
   rw 7 q49 ∷
   re 5 3 (CK30⁻ ∷ []) ∷
   rw 6 q54 ∷
   rw 7 q54 ∷
   rw 10 q49 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q54 ∷
   rw 10 q52 ∷
   rw 7 q55 ∷
   rw 4 q56 ∷
   rw 1 q57 ∷
   rw 15 q49 ∷
   rw 14 q58 ∷
   rw 13 q51 ∷
   re 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q52 ∷
   rw 11 q51 ∷
   rw 10 q51 ∷
   re 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q52 ∷
   rw 8 q51 ∷
   rw 7 q51 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q52 ∷
   rw 5 q51 ∷
   rw 6 q59 ∷
   rw⁻ 5 q58 ∷
   rw 6 q54 ∷
   rw 9 q49 ∷
   re 7 3 (CK30⁻ ∷ []) ∷
   rw 8 q54 ∷
   rw 9 q52 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CCZ123

-- pass [CCZ123] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 1 steps
lem-pass-CCZ123-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (CCZ123 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (CCZ123 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q62 : Eqn
  q62 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q63 : Eqn
  q63 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q64 : Eqn
  q64 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q65 : Eqn
  q65 = eqn (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1495 W)
  q66 : Eqn
  q66 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q67 : Eqn
  q67 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q68 : Eqn
  q68 = eqn (X2 ∷ CK20 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ []) (wn 1413 W)
  q69 : Eqn
  q69 = eqn (X2 ∷ CK20 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03)

-- pass [X2 CK20 X2] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 25 steps
lem-pass-X2-CK20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw 4 q61 ∷
   rw⁻ 3 q62 ∷
   rw⁻ 2 q63 ∷
   rw 1 q64 ∷
   rw⁻ 0 q63 ∷
   rw 1 q65 ∷
   rw 0 q62 ∷
   rw 1 q63 ∷
   rw 2 q66 ∷
   rw 3 q63 ∷
   rw 4 q67 ∷
   rw 1 q68 ∷
   rw 1 q69 ∷
   rw 5 q68 ∷
   rw 9 q61 ∷
   rw⁻ 8 q62 ∷
   rw⁻ 7 q63 ∷
   rw 6 q64 ∷
   rw⁻ 5 q63 ∷
   rw 6 q65 ∷
   rw 5 q62 ∷
   rw 6 q63 ∷
   rw 7 q66 ∷
   rw 8 q63 ∷
   rw 9 q67 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q71 : Eqn
  q71 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ K0⁻ ∷ []) (K0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 2061 W)
  q72 : Eqn
  q72 = eqn (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q73 : Eqn
  q73 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q74 : Eqn
  q74 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ K0 ∷ []) (K0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2062 W)

-- pass [X3 CSd30 X3] [Kd0 TOFF012 CS03 TOFF012 CSd03 K0]: 45 steps
lem-pass-X3-CSd30-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q49 ∷
   rw 3 q70 ∷
   rw 2 q51 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q52 ∷
   rw 0 q51 ∷
   rw 1 q71 ∷
   rw⁻ 0 q70 ∷
   rw 1 q54 ∷
   rw 4 q49 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q54 ∷
   rw 4 q54 ∷
   rw 7 q49 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q54 ∷
   rw 7 q54 ∷
   rw 10 q49 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q54 ∷
   rw 10 q52 ∷
   rw 7 q57 ∷
   rw 4 q72 ∷
   rw 1 q57 ∷
   rw 15 q49 ∷
   rw 14 q73 ∷
   rw 13 q51 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q52 ∷
   rw 11 q51 ∷
   rw 10 q51 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q52 ∷
   rw 8 q51 ∷
   rw 7 q51 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q52 ∷
   rw 5 q51 ∷
   rw 6 q74 ∷
   rw⁻ 5 q73 ∷
   rw 6 q54 ∷
   rw 9 q49 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q54 ∷
   rw 9 q52 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = eqn (CS02 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1462 W)
  q76 : Eqn
  q76 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ []) (wn 1463 W)

-- pass [CS30] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 23 steps
lem-pass-CS30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ [])
  (rw 2 q49 ∷
   rw 1 q51 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q52 ∷
   rw 1 q75 ∷
   rw 0 q54 ∷
   rw 1 q54 ∷
   rw 4 q49 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q54 ∷
   rw 4 q52 ∷
   rw 1 q57 ∷
   rw 9 q49 ∷
   rw 8 q51 ∷
   rw 7 q51 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q52 ∷
   rw 5 q51 ∷
   rw 6 q76 ∷
   rw 5 q54 ∷
   rw 8 q49 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q52 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (lem-S2-at1023)
  q78 : Eqn
  q78 = eqn [] (X3 ∷ X3 ∷ []) (wn 225 W)
  q79 : Eqn
  q79 = eqn (CS12 ∷ X3 ∷ []) (X3 ∷ CS12 ∷ []) (low₃-comm ((CS ↑)) (X))
  q80 : Eqn
  q80 = eqn (CS12⁻ ∷ X3 ∷ []) (X3 ∷ CS12⁻ ∷ []) (low₃-comm (((CS • CS • CS) ↑)) (X))

-- distribute Gad(t=1, W=(3,), d=1, e=1) TOFF103 CS12 TOFF103 CSd12: 8 steps
lem-distribute-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12 = derive (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ [])
  (rw 1 q77 ∷
   rw 2 q78 ∷
   rw 5 q78 ∷
   rw 8 q78 ∷
   rw⁻ 3 q79 ∷
   rw 4 q38 ∷
   rw⁻ 7 q80 ∷
   rw 8 q38 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (lem-S2-at1203)
  q82 : Eqn
  q82 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-TOFF123-CS01-TOFF123-CSd01)
  q83 : Eqn
  q83 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) lem-S2-at1203

-- pass [X3 CKd32 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CKd32-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X3 ∷ CK32⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  (rw 3 q81 ∷
   rw 0 q82 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CZ12 ∷ CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CZ12-CCZ123)

-- pass [X3 TOFF102 CS13 TOFF102 CSd13 X3] [CCZ123]: 5 steps
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CCZ123 : ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CCZ123 = derive (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 5 q5 ∷
   rw 1 q84 ∷
   rw⁻ 0 q7 ∷
   rw 1 q5 ∷
   rw 0 q8 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = eqn (X3 ∷ CK32 ∷ X3 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-TOFF123-CS01-TOFF123-CSd01)

-- pass [X3 CK32 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CK32-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X3 ∷ CK32 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  (rw 3 q81 ∷
   rw 0 q85 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = eqn (X2 ∷ CS23 ∷ X2 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ []) (lem-pass-X2-CS23-X2-vs-TOFF123-CS01-TOFF123-CSd01)

-- pass [X2 CS23 X2] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X2 ∷ CS23 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ [])
  (rw 3 q81 ∷
   rw 0 q86 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = eqn (X2 ∷ CK23 ∷ X2 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X2 ∷ CK23 ∷ X2 ∷ []) (lem-pass-X2-CK23-X2-vs-TOFF123-CS01-TOFF123-CSd01)

-- pass [X2 CK23 X2] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X2 ∷ CK23 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK23 ∷ X2 ∷ [])
  (rw 3 q81 ∷
   rw 0 q87 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = eqn (X2 ∷ CS23⁻ ∷ X2 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-TOFF123-CS01-TOFF123-CSd01)

-- pass [X2 CSd23 X2] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X2 ∷ CS23⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ [])
  (rw 3 q81 ∷
   rw 0 q88 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = eqn (CCZ123 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3)

-- CCZ(2,1,3) passes split Gad(t=1, W=(2, 3), d=1, e=1): 1 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩ : ⟪ (CCZ123 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩ = derive (CCZ123 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  (rw 0 q89 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = eqn (X2 ∷ CK23⁻ ∷ X2 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-TOFF123-CS01-TOFF123-CSd01)

-- pass [X2 CKd23 X2] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X2 ∷ CK23⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  (rw 3 q81 ∷
   rw 0 q90 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = eqn (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) (lem-S2-at2013)

-- distribute Gad(t=2, W=(3,), d=1, e=1) TOFF203 CS12 TOFF203 CSd12: 8 steps
lem-distribute-Gad⟨t≡2-W≡⟨3⟩-d≡1-e≡1⟩-TOFF203-CS12-TOFF203-CSd12 : ⟪ (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff203 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff203 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡2-W≡⟨3⟩-d≡1-e≡1⟩-TOFF203-CS12-TOFF203-CSd12 = derive (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ Toff203 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff203 ∷ X3 ∷ CS12⁻ ∷ [])
  (rw 1 q91 ∷
   rw 2 q78 ∷
   rw 5 q78 ∷
   rw 8 q78 ∷
   rw⁻ 3 q79 ∷
   rw 4 q38 ∷
   rw⁻ 7 q80 ∷
   rw 8 q38 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = eqn (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ []) (lem-S2-at2103)
  q93 : Eqn
  q93 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ []) (Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-TOFF213-CS02-TOFF213-CSd02)
  q94 : Eqn
  q94 = eqn (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ []) lem-S2-at2103

-- pass [X3 CKd31 X3] [TOFF201 CS23 TOFF201 CSd23]: 3 steps
lem-pass-X3-CKd31-X3-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-TOFF201-CS23-TOFF201-CSd23 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 3 q92 ∷
   rw 0 q93 ∷
   rw⁻ 0 q94 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = eqn (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ12 ∷ CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CZ12-CCZ123)

-- pass [X3 TOFF201 CS23 TOFF201 CSd23 X3] [CCZ123]: 5 steps
lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-CCZ123 : ⟪ (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-CCZ123 = derive (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 5 q5 ∷
   rw 1 q95 ∷
   rw⁻ 0 q7 ∷
   rw 1 q5 ∷
   rw 0 q8 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = eqn (X3 ∷ CK31 ∷ X3 ∷ Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ []) (Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-TOFF213-CS02-TOFF213-CSd02)

-- pass [X3 CK31 X3] [TOFF201 CS23 TOFF201 CSd23]: 3 steps
lem-pass-X3-CK31-X3-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-TOFF201-CS23-TOFF201-CSd23 = derive (X3 ∷ CK31 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 3 q92 ∷
   rw 0 q96 ∷
   rw⁻ 0 q94 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q98 : Eqn
  q98 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1681 W)
  q99 : Eqn
  q99 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q100 : Eqn
  q100 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q101 : Eqn
  q101 = eqn (X3 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (wn 2063 W)
  q102 : Eqn
  q102 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q103 : Eqn
  q103 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1482 W)

-- pass [X3 CSd30 X3] [X1 X2 TOFF012 CS03 TOFF012 CSd03 X1 X2]: 87 steps
lem-pass-X3-CSd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q49 ∷
   rw 3 q97 ∷
   rw 2 q51 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q52 ∷
   rw 0 q51 ∷
   rw 1 q98 ∷
   rw⁻ 0 q97 ∷
   rw 1 q54 ∷
   rw 4 q49 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q54 ∷
   rw 4 q52 ∷
   rw 5 q61 ∷
   rw⁻ 4 q63 ∷
   rw⁻ 3 q62 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q99 ∷
   rw 3 q100 ∷
   rw⁻ 2 q99 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 1 q62 ∷
   rw 2 q101 ∷
   rw 1 q63 ∷
   rw 2 q62 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q99 ∷
   rw 4 q102 ∷
   rw 5 q99 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q62 ∷
   rw 5 q67 ∷
   rw 5 q49 ∷
   rw 4 q51 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q52 ∷
   rw 2 q51 ∷
   rw 3 q103 ∷
   rw 2 q54 ∷
   rw 5 q49 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q54 ∷
   rw 5 q52 ∷
   rw 2 q55 ∷
   rw 9 q49 ∷
   rw 8 q51 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q52 ∷
   rw 6 q51 ∷
   rw 7 q103 ∷
   rw 6 q54 ∷
   rw 9 q49 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q54 ∷
   rw 9 q52 ∷
   rw 10 q49 ∷
   rw 9 q97 ∷
   rw 8 q51 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q52 ∷
   rw 6 q51 ∷
   rw 7 q98 ∷
   rw⁻ 6 q97 ∷
   rw 7 q54 ∷
   rw 10 q49 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q54 ∷
   rw 10 q52 ∷
   rw 11 q61 ∷
   rw⁻ 10 q63 ∷
   rw⁻ 9 q62 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q99 ∷
   rw 9 q100 ∷
   rw⁻ 8 q99 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q62 ∷
   rw 8 q101 ∷
   rw 7 q63 ∷
   rw 8 q62 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q99 ∷
   rw 10 q102 ∷
   rw 11 q99 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q62 ∷
   rw 11 q67 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = eqn (X2 ∷ CS02 ∷ X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1682 W)
  q105 : Eqn
  q105 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q106 : Eqn
  q106 = eqn (X3 ∷ CS13 ∷ X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (wn 2064 W)
  q107 : Eqn
  q107 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q108 : Eqn
  q108 = eqn (X2 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ []) (wn 1490 W)

-- pass [X3 CS30 X3] [X1 X2 TOFF012 CS03 TOFF012 CSd03 X1 X2]: 87 steps
lem-pass-X3-CS30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 = derive (X3 ∷ CS03 ∷ X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 4 q49 ∷
   rw 3 q97 ∷
   rw 2 q51 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q52 ∷
   rw 0 q51 ∷
   rw 1 q104 ∷
   rw⁻ 0 q97 ∷
   rw 1 q54 ∷
   rw 4 q49 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q54 ∷
   rw 4 q52 ∷
   rw 5 q61 ∷
   rw⁻ 4 q63 ∷
   rw⁻ 3 q62 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q99 ∷
   rw 3 q105 ∷
   rw⁻ 2 q99 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 1 q62 ∷
   rw 2 q106 ∷
   rw 1 q63 ∷
   rw 2 q62 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q99 ∷
   rw 4 q107 ∷
   rw 5 q99 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q62 ∷
   rw 5 q67 ∷
   rw 5 q49 ∷
   rw 4 q51 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q52 ∷
   rw 2 q51 ∷
   rw 3 q108 ∷
   rw 2 q54 ∷
   rw 5 q49 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q54 ∷
   rw 5 q52 ∷
   rw 2 q57 ∷
   rw 9 q49 ∷
   rw 8 q51 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q52 ∷
   rw 6 q51 ∷
   rw 7 q108 ∷
   rw 6 q54 ∷
   rw 9 q49 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q54 ∷
   rw 9 q52 ∷
   rw 10 q49 ∷
   rw 9 q97 ∷
   rw 8 q51 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q52 ∷
   rw 6 q51 ∷
   rw 7 q104 ∷
   rw⁻ 6 q97 ∷
   rw 7 q54 ∷
   rw 10 q49 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q54 ∷
   rw 10 q52 ∷
   rw 11 q61 ∷
   rw⁻ 10 q63 ∷
   rw⁻ 9 q62 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q99 ∷
   rw 9 q105 ∷
   rw⁻ 8 q99 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 7 q62 ∷
   rw 8 q106 ∷
   rw 7 q63 ∷
   rw 8 q62 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q99 ∷
   rw 10 q107 ∷
   rw 11 q99 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q62 ∷
   rw 11 q67 ∷ []) Eq.refl
