{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD643 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D643 (W : Ws) (Sᴰ : SD643) where

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
  lem-AXIOM-LF-at0132 : St 638
  lem-AXIOM-LF-at0132 = pickᴰ 0 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CX32 : St 543
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CX32 = pickᴰ 1 Sᴰ
  lem-X2-form : St 1567
  lem-X2-form = pickᴰ 2 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30 : St 1059
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30 = pickᴰ 3 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03 : St 1060
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03 = pickᴰ 4 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02 : St 1052
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02 = pickᴰ 5 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20 : St 1568
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20 = pickᴰ 6 Sᴰ
  lem-X-⟶Y-2-3 : St 1569
  lem-X-⟶Y-2-3 = pickᴰ 7 Sᴰ
  lem-X-⟶Y-3-2 : St 1570
  lem-X-⟶Y-3-2 = pickᴰ 8 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20 : St 1571
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20 = pickᴰ 9 Sᴰ

private
  q1 : Eqn
  q1 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q2 : Eqn
  q2 = sE 1570 lem-X-⟶Y-3-2
  q3 : Eqn
  q3 = wE 105 W
  q4 : Eqn
  q4 = sE 543 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CX32
  q5 : Eqn
  q5 = wE 1937 W
  q6 : Eqn
  q6 = wE 1938 W
  q7 : Eqn
  q7 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q8 : Eqn
  q8 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q9 : Eqn
  q9 = wE 3 W
  q10 : Eqn
  q10 = wE 372 W
  q11 : Eqn
  q11 = sE 1569 lem-X-⟶Y-2-3
  q12 : Eqn
  q12 = sE 1567 lem-X2-form
  q13 : Eqn
  q13 = sE 1060 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03
  q14 : Eqn
  q14 = sE 1571 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20
  q15 : Eqn
  q15 = wE 1939 W
  q16 : Eqn
  q16 = sE 1059 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30
  q17 : Eqn
  q17 = sE 1052 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02
  q18 : Eqn
  q18 = sE 1568 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20
  q19 : Eqn
  q19 = wE 1 W
  q20 : Eqn
  q20 = wE 464 W
  q21 : Eqn
  q21 = wE 1845 W
  q22 : Eqn
  q22 = wE 151 W
  q23 : Eqn
  q23 = sE 1567 lem-X2-form
  q24 : Eqn
  q24 = sE 638 lem-AXIOM-LF-at0132

-- hyb sym 23: 283 steps
lem-hyb-sym-23 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) ⟫ʷ
lem-hyb-sym-23 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ [])
  (rw 0 q1 ∷
   rw 29 q2 ∷
   rw 30 q3 ∷
   rw⁻ 31 q4 ∷
   rw 29 q5 ∷
   rw 62 q6 ∷
   rw⁻ 30 q7 ∷
   rw⁻ 31 q7 ∷
   rw⁻ 32 q7 ∷
   rw⁻ 33 q8 ∷
   rw⁻ 34 q7 ∷
   rw⁻ 35 q7 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q9 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q9 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q9 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q9 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q9 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q9 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q9 ∷
   re 44 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 43 q9 ∷
   rw 44 q10 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q9 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q9 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q9 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q9 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q9 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q9 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q9 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q9 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q9 ∷
   re 55 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 54 q9 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q9 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q9 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q9 ∷
   re 59 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 58 q9 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q9 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q9 ∷
   rw 61 q9 ∷
   rw⁻ 29 q11 ∷
   rw 29 q12 ∷
   rw 0 q13 ∷
   rw 31 q14 ∷
   rw 111 q15 ∷
   rw 142 q16 ∷
   rw⁻ 111 q17 ∷
   rw⁻ 31 q18 ∷
   rw 60 q19 ∷
   re 59 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 61 q9 ∷
   re 58 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 60 q9 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q9 ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 58 q9 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q9 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q9 ∷
   re 53 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 55 q9 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q9 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q9 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q9 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q9 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q9 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q9 ∷
   rw 46 q20 ∷
   re 45 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 47 q9 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q9 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q9 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q9 ∷
   rw 41 q20 ∷
   re 40 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 42 q9 ∷
   rw 39 q20 ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 40 q9 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 39 q9 ∷
   rw 36 q8 ∷
   rw 35 q8 ∷
   rw 34 q7 ∷
   rw 33 q8 ∷
   rw 32 q7 ∷
   rw 31 q7 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q9 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q9 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q9 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q9 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q9 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q9 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q9 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q9 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q9 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q9 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q9 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q9 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q9 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q9 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q9 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q9 ∷
   rw 14 q20 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 15 q9 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q9 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q9 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q9 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q9 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q9 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q9 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q9 ∷
   rw 5 q7 ∷
   rw 4 q7 ∷
   rw 3 q8 ∷
   rw 2 q7 ∷
   rw 1 q7 ∷
   rw 0 q7 ∷
   rw 1 q21 ∷
   rw⁻ 0 q7 ∷
   rw⁻ 1 q7 ∷
   rw⁻ 2 q8 ∷
   rw⁻ 3 q7 ∷
   rw⁻ 4 q8 ∷
   rw⁻ 5 q8 ∷
   rw 8 q19 ∷
   re 6 3 (CX13 ∷ []) ∷
   rw 9 q19 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q22 ∷
   rw 11 q19 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q22 ∷
   rw 13 q19 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q19 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q19 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q19 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q22 ∷
   rw 18 q19 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q19 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q19 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q19 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q19 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q19 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q19 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw 25 q19 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q19 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q19 ∷
   re 25 3 (CK30 ∷ []) ∷
   rw 28 q19 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q19 ∷
   re 27 3 (CK30 ∷ []) ∷
   rw 30 q19 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw⁻ 29 q7 ∷
   rw⁻ 30 q7 ∷
   rw⁻ 31 q7 ∷
   rw⁻ 32 q8 ∷
   rw⁻ 33 q7 ∷
   rw⁻ 34 q7 ∷
   rw 37 q19 ∷
   re 35 3 (CX13 ∷ []) ∷
   rw 38 q19 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q19 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 40 q19 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 41 q19 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q19 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 43 q19 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 44 q19 ∷
   re 42 3 (CK30 ∷ []) ∷
   rw 43 q22 ∷
   rw 46 q19 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 47 q19 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 48 q19 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 49 q19 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 50 q19 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 51 q19 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 52 q19 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 53 q19 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 54 q19 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 55 q19 ∷
   re 53 3 (CX13 ∷ []) ∷
   rw 56 q19 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 57 q19 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 58 q19 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 59 q19 ∷
   re 57 3 (CK30 ∷ []) ∷
   rw 60 q19 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 61 q19 ∷
   re 59 3 (CS03 ∷ []) ∷
   rw 60 q9 ∷
   rw⁻ 29 q23 ∷
   rw⁻ 0 q24 ∷ []) Eq.refl
