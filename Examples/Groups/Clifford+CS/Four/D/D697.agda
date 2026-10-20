{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D697 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D117 W using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2)
open import Examples.Groups.Clifford+CS.Four.D.D122 W using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2)
open import Examples.Groups.Clifford+CS.Four.D.D174 W using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D176 W using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D658 W using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D660 W using (lem-Bar⟨SSKSKK23-⟶0⟩-passes-II-white-units-1-0 ; lem-Bar⟨SSKSKK31-⟶0⟩-passes-II-white-units-2-0 ; lem-Bar⟨SSSKSS23-⟶0⟩-passes-II-white-units-1-0 ; lem-Bar⟨SSSKSS31-⟶0⟩-passes-II-white-units-2-0 ; lem-Bar⟨SSSKSS32-⟶0⟩-passes-II-white-units-1-0 ; lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-Z1-CZ12-CZ13-CCZ123 ; lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CZ12-CCZ123 ; lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CCZ123)
open import Examples.Groups.Clifford+CS.Four.D.D661 W using (lem-pass-CZ12-CCZ123-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CCZ123)
open import Examples.Groups.Clifford+CS.Four.D.D662 W using (lem-pass-CZ12-CCZ123-vs-TOFF201-CS23-TOFF201-CSd23)

private
  q1 : Eqn
  q1 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2)
  q2 : Eqn
  q2 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2)
  q3 : Eqn
  q3 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2)
  q4 : Eqn
  q4 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3)
  q5 : Eqn
  q5 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2)

-- Bar(SSKSKK;2,3->0) passes split Gad(t=1, W=(2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 0 q1 ∷
   rw 3 q2 ∷
   rw 6 q3 ∷
   rw 9 q3 ∷
   rw 12 q4 ∷
   rw 20 q1 ∷
   rw 23 q1 ∷
   rw 26 q5 ∷
   rw 29 q3 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q7 : Eqn
  q7 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q8 : Eqn
  q8 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q9 : Eqn
  q9 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q10 : Eqn
  q10 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q11 : Eqn
  q11 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q12 : Eqn
  q12 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q13 : Eqn
  q13 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 196 W)
  q14 : Eqn
  q14 = eqn (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (wn 1640 W)
  q15 : Eqn
  q15 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q16 : Eqn
  q16 = eqn (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ CX31 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (lem-Bar⟨SSSKSS32-⟶0⟩-passes-II-white-units-1-0)
  q17 : Eqn
  q17 = eqn (X2 ∷ CX21 ∷ X2 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (wn 1641 W)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X0 X3 TOFF103 X0 X3]: 135 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-TOFF103-X0-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-TOFF103-X0-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  (rw 36 q6 ∷
   rw 35 q7 ∷
   rw 34 q8 ∷
   re 33 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 34 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 33 q9 ∷
   rw 36 q6 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw⁻ 35 q10 ∷
   rw 38 q6 ∷
   re 36 3 (CS13⁻ ∷ []) ∷
   rw⁻ 37 q10 ∷
   rw 40 q6 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw⁻ 39 q9 ∷
   rw⁻ 40 q11 ∷
   rw 41 q12 ∷
   rw 40 q11 ∷
   rw 39 q9 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q12 ∷
   rw 37 q10 ∷
   re 36 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 38 q12 ∷
   rw 35 q10 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q12 ∷
   rw 33 q9 ∷
   rw 34 q13 ∷
   re 34 8 (Toff102 ∷ []) ∷
   rw 32 q7 ∷
   rw 31 q8 ∷
   rw 32 q14 ∷
   rw 31 q15 ∷
   rw 34 q6 ∷
   re 32 3 (CX31 ∷ []) ∷
   rw 33 q15 ∷
   rw 34 q15 ∷
   re 36 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 35 q9 ∷
   rw 38 q6 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw⁻ 37 q10 ∷
   rw 40 q6 ∷
   re 38 3 (CS13⁻ ∷ []) ∷
   rw⁻ 39 q10 ∷
   rw 42 q6 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw⁻ 41 q9 ∷
   rw⁻ 42 q11 ∷
   rw 35 q6 ∷
   rw⁻ 36 q9 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q12 ∷
   rw⁻ 38 q10 ∷
   re 40 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 39 q12 ∷
   rw⁻ 40 q10 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q12 ∷
   rw⁻ 42 q9 ∷
   rw⁻ 43 q11 ∷
   rw 36 q13 ∷
   re 36 8 (Toff102 ∷ []) ∷
   re 35 3 (Toff103 ∷ []) ∷
   rw 36 q15 ∷
   rw 37 q12 ∷
   rw 0 q16 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 q9 ∷
   rw 7 q6 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q10 ∷
   rw 9 q6 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q10 ∷
   rw 11 q6 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q9 ∷
   rw⁻ 11 q11 ∷
   rw 12 q12 ∷
   rw 11 q11 ∷
   rw 10 q9 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   rw 8 q10 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 6 q10 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 4 q9 ∷
   rw 5 q13 ∷
   re 5 8 (Toff102 ∷ []) ∷
   rw 3 q7 ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 3 q12 ∷
   rw 0 q7 ∷
   rw 1 q17 ∷
   rw⁻ 0 q8 ∷
   rw 1 q15 ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q9 ∷
   rw 5 q6 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q10 ∷
   rw 7 q6 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q10 ∷
   rw 9 q6 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q9 ∷
   rw⁻ 9 q11 ∷
   rw 2 q6 ∷
   rw⁻ 3 q9 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q12 ∷
   rw⁻ 5 q10 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q12 ∷
   rw⁻ 7 q10 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw⁻ 9 q9 ∷
   rw⁻ 10 q11 ∷
   rw 3 q13 ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   rw⁻ 3 q8 ∷
   rw 4 q15 ∷
   rw 5 q12 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = eqn (X3 ∷ CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (wn 1985 W)
  q19 : Eqn
  q19 = eqn (X2 ∷ CZ12 ∷ []) (Z1 ∷ CZ12 ∷ X2 ∷ []) (wn 1986 W)
  q20 : Eqn
  q20 = eqn (X2 ∷ CCZ123 ∷ []) (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (wn 1987 W)
  q21 : Eqn
  q21 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-Z1-CZ12-CZ13-CCZ123)
  q22 : Eqn
  q22 = eqn (Z1 ∷ X3 ∷ []) (X3 ∷ Z1 ∷ []) (low-comm ((Z ↑)) ((X ↑)))
  q23 : Eqn
  q23 = eqn (CZ12 ∷ X3 ∷ []) (X3 ∷ CZ12 ∷ []) (low₃-comm ((CZ ↑)) (X))
  q24 : Eqn
  q24 = eqn (X3 ∷ CZ13 ∷ []) (Z1 ∷ CZ13 ∷ X3 ∷ []) (wn 1988 W)
  q25 : Eqn
  q25 = eqn (Z1 ∷ X2 ∷ []) (X2 ∷ Z1 ∷ []) (low-comm ((Z ↑)) (X))
  q26 : Eqn
  q26 = eqn (X2 ∷ CZ13 ∷ []) (CZ13 ∷ X2 ∷ []) (wn 1989 W)
  q27 : Eqn
  q27 = eqn (Z1 ∷ Z1 ∷ CZ12 ∷ Z1 ∷ CZ13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) (wn 1990 W)

-- pass [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3] [CCZ123]: 15 steps
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CCZ123 : ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CCZ123 = derive (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ [])
  (rw 7 q18 ∷
   rw 6 q19 ∷
   rw 8 q20 ∷
   rw 2 q21 ∷
   rw⁻ 1 q22 ∷
   rw⁻ 2 q23 ∷
   rw 3 q24 ∷
   rw 5 q18 ∷
   rw⁻ 0 q25 ∷
   rw 1 q19 ∷
   rw⁻ 3 q25 ∷
   rw 4 q26 ∷
   rw 5 q19 ∷
   rw 7 q20 ∷
   rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-Bar⟨SSKSKK23-⟶0⟩-passes-II-white-units-1-0)

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X2 TOFF102 X0 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-TOFF102-X0-X2 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-TOFF102-X0-X2 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 29 q14 ∷
   rw 0 q28 ∷
   rw 0 q17 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CCZ123

-- pass [CCZ123] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-Bar⟨SSSKSS23-⟶0⟩-passes-II-white-units-1-0)

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X2 TOFF102 X0 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-TOFF102-X0-X2 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-TOFF102-X0-X2 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 31 q14 ∷
   rw 0 q30 ∷
   rw 0 q17 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q32 : Eqn
  q32 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q33 : Eqn
  q33 = eqn (X0 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ []) (wn 1106 W)
  q34 : Eqn
  q34 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q35 : Eqn
  q35 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q36 : Eqn
  q36 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q37 : Eqn
  q37 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q38 : Eqn
  q38 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q39 : Eqn
  q39 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q41 : Eqn
  q41 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q42 : Eqn
  q42 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q43 : Eqn
  q43 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q44 : Eqn
  q44 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q45 : Eqn
  q45 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wn 334 W)
  q46 : Eqn
  q46 = eqn (X1 ∷ X3 ∷ Toff213 ∷ X1 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) (wn 2037 W)
  q47 : Eqn
  q47 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q48 : Eqn
  q48 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q49 : Eqn
  q49 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q50 : Eqn
  q50 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q51 : Eqn
  q51 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-Bar⟨SSKSKK31-⟶0⟩-passes-II-white-units-2-0)
  q52 : Eqn
  q52 = eqn (X3 ∷ CX32 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Toff213 ∷ X1 ∷ X3 ∷ []) (wn 2038 W)
  q53 : Eqn
  q53 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wn 317 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X3 TOFF203 X0 X3]: 141 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF203-X0-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF203-X0-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 34 q31 ∷
   rw⁻ 33 q32 ∷
   rw 32 q33 ∷
   re 31 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 32 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 31 q34 ∷
   rw 32 q35 ∷
   rw 33 q36 ∷
   rw 34 q37 ∷
   rw 35 q36 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q38 ∷
   rw 37 q39 ∷
   rw 38 q38 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q34 ∷
   rw 38 q40 ∷
   rw 39 q41 ∷
   rw 38 q42 ∷
   rw⁻ 37 q34 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q38 ∷
   rw 37 q43 ∷
   rw⁻ 36 q38 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 35 q44 ∷
   rw⁻ 34 q37 ∷
   rw 33 q44 ∷
   rw⁻ 32 q35 ∷
   rw⁻ 31 q34 ∷
   rw 32 q45 ∷
   re 32 8 (Toff213 ∷ []) ∷
   rw⁻ 30 q32 ∷
   rw 29 q33 ∷
   rw 30 q46 ∷
   rw 29 q32 ∷
   rw 30 q47 ∷
   rw 31 q32 ∷
   rw 32 q32 ∷
   re 34 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 33 q34 ∷
   rw 34 q35 ∷
   rw 35 q36 ∷
   rw 36 q37 ∷
   rw 37 q36 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q38 ∷
   rw 39 q39 ∷
   rw 40 q38 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q34 ∷
   rw 40 q40 ∷
   rw 33 q31 ∷
   rw 34 q34 ∷
   rw 35 q35 ∷
   rw 36 q48 ∷
   rw 37 q37 ∷
   rw 38 q48 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q38 ∷
   rw 40 q49 ∷
   rw 41 q38 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 40 q34 ∷
   rw 41 q50 ∷
   rw 34 q45 ∷
   re 34 8 (Toff213 ∷ []) ∷
   re 33 3 (Toff203 ∷ []) ∷
   rw 34 q32 ∷
   rw 35 q41 ∷
   rw 0 q51 ∷
   rw 6 q31 ∷
   rw⁻ 5 q32 ∷
   re 4 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 5 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 4 q34 ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   rw 7 q37 ∷
   rw 8 q36 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q38 ∷
   rw 10 q39 ∷
   rw 11 q38 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q34 ∷
   rw 11 q40 ∷
   rw 12 q41 ∷
   rw 11 q42 ∷
   rw⁻ 10 q34 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q38 ∷
   rw 10 q43 ∷
   rw⁻ 9 q38 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q44 ∷
   rw⁻ 7 q37 ∷
   rw 6 q44 ∷
   rw⁻ 5 q35 ∷
   rw⁻ 4 q34 ∷
   rw 5 q45 ∷
   re 5 8 (Toff213 ∷ []) ∷
   rw⁻ 3 q32 ∷
   rw⁻ 2 q32 ∷
   rw⁻ 1 q47 ∷
   rw⁻ 0 q32 ∷
   rw 1 q52 ∷
   rw 0 q53 ∷
   rw 1 q32 ∷
   re 3 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 2 q34 ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 5 q37 ∷
   rw 6 q36 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q38 ∷
   rw 8 q39 ∷
   rw 9 q38 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q34 ∷
   rw 9 q40 ∷
   rw 2 q31 ∷
   rw 3 q34 ∷
   rw 4 q35 ∷
   rw 5 q48 ∷
   rw 6 q37 ∷
   rw 7 q48 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q38 ∷
   rw 9 q49 ∷
   rw 10 q38 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q34 ∷
   rw 10 q50 ∷
   rw 3 q45 ∷
   re 3 8 (Toff213 ∷ []) ∷
   re 2 3 (Toff203 ∷ []) ∷
   rw 3 q53 ∷
   rw 4 q32 ∷
   rw 5 q41 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-Bar⟨SSSKSS31-⟶0⟩-passes-II-white-units-2-0)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X0 X3 TOFF203 X0 X3]: 141 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF203-X0-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF203-X0-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 36 q31 ∷
   rw⁻ 35 q32 ∷
   rw 34 q33 ∷
   re 33 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 34 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 33 q34 ∷
   rw 34 q35 ∷
   rw 35 q36 ∷
   rw 36 q37 ∷
   rw 37 q36 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q38 ∷
   rw 39 q39 ∷
   rw 40 q38 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q34 ∷
   rw 40 q40 ∷
   rw 41 q41 ∷
   rw 40 q42 ∷
   rw⁻ 39 q34 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q38 ∷
   rw 39 q43 ∷
   rw⁻ 38 q38 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 37 q44 ∷
   rw⁻ 36 q37 ∷
   rw 35 q44 ∷
   rw⁻ 34 q35 ∷
   rw⁻ 33 q34 ∷
   rw 34 q45 ∷
   re 34 8 (Toff213 ∷ []) ∷
   rw⁻ 32 q32 ∷
   rw 31 q33 ∷
   rw 32 q46 ∷
   rw 31 q32 ∷
   rw 32 q47 ∷
   rw 33 q32 ∷
   rw 34 q32 ∷
   re 36 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 35 q34 ∷
   rw 36 q35 ∷
   rw 37 q36 ∷
   rw 38 q37 ∷
   rw 39 q36 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q38 ∷
   rw 41 q39 ∷
   rw 42 q38 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q34 ∷
   rw 42 q40 ∷
   rw 35 q31 ∷
   rw 36 q34 ∷
   rw 37 q35 ∷
   rw 38 q48 ∷
   rw 39 q37 ∷
   rw 40 q48 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q38 ∷
   rw 42 q49 ∷
   rw 43 q38 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 42 q34 ∷
   rw 43 q50 ∷
   rw 36 q45 ∷
   re 36 8 (Toff213 ∷ []) ∷
   re 35 3 (Toff203 ∷ []) ∷
   rw 36 q32 ∷
   rw 37 q41 ∷
   rw 0 q54 ∷
   rw 6 q31 ∷
   rw⁻ 5 q32 ∷
   re 4 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 5 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 4 q34 ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   rw 7 q37 ∷
   rw 8 q36 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q38 ∷
   rw 10 q39 ∷
   rw 11 q38 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q34 ∷
   rw 11 q40 ∷
   rw 12 q41 ∷
   rw 11 q42 ∷
   rw⁻ 10 q34 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q38 ∷
   rw 10 q43 ∷
   rw⁻ 9 q38 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q44 ∷
   rw⁻ 7 q37 ∷
   rw 6 q44 ∷
   rw⁻ 5 q35 ∷
   rw⁻ 4 q34 ∷
   rw 5 q45 ∷
   re 5 8 (Toff213 ∷ []) ∷
   rw⁻ 3 q32 ∷
   rw⁻ 2 q32 ∷
   rw⁻ 1 q47 ∷
   rw⁻ 0 q32 ∷
   rw 1 q52 ∷
   rw 0 q53 ∷
   rw 1 q32 ∷
   re 3 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 2 q34 ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 5 q37 ∷
   rw 6 q36 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q38 ∷
   rw 8 q39 ∷
   rw 9 q38 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q34 ∷
   rw 9 q40 ∷
   rw 2 q31 ∷
   rw 3 q34 ∷
   rw 4 q35 ∷
   rw 5 q48 ∷
   rw 6 q37 ∷
   rw 7 q48 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q38 ∷
   rw 9 q49 ∷
   rw 10 q38 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q34 ∷
   rw 10 q50 ∷
   rw 3 q45 ∷
   re 3 8 (Toff213 ∷ []) ∷
   re 2 3 (Toff203 ∷ []) ∷
   rw 3 q53 ∷
   rw 4 q32 ∷
   rw 5 q41 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ12 ∷ CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CZ12-CCZ123)
  q56 : Eqn
  q56 = eqn (CZ12 ∷ CZ12 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) (wn 2036 W)

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [CCZ123]: 5 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CCZ123 : ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CCZ123 = derive (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 5 q18 ∷
   rw 1 q55 ∷
   rw⁻ 0 q23 ∷
   rw 1 q18 ∷
   rw 0 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (CZ12 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CZ12 ∷ CCZ123 ∷ []) lem-pass-CZ12-CCZ123-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [CZ12 CCZ123]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CZ12-CCZ123 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CZ12 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CZ12-CCZ123 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CZ12 ∷ CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CCZ123

-- pass [CCZ123] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (CCZ123 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (CCZ123 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q58 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (CZ12 ∷ CCZ123 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ12 ∷ CCZ123 ∷ []) lem-pass-CZ12-CCZ123-vs-TOFF201-CS23-TOFF201-CSd23

-- pass [TOFF201 CS23 TOFF201 CSd23] [CZ12 CCZ123]: 1 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CZ12-CCZ123 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ12 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ123 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CZ12-CCZ123 = derive (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ12 ∷ CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  (rw⁻ 0 q59 ∷ []) Eq.refl
