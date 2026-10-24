{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD561 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D561 (W : Ws) (Sᴰ : SD561) where

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
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-comm-WBar⟨SSSSSSKiSSSSSSSSS~23-⟶1⟩ : St 963
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-comm-WBar⟨SSSSSSKiSSSSSSSSS~23-⟶1⟩ = pickᴰ 0 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X2-X3-TOFF302-X2-X3 : St 964
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X2-X3-TOFF302-X2-X3 = pickᴰ 1 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1 : St 965
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1 = pickᴰ 2 Sᴰ
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-II/IV-units-3-1 : St 966
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-II/IV-units-3-1 = pickᴰ 3 Sᴰ
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-comm-WBar⟨KiKiSSSKiSSSSSS~21-⟶3⟩ : St 967
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-comm-WBar⟨KiKiSSSKiSSSSSS~21-⟶3⟩ = pickᴰ 4 Sᴰ
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-comm-WBar⟨SSSSSSKiSSSSSSSSS~21-⟶3⟩ : St 968
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-comm-WBar⟨SSSSSSKiSSSSSSSSS~21-⟶3⟩ = pickᴰ 5 Sᴰ
  lem-AXIOM-LF-at2301 : St 969
  lem-AXIOM-LF-at2301 = pickᴰ 6 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1 : St 970
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1 = pickᴰ 7 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-comm-WBar⟨KiKiSSSKiSSSSSS~23-⟶1⟩ : St 971
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-comm-WBar⟨KiKiSSSKiSSSSSS~23-⟶1⟩ = pickᴰ 8 Sᴰ

private
  q1 : Eqn
  q1 = wE 1593 W
  q2 : Eqn
  q2 = sE 966 lem-Bar⟨SSSKSS21-⟶0⟩-passes-II/IV-units-3-1
  q3 : Eqn
  q3 = wE 1594 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 TOFF312 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-TOFF312-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乨丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-TOFF312-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乨丘") (ℓ "丘乨丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 31 q1 ∷
   rw 0 q2 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = wE 1595 W
  q5 : Eqn
  q5 = sE 968 lem-Bar⟨SSSKSS21-⟶0⟩-passes-comm-WBar⟨SSSSSSKiSSSSSSSSS~21-⟶3⟩
  q6 : Eqn
  q6 = wE 1596 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CS23 CS23 CS23 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX21 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S1 S1 S1 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX21 CS13 CS13 CS13 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX21-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S1-S1-S1-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX21-CS13-CS13-CS13-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘义义义义义义乍且义义义义义义义义义乆丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽与与与乁与丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乆丽丽丽丽丽丽乁与丽丽丽丽丽丽丽丽丽丘") ⟫ʷ ≈ ⟪ (ℓ "丘义义义义义义乍且义义义义义义义义义乆丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽与与与乁与丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乆丽丽丽丽丽丽乁与丽丽丽丽丽丽丽丽丽丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX21-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S1-S1-S1-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX21-CS13-CS13-CS13-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘义义义义义义乍且义义义义义义义义义乆丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽与与与乁与丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乆丽丽丽丽丽丽乁与丽丽丽丽丽丽丽丽丽丘") (ℓ "丘义义义义义义乍且义义义义义义义义义乆丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽与与与乁与丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乆丽丽丽丽丽丽乁与丽丽丽丽丽丽丽丽丽丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 31 q4 ∷
   rw 0 q5 ∷
   rw 0 q6 ∷ []) Eq.refl

private
  q7 : Eqn
  q7 = wE 1597 W
  q8 : Eqn
  q8 = sE 967 lem-Bar⟨SSSKSS21-⟶0⟩-passes-comm-WBar⟨KiKiSSSKiSSSSSS~21-⟶3⟩
  q9 : Eqn
  q9 = wE 1598 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CK23 S2 CK23 S2 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CX21 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S1 S1 S1 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S1 S1 S1 CK13 S1 S1 S1 S1 CK13 S1 CX21 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX21-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S1-S1-S1-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S1-S1-S1-CK13-S1-S1-S1-S1-CK13-S1-CX21-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乍且乍且义义义乍且义义义义义义乆丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽与与与乁与丽丽丽丽丽丽丽丽丽与与与乁与与与与乁与乆乁与乁与丽丽丽乁与丽丽丽丽丽丽丘") ⟫ʷ ≈ ⟪ (ℓ "丘乍且乍且义义义乍且义义义义义义乆丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽与与与乁与丽丽丽丽丽丽丽丽丽与与与乁与与与与乁与乆乁与乁与丽丽丽乁与丽丽丽丽丽丽丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX21-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S1-S1-S1-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S1-S1-S1-CK13-S1-S1-S1-S1-CK13-S1-CX21-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乍且乍且义义义乍且义义义义义义乆丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽与与与乁与丽丽丽丽丽丽丽丽丽与与与乁与与与与乁与乆乁与乁与丽丽丽乁与丽丽丽丽丽丽丘") (ℓ "丘乍且乍且义义义乍且义义义义义义乆丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽与与与乁与丽丽丽丽丽丽丽丽丽与与与乁与与与与乁与乆乁与乁与丽丽丽乁与丽丽丽丽丽丽丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 31 q7 ∷
   rw 0 q8 ∷
   rw 0 q9 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = wE 1567 W
  q11 : Eqn
  q11 = sE 965 lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1
  q12 : Eqn
  q12 = wE 1568 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 TOFF012 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF012-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF012-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘九丘") (ℓ "丘九丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q10 ∷
   rw 0 q11 ∷
   rw 0 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q15 : Eqn
  q15 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q16 : Eqn
  q16 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q18 : Eqn
  q18 = wE 30 W
  q19 : Eqn
  q19 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q20 : Eqn
  q20 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q21 : Eqn
  q21 = wE 27 W
  q22 : Eqn
  q22 = wE 122 W
  q23 : Eqn
  q23 = wE 31 W
  q24 : Eqn
  q24 = wE 127 W
  q25 : Eqn
  q25 = wE 7 W
  q26 : Eqn
  q26 = wE 74 W
  q27 : Eqn
  q27 = wE 337 W
  q28 : Eqn
  q28 = wE 1603 W
  q29 : Eqn
  q29 = wE 24 W
  q30 : Eqn
  q30 = wE 25 W
  q31 : Eqn
  q31 = wE 124 W
  q32 : Eqn
  q32 = sE 964 lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X2-X3-TOFF302-X2-X3
  q33 : Eqn
  q33 = wE 1604 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 TOFF302 X2 X3]: 135 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF302-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞乧丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞乧丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF302-X2-X3 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞乧丘丞") (ℓ "丘丞乧丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 34 q13 ∷
   rw⁻ 33 q14 ∷
   rw⁻ 32 q15 ∷
   re 31 1 (ℓ "並乨並") ∷
   re 32 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 31 q16 ∷
   rw 32 q17 ∷
   rw 33 q18 ∷
   rw 34 q19 ∷
   rw 35 q18 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q20 ∷
   rw 37 q21 ∷
   rw 38 q20 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q16 ∷
   rw 38 q22 ∷
   rw 39 q23 ∷
   rw 38 q24 ∷
   rw⁻ 37 q16 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q20 ∷
   rw 37 q25 ∷
   rw⁻ 36 q20 ∷
   re 37 3 (ℓ "丽") ∷
   rw 35 q26 ∷
   rw⁻ 34 q19 ∷
   rw 33 q26 ∷
   rw⁻ 32 q17 ∷
   rw⁻ 31 q16 ∷
   rw 32 q27 ∷
   re 32 8 (ℓ "乨") ∷
   rw⁻ 30 q14 ∷
   rw⁻ 29 q15 ∷
   rw 30 q28 ∷
   rw 29 q15 ∷
   re 31 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 30 q16 ∷
   rw 31 q17 ∷
   rw 32 q18 ∷
   rw 33 q19 ∷
   rw 34 q18 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q20 ∷
   rw 36 q21 ∷
   rw 37 q20 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q16 ∷
   rw 37 q22 ∷
   rw 30 q13 ∷
   rw 31 q16 ∷
   rw 32 q17 ∷
   rw 33 q29 ∷
   rw 34 q19 ∷
   rw 35 q29 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 36 q20 ∷
   rw 37 q30 ∷
   rw 38 q20 ∷
   re 36 3 (ℓ "丽") ∷
   rw 37 q16 ∷
   rw 38 q31 ∷
   rw 31 q27 ∷
   re 31 8 (ℓ "乨") ∷
   re 30 3 (ℓ "乧") ∷
   rw 31 q15 ∷
   rw 32 q23 ∷
   rw 0 q32 ∷
   rw 3 q13 ∷
   rw⁻ 2 q15 ∷
   re 1 1 (ℓ "並乨並") ∷
   re 2 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 1 q16 ∷
   rw 2 q17 ∷
   rw 3 q18 ∷
   rw 4 q19 ∷
   rw 5 q18 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q20 ∷
   rw 7 q21 ∷
   rw 8 q20 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q16 ∷
   rw 8 q22 ∷
   rw 9 q23 ∷
   rw 8 q24 ∷
   rw⁻ 7 q16 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q20 ∷
   rw 7 q25 ∷
   rw⁻ 6 q20 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q26 ∷
   rw⁻ 4 q19 ∷
   rw 3 q26 ∷
   rw⁻ 2 q17 ∷
   rw⁻ 1 q16 ∷
   rw 2 q27 ∷
   re 2 8 (ℓ "乨") ∷
   rw⁻ 0 q15 ∷
   rw 1 q33 ∷
   rw 0 q15 ∷
   rw 1 q14 ∷
   re 3 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 2 q16 ∷
   rw 3 q17 ∷
   rw 4 q18 ∷
   rw 5 q19 ∷
   rw 6 q18 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q20 ∷
   rw 8 q21 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q16 ∷
   rw 9 q22 ∷
   rw 2 q13 ∷
   rw 3 q16 ∷
   rw 4 q17 ∷
   rw 5 q29 ∷
   rw 6 q19 ∷
   rw 7 q29 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q20 ∷
   rw 9 q30 ∷
   rw 10 q20 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q16 ∷
   rw 10 q31 ∷
   rw 3 q27 ∷
   re 3 8 (ℓ "乨") ∷
   re 2 3 (ℓ "乧") ∷
   rw 3 q15 ∷
   rw 4 q14 ∷
   rw 5 q23 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 1605 W
  q35 : Eqn
  q35 = sE 963 lem-Bar⟨SSKSKK23-⟶0⟩-passes-comm-WBar⟨SSSSSSKiSSSSSSSSS~23-⟶1⟩
  q36 : Eqn
  q36 = wE 1606 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CS12 CS12 CS12 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S3 S3 S3 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丘") (ℓ "丘丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q34 ∷
   rw 0 q35 ∷
   rw 0 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 1607 W
  q38 : Eqn
  q38 = sE 971 lem-Bar⟨SSKSKK23-⟶0⟩-passes-comm-WBar⟨KiKiSSSKiSSSSSS~23-⟶1⟩
  q39 : Eqn
  q39 = wE 1608 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S3 S3 S3 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S3 S3 S3 CK31 S3 S3 S3 S3 CK31 S3 CX23 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘") (ℓ "丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q37 ∷
   rw 0 q38 ∷
   rw 0 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = sE 969 lem-AXIOM-LF-at2301
  q41 : Eqn
  q41 = wE 225 W
  q42 : Eqn
  q42 = wE 871 W
  q43 : Eqn
  q43 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q44 : Eqn
  q44 = wE 1609 W
  q45 : Eqn
  q45 = eqn (ℓ "习丞") (ℓ "丞习") (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q46 : Eqn
  q46 = wE 173 W
  q47 : Eqn
  q47 = wE 389 W

-- kk pieces X2 X3 CS23 CS23 CK32 CS23 CX30 CS02 CS02 CS02 CK02 S0 CS02 C at 3: 27 steps
lem-kk-pieces-X2-X3-CS23-CS23-CK32-CS23-CX30-CS02-CS02-CS02-CK02-S0-CS02-C-at-3 : ⟪ (ℓ "丘丞义义乗义乐丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧为丧丧丧丈丫丧丧丧丧丧丧乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丈丫丧丧丧丧丧丧丧丧丧乐义义义业乗义义义义义义与为丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘丞丞乡丞丘丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丘丞丞乡丞丘丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞") ⟫ʷ
lem-kk-pieces-X2-X3-CS23-CS23-CK32-CS23-CX30-CS02-CS02-CS02-CK02-S0-CS02-C-at-3 = derive (ℓ "丘丞义义乗义乐丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧为丧丧丧丈丫丧丧丧丧丧丧乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丈丫丧丧丧丧丧丧丧丧丧乐义义义业乗义义义义义义与为丘丞") (ℓ "丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘丞丞乡丞丘丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丘丞丞乡丞丘丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞")
  (rw 2 q40 ∷
   rw 31 q41 ∷
   rw 32 q42 ∷
   rw 36 q41 ∷
   rw 37 q42 ∷
   rw 71 q41 ∷
   rw 72 q42 ∷
   rw 76 q41 ∷
   rw 77 q42 ∷
   rw⁻ 31 q43 ∷
   rw 33 q43 ∷
   re 35 1 (ℓ "乏习乏") ∷
   rw 34 q44 ∷
   rw⁻ 35 q45 ∷
   rw 36 q46 ∷
   re 34 3 (ℓ "乡") ∷
   rw 35 q43 ∷
   rw 36 q47 ∷
   rw⁻ 69 q43 ∷
   rw 71 q43 ∷
   re 73 1 (ℓ "乏习乏") ∷
   rw 72 q44 ∷
   rw⁻ 73 q45 ∷
   rw 74 q46 ∷
   re 72 3 (ℓ "乡") ∷
   rw 73 q43 ∷
   rw 74 q47 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 1610 W
  q49 : Eqn
  q49 = sE 970 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1
  q50 : Eqn
  q50 = wE 1611 W

-- pass [CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02] [X3 TOFF213 X3]: 3 steps
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-TOFF213-X3 : ⟪ (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞乥丞") ⟫ʷ ≈ ⟪ (ℓ "丞乥丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫") ⟫ʷ
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-TOFF213-X3 = derive (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞乥丞") (ℓ "丞乥丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫")
  (rw 29 q48 ∷
   rw 0 q49 ∷
   rw 0 q50 ∷ []) Eq.refl
