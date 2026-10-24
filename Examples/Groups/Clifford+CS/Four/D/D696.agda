{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD696 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D696 (W : Ws) (Sᴰ : SD696) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2 : St 293
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2 = pickᴰ 0 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2 : St 299
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2 : St 365
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2 : St 367
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2 = pickᴰ 3 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-X2 : St 430
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-X2 = pickᴰ 4 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2 : St 431
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2 = pickᴰ 5 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-X2 : St 446
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-X2 = pickᴰ 6 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-X2 : St 448
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-X2 = pickᴰ 7 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CK10-X1 : St 1843
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CK10-X1 = pickᴰ 8 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CKd10-X1 : St 1844
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CKd10-X1 = pickᴰ 9 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-X1 : St 1845
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-X1 = pickᴰ 10 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CSd01-X1 : St 1846
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CSd01-X1 = pickᴰ 11 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X0-X3-TOFF103-X0-X3 : St 1847
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X0-X3-TOFF103-X0-X3 = pickᴰ 12 Sᴰ
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-factors-of-X0-X2-X3-TOFF302-X0-X2-X3 : St 1848
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-factors-of-X0-X2-X3-TOFF302-X0-X2-X3 = pickᴰ 13 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-Fredkin-WBar⟨KiKiSSSKiSSSSSS~20-⟶1⟩ : St 1849
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-Fredkin-WBar⟨KiKiSSSKiSSSSSS~20-⟶1⟩ = pickᴰ 14 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-Fredkin-WBar⟨KiKiSSSKiSSSSSS~20-⟶1⟩ : St 1850
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-Fredkin-WBar⟨KiKiSSSKiSSSSSS~20-⟶1⟩ = pickᴰ 15 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CZ12-CCZ123 : St 1851
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CZ12-CCZ123 = pickᴰ 16 Sᴰ
  lem-pass-X0-X1-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-vs-X2-TOFF312-X2 : St 1852
  lem-pass-X0-X1-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-vs-X2-TOFF312-X2 = pickᴰ 17 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : St 1853
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = pickᴰ 18 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : St 1854
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = pickᴰ 19 Sᴰ
  lem-pass-CZ12-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 : St 1855
  lem-pass-CZ12-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 20 Sᴰ
  lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CCZ123 : St 1856
  lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CCZ123 = pickᴰ 21 Sᴰ
  lem-pass-CZ12-CCZ123-vs-CS23-TOFF201-CSd23-TOFF201 : St 1857
  lem-pass-CZ12-CCZ123-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 22 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 1858
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 23 Sᴰ
  lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-CCZ123 : St 1859
  lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-CCZ123 = pickᴰ 24 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 196 W
  q9 : Eqn
  q9 = wE 1640 W
  q10 : Eqn
  q10 = wE 175 W
  q11 : Eqn
  q11 = sE 1847 lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X0-X3-TOFF103-X0-X3
  q12 : Eqn
  q12 = wE 1641 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X0 X3 TOFF103 X0 X3]: 135 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF103-X0-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞乡丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞乡丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF103-X0-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞乡丌丞") (ℓ "丌丞乡丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 34 q1 ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   re 31 1 (ℓ "乏习乏") ∷
   re 32 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 31 q4 ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "丽") ∷
   rw⁻ 33 q5 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "举") ∷
   rw⁻ 35 q5 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   rw⁻ 37 q4 ∷
   rw⁻ 38 q6 ∷
   rw 39 q7 ∷
   rw 38 q6 ∷
   rw 37 q4 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q7 ∷
   rw 35 q5 ∷
   re 34 1 (ℓ "乏丷乏") ∷
   rw 36 q7 ∷
   rw 33 q5 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 34 q7 ∷
   rw 31 q4 ∷
   rw 32 q8 ∷
   re 32 8 (ℓ "习") ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   rw 30 q9 ∷
   rw 29 q10 ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乓") ∷
   rw 31 q10 ∷
   rw 32 q10 ∷
   re 34 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 33 q4 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "丽") ∷
   rw⁻ 35 q5 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "举") ∷
   rw⁻ 37 q5 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw⁻ 39 q4 ∷
   rw⁻ 40 q6 ∷
   rw 33 q1 ∷
   rw⁻ 34 q4 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q7 ∷
   rw⁻ 36 q5 ∷
   re 38 1 (ℓ "乏丷乏") ∷
   rw 37 q7 ∷
   rw⁻ 38 q5 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q7 ∷
   rw⁻ 40 q4 ∷
   rw⁻ 41 q6 ∷
   rw 34 q8 ∷
   re 34 8 (ℓ "习") ∷
   re 33 3 (ℓ "乡") ∷
   rw 34 q10 ∷
   rw 35 q7 ∷
   rw 0 q11 ∷
   rw 6 q1 ∷
   rw 5 q2 ∷
   re 4 1 (ℓ "乏习乏") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q6 ∷
   rw 12 q7 ∷
   rw 11 q6 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q7 ∷
   rw 8 q5 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q7 ∷
   rw 6 q5 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q7 ∷
   rw 4 q4 ∷
   rw 5 q8 ∷
   re 5 8 (ℓ "习") ∷
   rw 3 q2 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏乆乏") ∷
   rw 3 q7 ∷
   rw 0 q2 ∷
   rw 1 q12 ∷
   rw⁻ 0 q3 ∷
   rw 1 q10 ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q4 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q5 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q6 ∷
   rw 2 q1 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q7 ∷
   rw⁻ 5 q5 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q7 ∷
   rw⁻ 7 q5 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q7 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q6 ∷
   rw 3 q8 ∷
   re 3 8 (ℓ "习") ∷
   re 2 3 (ℓ "乡") ∷
   rw⁻ 3 q3 ∷
   rw 4 q10 ∷
   rw 5 q7 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 2032 W
  q14 : Eqn
  q14 = sE 1849 lem-Bar⟨SSKSKK23-⟶0⟩-passes-Fredkin-WBar⟨KiKiSSSKiSSSSSS~20-⟶1⟩
  q15 : Eqn
  q15 = wE 2033 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX20 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 S0 S0 S0 CK01 S0 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘") (ℓ "丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q13 ∷
   rw 0 q14 ∷
   rw 0 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 1784 W
  q17 : Eqn
  q17 = wE 2034 W
  q18 : Eqn
  q18 = sE 1852 lem-pass-X0-X1-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-vs-X2-TOFF312-X2
  q19 : Eqn
  q19 = wE 2035 W
  q20 : Eqn
  q20 = wE 1787 W

-- pass [TOFF312] [X0 X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X0 X1 X2]: 5 steps
lem-pass-TOFF312-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : ⟪ (ℓ "乨丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘乨") ⟫ʷ
lem-pass-TOFF312-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = derive (ℓ "乨丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘") (ℓ "丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘乨")
  (rw 0 q16 ∷
   rw 4 q17 ∷
   rw⁻ 1 q18 ∷
   rw 0 q19 ∷
   rw 35 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = sE 1850 lem-Bar⟨SSSKSS23-⟶0⟩-passes-Fredkin-WBar⟨KiKiSSSKiSSSSSS~20-⟶1⟩

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX20 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 S0 S0 S0 CK01 S0 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘") (ℓ "丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q13 ∷
   rw 0 q21 ∷
   rw 0 q15 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = wE 5 W
  q23 : Eqn
  q23 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q24 : Eqn
  q24 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q25 : Eqn
  q25 = wE 1106 W
  q26 : Eqn
  q26 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q27 : Eqn
  q27 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q28 : Eqn
  q28 = wE 30 W
  q29 : Eqn
  q29 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q30 : Eqn
  q30 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q31 : Eqn
  q31 = wE 27 W
  q32 : Eqn
  q32 = wE 122 W
  q33 : Eqn
  q33 = wE 31 W
  q34 : Eqn
  q34 = wE 127 W
  q35 : Eqn
  q35 = wE 7 W
  q36 : Eqn
  q36 = wE 74 W
  q37 : Eqn
  q37 = wE 337 W
  q38 : Eqn
  q38 = wE 1658 W
  q39 : Eqn
  q39 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q40 : Eqn
  q40 = wE 24 W
  q41 : Eqn
  q41 = wE 25 W
  q42 : Eqn
  q42 = wE 124 W
  q43 : Eqn
  q43 = sE 1848 lem-Bar⟨SSKSKK21-⟶0⟩-passes-factors-of-X0-X2-X3-TOFF302-X0-X2-X3
  q44 : Eqn
  q44 = wE 1659 W
  q45 : Eqn
  q45 = wE 317 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X2 X3 TOFF302 X0 X2 X3]: 145 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-TOFF302-X0-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丌丘丞乧丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞乧丌丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-TOFF302-X0-X2-X3 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丌丘丞乧丌丘丞") (ℓ "丌丘丞乧丌丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 36 q22 ∷
   rw⁻ 35 q23 ∷
   rw⁻ 34 q24 ∷
   rw 33 q25 ∷
   re 32 1 (ℓ "並乨並") ∷
   re 33 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 32 q26 ∷
   rw 33 q27 ∷
   rw 34 q28 ∷
   rw 35 q29 ∷
   rw 36 q28 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q30 ∷
   rw 38 q31 ∷
   rw 39 q30 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q26 ∷
   rw 39 q32 ∷
   rw 40 q33 ∷
   rw 39 q34 ∷
   rw⁻ 38 q26 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q30 ∷
   rw 38 q35 ∷
   rw⁻ 37 q30 ∷
   re 38 3 (ℓ "丽") ∷
   rw 36 q36 ∷
   rw⁻ 35 q29 ∷
   rw 34 q36 ∷
   rw⁻ 33 q27 ∷
   rw⁻ 32 q26 ∷
   rw 33 q37 ∷
   re 33 8 (ℓ "乨") ∷
   rw⁻ 31 q23 ∷
   rw⁻ 30 q24 ∷
   rw 29 q25 ∷
   rw 30 q38 ∷
   rw 29 q24 ∷
   rw 30 q39 ∷
   rw 31 q24 ∷
   rw 32 q24 ∷
   re 34 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 33 q26 ∷
   rw 34 q27 ∷
   rw 35 q28 ∷
   rw 36 q29 ∷
   rw 37 q28 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q30 ∷
   rw 39 q31 ∷
   rw 40 q30 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q26 ∷
   rw 40 q32 ∷
   rw 33 q22 ∷
   rw 34 q26 ∷
   rw 35 q27 ∷
   rw 36 q40 ∷
   rw 37 q29 ∷
   rw 38 q40 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q30 ∷
   rw 40 q41 ∷
   rw 41 q30 ∷
   re 39 3 (ℓ "丽") ∷
   rw 40 q26 ∷
   rw 41 q42 ∷
   rw 34 q37 ∷
   re 34 8 (ℓ "乨") ∷
   re 33 3 (ℓ "乧") ∷
   rw 34 q24 ∷
   rw 35 q33 ∷
   rw 0 q43 ∷
   rw 6 q22 ∷
   rw⁻ 5 q24 ∷
   re 4 1 (ℓ "並乨並") ∷
   re 5 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 4 q26 ∷
   rw 5 q27 ∷
   rw 6 q28 ∷
   rw 7 q29 ∷
   rw 8 q28 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q30 ∷
   rw 10 q31 ∷
   rw 11 q30 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q26 ∷
   rw 11 q32 ∷
   rw 12 q33 ∷
   rw 11 q34 ∷
   rw⁻ 10 q26 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q30 ∷
   rw 10 q35 ∷
   rw⁻ 9 q30 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q36 ∷
   rw⁻ 7 q29 ∷
   rw 6 q36 ∷
   rw⁻ 5 q27 ∷
   rw⁻ 4 q26 ∷
   rw 5 q37 ∷
   re 5 8 (ℓ "乨") ∷
   rw⁻ 3 q24 ∷
   rw⁻ 2 q24 ∷
   rw⁻ 1 q39 ∷
   rw⁻ 0 q24 ∷
   rw 1 q44 ∷
   rw 0 q45 ∷
   rw 1 q24 ∷
   rw 2 q23 ∷
   re 4 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 3 q26 ∷
   rw 4 q27 ∷
   rw 5 q28 ∷
   rw 6 q29 ∷
   rw 7 q28 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q30 ∷
   rw 9 q31 ∷
   rw 10 q30 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q26 ∷
   rw 10 q32 ∷
   rw 3 q22 ∷
   rw 4 q26 ∷
   rw 5 q27 ∷
   rw 6 q40 ∷
   rw 7 q29 ∷
   rw 8 q40 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q30 ∷
   rw 10 q41 ∷
   rw 11 q30 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q26 ∷
   rw 11 q42 ∷
   rw 4 q37 ∷
   re 4 8 (ℓ "乨") ∷
   re 3 3 (ℓ "乧") ∷
   rw 4 q45 ∷
   rw 5 q24 ∷
   rw 6 q23 ∷
   rw 7 q33 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 1985 W
  q47 : Eqn
  q47 = sE 1851 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CZ12-CCZ123
  q48 : Eqn
  q48 = eqn (ℓ "丸丞") (ℓ "丞丸") (low₃-comm ((CZ ↑)) (X))
  q49 : Eqn
  q49 = wE 2036 W

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [CCZ123]: 5 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CCZ123 : ⟪ (ℓ "丞中九丮九丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丞中九丮九丞") ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CCZ123 = derive (ℓ "丞中九丮九丞乜") (ℓ "乜丞中九丮九丞")
  (rw 5 q46 ∷
   rw 1 q47 ∷
   rw⁻ 0 q48 ∷
   rw 1 q46 ∷
   rw 0 q49 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = sE 1855 lem-pass-CZ12-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [CZ12 CCZ123]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ12-CCZ123 : ⟪ (ℓ "丽习举习丸乜") ⟫ʷ ≈ ⟪ (ℓ "丸乜丽习举习") ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ12-CCZ123 = derive (ℓ "丽习举习丸乜") (ℓ "丸乜丽习举习")
  (rw⁻ 0 q50 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = sE 365 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2
  q52 : Eqn
  q52 = sE 293 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2
  q53 : Eqn
  q53 = sE 1853 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3
  q54 : Eqn
  q54 = sE 299 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2
  q55 : Eqn
  q55 = sE 367 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2

-- Bar(SSKSKK;2,3->0) passes split Gad(t=1, W=(2, 3), d=SK, e=-1): 5 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘") (ℓ "丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 0 q51 ∷
   rw 3 q52 ∷
   rw 6 q53 ∷
   rw 14 q54 ∷
   rw 17 q55 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = sE 1856 lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CCZ123

-- pass [CCZ123] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (ℓ "乜丘丞丽习举习丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丽习举习丘丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = derive (ℓ "乜丘丞丽习举习丘丞") (ℓ "丘丞丽习举习丘丞乜")
  (rw⁻ 0 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = sE 446 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-X2
  q58 : Eqn
  q58 = sE 430 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-X2
  q59 : Eqn
  q59 = sE 1854 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3
  q60 : Eqn
  q60 = sE 431 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2
  q61 : Eqn
  q61 = sE 448 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-X2

-- Bar(SSSKSS;2,3->0) passes split Gad(t=1, W=(2, 3), d=SK, e=-1): 5 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘") (ℓ "丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 0 q57 ∷
   rw 3 q58 ∷
   rw 6 q59 ∷
   rw 14 q60 ∷
   rw 17 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = sE 1857 lem-pass-CZ12-CCZ123-vs-CS23-TOFF201-CSd23-TOFF201

-- pass [CS23 TOFF201 CSd23 TOFF201] [CZ12 CCZ123]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CZ12-CCZ123 : ⟪ (ℓ "义乣乊乣丸乜") ⟫ʷ ≈ ⟪ (ℓ "丸乜义乣乊乣") ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CZ12-CCZ123 = derive (ℓ "义乣乊乣丸乜") (ℓ "丸乜义乣乊乣")
  (rw⁻ 0 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = sE 1859 lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-CCZ123

-- pass [CCZ123] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (ℓ "乜丒丘丞中九丮九丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞中九丮九丒丘丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (ℓ "乜丒丘丞中九丮九丒丘丞") (ℓ "丒丘丞中九丮九丒丘丞乜")
  (rw⁻ 0 q63 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = sE 1845 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-X1
  q65 : Eqn
  q65 = sE 1843 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CK10-X1
  q66 : Eqn
  q66 = sE 1858 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q67 : Eqn
  q67 = sE 1844 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CKd10-X1
  q68 : Eqn
  q68 = sE 1846 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CSd01-X1

-- Bar(SSSKSS;1,3->0) passes split Gad(t=0, W=(1, 2, 3), d=SK, e=-1): 5 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒") ⟫ʷ ≈ ⟪ (ℓ "丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒") (ℓ "丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 0 q64 ∷
   rw 3 q65 ∷
   rw 6 q66 ∷
   rw 16 q67 ∷
   rw 19 q68 ∷ []) Eq.refl
