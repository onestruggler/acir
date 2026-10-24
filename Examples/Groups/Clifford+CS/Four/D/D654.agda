{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD654 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D654 (W : Ws) (Sᴰ : SD654) where

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
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-CKd21-CS12-CS12-X2 : St 1675
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-CKd21-CS12-CS12-X2 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-CS23-CS23-CKd32-X3 : St 398
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-CS23-CS23-CKd32-X3 = pickᴰ 1 Sᴰ
  lem-pass-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3 : St 975
  lem-pass-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X3 : St 999
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X3 = pickᴰ 3 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X3 : St 1676
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X3 = pickᴰ 4 Sᴰ
  lem-pass-CK21-CS12-CS12-CKd21-vs-X2-TOFF312-X2 : St 991
  lem-pass-CK21-CS12-CS12-CKd21-vs-X2-TOFF312-X2 = pickᴰ 5 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF023-X3 : St 1230
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF023-X3 = pickᴰ 6 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-X2 : St 1241
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-X2 = pickᴰ 7 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF012-X2 : St 1266
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF012-X2 = pickᴰ 8 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF023-X3 : St 1286
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF023-X3 = pickᴰ 9 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-X2 : St 1677
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-X2 = pickᴰ 10 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF012-X2 : St 1292
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF012-X2 = pickᴰ 11 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3 : St 1664
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3 = pickᴰ 12 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2 : St 1678
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2 = pickᴰ 13 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-X2 : St 1679
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-X2 = pickᴰ 14 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X3 : St 1680
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X3 = pickᴰ 15 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X3 : St 1681
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X3 = pickᴰ 16 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF203-X3 : St 1682
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF203-X3 = pickᴰ 17 Sᴰ
  lem-pass-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-vs-X2-TOFF312-X2 : St 1683
  lem-pass-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-vs-X2-TOFF312-X2 = pickᴰ 18 Sᴰ
  lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-TOFF123-X3 : St 1684
  lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-TOFF123-X3 = pickᴰ 19 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2 : St 1685
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2 = pickᴰ 20 Sᴰ
  lem-pass-X3-TOFF302-X3-vs-X2-TOFF312-X2 : St 1686
  lem-pass-X3-TOFF302-X3-vs-X2-TOFF312-X2 = pickᴰ 21 Sᴰ

private
  q1 : Eqn
  q1 = sE 1675 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-CKd21-CS12-CS12-X2
  q2 : Eqn
  q2 = sE 1679 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-X2

-- Bar(SSSKSS;2,1->0) passes factors of X2 X3 CS12 CS12 CK21 CS12 CK21 CK21 CX23 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CK31 CS13 CK31 CK31 X2 X3: 2 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-factors-of-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丷么丶丶丘丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷么丶丶丘丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-factors-of-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X2-X3 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丷么丶丶丘丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘") (ℓ "丘丷么丶丶丘丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q1 ∷
   rw 6 q2 ∷ []) Eq.refl

private
  q3 : Eqn
  q3 = sE 1266 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF012-X2
  q4 : Eqn
  q4 = sE 1678 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2
  q5 : Eqn
  q5 = sE 1241 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-X2

-- Bar(SSKSKK;2,3->0) passes Fredkin WBar(SSKSKK;~2,0->1): 7 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~20-⟶1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘九丘丘习丘丘九丘丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丘九丘丘习丘丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘丘习丘丘九丘丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丘九丘丘习丘丘九丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~20-⟶1⟩ = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘九丘丘习丘丘九丘丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丘九丘丘习丘丘九丘") (ℓ "丘九丘丘习丘丘九丘丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丘九丘丘习丘丘九丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 0 q3 ∷
   rw 3 q4 ∷
   rw 6 q3 ∷
   rw 9 q5 ∷
   rw 40 q3 ∷
   rw 43 q4 ∷
   rw 46 q3 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = sE 1230 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF023-X3
  q7 : Eqn
  q7 = sE 1664 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3
  q8 : Eqn
  q8 = sE 999 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X3

-- Bar(SSKSKK;3,1->0) passes Fredkin WBar(SSKSKK;~3,0->2): 7 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶2⟩ : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞也丞丞乤丞丞也丞丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丞也丞丞乤丞丞也丞") ⟫ʷ ≈ ⟪ (ℓ "丞也丞丞乤丞丞也丞丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丞也丞丞乤丞丞也丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶2⟩ = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞也丞丞乤丞丞也丞丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丞也丞丞乤丞丞也丞") (ℓ "丞也丞丞乤丞丞也丞丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丞也丞丞乤丞丞也丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 0 q6 ∷
   rw 3 q7 ∷
   rw 6 q6 ∷
   rw 9 q8 ∷
   rw 40 q6 ∷
   rw 43 q7 ∷
   rw 46 q6 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = wE 5 W
  q10 : Eqn
  q10 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q11 : Eqn
  q11 = wE 772 W
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q14 : Eqn
  q14 = wE 6 W
  q15 : Eqn
  q15 = wE 481 W
  q16 : Eqn
  q16 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q17 : Eqn
  q17 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q18 : Eqn
  q18 = wE 1616 W
  q19 : Eqn
  q19 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q20 : Eqn
  q20 = wE 39 W
  q21 : Eqn
  q21 = wE 329 W
  q22 : Eqn
  q22 = wE 315 W
  q23 : Eqn
  q23 = wE 27 W
  q24 : Eqn
  q24 = wE 31 W
  q25 : Eqn
  q25 = sE 975 lem-pass-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3
  q26 : Eqn
  q26 = sE 1684 lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-TOFF123-X3
  q27 : Eqn
  q27 = wE 1617 W

-- pass [X2 CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02 X2] [X3 TOFF123 X3]: 177 steps
lem-pass-X2-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-vs-X3-TOFF123-X3 : ⟪ (ℓ "丘义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞丘义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘") ⟫ʷ
lem-pass-X2-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-vs-X3-TOFF123-X3 = derive (ℓ "丘义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘丞乢丞") (ℓ "丞乢丞丘义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘")
  (rw 31 q9 ∷
   rw⁻ 30 q10 ∷
   rw 29 q11 ∷
   rw 28 q11 ∷
   rw 27 q12 ∷
   rw 26 q11 ∷
   rw 25 q12 ∷
   rw 24 q12 ∷
   re 23 1 (ℓ "乏乃乏") ∷
   rw⁻ 25 q13 ∷
   rw 24 q14 ∷
   rw⁻ 23 q13 ∷
   re 24 3 (ℓ "乓") ∷
   rw 22 q12 ∷
   rw 21 q12 ∷
   rw 20 q12 ∷
   rw 19 q12 ∷
   rw 18 q12 ∷
   rw 17 q12 ∷
   rw 16 q15 ∷
   rw 15 q11 ∷
   rw 14 q12 ∷
   rw 13 q12 ∷
   rw 12 q12 ∷
   rw 11 q15 ∷
   rw 10 q11 ∷
   rw 9 q15 ∷
   rw 8 q11 ∷
   re 7 1 (ℓ "乏乃乏") ∷
   rw⁻ 9 q13 ∷
   rw 8 q14 ∷
   rw⁻ 7 q13 ∷
   re 8 3 (ℓ "乓") ∷
   rw⁻ 6 q16 ∷
   rw⁻ 5 q16 ∷
   rw⁻ 4 q17 ∷
   rw⁻ 3 q16 ∷
   rw⁻ 2 q17 ∷
   rw⁻ 1 q17 ∷
   rw⁻ 0 q10 ∷
   rw 1 q18 ∷
   rw 0 q16 ∷
   rw 1 q17 ∷
   rw 2 q17 ∷
   rw 3 q19 ∷
   rw 4 q17 ∷
   rw 5 q17 ∷
   rw 6 q16 ∷
   rw 7 q17 ∷
   rw 8 q16 ∷
   rw 9 q16 ∷
   re 11 1 (ℓ "乏乆乏") ∷
   rw 10 q13 ∷
   rw 11 q20 ∷
   rw 12 q13 ∷
   re 10 3 (ℓ "乐") ∷
   rw 11 q21 ∷
   rw 12 q22 ∷
   rw 13 q21 ∷
   rw 14 q22 ∷
   rw 15 q23 ∷
   rw 16 q23 ∷
   rw 17 q23 ∷
   rw 18 q21 ∷
   rw 19 q22 ∷
   rw 20 q23 ∷
   rw 21 q23 ∷
   rw 22 q23 ∷
   rw 23 q23 ∷
   rw 24 q23 ∷
   rw 25 q23 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q13 ∷
   rw 27 q20 ∷
   rw 28 q13 ∷
   re 26 3 (ℓ "乐") ∷
   rw 27 q23 ∷
   rw 28 q23 ∷
   rw 29 q21 ∷
   rw 30 q23 ∷
   rw 31 q21 ∷
   rw 32 q21 ∷
   rw 33 q16 ∷
   rw 34 q17 ∷
   rw 35 q17 ∷
   rw 36 q19 ∷
   rw 37 q24 ∷
   rw 33 q25 ∷
   rw 4 q26 ∷
   rw 0 q25 ∷
   rw 40 q9 ∷
   rw⁻ 39 q19 ∷
   rw⁻ 38 q17 ∷
   rw⁻ 37 q17 ∷
   rw⁻ 36 q16 ∷
   rw 35 q11 ∷
   rw 34 q11 ∷
   rw 33 q12 ∷
   rw 32 q11 ∷
   rw 31 q12 ∷
   rw 30 q12 ∷
   re 29 1 (ℓ "乏乃乏") ∷
   rw⁻ 31 q13 ∷
   rw 30 q14 ∷
   rw⁻ 29 q13 ∷
   re 30 3 (ℓ "乓") ∷
   rw 28 q12 ∷
   rw 27 q12 ∷
   rw 26 q12 ∷
   rw 25 q12 ∷
   rw 24 q12 ∷
   rw 23 q12 ∷
   rw 22 q15 ∷
   rw 21 q11 ∷
   rw 20 q12 ∷
   rw 19 q12 ∷
   rw 18 q12 ∷
   rw 17 q15 ∷
   rw 16 q11 ∷
   rw 15 q15 ∷
   rw 14 q11 ∷
   re 13 1 (ℓ "乏乃乏") ∷
   rw⁻ 15 q13 ∷
   rw 14 q14 ∷
   rw⁻ 13 q13 ∷
   re 14 3 (ℓ "乓") ∷
   rw⁻ 12 q16 ∷
   rw⁻ 11 q16 ∷
   rw⁻ 10 q17 ∷
   rw⁻ 9 q16 ∷
   rw⁻ 8 q17 ∷
   rw⁻ 7 q17 ∷
   rw⁻ 6 q19 ∷
   rw⁻ 5 q17 ∷
   rw⁻ 4 q17 ∷
   rw⁻ 3 q16 ∷
   rw 4 q27 ∷
   rw 3 q10 ∷
   rw 4 q17 ∷
   rw 5 q17 ∷
   rw 6 q16 ∷
   rw 7 q17 ∷
   rw 8 q16 ∷
   rw 9 q16 ∷
   re 11 1 (ℓ "乏乆乏") ∷
   rw 10 q13 ∷
   rw 11 q20 ∷
   rw 12 q13 ∷
   re 10 3 (ℓ "乐") ∷
   rw 11 q21 ∷
   rw 12 q22 ∷
   rw 13 q21 ∷
   rw 14 q22 ∷
   rw 15 q23 ∷
   rw 16 q23 ∷
   rw 17 q23 ∷
   rw 18 q21 ∷
   rw 19 q22 ∷
   rw 20 q23 ∷
   rw 21 q23 ∷
   rw 22 q23 ∷
   rw 23 q23 ∷
   rw 24 q23 ∷
   rw 25 q23 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q13 ∷
   rw 27 q20 ∷
   rw 28 q13 ∷
   re 26 3 (ℓ "乐") ∷
   rw 27 q23 ∷
   rw 28 q23 ∷
   rw 29 q21 ∷
   rw 30 q23 ∷
   rw 31 q21 ∷
   rw 32 q21 ∷
   rw 33 q10 ∷
   rw 34 q24 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = sE 1286 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF023-X3
  q29 : Eqn
  q29 = sE 1682 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF203-X3
  q30 : Eqn
  q30 = sE 1676 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X3

-- Bar(SSSKSS;3,1->0) passes Fredkin WBar(SSKSKK;~3,0->2): 7 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶2⟩ : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞也丞丞乤丞丞也丞丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丞也丞丞乤丞丞也丞") ⟫ʷ ≈ ⟪ (ℓ "丞也丞丞乤丞丞也丞丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丞也丞丞乤丞丞也丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶2⟩ = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞也丞丞乤丞丞也丞丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丞也丞丞乤丞丞也丞") (ℓ "丞也丞丞乤丞丞也丞丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丞也丞丞乤丞丞也丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 0 q28 ∷
   rw 3 q29 ∷
   rw 6 q28 ∷
   rw 9 q30 ∷
   rw 40 q28 ∷
   rw 43 q29 ∷
   rw 46 q28 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = sE 398 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-CS23-CS23-CKd32-X3
  q32 : Eqn
  q32 = sE 1681 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X3

-- Bar(SSKSKK;3,2->0) passes factors of X2 X3 CS23 CS23 CS23 CK32 CS23 CS23 CX31 CS12 CS12 CS12 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CS12 CK12 CS12 CS12 X2 X3: 3 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X2-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗义义乘丞丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞丞乗义义乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗义义乘丞丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞丞乗义义乘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X2-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗义义乘丞丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞丞乗义义乘丞") (ℓ "丞乗义义乘丞丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞丞乗义义乘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q31 ∷
   rw 6 q32 ∷
   rw 39 q31 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = sE 1680 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X3

-- Bar(SSKSKK;3,2->0) passes factors of X2 X3 CS23 CS23 CK32 CS23 CK32 CK32 CX31 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CK12 CS12 CK12 CK12 X2 X3: 3 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗义义乘丞丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞丞乗义义乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗义义乘丞丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞丞乗义义乘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗义义乘丞丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞丞乗义义乘丞") (ℓ "丞乗义义乘丞丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞丞乗义义乘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q31 ∷
   rw 6 q33 ∷
   rw 37 q31 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 1974 W
  q35 : Eqn
  q35 = sE 991 lem-pass-CK21-CS12-CS12-CKd21-vs-X2-TOFF312-X2
  q36 : Eqn
  q36 = sE 1683 lem-pass-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-vs-X2-TOFF312-X2
  q37 : Eqn
  q37 = wE 1975 W

-- pass [X1 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X1] [X2 TOFF312 X2]: 5 steps
lem-pass-X1-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-vs-X2-TOFF312-X2 : ⟪ (ℓ "丒丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘乨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乨丘丒丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒") ⟫ʷ
lem-pass-X1-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-vs-X2-TOFF312-X2 = derive (ℓ "丒丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘乨丘") (ℓ "丘乨丘丒丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒")
  (rw 0 q34 ∷
   rw 33 q35 ∷
   rw 4 q36 ∷
   rw 0 q35 ∷
   rw 3 q37 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = wE 1784 W
  q39 : Eqn
  q39 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q40 : Eqn
  q40 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q41 : Eqn
  q41 = wE 30 W
  q42 : Eqn
  q42 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q43 : Eqn
  q43 = wE 122 W
  q44 : Eqn
  q44 = wE 127 W
  q45 : Eqn
  q45 = wE 74 W
  q46 : Eqn
  q46 = wE 337 W
  q47 : Eqn
  q47 = wE 1976 W
  q48 : Eqn
  q48 = wE 24 W
  q49 : Eqn
  q49 = wE 25 W
  q50 : Eqn
  q50 = wE 124 W
  q51 : Eqn
  q51 = sE 1686 lem-pass-X3-TOFF302-X3-vs-X2-TOFF312-X2
  q52 : Eqn
  q52 = wE 1977 W
  q53 : Eqn
  q53 = wE 1787 W

-- pass [TOFF312] [X2 X3 TOFF302 X2 X3]: 141 steps
lem-pass-TOFF312-vs-X2-X3-TOFF302-X2-X3 : ⟪ (ℓ "乨丘丞乧丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞乧丘丞乨") ⟫ʷ
lem-pass-TOFF312-vs-X2-X3-TOFF302-X2-X3 = derive (ℓ "乨丘丞乧丘丞") (ℓ "丘丞乧丘丞乨")
  (rw 0 q38 ∷
   rw 10 q9 ∷
   rw⁻ 9 q39 ∷
   rw⁻ 8 q10 ∷
   re 7 1 (ℓ "並乨並") ∷
   re 8 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 7 q40 ∷
   rw 8 q17 ∷
   rw 9 q41 ∷
   rw 10 q42 ∷
   rw 11 q41 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q13 ∷
   rw 13 q23 ∷
   rw 14 q13 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q40 ∷
   rw 14 q43 ∷
   rw 15 q24 ∷
   rw 14 q44 ∷
   rw⁻ 13 q40 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q13 ∷
   rw 13 q12 ∷
   rw⁻ 12 q13 ∷
   re 13 3 (ℓ "丽") ∷
   rw 11 q45 ∷
   rw⁻ 10 q42 ∷
   rw 9 q45 ∷
   rw⁻ 8 q17 ∷
   rw⁻ 7 q40 ∷
   rw 8 q46 ∷
   re 8 8 (ℓ "乨") ∷
   rw⁻ 6 q39 ∷
   rw⁻ 5 q10 ∷
   rw⁻ 4 q10 ∷
   rw 5 q47 ∷
   rw 4 q39 ∷
   re 6 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 5 q40 ∷
   rw 6 q17 ∷
   rw 7 q41 ∷
   rw 8 q42 ∷
   rw 9 q41 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q13 ∷
   rw 11 q23 ∷
   rw 12 q13 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q40 ∷
   rw 12 q43 ∷
   rw 5 q9 ∷
   rw 6 q40 ∷
   rw 7 q17 ∷
   rw 8 q48 ∷
   rw 9 q42 ∷
   rw 10 q48 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q13 ∷
   rw 12 q49 ∷
   rw 13 q13 ∷
   re 11 3 (ℓ "丽") ∷
   rw 12 q40 ∷
   rw 13 q50 ∷
   rw 6 q46 ∷
   re 6 8 (ℓ "乨") ∷
   re 5 3 (ℓ "乧") ∷
   rw 6 q39 ∷
   rw 7 q10 ∷
   rw 8 q24 ∷
   rw⁻ 1 q51 ∷
   rw 4 q9 ∷
   rw⁻ 3 q39 ∷
   re 2 1 (ℓ "並乨並") ∷
   re 3 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 2 q40 ∷
   rw 3 q17 ∷
   rw 4 q41 ∷
   rw 5 q42 ∷
   rw 6 q41 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q13 ∷
   rw 8 q23 ∷
   rw 9 q13 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q40 ∷
   rw 9 q43 ∷
   rw 10 q24 ∷
   rw 9 q44 ∷
   rw⁻ 8 q40 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q13 ∷
   rw 8 q12 ∷
   rw⁻ 7 q13 ∷
   re 8 3 (ℓ "丽") ∷
   rw 6 q45 ∷
   rw⁻ 5 q42 ∷
   rw 4 q45 ∷
   rw⁻ 3 q17 ∷
   rw⁻ 2 q40 ∷
   rw 3 q46 ∷
   re 3 8 (ℓ "乨") ∷
   rw⁻ 1 q39 ∷
   rw⁻ 0 q10 ∷
   rw 1 q52 ∷
   rw 0 q10 ∷
   rw 1 q39 ∷
   re 3 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 2 q40 ∷
   rw 3 q17 ∷
   rw 4 q41 ∷
   rw 5 q42 ∷
   rw 6 q41 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q13 ∷
   rw 8 q23 ∷
   rw 9 q13 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q40 ∷
   rw 9 q43 ∷
   rw 2 q9 ∷
   rw 3 q40 ∷
   rw 4 q17 ∷
   rw 5 q48 ∷
   rw 6 q42 ∷
   rw 7 q48 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q13 ∷
   rw 9 q49 ∷
   rw 10 q13 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q40 ∷
   rw 10 q50 ∷
   rw 3 q46 ∷
   re 3 8 (ℓ "乨") ∷
   re 2 3 (ℓ "乧") ∷
   rw 3 q10 ∷
   rw 4 q39 ∷
   rw 5 q10 ∷
   rw 6 q24 ∷
   rw 5 q53 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = sE 1292 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF012-X2
  q55 : Eqn
  q55 = sE 1685 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2
  q56 : Eqn
  q56 = sE 1677 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-X2

-- Bar(SSSKSS;2,3->0) passes Fredkin WBar(SSKSKK;~2,0->1): 7 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~20-⟶1⟩ : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘九丘丘习丘丘九丘丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丘九丘丘习丘丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘丘习丘丘九丘丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丘九丘丘习丘丘九丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~20-⟶1⟩ = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘九丘丘习丘丘九丘丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丘九丘丘习丘丘九丘") (ℓ "丘九丘丘习丘丘九丘丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丘九丘丘习丘丘九丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 0 q54 ∷
   rw 3 q55 ∷
   rw 6 q54 ∷
   rw 9 q56 ∷
   rw 40 q54 ∷
   rw 43 q55 ∷
   rw 46 q54 ∷ []) Eq.refl
