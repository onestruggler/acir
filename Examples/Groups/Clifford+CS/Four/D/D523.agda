{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD523 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D523 (W : Ws) (Sᴰ : SD523) where

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
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part0 : St 362
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part0 = pickᴰ 0 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part1 : St 363
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part1 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part2 : St 364
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part2 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2 : St 365
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2 = pickᴰ 3 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CK31 : St 366
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CK31 = pickᴰ 4 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2 : St 367
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2 = pickᴰ 5 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CKd31 : St 368
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CKd31 = pickᴰ 6 Sᴰ
  lem-AXIOM-LF-at0321-part0 : St 369
  lem-AXIOM-LF-at0321-part0 = pickᴰ 7 Sᴰ
  lem-AXIOM-LF-at0321-part1 : St 370
  lem-AXIOM-LF-at0321-part1 = pickᴰ 8 Sᴰ
  lem-AXIOM-LF-at0321-part2 : St 371
  lem-AXIOM-LF-at0321-part2 = pickᴰ 9 Sᴰ
  lem-AXIOM-LF-at2301-part0 : St 372
  lem-AXIOM-LF-at2301-part0 = pickᴰ 10 Sᴰ
  lem-AXIOM-LF-at2301-part1 : St 373
  lem-AXIOM-LF-at2301-part1 = pickᴰ 11 Sᴰ
  lem-AXIOM-LF-at2301-part2 : St 374
  lem-AXIOM-LF-at2301-part2 = pickᴰ 12 Sᴰ
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~32-⟶0⟩ : St 375
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~32-⟶0⟩ = pickᴰ 13 Sᴰ
  lem-groups-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3 : St 376
  lem-groups-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3 = pickᴰ 14 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF103-X3 : St 377
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF103-X3 = pickᴰ 15 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part0 : St 378
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part0 = pickᴰ 16 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part1 : St 379
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part1 = pickᴰ 17 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part2 : St 380
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part2 = pickᴰ 18 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part3 : St 381
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part3 = pickᴰ 19 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part4 : St 382
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part4 = pickᴰ 20 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part5 : St 383
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part5 = pickᴰ 21 Sᴰ
  lem-comm-CCZ013-CZ12 : St 384
  lem-comm-CCZ013-CZ12 = pickᴰ 22 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part0 : St 385
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part0 = pickᴰ 23 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part1 : St 386
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part1 = pickᴰ 24 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part2 : St 387
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part2 = pickᴰ 25 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part3 : St 388
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part3 = pickᴰ 26 Sᴰ

private
  q1 : Eqn
  q1 = sE 362 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part0
  q2 : Eqn
  q2 = sE 363 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part1
  q3 : Eqn
  q3 = sE 364 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part2

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CSd12 CKd21 CS12 CS12 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丷么丶丶丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷么丶丶丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丷么丶丶丘") (ℓ "丘丷么丶丶丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 0 q1 ∷
   rw 0 q2 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = sE 365 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2
  q5 : Eqn
  q5 = sE 366 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CK31
  q6 : Eqn
  q6 = sE 367 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2
  q7 : Eqn
  q7 = sE 368 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CKd31

-- Bar(SSKSKK;2,3->0) passes comm WBar(KiKiSSSKiSSSSSS;~2,3->1): 4 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-comm-WBar⟨KiKiSSSKiSSSSSS~23-⟶1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丶丘乔丘丷丘乕") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘乔丘丷丘乕丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-comm-WBar⟨KiKiSSSKiSSSSSS~23-⟶1⟩ = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丶丘乔丘丷丘乕") (ℓ "丘丶丘乔丘丷丘乕丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 0 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 7 q7 ∷ []) Eq.refl

private
  q8 : Eqn
  q8 = sE 369 lem-AXIOM-LF-at0321-part0
  q9 : Eqn
  q9 = sE 370 lem-AXIOM-LF-at0321-part1
  q10 : Eqn
  q10 = sE 371 lem-AXIOM-LF-at0321-part2

-- AXIOM LF @0321: 3 steps
lem-AXIOM-LF-at0321 : ⟪ (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临") ⟫ʷ ≈ ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄乢中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠乢中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-AXIOM-LF-at0321 = derive (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临") (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄乢中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠乢中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 0 q8 ∷
   rw 0 q9 ∷
   rw 0 q10 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = sE 372 lem-AXIOM-LF-at2301-part0
  q12 : Eqn
  q12 = sE 373 lem-AXIOM-LF-at2301-part1
  q13 : Eqn
  q13 = sE 374 lem-AXIOM-LF-at2301-part2

-- AXIOM LF @2301: 3 steps
lem-AXIOM-LF-at2301 : ⟪ (ℓ "义义乗义乐丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧为丧丧丧丈丫丧丧丧丧丧丧乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丈丫丧丧丧丧丧丧丧丧丧乐义义义业乗义义义义义义与为") ⟫ʷ ≈ ⟪ (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫乡义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶乡义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为") ⟫ʷ
lem-AXIOM-LF-at2301 = derive (ℓ "义义乗义乐丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧为丧丧丧丈丫丧丧丧丧丧丧乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丈丫丧丧丧丧丧丧丧丧丧乐义义义业乗义义义义义义与为") (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫乡义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶乡义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为")
  (rw 0 q11 ∷
   rw 0 q12 ∷
   rw 0 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q16 : Eqn
  q16 = wE 140 W
  q17 : Eqn
  q17 = wE 7 W
  q18 : Eqn
  q18 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q19 : Eqn
  q19 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q20 : Eqn
  q20 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q21 : Eqn
  q21 = wE 1399 W
  q22 : Eqn
  q22 = wE 27 W
  q23 : Eqn
  q23 = wE 142 W
  q24 : Eqn
  q24 = wE 31 W
  q25 : Eqn
  q25 = sE 375 lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~32-⟶0⟩
  q26 : Eqn
  q26 = wE 1400 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20 X3]: 235 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞") ⟫ʷ ≈ ⟪ (ℓ "丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞") (ℓ "丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 60 q14 ∷
   rw⁻ 59 q15 ∷
   rw 58 q16 ∷
   rw 57 q16 ∷
   rw 56 q17 ∷
   rw 55 q16 ∷
   rw 54 q17 ∷
   rw 53 q17 ∷
   rw⁻ 52 q18 ∷
   rw 51 q17 ∷
   rw 50 q17 ∷
   rw 49 q17 ∷
   rw 48 q17 ∷
   rw 47 q17 ∷
   rw 46 q17 ∷
   rw⁻ 45 q19 ∷
   rw 44 q16 ∷
   rw 43 q17 ∷
   rw 42 q17 ∷
   rw 41 q17 ∷
   rw⁻ 40 q19 ∷
   rw 39 q16 ∷
   rw⁻ 38 q19 ∷
   rw 37 q16 ∷
   rw⁻ 36 q18 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw⁻ 37 q20 ∷
   rw 36 q16 ∷
   rw⁻ 35 q20 ∷
   re 36 3 (ℓ "乔") ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw⁻ 36 q20 ∷
   rw 35 q16 ∷
   rw⁻ 34 q20 ∷
   re 35 3 (ℓ "乔") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q20 ∷
   rw 34 q17 ∷
   rw⁻ 33 q20 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw⁻ 34 q20 ∷
   rw 33 q16 ∷
   rw⁻ 32 q20 ∷
   re 33 3 (ℓ "乔") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q20 ∷
   rw 32 q17 ∷
   rw⁻ 31 q20 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q20 ∷
   rw 31 q17 ∷
   rw⁻ 30 q20 ∷
   re 31 3 (ℓ "丽") ∷
   rw⁻ 29 q15 ∷
   rw 30 q21 ∷
   rw 29 q15 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q20 ∷
   rw 31 q22 ∷
   rw 32 q20 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q20 ∷
   rw 32 q22 ∷
   rw 33 q20 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏乇乏") ∷
   rw 32 q20 ∷
   rw 33 q23 ∷
   rw 34 q20 ∷
   re 32 3 (ℓ "乑") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q20 ∷
   rw 34 q22 ∷
   rw 35 q20 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 34 q20 ∷
   rw 35 q23 ∷
   rw 36 q20 ∷
   re 34 3 (ℓ "乑") ∷
   re 36 1 (ℓ "乏乇乏") ∷
   rw 35 q20 ∷
   rw 36 q23 ∷
   rw 37 q20 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q15 ∷
   rw 37 q15 ∷
   rw 38 q18 ∷
   rw 39 q15 ∷
   rw 40 q23 ∷
   rw 41 q19 ∷
   rw 42 q23 ∷
   rw 43 q19 ∷
   rw 44 q22 ∷
   rw 45 q22 ∷
   rw 46 q22 ∷
   rw 47 q23 ∷
   rw 48 q19 ∷
   rw 49 q22 ∷
   rw 50 q22 ∷
   rw 51 q22 ∷
   rw 52 q22 ∷
   rw 53 q22 ∷
   rw 54 q22 ∷
   rw 55 q15 ∷
   rw 56 q18 ∷
   rw 57 q15 ∷
   rw 58 q22 ∷
   rw 59 q22 ∷
   rw 60 q23 ∷
   rw 61 q22 ∷
   rw 62 q23 ∷
   rw 63 q23 ∷
   rw 64 q24 ∷
   rw 0 q25 ∷
   rw 35 q14 ∷
   rw 34 q16 ∷
   rw 33 q16 ∷
   rw 32 q17 ∷
   rw 31 q16 ∷
   rw 30 q17 ∷
   rw 29 q17 ∷
   rw⁻ 28 q15 ∷
   rw⁻ 27 q18 ∷
   rw⁻ 26 q15 ∷
   rw 25 q17 ∷
   rw 24 q17 ∷
   rw 23 q17 ∷
   rw 22 q17 ∷
   rw 21 q17 ∷
   rw 20 q17 ∷
   rw⁻ 19 q19 ∷
   rw 18 q16 ∷
   rw 17 q17 ∷
   rw 16 q17 ∷
   rw 15 q17 ∷
   rw⁻ 14 q19 ∷
   rw 13 q16 ∷
   rw⁻ 12 q19 ∷
   rw 11 q16 ∷
   rw⁻ 10 q15 ∷
   rw⁻ 9 q18 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 7 q15 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw⁻ 8 q20 ∷
   rw 7 q16 ∷
   rw⁻ 6 q20 ∷
   re 7 3 (ℓ "乔") ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q20 ∷
   rw 6 q16 ∷
   rw⁻ 5 q20 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q20 ∷
   rw 5 q17 ∷
   rw⁻ 4 q20 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q20 ∷
   rw 4 q16 ∷
   rw⁻ 3 q20 ∷
   re 4 3 (ℓ "乔") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q20 ∷
   rw 3 q17 ∷
   rw⁻ 2 q20 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q20 ∷
   rw 2 q17 ∷
   rw⁻ 1 q20 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 0 q15 ∷
   rw 1 q26 ∷
   rw 0 q15 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q20 ∷
   rw 2 q22 ∷
   rw 3 q20 ∷
   re 1 3 (ℓ "中") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q20 ∷
   rw 3 q22 ∷
   rw 4 q20 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏乇乏") ∷
   rw 3 q20 ∷
   rw 4 q23 ∷
   rw 5 q20 ∷
   re 3 3 (ℓ "乑") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q20 ∷
   rw 5 q22 ∷
   rw 6 q20 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q20 ∷
   rw 6 q23 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "乑") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q20 ∷
   rw 7 q23 ∷
   rw 8 q20 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q18 ∷
   rw 8 q23 ∷
   rw 9 q19 ∷
   rw 10 q23 ∷
   rw 11 q19 ∷
   rw 12 q22 ∷
   rw 13 q22 ∷
   rw 14 q22 ∷
   rw 15 q23 ∷
   rw 16 q19 ∷
   rw 17 q22 ∷
   rw 18 q22 ∷
   rw 19 q22 ∷
   rw 20 q22 ∷
   rw 21 q22 ∷
   rw 22 q22 ∷
   rw 23 q18 ∷
   rw 24 q22 ∷
   rw 25 q22 ∷
   rw 26 q23 ∷
   rw 27 q22 ∷
   rw 28 q23 ∷
   rw 29 q23 ∷
   rw 30 q15 ∷
   rw 31 q24 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = sE 377 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF103-X3

-- Bar(SSKSKK;3,1->0) passes factors of X3 TOFF103 X3: 1 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X3-TOFF103-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乡丞") ⟫ʷ ≈ ⟪ (ℓ "丞乡丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X3-TOFF103-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乡丞") (ℓ "丞乡丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = sE 376 lem-groups-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3

-- pass [CK32 CS23 CS23 CKd32] [X3 TOFF123 X3]: 1 steps
lem-pass-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3 : ⟪ (ℓ "乗义义乘丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞乗义义乘") ⟫ʷ
lem-pass-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3 = derive (ℓ "乗义义乘丞乢丞") (ℓ "丞乢丞乗义义乘")
  (rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = sE 378 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part0
  q30 : Eqn
  q30 = sE 379 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part1
  q31 : Eqn
  q31 = sE 380 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part2
  q32 : Eqn
  q32 = sE 381 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part3
  q33 : Eqn
  q33 = sE 382 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part4
  q34 : Eqn
  q34 = sE 383 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part5

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->2) passes white iX via V2 conjugates 1: 6 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1 : ⟪ (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫") ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1 = derive (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫")
  (rw 0 q29 ∷
   rw 0 q30 ∷
   rw 0 q31 ∷
   rw 0 q32 ∷
   rw 0 q33 ∷
   rw 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = sE 384 lem-comm-CCZ013-CZ12

-- pass [CCZ013] [CZ12]: 1 steps
lem-pass-CCZ013-vs-CZ12 : ⟪ (ℓ "乚丸") ⟫ʷ ≈ ⟪ (ℓ "丸乚") ⟫ʷ
lem-pass-CCZ013-vs-CZ12 = derive (ℓ "乚丸") (ℓ "丸乚")
  (rw 0 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = sE 385 lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part0
  q37 : Eqn
  q37 = sE 386 lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part1
  q38 : Eqn
  q38 = sE 387 lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part2
  q39 : Eqn
  q39 = sE 388 lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part3

-- Bar(SSSKSS;3,1->0) passes white iX via V2 conjugates 2: 4 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 0 q36 ∷
   rw 0 q37 ∷
   rw 0 q38 ∷
   rw 0 q39 ∷ []) Eq.refl
