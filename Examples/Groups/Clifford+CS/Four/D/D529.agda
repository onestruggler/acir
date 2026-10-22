{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD529 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D529 (W : Ws) (Sᴰ : SD529) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CCZ012-CZ13 : St 573
  lem-comm-CCZ012-CZ13 = pickᴰ 0 Sᴰ
  lem-pass-CZ12-vs-CS03 : St 574
  lem-pass-CZ12-vs-CS03 = pickᴰ 1 Sᴰ
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 38
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 2 Sᴰ
  lem-pass-X3-CK31-X3-vs-CS02 : St 114
  lem-pass-X3-CK31-X3-vs-CS02 = pickᴰ 3 Sᴰ
  lem-pass-X3-CK31-X3-vs-CSd02 : St 115
  lem-pass-X3-CK31-X3-vs-CSd02 = pickᴰ 4 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS02 : St 117
  lem-pass-X3-CKd31-X3-vs-CS02 = pickᴰ 5 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CSd02 : St 118
  lem-pass-X3-CKd31-X3-vs-CSd02 = pickᴰ 6 Sᴰ
  lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : St 136
  lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 7 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CS01 : St 139
  lem-pass-X3-CKd32-X3-vs-CS01 = pickᴰ 8 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CSd01 : St 140
  lem-pass-X3-CKd32-X3-vs-CSd01 = pickᴰ 9 Sᴰ
  lem-pass-X3-CK32-X3-vs-CS01 : St 154
  lem-pass-X3-CK32-X3-vs-CS01 = pickᴰ 10 Sᴰ
  lem-pass-X3-CK32-X3-vs-CSd01 : St 155
  lem-pass-X3-CK32-X3-vs-CSd01 = pickᴰ 11 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-CKd21-CS12-CS12-X2 : St 575
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-CKd21-CS12-CS12-X2 = pickᴰ 12 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF302-X2 : St 356
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF302-X2 = pickᴰ 13 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF302-X2 : St 437
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF302-X2 = pickᴰ 14 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-CS12-CS12-CKd21-X2 : St 450
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-CS12-CS12-CKd21-X2 = pickᴰ 15 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part0 : St 576
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part0 = pickᴰ 16 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part1 : St 577
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part1 = pickᴰ 17 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part2 : St 578
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part2 = pickᴰ 18 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part3 : St 579
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part3 = pickᴰ 19 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part4 : St 580
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part4 = pickᴰ 20 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CX23-X2 : St 581
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CX23-X2 = pickᴰ 21 Sᴰ
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part0 : St 582
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part0 = pickᴰ 22 Sᴰ
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part1 : St 583
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part1 = pickᴰ 23 Sᴰ
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part2 : St 584
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part2 = pickᴰ 24 Sᴰ
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part3 : St 585
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part3 = pickᴰ 25 Sᴰ
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part4 : St 586
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part4 = pickᴰ 26 Sᴰ
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part5 : St 587
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part5 = pickᴰ 27 Sᴰ
  lem-groups-CX23-vs-X2-TOFF312-X2 : St 588
  lem-groups-CX23-vs-X2-TOFF312-X2 = pickᴰ 28 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part0 : St 589
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part0 = pickᴰ 29 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part1 : St 590
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part1 = pickᴰ 30 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part2 : St 591
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part2 = pickᴰ 31 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part3 : St 592
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part3 = pickᴰ 32 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part4 : St 593
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part4 = pickᴰ 33 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part5 : St 594
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part5 = pickᴰ 34 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2 : St 595
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2 = pickᴰ 35 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CX23-X2 : St 596
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CX23-X2 = pickᴰ 36 Sᴰ
  lem-pass-CZ12-vs-CSd03 : St 597
  lem-pass-CZ12-vs-CSd03 = pickᴰ 37 Sᴰ
  lem-pass-X3-CK32-X3-vs-TOFF123 : St 598
  lem-pass-X3-CK32-X3-vs-TOFF123 = pickᴰ 38 Sᴰ
  lem-pass-X3-CKd32-X3-vs-TOFF123 : St 599
  lem-pass-X3-CKd32-X3-vs-TOFF123 = pickᴰ 39 Sᴰ
  lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 : St 600
  lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 40 Sᴰ
  lem-pass-X2-CK23-X2-vs-CS01 : St 601
  lem-pass-X2-CK23-X2-vs-CS01 = pickᴰ 41 Sᴰ
  lem-pass-X2-CK23-X2-vs-CSd01 : St 602
  lem-pass-X2-CK23-X2-vs-CSd01 = pickᴰ 42 Sᴰ
  lem-pass-X2-CK23-X2-vs-TOFF123 : St 603
  lem-pass-X2-CK23-X2-vs-TOFF123 = pickᴰ 43 Sᴰ
  lem-pass-X2-CKd23-X2-vs-CS01 : St 604
  lem-pass-X2-CKd23-X2-vs-CS01 = pickᴰ 44 Sᴰ
  lem-pass-X2-CKd23-X2-vs-CSd01 : St 605
  lem-pass-X2-CKd23-X2-vs-CSd01 = pickᴰ 45 Sᴰ
  lem-pass-X2-CKd23-X2-vs-TOFF123 : St 606
  lem-pass-X2-CKd23-X2-vs-TOFF123 = pickᴰ 46 Sᴰ
  lem-pass-X2-CS23-X2-vs-CS01 : St 607
  lem-pass-X2-CS23-X2-vs-CS01 = pickᴰ 47 Sᴰ
  lem-pass-X2-CS23-X2-vs-CSd01 : St 608
  lem-pass-X2-CS23-X2-vs-CSd01 = pickᴰ 48 Sᴰ
  lem-pass-X2-CS23-X2-vs-TOFF123 : St 609
  lem-pass-X2-CS23-X2-vs-TOFF123 = pickᴰ 49 Sᴰ
  lem-pass-X2-CSd23-X2-vs-CS01 : St 610
  lem-pass-X2-CSd23-X2-vs-CS01 = pickᴰ 50 Sᴰ
  lem-pass-X2-CSd23-X2-vs-CSd01 : St 611
  lem-pass-X2-CSd23-X2-vs-CSd01 = pickᴰ 51 Sᴰ
  lem-pass-X2-CSd23-X2-vs-TOFF123 : St 612
  lem-pass-X2-CSd23-X2-vs-TOFF123 = pickᴰ 52 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-TOFF102-X2 : St 613
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-TOFF102-X2 = pickᴰ 53 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-X3 : St 614
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-X3 = pickᴰ 54 Sᴰ
  lem-comm-CCZ013-CSd23 : St 615
  lem-comm-CCZ013-CSd23 = pickᴰ 55 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd13-X3 : St 616
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd13-X3 = pickᴰ 56 Sᴰ
  lem-pass-X3-CK31-X3-vs-TOFF213 : St 617
  lem-pass-X3-CK31-X3-vs-TOFF213 = pickᴰ 57 Sᴰ
  lem-pass-X3-CKd31-X3-vs-TOFF213 : St 618
  lem-pass-X3-CKd31-X3-vs-TOFF213 = pickᴰ 58 Sᴰ
  lem-comm-CCZ012-CZ23 : St 619
  lem-comm-CCZ012-CZ23 = pickᴰ 59 Sᴰ
  lem-pass-X1-CK13-X1-vs-CS02 : St 620
  lem-pass-X1-CK13-X1-vs-CS02 = pickᴰ 60 Sᴰ
  lem-pass-X1-CK13-X1-vs-CSd02 : St 621
  lem-pass-X1-CK13-X1-vs-CSd02 = pickᴰ 61 Sᴰ
  lem-pass-X1-CK13-X1-vs-TOFF013 : St 622
  lem-pass-X1-CK13-X1-vs-TOFF013 = pickᴰ 62 Sᴰ
  lem-pass-X1-CKd13-X1-vs-CS02 : St 623
  lem-pass-X1-CKd13-X1-vs-CS02 = pickᴰ 63 Sᴰ
  lem-pass-X1-CKd13-X1-vs-CSd02 : St 624
  lem-pass-X1-CKd13-X1-vs-CSd02 = pickᴰ 64 Sᴰ
  lem-pass-X1-CKd13-X1-vs-TOFF013 : St 625
  lem-pass-X1-CKd13-X1-vs-TOFF013 = pickᴰ 65 Sᴰ
  lem-pass-X1-CS13-X1-vs-CS02 : St 626
  lem-pass-X1-CS13-X1-vs-CS02 = pickᴰ 66 Sᴰ
  lem-pass-X1-CS13-X1-vs-CSd02 : St 627
  lem-pass-X1-CS13-X1-vs-CSd02 = pickᴰ 67 Sᴰ
  lem-pass-X1-CS13-X1-vs-TOFF013 : St 628
  lem-pass-X1-CS13-X1-vs-TOFF013 = pickᴰ 68 Sᴰ
  lem-pass-X1-CSd13-X1-vs-CS02 : St 629
  lem-pass-X1-CSd13-X1-vs-CS02 = pickᴰ 69 Sᴰ
  lem-pass-X1-CSd13-X1-vs-CSd02 : St 630
  lem-pass-X1-CSd13-X1-vs-CSd02 = pickᴰ 70 Sᴰ
  lem-pass-X1-CSd13-X1-vs-TOFF013 : St 631
  lem-pass-X1-CSd13-X1-vs-TOFF013 = pickᴰ 71 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-TOFF102-X2 : St 632
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-TOFF102-X2 = pickᴰ 72 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS13-X3 : St 633
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS13-X3 = pickᴰ 73 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd13-X3 : St 634
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd13-X3 = pickᴰ 74 Sᴰ
  lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 : St 635
  lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 75 Sᴰ
  lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 : St 636
  lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 76 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-TOFF102-X0-X2 : St 637
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-TOFF102-X0-X2 = pickᴰ 77 Sᴰ

private
  q1 : Eqn
  q1 = sE 576 lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part0
  q2 : Eqn
  q2 = sE 577 lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part1
  q3 : Eqn
  q3 = sE 578 lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part2
  q4 : Eqn
  q4 = sE 579 lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part3
  q5 : Eqn
  q5 = sE 580 lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part4

-- Bar(SSKSKK;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0): 5 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩ : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩ = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 0 q1 ∷
   rw 0 q2 ∷
   rw 0 q3 ∷
   rw 0 q4 ∷
   rw 0 q5 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = sE 581 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CX23-X2
  q7 : Eqn
  q7 = sE 356 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF302-X2

-- Bar(SSKSKK;2,3->0) passes factors of X0 X2 X3 TOFF302 X0 X2 X3: 2 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X0-X2-X3-TOFF302-X0-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ Toff302 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CX23 ∷ X2 ∷ X2 ∷ Toff302 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X0-X2-X3-TOFF302-X0-X2-X3 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ Toff302 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ X2 ∷ Toff302 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 0 q6 ∷
   rw 3 q7 ∷ []) Eq.refl

private
  q8 : Eqn
  q8 = sE 582 lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part0
  q9 : Eqn
  q9 = sE 583 lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part1
  q10 : Eqn
  q10 = sE 584 lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part2
  q11 : Eqn
  q11 = sE 585 lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part3
  q12 : Eqn
  q12 = sE 586 lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part4
  q13 : Eqn
  q13 = sE 587 lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part5

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];2,0->1) passes white iX via V2 conjugates 3: 6 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3 : ⟪ (CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3 = derive (CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  (rw 0 q8 ∷
   rw 0 q9 ∷
   rw 0 q10 ∷
   rw 0 q11 ∷
   rw 0 q12 ∷
   rw 0 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = sE 588 lem-groups-CX23-vs-X2-TOFF312-X2

-- pass [CX23] [X2 TOFF312 X2]: 1 steps
lem-pass-CX23-vs-X2-TOFF312-X2 : ⟪ (CX23 ∷ X2 ∷ Toff312 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff312 ∷ X2 ∷ CX23 ∷ []) ⟫ʷ
lem-pass-CX23-vs-X2-TOFF312-X2 = derive (CX23 ∷ X2 ∷ Toff312 ∷ X2 ∷ []) (X2 ∷ Toff312 ∷ X2 ∷ CX23 ∷ [])
  (rw 0 q14 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = sE 589 lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part0
  q16 : Eqn
  q16 = sE 590 lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part1
  q17 : Eqn
  q17 = sE 591 lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part2
  q18 : Eqn
  q18 = sE 592 lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part3
  q19 : Eqn
  q19 = sE 593 lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part4
  q20 : Eqn
  q20 = sE 594 lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part5

-- Bar(SSSKSS;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0): 6 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩ : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩ = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 0 q15 ∷
   rw 0 q16 ∷
   rw 0 q17 ∷
   rw 0 q18 ∷
   rw 0 q19 ∷
   rw 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = sE 596 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CX23-X2
  q22 : Eqn
  q22 = sE 437 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF302-X2

-- Bar(SSSKSS;2,3->0) passes factors of X0 X2 X3 TOFF302 X0 X2 X3: 2 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X2-X3-TOFF302-X0-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ Toff302 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CX23 ∷ X2 ∷ X2 ∷ Toff302 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X2-X3-TOFF302-X0-X2-X3 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ Toff302 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ X2 ∷ Toff302 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 0 q21 ∷
   rw 3 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = sE 450 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-CS12-CS12-CKd21-X2
  q24 : Eqn
  q24 = sE 575 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-CKd21-CS12-CS12-X2
  q25 : Eqn
  q25 = sE 595 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2

-- Bar(SSKSKK;2,1->0) passes factors of X0 X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X0 X1 X2: 4 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 0 q23 ∷
   rw 6 q24 ∷
   rw 12 q25 ∷
   rw 88 q23 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = sE 139 lem-pass-X3-CKd32-X3-vs-CS01
  q27 : Eqn
  q27 = sE 599 lem-pass-X3-CKd32-X3-vs-TOFF123
  q28 : Eqn
  q28 = sE 140 lem-pass-X3-CKd32-X3-vs-CSd01

-- pass [X3 CKd32 X3] [CS01 TOFF123 CSd01 TOFF123]: 4 steps
lem-pass-X3-CKd32-X3-vs-CS01-TOFF123-CSd01-TOFF123 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS01-TOFF123-CSd01-TOFF123 = derive (X3 ∷ CK32⁻ ∷ X3 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  (rw 0 q26 ∷
   rw 1 q27 ∷
   rw 2 q28 ∷
   rw 3 q27 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = sE 154 lem-pass-X3-CK32-X3-vs-CS01
  q30 : Eqn
  q30 = sE 598 lem-pass-X3-CK32-X3-vs-TOFF123
  q31 : Eqn
  q31 = sE 155 lem-pass-X3-CK32-X3-vs-CSd01

-- pass [X3 CK32 X3] [CS01 TOFF123 CSd01 TOFF123]: 4 steps
lem-pass-X3-CK32-X3-vs-CS01-TOFF123-CSd01-TOFF123 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-CS01-TOFF123-CSd01-TOFF123 = derive (X3 ∷ CK32 ∷ X3 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  (rw 0 q29 ∷
   rw 1 q30 ∷
   rw 2 q31 ∷
   rw 3 q30 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 607 lem-pass-X2-CS23-X2-vs-CS01
  q33 : Eqn
  q33 = sE 609 lem-pass-X2-CS23-X2-vs-TOFF123
  q34 : Eqn
  q34 = sE 608 lem-pass-X2-CS23-X2-vs-CSd01

-- pass [X2 CS23 X2] [CS01 TOFF123 CSd01 TOFF123]: 4 steps
lem-pass-X2-CS23-X2-vs-CS01-TOFF123-CSd01-TOFF123 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS23-X2-vs-CS01-TOFF123-CSd01-TOFF123 = derive (X2 ∷ CS23 ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CS23 ∷ X2 ∷ [])
  (rw 0 q32 ∷
   rw 1 q33 ∷
   rw 2 q34 ∷
   rw 3 q33 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = sE 601 lem-pass-X2-CK23-X2-vs-CS01
  q36 : Eqn
  q36 = sE 603 lem-pass-X2-CK23-X2-vs-TOFF123
  q37 : Eqn
  q37 = sE 602 lem-pass-X2-CK23-X2-vs-CSd01

-- pass [X2 CK23 X2] [CS01 TOFF123 CSd01 TOFF123]: 4 steps
lem-pass-X2-CK23-X2-vs-CS01-TOFF123-CSd01-TOFF123 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK23-X2-vs-CS01-TOFF123-CSd01-TOFF123 = derive (X2 ∷ CK23 ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CK23 ∷ X2 ∷ [])
  (rw 0 q35 ∷
   rw 1 q36 ∷
   rw 2 q37 ∷
   rw 3 q36 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = sE 610 lem-pass-X2-CSd23-X2-vs-CS01
  q39 : Eqn
  q39 = sE 612 lem-pass-X2-CSd23-X2-vs-TOFF123
  q40 : Eqn
  q40 = sE 611 lem-pass-X2-CSd23-X2-vs-CSd01

-- pass [X2 CSd23 X2] [CS01 TOFF123 CSd01 TOFF123]: 4 steps
lem-pass-X2-CSd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 = derive (X2 ∷ CS23⁻ ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ [])
  (rw 0 q38 ∷
   rw 1 q39 ∷
   rw 2 q40 ∷
   rw 3 q39 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = sE 604 lem-pass-X2-CKd23-X2-vs-CS01
  q42 : Eqn
  q42 = sE 606 lem-pass-X2-CKd23-X2-vs-TOFF123
  q43 : Eqn
  q43 = sE 605 lem-pass-X2-CKd23-X2-vs-CSd01

-- pass [X2 CKd23 X2] [CS01 TOFF123 CSd01 TOFF123]: 4 steps
lem-pass-X2-CKd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 = derive (X2 ∷ CK23⁻ ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  (rw 0 q41 ∷
   rw 1 q42 ∷
   rw 2 q43 ∷
   rw 3 q42 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 1018 W
  q45 : Eqn
  q45 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q46 : Eqn
  q46 = wE 257 W
  q47 : Eqn
  q47 = wE 389 W
  q48 : Eqn
  q48 = eqn (Toff102 ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ []) (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q49 : Eqn
  q49 = wE 390 W
  q50 : Eqn
  q50 = wE 258 W
  q51 : Eqn
  q51 = sE 614 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-X3
  q52 : Eqn
  q52 = sE 613 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-TOFF102-X2
  q53 : Eqn
  q53 = sE 616 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd13-X3
  q54 : Eqn
  q54 = sE 600 lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 20 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 32 q44 ∷
   rw 37 q44 ∷
   rw 42 q44 ∷
   rw 29 q45 ∷
   rw 30 q46 ∷
   rw 31 q47 ∷
   rw⁻ 33 q48 ∷
   rw⁻ 34 q45 ∷
   rw 35 q49 ∷
   rw 35 q45 ∷
   rw 36 q50 ∷
   rw 37 q47 ∷
   rw⁻ 39 q48 ∷
   rw⁻ 40 q45 ∷
   rw 41 q49 ∷
   rw 0 q51 ∷
   rw 3 q52 ∷
   rw 6 q53 ∷
   rw 9 q52 ∷
   rw⁻ 0 q54 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = sE 117 lem-pass-X3-CKd31-X3-vs-CS02
  q56 : Eqn
  q56 = sE 618 lem-pass-X3-CKd31-X3-vs-TOFF213
  q57 : Eqn
  q57 = sE 118 lem-pass-X3-CKd31-X3-vs-CSd02

-- pass [X3 CKd31 X3] [CS02 TOFF213 CSd02 TOFF213]: 4 steps
lem-pass-X3-CKd31-X3-vs-CS02-TOFF213-CSd02-TOFF213 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-CS02-TOFF213-CSd02-TOFF213 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 0 q55 ∷
   rw 1 q56 ∷
   rw 2 q57 ∷
   rw 3 q56 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = sE 615 lem-comm-CCZ013-CSd23

-- pass [CCZ013] [CSd23]: 1 steps
lem-pass-CCZ013-vs-CSd23 : ⟪ (CCZ013 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CSd23 = derive (CCZ013 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ013 ∷ [])
  (rw 0 q58 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = sE 114 lem-pass-X3-CK31-X3-vs-CS02
  q60 : Eqn
  q60 = sE 617 lem-pass-X3-CK31-X3-vs-TOFF213
  q61 : Eqn
  q61 = sE 115 lem-pass-X3-CK31-X3-vs-CSd02

-- pass [X3 CK31 X3] [CS02 TOFF213 CSd02 TOFF213]: 4 steps
lem-pass-X3-CK31-X3-vs-CS02-TOFF213-CSd02-TOFF213 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-CS02-TOFF213-CSd02-TOFF213 = derive (X3 ∷ CK31 ∷ X3 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 0 q59 ∷
   rw 1 q60 ∷
   rw 2 q61 ∷
   rw 3 q60 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = sE 626 lem-pass-X1-CS13-X1-vs-CS02
  q63 : Eqn
  q63 = sE 628 lem-pass-X1-CS13-X1-vs-TOFF013
  q64 : Eqn
  q64 = sE 627 lem-pass-X1-CS13-X1-vs-CSd02

-- pass [X1 CS13 X1] [CS02 TOFF013 CSd02 TOFF013]: 4 steps
lem-pass-X1-CS13-X1-vs-CS02-TOFF013-CSd02-TOFF013 : ⟪ (X1 ∷ CS13 ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CS13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS13-X1-vs-CS02-TOFF013-CSd02-TOFF013 = derive (X1 ∷ CS13 ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CS13 ∷ X1 ∷ [])
  (rw 0 q62 ∷
   rw 1 q63 ∷
   rw 2 q64 ∷
   rw 3 q63 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = sE 620 lem-pass-X1-CK13-X1-vs-CS02
  q66 : Eqn
  q66 = sE 622 lem-pass-X1-CK13-X1-vs-TOFF013
  q67 : Eqn
  q67 = sE 621 lem-pass-X1-CK13-X1-vs-CSd02

-- pass [X1 CK13 X1] [CS02 TOFF013 CSd02 TOFF013]: 4 steps
lem-pass-X1-CK13-X1-vs-CS02-TOFF013-CSd02-TOFF013 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-CS02-TOFF013-CSd02-TOFF013 = derive (X1 ∷ CK13 ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  (rw 0 q65 ∷
   rw 1 q66 ∷
   rw 2 q67 ∷
   rw 3 q66 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = sE 629 lem-pass-X1-CSd13-X1-vs-CS02
  q69 : Eqn
  q69 = sE 631 lem-pass-X1-CSd13-X1-vs-TOFF013
  q70 : Eqn
  q70 = sE 630 lem-pass-X1-CSd13-X1-vs-CSd02

-- pass [X1 CSd13 X1] [CS02 TOFF013 CSd02 TOFF013]: 4 steps
lem-pass-X1-CSd13-X1-vs-CS02-TOFF013-CSd02-TOFF013 : ⟪ (X1 ∷ CS13⁻ ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd13-X1-vs-CS02-TOFF013-CSd02-TOFF013 = derive (X1 ∷ CS13⁻ ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ [])
  (rw 0 q68 ∷
   rw 1 q69 ∷
   rw 2 q70 ∷
   rw 3 q69 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = sE 574 lem-pass-CZ12-vs-CS03

-- pass [CS03] [CZ12]: 1 steps
lem-pass-CS03-vs-CZ12 : ⟪ (CS03 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CZ12 = derive (CS03 ∷ CZ12 ∷ []) (CZ12 ∷ CS03 ∷ [])
  (rw⁻ 0 q71 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = sE 573 lem-comm-CCZ012-CZ13

-- pass [CCZ012] [CZ13]: 1 steps
lem-pass-CCZ012-vs-CZ13 : ⟪ (CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CZ13 = derive (CCZ012 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ012 ∷ [])
  (rw 0 q72 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = sE 619 lem-comm-CCZ012-CZ23

-- pass [CCZ012] [CZ23]: 1 steps
lem-pass-CCZ012-vs-CZ23 : ⟪ (CCZ012 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CZ23 = derive (CCZ012 ∷ CZ23 ∷ []) (CZ23 ∷ CCZ012 ∷ [])
  (rw 0 q73 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = sE 597 lem-pass-CZ12-vs-CSd03

-- pass [CSd03] [CZ12]: 1 steps
lem-pass-CSd03-vs-CZ12 : ⟪ (CS03⁻ ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CZ12 = derive (CS03⁻ ∷ CZ12 ∷ []) (CZ12 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q74 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = sE 623 lem-pass-X1-CKd13-X1-vs-CS02
  q76 : Eqn
  q76 = sE 625 lem-pass-X1-CKd13-X1-vs-TOFF013
  q77 : Eqn
  q77 = sE 624 lem-pass-X1-CKd13-X1-vs-CSd02

-- pass [X1 CKd13 X1] [CS02 TOFF013 CSd02 TOFF013]: 4 steps
lem-pass-X1-CKd13-X1-vs-CS02-TOFF013-CSd02-TOFF013 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-CS02-TOFF013-CSd02-TOFF013 = derive (X1 ∷ CK13⁻ ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  (rw 0 q75 ∷
   rw 1 q76 ∷
   rw 2 q77 ∷
   rw 3 q76 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = sE 633 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS13-X3
  q79 : Eqn
  q79 = sE 632 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-TOFF102-X2
  q80 : Eqn
  q80 = sE 634 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd13-X3

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 20 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 34 q44 ∷
   rw 39 q44 ∷
   rw 44 q44 ∷
   rw 31 q45 ∷
   rw 32 q46 ∷
   rw 33 q47 ∷
   rw⁻ 35 q48 ∷
   rw⁻ 36 q45 ∷
   rw 37 q49 ∷
   rw 37 q45 ∷
   rw 38 q50 ∷
   rw 39 q47 ∷
   rw⁻ 41 q48 ∷
   rw⁻ 42 q45 ∷
   rw 43 q49 ∷
   rw 0 q78 ∷
   rw 3 q79 ∷
   rw 6 q80 ∷
   rw 9 q79 ∷
   rw⁻ 0 q54 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 1102 W
  q82 : Eqn
  q82 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))
  q83 : Eqn
  q83 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q84 : Eqn
  q84 = eqn (X0 ∷ CS13 ∷ []) (CS13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))
  q85 : Eqn
  q85 = wE 387 W
  q86 : Eqn
  q86 = eqn (X0 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • (CS • CS • CS) • Swap ↑)))
  q87 : Eqn
  q87 = sE 637 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-TOFF102-X0-X2
  q88 : Eqn
  q88 = sE 635 lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 30 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 33 q81 ∷
   rw 40 q81 ∷
   rw 47 q81 ∷
   rw 29 q82 ∷
   rw 30 q83 ∷
   rw 31 q84 ∷
   rw 32 q85 ∷
   rw 29 q45 ∷
   rw 30 q46 ∷
   rw 31 q47 ∷
   rw⁻ 34 q48 ∷
   rw⁻ 35 q83 ∷
   rw⁻ 36 q45 ∷
   rw 37 q49 ∷
   rw 37 q82 ∷
   rw 38 q83 ∷
   rw 39 q86 ∷
   rw 40 q85 ∷
   rw 37 q45 ∷
   rw 38 q50 ∷
   rw 39 q47 ∷
   rw⁻ 42 q48 ∷
   rw⁻ 43 q83 ∷
   rw⁻ 44 q45 ∷
   rw 45 q49 ∷
   rw 0 q51 ∷
   rw 3 q87 ∷
   rw 8 q53 ∷
   rw 11 q87 ∷
   rw⁻ 0 q88 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = wE 1 W
  q90 : Eqn
  q90 = wE 173 W
  q91 : Eqn
  q91 = wE 3 W
  q92 : Eqn
  q92 = wE 1407 W
  q93 : Eqn
  q93 = wE 175 W
  q94 : Eqn
  q94 = sE 38 lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q95 : Eqn
  q95 = wE 1408 W

-- pass [CK30] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 23 steps
lem-pass-CK30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CK30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ [])
  (rw 2 q89 ∷
   rw 1 q90 ∷
   re 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q91 ∷
   rw 1 q92 ∷
   rw 0 q93 ∷
   rw 1 q93 ∷
   rw 4 q89 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q93 ∷
   rw 4 q91 ∷
   rw 1 q94 ∷
   rw 9 q89 ∷
   rw 8 q90 ∷
   rw 7 q90 ∷
   re 6 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 8 q91 ∷
   rw 5 q90 ∷
   rw 6 q95 ∷
   rw 5 q93 ∷
   rw 8 q89 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q91 ∷ []) Eq.refl

-- pass [X3 CKd32 X3] [TOFF123 CS01 TOFF123 CSd01]: 4 steps
lem-pass-X3-CKd32-X3-vs-TOFF123-CS01-TOFF123-CSd01 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-TOFF123-CS01-TOFF123-CSd01 = derive (X3 ∷ CK32⁻ ∷ X3 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  (rw 0 q27 ∷
   rw 1 q26 ∷
   rw 2 q27 ∷
   rw 3 q28 ∷ []) Eq.refl

-- pass [X3 CK32 X3] [TOFF123 CS01 TOFF123 CSd01]: 4 steps
lem-pass-X3-CK32-X3-vs-TOFF123-CS01-TOFF123-CSd01 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF123-CS01-TOFF123-CSd01 = derive (X3 ∷ CK32 ∷ X3 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  (rw 0 q30 ∷
   rw 1 q29 ∷
   rw 2 q30 ∷
   rw 3 q31 ∷ []) Eq.refl

-- pass [X2 CS23 X2] [TOFF123 CS01 TOFF123 CSd01]: 4 steps
lem-pass-X2-CS23-X2-vs-TOFF123-CS01-TOFF123-CSd01 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS23-X2-vs-TOFF123-CS01-TOFF123-CSd01 = derive (X2 ∷ CS23 ∷ X2 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ [])
  (rw 0 q33 ∷
   rw 1 q32 ∷
   rw 2 q33 ∷
   rw 3 q34 ∷ []) Eq.refl

-- pass [X2 CK23 X2] [TOFF123 CS01 TOFF123 CSd01]: 4 steps
lem-pass-X2-CK23-X2-vs-TOFF123-CS01-TOFF123-CSd01 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK23-X2-vs-TOFF123-CS01-TOFF123-CSd01 = derive (X2 ∷ CK23 ∷ X2 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X2 ∷ CK23 ∷ X2 ∷ [])
  (rw 0 q36 ∷
   rw 1 q35 ∷
   rw 2 q36 ∷
   rw 3 q37 ∷ []) Eq.refl

-- pass [X2 CSd23 X2] [TOFF123 CS01 TOFF123 CSd01]: 4 steps
lem-pass-X2-CSd23-X2-vs-TOFF123-CS01-TOFF123-CSd01 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd23-X2-vs-TOFF123-CS01-TOFF123-CSd01 = derive (X2 ∷ CS23⁻ ∷ X2 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ [])
  (rw 0 q39 ∷
   rw 1 q38 ∷
   rw 2 q39 ∷
   rw 3 q40 ∷ []) Eq.refl

-- pass [X2 CKd23 X2] [TOFF123 CS01 TOFF123 CSd01]: 4 steps
lem-pass-X2-CKd23-X2-vs-TOFF123-CS01-TOFF123-CSd01 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-TOFF123-CS01-TOFF123-CSd01 = derive (X2 ∷ CK23⁻ ∷ X2 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  (rw 0 q42 ∷
   rw 1 q41 ∷
   rw 2 q42 ∷
   rw 3 q43 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = sE 636 lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 20 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 32 q44 ∷
   rw 37 q44 ∷
   rw 42 q44 ∷
   rw⁻ 30 q48 ∷
   rw⁻ 31 q45 ∷
   rw 32 q49 ∷
   rw 32 q45 ∷
   rw 33 q46 ∷
   rw 34 q47 ∷
   rw⁻ 36 q48 ∷
   rw⁻ 37 q45 ∷
   rw 38 q49 ∷
   rw 38 q45 ∷
   rw 39 q50 ∷
   rw 40 q47 ∷
   rw 0 q52 ∷
   rw 3 q51 ∷
   rw 6 q52 ∷
   rw 9 q53 ∷
   rw⁻ 0 q96 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = wE 1409 W
  q98 : Eqn
  q98 = sE 136 lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23
  q99 : Eqn
  q99 = wE 1410 W

-- pass [CK32] [X3 TOFF201 CS23 TOFF201 CSd23 X3]: 3 steps
lem-pass-CK32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : ⟪ (CK32 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CK32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = derive (CK32 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CK32 ∷ [])
  (rw 0 q97 ∷
   rw 1 q98 ∷
   rw 5 q99 ∷ []) Eq.refl

-- pass [X3 CKd31 X3] [TOFF213 CS02 TOFF213 CSd02]: 4 steps
lem-pass-X3-CKd31-X3-vs-TOFF213-CS02-TOFF213-CSd02 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-TOFF213-CS02-TOFF213-CSd02 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ []) (Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 0 q56 ∷
   rw 1 q55 ∷
   rw 2 q56 ∷
   rw 3 q57 ∷ []) Eq.refl

-- pass [X3 CK31 X3] [TOFF213 CS02 TOFF213 CSd02]: 4 steps
lem-pass-X3-CK31-X3-vs-TOFF213-CS02-TOFF213-CSd02 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-TOFF213-CS02-TOFF213-CSd02 = derive (X3 ∷ CK31 ∷ X3 ∷ Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ []) (Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 0 q60 ∷
   rw 1 q59 ∷
   rw 2 q60 ∷
   rw 3 q61 ∷ []) Eq.refl

-- pass [X1 CS13 X1] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X1-CS13-X1-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X1 ∷ CS13 ∷ X1 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS13-X1-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X1 ∷ CS13 ∷ X1 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ [])
  (rw 0 q63 ∷
   rw 1 q62 ∷
   rw 2 q63 ∷
   rw 3 q64 ∷ []) Eq.refl

-- pass [X1 CK13 X1] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X1-CK13-X1-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X1 ∷ CK13 ∷ X1 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  (rw 0 q66 ∷
   rw 1 q65 ∷
   rw 2 q66 ∷
   rw 3 q67 ∷ []) Eq.refl

-- pass [X1 CSd13 X1] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X1-CSd13-X1-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X1 ∷ CS13⁻ ∷ X1 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd13-X1-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X1 ∷ CS13⁻ ∷ X1 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ [])
  (rw 0 q69 ∷
   rw 1 q68 ∷
   rw 2 q69 ∷
   rw 3 q70 ∷ []) Eq.refl

-- pass [X1 CKd13 X1] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X1-CKd13-X1-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X1 ∷ CK13⁻ ∷ X1 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  (rw 0 q76 ∷
   rw 1 q75 ∷
   rw 2 q76 ∷
   rw 3 q77 ∷ []) Eq.refl
