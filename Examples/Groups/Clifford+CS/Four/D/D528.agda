{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD528 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D528 (W : Ws) (Sᴰ : SD528) where

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
  lem-AXIOM-LF-at1203 : St 308
  lem-AXIOM-LF-at1203 = pickᴰ 0 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CK10-CS01-CS01-CKd10-X1 : St 545
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CK10-CS01-CS01-CKd10-X1 = pickᴰ 1 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CSd01-CKd10-CS01-CS01-X1 : St 546
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CSd01-CKd10-CS01-CS01-X1 = pickᴰ 2 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-CS01-CK10-CS01-X1 : St 547
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-CS01-CK10-CS01-X1 = pickᴰ 3 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-X1 : St 548
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-X1 = pickᴰ 4 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-X1 : St 549
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-X1 = pickᴰ 5 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CK10-CS01-CS01-CKd10-X1 : St 550
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CK10-CS01-CS01-CKd10-X1 = pickᴰ 6 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-X1 : St 551
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-X1 = pickᴰ 7 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CSd01-CKd10-CS01-CS01-X1 : St 552
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CSd01-CKd10-CS01-CS01-X1 = pickᴰ 8 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12 : St 553
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12 = pickᴰ 9 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CZ23 : St 554
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CZ23 = pickᴰ 10 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CK13-X1 : St 555
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CK13-X1 = pickᴰ 11 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS13 : St 556
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS13 = pickᴰ 12 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CX23 : St 557
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CX23 = pickᴰ 13 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd13 : St 558
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd13 = pickᴰ 14 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CKd13-X1 : St 559
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CKd13-X1 = pickᴰ 15 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part0 : St 560
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part0 = pickᴰ 16 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part1 : St 561
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part1 = pickᴰ 17 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part2 : St 562
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part2 = pickᴰ 18 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part3 : St 563
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part3 = pickᴰ 19 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part4 : St 564
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part4 = pickᴰ 20 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part5 : St 565
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part5 = pickᴰ 21 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part6 : St 566
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part6 = pickᴰ 22 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part0 : St 567
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part0 = pickᴰ 23 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part1 : St 568
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part1 = pickᴰ 24 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part2 : St 569
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part2 = pickᴰ 25 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part3 : St 570
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part3 = pickᴰ 26 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part4 : St 571
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part4 = pickᴰ 27 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part5 : St 572
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part5 = pickᴰ 28 Sᴰ

private
  q1 : Eqn
  q1 = sE 545 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CK10-CS01-CS01-CKd10-X1
  q2 : Eqn
  q2 = sE 547 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-CS01-CK10-CS01-X1
  q3 : Eqn
  q3 = sE 548 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-X1

-- Bar(SSSKSS;1,3->0) passes factors of X0 X1 X3 CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03 X0 X1 X3: 4 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒临丠丠丵丒丒丠丠临丠丒丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中丒丒临丠丠丵丒") ⟫ʷ ≈ ⟪ (ℓ "丒临丠丠丵丒丒丠丠临丠丒丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中丒丒临丠丠丵丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒临丠丠丵丒丒丠丠临丠丒丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中丒丒临丠丠丵丒") (ℓ "丒临丠丠丵丒丒丠丠临丠丒丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中丒丒临丠丠丵丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 0 q1 ∷
   rw 6 q2 ∷
   rw 12 q3 ∷
   rw 100 q1 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = sE 546 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CSd01-CKd10-CS01-CS01-X1
  q5 : Eqn
  q5 = sE 549 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-X1

-- Bar(SSSKSS;1,3->0) passes factors of X0 X1 X3 CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30 X0 X1 X3: 4 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X0-X1-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X1-X3 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒临丠丠丵丒丒両丵丠丠丒丒临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中丒丒临丠丠丵丒") ⟫ʷ ≈ ⟪ (ℓ "丒临丠丠丵丒丒両丵丠丠丒丒临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中丒丒临丠丠丵丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X0-X1-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X1-X3 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒临丠丠丵丒丒両丵丠丠丒丒临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中丒丒临丠丠丵丒") (ℓ "丒临丠丠丵丒丒両丵丠丠丒丒临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中丒丒临丠丠丵丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 0 q1 ∷
   rw 6 q4 ∷
   rw 12 q5 ∷
   rw 88 q1 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = sE 550 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CK10-CS01-CS01-CKd10-X1
  q7 : Eqn
  q7 = sE 552 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CSd01-CKd10-CS01-CS01-X1
  q8 : Eqn
  q8 = sE 551 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-X1

-- Bar(SSKSKK;1,2->0) passes factors of X0 X1 X2 CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20 X0 X1 X2: 4 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-factors-of-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒临丠丠丵丒丒両丵丠丠丒丒临与临与丠丠丠临与丠丠丠丠丠丠丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丒临丠丠丵丒") ⟫ʷ ≈ ⟪ (ℓ "丒临丠丠丵丒丒両丵丠丠丒丒临与临与丠丠丠临与丠丠丠丠丠丠丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丒临丠丠丵丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-factors-of-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒临丠丠丵丒丒両丵丠丠丒丒临与临与丠丠丠临与丠丠丠丠丠丠丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丒临丠丠丵丒") (ℓ "丒临丠丠丵丒丒両丵丠丠丒丒临与临与丠丠丠临与丠丠丠丠丠丠丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丒临丠丠丵丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (rw 0 q6 ∷
   rw 6 q7 ∷
   rw 12 q8 ∷
   rw 88 q6 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = sE 555 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CK13-X1
  q10 : Eqn
  q10 = sE 554 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CZ23
  q11 : Eqn
  q11 = sE 553 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12
  q12 : Eqn
  q12 = sE 556 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS13
  q13 : Eqn
  q13 = sE 557 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CX23
  q14 : Eqn
  q14 = sE 558 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd13
  q15 : Eqn
  q15 = sE 559 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CKd13-X1

-- Bar(SSKSKK;1,2->0) passes II/IV units 3 2: 8 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-II/IV-units-3-2 : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒乁丒之丶丽乌举乌丒乂丒") ⟫ʷ ≈ ⟪ (ℓ "丒乁丒之丶丽乌举乌丒乂丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-II/IV-units-3-2 = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒乁丒之丶丽乌举乌丒乂丒") (ℓ "丒乁丒之丶丽乌举乌丒乂丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (rw 0 q9 ∷
   rw 3 q10 ∷
   rw 4 q11 ∷
   rw 5 q12 ∷
   rw 6 q13 ∷
   rw 7 q14 ∷
   rw 8 q13 ∷
   rw 9 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = sE 560 lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part0
  q17 : Eqn
  q17 = sE 561 lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part1
  q18 : Eqn
  q18 = sE 562 lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part2
  q19 : Eqn
  q19 = sE 563 lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part3
  q20 : Eqn
  q20 = sE 564 lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part4
  q21 : Eqn
  q21 = sE 565 lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part5
  q22 : Eqn
  q22 = sE 566 lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part6

-- Bar(SSKSKK;1,2->0) passes groups of WBar(SSSSSSKiSSSSSSSSS;~1,3->0): 7 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩ : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丒乀丒中中中中中中乑业中中中中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丒乀丒中中中中中中乑业中中中中中中中中中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩ = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丒乀丒中中中中中中乑业中中中中中中中中中") (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丒乀丒中中中中中中乑业中中中中中中中中中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (rw 0 q16 ∷
   rw 0 q17 ∷
   rw 0 q18 ∷
   rw 0 q19 ∷
   rw 0 q20 ∷
   rw 0 q21 ∷
   rw 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = sE 567 lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part0
  q24 : Eqn
  q24 = sE 568 lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part1
  q25 : Eqn
  q25 = sE 569 lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part2
  q26 : Eqn
  q26 = sE 570 lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part3
  q27 : Eqn
  q27 = sE 571 lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part4
  q28 : Eqn
  q28 = sE 572 lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part5

-- Bar(SSKSKK;1,2->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,3->0): 6 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩ : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业丒乀丒乑业乑业中中中乑业中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业丒乀丒乑业乑业中中中乑业中中中中中中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩ = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业丒乀丒乑业乑业中中中乑业中中中中中中") (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业丒乀丒乑业乑业中中中乑业中中中中中中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (rw 0 q23 ∷
   rw 0 q24 ∷
   rw 0 q25 ∷
   rw 0 q26 ∷
   rw 0 q27 ∷
   rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = sE 308 lem-AXIOM-LF-at1203
  q30 : Eqn
  q30 = wE 225 W
  q31 : Eqn
  q31 = wE 871 W
  q32 : Eqn
  q32 = wE 872 W
  q33 : Eqn
  q33 = wE 873 W
  q34 : Eqn
  q34 = eqn (ℓ "丶丞") (ℓ "丞丶") (low₃-comm ((CS ↑)) (X))
  q35 : Eqn
  q35 = eqn (ℓ "乇丞") (ℓ "丞乇") (low₃-comm ((CK₁₀ ↑)) (X))
  q36 : Eqn
  q36 = eqn (ℓ "乃丞") (ℓ "丞乃") (low₃-comm ((Swap ↑ • CX₁₀ • Swap ↑)) (X))
  q37 : Eqn
  q37 = eqn (ℓ "两丞") (ℓ "丞两") (low-comm (CK₀₁) ((X ↑)))
  q38 : Eqn
  q38 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q39 : Eqn
  q39 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q40 : Eqn
  q40 = wE 390 W
  q41 : Eqn
  q41 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q42 : Eqn
  q42 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q43 : Eqn
  q43 = eqn (ℓ "丌丒") (ℓ "丒丌") (low₁-comm (X) (X))
  q44 : Eqn
  q44 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q45 : Eqn
  q45 = wE 217 W
  q46 : Eqn
  q46 = eqn (ℓ "丌乨") (ℓ "乨丌") (low₁-comm (X) (Toffᵗ))
  q47 : Eqn
  q47 = wE 1106 W
  q48 : Eqn
  q48 = wE 388 W
  q49 : Eqn
  q49 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q50 : Eqn
  q50 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q51 : Eqn
  q51 = eqn (ℓ "丌丶") (ℓ "丶丌") (low₁-comm (X) (CS))
  q52 : Eqn
  q52 = eqn (ℓ "丌乇") (ℓ "乇丌") (low₁-comm (X) (CK₁₀))
  q53 : Eqn
  q53 = eqn (ℓ "丌乌") (ℓ "乌丌") (low₁-comm (X) ((CX₀₁ ↑)))
  q54 : Eqn
  q54 = eqn (ℓ "丌丽") (ℓ "丽丌") (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))
  q55 : Eqn
  q55 = eqn (ℓ "丌乔") (ℓ "乔丌") (low₁-comm (X) ((Swap ↑ • CK₁₀ • Swap ↑)))
  q56 : Eqn
  q56 = eqn (ℓ "丌业") (ℓ "业丌") (low₁-comm (X) ((S ↑ ↑)))
  q57 : Eqn
  q57 = wE 387 W

-- kk pieces X0 X1 X2 X3 CS12 CS12 CK21 CS12 CX20 CS01 CS01 CS01 CK01 S0  at 2: 150 steps
lem-kk-pieces-X0-X1-X2-X3-CS12-CS12-CK21-CS12-CX20-CS01-CS01-CS01-CK01-S0--at-2 : ⟪ (ℓ "丌丒丘丞丶丶乇丶乃丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠乔丠丠丠丈两丠丠丠丠丠丠乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈丈两丠丠丠丠丠丠丠丠丠乃丶丶丶且乇丶丶丶丶丶丶业乔丌丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘丌丘丞乧丌丘丞丒丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丘丞丌丘丞乧丌丘丞丒丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丘丞") ⟫ʷ
lem-kk-pieces-X0-X1-X2-X3-CS12-CS12-CK21-CS12-CX20-CS01-CS01-CS01-CK01-S0--at-2 = derive (ℓ "丌丒丘丞丶丶乇丶乃丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠乔丠丠丠丈两丠丠丠丠丠丠乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈丈两丠丠丠丠丠丠丠丠丠乃丶丶丶且乇丶丶丶丶丶丶业乔丌丒丘丞") (ℓ "丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘丌丘丞乧丌丘丞丒丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丘丞丌丘丞乧丌丘丞丒丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丘丞")
  (rw 4 q29 ∷
   rw 33 q30 ∷
   rw 34 q31 ∷
   rw 35 q32 ∷
   rw 36 q33 ∷
   rw 42 q30 ∷
   rw 43 q31 ∷
   rw 44 q32 ∷
   rw 45 q33 ∷
   rw 81 q30 ∷
   rw 82 q31 ∷
   rw 83 q32 ∷
   rw 84 q33 ∷
   rw 90 q30 ∷
   rw 91 q31 ∷
   rw 92 q32 ∷
   rw 93 q33 ∷
   rw⁻ 3 q34 ∷
   rw⁻ 4 q34 ∷
   rw⁻ 5 q35 ∷
   rw⁻ 6 q34 ∷
   rw⁻ 7 q35 ∷
   rw⁻ 8 q35 ∷
   rw⁻ 9 q36 ∷
   rw⁻ 10 q37 ∷
   rw⁻ 11 q38 ∷
   rw⁻ 12 q37 ∷
   rw⁻ 13 q38 ∷
   rw⁻ 14 q39 ∷
   rw⁻ 15 q39 ∷
   rw⁻ 16 q39 ∷
   rw⁻ 17 q37 ∷
   rw⁻ 18 q38 ∷
   rw⁻ 19 q39 ∷
   rw⁻ 20 q39 ∷
   rw⁻ 21 q39 ∷
   rw⁻ 22 q39 ∷
   rw⁻ 23 q39 ∷
   rw⁻ 24 q39 ∷
   rw⁻ 25 q36 ∷
   rw⁻ 26 q39 ∷
   rw⁻ 27 q39 ∷
   rw⁻ 28 q37 ∷
   rw⁻ 29 q39 ∷
   rw⁻ 30 q37 ∷
   rw⁻ 31 q37 ∷
   rw 32 q40 ∷
   rw⁻ 32 q41 ∷
   rw⁻ 33 q42 ∷
   rw⁻ 32 q43 ∷
   rw 36 q41 ∷
   rw 37 q44 ∷
   re 39 1 (ℓ "並乨並") ∷
   rw 38 q45 ∷
   rw 39 q46 ∷
   rw 40 q47 ∷
   re 38 3 (ℓ "乧") ∷
   rw 39 q44 ∷
   rw 40 q41 ∷
   rw 41 q48 ∷
   rw⁻ 39 q49 ∷
   rw⁻ 40 q50 ∷
   rw⁻ 39 q42 ∷
   rw 42 q43 ∷
   rw 43 q42 ∷
   rw 44 q50 ∷
   rw 45 q51 ∷
   rw 46 q51 ∷
   rw 47 q51 ∷
   rw 48 q52 ∷
   rw 49 q51 ∷
   rw 50 q51 ∷
   rw 51 q53 ∷
   rw 52 q54 ∷
   rw 53 q54 ∷
   rw 54 q54 ∷
   rw 55 q54 ∷
   rw 56 q54 ∷
   rw 57 q54 ∷
   rw 58 q55 ∷
   rw 59 q56 ∷
   rw 60 q54 ∷
   rw 61 q54 ∷
   rw 62 q54 ∷
   rw 63 q54 ∷
   rw 64 q54 ∷
   rw 65 q54 ∷
   rw 66 q54 ∷
   rw 67 q54 ∷
   rw 68 q54 ∷
   rw 69 q53 ∷
   rw 70 q54 ∷
   rw 71 q54 ∷
   rw 72 q54 ∷
   rw 73 q55 ∷
   rw 74 q54 ∷
   rw 75 q54 ∷
   rw 76 q50 ∷
   rw 77 q42 ∷
   rw 78 q43 ∷
   rw 79 q57 ∷
   rw⁻ 76 q49 ∷
   rw⁻ 77 q44 ∷
   rw⁻ 76 q41 ∷
   rw 80 q41 ∷
   rw 81 q44 ∷
   re 83 1 (ℓ "並乨並") ∷
   rw 82 q45 ∷
   rw 83 q46 ∷
   rw 84 q47 ∷
   re 82 3 (ℓ "乧") ∷
   rw 83 q44 ∷
   rw 84 q41 ∷
   rw 85 q48 ∷
   rw⁻ 83 q49 ∷
   rw⁻ 84 q50 ∷
   rw⁻ 83 q42 ∷
   rw 86 q43 ∷
   rw 87 q42 ∷
   rw 88 q50 ∷
   rw 89 q51 ∷
   rw 90 q51 ∷
   rw 91 q52 ∷
   rw 92 q51 ∷
   rw 93 q52 ∷
   rw 94 q52 ∷
   rw 95 q53 ∷
   rw 96 q55 ∷
   rw 97 q56 ∷
   rw 98 q55 ∷
   rw 99 q56 ∷
   rw 100 q54 ∷
   rw 101 q54 ∷
   rw 102 q54 ∷
   rw 103 q55 ∷
   rw 104 q56 ∷
   rw 105 q54 ∷
   rw 106 q54 ∷
   rw 107 q54 ∷
   rw 108 q54 ∷
   rw 109 q54 ∷
   rw 110 q54 ∷
   rw 111 q53 ∷
   rw 112 q54 ∷
   rw 113 q54 ∷
   rw 114 q55 ∷
   rw 115 q54 ∷
   rw 116 q55 ∷
   rw 117 q55 ∷
   rw 118 q57 ∷ []) Eq.refl
