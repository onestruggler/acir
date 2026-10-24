{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD746 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D746 (W : Ws) (Sᴰ : SD746) where

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
  lem-AXIOM-LF-at0312 : St 180
  lem-AXIOM-LF-at0312 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-X3 : St 389
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-X3 = pickᴰ 1 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd32-X3 : St 390
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd32-X3 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-X3 : St 392
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-X3 = pickᴰ 3 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd23-X3 : St 395
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd23-X3 = pickᴰ 4 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3 : St 400
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3 = pickᴰ 5 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd32-X3 : St 407
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd32-X3 = pickᴰ 6 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3 : St 2374
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3 = pickᴰ 7 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3 : St 2375
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3 = pickᴰ 8 Sᴰ
  lem-CA-CS10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Sd-e≡1⟩ : St 2572
  lem-CA-CS10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Sd-e≡1⟩ = pickᴰ 9 Sᴰ
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡1⟩ : St 2573
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡1⟩ = pickᴰ 10 Sᴰ
  lem-pass-CS20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : St 2574
  lem-pass-CS20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = pickᴰ 11 Sᴰ
  lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 1996
  lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 12 Sᴰ
  lem-pass-CS30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : St 2575
  lem-pass-CS30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = pickᴰ 13 Sᴰ
  lem-CA-CKd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ : St 2576
  lem-CA-CKd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ = pickᴰ 14 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2577
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 15 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2578
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 16 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2579
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 17 Sᴰ
  lem-pass-CSd30-vs-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X3 : St 2580
  lem-pass-CSd30-vs-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X3 = pickᴰ 18 Sᴰ
  lem-pass-CCZ123-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : St 2390
  lem-pass-CCZ123-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = pickᴰ 19 Sᴰ
  lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : St 2581
  lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = pickᴰ 20 Sᴰ
  lem-CA-CK20-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡1⟩ : St 2582
  lem-CA-CK20-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡1⟩ = pickᴰ 21 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : St 2583
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = pickᴰ 22 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : St 2584
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = pickᴰ 23 Sᴰ
  lem-pass-X2-CK23-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : St 2585
  lem-pass-X2-CK23-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = pickᴰ 24 Sᴰ
  lem-pass-X2-CKd23-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : St 2586
  lem-pass-X2-CKd23-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = pickᴰ 25 Sᴰ
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ : St 2587
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ = pickᴰ 26 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ : St 2588
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ = pickᴰ 27 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ : St 2589
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ = pickᴰ 28 Sᴰ
  lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ : St 2590
  lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ = pickᴰ 29 Sᴰ
  lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩-3 : St 2591
  lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩-3 = pickᴰ 30 Sᴰ
  lem-pass-CK23-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 2592
  lem-pass-CK23-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 31 Sᴰ
  lem-pass-CK32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : St 2593
  lem-pass-CK32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = pickᴰ 32 Sᴰ
  lem-pass-CKd20-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3 : St 2594
  lem-pass-CKd20-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3 = pickᴰ 33 Sᴰ
  lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : St 2595
  lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = pickᴰ 34 Sᴰ
  lem-pass-CKd23-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 2596
  lem-pass-CKd23-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 35 Sᴰ
  lem-pass-CKd32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : St 2597
  lem-pass-CKd32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = pickᴰ 36 Sᴰ
  lem-pass-TOFF213-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2598
  lem-pass-TOFF213-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 37 Sᴰ
  lem-pass-X1-CKd10-X1-vs-X2-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X2-X3 : St 2599
  lem-pass-X1-CKd10-X1-vs-X2-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X2-X3 = pickᴰ 38 Sᴰ
  lem-pass-X1-CKd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : St 2600
  lem-pass-X1-CKd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = pickᴰ 39 Sᴰ
  lem-pass-X2-CK21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3 : St 2601
  lem-pass-X2-CK21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3 = pickᴰ 40 Sᴰ
  lem-pass-X2-CKd21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2602
  lem-pass-X2-CKd21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 41 Sᴰ

private
  q1 : Eqn
  q1 = sE 395 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd23-X3
  q2 : Eqn
  q2 = sE 390 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd32-X3
  q3 : Eqn
  q3 = sE 392 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-X3
  q4 : Eqn
  q4 = sE 2584 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3
  q5 : Eqn
  q5 = sE 389 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-X3

-- Bar(SSSKSS;3,1->0) passes split Gad(t=2, W=(0, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞") (ℓ "丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
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
  q6 = sE 2375 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3
  q7 : Eqn
  q7 = sE 407 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd32-X3
  q8 : Eqn
  q8 = sE 2374 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3
  q9 : Eqn
  q9 = sE 2583 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3
  q10 : Eqn
  q10 = sE 400 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3

-- Bar(SSKSKK;3,2->0) passes split Gad(t=2, W=(0, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞") (ℓ "丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q6 ∷
   rw 3 q7 ∷
   rw 6 q8 ∷
   rw 9 q8 ∷
   rw 12 q9 ∷
   rw 20 q6 ∷
   rw 23 q6 ∷
   rw 26 q10 ∷
   rw 29 q8 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q12 : Eqn
  q12 = wE 2301 W
  q13 : Eqn
  q13 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q14 : Eqn
  q14 = sE 2586 lem-pass-X2-CKd23-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3
  q15 : Eqn
  q15 = wE 2302 W

-- pass [CKd23] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CKd23-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "乎丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乎") ⟫ʷ
lem-pass-CKd23-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "乎丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乎")
  (rw 1 q11 ∷
   rw 0 q12 ∷
   rw 19 q13 ∷
   rw 1 q14 ∷
   rw 17 q15 ∷
   rw⁻ 0 q11 ∷
   rw⁻ 16 q13 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 2303 W
  q17 : Eqn
  q17 = sE 2585 lem-pass-X2-CK23-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3
  q18 : Eqn
  q18 = wE 2304 W

-- pass [CK23] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CK23-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "乍丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乍") ⟫ʷ
lem-pass-CK23-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "乍丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乍")
  (rw 1 q11 ∷
   rw 0 q16 ∷
   rw 19 q13 ∷
   rw 1 q17 ∷
   rw 17 q18 ∷
   rw⁻ 0 q11 ∷
   rw⁻ 16 q13 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 5 W
  q20 : Eqn
  q20 = wE 7 W
  q21 : Eqn
  q21 = wE 140 W
  q22 : Eqn
  q22 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q23 : Eqn
  q23 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q24 : Eqn
  q24 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q25 : Eqn
  q25 = wE 2423 W
  q26 : Eqn
  q26 = wE 27 W
  q27 : Eqn
  q27 = wE 142 W
  q28 : Eqn
  q28 = wE 29 W
  q29 : Eqn
  q29 = wE 139 W
  q30 : Eqn
  q30 = wE 31 W
  q31 : Eqn
  q31 = sE 2576 lem-CA-CKd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩
  q32 : Eqn
  q32 = sE 2580 lem-pass-CSd30-vs-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X3
  q33 : Eqn
  q33 = sE 2582 lem-CA-CK20-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡1⟩
  q34 : Eqn
  q34 = sE 2575 lem-pass-CS30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3
  q35 : Eqn
  q35 = wE 137 W
  q36 : Eqn
  q36 = wE 76 W
  q37 : Eqn
  q37 = wE 2424 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 144 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞九中九丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞九中九丮丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞九中九丮丞") (ℓ "丞九中九丮丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 31 q19 ∷
   rw 30 q20 ∷
   rw 29 q20 ∷
   rw 28 q21 ∷
   rw 27 q20 ∷
   rw 26 q20 ∷
   rw 25 q20 ∷
   rw⁻ 24 q22 ∷
   rw 23 q20 ∷
   rw 22 q20 ∷
   rw 21 q20 ∷
   rw 20 q20 ∷
   rw 19 q20 ∷
   rw 18 q20 ∷
   rw 17 q20 ∷
   rw 16 q20 ∷
   rw 15 q20 ∷
   rw⁻ 14 q23 ∷
   rw 13 q21 ∷
   rw 12 q20 ∷
   rw 11 q20 ∷
   rw 10 q20 ∷
   rw 9 q20 ∷
   rw 8 q20 ∷
   rw 7 q20 ∷
   rw⁻ 6 q22 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q24 ∷
   rw 6 q20 ∷
   rw⁻ 5 q24 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q24 ∷
   rw 5 q20 ∷
   rw⁻ 4 q24 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q24 ∷
   rw 4 q21 ∷
   rw⁻ 3 q24 ∷
   re 4 3 (ℓ "乔") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q24 ∷
   rw 3 q20 ∷
   rw⁻ 2 q24 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q24 ∷
   rw 2 q20 ∷
   rw⁻ 1 q24 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q24 ∷
   rw 1 q20 ∷
   rw⁻ 0 q24 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q25 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q24 ∷
   rw 1 q26 ∷
   rw 2 q24 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q27 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q24 ∷
   rw 3 q28 ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q29 ∷
   rw 4 q30 ∷
   rw 3 q31 ∷
   rw 2 q32 ∷
   rw 1 q33 ∷
   rw 0 q34 ∷
   rw 10 q19 ∷
   rw 9 q35 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw⁻ 10 q24 ∷
   rw 9 q36 ∷
   rw⁻ 8 q24 ∷
   re 9 3 (ℓ "举") ∷
   rw 7 q21 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q24 ∷
   rw 7 q20 ∷
   rw⁻ 6 q24 ∷
   re 7 3 (ℓ "丽") ∷
   rw 7 q37 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q24 ∷
   rw 7 q26 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q24 ∷
   rw 8 q26 ∷
   rw 9 q24 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q24 ∷
   rw 9 q26 ∷
   rw 10 q24 ∷
   re 8 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏乇乏") ∷
   rw 9 q24 ∷
   rw 10 q27 ∷
   rw 11 q24 ∷
   re 9 3 (ℓ "乑") ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q24 ∷
   rw 11 q26 ∷
   rw 12 q24 ∷
   re 10 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q24 ∷
   rw 12 q26 ∷
   rw 13 q24 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q22 ∷
   rw 13 q26 ∷
   rw 14 q26 ∷
   rw 15 q26 ∷
   rw 16 q26 ∷
   rw 17 q26 ∷
   rw 18 q26 ∷
   rw 19 q27 ∷
   rw 20 q23 ∷
   rw 21 q26 ∷
   rw 22 q26 ∷
   rw 23 q26 ∷
   rw 24 q26 ∷
   rw 25 q26 ∷
   rw 26 q26 ∷
   rw 27 q26 ∷
   rw 28 q26 ∷
   rw 29 q26 ∷
   rw 30 q22 ∷
   rw 31 q26 ∷
   rw 32 q26 ∷
   rw 33 q26 ∷
   rw 34 q27 ∷
   rw 35 q26 ∷
   rw 36 q26 ∷
   rw 37 q30 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = sE 180 lem-AXIOM-LF-at0312
  q39 : Eqn
  q39 = sE 2578 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q40 : Eqn
  q40 = sE 2598 lem-pass-TOFF213-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q41 : Eqn
  q41 = sE 2579 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q42 : Eqn
  q42 = sE 2577 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q43 : Eqn
  q43 = sE 180 lem-AXIOM-LF-at0312

-- far CS03 CS03 CK30 CS03 CX31 CS01 CS01 CS01 .. 0001PP1 sep 3: 7 steps
lem-far-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01-··-0001PP1-sep-3 : ⟪ (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄丞习丽习举丞") ⟫ʷ ≈ ⟪ (ℓ "丞习丽习举丞中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄") ⟫ʷ
lem-far-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01-··-0001PP1-sep-3 = derive (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄丞习丽习举丞") (ℓ "丞习丽习举丞中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄")
  (rw 0 q38 ∷
   rw 62 q39 ∷
   rw 61 q40 ∷
   rw 30 q41 ∷
   rw 29 q40 ∷
   rw 0 q42 ∷
   rw⁻ 6 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 2425 W
  q45 : Eqn
  q45 = sE 2596 lem-pass-CKd23-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q46 : Eqn
  q46 = sE 1996 lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q47 : Eqn
  q47 = sE 2592 lem-pass-CK23-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q48 : Eqn
  q48 = wE 2426 W

-- pass [TOFF312] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "乨丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞乨") ⟫ʷ
lem-pass-TOFF312-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "乨丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞乨")
  (rw 0 q44 ∷
   rw 2 q45 ∷
   rw 1 q46 ∷
   rw 0 q47 ∷
   rw 8 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = sE 2591 lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩-3
  q50 : Eqn
  q50 = sE 2587 lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩
  q51 : Eqn
  q51 = sE 2591 lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩-3

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 K2 S2 S2 Kd2 TOFF201 CS23 TOFF201 CSd23 K2 Sd2 Sd2 Kd2 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞世且且丗乣义乣乊世丕丕丗丞") ⟫ʷ ≈ ⟪ (ℓ "丞世且且丗乣义乣乊世丕丕丗丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞世且且丗乣义乣乊世丕丕丗丞") (ℓ "丞世且且丗乣义乣乊世丕丕丗丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q49 ∷
   rw 0 q50 ∷
   rw⁻ 0 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = sE 2590 lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩

-- pass [CCZ123] [X3 K2 S2 S2 Kd2 TOFF201 CS23 TOFF201 CSd23 K2 Sd2 Sd2 Kd2 X3]: 3 steps
lem-pass-CCZ123-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 : ⟪ (ℓ "乜丞世且且丗乣义乣乊世丕丕丗丞") ⟫ʷ ≈ ⟪ (ℓ "丞世且且丗乣义乣乊世丕丕丗丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 = derive (ℓ "乜丞世且且丗乣义乣乊世丕丕丗丞") (ℓ "丞世且且丗乣义乣乊世丕丕丗丞乜")
  (rw 1 q49 ∷
   rw 0 q52 ∷
   rw⁻ 0 q51 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = sE 2589 lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 K2 S2 S2 Kd2 TOFF201 CS23 TOFF201 CSd23 K2 Sd2 Sd2 Kd2 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞世且且丗乣义乣乊世丕丕丗丞") ⟫ʷ ≈ ⟪ (ℓ "丞世且且丗乣义乣乊世丕丕丗丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞世且且丗乣义乣乊世丕丕丗丞") (ℓ "丞世且且丗乣义乣乊世丕丕丗丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 31 q49 ∷
   rw 0 q53 ∷
   rw⁻ 0 q51 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = sE 2588 lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 K2 S2 S2 Kd2 TOFF201 CS23 TOFF201 CSd23 K2 Sd2 Sd2 Kd2 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞世且且丗乣义乣乊世丕丕丗丞") ⟫ʷ ≈ ⟪ (ℓ "丞世且且丗乣义乣乊世丕丕丗丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞世且且丗乣义乣乊世丕丕丗丞") (ℓ "丞世且且丗乣义乣乊世丕丕丗丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q49 ∷
   rw 0 q54 ∷
   rw⁻ 0 q51 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = wE 2415 W
  q56 : Eqn
  q56 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q57 : Eqn
  q57 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q58 : Eqn
  q58 = sE 2600 lem-pass-X1-CKd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3
  q59 : Eqn
  q59 = wE 2416 W

-- pass [CKd10] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 7 steps
lem-pass-CKd10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (ℓ "丵丒丘丞九中九丮丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞九中九丮丒丘丞丵") ⟫ʷ
lem-pass-CKd10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = derive (ℓ "丵丒丘丞九中九丮丒丘丞") (ℓ "丒丘丞九中九丮丒丘丞丵")
  (rw 0 q55 ∷
   rw 10 q56 ∷
   rw 11 q57 ∷
   rw 1 q58 ∷
   rw 9 q59 ∷
   rw⁻ 8 q57 ∷
   rw⁻ 7 q56 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = wE 1478 W
  q61 : Eqn
  q61 = sE 2602 lem-pass-X2-CKd21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q62 : Eqn
  q62 = wE 1479 W

-- pass [CKd21] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "么丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞么") ⟫ʷ
lem-pass-CKd21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "么丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞么")
  (rw 0 q60 ∷
   rw 9 q13 ∷
   rw 1 q61 ∷
   rw 7 q62 ∷
   rw⁻ 6 q13 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 1476 W
  q64 : Eqn
  q64 = sE 2601 lem-pass-X2-CK21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3
  q65 : Eqn
  q65 = wE 1477 W

-- pass [CK21] [X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 : ⟪ (ℓ "乇丘丞丐与与丑习丽习举丐丏丏丑丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丐与与丑习丽习举丐丏丏丑丘丞乇") ⟫ʷ
lem-pass-CK21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 = derive (ℓ "乇丘丞丐与与丑习丽习举丐丏丏丑丘丞") (ℓ "丘丞丐与与丑习丽习举丐丏丏丑丘丞乇")
  (rw 0 q63 ∷
   rw 17 q13 ∷
   rw 1 q64 ∷
   rw 15 q65 ∷
   rw⁻ 14 q13 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 2297 W
  q67 : Eqn
  q67 = sE 2597 lem-pass-CKd32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3
  q68 : Eqn
  q68 = sE 2390 lem-pass-CCZ123-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3
  q69 : Eqn
  q69 = sE 2593 lem-pass-CK32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3
  q70 : Eqn
  q70 = wE 2298 W

-- pass [TOFF213] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 5 steps
lem-pass-TOFF213-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (ℓ "乥丌丞习丽习举丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞习丽习举丌丞乥") ⟫ʷ
lem-pass-TOFF213-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = derive (ℓ "乥丌丞习丽习举丌丞") (ℓ "丌丞习丽习举丌丞乥")
  (rw 0 q66 ∷
   rw 2 q67 ∷
   rw 1 q68 ∷
   rw 0 q69 ∷
   rw 8 q70 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = eqn (ℓ "上丞") (ℓ "丞上") (low₁-comm (K) ((X ↑ ↑)))
  q72 : Eqn
  q72 = eqn (ℓ "上丘") (ℓ "丘上") (low₁-comm (K) ((X ↑)))
  q73 : Eqn
  q73 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q74 : Eqn
  q74 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q75 : Eqn
  q75 = eqn (ℓ "下丞") (ℓ "丞下") (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q76 : Eqn
  q76 = eqn (ℓ "下丘") (ℓ "丘下") (low₁-comm ((K • iI)) ((X ↑)))
  q77 : Eqn
  q77 = eqn (ℓ "三丘") (ℓ "丘三") (low₁-comm ((S • S • S)) ((X ↑)))
  q78 : Eqn
  q78 = eqn (ℓ "三丞") (ℓ "丞三") (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q79 : Eqn
  q79 = wE 2427 W
  q80 : Eqn
  q80 = wE 2428 W
  q81 : Eqn
  q81 = sE 2595 lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3
  q82 : Eqn
  q82 = sE 2574 lem-pass-CS20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3
  q83 : Eqn
  q83 = sE 2581 lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3
  q84 : Eqn
  q84 = wE 2429 W

-- ca-split Gad(t=0, W=(2, 3), d=KSSKd, e=1) 2: 23 steps
lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2 : ⟪ (ℓ "丘丞上丈丈下九中九丮上三三下丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘乄丘丘丧丘丘丧丘丘久丘丘丞九中九丮丘丞丘乄丘丘丨丘丘丨丘丘久丘") ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2 = derive (ℓ "丘丞上丈丈下九中九丮上三三下丘丞") (ℓ "丘乄丘丘丧丘丘丧丘丘久丘丘丞九中九丮丘丞丘乄丘丘丨丘丘丨丘丘久丘")
  (rw⁻ 1 q71 ∷
   rw⁻ 0 q72 ∷
   rw⁻ 2 q73 ∷
   rw⁻ 1 q74 ∷
   rw⁻ 3 q73 ∷
   rw⁻ 2 q74 ∷
   rw⁻ 4 q75 ∷
   rw⁻ 3 q76 ∷
   rw 13 q76 ∷
   rw 12 q77 ∷
   rw 11 q77 ∷
   rw 10 q72 ∷
   rw 14 q75 ∷
   rw 13 q78 ∷
   rw 12 q78 ∷
   rw 11 q71 ∷
   rw 0 q79 ∷
   rw 24 q80 ∷
   rw 15 q81 ∷
   rw 14 q82 ∷
   rw 13 q82 ∷
   rw 12 q83 ∷
   rw 20 q84 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 2299 W
  q86 : Eqn
  q86 = sE 2573 lem-CA-CSd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡1⟩
  q87 : Eqn
  q87 = sE 2594 lem-pass-CKd20-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3
  q88 : Eqn
  q88 = sE 2572 lem-CA-CS10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Sd-e≡1⟩
  q89 : Eqn
  q89 = wE 2300 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 6 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丞九中九丮丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞九中九丮丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丞九中九丮丘丞") (ℓ "丘丞九中九丮丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q85 ∷
   rw 3 q86 ∷
   rw 2 q87 ∷
   rw 1 q88 ∷
   rw 0 q83 ∷
   rw 8 q89 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = wE 2430 W
  q91 : Eqn
  q91 = sE 2599 lem-pass-X1-CKd10-X1-vs-X2-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X2-X3
  q92 : Eqn
  q92 = wE 1846 W
  q93 : Eqn
  q93 = wE 1460 W
  q94 : Eqn
  q94 = wE 2431 W

-- CA CK10 Gad(t=0, W=(2, 3), d=Kd, e=1): 9 steps
lem-CA-CK10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Kd-e≡1⟩ : ⟪ (ℓ "临丘丞下九中九丮上丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞九中九丮丘丞临") ⟫ʷ
lem-CA-CK10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Kd-e≡1⟩ = derive (ℓ "临丘丞下九中九丮上丘丞") (ℓ "丘丞九中九丮丘丞临")
  (rw 0 q90 ∷
   rw 1 q91 ∷
   rw 0 q72 ∷
   rw 1 q71 ∷
   rw 2 q92 ∷
   rw 6 q93 ∷
   rw 6 q72 ∷
   rw 7 q71 ∷
   rw 8 q94 ∷ []) Eq.refl
