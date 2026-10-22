{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD752 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D752 (W : Ws) (Sᴰ : SD752) where

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
  lem-pass-S0-vs-CSd03 : St 818
  lem-pass-S0-vs-CSd03 = pickᴰ 0 Sᴰ
  lem-pass-Sd0-vs-CSd03 : St 825
  lem-pass-Sd0-vs-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-CS12-vs-CSd03 : St 34
  lem-pass-CS12-vs-CSd03 = pickᴰ 2 Sᴰ
  lem-pass-S0-vs-CCZ013 : St 2680
  lem-pass-S0-vs-CCZ013 = pickᴰ 3 Sᴰ
  lem-pass-S0-vs-CCZ123 : St 2681
  lem-pass-S0-vs-CCZ123 = pickᴰ 4 Sᴰ
  lem-pass-Sd0-vs-CCZ013 : St 2682
  lem-pass-Sd0-vs-CCZ013 = pickᴰ 5 Sᴰ
  lem-pass-CCZ123-vs-CSd03 : St 861
  lem-pass-CCZ123-vs-CSd03 = pickᴰ 6 Sᴰ
  lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 849
  lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 7 Sᴰ
  lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 850
  lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 8 Sᴰ
  lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 852
  lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 9 Sᴰ
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 869
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 10 Sᴰ
  lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 853
  lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 11 Sᴰ
  lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 904
  lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 12 Sᴰ
  lem-pass-CS12-vs-CCZ013 : St 2683
  lem-pass-CS12-vs-CCZ013 = pickᴰ 13 Sᴰ
  lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 : St 1117
  lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 14 Sᴰ
  lem-pass-Sd0-vs-CS03-TOFF012-CSd03-TOFF012 : St 1170
  lem-pass-Sd0-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 15 Sᴰ
  lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2457
  lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 16 Sᴰ
  lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 1135
  lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 17 Sᴰ
  lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2458
  lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 18 Sᴰ
  lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 1137
  lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 19 Sᴰ
  lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2459
  lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 20 Sᴰ
  lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 1140
  lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 21 Sᴰ
  lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2460
  lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 22 Sᴰ
  lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 1144
  lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 23 Sᴰ
  lem-pass-CK21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : St 2684
  lem-pass-CK21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = pickᴰ 24 Sᴰ
  lem-pass-CKd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : St 2685
  lem-pass-CKd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = pickᴰ 25 Sᴰ
  lem-pass-CS21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : St 2686
  lem-pass-CS21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = pickᴰ 26 Sᴰ
  lem-pass-CSd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : St 2687
  lem-pass-CSd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = pickᴰ 27 Sᴰ
  lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1765
  lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 28 Sᴰ
  lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1766
  lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 29 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2688
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 30 Sᴰ
  lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2036
  lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 31 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2037
  lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 32 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2039
  lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 33 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2042
  lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 34 Sᴰ
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2059
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 35 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 : St 2230
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 = pickᴰ 36 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-3 : St 2689
  lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-3 = pickᴰ 37 Sᴰ
  lem-pass-CK31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2690
  lem-pass-CK31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 38 Sᴰ
  lem-pass-CKd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2691
  lem-pass-CKd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 39 Sᴰ
  lem-pass-CS31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2692
  lem-pass-CS31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 40 Sᴰ
  lem-pass-CSd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2693
  lem-pass-CSd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 41 Sᴰ
  lem-pass-X3-CK30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2694
  lem-pass-X3-CK30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 42 Sᴰ
  lem-pass-X3-CKd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2695
  lem-pass-X3-CKd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 43 Sᴰ
  lem-pass-X3-CS30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2696
  lem-pass-X3-CS30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 44 Sᴰ
  lem-pass-X3-CSd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2697
  lem-pass-X3-CSd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 45 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2 : St 2236
  lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2 = pickᴰ 46 Sᴰ
  lem-pass-X2-CK20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2698
  lem-pass-X2-CK20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 47 Sᴰ
  lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2245
  lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 48 Sᴰ
  lem-pass-X2-CSd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2699
  lem-pass-X2-CSd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 49 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2 : St 2482
  lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2 = pickᴰ 50 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 : St 2483
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 = pickᴰ 51 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2 : St 2484
  lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2 = pickᴰ 52 Sᴰ
  lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2487
  lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 53 Sᴰ
  lem-pass-CK31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : St 2700
  lem-pass-CK31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = pickᴰ 54 Sᴰ
  lem-pass-CKd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : St 2701
  lem-pass-CKd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = pickᴰ 55 Sᴰ
  lem-pass-CS31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : St 2702
  lem-pass-CS31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = pickᴰ 56 Sᴰ
  lem-pass-CSd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : St 2703
  lem-pass-CSd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = pickᴰ 57 Sᴰ
  lem-pass-X2-CKd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2704
  lem-pass-X2-CKd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 58 Sᴰ
  lem-pass-X2-CS20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2705
  lem-pass-X2-CS20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 59 Sᴰ
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2519
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 60 Sᴰ
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2706
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 61 Sᴰ
  lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2707
  lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 62 Sᴰ
  lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ : St 2708
  lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ = pickᴰ 63 Sᴰ
  lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSK-e≡-1⟩ : St 2709
  lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSK-e≡-1⟩ = pickᴰ 64 Sᴰ
  lem-E-PPi : St 2710
  lem-E-PPi = pickᴰ 65 Sᴰ
  lem-PP-flip-ᵖ-1 : St 2671
  lem-PP-flip-ᵖ-1 = pickᴰ 66 Sᴰ
  lem-c--⟶-ci-E : St 2711
  lem-c--⟶-ci-E = pickᴰ 67 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 : St 2712
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 = pickᴰ 68 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2 : St 2713
  lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2 = pickᴰ 69 Sᴰ
  lem-merge3 : St 2674
  lem-merge3 = pickᴰ 70 Sᴰ
  lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2714
  lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 71 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : St 2715
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = pickᴰ 72 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : St 2716
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = pickᴰ 73 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : St 2717
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = pickᴰ 74 Sᴰ
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2718
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 75 Sᴰ
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2719
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 76 Sᴰ
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2720
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 77 Sᴰ
  lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : St 2721
  lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = pickᴰ 78 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q3 : Eqn
  q3 = wE 9 W
  q4 : Eqn
  q4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q7 : Eqn
  q7 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q8 : Eqn
  q8 = wE 3 W
  q9 : Eqn
  q9 = wE 127 W
  q10 : Eqn
  q10 = wE 271 W
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 8 W
  q14 : Eqn
  q14 = wE 10 W
  q15 : Eqn
  q15 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q16 : Eqn
  q16 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q17 : Eqn
  q17 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (low-comm ((iI ↑)) (Swap))
  q18 : Eqn
  q18 = wE 272 W
  q19 : Eqn
  q19 = wE 1609 W
  q20 : Eqn
  q20 = wE 56 W
  q21 : Eqn
  q21 = sE 2674 lem-merge3
  q22 : Eqn
  q22 = wE 43 W
  q23 : Eqn
  q23 = wE 27 W
  q24 : Eqn
  q24 = wE 28 W
  q25 : Eqn
  q25 = wE 29 W
  q26 : Eqn
  q26 = wE 25 W
  q27 : Eqn
  q27 = wE 11 W
  q28 : Eqn
  q28 = wE 31 W

-- merge3 @1032: 393 steps
lem-merge3-at1032 : ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X2 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ013 ∷ []) ⟫ʷ
lem-merge3-at1032 = derive (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X2 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X2 ∷ []) (CS03 ∷ CCZ013 ∷ [])
  (rw 10 q1 ∷
   rw⁻ 9 q2 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q5 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q6 ∷
   rw 12 q5 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q6 ∷
   rw 14 q5 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q7 ∷
   rw 15 q8 ∷
   rw 14 q9 ∷
   rw 13 q10 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q11 ∷
   rw 13 q12 ∷
   rw⁻ 12 q11 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 11 q13 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q11 ∷
   rw 11 q3 ∷
   rw⁻ 10 q11 ∷
   re 11 3 (CS03⁻ ∷ []) ∷
   rw 9 q13 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q11 ∷
   rw 9 q14 ∷
   rw⁻ 8 q11 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 7 q10 ∷
   rw 8 q5 ∷
   rw⁻ 9 q15 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw⁻ 11 q16 ∷
   re 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q8 ∷
   rw⁻ 13 q16 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   rw⁻ 15 q15 ∷
   rw⁻ 16 q17 ∷
   rw 9 q18 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 8 3 (Toff013 ∷ []) ∷
   rw 6 q14 ∷
   re 5 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 10 q5 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q6 ∷
   rw 12 q5 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q4 ∷
   rw⁻ 12 q7 ∷
   rw 13 q8 ∷
   rw 12 q9 ∷
   rw 11 q10 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q11 ∷
   rw 11 q12 ∷
   rw⁻ 10 q11 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q13 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q11 ∷
   rw 9 q3 ∷
   rw⁻ 8 q11 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 7 q13 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q11 ∷
   rw 7 q14 ∷
   rw⁻ 6 q11 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 5 q10 ∷
   rw 6 q5 ∷
   rw⁻ 7 q15 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw⁻ 9 q16 ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw⁻ 11 q16 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q8 ∷
   rw⁻ 13 q15 ∷
   rw⁻ 14 q17 ∷
   rw 7 q18 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   rw⁻ 4 q2 ∷
   rw 3 q3 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q5 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 9 q5 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q7 ∷
   rw 10 q8 ∷
   rw 9 q9 ∷
   rw 8 q10 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q11 ∷
   rw 8 q12 ∷
   rw⁻ 7 q11 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 6 q13 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw 6 q3 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 4 q13 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q11 ∷
   rw 4 q14 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 2 q10 ∷
   rw 3 q5 ∷
   rw⁻ 4 q15 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   rw⁻ 8 q16 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw⁻ 10 q15 ∷
   rw⁻ 11 q17 ∷
   rw 4 q18 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw 1 q14 ∷
   re 0 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q4 ∷
   rw 3 q5 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 5 q5 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw⁻ 7 q7 ∷
   rw 8 q8 ∷
   rw 7 q9 ∷
   rw 6 q10 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw 6 q12 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q13 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q11 ∷
   rw 4 q3 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   rw 2 q13 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q11 ∷
   rw 2 q14 ∷
   rw⁻ 1 q11 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 0 q10 ∷
   rw 1 q5 ∷
   rw⁻ 2 q15 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw⁻ 4 q16 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 9 q17 ∷
   rw 2 q18 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 11 q5 ∷
   rw 10 q19 ∷
   rw 9 q5 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   re 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q15 ∷
   rw 11 q5 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 13 q5 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q6 ∷
   rw 15 q5 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q15 ∷
   rw⁻ 15 q7 ∷
   rw 16 q8 ∷
   rw 15 q7 ∷
   rw 14 q15 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q8 ∷
   rw 12 q6 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q8 ∷
   rw 10 q6 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   rw 8 q15 ∷
   rw 9 q20 ∷
   re 9 8 (Toff012 ∷ []) ∷
   rw 7 q5 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q15 ∷
   rw 9 q5 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q6 ∷
   rw 11 q5 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 13 q5 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q15 ∷
   rw⁻ 13 q7 ∷
   rw 14 q8 ∷
   rw 13 q7 ∷
   rw 12 q15 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q8 ∷
   rw 10 q6 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   rw 8 q6 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 6 q15 ∷
   rw 7 q20 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 5 q19 ∷
   rw 4 q5 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q15 ∷
   rw 6 q5 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 10 q5 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q15 ∷
   rw⁻ 10 q7 ∷
   rw 11 q8 ∷
   rw 10 q7 ∷
   rw 9 q15 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw 7 q6 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q6 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 3 q15 ∷
   rw 4 q20 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q5 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q15 ∷
   rw 4 q5 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw⁻ 8 q7 ∷
   rw 9 q8 ∷
   rw 8 q7 ∷
   rw 7 q15 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q6 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 3 q6 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   rw 1 q15 ∷
   rw 2 q20 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 2 q21 ∷
   rw 3 q5 ∷
   re 1 3 (CS13 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q5 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 2 q5 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw⁻ 4 q6 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw⁻ 6 q6 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   rw 3 q22 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   rw 3 q8 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q11 ∷
   rw 1 q23 ∷
   rw 2 q11 ∷
   re 0 3 (CS03 ∷ []) ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q5 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q8 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q11 ∷
   rw 2 q23 ∷
   rw 3 q11 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q24 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q11 ∷
   rw 4 q25 ∷
   rw 5 q11 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q24 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q11 ∷
   rw 6 q26 ∷
   rw 7 q11 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 1 q5 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q8 ∷
   rw⁻ 3 q16 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   rw⁻ 5 q16 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 2 q27 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 2052 W
  q30 : Eqn
  q30 = wE 4 W
  q31 : Eqn
  q31 = sE 2674 lem-merge3
  q32 : Eqn
  q32 = wE 227 W
  q33 : Eqn
  q33 = wE 1358 W
  q34 : Eqn
  q34 = wE 1342 W
  q35 : Eqn
  q35 = wE 390 W

-- merge3 ^-1: 37 steps
lem-merge3-ᵖ-1 : ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-merge3-ᵖ-1 = derive (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CCZ012 ∷ CS12⁻ ∷ [])
  (rw 10 q29 ∷
   rw 11 q30 ∷
   rw⁻ 10 q31 ∷
   rw 9 q32 ∷
   rw 10 q5 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw 9 q33 ∷
   rw 8 q8 ∷
   rw 7 q32 ∷
   rw 8 q5 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 7 q34 ∷
   rw 6 q8 ∷
   rw 5 q35 ∷
   rw 4 q32 ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw 4 q33 ∷
   rw 3 q8 ∷
   rw 2 q32 ∷
   rw 3 q5 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw 2 q34 ∷
   rw 1 q8 ∷
   rw 0 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = sE 2683 lem-pass-CS12-vs-CCZ013
  q37 : Eqn
  q37 = sE 34 lem-pass-CS12-vs-CSd03
  q38 : Eqn
  q38 = wE 1455 W
  q39 : Eqn
  q39 = sE 2682 lem-pass-Sd0-vs-CCZ013
  q40 : Eqn
  q40 = sE 825 lem-pass-Sd0-vs-CSd03
  q41 : Eqn
  q41 = wE 2487 W
  q42 : Eqn
  q42 = wE 45 W
  q43 : Eqn
  q43 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)
  q44 : Eqn
  q44 = wE 231 W
  q45 : Eqn
  q45 = sE 1170 lem-pass-Sd0-vs-CS03-TOFF012-CSd03-TOFF012
  q46 : Eqn
  q46 = sE 2680 lem-pass-S0-vs-CCZ013
  q47 : Eqn
  q47 = sE 2681 lem-pass-S0-vs-CCZ123
  q48 : Eqn
  q48 = sE 818 lem-pass-S0-vs-CSd03
  q49 : Eqn
  q49 = wE 1728 W
  q50 : Eqn
  q50 = sE 861 lem-pass-CCZ123-vs-CSd03
  q51 : Eqn
  q51 = sE 2710 lem-E-PPi

-- CI conj: 22 steps
lem-CI-conj : ⟪ (S0 ∷ Toff012 ∷ S0⁻ ∷ CS12 ∷ CCZ013 ∷ CS03⁻ ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CI-conj = derive (S0 ∷ Toff012 ∷ S0⁻ ∷ CS12 ∷ CCZ013 ∷ CS03⁻ ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (CCZ013 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 3 q36 ∷
   rw 4 q37 ∷
   rw 5 q38 ∷
   rw 2 q39 ∷
   rw 3 q40 ∷
   rw 4 q41 ∷
   rw 3 q42 ∷
   rw 1 q43 ∷
   rw 3 q5 ∷
   rw 4 q44 ∷
   rw 5 q5 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 6 q5 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q8 ∷
   rw⁻ 4 q45 ∷
   rw 0 q46 ∷
   rw 1 q47 ∷
   rw 2 q48 ∷
   rw 3 q49 ∷
   rw 1 q50 ∷
   rw 2 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = sE 2483 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3
  q53 : Eqn
  q53 = sE 2042 lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q54 : Eqn
  q54 = sE 2037 lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q55 : Eqn
  q55 = sE 2720 lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q56 : Eqn
  q56 = sE 2036 lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q57 : Eqn
  q57 = sE 2039 lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q58 : Eqn
  q58 = sE 2483 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3

-- pass [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3] [TOFF102 CS13 TOFF102 CSd13]: 7 steps
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ [])
  (rw 0 q52 ∷
   rw 15 q53 ∷
   rw 12 q54 ∷
   rw 6 q55 ∷
   rw 3 q56 ∷
   rw 0 q57 ∷
   rw⁻ 4 q58 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 871 W
  q60 : Eqn
  q60 = wE 1376 W
  q61 : Eqn
  q61 = wE 1377 W
  q62 : Eqn
  q62 = wE 1378 W
  q63 : Eqn
  q63 = sE 2721 lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q64 : Eqn
  q64 = wE 389 W
  q65 : Eqn
  q65 = wE 1379 W
  q66 : Eqn
  q66 = wE 1380 W
  q67 : Eqn
  q67 = wE 1381 W

-- pass [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3] [X2 CS13 TOFF102 CSd13 TOFF102 X2]: 13 steps
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-X2-CS13-TOFF102-CSd13-TOFF102-X2 : ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-X2-CS13-TOFF102-CSd13-TOFF102-X2 = derive (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ [])
  (rw 0 q59 ∷
   rw 1 q60 ∷
   rw 2 q61 ∷
   rw 3 q62 ∷
   rw 4 q61 ∷
   rw 5 q59 ∷
   rw⁻ 6 q63 ∷
   rw 21 q64 ∷
   rw 20 q65 ∷
   rw 19 q66 ∷
   rw 18 q67 ∷
   rw 17 q66 ∷
   rw 16 q64 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = sE 2711 lem-c--⟶-ci-E
  q69 : Eqn
  q69 = eqn (K0⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (CCZ))
  q70 : Eqn
  q70 = eqn (S0⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) (CCZ))

-- Ri = R E: 3 steps
lem-Ri-≡-R-E : ⟪ (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-Ri-≡-R-E = derive (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ CCZ123 ∷ [])
  (rw 2 q68 ∷
   rw⁻ 6 q69 ∷
   rw⁻ 7 q70 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = wE 2488 W
  q72 : Eqn
  q72 = wE 2489 W
  q73 : Eqn
  q73 = wE 2490 W
  q74 : Eqn
  q74 = wE 1739 W
  q75 : Eqn
  q75 = wE 1738 W
  q76 : Eqn
  q76 = wE 1740 W
  q77 : Eqn
  q77 = sE 1117 lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012
  q78 : Eqn
  q78 = wE 2491 W
  q79 : Eqn
  q79 = sE 2671 lem-PP-flip-ᵖ-1

-- spell Gad(t=0, W=(), d=1, e=-1) -> Gad(t=0, W=(), d=SSKSSK, e=1): 27 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SSKSSK-e≡1⟩ : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SSKSSK-e≡1⟩ = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ [])
  (rw 0 q71 ∷
   rw 16 q72 ∷
   rw 6 q73 ∷
   rw 11 q5 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q8 ∷
   rw 9 q7 ∷
   rw 10 q74 ∷
   rw 11 q5 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q7 ∷
   rw 11 q8 ∷
   rw 10 q75 ∷
   rw 13 q5 ∷
   re 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   rw 11 q7 ∷
   rw 12 q76 ∷
   rw 13 q5 ∷
   re 11 3 (CS03⁻ ∷ []) ∷
   rw⁻ 12 q7 ∷
   rw 13 q8 ∷
   rw 12 q75 ∷
   rw 8 q77 ∷
   rw 7 q77 ∷
   rw 11 q78 ∷
   rw 6 q79 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = wE 2492 W
  q81 : Eqn
  q81 = wE 2493 W

-- spell Gad(t=0, W=(), d=SdKdSS, e=-1) -> Gad(t=0, W=(), d=SK, e=1): 27 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = derive (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ [])
  (rw 0 q80 ∷
   rw 12 q81 ∷
   rw 2 q73 ∷
   rw 7 q5 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q7 ∷
   rw 6 q74 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 7 q8 ∷
   rw 6 q75 ∷
   rw 9 q5 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw 7 q7 ∷
   rw 8 q76 ∷
   rw 9 q5 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw⁻ 8 q7 ∷
   rw 9 q8 ∷
   rw 8 q75 ∷
   rw 4 q77 ∷
   rw 3 q77 ∷
   rw 7 q78 ∷
   rw 2 q79 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = sE 2697 lem-pass-X3-CSd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q83 : Eqn
  q83 = sE 2695 lem-pass-X3-CKd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q84 : Eqn
  q84 = sE 2719 lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q85 : Eqn
  q85 = sE 2694 lem-pass-X3-CK30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q86 : Eqn
  q86 = sE 2696 lem-pass-X3-CS30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0

-- pass [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ [])
  (rw 0 q52 ∷
   rw 15 q82 ∷
   rw 12 q83 ∷
   rw 6 q84 ∷
   rw 3 q85 ∷
   rw 0 q86 ∷
   rw⁻ 8 q58 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = sE 2689 lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-3
  q88 : Eqn
  q88 = sE 2692 lem-pass-CS31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q89 : Eqn
  q89 = sE 2690 lem-pass-CK31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q90 : Eqn
  q90 = sE 2691 lem-pass-CKd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q91 : Eqn
  q91 = sE 2693 lem-pass-CSd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q92 : Eqn
  q92 = sE 2689 lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-3

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ [])
  (rw 6 q87 ∷
   rw⁻ 0 q88 ∷
   rw⁻ 1 q89 ∷
   rw 2 q55 ∷
   rw⁻ 6 q90 ∷
   rw⁻ 7 q91 ∷
   rw⁻ 0 q92 ∷ []) Eq.refl

private
  q93 : Eqn
  q93 = sE 2482 lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2
  q94 : Eqn
  q94 = sE 2699 lem-pass-X2-CSd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q95 : Eqn
  q95 = sE 2704 lem-pass-X2-CKd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q96 : Eqn
  q96 = sE 2718 lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q97 : Eqn
  q97 = sE 2698 lem-pass-X2-CK20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q98 : Eqn
  q98 = sE 2705 lem-pass-X2-CS20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q99 : Eqn
  q99 = sE 2482 lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2

-- pass [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ [])
  (rw 0 q93 ∷
   rw 15 q94 ∷
   rw 12 q95 ∷
   rw 6 q96 ∷
   rw 3 q97 ∷
   rw 0 q98 ∷
   rw⁻ 8 q99 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = sE 2230 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2
  q101 : Eqn
  q101 = sE 1765 lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q102 : Eqn
  q102 = sE 2487 lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q103 : Eqn
  q103 = sE 2519 lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q104 : Eqn
  q104 = sE 2714 lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q105 : Eqn
  q105 = sE 1766 lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q106 : Eqn
  q106 = sE 2230 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2

-- pass [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ [])
  (rw 8 q100 ∷
   rw⁻ 0 q101 ∷
   rw⁻ 1 q102 ∷
   rw 2 q103 ∷
   rw⁻ 6 q104 ∷
   rw⁻ 7 q105 ∷
   rw⁻ 0 q106 ∷ []) Eq.refl

private
  q107 : Eqn
  q107 = sE 2712 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2
  q108 : Eqn
  q108 = sE 2460 lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q109 : Eqn
  q109 = sE 2458 lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q110 : Eqn
  q110 = sE 2706 lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q111 : Eqn
  q111 = sE 2457 lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q112 : Eqn
  q112 = sE 2459 lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q113 : Eqn
  q113 = sE 2712 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2

-- pass [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  (rw 0 q107 ∷
   rw 17 q108 ∷
   rw 14 q109 ∷
   rw 6 q110 ∷
   rw 3 q111 ∷
   rw 0 q112 ∷
   rw⁻ 8 q113 ∷ []) Eq.refl

private
  q114 : Eqn
  q114 = sE 2713 lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2
  q115 : Eqn
  q115 = sE 1144 lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q116 : Eqn
  q116 = sE 1137 lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q117 : Eqn
  q117 = sE 2707 lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q118 : Eqn
  q118 = sE 1135 lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q119 : Eqn
  q119 = sE 1140 lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q120 : Eqn
  q120 = sE 2713 lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2

-- pass [X2 X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ [])
  (rw 0 q114 ∷
   rw 17 q115 ∷
   rw 14 q116 ∷
   rw 6 q117 ∷
   rw 3 q118 ∷
   rw 0 q119 ∷
   rw⁻ 8 q120 ∷ []) Eq.refl

private
  q121 : Eqn
  q121 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q122 : Eqn
  q122 = eqn (K0 ∷ X3 ∷ []) (X3 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑ ↑)))
  q123 : Eqn
  q123 = wE 2494 W
  q124 : Eqn
  q124 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q125 : Eqn
  q125 = eqn (K0⁻ ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑ ↑)))

-- merge3 Gad(t=0, W=(), d=SK, e=1): 6 steps
lem-merge3-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : ⟪ (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-merge3-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = derive (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ [])
  (rw⁻ 8 q121 ∷
   rw⁻ 9 q122 ∷
   rw 6 q123 ∷
   rw 12 q124 ∷
   rw 11 q125 ∷
   rw 2 q21 ∷ []) Eq.refl

private
  q126 : Eqn
  q126 = sE 2708 lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩
  q127 : Eqn
  q127 = wE 1698 W
  q128 : Eqn
  q128 = sE 2709 lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSK-e≡-1⟩

-- CAw1 SS Gad(t=0, W=(), d=SK, e=-1): 4 steps
lem-CAw1-SS-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ : ⟪ (CS01 ∷ CS01 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
lem-CAw1-SS-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ = derive (CS01 ∷ CS01 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (S0⁻ ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ [])
  (rw 1 q126 ∷
   rw 11 q127 ∷
   rw 0 q128 ∷
   rw 8 q127 ∷ []) Eq.refl

private
  q129 : Eqn
  q129 = wE 2495 W
  q130 : Eqn
  q130 = wE 2496 W
  q131 : Eqn
  q131 = wE 2497 W
  q132 : Eqn
  q132 = wE 2498 W

-- spell Gad(t=0, W=(), d=SdK, e=-1) -> Gad(t=0, W=(), d=SK, e=1): 5 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : ⟪ (S0⁻ ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = derive (S0⁻ ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ []) (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ [])
  (rw 0 q129 ∷
   rw 10 q130 ∷
   rw 2 q131 ∷
   rw 7 q132 ∷
   rw 2 q79 ∷ []) Eq.refl

private
  q133 : Eqn
  q133 = sE 2720 lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q133 ∷ []) Eq.refl

private
  q134 : Eqn
  q134 = sE 2236 lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2
  q135 : Eqn
  q135 = sE 2687 lem-pass-CSd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2
  q136 : Eqn
  q136 = sE 2685 lem-pass-CKd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2
  q137 : Eqn
  q137 = sE 2715 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2
  q138 : Eqn
  q138 = sE 2684 lem-pass-CK21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2
  q139 : Eqn
  q139 = sE 2686 lem-pass-CS21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2
  q140 : Eqn
  q140 = sE 2236 lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2

-- pass [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1] [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2]: 7 steps
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = derive (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ [])
  (rw 0 q134 ∷
   rw 7 q135 ∷
   rw 6 q136 ∷
   rw 2 q137 ∷
   rw 1 q138 ∷
   rw 0 q139 ∷
   rw⁻ 10 q140 ∷ []) Eq.refl

private
  q141 : Eqn
  q141 = sE 852 lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q142 : Eqn
  q142 = sE 849 lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q143 : Eqn
  q143 = sE 2688 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q144 : Eqn
  q144 = sE 850 lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q145 : Eqn
  q145 = sE 853 lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 7 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 4 q107 ∷
   rw⁻ 0 q141 ∷
   rw⁻ 3 q142 ∷
   rw 6 q143 ∷
   rw⁻ 14 q144 ∷
   rw⁻ 17 q145 ∷
   rw⁻ 0 q113 ∷ []) Eq.refl

private
  q146 : Eqn
  q146 = sE 2703 lem-pass-CSd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3
  q147 : Eqn
  q147 = sE 2701 lem-pass-CKd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3
  q148 : Eqn
  q148 = sE 2717 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3
  q149 : Eqn
  q149 = sE 2700 lem-pass-CK31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3
  q150 : Eqn
  q150 = sE 2702 lem-pass-CS31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3

-- pass [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 7 steps
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ [])
  (rw 0 q87 ∷
   rw 7 q146 ∷
   rw 6 q147 ∷
   rw 2 q148 ∷
   rw 1 q149 ∷
   rw 0 q150 ∷
   rw⁻ 10 q92 ∷ []) Eq.refl

private
  q151 : Eqn
  q151 = sE 2484 lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2
  q152 : Eqn
  q152 = sE 869 lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q153 : Eqn
  q153 = sE 2059 lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q154 : Eqn
  q154 = sE 2716 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q155 : Eqn
  q155 = sE 2245 lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q156 : Eqn
  q156 = sE 904 lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q157 : Eqn
  q157 = sE 2484 lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 7 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 4 q151 ∷
   rw⁻ 0 q152 ∷
   rw⁻ 3 q153 ∷
   rw 6 q154 ∷
   rw⁻ 12 q155 ∷
   rw⁻ 15 q156 ∷
   rw⁻ 0 q157 ∷ []) Eq.refl
