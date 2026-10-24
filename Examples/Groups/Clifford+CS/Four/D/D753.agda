{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD753 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D753 (W : Ws) (Sᴰ : SD753) where

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
  lem-b2g-1001R0 : St 2722
  lem-b2g-1001R0 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-X3 : St 1162
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-X3 = pickᴰ 1 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd30-X3 : St 1163
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd30-X3 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK30-X3 : St 1216
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK30-X3 = pickᴰ 3 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd30-X3 : St 1217
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd30-X3 = pickᴰ 4 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-X3 : St 1871
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-X3 = pickᴰ 5 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd03-X3 : St 1872
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd03-X3 = pickᴰ 6 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-X3 : St 2723
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-X3 = pickᴰ 7 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd03-X3 : St 2724
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd03-X3 = pickᴰ 8 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 840
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 9 Sᴰ
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 869
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 10 Sᴰ
  lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 904
  lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 11 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 12 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1143
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 13 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 1146
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 14 Sᴰ
  lem-pass-CK31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2725
  lem-pass-CK31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 15 Sᴰ
  lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1765
  lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 16 Sᴰ
  lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1766
  lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 17 Sᴰ
  lem-pass-CKd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : St 2726
  lem-pass-CKd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = pickᴰ 18 Sᴰ
  lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 1747
  lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 19 Sᴰ
  lem-pass-CS21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : St 2727
  lem-pass-CS21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = pickᴰ 20 Sᴰ
  lem-S2 : St 1778
  lem-S2 = pickᴰ 21 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2034
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 22 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2038
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 23 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2049
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 24 Sᴰ
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2059
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 25 Sᴰ
  lem-ROT-gad : St 2261
  lem-ROT-gad = pickᴰ 26 Sᴰ
  lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2231
  lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 27 Sᴰ
  lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2244
  lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 28 Sᴰ
  lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2245
  lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 29 Sᴰ
  lem-PP2≡E : St 2474
  lem-PP2≡E = pickᴰ 30 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 : St 2505
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 = pickᴰ 31 Sᴰ
  lem-CA-CKd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩ : St 2728
  lem-CA-CKd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩ = pickᴰ 32 Sᴰ
  lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ : St 2729
  lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ = pickᴰ 33 Sᴰ
  lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ : St 2730
  lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 34 Sᴰ
  lem-pass-CSd30-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3 : St 2731
  lem-pass-CSd30-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3 = pickᴰ 35 Sᴰ
  lem-PP4 : St 2672
  lem-PP4 = pickᴰ 36 Sᴰ
  lem-ROT2≡E : St 2673
  lem-ROT2≡E = pickᴰ 37 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 : St 2712
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 = pickᴰ 38 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2 : St 2713
  lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2 = pickᴰ 39 Sᴰ
  lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 : St 2732
  lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 = pickᴰ 40 Sᴰ
  lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2714
  lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 41 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2733
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 42 Sᴰ
  lem-pass-CS31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2734
  lem-pass-CS31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 43 Sᴰ
  lem-pass-CS32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : St 2735
  lem-pass-CS32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = pickᴰ 44 Sᴰ
  lem-pass-CSd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : St 2736
  lem-pass-CSd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = pickᴰ 45 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : St 2737
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = pickᴰ 46 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : St 2738
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = pickᴰ 47 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : St 2739
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = pickᴰ 48 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 2740
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 49 Sᴰ
  lem-CA-CK20-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡-1⟩ : St 2741
  lem-CA-CK20-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡-1⟩ = pickᴰ 50 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩-3 : St 2742
  lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩-3 = pickᴰ 51 Sᴰ
  lem-pass-CCZ123-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 2743
  lem-pass-CCZ123-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 52 Sᴰ
  lem-pass-CK21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : St 2744
  lem-pass-CK21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = pickᴰ 53 Sᴰ
  lem-pass-CK32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 2745
  lem-pass-CK32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 54 Sᴰ
  lem-pass-CKd32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 2746
  lem-pass-CKd32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 55 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2747
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 56 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2748
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 57 Sᴰ
  lem-pass-X1-CK10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : St 2749
  lem-pass-X1-CK10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = pickᴰ 58 Sᴰ
  lem-pass-X1-CKd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2750
  lem-pass-X1-CKd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 59 Sᴰ
  lem-pass-X1-CS10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : St 2751
  lem-pass-X1-CS10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = pickᴰ 60 Sᴰ
  lem-pass-X2-CKd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2752
  lem-pass-X2-CKd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 61 Sᴰ
  lem-pass-X2-CKd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : St 2753
  lem-pass-X2-CKd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = pickᴰ 62 Sᴰ
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ : St 2754
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ = pickᴰ 63 Sᴰ
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ : St 2755
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 64 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ : St 2756
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ = pickᴰ 65 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ : St 2757
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 66 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ : St 2758
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 67 Sᴰ
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ : St 2759
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ = pickᴰ 68 Sᴰ
  lem-pass-CK10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 2760
  lem-pass-CK10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 69 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2761
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 70 Sᴰ
  lem-pass-X2-CK21-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : St 2762
  lem-pass-X2-CK21-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = pickᴰ 71 Sᴰ

private
  q1 : Eqn
  q1 = sE 2713 lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2
  q2 : Eqn
  q2 = sE 869 lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q3 : Eqn
  q3 = sE 2059 lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q4 : Eqn
  q4 = sE 2740 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q5 : Eqn
  q5 = sE 2245 lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q6 : Eqn
  q6 = sE 904 lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q7 : Eqn
  q7 = sE 2713 lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2 X3]: 7 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : ⟪ (ℓ "习丽习举丘丞与丐习丽习举丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐习丽习举丑丏丘丞习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = derive (ℓ "习丽习举丘丞与丐习丽习举丑丏丘丞") (ℓ "丘丞与丐习丽习举丑丏丘丞习丽习举")
  (rw 4 q1 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 3 q3 ∷
   rw 6 q4 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 17 q6 ∷
   rw⁻ 0 q7 ∷ []) Eq.refl

private
  q8 : Eqn
  q8 = sE 2672 lem-PP4

-- cls 0000PP0 0000PP0 0000PP0 0000PP0 = e: 1 steps
lem-cls-0000PP0-0000PP0-0000PP0-0000PP0-≡-e : ⟪ (ℓ "九中九丮九中九丮九中九丮九中九丮") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-cls-0000PP0-0000PP0-0000PP0-0000PP0-≡-e = derive (ℓ "九中九丮九中九丮九中九丮九中九丮") []
  (rw 0 q8 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = sE 2474 lem-PP2≡E
  q10 : Eqn
  q10 = sE 2673 lem-ROT2≡E
  q11 : Eqn
  q11 = sE 2261 lem-ROT-gad

-- cls 0000PP0 0000PP0 = 0000R0 0000R0: 4 steps
lem-cls-0000PP0-0000PP0-≡-0000R0-0000R0 : ⟪ (ℓ "九中九丮九中九丮") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丈上中九丮九下三") ⟫ʷ
lem-cls-0000PP0-0000PP0-≡-0000R0-0000R0 = derive (ℓ "九中九丮九中九丮") (ℓ "丈上中九丮九下三丈上中九丮九下三")
  (rw 0 q9 ∷
   rw⁻ 0 q10 ∷
   rw 0 q11 ∷
   rw 8 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = sE 2722 lem-b2g-1001R0
  q13 : Eqn
  q13 = sE 2737 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3
  q14 : Eqn
  q14 = sE 2722 lem-b2g-1001R0

-- cls 0000PP0 1001R0 = 1001R0 0000PP0: 3 steps
lem-cls-0000PP0-1001R0-≡-1001R0-0000PP0 : ⟪ (ℓ "九中九丮丌丞丈上中九丮九下三丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丈上中九丮九下三丌丞九中九丮") ⟫ʷ
lem-cls-0000PP0-1001R0-≡-1001R0-0000PP0 = derive (ℓ "九中九丮丌丞丈上中九丮九下三丌丞") (ℓ "丌丞丈上中九丮九下三丌丞九中九丮")
  (rw 4 q12 ∷
   rw 0 q13 ∷
   rw⁻ 0 q14 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = sE 1778 lem-S2
  q16 : Eqn
  q16 = sE 2739 lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3
  q17 : Eqn
  q17 = sE 1778 lem-S2

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 TOFF201 CS23 TOFF201 CSd23 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : ⟪ (ℓ "九中九丮丞乣义乣乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞乣义乣乊丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = derive (ℓ "九中九丮丞乣义乣乊丞") (ℓ "丞乣义乣乊丞九中九丮")
  (rw 0 q15 ∷
   rw 0 q16 ∷
   rw⁻ 6 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q19 : Eqn
  q19 = eqn (ℓ "丌与") (ℓ "与丌") (low₁-comm (X) (S))
  q20 : Eqn
  q20 = eqn (ℓ "丐丞") (ℓ "丞丐") (low-comm ((K ↑)) ((X ↑)))
  q21 : Eqn
  q21 = eqn (ℓ "丌丐") (ℓ "丐丌") (low₁-comm (X) (K))
  q22 : Eqn
  q22 = eqn (ℓ "丌丏") (ℓ "丏丌") (low₁-comm (X) ((S • S • S)))
  q23 : Eqn
  q23 = eqn (ℓ "丌丑") (ℓ "丑丌") (low₁-comm (X) ((K • iI)))
  q24 : Eqn
  q24 = eqn (ℓ "丏丞") (ℓ "丞丏") (low-comm (((S • S • S) ↑)) ((X ↑)))
  q25 : Eqn
  q25 = eqn (ℓ "丑丞") (ℓ "丞丑") (low-comm (((K • iI) ↑)) ((X ↑)))
  q26 : Eqn
  q26 = wE 2225 W
  q27 : Eqn
  q27 = wE 2226 W
  q28 : Eqn
  q28 = sE 2725 lem-pass-CK31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3
  q29 : Eqn
  q29 = sE 2734 lem-pass-CS31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3
  q30 : Eqn
  q30 = wE 2227 W

-- ca-split Gad(t=1, W=(0, 3), d=SK, e=-1) 3: 13 steps
lem-ca-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩-3 : ⟪ (ℓ "丌丞与丐丽习举习丑丏丌丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞") ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩-3 = derive (ℓ "丌丞与丐丽习举习丑丏丌丞") (ℓ "丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞")
  (rw⁻ 1 q18 ∷
   rw 0 q19 ∷
   rw⁻ 2 q20 ∷
   rw 1 q21 ∷
   rw⁻ 9 q22 ∷
   rw⁻ 8 q23 ∷
   rw 10 q24 ∷
   rw 9 q25 ∷
   rw 0 q26 ∷
   rw 16 q27 ∷
   rw 7 q28 ∷
   rw 6 q29 ∷
   rw 14 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = sE 2505 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3
  q32 : Eqn
  q32 = sE 2049 lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q33 : Eqn
  q33 = sE 1146 lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q34 : Eqn
  q34 = sE 2038 lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q35 : Eqn
  q35 = sE 2733 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q36 : Eqn
  q36 = sE 840 lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q37 : Eqn
  q37 = sE 2505 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3

-- pass [CS03 TOFF012 CSd03 TOFF012] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 11 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "中九丮九丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "中九丮九丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞中九丮九")
  (rw 4 q31 ∷
   rw⁻ 0 q32 ∷
   rw⁻ 3 q33 ∷
   rw⁻ 6 q34 ∷
   rw⁻ 9 q34 ∷
   rw 12 q35 ∷
   rw⁻ 18 q32 ∷
   rw⁻ 21 q32 ∷
   rw⁻ 24 q36 ∷
   rw⁻ 27 q34 ∷
   rw⁻ 0 q37 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = eqn (ℓ "丕丞") (ℓ "丞丕") (low₃-comm (((S • S • S) ↑ ↑)) (X))
  q39 : Eqn
  q39 = eqn (ℓ "丌丕") (ℓ "丕丌") (low₁-comm (X) (((S • S • S) ↑)))
  q40 : Eqn
  q40 = eqn (ℓ "丗丞") (ℓ "丞丗") (low₃-comm (((K • iI) ↑ ↑)) (X))
  q41 : Eqn
  q41 = eqn (ℓ "丌丗") (ℓ "丗丌") (low₁-comm (X) (((K • iI) ↑)))
  q42 : Eqn
  q42 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q43 : Eqn
  q43 = eqn (ℓ "丌且") (ℓ "且丌") (low₁-comm (X) ((S ↑)))
  q44 : Eqn
  q44 = eqn (ℓ "丌世") (ℓ "世丌") (low₁-comm (X) ((K ↑)))
  q45 : Eqn
  q45 = eqn (ℓ "世丞") (ℓ "丞世") (low₃-comm ((K ↑ ↑)) (X))
  q46 : Eqn
  q46 = wE 2412 W
  q47 : Eqn
  q47 = wE 2413 W
  q48 : Eqn
  q48 = sE 2735 lem-pass-CS32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3
  q49 : Eqn
  q49 = sE 2726 lem-pass-CKd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3
  q50 : Eqn
  q50 = sE 2736 lem-pass-CSd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3
  q51 : Eqn
  q51 = wE 2414 W

-- ca-split Gad(t=2, W=(0, 3), d=SdKdSS, e=-1) 3: 23 steps
lem-ca-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩-3 : ⟪ (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞") ⟫ʷ
lem-ca-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩-3 = derive (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞") (ℓ "丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞")
  (rw⁻ 1 q38 ∷
   rw 0 q39 ∷
   rw⁻ 2 q40 ∷
   rw 1 q41 ∷
   rw⁻ 3 q42 ∷
   rw 2 q43 ∷
   rw⁻ 4 q42 ∷
   rw 3 q43 ∷
   rw⁻ 13 q43 ∷
   rw⁻ 12 q44 ∷
   rw⁻ 11 q39 ∷
   rw⁻ 10 q39 ∷
   rw 14 q42 ∷
   rw 13 q45 ∷
   rw 12 q38 ∷
   rw 11 q38 ∷
   rw 0 q46 ∷
   rw 24 q47 ∷
   rw 15 q48 ∷
   rw 14 q48 ∷
   rw 13 q49 ∷
   rw 12 q50 ∷
   rw 20 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = sE 2738 lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3

-- pass [TOFF012 CS03 TOFF012 CSd03] [X0 X3 TOFF201 CS23 TOFF201 CSd23 X0 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : ⟪ (ℓ "九中九丮丌丞乣义乣乊丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞乣义乣乊丌丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = derive (ℓ "九中九丮丌丞乣义乣乊丌丞") (ℓ "丌丞乣义乣乊丌丞九中九丮")
  (rw 0 q15 ∷
   rw 0 q52 ∷
   rw⁻ 8 q17 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = sE 2712 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2
  q54 : Eqn
  q54 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q55 : Eqn
  q55 = sE 2034 lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q56 : Eqn
  q56 = sE 2748 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q57 : Eqn
  q57 = sE 2244 lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q58 : Eqn
  q58 = sE 1143 lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q59 : Eqn
  q59 = sE 2712 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2

-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 7 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (ℓ "中九丮九丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丈上中九丮九下三丘丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (ℓ "中九丮九丘丞丈上中九丮九下三丘丞") (ℓ "丘丞丈上中九丮九下三丘丞中九丮九")
  (rw 4 q53 ∷
   rw⁻ 0 q54 ∷
   rw⁻ 3 q55 ∷
   rw 6 q56 ∷
   rw⁻ 14 q57 ∷
   rw⁻ 17 q58 ∷
   rw⁻ 0 q59 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = wE 1478 W
  q61 : Eqn
  q61 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q62 : Eqn
  q62 = sE 2753 lem-pass-X2-CKd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3
  q63 : Eqn
  q63 = wE 1479 W

-- pass [CKd21] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (ℓ "么丘丞丽习举习丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丽习举习丘丞么") ⟫ʷ
lem-pass-CKd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = derive (ℓ "么丘丞丽习举习丘丞") (ℓ "丘丞丽习举习丘丞么")
  (rw 0 q60 ∷
   rw 9 q61 ∷
   rw 1 q62 ∷
   rw 7 q63 ∷
   rw⁻ 6 q61 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 2415 W
  q65 : Eqn
  q65 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q66 : Eqn
  q66 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q67 : Eqn
  q67 = sE 2750 lem-pass-X1-CKd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q68 : Eqn
  q68 = wE 2416 W

-- pass [CKd10] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 7 steps
lem-pass-CKd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (ℓ "丵丒丘丞中九丮九丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞中九丮九丒丘丞丵") ⟫ʷ
lem-pass-CKd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (ℓ "丵丒丘丞中九丮九丒丘丞") (ℓ "丒丘丞中九丮九丒丘丞丵")
  (rw 0 q64 ∷
   rw 10 q65 ∷
   rw 11 q66 ∷
   rw 1 q67 ∷
   rw 9 q68 ∷
   rw⁻ 8 q66 ∷
   rw⁻ 7 q65 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = wE 2205 W
  q70 : Eqn
  q70 = sE 2749 lem-pass-X1-CK10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3
  q71 : Eqn
  q71 = wE 2206 W

-- pass [CK10] [X1 X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X1 X2 X3]: 7 steps
lem-pass-CK10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 : ⟪ (ℓ "临丒丘丞三下丈丈中九丮九三三上丈丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞临") ⟫ʷ
lem-pass-CK10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 = derive (ℓ "临丒丘丞三下丈丈中九丮九三三上丈丒丘丞") (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞临")
  (rw 0 q69 ∷
   rw 18 q65 ∷
   rw 19 q66 ∷
   rw 1 q70 ∷
   rw 17 q71 ∷
   rw⁻ 16 q66 ∷
   rw⁻ 15 q65 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 1714 W
  q73 : Eqn
  q73 = sE 2751 lem-pass-X1-CS10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3
  q74 : Eqn
  q74 = wE 1715 W

-- pass [CS10] [X1 X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X1 X2 X3]: 7 steps
lem-pass-CS10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 : ⟪ (ℓ "丠丒丘丞三下丈丈中九丮九三三上丈丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞丠") ⟫ʷ
lem-pass-CS10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 = derive (ℓ "丠丒丘丞三下丈丈中九丮九三三上丈丒丘丞") (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞丠")
  (rw 0 q72 ∷
   rw 18 q65 ∷
   rw 19 q66 ∷
   rw 1 q73 ∷
   rw 17 q74 ∷
   rw⁻ 16 q66 ∷
   rw⁻ 15 q65 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q76 : Eqn
  q76 = sE 2752 lem-pass-X2-CKd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3

-- pass [CKd21] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 7 steps
lem-pass-CKd21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "么丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞么") ⟫ʷ
lem-pass-CKd21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "么丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞么")
  (rw 1 q75 ∷
   rw 0 q60 ∷
   rw 11 q61 ∷
   rw 1 q76 ∷
   rw 9 q63 ∷
   rw⁻ 0 q75 ∷
   rw⁻ 8 q61 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q78 : Eqn
  q78 = eqn (ℓ "丐丘") (ℓ "丘丐") (low-comm ((K ↑)) (X))
  q79 : Eqn
  q79 = eqn (ℓ "丏丘") (ℓ "丘丏") (low-comm (((S • S • S) ↑)) (X))
  q80 : Eqn
  q80 = eqn (ℓ "丑丘") (ℓ "丘丑") (low-comm (((K • iI) ↑)) (X))
  q81 : Eqn
  q81 = wE 2228 W
  q82 : Eqn
  q82 = wE 2229 W
  q83 : Eqn
  q83 = sE 2744 lem-pass-CK21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3
  q84 : Eqn
  q84 = sE 2727 lem-pass-CS21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3
  q85 : Eqn
  q85 = wE 2230 W

-- ca-split Gad(t=1, W=(2, 3), d=SK, e=-1) 2: 13 steps
lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 : ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘") ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 = derive (ℓ "丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘")
  (rw⁻ 1 q18 ∷
   rw⁻ 0 q77 ∷
   rw⁻ 2 q20 ∷
   rw⁻ 1 q78 ∷
   rw 9 q79 ∷
   rw 8 q80 ∷
   rw 10 q24 ∷
   rw 9 q25 ∷
   rw 0 q81 ∷
   rw 16 q82 ∷
   rw 7 q83 ∷
   rw 6 q84 ∷
   rw 14 q85 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = sE 1871 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-X3
  q87 : Eqn
  q87 = sE 1162 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-X3
  q88 : Eqn
  q88 = sE 2747 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q89 : Eqn
  q89 = sE 1163 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd30-X3
  q90 : Eqn
  q90 = sE 1872 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd03-X3

-- Bar(SSKSKK;3,2->0) passes split Gad(t=0, W=(3,), d=SK, e=-1): 5 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞") (ℓ "丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q86 ∷
   rw 3 q87 ∷
   rw 6 q88 ∷
   rw 12 q89 ∷
   rw 15 q90 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = wE 2297 W
  q92 : Eqn
  q92 = sE 2746 lem-pass-CKd32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3
  q93 : Eqn
  q93 = sE 2743 lem-pass-CCZ123-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3
  q94 : Eqn
  q94 = sE 2745 lem-pass-CK32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3
  q95 : Eqn
  q95 = wE 2298 W

-- pass [TOFF213] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 5 steps
lem-pass-TOFF213-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "乥丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞乥") ⟫ʷ
lem-pass-TOFF213-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "乥丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞乥")
  (rw 0 q91 ∷
   rw 2 q92 ∷
   rw 1 q93 ∷
   rw 0 q94 ∷
   rw 10 q95 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = wE 5 W
  q97 : Eqn
  q97 = wE 7 W
  q98 : Eqn
  q98 = wE 140 W
  q99 : Eqn
  q99 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q100 : Eqn
  q100 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q101 : Eqn
  q101 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q102 : Eqn
  q102 = wE 2423 W
  q103 : Eqn
  q103 = wE 27 W
  q104 : Eqn
  q104 = wE 142 W
  q105 : Eqn
  q105 = wE 29 W
  q106 : Eqn
  q106 = wE 139 W
  q107 : Eqn
  q107 = wE 31 W
  q108 : Eqn
  q108 = sE 2728 lem-CA-CKd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩
  q109 : Eqn
  q109 = sE 2731 lem-pass-CSd30-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3
  q110 : Eqn
  q110 = sE 2741 lem-CA-CK20-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡-1⟩
  q111 : Eqn
  q111 = sE 2231 lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q112 : Eqn
  q112 = wE 137 W
  q113 : Eqn
  q113 = wE 76 W
  q114 : Eqn
  q114 = wE 2424 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 144 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中九丮九丞") (ℓ "丞中九丮九丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 31 q96 ∷
   rw 30 q97 ∷
   rw 29 q97 ∷
   rw 28 q98 ∷
   rw 27 q97 ∷
   rw 26 q97 ∷
   rw 25 q97 ∷
   rw⁻ 24 q99 ∷
   rw 23 q97 ∷
   rw 22 q97 ∷
   rw 21 q97 ∷
   rw 20 q97 ∷
   rw 19 q97 ∷
   rw 18 q97 ∷
   rw 17 q97 ∷
   rw 16 q97 ∷
   rw 15 q97 ∷
   rw⁻ 14 q100 ∷
   rw 13 q98 ∷
   rw 12 q97 ∷
   rw 11 q97 ∷
   rw 10 q97 ∷
   rw 9 q97 ∷
   rw 8 q97 ∷
   rw 7 q97 ∷
   rw⁻ 6 q99 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q101 ∷
   rw 6 q97 ∷
   rw⁻ 5 q101 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q101 ∷
   rw 5 q97 ∷
   rw⁻ 4 q101 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q101 ∷
   rw 4 q98 ∷
   rw⁻ 3 q101 ∷
   re 4 3 (ℓ "乔") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q101 ∷
   rw 3 q97 ∷
   rw⁻ 2 q101 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q101 ∷
   rw 2 q97 ∷
   rw⁻ 1 q101 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q101 ∷
   rw 1 q97 ∷
   rw⁻ 0 q101 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q102 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q101 ∷
   rw 1 q103 ∷
   rw 2 q101 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q104 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q101 ∷
   rw 3 q105 ∷
   rw 4 q101 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q106 ∷
   rw 4 q107 ∷
   rw 3 q108 ∷
   rw 2 q109 ∷
   rw 1 q110 ∷
   rw 0 q111 ∷
   rw 10 q96 ∷
   rw 9 q112 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw⁻ 10 q101 ∷
   rw 9 q113 ∷
   rw⁻ 8 q101 ∷
   re 9 3 (ℓ "举") ∷
   rw 7 q98 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q101 ∷
   rw 7 q97 ∷
   rw⁻ 6 q101 ∷
   re 7 3 (ℓ "丽") ∷
   rw 7 q114 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q101 ∷
   rw 7 q103 ∷
   rw 8 q101 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q101 ∷
   rw 8 q103 ∷
   rw 9 q101 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q101 ∷
   rw 9 q103 ∷
   rw 10 q101 ∷
   re 8 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏乇乏") ∷
   rw 9 q101 ∷
   rw 10 q104 ∷
   rw 11 q101 ∷
   re 9 3 (ℓ "乑") ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q101 ∷
   rw 11 q103 ∷
   rw 12 q101 ∷
   re 10 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q101 ∷
   rw 12 q103 ∷
   rw 13 q101 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q99 ∷
   rw 13 q103 ∷
   rw 14 q103 ∷
   rw 15 q103 ∷
   rw 16 q103 ∷
   rw 17 q103 ∷
   rw 18 q103 ∷
   rw 19 q104 ∷
   rw 20 q100 ∷
   rw 21 q103 ∷
   rw 22 q103 ∷
   rw 23 q103 ∷
   rw 24 q103 ∷
   rw 25 q103 ∷
   rw 26 q103 ∷
   rw 27 q103 ∷
   rw 28 q103 ∷
   rw 29 q103 ∷
   rw 30 q99 ∷
   rw 31 q103 ∷
   rw 32 q103 ∷
   rw 33 q103 ∷
   rw 34 q104 ∷
   rw 35 q103 ∷
   rw 36 q103 ∷
   rw 37 q107 ∷ []) Eq.refl

private
  q115 : Eqn
  q115 = sE 2723 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-X3
  q116 : Eqn
  q116 = sE 1216 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK30-X3
  q117 : Eqn
  q117 = sE 2761 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q118 : Eqn
  q118 = sE 1217 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd30-X3
  q119 : Eqn
  q119 = sE 2724 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd03-X3

-- Bar(SSKSKK;3,1->0) passes split Gad(t=0, W=(3,), d=SK, e=-1): 5 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞") (ℓ "丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 0 q115 ∷
   rw 3 q116 ∷
   rw 6 q117 ∷
   rw 12 q118 ∷
   rw 15 q119 ∷ []) Eq.refl

private
  q120 : Eqn
  q120 = sE 2742 lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩-3
  q121 : Eqn
  q121 = sE 2756 lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩
  q122 : Eqn
  q122 = sE 2742 lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩-3

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞与丐丽习举习丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐丽习举习丑丏丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞与丐丽习举习丑丏丞") (ℓ "丞与丐丽习举习丑丏丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q120 ∷
   rw 0 q121 ∷
   rw⁻ 0 q122 ∷ []) Eq.refl

private
  q123 : Eqn
  q123 = sE 2729 lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩

-- pass [CCZ123] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 3 steps
lem-pass-CCZ123-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (ℓ "乜丞与丐丽习举习丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐丽习举习丑丏丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (ℓ "乜丞与丐丽习举习丑丏丞") (ℓ "丞与丐丽习举习丑丏丞乜")
  (rw 1 q120 ∷
   rw 0 q123 ∷
   rw⁻ 0 q122 ∷ []) Eq.refl

private
  q124 : Eqn
  q124 = sE 2759 lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞与丐丽习举习丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐丽习举习丑丏丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞与丐丽习举习丑丏丞") (ℓ "丞与丐丽习举习丑丏丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 31 q120 ∷
   rw 0 q124 ∷
   rw⁻ 0 q122 ∷ []) Eq.refl

private
  q125 : Eqn
  q125 = sE 2754 lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞与丐丽习举习丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐丽习举习丑丏丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞与丐丽习举习丑丏丞") (ℓ "丞与丐丽习举习丑丏丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q120 ∷
   rw 0 q125 ∷
   rw⁻ 0 q122 ∷ []) Eq.refl

private
  q126 : Eqn
  q126 = sE 2732 lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3
  q127 : Eqn
  q127 = sE 2755 lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩
  q128 : Eqn
  q128 = sE 2732 lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ ≈ ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丕丗且且义乣乊乣丕丕世且丞") (ℓ "丞丕丗且且义乣乊乣丕丕世且丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q126 ∷
   rw 0 q127 ∷
   rw⁻ 0 q128 ∷ []) Eq.refl

private
  q129 : Eqn
  q129 = sE 2730 lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CCZ123] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 3 steps
lem-pass-CCZ123-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (ℓ "乜丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ ≈ ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (ℓ "乜丞丕丗且且义乣乊乣丕丕世且丞") (ℓ "丞丕丗且且义乣乊乣丕丕世且丞乜")
  (rw 1 q126 ∷
   rw 0 q129 ∷
   rw⁻ 0 q128 ∷ []) Eq.refl

private
  q130 : Eqn
  q130 = sE 2758 lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ ≈ ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞丕丗且且义乣乊乣丕丕世且丞") (ℓ "丞丕丗且且义乣乊乣丕丕世且丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 31 q126 ∷
   rw 0 q130 ∷
   rw⁻ 0 q128 ∷ []) Eq.refl

private
  q131 : Eqn
  q131 = sE 2757 lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ ≈ ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丕丗且且义乣乊乣丕丕世且丞") (ℓ "丞丕丗且且义乣乊乣丕丕世且丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q126 ∷
   rw 0 q131 ∷
   rw⁻ 0 q128 ∷ []) Eq.refl

private
  q132 : Eqn
  q132 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q133 : Eqn
  q133 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q134 : Eqn
  q134 = eqn (ℓ "丈丒") (ℓ "丒丈") (low₁-comm (S) (X))
  q135 : Eqn
  q135 = eqn (ℓ "上丞") (ℓ "丞上") (low₁-comm (K) ((X ↑ ↑)))
  q136 : Eqn
  q136 = eqn (ℓ "上丘") (ℓ "丘上") (low₁-comm (K) ((X ↑)))
  q137 : Eqn
  q137 = eqn (ℓ "上丒") (ℓ "丒上") (low₁-comm (K) (X))
  q138 : Eqn
  q138 = eqn (ℓ "三丒") (ℓ "丒三") (low₁-comm ((S • S • S)) (X))
  q139 : Eqn
  q139 = eqn (ℓ "下丒") (ℓ "丒下") (low₁-comm ((K • iI)) (X))
  q140 : Eqn
  q140 = eqn (ℓ "三丘") (ℓ "丘三") (low₁-comm ((S • S • S)) ((X ↑)))
  q141 : Eqn
  q141 = eqn (ℓ "下丘") (ℓ "丘下") (low₁-comm ((K • iI)) ((X ↑)))
  q142 : Eqn
  q142 = eqn (ℓ "三丞") (ℓ "丞三") (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q143 : Eqn
  q143 = eqn (ℓ "下丞") (ℓ "丞下") (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q144 : Eqn
  q144 = wE 2499 W
  q145 : Eqn
  q145 = wE 2500 W
  q146 : Eqn
  q146 = sE 2760 lem-pass-CK10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q147 : Eqn
  q147 = sE 1747 lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q148 : Eqn
  q148 = wE 2501 W

-- ca-split Gad(t=0, W=(1, 2, 3), d=SK, e=-1) 1: 17 steps
lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩-1 : ⟪ (ℓ "丒丘丞丈上中九丮九下三丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒") ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩-1 = derive (ℓ "丒丘丞丈上中九丮九下三丒丘丞") (ℓ "丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒")
  (rw⁻ 2 q132 ∷
   rw⁻ 1 q133 ∷
   rw⁻ 0 q134 ∷
   rw⁻ 3 q135 ∷
   rw⁻ 2 q136 ∷
   rw⁻ 1 q137 ∷
   rw 10 q138 ∷
   rw 9 q139 ∷
   rw 11 q140 ∷
   rw 10 q141 ∷
   rw 12 q142 ∷
   rw 11 q143 ∷
   rw 0 q144 ∷
   rw 18 q145 ∷
   rw 7 q146 ∷
   rw 6 q147 ∷
   rw 16 q148 ∷ []) Eq.refl

private
  q149 : Eqn
  q149 = wE 1476 W
  q150 : Eqn
  q150 = sE 2762 lem-pass-X2-CK21-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3
  q151 : Eqn
  q151 = wE 1477 W

-- pass [CK21] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (ℓ "乇丘丞丏丑与与丽习举习丏丏丐与丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞乇") ⟫ʷ
lem-pass-CK21-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (ℓ "乇丘丞丏丑与与丽习举习丏丏丐与丘丞") (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞乇")
  (rw 0 q149 ∷
   rw 17 q61 ∷
   rw 1 q150 ∷
   rw 15 q151 ∷
   rw⁻ 14 q61 ∷ []) Eq.refl

private
  q152 : Eqn
  q152 = wE 2239 W
  q153 : Eqn
  q153 = wE 2240 W
  q154 : Eqn
  q154 = sE 1765 lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q155 : Eqn
  q155 = sE 2714 lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q156 : Eqn
  q156 = sE 1766 lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q157 : Eqn
  q157 = wE 2241 W

-- ca-split Gad(t=0, W=(2, 3), d=SdKdSS, e=-1) 2: 23 steps
lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2 : ⟪ (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘") ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2 = derive (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘")
  (rw⁻ 1 q142 ∷
   rw⁻ 0 q140 ∷
   rw⁻ 2 q143 ∷
   rw⁻ 1 q141 ∷
   rw⁻ 3 q132 ∷
   rw⁻ 2 q133 ∷
   rw⁻ 4 q132 ∷
   rw⁻ 3 q133 ∷
   rw 13 q133 ∷
   rw 12 q136 ∷
   rw 11 q140 ∷
   rw 10 q140 ∷
   rw 14 q132 ∷
   rw 13 q135 ∷
   rw 12 q142 ∷
   rw 11 q142 ∷
   rw 0 q152 ∷
   rw 24 q153 ∷
   rw 15 q154 ∷
   rw 14 q154 ∷
   rw 13 q155 ∷
   rw 12 q156 ∷
   rw 20 q157 ∷ []) Eq.refl
