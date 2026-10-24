{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD760 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D760 (W : Ws) (Sᴰ : SD760) where

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
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CK30-X3 : St 1214
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CK30-X3 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CKd30-X3 : St 1215
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CKd30-X3 = pickᴰ 1 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-X3 : St 2870
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-X3 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CSd03-X3 : St 2871
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CSd03-X3 = pickᴰ 3 Sᴰ
  lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 866
  lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 4 Sᴰ
  lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 867
  lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 5 Sᴰ
  lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 868
  lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 6 Sᴰ
  lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 871
  lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 7 Sᴰ
  lem-g-b : St 2872
  lem-g-b = pickᴰ 8 Sᴰ
  lem-pass-CK21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : St 2873
  lem-pass-CK21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = pickᴰ 9 Sᴰ
  lem-pass-CKd21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : St 2874
  lem-pass-CKd21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = pickᴰ 10 Sᴰ
  lem-pass-CSd21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : St 2875
  lem-pass-CSd21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = pickᴰ 11 Sᴰ
  lem-pass-CS21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : St 2876
  lem-pass-CS21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = pickᴰ 12 Sᴰ
  lem-S3 : St 1623
  lem-S3 = pickᴰ 13 Sᴰ
  lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 1747
  lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 14 Sᴰ
  lem-pass-CS21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 2765
  lem-pass-CS21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 15 Sᴰ
  lem-pass-CS21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : St 2727
  lem-pass-CS21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = pickᴰ 16 Sᴰ
  lem-pass-CSd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 1748
  lem-pass-CSd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 17 Sᴰ
  lem-pass-CSd21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 2877
  lem-pass-CSd21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 18 Sᴰ
  lem-pass-CSd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : St 2878
  lem-pass-CSd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = pickᴰ 19 Sᴰ
  lem-S2-at1023 : St 1918
  lem-S2-at1023 = pickᴰ 20 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ : St 2879
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ = pickᴰ 21 Sᴰ
  lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2036
  lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 22 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2037
  lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 23 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2039
  lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 24 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2042
  lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 25 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : St 2880
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = pickᴰ 26 Sᴰ
  lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ : St 2881
  lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ = pickᴰ 27 Sᴰ
  lem-ROT-gad : St 2261
  lem-ROT-gad = pickᴰ 28 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 : St 2230
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 = pickᴰ 29 Sᴰ
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03-ᵖ-1 : St 2882
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03-ᵖ-1 = pickᴰ 30 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-3 : St 2470
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-3 = pickᴰ 31 Sᴰ
  lem-pass-X3-CK30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2883
  lem-pass-X3-CK30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 32 Sᴰ
  lem-pass-X3-CKd30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2884
  lem-pass-X3-CKd30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 33 Sᴰ
  lem-pass-X3-CS30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2885
  lem-pass-X3-CS30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 34 Sᴰ
  lem-pass-X3-CSd30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2886
  lem-pass-X3-CSd30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 35 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2 : St 2236
  lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2 = pickᴰ 36 Sᴰ
  lem-pass-X2-CK20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2698
  lem-pass-X2-CK20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 37 Sᴰ
  lem-pass-X2-CSd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2699
  lem-pass-X2-CSd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 38 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 : St 2483
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 = pickᴰ 39 Sᴰ
  lem-pass-CK21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : St 2887
  lem-pass-CK21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = pickᴰ 40 Sᴰ
  lem-pass-CK21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : St 2888
  lem-pass-CK21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = pickᴰ 41 Sᴰ
  lem-pass-CSd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : St 2889
  lem-pass-CSd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = pickᴰ 42 Sᴰ
  lem-pass-CSd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : St 2890
  lem-pass-CSd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = pickᴰ 43 Sᴰ
  lem-pass-X2-CKd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2704
  lem-pass-X2-CKd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 44 Sᴰ
  lem-pass-X2-CS20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2705
  lem-pass-X2-CS20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 45 Sᴰ
  lem-pass-CK30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : St 2891
  lem-pass-CK30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = pickᴰ 46 Sᴰ
  lem-pass-CKd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : St 2892
  lem-pass-CKd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = pickᴰ 47 Sᴰ
  lem-pass-CS30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : St 2893
  lem-pass-CS30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = pickᴰ 48 Sᴰ
  lem-pass-CSd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : St 2894
  lem-pass-CSd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = pickᴰ 49 Sᴰ
  lem-pass-CSd20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : St 2895
  lem-pass-CSd20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = pickᴰ 50 Sᴰ
  lem-pass-CK20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : St 2896
  lem-pass-CK20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = pickᴰ 51 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 : St 2712
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 = pickᴰ 52 Sᴰ
  lem-pass-CKd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : St 2897
  lem-pass-CKd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = pickᴰ 53 Sᴰ
  lem-pass-CKd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : St 2898
  lem-pass-CKd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = pickᴰ 54 Sᴰ
  lem-pass-CS21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : St 2899
  lem-pass-CS21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = pickᴰ 55 Sᴰ
  lem-pass-CS21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : St 2900
  lem-pass-CS21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = pickᴰ 56 Sᴰ
  lem-pass-CKd20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : St 2901
  lem-pass-CKd20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = pickᴰ 57 Sᴰ
  lem-pass-CS20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : St 2902
  lem-pass-CS20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = pickᴰ 58 Sᴰ
  lem-pass-CK32-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : St 2903
  lem-pass-CK32-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = pickᴰ 59 Sᴰ
  lem-pass-CKd32-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : St 2904
  lem-pass-CKd32-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = pickᴰ 60 Sᴰ
  lem-PP-g : St 2905
  lem-PP-g = pickᴰ 61 Sᴰ
  lem-PPi≡PP3ᵖ3 : St 2906
  lem-PPi≡PP3ᵖ3 = pickᴰ 62 Sᴰ
  lem-REL0 : St 2907
  lem-REL0 = pickᴰ 63 Sᴰ
  lem-ROT-inv : St 2908
  lem-ROT-inv = pickᴰ 64 Sᴰ
  lem-merge3-at1023 : St 2909
  lem-merge3-at1023 = pickᴰ 65 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 : St 2910
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 = pickᴰ 66 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : St 2911
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = pickᴰ 67 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 : St 2912
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 = pickᴰ 68 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2913
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 69 Sᴰ
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : St 2914
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = pickᴰ 70 Sᴰ
  lem-CI-conj : St 2915
  lem-CI-conj = pickᴰ 71 Sᴰ
  lem-merge3-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : St 2916
  lem-merge3-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = pickᴰ 72 Sᴰ
  lem-merge3-at1032 : St 2917
  lem-merge3-at1032 = pickᴰ 73 Sᴰ
  lem-merge3-ᵖ-1 : St 2918
  lem-merge3-ᵖ-1 = pickᴰ 74 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : St 2919
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = pickᴰ 75 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : St 2920
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = pickᴰ 76 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2921
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 77 Sᴰ
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2922
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 78 Sᴰ
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2923
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 79 Sᴰ
  lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2924
  lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 80 Sᴰ
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : St 2925
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = pickᴰ 81 Sᴰ
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : St 2926
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = pickᴰ 82 Sᴰ
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ : St 2927
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ = pickᴰ 83 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ : St 2928
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ = pickᴰ 84 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 : St 2929
  lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 = pickᴰ 85 Sᴰ
  lem-pass-CCZ123-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : St 2930
  lem-pass-CCZ123-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = pickᴰ 86 Sᴰ
  lem-pass-CKd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 2931
  lem-pass-CKd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 87 Sᴰ
  lem-pass-CKd21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 2932
  lem-pass-CKd21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 88 Sᴰ
  lem-pass-CKd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : St 2933
  lem-pass-CKd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = pickᴰ 89 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2934
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 90 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : St 2935
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = pickᴰ 91 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : St 2936
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = pickᴰ 92 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : St 2937
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = pickᴰ 93 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : St 2938
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = pickᴰ 94 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : St 2939
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = pickᴰ 95 Sᴰ

private
  q1 : Eqn
  q1 = sE 2906 lem-PPi≡PP3ᵖ3
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = sE 1623 lem-S3
  q4 : Eqn
  q4 = sE 2906 lem-PPi≡PP3ᵖ3

-- S3i: 7 steps
lem-S3i : ⟪ (ℓ "乏中九丮九乏") ⟫ʷ ≈ ⟪ (ℓ "中九丮九") ⟫ʷ
lem-S3i = derive (ℓ "乏中九丮九乏") (ℓ "中九丮九")
  (rw 1 q1 ∷
   rw 9 q2 ∷
   rw 5 q2 ∷
   rw 12 q3 ∷
   rw 6 q3 ∷
   rw 0 q3 ∷
   rw⁻ 0 q4 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = wE 872 W
  q6 : Eqn
  q6 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q7 : Eqn
  q7 = sE 2912 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3
  q8 : Eqn
  q8 = wE 388 W

-- pass [X1 TOFF012 CS03 TOFF012 CSd03 X1] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 5 steps
lem-pass-X1-TOFF012-CS03-TOFF012-CSd03-X1-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (ℓ "丒九中九丮丒丞习丽习举丞") ⟫ʷ ≈ ⟪ (ℓ "丞习丽习举丞丒九中九丮丒") ⟫ʷ
lem-pass-X1-TOFF012-CS03-TOFF012-CSd03-X1-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (ℓ "丒九中九丮丒丞习丽习举丞") (ℓ "丞习丽习举丞丒九中九丮丒")
  (rw 12 q5 ∷
   rw⁻ 11 q6 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 5 q6 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = eqn (ℓ "丌丒") (ℓ "丒丌") (low₁-comm (X) (X))
  q10 : Eqn
  q10 = sE 2910 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3

-- pass [X1 TOFF012 CS03 TOFF012 CSd03 X1] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 7 steps
lem-pass-X1-TOFF012-CS03-TOFF012-CSd03-X1-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (ℓ "丒九中九丮丒丌丞习丽习举丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞习丽习举丌丞丒九中九丮丒") ⟫ʷ
lem-pass-X1-TOFF012-CS03-TOFF012-CSd03-X1-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = derive (ℓ "丒九中九丮丒丌丞习丽习举丌丞") (ℓ "丌丞习丽习举丌丞丒九中九丮丒")
  (rw⁻ 5 q9 ∷
   rw 14 q5 ∷
   rw⁻ 13 q6 ∷
   rw 1 q10 ∷
   rw⁻ 0 q9 ∷
   rw 1 q8 ∷
   rw 7 q6 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = wE 225 W
  q12 : Eqn
  q12 = wE 1377 W
  q13 : Eqn
  q13 = wE 1376 W
  q14 : Eqn
  q14 = wE 1378 W
  q15 : Eqn
  q15 = sE 2909 lem-merge3-at1023

-- PP1-split: 7 steps
lem-PP1-split : ⟪ (ℓ "习丽习举") ⟫ʷ ≈ ⟪ (ℓ "丧乙丞丽习举习丞") ⟫ʷ
lem-PP1-split = derive (ℓ "习丽习举") (ℓ "丧乙丞丽习举习丞")
  (rw 4 q11 ∷
   rw 5 q12 ∷
   rw 6 q13 ∷
   rw 7 q12 ∷
   rw 8 q14 ∷
   rw 9 q11 ∷
   rw 0 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = sE 2913 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q17 : Eqn
  q17 = wE 390 W
  q18 : Eqn
  q18 = wE 1379 W
  q19 : Eqn
  q19 = wE 1380 W
  q20 : Eqn
  q20 = wE 1381 W

-- PP0-sep-inv: 13 steps
lem-PP0-sep-inv : ⟪ (ℓ "九中九丮丞丽习举习丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽习举习丞九中九丮") ⟫ʷ
lem-PP0-sep-inv = derive (ℓ "九中九丮丞丽习举习丞") (ℓ "丞丽习举习丞九中九丮")
  (rw 0 q11 ∷
   rw 1 q13 ∷
   rw 2 q12 ∷
   rw 3 q14 ∷
   rw 4 q12 ∷
   rw 5 q11 ∷
   rw⁻ 6 q16 ∷
   rw 15 q17 ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   rw 12 q20 ∷
   rw 11 q19 ∷
   rw 10 q17 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = sE 2905 lem-PP-g
  q22 : Eqn
  q22 = sE 2914 lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0
  q23 : Eqn
  q23 = sE 2872 lem-g-b
  q24 : Eqn
  q24 = sE 2905 lem-PP-g

-- Q1: 4 steps
lem-Q1 : ⟪ (ℓ "九中九丮下九中九丮上") ⟫ʷ ≈ ⟪ (ℓ "下中九丮九上九中九丮") ⟫ʷ
lem-Q1 = derive (ℓ "九中九丮下九中九丮上") (ℓ "下中九丮九上九中九丮")
  (rw 0 q21 ∷
   rw 2 q22 ∷
   rw 0 q23 ∷
   rw⁻ 6 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 2097 W
  q26 : Eqn
  q26 = wE 2098 W
  q27 : Eqn
  q27 = sE 2907 lem-REL0
  q28 : Eqn
  q28 = wE 2536 W
  q29 : Eqn
  q29 = wE 2537 W

-- REL Sd: 5 steps
lem-REL-Sd : ⟪ (ℓ "三九中九丮丈三下三九中九丮丈上丈") ⟫ʷ ≈ ⟪ (ℓ "丈丈下三九中九丮丈上三三") ⟫ʷ
lem-REL-Sd = derive (ℓ "三九中九丮丈三下三九中九丮丈上丈") (ℓ "丈丈下三九中九丮丈上三三")
  (rw 5 q25 ∷
   rw 11 q26 ∷
   rw 1 q27 ∷
   rw 0 q28 ∷
   rw 8 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 2538 W
  q31 : Eqn
  q31 = wE 2539 W
  q32 : Eqn
  q32 = wE 2540 W
  q33 : Eqn
  q33 = wE 2541 W

-- REL SdKSS: 5 steps
lem-REL-SdKSS : ⟪ (ℓ "三上丈丈九中九丮三三下丈上丈丈上九中九丮下三三下") ⟫ʷ ≈ ⟪ (ℓ "丈丈下丈丈九中九丮三三上三三") ⟫ʷ
lem-REL-SdKSS = derive (ℓ "三上丈丈九中九丮三三下丈上丈丈上九中九丮下三三下") (ℓ "丈丈下丈丈九中九丮三三上三三")
  (rw 8 q30 ∷
   rw 14 q31 ∷
   rw 4 q27 ∷
   rw 0 q32 ∷
   rw 9 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = sE 1918 lem-S2-at1023
  q35 : Eqn
  q35 = sE 2917 lem-merge3-at1032

-- merge a1: 3 steps
lem-merge-a1 : ⟪ (ℓ "习丽习举丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "中乚") ⟫ʷ
lem-merge-a1 = derive (ℓ "习丽习举丘习丽习举丘") (ℓ "中乚")
  (rw 0 q34 ∷
   rw 5 q34 ∷
   rw 0 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q37 : Eqn
  q37 = eqn (ℓ "上丞") (ℓ "丞上") (low₁-comm (K) ((X ↑ ↑)))
  q38 : Eqn
  q38 = wE 2494 W
  q39 : Eqn
  q39 = eqn (ℓ "三丞") (ℓ "丞三") (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q40 : Eqn
  q40 = eqn (ℓ "下丞") (ℓ "丞下") (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q41 : Eqn
  q41 = sE 2882 lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03-ᵖ-1
  q42 : Eqn
  q42 = sE 2918 lem-merge3-ᵖ-1
  q43 : Eqn
  q43 = wE 2542 W

-- merge R0: 8 steps
lem-merge-R0 : ⟪ (ℓ "丈上中九丮九下三丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丷丈九三") ⟫ʷ
lem-merge-R0 = derive (ℓ "丈上中九丮九下三丞丈上中九丮九下三丞") (ℓ "丷丈九三")
  (rw⁻ 8 q36 ∷
   rw⁻ 9 q37 ∷
   rw 6 q38 ∷
   rw 12 q39 ∷
   rw 11 q40 ∷
   rw 2 q41 ∷
   rw 2 q42 ∷
   rw 0 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 2053 W
  q45 : Eqn
  q45 = wE 1732 W
  q46 : Eqn
  q46 = wE 45 W
  q47 : Eqn
  q47 = wE 1726 W
  q48 : Eqn
  q48 = sE 2915 lem-CI-conj

-- CI MB MA: 5 steps
lem-CI-MB-MA : ⟪ (ℓ "乚丮丷丈九三") ⟫ʷ ≈ ⟪ (ℓ "丷丈九三乚丮九中九丮") ⟫ʷ
lem-CI-MB-MA = derive (ℓ "乚丮丷丈九三") (ℓ "丷丈九三乚丮九中九丮")
  (rw 0 q44 ∷
   rw 1 q45 ∷
   rw 2 q46 ∷
   rw 3 q47 ∷
   rw 4 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = sE 2924 lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丞丈上中九丮九下三丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丞丈上中九丮九下三丞") ⟫ʷ
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丞丈上中九丮九下三丞丽习举习") (ℓ "丽习举习丞丈上中九丮九下三丞")
  (rw 0 q13 ∷
   rw 1 q12 ∷
   rw 2 q14 ∷
   rw 3 q12 ∷
   rw⁻ 4 q49 ∷
   rw 17 q18 ∷
   rw 16 q19 ∷
   rw 15 q20 ∷
   rw 14 q19 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 2512 W
  q51 : Eqn
  q51 = wE 2513 W
  q52 : Eqn
  q52 = wE 2543 W

-- REL S: 5 steps
lem-REL-S : ⟪ (ℓ "丈九中九丮三丈下三九中九丮丈上三") ⟫ʷ ≈ ⟪ (ℓ "下三九中九丮丈上") ⟫ʷ
lem-REL-S = derive (ℓ "丈九中九丮三丈下三九中九丮丈上三") (ℓ "下三九中九丮丈上")
  (rw 5 q50 ∷
   rw 11 q51 ∷
   rw 1 q27 ∷
   rw 0 q25 ∷
   rw 6 q52 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = wE 2544 W
  q54 : Eqn
  q54 = wE 2545 W
  q55 : Eqn
  q55 = wE 2546 W
  q56 : Eqn
  q56 = wE 2547 W

-- REL SKSS: 5 steps
lem-REL-SKSS : ⟪ (ℓ "丈上丈丈九中九丮三三下三丈丈上丈丈上九中九丮下三三下三三") ⟫ʷ ≈ ⟪ (ℓ "下丈丈九中九丮三三上") ⟫ʷ
lem-REL-SKSS = derive (ℓ "丈上丈丈九中九丮三三下三丈丈上丈丈上九中九丮下三三下三三") (ℓ "下丈丈九中九丮三三上")
  (rw 8 q53 ∷
   rw 14 q54 ∷
   rw 4 q27 ∷
   rw 0 q55 ∷
   rw 7 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = sE 2261 lem-ROT-gad
  q58 : Eqn
  q58 = wE 391 W
  q59 : Eqn
  q59 = wE 392 W
  q60 : Eqn
  q60 = sE 2926 lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩

-- h-gad: 4 steps
lem-h-gad : ⟪ (ℓ "丌临乙习丿习乙丿与临乙习丿习乙丿丌") ⟫ʷ ≈ ⟪ (ℓ "丈上九中九丮下三") ⟫ʷ
lem-h-gad = derive (ℓ "丌临乙习丿习乙丿与临乙习丿习乙丿丌") (ℓ "丈上九中九丮下三")
  (rw 1 q57 ∷
   rw 0 q58 ∷
   rw 8 q59 ∷
   rw 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = sE 2483 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3
  q62 : Eqn
  q62 = sE 2886 lem-pass-X3-CSd30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q63 : Eqn
  q63 = sE 2884 lem-pass-X3-CKd30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q64 : Eqn
  q64 = sE 2923 lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q65 : Eqn
  q65 = sE 2883 lem-pass-X3-CK30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q66 : Eqn
  q66 = sE 2885 lem-pass-X3-CS30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q67 : Eqn
  q67 = sE 2483 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3

-- pass [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (ℓ "丞丈上中九丮九下三丞与丐习丽习举丑丏") ⟫ʷ ≈ ⟪ (ℓ "与丐习丽习举丑丏丞丈上中九丮九下三丞") ⟫ʷ
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (ℓ "丞丈上中九丮九下三丞与丐习丽习举丑丏") (ℓ "与丐习丽习举丑丏丞丈上中九丮九下三丞")
  (rw 0 q61 ∷
   rw 15 q62 ∷
   rw 12 q63 ∷
   rw 6 q64 ∷
   rw 3 q65 ∷
   rw 0 q66 ∷
   rw⁻ 8 q67 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = sE 2712 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2
  q69 : Eqn
  q69 = sE 2699 lem-pass-X2-CSd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q70 : Eqn
  q70 = sE 2704 lem-pass-X2-CKd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q71 : Eqn
  q71 = sE 2922 lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q72 : Eqn
  q72 = sE 2698 lem-pass-X2-CK20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q73 : Eqn
  q73 = sE 2705 lem-pass-X2-CS20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q74 : Eqn
  q74 = sE 2712 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2

-- pass [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丘丞丈上中九丮九下三丘丞丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丘丞丈上中九丮九下三丘丞") ⟫ʷ
lem-pass-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丘丞丈上中九丮九下三丘丞丈上中九丮九下三") (ℓ "丈上中九丮九下三丘丞丈上中九丮九下三丘丞")
  (rw 0 q68 ∷
   rw 17 q69 ∷
   rw 14 q70 ∷
   rw 6 q71 ∷
   rw 3 q72 ∷
   rw 0 q73 ∷
   rw⁻ 8 q74 ∷ []) Eq.refl

-- pass [X3 TOFF102 CS13 TOFF102 CSd13 X3] [TOFF012 CS03 TOFF012 CSd03]: 1 steps
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丞习丽习举丞九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丞习丽习举丞") ⟫ʷ
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丞习丽习举丞九中九丮") (ℓ "九中九丮丞习丽习举丞")
  (rw⁻ 0 q16 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = sE 2916 lem-merge3-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩
  q76 : Eqn
  q76 = wE 389 W
  q77 : Eqn
  q77 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q78 : Eqn
  q78 = wE 2548 W

-- merge-all Gad(t=0, W=(), d=SK, e=1): 5 steps
lem-merge-all-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : ⟪ (ℓ "丈上九中九丮下三丞丈上九中九丮下三丞丘丈上九中九丮下三丘丘丞丈上九中九丮下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丢丳") ⟫ʷ
lem-merge-all-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = derive (ℓ "丈上九中九丮下三丞丈上九中九丮下三丞丘丈上九中九丮下三丘丘丞丈上九中九丮下三丘丞") (ℓ "丢丳")
  (rw 0 q75 ∷
   rw 15 q76 ∷
   rw 24 q77 ∷
   rw 7 q75 ∷
   rw 0 q78 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 5 W
  q80 : Eqn
  q80 = wE 1207 W
  q81 : Eqn
  q81 = wE 1731 W
  q82 : Eqn
  q82 = wE 127 W
  q83 : Eqn
  q83 = wE 271 W
  q84 : Eqn
  q84 = wE 7 W
  q85 : Eqn
  q85 = wE 8 W
  q86 : Eqn
  q86 = wE 9 W
  q87 : Eqn
  q87 = wE 10 W
  q88 : Eqn
  q88 = wE 272 W
  q89 : Eqn
  q89 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q90 : Eqn
  q90 = wE 2549 W
  q91 : Eqn
  q91 = sE 2925 lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩
  q92 : Eqn
  q92 = wE 311 W
  q93 : Eqn
  q93 = wE 123 W
  q94 : Eqn
  q94 = wE 27 W
  q95 : Eqn
  q95 = wE 28 W
  q96 : Eqn
  q96 = wE 29 W
  q97 : Eqn
  q97 = wE 25 W
  q98 : Eqn
  q98 = wE 124 W
  q99 : Eqn
  q99 = wE 274 W
  q100 : Eqn
  q100 = wE 322 W
  q101 : Eqn
  q101 = wE 313 W
  q102 : Eqn
  q102 = wE 312 W
  q103 : Eqn
  q103 = wE 31 W

-- spell Gad(t=0, W=(), d=SdK, e=-1) -> Gad(t=0, W=(), d=SK, e=1) @1023: 75 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩-at1023 : ⟪ (ℓ "丏丐丽习举习丑与") ⟫ʷ ≈ ⟪ (ℓ "与丐习丽习举丑丏") ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩-at1023 = derive (ℓ "丏丐丽习举习丑与") (ℓ "与丐习丽习举丑丏")
  (rw 8 q79 ∷
   rw 7 q80 ∷
   rw 6 q81 ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 12 q82 ∷
   rw 11 q83 ∷
   rw 10 q84 ∷
   rw 9 q85 ∷
   rw 8 q86 ∷
   rw 7 q85 ∷
   rw 6 q87 ∷
   rw 5 q83 ∷
   rw 6 q88 ∷
   re 6 8 (ℓ "九") ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw⁻ 6 q89 ∷
   rw 5 q86 ∷
   rw⁻ 4 q89 ∷
   re 5 3 (ℓ "丮") ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 10 q82 ∷
   rw 9 q83 ∷
   rw 8 q84 ∷
   rw 7 q85 ∷
   rw 6 q86 ∷
   rw 5 q85 ∷
   rw 4 q87 ∷
   rw 3 q83 ∷
   rw 4 q88 ∷
   re 4 8 (ℓ "九") ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw⁻ 4 q89 ∷
   rw 3 q87 ∷
   rw⁻ 2 q89 ∷
   re 3 3 (ℓ "中") ∷
   rw 1 q83 ∷
   rw 0 q90 ∷
   rw 1 q91 ∷
   rw 0 q92 ∷
   rw 1 q93 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 2 q93 ∷
   rw 3 q94 ∷
   rw 4 q95 ∷
   rw 5 q96 ∷
   rw 6 q95 ∷
   rw 7 q97 ∷
   rw 8 q93 ∷
   rw 9 q98 ∷
   rw 2 q99 ∷
   re 2 8 (ℓ "习") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 3 q89 ∷
   rw 4 q97 ∷
   rw 5 q89 ∷
   re 3 3 (ℓ "丽") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 4 q93 ∷
   rw 5 q94 ∷
   rw 6 q95 ∷
   rw 7 q96 ∷
   rw 8 q95 ∷
   rw 9 q97 ∷
   rw 10 q93 ∷
   rw 11 q98 ∷
   rw 4 q99 ∷
   re 4 8 (ℓ "习") ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw 5 q89 ∷
   rw 6 q100 ∷
   rw 7 q89 ∷
   re 5 3 (ℓ "举") ∷
   rw 6 q101 ∷
   rw 7 q102 ∷
   rw 8 q103 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = sE 2039 lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q105 : Eqn
  q105 = sE 2036 lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q106 : Eqn
  q106 = sE 2921 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q107 : Eqn
  q107 = sE 2037 lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q108 : Eqn
  q108 = sE 2042 lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 7 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "习丽习举丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "习丽习举丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞习丽习举")
  (rw 4 q61 ∷
   rw⁻ 0 q104 ∷
   rw⁻ 3 q105 ∷
   rw 6 q106 ∷
   rw⁻ 12 q107 ∷
   rw⁻ 15 q108 ∷
   rw⁻ 0 q67 ∷ []) Eq.refl

private
  q109 : Eqn
  q109 = sE 2236 lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2
  q110 : Eqn
  q110 = sE 2875 lem-pass-CSd21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3
  q111 : Eqn
  q111 = sE 2874 lem-pass-CKd21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3
  q112 : Eqn
  q112 = sE 2920 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3
  q113 : Eqn
  q113 = sE 2873 lem-pass-CK21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3
  q114 : Eqn
  q114 = sE 2876 lem-pass-CS21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3
  q115 : Eqn
  q115 = sE 2236 lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2

-- pass [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 7 steps
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (ℓ "与丐习丽习举丑丏丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丈上中九丮九下三丘丞与丐习丽习举丑丏") ⟫ʷ
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (ℓ "与丐习丽习举丑丏丘丞丈上中九丮九下三丘丞") (ℓ "丘丞丈上中九丮九下三丘丞与丐习丽习举丑丏")
  (rw 0 q109 ∷
   rw 7 q110 ∷
   rw 6 q111 ∷
   rw 2 q112 ∷
   rw 1 q113 ∷
   rw 0 q114 ∷
   rw⁻ 12 q115 ∷ []) Eq.refl

private
  q116 : Eqn
  q116 = sE 2889 lem-pass-CSd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2
  q117 : Eqn
  q117 = sE 2897 lem-pass-CKd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2
  q118 : Eqn
  q118 = sE 2919 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2
  q119 : Eqn
  q119 = sE 2887 lem-pass-CK21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2
  q120 : Eqn
  q120 = sE 2899 lem-pass-CS21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2

-- pass [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 7 steps
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (ℓ "与丐习丽习举丑丏丘与丐习丽习举丑丏丘") ⟫ʷ ≈ ⟪ (ℓ "丘与丐习丽习举丑丏丘与丐习丽习举丑丏") ⟫ʷ
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = derive (ℓ "与丐习丽习举丑丏丘与丐习丽习举丑丏丘") (ℓ "丘与丐习丽习举丑丏丘与丐习丽习举丑丏")
  (rw 0 q109 ∷
   rw 7 q116 ∷
   rw 6 q117 ∷
   rw 2 q118 ∷
   rw 1 q119 ∷
   rw 0 q120 ∷
   rw⁻ 10 q115 ∷ []) Eq.refl

private
  q121 : Eqn
  q121 = sE 2890 lem-pass-CSd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3
  q122 : Eqn
  q122 = sE 2898 lem-pass-CKd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3
  q123 : Eqn
  q123 = sE 2939 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3
  q124 : Eqn
  q124 = sE 2888 lem-pass-CK21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3
  q125 : Eqn
  q125 = sE 2900 lem-pass-CS21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3

-- pass [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1] [X2 X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2 X3]: 7 steps
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : ⟪ (ℓ "与丐习丽习举丑丏丘丞与丐习丽习举丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐习丽习举丑丏丘丞与丐习丽习举丑丏") ⟫ʷ
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = derive (ℓ "与丐习丽习举丑丏丘丞与丐习丽习举丑丏丘丞") (ℓ "丘丞与丐习丽习举丑丏丘丞与丐习丽习举丑丏")
  (rw 0 q109 ∷
   rw 7 q121 ∷
   rw 6 q122 ∷
   rw 2 q123 ∷
   rw 1 q124 ∷
   rw 0 q125 ∷
   rw⁻ 12 q115 ∷ []) Eq.refl

private
  q126 : Eqn
  q126 = sE 2261 lem-ROT-gad
  q127 : Eqn
  q127 = sE 2908 lem-ROT-inv

-- cls 0000R0 1000R0 = e: 3 steps
lem-cls-0000R0-1000R0-≡-e : ⟪ (ℓ "丈上中九丮九下三丌丈上中九丮九下三丌") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-cls-0000R0-1000R0-≡-e = derive (ℓ "丈上中九丮九下三丌丈上中九丮九下三丌") []
  (rw⁻ 0 q126 ∷
   rw⁻ 16 q126 ∷
   rw 0 q127 ∷ []) Eq.refl

private
  q128 : Eqn
  q128 = wE 1520 W
  q129 : Eqn
  q129 = wE 1521 W
  q130 : Eqn
  q130 = wE 1522 W
  q131 : Eqn
  q131 = sE 2938 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3
  q132 : Eqn
  q132 = wE 1523 W
  q133 : Eqn
  q133 = wE 1524 W
  q134 : Eqn
  q134 = wE 1525 W

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 13 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (ℓ "九中九丮丞义乣乊乣丞") ⟫ʷ ≈ ⟪ (ℓ "丞义乣乊乣丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = derive (ℓ "九中九丮丞义乣乊乣丞") (ℓ "丞义乣乊乣丞九中九丮")
  (rw 0 q11 ∷
   rw 1 q128 ∷
   rw 2 q129 ∷
   rw 3 q130 ∷
   rw 4 q129 ∷
   rw 5 q11 ∷
   rw⁻ 6 q131 ∷
   rw 15 q17 ∷
   rw 14 q132 ∷
   rw 13 q133 ∷
   rw 12 q134 ∷
   rw 11 q133 ∷
   rw 10 q17 ∷ []) Eq.refl

private
  q135 : Eqn
  q135 = wE 873 W
  q136 : Eqn
  q136 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q137 : Eqn
  q137 = sE 2911 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3
  q138 : Eqn
  q138 = wE 387 W

-- pass [TOFF012 CS03 TOFF012 CSd03] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 21 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (ℓ "九中九丮丌丞丽习举习丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丽习举习丌丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (ℓ "九中九丮丌丞丽习举习丌丞") (ℓ "丌丞丽习举习丌丞九中九丮")
  (rw 0 q135 ∷
   rw 1 q11 ∷
   rw 2 q13 ∷
   rw 3 q12 ∷
   rw 4 q14 ∷
   rw 5 q12 ∷
   rw 6 q135 ∷
   rw 7 q11 ∷
   rw⁻ 8 q136 ∷
   rw⁻ 14 q136 ∷
   rw⁻ 8 q137 ∷
   rw 20 q136 ∷
   rw 26 q136 ∷
   rw 19 q17 ∷
   rw 18 q138 ∷
   rw 17 q18 ∷
   rw 16 q19 ∷
   rw 15 q20 ∷
   rw 14 q19 ∷
   rw 13 q17 ∷
   rw 12 q138 ∷ []) Eq.refl

private
  q139 : Eqn
  q139 = sE 2470 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-3
  q140 : Eqn
  q140 = sE 2894 lem-pass-CSd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3
  q141 : Eqn
  q141 = sE 2892 lem-pass-CKd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3
  q142 : Eqn
  q142 = sE 2936 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3
  q143 : Eqn
  q143 = sE 2891 lem-pass-CK30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3
  q144 : Eqn
  q144 = sE 2893 lem-pass-CS30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3
  q145 : Eqn
  q145 = sE 2470 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-3

-- pass [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 7 steps
lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "丈上中九丮九下三丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞丈上中九丮九下三") ⟫ʷ
lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "丈上中九丮九下三丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞丈上中九丮九下三")
  (rw 0 q139 ∷
   rw 7 q140 ∷
   rw 6 q141 ∷
   rw 2 q142 ∷
   rw 1 q143 ∷
   rw 0 q144 ∷
   rw⁻ 14 q145 ∷ []) Eq.refl

private
  q146 : Eqn
  q146 = sE 2937 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3

-- pass [TOFF012 CS03 TOFF012 CSd03] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 21 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (ℓ "九中九丮丌丞义乣乊乣丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞义乣乊乣丌丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = derive (ℓ "九中九丮丌丞义乣乊乣丌丞") (ℓ "丌丞义乣乊乣丌丞九中九丮")
  (rw 0 q135 ∷
   rw 1 q11 ∷
   rw 2 q128 ∷
   rw 3 q129 ∷
   rw 4 q130 ∷
   rw 5 q129 ∷
   rw 6 q135 ∷
   rw 7 q11 ∷
   rw⁻ 8 q136 ∷
   rw⁻ 14 q136 ∷
   rw⁻ 8 q146 ∷
   rw 20 q136 ∷
   rw 26 q136 ∷
   rw 19 q17 ∷
   rw 18 q138 ∷
   rw 17 q132 ∷
   rw 16 q133 ∷
   rw 15 q134 ∷
   rw 14 q133 ∷
   rw 13 q17 ∷
   rw 12 q138 ∷ []) Eq.refl

private
  q147 : Eqn
  q147 = sE 2230 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2
  q148 : Eqn
  q148 = sE 2895 lem-pass-CSd20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3
  q149 : Eqn
  q149 = sE 2901 lem-pass-CKd20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3
  q150 : Eqn
  q150 = sE 2935 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3
  q151 : Eqn
  q151 = sE 2896 lem-pass-CK20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3
  q152 : Eqn
  q152 = sE 2902 lem-pass-CS20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3
  q153 : Eqn
  q153 = sE 2230 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2

-- pass [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 7 steps
lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (ℓ "丈上中九丮九下三丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丈上中九丮九下三丘丞丈上中九丮九下三") ⟫ʷ
lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (ℓ "丈上中九丮九下三丘丞丈上中九丮九下三丘丞") (ℓ "丘丞丈上中九丮九下三丘丞丈上中九丮九下三")
  (rw 0 q147 ∷
   rw 7 q148 ∷
   rw 6 q149 ∷
   rw 2 q150 ∷
   rw 1 q151 ∷
   rw 0 q152 ∷
   rw⁻ 12 q153 ∷ []) Eq.refl

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 13 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (ℓ "九中九丮丞丽习举习丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽习举习丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (ℓ "九中九丮丞丽习举习丞") (ℓ "丞丽习举习丞九中九丮")
  (rw 0 q11 ∷
   rw 1 q13 ∷
   rw 2 q12 ∷
   rw 3 q14 ∷
   rw 4 q12 ∷
   rw 5 q11 ∷
   rw⁻ 6 q16 ∷
   rw 15 q17 ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   rw 12 q20 ∷
   rw 11 q19 ∷
   rw 10 q17 ∷ []) Eq.refl

private
  q154 : Eqn
  q154 = eqn (ℓ "丏丞") (ℓ "丞丏") (low-comm (((S • S • S) ↑)) ((X ↑)))
  q155 : Eqn
  q155 = eqn (ℓ "丏丘") (ℓ "丘丏") (low-comm (((S • S • S) ↑)) (X))
  q156 : Eqn
  q156 = eqn (ℓ "丑丞") (ℓ "丞丑") (low-comm (((K • iI) ↑)) ((X ↑)))
  q157 : Eqn
  q157 = eqn (ℓ "丑丘") (ℓ "丘丑") (low-comm (((K • iI) ↑)) (X))
  q158 : Eqn
  q158 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q159 : Eqn
  q159 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q160 : Eqn
  q160 = eqn (ℓ "丐丘") (ℓ "丘丐") (low-comm ((K ↑)) (X))
  q161 : Eqn
  q161 = eqn (ℓ "丐丞") (ℓ "丞丐") (low-comm ((K ↑)) ((X ↑)))
  q162 : Eqn
  q162 = wE 2550 W
  q163 : Eqn
  q163 = wE 2551 W
  q164 : Eqn
  q164 = sE 2727 lem-pass-CS21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3
  q165 : Eqn
  q165 = sE 2933 lem-pass-CKd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3
  q166 : Eqn
  q166 = sE 2878 lem-pass-CSd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3
  q167 : Eqn
  q167 = wE 2552 W

-- ca-split Gad(t=1, W=(2, 3), d=SdKdSS, e=-1) 2: 23 steps
lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2 : ⟪ (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘") ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2 = derive (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞") (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘")
  (rw⁻ 1 q154 ∷
   rw⁻ 0 q155 ∷
   rw⁻ 2 q156 ∷
   rw⁻ 1 q157 ∷
   rw⁻ 3 q158 ∷
   rw⁻ 2 q159 ∷
   rw⁻ 4 q158 ∷
   rw⁻ 3 q159 ∷
   rw 13 q159 ∷
   rw 12 q160 ∷
   rw 11 q155 ∷
   rw 10 q155 ∷
   rw 14 q158 ∷
   rw 13 q161 ∷
   rw 12 q154 ∷
   rw 11 q154 ∷
   rw 0 q162 ∷
   rw 24 q163 ∷
   rw 15 q164 ∷
   rw 14 q164 ∷
   rw 13 q165 ∷
   rw 12 q166 ∷
   rw 20 q167 ∷ []) Eq.refl

private
  q168 : Eqn
  q168 = eqn (ℓ "三丘") (ℓ "丘三") (low₁-comm ((S • S • S)) ((X ↑)))
  q169 : Eqn
  q169 = eqn (ℓ "三丒") (ℓ "丒三") (low₁-comm ((S • S • S)) (X))
  q170 : Eqn
  q170 = eqn (ℓ "下丘") (ℓ "丘下") (low₁-comm ((K • iI)) ((X ↑)))
  q171 : Eqn
  q171 = eqn (ℓ "下丒") (ℓ "丒下") (low₁-comm ((K • iI)) (X))
  q172 : Eqn
  q172 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q173 : Eqn
  q173 = eqn (ℓ "丈丒") (ℓ "丒丈") (low₁-comm (S) (X))
  q174 : Eqn
  q174 = eqn (ℓ "上丒") (ℓ "丒上") (low₁-comm (K) (X))
  q175 : Eqn
  q175 = eqn (ℓ "上丘") (ℓ "丘上") (low₁-comm (K) ((X ↑)))
  q176 : Eqn
  q176 = wE 2553 W
  q177 : Eqn
  q177 = wE 2554 W
  q178 : Eqn
  q178 = sE 1747 lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q179 : Eqn
  q179 = sE 2931 lem-pass-CKd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q180 : Eqn
  q180 = sE 1748 lem-pass-CSd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q181 : Eqn
  q181 = wE 2555 W

-- ca-split Gad(t=0, W=(1, 2, 3), d=SdKdSS, e=-1) 1: 31 steps
lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SdKdSS-e≡-1⟩-1 : ⟪ (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒両丒丒丵丒丒丠丒丒丠丒丒丘丞中九丮九丒丘丞丒両丒丒両丒丒临丒丒丠丒") ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SdKdSS-e≡-1⟩-1 = derive (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞") (ℓ "丒両丒丒丵丒丒丠丒丒丠丒丒丘丞中九丮九丒丘丞丒両丒丒両丒丒临丒丒丠丒")
  (rw⁻ 2 q39 ∷
   rw⁻ 1 q168 ∷
   rw⁻ 0 q169 ∷
   rw⁻ 3 q40 ∷
   rw⁻ 2 q170 ∷
   rw⁻ 1 q171 ∷
   rw⁻ 4 q36 ∷
   rw⁻ 3 q172 ∷
   rw⁻ 2 q173 ∷
   rw⁻ 5 q36 ∷
   rw⁻ 4 q172 ∷
   rw⁻ 3 q173 ∷
   rw 14 q173 ∷
   rw 13 q174 ∷
   rw 12 q169 ∷
   rw 11 q169 ∷
   rw 15 q172 ∷
   rw 14 q175 ∷
   rw 13 q168 ∷
   rw 12 q168 ∷
   rw 16 q36 ∷
   rw 15 q37 ∷
   rw 14 q39 ∷
   rw 13 q39 ∷
   rw 0 q176 ∷
   rw 26 q177 ∷
   rw 15 q178 ∷
   rw 14 q178 ∷
   rw 13 q179 ∷
   rw 12 q180 ∷
   rw 22 q181 ∷ []) Eq.refl

private
  q182 : Eqn
  q182 = eqn (ℓ "丌丏") (ℓ "丏丌") (low₁-comm (X) ((S • S • S)))
  q183 : Eqn
  q183 = eqn (ℓ "丌丑") (ℓ "丑丌") (low₁-comm (X) ((K • iI)))
  q184 : Eqn
  q184 = eqn (ℓ "丌与") (ℓ "与丌") (low₁-comm (X) (S))
  q185 : Eqn
  q185 = eqn (ℓ "丌丐") (ℓ "丐丌") (low₁-comm (X) (K))
  q186 : Eqn
  q186 = sE 2765 lem-pass-CS21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3
  q187 : Eqn
  q187 = sE 2932 lem-pass-CKd21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3
  q188 : Eqn
  q188 = sE 2877 lem-pass-CSd21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3

-- ca-split Gad(t=1, W=(0, 2, 3), d=SdKdSS, e=-1) 2: 31 steps
lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-2 : ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丞丽习举习丌丘丞丘丷丘丘丷丘丘乇丘丘丶丘") ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-2 = derive (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丞丽习举习丌丘丞丘丷丘丘丷丘丘乇丘丘丶丘")
  (rw⁻ 2 q154 ∷
   rw⁻ 1 q155 ∷
   rw 0 q182 ∷
   rw⁻ 3 q156 ∷
   rw⁻ 2 q157 ∷
   rw 1 q183 ∷
   rw⁻ 4 q158 ∷
   rw⁻ 3 q159 ∷
   rw 2 q184 ∷
   rw⁻ 5 q158 ∷
   rw⁻ 4 q159 ∷
   rw 3 q184 ∷
   rw⁻ 14 q184 ∷
   rw⁻ 13 q185 ∷
   rw⁻ 12 q182 ∷
   rw⁻ 11 q182 ∷
   rw 15 q159 ∷
   rw 14 q160 ∷
   rw 13 q155 ∷
   rw 12 q155 ∷
   rw 16 q158 ∷
   rw 15 q161 ∷
   rw 14 q154 ∷
   rw 13 q154 ∷
   rw 0 q162 ∷
   rw 26 q163 ∷
   rw 15 q186 ∷
   rw 14 q186 ∷
   rw 13 q187 ∷
   rw 12 q188 ∷
   rw 22 q167 ∷ []) Eq.refl

private
  q189 : Eqn
  q189 = sE 2929 lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2
  q190 : Eqn
  q190 = sE 868 lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q191 : Eqn
  q191 = sE 866 lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q192 : Eqn
  q192 = sE 2880 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3
  q193 : Eqn
  q193 = sE 867 lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q194 : Eqn
  q194 = sE 871 lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q195 : Eqn
  q195 = sE 2929 lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2

-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 7 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (ℓ "中九丮九丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (ℓ "中九丮九丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丞与丐丽习举习丑丏丘丞中九丮九")
  (rw 4 q189 ∷
   rw⁻ 0 q190 ∷
   rw⁻ 3 q191 ∷
   rw 6 q192 ∷
   rw⁻ 14 q193 ∷
   rw⁻ 17 q194 ∷
   rw⁻ 0 q195 ∷ []) Eq.refl

private
  q196 : Eqn
  q196 = sE 2928 lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q61 ∷
   rw 0 q196 ∷
   rw⁻ 0 q67 ∷ []) Eq.refl

private
  q197 : Eqn
  q197 = sE 2870 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-X3
  q198 : Eqn
  q198 = sE 1214 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CK30-X3
  q199 : Eqn
  q199 = sE 2934 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q200 : Eqn
  q200 = sE 1215 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CKd30-X3
  q201 : Eqn
  q201 = sE 2871 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CSd03-X3

-- Bar(SSSKSS;3,2->0) passes split Gad(t=0, W=(3,), d=SK, e=-1): 5 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞") (ℓ "丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 0 q197 ∷
   rw 3 q198 ∷
   rw 6 q199 ∷
   rw 12 q200 ∷
   rw 15 q201 ∷ []) Eq.refl

private
  q202 : Eqn
  q202 = sE 2927 lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q61 ∷
   rw 0 q202 ∷
   rw⁻ 0 q67 ∷ []) Eq.refl

private
  q203 : Eqn
  q203 = wE 2297 W
  q204 : Eqn
  q204 = sE 2904 lem-pass-CKd32-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3
  q205 : Eqn
  q205 = sE 2930 lem-pass-CCZ123-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3
  q206 : Eqn
  q206 = sE 2903 lem-pass-CK32-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3
  q207 : Eqn
  q207 = wE 2298 W

-- pass [TOFF213] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 5 steps
lem-pass-TOFF213-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (ℓ "乥丞与丐丽习举习丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐丽习举习丑丏丞乥") ⟫ʷ
lem-pass-TOFF213-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (ℓ "乥丞与丐丽习举习丑丏丞") (ℓ "丞与丐丽习举习丑丏丞乥")
  (rw 0 q203 ∷
   rw 2 q204 ∷
   rw 1 q205 ∷
   rw 0 q206 ∷
   rw 10 q207 ∷ []) Eq.refl

private
  q208 : Eqn
  q208 = sE 2879 lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丞与丐丽习举习丑丏丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q189 ∷
   rw 0 q208 ∷
   rw⁻ 0 q195 ∷ []) Eq.refl

private
  q209 : Eqn
  q209 = sE 2881 lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩

-- pass [CCZ123] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 3 steps
lem-pass-CCZ123-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (ℓ "乜丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (ℓ "乜丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丞与丐丽习举习丑丏丘丞乜")
  (rw 1 q189 ∷
   rw 0 q209 ∷
   rw⁻ 0 q195 ∷ []) Eq.refl
