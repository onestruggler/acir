{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD766 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D766 (W : Ws) (Sᴰ : SD766) where

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
  lem-b2g-0011R2 : St 3101
  lem-b2g-0011R2 = pickᴰ 0 Sᴰ
  lem-b2g-1001R0 : St 2722
  lem-b2g-1001R0 = pickᴰ 1 Sᴰ
  lem-AXIOM-LF-at0312 : St 180
  lem-AXIOM-LF-at0312 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK20-X2 : St 1247
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK20-X2 = pickᴰ 3 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd20-X2 : St 1248
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd20-X2 = pickᴰ 4 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CK10-X1 : St 3102
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CK10-X1 = pickᴰ 5 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CKd10-X1 : St 3103
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CKd10-X1 = pickᴰ 6 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-X1 : St 3104
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-X1 = pickᴰ 7 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CSd01-X1 : St 3105
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CSd01-X1 = pickᴰ 8 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CK10-X1 : St 3106
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CK10-X1 = pickᴰ 9 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CKd10-X1 : St 3107
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CKd10-X1 = pickᴰ 10 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CS01-X1 : St 3108
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CS01-X1 = pickᴰ 11 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CSd01-X1 : St 3109
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CSd01-X1 = pickᴰ 12 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS02-X2 : St 2979
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS02-X2 = pickᴰ 13 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd02-X2 : St 2980
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd02-X2 = pickᴰ 14 Sᴰ
  lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 866
  lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 15 Sᴰ
  lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 867
  lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 16 Sᴰ
  lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 868
  lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 17 Sᴰ
  lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 871
  lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 18 Sᴰ
  lem-AXIOM-LF-at0321 : St 1002
  lem-AXIOM-LF-at0321 = pickᴰ 19 Sᴰ
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1175
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 20 Sᴰ
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1191
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 21 Sᴰ
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : St 3110
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 22 Sᴰ
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : St 3111
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 23 Sᴰ
  lem-pass-CK20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : St 3112
  lem-pass-CK20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = pickᴰ 24 Sᴰ
  lem-pass-CKd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : St 3113
  lem-pass-CKd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = pickᴰ 25 Sᴰ
  lem-pass-CS20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : St 3114
  lem-pass-CS20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = pickᴰ 26 Sᴰ
  lem-pass-CSd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : St 3115
  lem-pass-CSd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = pickᴰ 27 Sᴰ
  lem-pass-CK21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : St 3116
  lem-pass-CK21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = pickᴰ 28 Sᴰ
  lem-pass-CKd21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : St 3117
  lem-pass-CKd21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = pickᴰ 29 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : St 3118
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 30 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : St 2880
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = pickᴰ 31 Sᴰ
  lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : St 3119
  lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 32 Sᴰ
  lem-CCZ⟨231⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : St 3120
  lem-CCZ⟨231⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 33 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 : St 2230
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 = pickᴰ 34 Sᴰ
  lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 2240
  lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 35 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 3121
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 36 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : St 3122
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 37 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 : St 2483
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 = pickᴰ 38 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 3123
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 39 Sᴰ
  lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 2523
  lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 40 Sᴰ
  lem-pass-CK13-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 : St 3124
  lem-pass-CK13-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 = pickᴰ 41 Sᴰ
  lem-pass-CKd13-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 : St 3125
  lem-pass-CKd13-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 = pickᴰ 42 Sᴰ
  lem-pass-CK23-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 : St 3126
  lem-pass-CK23-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 = pickᴰ 43 Sᴰ
  lem-pass-CK23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : St 3127
  lem-pass-CK23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = pickᴰ 44 Sᴰ
  lem-pass-CK31-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : St 3128
  lem-pass-CK31-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = pickᴰ 45 Sᴰ
  lem-pass-CK32-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : St 3129
  lem-pass-CK32-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = pickᴰ 46 Sᴰ
  lem-pass-CKd23-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 : St 3130
  lem-pass-CKd23-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 = pickᴰ 47 Sᴰ
  lem-pass-CKd23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : St 3131
  lem-pass-CKd23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = pickᴰ 48 Sᴰ
  lem-pass-CKd31-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : St 3132
  lem-pass-CKd31-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = pickᴰ 49 Sᴰ
  lem-pass-CKd32-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : St 3133
  lem-pass-CKd32-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = pickᴰ 50 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2 : St 2970
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2 = pickᴰ 51 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : St 3134
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = pickᴰ 52 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : St 3135
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = pickᴰ 53 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : St 3136
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = pickᴰ 54 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : St 3137
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = pickᴰ 55 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : St 3138
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = pickᴰ 56 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : St 3139
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = pickᴰ 57 Sᴰ
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ : St 3140
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ = pickᴰ 58 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SdKdSS-e≡-1⟩-1 : St 3141
  lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SdKdSS-e≡-1⟩-1 = pickᴰ 59 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-2 : St 3142
  lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-2 = pickᴰ 60 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2 : St 3143
  lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2 = pickᴰ 61 Sᴰ
  lem-pass-CCZ123-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : St 3144
  lem-pass-CCZ123-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = pickᴰ 62 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : St 3145
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = pickᴰ 63 Sᴰ
  lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : St 3146
  lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = pickᴰ 64 Sᴰ
  lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : St 3147
  lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = pickᴰ 65 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : St 3148
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = pickᴰ 66 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : St 3149
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = pickᴰ 67 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : St 3097
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = pickᴰ 68 Sᴰ
  lem-pass-TOFF213-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : St 3150
  lem-pass-TOFF213-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = pickᴰ 69 Sᴰ
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : St 3151
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 70 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : St 3152
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 71 Sᴰ
  lem-pass-CCZ123-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 : St 3153
  lem-pass-CCZ123-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 = pickᴰ 72 Sᴰ
  lem-pass-CCZ123-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : St 3154
  lem-pass-CCZ123-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = pickᴰ 73 Sᴰ
  lem-pass-CCZ123-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : St 3155
  lem-pass-CCZ123-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = pickᴰ 74 Sᴰ
  lem-pass-CCZ123-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 : St 3156
  lem-pass-CCZ123-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 = pickᴰ 75 Sᴰ
  lem-pass-CCZ123-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : St 3157
  lem-pass-CCZ123-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = pickᴰ 76 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 3158
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 77 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 3159
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 78 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 3160
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 79 Sᴰ
  lem-pass-TOFF123-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : St 3161
  lem-pass-TOFF123-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = pickᴰ 80 Sᴰ

private
  q1 : Eqn
  q1 = sE 2722 lem-b2g-1001R0
  q2 : Eqn
  q2 = sE 3147 lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3
  q3 : Eqn
  q3 = sE 2722 lem-b2g-1001R0

-- cls 0000R0 1001R0 = 1001R0 0000R0: 3 steps
lem-cls-0000R0-1001R0-≡-1001R0-0000R0 : ⟪ (ℓ "丈上中九丮九下三丌丞丈上中九丮九下三丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丈上中九丮九下三丌丞丈上中九丮九下三") ⟫ʷ
lem-cls-0000R0-1001R0-≡-1001R0-0000R0 = derive (ℓ "丈上中九丮九下三丌丞丈上中九丮九下三丌丞") (ℓ "丌丞丈上中九丮九下三丌丞丈上中九丮九下三")
  (rw 8 q1 ∷
   rw 0 q2 ∷
   rw⁻ 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = wE 45 W
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = wE 1357 W
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 231 W
  q9 : Eqn
  q9 = sE 3148 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3
  q10 : Eqn
  q10 = wE 227 W
  q11 : Eqn
  q11 = wE 1358 W
  q12 : Eqn
  q12 = wE 1342 W

-- pass [CS03 TOFF012 CSd03 TOFF012] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 33 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (ℓ "中九丮九丌丞义乣乊乣丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞义乣乊乣丌丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = derive (ℓ "中九丮九丌丞义乣乊乣丌丞") (ℓ "丌丞义乣乊乣丌丞中九丮九")
  (rw 12 q4 ∷
   rw 13 q5 ∷
   rw 14 q6 ∷
   rw 15 q5 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q5 ∷
   re 14 3 (ℓ "丮") ∷
   rw 15 q7 ∷
   rw 14 q4 ∷
   rw 15 q5 ∷
   rw 16 q8 ∷
   rw 17 q5 ∷
   re 15 3 (ℓ "丮") ∷
   rw 18 q5 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q7 ∷
   rw⁻ 4 q9 ∷
   rw 3 q10 ∷
   rw 4 q5 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q7 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q7 ∷
   rw 3 q11 ∷
   rw 2 q7 ∷
   rw 1 q10 ∷
   rw 2 q5 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q7 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q7 ∷
   rw 1 q12 ∷
   rw 0 q7 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = sE 3146 lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3

-- cls 0000R0 0011R0 = 0011R0 0000R0: 1 steps
lem-cls-0000R0-0011R0-≡-0011R0-0000R0 : ⟪ (ℓ "丈上中九丮九下三丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丈上中九丮九下三丘丞丈上中九丮九下三") ⟫ʷ
lem-cls-0000R0-0011R0-≡-0011R0-0000R0 = derive (ℓ "丈上中九丮九下三丘丞丈上中九丮九下三丘丞") (ℓ "丘丞丈上中九丮九下三丘丞丈上中九丮九下三")
  (rw 0 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = sE 3149 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3

-- pass [CS03 TOFF012 CSd03 TOFF012] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 33 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (ℓ "中九丮九丞丽习举习丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽习举习丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (ℓ "中九丮九丞丽习举习丞") (ℓ "丞丽习举习丞中九丮九")
  (rw 10 q4 ∷
   rw 11 q5 ∷
   rw 12 q6 ∷
   rw 13 q5 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q5 ∷
   re 12 3 (ℓ "丮") ∷
   rw 13 q7 ∷
   rw 12 q4 ∷
   rw 13 q5 ∷
   rw 14 q8 ∷
   rw 15 q5 ∷
   re 13 3 (ℓ "丮") ∷
   rw 16 q5 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q7 ∷
   rw⁻ 4 q14 ∷
   rw 3 q10 ∷
   rw 4 q5 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q7 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q7 ∷
   rw 3 q11 ∷
   rw 2 q7 ∷
   rw 1 q10 ∷
   rw 2 q5 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q7 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q7 ∷
   rw 1 q12 ∷
   rw 0 q7 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = sE 3143 lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2
  q16 : Eqn
  q16 = sE 871 lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q17 : Eqn
  q17 = sE 867 lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q18 : Eqn
  q18 = sE 868 lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q19 : Eqn
  q19 = sE 2880 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3
  q20 : Eqn
  q20 = sE 866 lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q21 : Eqn
  q21 = sE 3143 lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2

-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 11 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (ℓ "中九丮九丘丞丏丑与与丽习举习丏丏丐与丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (ℓ "中九丮九丘丞丏丑与与丽习举习丏丏丐与丘丞") (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞中九丮九")
  (rw 4 q15 ∷
   rw⁻ 0 q16 ∷
   rw⁻ 3 q17 ∷
   rw⁻ 6 q18 ∷
   rw⁻ 9 q18 ∷
   rw 12 q19 ∷
   rw⁻ 20 q16 ∷
   rw⁻ 23 q16 ∷
   rw⁻ 26 q20 ∷
   rw⁻ 29 q18 ∷
   rw⁻ 0 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = sE 3141 lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SdKdSS-e≡-1⟩-1
  q23 : Eqn
  q23 = sE 1191 lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q24 : Eqn
  q24 = sE 2523 lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q25 : Eqn
  q25 = sE 1175 lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q26 : Eqn
  q26 = sE 3123 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q27 : Eqn
  q27 = sE 2240 lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q28 : Eqn
  q28 = sE 3141 lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SdKdSS-e≡-1⟩-1

-- pass [CS03 TOFF012 CSd03 TOFF012] [X1 X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X1 X2 X3]: 11 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 : ⟪ (ℓ "中九丮九丒丘丞三下丈丈中九丮九三三上丈丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 = derive (ℓ "中九丮九丒丘丞三下丈丈中九丮九三三上丈丒丘丞") (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞中九丮九")
  (rw 4 q22 ∷
   rw⁻ 0 q23 ∷
   rw⁻ 3 q24 ∷
   rw⁻ 6 q25 ∷
   rw⁻ 9 q25 ∷
   rw 12 q26 ∷
   rw⁻ 22 q23 ∷
   rw⁻ 25 q23 ∷
   rw⁻ 28 q27 ∷
   rw⁻ 31 q25 ∷
   rw⁻ 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = sE 3097 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3

-- pass [CS03 TOFF012 CSd03 TOFF012] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 33 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (ℓ "中九丮九丞义乣乊乣丞") ⟫ʷ ≈ ⟪ (ℓ "丞义乣乊乣丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = derive (ℓ "中九丮九丞义乣乊乣丞") (ℓ "丞义乣乊乣丞中九丮九")
  (rw 10 q4 ∷
   rw 11 q5 ∷
   rw 12 q6 ∷
   rw 13 q5 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q5 ∷
   re 12 3 (ℓ "丮") ∷
   rw 13 q7 ∷
   rw 12 q4 ∷
   rw 13 q5 ∷
   rw 14 q8 ∷
   rw 15 q5 ∷
   re 13 3 (ℓ "丮") ∷
   rw 16 q5 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q7 ∷
   rw⁻ 4 q29 ∷
   rw 3 q10 ∷
   rw 4 q5 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q7 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q7 ∷
   rw 3 q11 ∷
   rw 2 q7 ∷
   rw 1 q10 ∷
   rw 2 q5 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q7 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q7 ∷
   rw 1 q12 ∷
   rw 0 q7 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = sE 3142 lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-2
  q31 : Eqn
  q31 = sE 3121 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3
  q32 : Eqn
  q32 = sE 3142 lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-2

-- pass [CS03 TOFF012 CSd03 TOFF012] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 11 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "中九丮九丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "中九丮九丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞中九丮九")
  (rw 4 q30 ∷
   rw⁻ 0 q16 ∷
   rw⁻ 3 q17 ∷
   rw⁻ 6 q18 ∷
   rw⁻ 9 q18 ∷
   rw 12 q31 ∷
   rw⁻ 22 q16 ∷
   rw⁻ 25 q16 ∷
   rw⁻ 28 q20 ∷
   rw⁻ 31 q18 ∷
   rw⁻ 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = sE 2230 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2
  q34 : Eqn
  q34 = sE 3115 lem-pass-CSd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3
  q35 : Eqn
  q35 = sE 3113 lem-pass-CKd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3
  q36 : Eqn
  q36 = sE 3145 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3
  q37 : Eqn
  q37 = sE 3112 lem-pass-CK20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3
  q38 : Eqn
  q38 = sE 3114 lem-pass-CS20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3
  q39 : Eqn
  q39 = sE 2230 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2

-- pass [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 7 steps
lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (ℓ "丈上中九丮九下三丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞丈上中九丮九下三") ⟫ʷ
lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (ℓ "丈上中九丮九下三丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丞与丐丽习举习丑丏丘丞丈上中九丮九下三")
  (rw 0 q33 ∷
   rw 7 q34 ∷
   rw 6 q35 ∷
   rw 2 q36 ∷
   rw 1 q37 ∷
   rw 0 q38 ∷
   rw⁻ 12 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = sE 2483 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3
  q41 : Eqn
  q41 = sE 3140 lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩
  q42 : Eqn
  q42 = sE 2483 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 31 q40 ∷
   rw 0 q41 ∷
   rw⁻ 0 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = sE 180 lem-AXIOM-LF-at0312
  q44 : Eqn
  q44 = sE 3136 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3
  q45 : Eqn
  q45 = sE 3150 lem-pass-TOFF213-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3
  q46 : Eqn
  q46 = sE 3139 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3
  q47 : Eqn
  q47 = sE 3134 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3
  q48 : Eqn
  q48 = sE 180 lem-AXIOM-LF-at0312

-- far CS03 CS03 CK30 CS03 CX31 CS01 CS01 CS01 .. 0001R1 sep 3: 7 steps
lem-far-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01-··-0001R1-sep-3 : ⟪ (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄丞与丐丽习举习丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐丽习举习丑丏丞中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄") ⟫ʷ
lem-far-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01-··-0001R1-sep-3 = derive (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄丞与丐丽习举习丑丏丞") (ℓ "丞与丐丽习举习丑丏丞中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄")
  (rw 0 q43 ∷
   rw 62 q44 ∷
   rw 61 q45 ∷
   rw 30 q46 ∷
   rw 29 q45 ∷
   rw 0 q47 ∷
   rw⁻ 10 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 2425 W
  q50 : Eqn
  q50 = sE 3131 lem-pass-CKd23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3
  q51 : Eqn
  q51 = sE 3144 lem-pass-CCZ123-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3
  q52 : Eqn
  q52 = sE 3127 lem-pass-CK23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3
  q53 : Eqn
  q53 = wE 2426 W

-- pass [TOFF312] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (ℓ "乨丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞乨") ⟫ʷ
lem-pass-TOFF312-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (ℓ "乨丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丞与丐丽习举习丑丏丘丞乨")
  (rw 0 q49 ∷
   rw 2 q50 ∷
   rw 1 q51 ∷
   rw 0 q52 ∷
   rw 12 q53 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = sE 3101 lem-b2g-0011R2
  q55 : Eqn
  q55 = sE 1002 lem-AXIOM-LF-at0321
  q56 : Eqn
  q56 = sE 3135 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3
  q57 : Eqn
  q57 = sE 3161 lem-pass-TOFF123-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3
  q58 : Eqn
  q58 = sE 3138 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3
  q59 : Eqn
  q59 = sE 3137 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3
  q60 : Eqn
  q60 = sE 1002 lem-AXIOM-LF-at0321
  q61 : Eqn
  q61 = sE 3101 lem-b2g-0011R2

-- far CS03 CS03 CK30 CS03 CX32 CS02 CS02 CS02 .. 0011R2 sep 3: 9 steps
lem-far-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02-··-0011R2-sep-3 : ⟪ (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丘丞且世义乣乊乣丗丕丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞且世义乣乊乣丗丕丘丞中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临") ⟫ʷ
lem-far-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02-··-0011R2-sep-3 = derive (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丘丞且世义乣乊乣丗丕丘丞") (ℓ "丘丞且世义乣乊乣丗丕丘丞中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临")
  (rw 80 q54 ∷
   rw 0 q55 ∷
   rw 62 q56 ∷
   rw 61 q57 ∷
   rw 30 q58 ∷
   rw 29 q57 ∷
   rw 0 q59 ∷
   rw⁻ 14 q60 ∷
   rw⁻ 0 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = sE 3104 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-X1
  q63 : Eqn
  q63 = sE 3102 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CK10-X1
  q64 : Eqn
  q64 = sE 3159 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q65 : Eqn
  q65 = sE 3103 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CKd10-X1
  q66 : Eqn
  q66 = sE 3105 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CSd01-X1

-- Bar(SSKSKK;1,3->0) passes split Gad(t=0, W=(1, 2, 3), d=SK, e=-1): 5 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒") ⟫ʷ ≈ ⟪ (ℓ "丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒") (ℓ "丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 0 q62 ∷
   rw 3 q63 ∷
   rw 6 q64 ∷
   rw 16 q65 ∷
   rw 19 q66 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 2207 W
  q68 : Eqn
  q68 = sE 3125 lem-pass-CKd13-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3
  q69 : Eqn
  q69 = sE 3156 lem-pass-CCZ123-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3
  q70 : Eqn
  q70 = sE 3124 lem-pass-CK13-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3
  q71 : Eqn
  q71 = wE 2208 W

-- pass [TOFF312] [X1 X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X1 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 : ⟪ (ℓ "乨丒丘丞丈上中九丮九下三丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞丈上中九丮九下三丒丘丞乨") ⟫ʷ
lem-pass-TOFF312-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 = derive (ℓ "乨丒丘丞丈上中九丮九下三丒丘丞") (ℓ "丒丘丞丈上中九丮九下三丒丘丞乨")
  (rw 0 q67 ∷
   rw 2 q68 ∷
   rw 1 q69 ∷
   rw 0 q70 ∷
   rw 14 q71 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = sE 3108 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CS01-X1
  q73 : Eqn
  q73 = sE 3106 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CK10-X1
  q74 : Eqn
  q74 = sE 3158 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q75 : Eqn
  q75 = sE 3107 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CKd10-X1
  q76 : Eqn
  q76 = sE 3109 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CSd01-X1

-- Bar(SSKSKK;1,2->0) passes split Gad(t=0, W=(1, 2, 3), d=SK, e=-1): 5 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒") ⟫ʷ ≈ ⟪ (ℓ "丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒") (ℓ "丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (rw 0 q72 ∷
   rw 3 q73 ∷
   rw 6 q74 ∷
   rw 16 q75 ∷
   rw 19 q76 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = sE 3110 lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丞丏丑与与丽习举习丏丏丐与丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丞丏丑与与丽习举习丏丏丐与丘丞") (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 29 q15 ∷
   rw 0 q77 ∷
   rw⁻ 0 q21 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = sE 3120 lem-CCZ⟨231⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CCZ123] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 3 steps
lem-pass-CCZ123-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (ℓ "乜丘丞丏丑与与丽习举习丏丏丐与丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (ℓ "乜丘丞丏丑与与丽习举习丏丏丐与丘丞") (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞乜")
  (rw 1 q15 ∷
   rw 0 q78 ∷
   rw⁻ 0 q21 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = sE 3111 lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丞丏丑与与丽习举习丏丏丐与丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丞丏丑与与丽习举习丏丏丐与丘丞") (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 31 q15 ∷
   rw 0 q79 ∷
   rw⁻ 0 q21 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = sE 3118 lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞丏丑与与丽习举习丏丏丐与丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞丏丑与与丽习举习丏丏丐与丘丞") (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q15 ∷
   rw 0 q80 ∷
   rw⁻ 0 q21 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 2297 W
  q82 : Eqn
  q82 = sE 3133 lem-pass-CKd32-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3
  q83 : Eqn
  q83 = sE 3154 lem-pass-CCZ123-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3
  q84 : Eqn
  q84 = sE 3129 lem-pass-CK32-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3
  q85 : Eqn
  q85 = wE 2298 W

-- pass [TOFF213] [X0 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X3]: 5 steps
lem-pass-TOFF213-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : ⟪ (ℓ "乥丌丞与丐丽习举习丑丏丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞与丐丽习举习丑丏丌丞乥") ⟫ʷ
lem-pass-TOFF213-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = derive (ℓ "乥丌丞与丐丽习举习丑丏丌丞") (ℓ "丌丞与丐丽习举习丑丏丌丞乥")
  (rw 0 q81 ∷
   rw 2 q82 ∷
   rw 1 q83 ∷
   rw 0 q84 ∷
   rw 12 q85 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = sE 2970 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2
  q87 : Eqn
  q87 = sE 3151 lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩
  q88 : Eqn
  q88 = sE 2970 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 29 q86 ∷
   rw 0 q87 ∷
   rw⁻ 0 q88 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = wE 2556 W
  q90 : Eqn
  q90 = sE 3117 lem-pass-CKd21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3
  q91 : Eqn
  q91 = sE 3157 lem-pass-CCZ123-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3
  q92 : Eqn
  q92 = sE 3116 lem-pass-CK21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3
  q93 : Eqn
  q93 = wE 2557 W

-- pass [TOFF123] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 5 steps
lem-pass-TOFF123-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (ℓ "乢丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞乢") ⟫ʷ
lem-pass-TOFF123-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (ℓ "乢丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞乢")
  (rw 0 q89 ∷
   rw 2 q90 ∷
   rw 1 q91 ∷
   rw 0 q92 ∷
   rw 16 q93 ∷ []) Eq.refl

private
  q94 : Eqn
  q94 = sE 2980 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd02-X2
  q95 : Eqn
  q95 = sE 1248 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd20-X2
  q96 : Eqn
  q96 = sE 2979 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS02-X2
  q97 : Eqn
  q97 = sE 3160 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q98 : Eqn
  q98 = sE 1247 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK20-X2

-- Bar(SSSKSS;2,1->0) passes split Gad(t=0, W=(2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘") ⟫ʷ ≈ ⟪ (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘") (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q94 ∷
   rw 3 q95 ∷
   rw 6 q96 ∷
   rw 9 q96 ∷
   rw 12 q97 ∷
   rw 20 q94 ∷
   rw 23 q94 ∷
   rw 26 q98 ∷
   rw 29 q96 ∷ []) Eq.refl

private
  q99 : Eqn
  q99 = sE 3152 lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q86 ∷
   rw 0 q99 ∷
   rw⁻ 0 q88 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = sE 3130 lem-pass-CKd23-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3
  q101 : Eqn
  q101 = sE 3153 lem-pass-CCZ123-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3
  q102 : Eqn
  q102 = sE 3126 lem-pass-CK23-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3

-- pass [TOFF312] [X0 X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 : ⟪ (ℓ "乨丌丘丞与丐丽习举习丑丏丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞乨") ⟫ʷ
lem-pass-TOFF312-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 = derive (ℓ "乨丌丘丞与丐丽习举习丑丏丌丘丞") (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞乨")
  (rw 0 q49 ∷
   rw 2 q100 ∷
   rw 1 q101 ∷
   rw 0 q102 ∷
   rw 14 q53 ∷ []) Eq.refl

private
  q103 : Eqn
  q103 = wE 2502 W
  q104 : Eqn
  q104 = sE 3132 lem-pass-CKd31-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3
  q105 : Eqn
  q105 = sE 3155 lem-pass-CCZ123-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3
  q106 : Eqn
  q106 = sE 3128 lem-pass-CK31-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3
  q107 : Eqn
  q107 = wE 2503 W

-- pass [TOFF123] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 5 steps
lem-pass-TOFF123-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (ℓ "乢丌丞丕丗且且义乣乊乣丕丕世且丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞乢") ⟫ʷ
lem-pass-TOFF123-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (ℓ "乢丌丞丕丗且且义乣乊乣丕丕世且丌丞") (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞乢")
  (rw 0 q103 ∷
   rw 2 q104 ∷
   rw 1 q105 ∷
   rw 0 q106 ∷
   rw 16 q107 ∷ []) Eq.refl

private
  q108 : Eqn
  q108 = sE 3122 lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q30 ∷
   rw 0 q108 ∷
   rw⁻ 0 q32 ∷ []) Eq.refl

private
  q109 : Eqn
  q109 = sE 3119 lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CCZ123] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 3 steps
lem-pass-CCZ123-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "乜丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "乜丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乜")
  (rw 1 q30 ∷
   rw 0 q109 ∷
   rw⁻ 0 q32 ∷ []) Eq.refl
