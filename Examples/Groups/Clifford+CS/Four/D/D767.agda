{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD767 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D767 (W : Ws) (Sᴰ : SD767) where

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
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK20-X2 : St 1247
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK20-X2 = pickᴰ 0 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd20-X2 : St 1248
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd20-X2 = pickᴰ 1 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK30-X3 : St 1272
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK30-X3 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd30-X3 : St 1273
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd30-X3 = pickᴰ 3 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS02-X2 : St 2979
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS02-X2 = pickᴰ 4 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd02-X2 : St 2980
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd02-X2 = pickᴰ 5 Sᴰ
  lem-b2g-1011PP2 : St 3162
  lem-b2g-1011PP2 = pickᴰ 6 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS03-X3 : St 3163
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS03-X3 = pickᴰ 7 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd03-X3 : St 3164
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd03-X3 = pickᴰ 8 Sᴰ
  lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡KKKK-e≡-1⟩ : St 3165
  lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡KKKK-e≡-1⟩ = pickᴰ 9 Sᴰ
  lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ : St 3166
  lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ = pickᴰ 10 Sᴰ
  lem-AXIOM-LF-at0321 : St 1002
  lem-AXIOM-LF-at0321 = pickᴰ 11 Sᴰ
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : St 3167
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 12 Sᴰ
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ : St 3168
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 13 Sᴰ
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ : St 3169
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 14 Sᴰ
  lem-HD-passes-D : St 3170
  lem-HD-passes-D = pickᴰ 15 Sᴰ
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡S-e≡1⟩ : St 3066
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡S-e≡1⟩ = pickᴰ 16 Sᴰ
  lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ : St 3171
  lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 17 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2280
  lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 18 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2281
  lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 19 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2282
  lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 20 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2283
  lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 21 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : St 3172
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 22 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ : St 3173
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 23 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ : St 3174
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 24 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 : St 2483
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 = pickᴰ 25 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 : St 2505
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 = pickᴰ 26 Sᴰ
  lem-pass-CKd21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 : St 3175
  lem-pass-CKd21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 = pickᴰ 27 Sᴰ
  lem-pass-CK23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 : St 3176
  lem-pass-CK23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 = pickᴰ 28 Sᴰ
  lem-pass-CKd23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 : St 3177
  lem-pass-CKd23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 = pickᴰ 29 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2 : St 2801
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2 = pickᴰ 30 Sᴰ
  lem-pass-CK21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 : St 3178
  lem-pass-CK21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 = pickᴰ 31 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩-2 : St 2822
  lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩-2 = pickᴰ 32 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-3 : St 2824
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-3 = pickᴰ 33 Sᴰ
  lem-pass-CK32-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : St 3179
  lem-pass-CK32-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = pickᴰ 34 Sᴰ
  lem-pass-CK32-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : St 3180
  lem-pass-CK32-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = pickᴰ 35 Sᴰ
  lem-pass-CKd32-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : St 3181
  lem-pass-CKd32-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = pickᴰ 36 Sᴰ
  lem-pass-CKd32-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : St 3182
  lem-pass-CKd32-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = pickᴰ 37 Sᴰ
  lem-pass-CK31-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : St 3183
  lem-pass-CK31-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = pickᴰ 38 Sᴰ
  lem-pass-CKd31-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : St 3184
  lem-pass-CKd31-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = pickᴰ 39 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3 : St 3185
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3 = pickᴰ 40 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3 : St 3186
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3 = pickᴰ 41 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3 : St 3187
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3 = pickᴰ 42 Sᴰ
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡1⟩ : St 3188
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡1⟩ = pickᴰ 43 Sᴰ
  lem-REL-S : St 3087
  lem-REL-S = pickᴰ 44 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-2 : St 3142
  lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-2 = pickᴰ 45 Sᴰ
  lem-pass-CCZ123-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : St 3157
  lem-pass-CCZ123-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = pickᴰ 46 Sᴰ
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ : St 3189
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 47 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ : St 3190
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 48 Sᴰ
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ : St 3191
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ = pickᴰ 49 Sᴰ
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : St 3192
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 50 Sᴰ
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ : St 3193
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 51 Sᴰ
  lem-merge3-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ : St 3194
  lem-merge3-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 52 Sᴰ
  lem-pass-CCZ123-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 : St 3195
  lem-pass-CCZ123-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 = pickᴰ 53 Sᴰ
  lem-pass-CCZ123-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 : St 3196
  lem-pass-CCZ123-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 = pickᴰ 54 Sᴰ
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 3197
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 55 Sᴰ
  lem-pass-TOFF123-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3 : St 3198
  lem-pass-TOFF123-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3 = pickᴰ 56 Sᴰ
  lem-HD-conj-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ : St 3199
  lem-HD-conj-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 57 Sᴰ
  lem-IY : St 3200
  lem-IY = pickᴰ 58 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩-2 : St 3201
  lem-ca-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩-2 = pickᴰ 59 Sᴰ
  lem-pass-CCZ123-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : St 3202
  lem-pass-CCZ123-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = pickᴰ 60 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 3203
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 61 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 3204
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 62 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 3205
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 63 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : St 3206
  lem-pass-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = pickᴰ 64 Sᴰ

private
  q1 : Eqn
  q1 = sE 3142 lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-2
  q2 : Eqn
  q2 = sE 3172 lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩
  q3 : Eqn
  q3 = sE 3142 lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-2

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q1 ∷
   rw 0 q2 ∷
   rw⁻ 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = sE 3167 lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 29 q1 ∷
   rw 0 q4 ∷
   rw⁻ 0 q3 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = wE 2556 W
  q6 : Eqn
  q6 = sE 3175 lem-pass-CKd21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3
  q7 : Eqn
  q7 = sE 3196 lem-pass-CCZ123-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3
  q8 : Eqn
  q8 = sE 3178 lem-pass-CK21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3
  q9 : Eqn
  q9 = wE 2557 W

-- pass [TOFF123] [X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X2 X3]: 5 steps
lem-pass-TOFF123-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 : ⟪ (ℓ "乢丘丞丐与与丑习丽习举丐丏丏丑丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丐与与丑习丽习举丐丏丏丑丘丞乢") ⟫ʷ
lem-pass-TOFF123-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 = derive (ℓ "乢丘丞丐与与丑习丽习举丐丏丏丑丘丞") (ℓ "丘丞丐与与丑习丽习举丐丏丏丑丘丞乢")
  (rw 0 q5 ∷
   rw 2 q6 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 16 q9 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = sE 2801 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2
  q11 : Eqn
  q11 = sE 3191 lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩
  q12 : Eqn
  q12 = sE 2801 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 X3 K0 S0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 Sd0 Kd0 X2 X3]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丞上丈丈下九中九丮上三三下丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞上丈丈下九中九丮上三三下丘丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丞上丈丈下九中九丮上三三下丘丞") (ℓ "丘丞上丈丈下九中九丮上三三下丘丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 31 q10 ∷
   rw 0 q11 ∷
   rw⁻ 0 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = sE 3162 lem-b2g-1011PP2
  q14 : Eqn
  q14 = sE 1002 lem-AXIOM-LF-at0321
  q15 : Eqn
  q15 = sE 3185 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3
  q16 : Eqn
  q16 = sE 3198 lem-pass-TOFF123-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3
  q17 : Eqn
  q17 = sE 3187 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3
  q18 : Eqn
  q18 = sE 3186 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3
  q19 : Eqn
  q19 = sE 1002 lem-AXIOM-LF-at0321
  q20 : Eqn
  q20 = sE 3162 lem-b2g-1011PP2

-- far CS03 CS03 CK30 CS03 CX32 CS02 CS02 CS02 .. 1011PP2 sep 3: 9 steps
lem-far-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02-··-1011PP2-sep-3 : ⟪ (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丌丘丞乣义乣乊丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞乣义乣乊丌丘丞中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临") ⟫ʷ
lem-far-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02-··-1011PP2-sep-3 = derive (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丌丘丞乣义乣乊丌丘丞") (ℓ "丌丘丞乣义乣乊丌丘丞中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临")
  (rw 80 q13 ∷
   rw 0 q14 ∷
   rw 62 q15 ∷
   rw 61 q16 ∷
   rw 30 q17 ∷
   rw 29 q16 ∷
   rw 0 q18 ∷
   rw⁻ 16 q19 ∷
   rw⁻ 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 2425 W
  q22 : Eqn
  q22 = sE 3177 lem-pass-CKd23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3
  q23 : Eqn
  q23 = sE 3195 lem-pass-CCZ123-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3
  q24 : Eqn
  q24 = sE 3176 lem-pass-CK23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3
  q25 : Eqn
  q25 = wE 2426 W

-- pass [TOFF312] [X0 X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X0 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 : ⟪ (ℓ "乨丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞乨") ⟫ʷ
lem-pass-TOFF312-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 = derive (ℓ "乨丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞") (ℓ "丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞乨")
  (rw 0 q21 ∷
   rw 2 q22 ∷
   rw 1 q23 ∷
   rw 0 q24 ∷
   rw 18 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = sE 3194 lem-merge3-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩
  q27 : Eqn
  q27 = wE 389 W
  q28 : Eqn
  q28 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q29 : Eqn
  q29 = wE 2565 W

-- merge-all Gad(t=0, W=(), d=SdKdSS, e=-1): 5 steps
lem-merge-all-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "三下丈丈中九丮九三三上丈丞三下丈丈中九丮九三三上丈丞丘三下丈丈中九丮九三三上丈丘丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丳丢丌") ⟫ʷ
lem-merge-all-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "三下丈丈中九丮九三三上丈丞三下丈丈中九丮九三三上丈丞丘三下丈丈中九丮九三三上丈丘丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丌丳丢丌")
  (rw 0 q26 ∷
   rw 23 q27 ∷
   rw 36 q28 ∷
   rw 11 q26 ∷
   rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = sE 2483 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3
  q31 : Eqn
  q31 = sE 2282 lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q32 : Eqn
  q32 = sE 2280 lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q33 : Eqn
  q33 = sE 3197 lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q34 : Eqn
  q34 = sE 2281 lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q35 : Eqn
  q35 = sE 2283 lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q36 : Eqn
  q36 = sE 2483 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3

-- pass [CS13 TOFF102 CSd13 TOFF102] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 7 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "丽习举习丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞丽习举习") ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "丽习举习丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞丽习举习")
  (rw 4 q30 ∷
   rw⁻ 0 q31 ∷
   rw⁻ 3 q32 ∷
   rw 6 q33 ∷
   rw⁻ 12 q34 ∷
   rw⁻ 15 q35 ∷
   rw⁻ 0 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = sE 2505 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3
  q38 : Eqn
  q38 = sE 3193 lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩
  q39 : Eqn
  q39 = sE 2505 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 31 q37 ∷
   rw 0 q38 ∷
   rw⁻ 0 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = sE 2822 lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩-2
  q41 : Eqn
  q41 = sE 3190 lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩
  q42 : Eqn
  q42 = sE 2822 lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩-2

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘三下丈丈中九丮九三三上丈丘") ⟫ʷ ≈ ⟪ (ℓ "丘三下丈丈中九丮九三三上丈丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘三下丈丈中九丮九三三上丈丘") (ℓ "丘三下丈丈中九丮九三三上丈丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q40 ∷
   rw 0 q41 ∷
   rw⁻ 0 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = sE 3189 lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘三下丈丈中九丮九三三上丈丘") ⟫ʷ ≈ ⟪ (ℓ "丘三下丈丈中九丮九三三上丈丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘三下丈丈中九丮九三三上丈丘") (ℓ "丘三下丈丈中九丮九三三上丈丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 29 q40 ∷
   rw 0 q43 ∷
   rw⁻ 0 q42 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 2297 W
  q45 : Eqn
  q45 = sE 3182 lem-pass-CKd32-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3
  q46 : Eqn
  q46 = sE 3157 lem-pass-CCZ123-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3
  q47 : Eqn
  q47 = sE 3180 lem-pass-CK32-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3
  q48 : Eqn
  q48 = wE 2298 W

-- pass [TOFF213] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 5 steps
lem-pass-TOFF213-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (ℓ "乥丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞乥") ⟫ʷ
lem-pass-TOFF213-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (ℓ "乥丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞乥")
  (rw 0 q44 ∷
   rw 2 q45 ∷
   rw 1 q46 ∷
   rw 0 q47 ∷
   rw 16 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = sE 2824 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-3
  q50 : Eqn
  q50 = sE 3192 lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩
  q51 : Eqn
  q51 = sE 2824 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-3

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 31 q49 ∷
   rw 0 q50 ∷
   rw⁻ 0 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = sE 3181 lem-pass-CKd32-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3
  q53 : Eqn
  q53 = sE 3202 lem-pass-CCZ123-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3
  q54 : Eqn
  q54 = sE 3179 lem-pass-CK32-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3

-- pass [TOFF213] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 5 steps
lem-pass-TOFF213-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (ℓ "乥丌丞丏丑与与丽习举习丏丏丐与丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞乥") ⟫ʷ
lem-pass-TOFF213-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (ℓ "乥丌丞丏丑与与丽习举习丏丏丐与丌丞") (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞乥")
  (rw 0 q44 ∷
   rw 2 q52 ∷
   rw 1 q53 ∷
   rw 0 q54 ∷
   rw 16 q48 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = sE 3201 lem-ca-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩-2
  q56 : Eqn
  q56 = sE 3173 lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩
  q57 : Eqn
  q57 = sE 3201 lem-ca-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩-2

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丌丘丏丑与与丽习举习丏丏丐与丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丌丘丏丑与与丽习举习丏丏丐与丌丘") (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q55 ∷
   rw 0 q56 ∷
   rw⁻ 0 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = sE 3171 lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩

-- pass [CCZ123] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 3 steps
lem-pass-CCZ123-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (ℓ "乜丌丘丏丑与与丽习举习丏丏丐与丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘乜") ⟫ʷ
lem-pass-CCZ123-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (ℓ "乜丌丘丏丑与与丽习举习丏丏丐与丌丘") (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘乜")
  (rw 1 q55 ∷
   rw 0 q58 ∷
   rw⁻ 0 q57 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = sE 3174 lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丌丘丏丑与与丽习举习丏丏丐与丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丌丘丏丑与与丽习举习丏丏丐与丌丘") (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q55 ∷
   rw 0 q59 ∷
   rw⁻ 0 q57 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = sE 3168 lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丌丘丏丑与与丽习举习丏丏丐与丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丌丘丏丑与与丽习举习丏丏丐与丌丘") (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 29 q55 ∷
   rw 0 q60 ∷
   rw⁻ 0 q57 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = sE 3164 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd03-X3
  q62 : Eqn
  q62 = sE 1273 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd30-X3
  q63 : Eqn
  q63 = sE 3163 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS03-X3
  q64 : Eqn
  q64 = sE 3205 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q65 : Eqn
  q65 = sE 1272 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK30-X3

-- Bar(SSSKSS;3,1->0) passes split Gad(t=0, W=(3,), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞丮丞丞乒丞丞中丞丞中丞丞中九丮九丞丞丮丞丞丮丞丞乑丞丞中丞") ⟫ʷ ≈ ⟪ (ℓ "丞丮丞丞乒丞丞中丞丞中丞丞中九丮九丞丞丮丞丞丮丞丞乑丞丞中丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞丮丞丞乒丞丞中丞丞中丞丞中九丮九丞丞丮丞丞丮丞丞乑丞丞中丞") (ℓ "丞丮丞丞乒丞丞中丞丞中丞丞中九丮九丞丞丮丞丞丮丞丞乑丞丞中丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 0 q61 ∷
   rw 3 q62 ∷
   rw 6 q63 ∷
   rw 9 q63 ∷
   rw 12 q64 ∷
   rw 18 q61 ∷
   rw 21 q61 ∷
   rw 24 q65 ∷
   rw 27 q63 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = sE 2980 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd02-X2
  q67 : Eqn
  q67 = sE 1248 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd20-X2
  q68 : Eqn
  q68 = sE 2979 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS02-X2
  q69 : Eqn
  q69 = sE 3203 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q70 : Eqn
  q70 = sE 1247 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK20-X2

-- Bar(SSSKSS;2,1->0) passes split Gad(t=0, W=(2,), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘") ⟫ʷ ≈ ⟪ (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘") (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q66 ∷
   rw 3 q67 ∷
   rw 6 q68 ∷
   rw 9 q68 ∷
   rw 12 q69 ∷
   rw 18 q66 ∷
   rw 21 q66 ∷
   rw 24 q70 ∷
   rw 27 q68 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = sE 3204 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3

-- Bar(SSSKSS;3,1->0) passes split Gad(t=0, W=(2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞") ⟫ʷ ≈ ⟪ (ℓ "丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞") (ℓ "丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 0 q61 ∷
   rw 3 q62 ∷
   rw 6 q63 ∷
   rw 9 q63 ∷
   rw 12 q71 ∷
   rw 20 q61 ∷
   rw 23 q61 ∷
   rw 26 q65 ∷
   rw 29 q63 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 2502 W
  q73 : Eqn
  q73 = sE 3184 lem-pass-CKd31-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3
  q74 : Eqn
  q74 = sE 3183 lem-pass-CK31-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3
  q75 : Eqn
  q75 = wE 2503 W

-- pass [TOFF123] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 5 steps
lem-pass-TOFF123-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (ℓ "乢丌丞丏丑与与丽习举习丏丏丐与丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞乢") ⟫ʷ
lem-pass-TOFF123-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (ℓ "乢丌丞丏丑与与丽习举习丏丏丐与丌丞") (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞乢")
  (rw 0 q72 ∷
   rw 2 q73 ∷
   rw 1 q53 ∷
   rw 0 q74 ∷
   rw 16 q75 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = sE 3169 lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丌丘丏丑与与丽习举习丏丏丐与丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丌丘丏丑与与丽习举习丏丏丐与丌丘") (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 31 q55 ∷
   rw 0 q76 ∷
   rw⁻ 0 q57 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = wE 873 W
  q78 : Eqn
  q78 = sE 3166 lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩
  q79 : Eqn
  q79 = sE 3199 lem-HD-conj-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩
  q80 : Eqn
  q80 = sE 3165 lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡KKKK-e≡-1⟩

-- k conj Gad(t=0, W=(), d=SK, e=-1): 5 steps
lem-k-conj-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "丌丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丌丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈下丈丈下丈中九丮九三上三三上三丌丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丌") ⟫ʷ
lem-k-conj-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ = derive (ℓ "丌丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丌丈上中九丮九下三") (ℓ "丈下丈丈下丈中九丮九三上三三上三丌丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丌")
  (rw 90 q77 ∷
   rw 81 q78 ∷
   rw 1 q79 ∷
   rw 13 q77 ∷
   rw 0 q80 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = sE 3066 lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡S-e≡1⟩
  q82 : Eqn
  q82 = sE 3188 lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡1⟩
  q83 : Eqn
  q83 = sE 3087 lem-REL-S

-- prod Gad(t=0, W=(), d=1, e=1) Gad(t=0, W=(), d=SdKdSS, e=-1): 3 steps
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "九中九丮三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "下三九中九丮丈上") ⟫ʷ
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "九中九丮三下丈丈中九丮九三三上丈") (ℓ "下三九中九丮丈上")
  (rw 0 q81 ∷
   rw 6 q82 ∷
   rw 0 q83 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = sE 3200 lem-IY
  q85 : Eqn
  q85 = sE 3206 lem-pass-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1
  q86 : Eqn
  q86 = sE 3170 lem-HD-passes-D
  q87 : Eqn
  q87 = sE 3200 lem-IY

-- HD passes Y: 4 steps
lem-HD-passes-Y : ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑乛九中九丮") ⟫ʷ ≈ ⟪ (ℓ "乛九中九丮丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") ⟫ʷ
lem-HD-passes-Y = derive (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑乛九中九丮") (ℓ "乛九中九丮丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑")
  (rw 80 q84 ∷
   rw 0 q85 ∷
   rw 6 q86 ∷
   rw⁻ 0 q87 ∷ []) Eq.refl
