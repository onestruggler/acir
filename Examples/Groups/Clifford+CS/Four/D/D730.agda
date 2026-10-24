{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD730 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D730 (W : Ws) (Sᴰ : SD730) where

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
  lem-pass-CK31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2202
  lem-pass-CK31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 0 Sᴰ
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 869
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 1 Sᴰ
  lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 904
  lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 2 Sᴰ
  lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ : St 2203
  lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ = pickᴰ 3 Sᴰ
  lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03 : St 2204
  lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 4 Sᴰ
  lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2205
  lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 5 Sᴰ
  lem-pass-CK20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : St 2206
  lem-pass-CK20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = pickᴰ 6 Sᴰ
  lem-pass-CKd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : St 2207
  lem-pass-CKd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = pickᴰ 7 Sᴰ
  lem-pass-CS20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : St 2208
  lem-pass-CS20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = pickᴰ 8 Sᴰ
  lem-pass-CSd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : St 2209
  lem-pass-CSd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = pickᴰ 9 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 10 Sᴰ
  lem-pass-CK21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2210
  lem-pass-CK21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 11 Sᴰ
  lem-pass-CKd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2211
  lem-pass-CKd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 12 Sᴰ
  lem-pass-CS21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2212
  lem-pass-CS21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 13 Sᴰ
  lem-pass-CS21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : St 2213
  lem-pass-CS21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = pickᴰ 14 Sᴰ
  lem-pass-CSd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2214
  lem-pass-CSd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 15 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1143
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 16 Sᴰ
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1175
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 17 Sᴰ
  lem-pass-CK20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 2215
  lem-pass-CK20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 18 Sᴰ
  lem-pass-CK21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2216
  lem-pass-CK21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 19 Sᴰ
  lem-pass-CKd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 2217
  lem-pass-CKd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 20 Sᴰ
  lem-pass-CKd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2218
  lem-pass-CKd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 21 Sᴰ
  lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2219
  lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 22 Sᴰ
  lem-pass-CS20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 2220
  lem-pass-CS20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 23 Sᴰ
  lem-pass-CS21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2221
  lem-pass-CS21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 24 Sᴰ
  lem-pass-CSd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 2222
  lem-pass-CSd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 25 Sᴰ
  lem-pass-CSd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2223
  lem-pass-CSd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 26 Sᴰ
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 1798
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 27 Sᴰ
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 1799
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 28 Sᴰ
  lem-S2-at1023 : St 1918
  lem-S2-at1023 = pickᴰ 29 Sᴰ
  lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 1924
  lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 30 Sᴰ
  lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2224
  lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 31 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2034
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 32 Sᴰ
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2059
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 33 Sᴰ
  lem-C3d-A : St 2197
  lem-C3d-A = pickᴰ 34 Sᴰ
  lem-pass-X3-K0-CS03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 2225
  lem-pass-X3-K0-CS03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 35 Sᴰ
  lem-pass-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 2226
  lem-pass-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 36 Sᴰ
  lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : St 2227
  lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = pickᴰ 37 Sᴰ
  lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡K-e≡1⟩ : St 2228
  lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡K-e≡1⟩ = pickᴰ 38 Sᴰ
  lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ : St 2229
  lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ = pickᴰ 39 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 : St 2230
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 = pickᴰ 40 Sᴰ
  lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2231
  lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 41 Sᴰ
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF103-CS12-TOFF103-CSd12 : St 2232
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF103-CS12-TOFF103-CSd12 = pickᴰ 42 Sᴰ
  lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2233
  lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 43 Sᴰ
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03 : St 2234
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03 = pickᴰ 44 Sᴰ
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2235
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 45 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2 : St 2236
  lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2 = pickᴰ 46 Sᴰ
  lem-pass-CK21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : St 2237
  lem-pass-CK21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = pickᴰ 47 Sᴰ
  lem-pass-CS31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2238
  lem-pass-CS31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 48 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 : St 2239
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 = pickᴰ 49 Sᴰ
  lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 2240
  lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 50 Sᴰ
  lem-pass-X2-CK20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2241
  lem-pass-X2-CK20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 51 Sᴰ
  lem-pass-X2-CK21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2242
  lem-pass-X2-CK21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 52 Sᴰ
  lem-pass-X2-CK21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2243
  lem-pass-X2-CK21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 53 Sᴰ
  lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2244
  lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 54 Sᴰ
  lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2245
  lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 55 Sᴰ
  lem-pass-X2-CSd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2246
  lem-pass-X2-CSd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 56 Sᴰ
  lem-pass-X2-TOFF012-CS03-TOFF012-CSd03-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2247
  lem-pass-X2-TOFF012-CS03-TOFF012-CSd03-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 57 Sᴰ
  lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2248
  lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 58 Sᴰ
  lem-pass-X3-CK31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2249
  lem-pass-X3-CK31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 59 Sᴰ
  lem-pass-X3-CK31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2250
  lem-pass-X3-CK31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 60 Sᴰ
  lem-pass-X3-CKd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2251
  lem-pass-X3-CKd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 61 Sᴰ
  lem-pass-X3-CKd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2252
  lem-pass-X3-CKd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 62 Sᴰ
  lem-pass-X3-CS31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2253
  lem-pass-X3-CS31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 63 Sᴰ
  lem-pass-X3-CS31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2254
  lem-pass-X3-CS31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 64 Sᴰ
  lem-pass-X3-CSd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2255
  lem-pass-X3-CSd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 65 Sᴰ
  lem-pass-X3-CSd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2256
  lem-pass-X3-CSd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 66 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 : St 2257
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 = pickᴰ 67 Sᴰ
  lem-pass-X2-CK21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : St 2258
  lem-pass-X2-CK21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = pickᴰ 68 Sᴰ
  lem-pass-X2-CSd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : St 2259
  lem-pass-X2-CSd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = pickᴰ 69 Sᴰ

private
  q1 : Eqn
  q1 = sE 2197 lem-C3d-A

-- pass [CSd03] [TOFF012 CS03 TOFF012]: 1 steps
lem-pass-CSd03-vs-TOFF012-CS03-TOFF012 : ⟪ (ℓ "丮九中九") ⟫ʷ ≈ ⟪ (ℓ "九中九丮") ⟫ʷ
lem-pass-CSd03-vs-TOFF012-CS03-TOFF012 = derive (ℓ "丮九中九") (ℓ "九中九丮")
  (rw 0 q1 ∷ []) Eq.refl

private
  q2 : Eqn
  q2 = sE 2226 lem-pass-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q3 : Eqn
  q3 = sE 2204 lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03
  q4 : Eqn
  q4 = sE 2225 lem-pass-X3-K0-CS03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [CCZ012 X3 K0 CS03 Kd0 X3 CCZ012 X3 K0 CSd03 Kd0 X3] [TOFF012 CS03 TOFF012 CSd03]: 4 steps
lem-pass-CCZ012-X3-K0-CS03-Kd0-X3-CCZ012-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "乙丞上中下丞乙丞上丮下丞九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮乙丞上中下丞乙丞上丮下丞") ⟫ʷ
lem-pass-CCZ012-X3-K0-CS03-Kd0-X3-CCZ012-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "乙丞上中下丞乙丞上丮下丞九中九丮") (ℓ "九中九丮乙丞上中下丞乙丞上丮下丞")
  (rw 7 q2 ∷
   rw 6 q3 ∷
   rw 1 q4 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = sE 2203 lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 1696 W
  q9 : Eqn
  q9 = sE 2228 lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡K-e≡1⟩
  q10 : Eqn
  q10 = wE 1342 W
  q11 : Eqn
  q11 = sE 2227 lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩
  q12 : Eqn
  q12 = wE 1356 W

-- CAw KdSK Gad(t=0, W=(), d=1, e=1): 24 steps
lem-CAw-KdSK-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ : ⟪ (ℓ "乒中乑九中九丮乒丮乑") ⟫ʷ ≈ ⟪ (ℓ "三下三九中九丮丈上丈") ⟫ʷ
lem-CAw-KdSK-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ = derive (ℓ "乒中乑九中九丮乒丮乑") (ℓ "三下三九中九丮丈上丈")
  (rw 2 q5 ∷
   rw 10 q6 ∷
   re 9 1 (ℓ "乏久乏") ∷
   rw 11 q7 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw 10 q7 ∷
   rw 9 q8 ∷
   rw 8 q7 ∷
   rw 1 q9 ∷
   rw 11 q6 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q7 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q7 ∷
   rw 10 q10 ∷
   rw 9 q7 ∷
   rw 0 q11 ∷
   rw 12 q6 ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw 13 q7 ∷
   re 10 1 (ℓ "乏久乏") ∷
   rw 12 q7 ∷
   rw 11 q12 ∷
   rw 10 q7 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = sE 2229 lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩

-- CAw S Gad(t=0, W=(), d=SdKdSd, e=1): 8 steps
lem-CAw-S-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ : ⟪ (ℓ "中三下三九中九丮丈上丈丮") ⟫ʷ ≈ ⟪ (ℓ "下三九中九丮丈上") ⟫ʷ
lem-CAw-S-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ = derive (ℓ "中三下三九中九丮丈上丈丮") (ℓ "下三九中九丮丈上")
  (rw 0 q13 ∷
   rw 10 q6 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q7 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q7 ∷
   rw 9 q10 ∷
   rw 8 q7 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q15 : Eqn
  q15 = eqn (ℓ "上丞") (ℓ "丞上") (low₁-comm (K) ((X ↑ ↑)))
  q16 : Eqn
  q16 = eqn (ℓ "三丞") (ℓ "丞三") (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "下丞") (ℓ "丞下") (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q18 : Eqn
  q18 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q19 : Eqn
  q19 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q20 : Eqn
  q20 = wE 2222 W
  q21 : Eqn
  q21 = wE 175 W
  q22 : Eqn
  q22 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q23 : Eqn
  q23 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q24 : Eqn
  q24 = wE 2223 W
  q25 : Eqn
  q25 = sE 2205 lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q26 : Eqn
  q26 = sE 2231 lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q27 : Eqn
  q27 = wE 2224 W

-- ca-split Gad(t=0, W=(3,), d=SK, e=-1) 3: 51 steps
lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 : ⟪ (ℓ "丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞") ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 = derive (ℓ "丞丈上中九丮九下三丞") (ℓ "丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞")
  (rw⁻ 0 q14 ∷
   rw⁻ 1 q15 ∷
   rw 8 q16 ∷
   rw 7 q17 ∷
   rw 2 q6 ∷
   rw 1 q18 ∷
   rw 0 q19 ∷
   rw 1 q20 ∷
   rw 0 q21 ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q21 ∷
   rw 3 q21 ∷
   rw 6 q6 ∷
   re 4 3 (ℓ "乑") ∷
   rw 5 q21 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q7 ∷
   rw 16 q6 ∷
   rw 15 q22 ∷
   rw 14 q23 ∷
   rw 15 q24 ∷
   rw 16 q6 ∷
   re 14 3 (ℓ "乒") ∷
   rw 17 q6 ∷
   re 15 3 (ℓ "丮") ∷
   rw 16 q21 ∷
   rw 19 q6 ∷
   re 17 3 (ℓ "乒") ∷
   rw 18 q21 ∷
   rw 19 q21 ∷
   rw 22 q6 ∷
   re 20 3 (ℓ "丮") ∷
   rw 21 q21 ∷
   rw 22 q7 ∷
   rw 7 q25 ∷
   rw 6 q26 ∷
   rw 16 q6 ∷
   re 15 1 (ℓ "乏丨乏") ∷
   rw 17 q7 ∷
   re 14 1 (ℓ "乏久乏") ∷
   rw 16 q7 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q7 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q7 ∷
   rw 13 q27 ∷
   rw 12 q7 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = sE 1918 lem-S2-at1023
  q29 : Eqn
  q29 = sE 2232 lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF103-CS12-TOFF103-CSd12
  q30 : Eqn
  q30 = sE 1918 lem-S2-at1023

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丞九中九丮丞习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丞九中九丮丞") ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丞九中九丮丞习丽习举") (ℓ "习丽习举丞九中九丮丞")
  (rw 6 q28 ∷
   rw 0 q29 ∷
   rw⁻ 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = sE 2230 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2
  q32 : Eqn
  q32 = sE 2208 lem-pass-CS20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q33 : Eqn
  q33 = sE 2206 lem-pass-CK20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q34 : Eqn
  q34 = sE 2224 lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q35 : Eqn
  q35 = sE 2207 lem-pass-CKd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q36 : Eqn
  q36 = sE 2209 lem-pass-CSd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q37 : Eqn
  q37 = sE 2230 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2

-- pass [X2 TOFF102 CS13 TOFF102 CSd13 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丘习丽习举丘丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丘习丽习举丘") ⟫ʷ
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丘习丽习举丘丈上中九丮九下三") (ℓ "丈上中九丮九下三丘习丽习举丘")
  (rw 6 q31 ∷
   rw⁻ 0 q32 ∷
   rw⁻ 1 q33 ∷
   rw 2 q34 ∷
   rw⁻ 6 q35 ∷
   rw⁻ 7 q36 ∷
   rw⁻ 0 q37 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = sE 2234 lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03

-- pass [CS03] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 1 steps
lem-pass-CS03-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (ℓ "中丞九中九丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞九中九丮丞中") ⟫ʷ
lem-pass-CS03-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (ℓ "中丞九中九丮丞") (ℓ "丞九中九丮丞中")
  (rw⁻ 0 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 225 W
  q40 : Eqn
  q40 = wE 45 W
  q41 : Eqn
  q41 = wE 1357 W
  q42 : Eqn
  q42 = wE 231 W
  q43 : Eqn
  q43 = sE 2235 lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q44 : Eqn
  q44 = wE 390 W
  q45 : Eqn
  q45 = wE 227 W
  q46 : Eqn
  q46 = wE 1358 W

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [CS03 TOFF012 CSd03 TOFF012]: 37 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丞中九丮九丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丞中九丮九丞") ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丞中九丮九丞中九丮九") (ℓ "中九丮九丞中九丮九丞")
  (rw 10 q39 ∷
   rw 11 q40 ∷
   rw 12 q6 ∷
   rw 13 q41 ∷
   rw 14 q6 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q6 ∷
   re 13 3 (ℓ "丮") ∷
   rw 14 q7 ∷
   rw 13 q40 ∷
   rw 14 q6 ∷
   rw 15 q42 ∷
   rw 16 q6 ∷
   re 14 3 (ℓ "丮") ∷
   rw 17 q6 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q7 ∷
   rw 15 q39 ∷
   rw⁻ 6 q43 ∷
   rw 5 q44 ∷
   rw 4 q45 ∷
   rw 5 q6 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q7 ∷
   rw 4 q46 ∷
   rw 3 q7 ∷
   rw 2 q45 ∷
   rw 3 q6 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q7 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q7 ∷
   rw 2 q10 ∷
   rw 1 q7 ∷
   rw 0 q44 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q48 : Eqn
  q48 = eqn (ℓ "上丘") (ℓ "丘上") (low₁-comm (K) ((X ↑)))
  q49 : Eqn
  q49 = eqn (ℓ "三丘") (ℓ "丘三") (low₁-comm ((S • S • S)) ((X ↑)))
  q50 : Eqn
  q50 = eqn (ℓ "下丘") (ℓ "丘下") (low₁-comm ((K • iI)) ((X ↑)))
  q51 : Eqn
  q51 = sE 2233 lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q52 : Eqn
  q52 = sE 2219 lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2

-- ca-split Gad(t=0, W=(2,), d=SK, e=-1) 2: 9 steps
lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2 : ⟪ (ℓ "丘丈上中九丮九下三丘") ⟫ʷ ≈ ⟪ (ℓ "丘丧丘丘乄丘丘中九丮九丘丘久丘丘丨丘") ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2 = derive (ℓ "丘丈上中九丮九下三丘") (ℓ "丘丧丘丘乄丘丘中九丮九丘丘久丘丘丨丘")
  (rw⁻ 0 q47 ∷
   rw⁻ 1 q48 ∷
   rw 8 q49 ∷
   rw 7 q50 ∷
   rw 0 q20 ∷
   rw 14 q24 ∷
   rw 7 q51 ∷
   rw 6 q52 ∷
   rw 12 q27 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = wE 871 W
  q54 : Eqn
  q54 = sE 2247 lem-pass-X2-TOFF012-CS03-TOFF012-CSd03-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q55 : Eqn
  q55 = wE 389 W

-- pass [X2 CS03 TOFF012 CSd03 TOFF012 X2] [CS03 TOFF012 CSd03 TOFF012]: 37 steps
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丘中九丮九丘中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丘中九丮九丘") ⟫ʷ
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丘中九丮九丘中九丮九") (ℓ "中九丮九丘中九丮九丘")
  (rw 10 q53 ∷
   rw 11 q40 ∷
   rw 12 q6 ∷
   rw 13 q41 ∷
   rw 14 q6 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q6 ∷
   re 13 3 (ℓ "丮") ∷
   rw 14 q7 ∷
   rw 13 q40 ∷
   rw 14 q6 ∷
   rw 15 q42 ∷
   rw 16 q6 ∷
   re 14 3 (ℓ "丮") ∷
   rw 17 q6 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q7 ∷
   rw 15 q53 ∷
   rw⁻ 6 q54 ∷
   rw 5 q55 ∷
   rw 4 q45 ∷
   rw 5 q6 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q7 ∷
   rw 4 q46 ∷
   rw 3 q7 ∷
   rw 2 q45 ∷
   rw 3 q6 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q7 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q7 ∷
   rw 2 q10 ∷
   rw 1 q7 ∷
   rw 0 q55 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = wE 1464 W
  q57 : Eqn
  q57 = sE 2244 lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q58 : Eqn
  q58 = wE 1465 W

-- pass [CKd20] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (ℓ "久丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘久") ⟫ʷ
lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (ℓ "久丘中九丮九丘") (ℓ "丘中九丮九丘久")
  (rw 0 q56 ∷
   rw 1 q57 ∷
   rw 5 q58 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 2104 W
  q60 : Eqn
  q60 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q61 : Eqn
  q61 = sE 2034 lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q62 : Eqn
  q62 = wE 2105 W

-- pass [X2 CKd20 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-CKd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丘久丘丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丘久丘丈上中九丮九下三") (ℓ "丈上中九丮九下三丘久丘")
  (rw 0 q59 ∷
   rw 14 q57 ∷
   rw 11 q60 ∷
   rw 8 q60 ∷
   rw 5 q61 ∷
   rw 2 q60 ∷
   rw 6 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 2106 W
  q64 : Eqn
  q64 = sE 1143 lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q65 : Eqn
  q65 = wE 2107 W

-- pass [X2 CS20 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 5 steps
lem-pass-X2-CS20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丘丧丘丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丘丧丘丈上中九丮九下三") (ℓ "丈上中九丮九下三丘丧丘")
  (rw 0 q63 ∷
   rw 8 q64 ∷
   rw 5 q57 ∷
   rw 2 q64 ∷
   rw 6 q65 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = sE 2236 lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2
  q67 : Eqn
  q67 = sE 2212 lem-pass-CS21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q68 : Eqn
  q68 = sE 2210 lem-pass-CK21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q69 : Eqn
  q69 = sE 1798 lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q70 : Eqn
  q70 = sE 2211 lem-pass-CKd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q71 : Eqn
  q71 = sE 2214 lem-pass-CSd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q72 : Eqn
  q72 = sE 2236 lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2

-- pass [X2 CS03 TOFF012 CSd03 TOFF012 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (ℓ "丘中九丮九丘与丐习丽习举丑丏") ⟫ʷ ≈ ⟪ (ℓ "与丐习丽习举丑丏丘中九丮九丘") ⟫ʷ
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (ℓ "丘中九丮九丘与丐习丽习举丑丏") (ℓ "与丐习丽习举丑丏丘中九丮九丘")
  (rw 6 q66 ∷
   rw⁻ 0 q67 ∷
   rw⁻ 1 q68 ∷
   rw 2 q69 ∷
   rw⁻ 6 q70 ∷
   rw⁻ 7 q71 ∷
   rw⁻ 0 q72 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = wE 1407 W
  q74 : Eqn
  q74 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q75 : Eqn
  q75 = sE 2241 lem-pass-X2-CK20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q76 : Eqn
  q76 = wE 1408 W

-- pass [CK20] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 5 steps
lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "乄丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞乄") ⟫ʷ
lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "乄丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞乄")
  (rw 0 q73 ∷
   rw 9 q74 ∷
   rw 1 q75 ∷
   rw 7 q76 ∷
   rw⁻ 6 q74 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = sE 2248 lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3] [CS03 TOFF012 CSd03 TOFF012]: 45 steps
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丘丞中九丮九丘丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丘丞中九丮九丘丞") ⟫ʷ
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丘丞中九丮九丘丞中九丮九") (ℓ "中九丮九丘丞中九丮九丘丞")
  (rw 12 q53 ∷
   rw 13 q39 ∷
   rw 14 q40 ∷
   rw 15 q6 ∷
   rw 16 q41 ∷
   rw 17 q6 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q6 ∷
   re 16 3 (ℓ "丮") ∷
   rw 17 q7 ∷
   rw 16 q40 ∷
   rw 17 q6 ∷
   rw 18 q42 ∷
   rw 19 q6 ∷
   re 17 3 (ℓ "丮") ∷
   rw 20 q6 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q7 ∷
   rw 18 q53 ∷
   rw 19 q39 ∷
   rw⁻ 20 q74 ∷
   rw⁻ 26 q74 ∷
   rw⁻ 8 q77 ∷
   rw 8 q74 ∷
   rw 14 q74 ∷
   rw 7 q44 ∷
   rw 6 q55 ∷
   rw 5 q45 ∷
   rw 6 q6 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   re 4 1 (ℓ "乏丨乏") ∷
   rw 6 q7 ∷
   rw 5 q46 ∷
   rw 4 q7 ∷
   rw 3 q45 ∷
   rw 4 q6 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q7 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q7 ∷
   rw 3 q10 ∷
   rw 2 q7 ∷
   rw 1 q44 ∷
   rw 0 q55 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 5 W
  q79 : Eqn
  q79 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q80 : Eqn
  q80 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q81 : Eqn
  q81 = wE 137 W
  q82 : Eqn
  q82 = wE 1497 W
  q83 : Eqn
  q83 = wE 139 W
  q84 : Eqn
  q84 = wE 31 W
  q85 : Eqn
  q85 = wE 1485 W

-- pass [X2 CKd20 X2] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 25 steps
lem-pass-X2-CKd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "丘久丘丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "丘久丘丞中九丮九丞") (ℓ "丞中九丮九丞丘久丘")
  (rw 4 q78 ∷
   rw⁻ 3 q79 ∷
   rw⁻ 2 q80 ∷
   rw 1 q81 ∷
   rw⁻ 0 q80 ∷
   rw 1 q82 ∷
   rw 0 q79 ∷
   rw 1 q80 ∷
   rw 2 q83 ∷
   rw 3 q80 ∷
   rw 4 q84 ∷
   rw 1 q85 ∷
   rw 1 q57 ∷
   rw 5 q85 ∷
   rw 9 q78 ∷
   rw⁻ 8 q79 ∷
   rw⁻ 7 q80 ∷
   rw 6 q81 ∷
   rw⁻ 5 q80 ∷
   rw 6 q82 ∷
   rw 5 q79 ∷
   rw 6 q80 ∷
   rw 7 q83 ∷
   rw 8 q80 ∷
   rw 9 q84 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = sE 2221 lem-pass-CS21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q87 : Eqn
  q87 = sE 2216 lem-pass-CK21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q88 : Eqn
  q88 = sE 1799 lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q89 : Eqn
  q89 = sE 2218 lem-pass-CKd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q90 : Eqn
  q90 = sE 2223 lem-pass-CSd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3

-- pass [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (ℓ "丘丞中九丮九丘丞与丐习丽习举丑丏") ⟫ʷ ≈ ⟪ (ℓ "与丐习丽习举丑丏丘丞中九丮九丘丞") ⟫ʷ
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (ℓ "丘丞中九丮九丘丞与丐习丽习举丑丏") (ℓ "与丐习丽习举丑丏丘丞中九丮九丘丞")
  (rw 8 q66 ∷
   rw⁻ 0 q86 ∷
   rw⁻ 1 q87 ∷
   rw 2 q88 ∷
   rw⁻ 6 q89 ∷
   rw⁻ 7 q90 ∷
   rw⁻ 0 q72 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q92 : Eqn
  q92 = eqn (ℓ "丐丞") (ℓ "丞丐") (low-comm ((K ↑)) ((X ↑)))
  q93 : Eqn
  q93 = eqn (ℓ "丏丞") (ℓ "丞丏") (low-comm (((S • S • S) ↑)) ((X ↑)))
  q94 : Eqn
  q94 = eqn (ℓ "丑丞") (ℓ "丞丑") (low-comm (((K • iI) ↑)) ((X ↑)))
  q95 : Eqn
  q95 = wE 2225 W
  q96 : Eqn
  q96 = wE 2226 W
  q97 : Eqn
  q97 = sE 2202 lem-pass-CK31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q98 : Eqn
  q98 = sE 2238 lem-pass-CS31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q99 : Eqn
  q99 = wE 2227 W

-- ca-split Gad(t=1, W=(3,), d=SK, e=1) 3: 9 steps
lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3 : ⟪ (ℓ "丞与丐习丽习举丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丞丞乔丞丞习丽习举丞丞乕丞丞举丞") ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3 = derive (ℓ "丞与丐习丽习举丑丏丞") (ℓ "丞丽丞丞乔丞丞习丽习举丞丞乕丞丞举丞")
  (rw⁻ 0 q91 ∷
   rw⁻ 1 q92 ∷
   rw 8 q93 ∷
   rw 7 q94 ∷
   rw 0 q95 ∷
   rw 14 q96 ∷
   rw 7 q97 ∷
   rw 6 q98 ∷
   rw 12 q99 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q101 : Eqn
  q101 = eqn (ℓ "丐丘") (ℓ "丘丐") (low-comm ((K ↑)) (X))
  q102 : Eqn
  q102 = eqn (ℓ "丏丘") (ℓ "丘丏") (low-comm (((S • S • S) ↑)) (X))
  q103 : Eqn
  q103 = eqn (ℓ "丑丘") (ℓ "丘丑") (low-comm (((K • iI) ↑)) (X))
  q104 : Eqn
  q104 = wE 2228 W
  q105 : Eqn
  q105 = wE 2229 W
  q106 : Eqn
  q106 = sE 2237 lem-pass-CK21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q107 : Eqn
  q107 = sE 2213 lem-pass-CS21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q108 : Eqn
  q108 = wE 2230 W

-- ca-split Gad(t=1, W=(2,), d=SK, e=1) 2: 9 steps
lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2 : ⟪ (ℓ "丘与丐习丽习举丑丏丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘丘乇丘丘习丽习举丘丘么丘丘丷丘") ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2 = derive (ℓ "丘与丐习丽习举丑丏丘") (ℓ "丘丶丘丘乇丘丘习丽习举丘丘么丘丘丷丘")
  (rw⁻ 0 q100 ∷
   rw⁻ 1 q101 ∷
   rw 8 q102 ∷
   rw 7 q103 ∷
   rw 0 q104 ∷
   rw 14 q105 ∷
   rw 7 q106 ∷
   rw 6 q107 ∷
   rw 12 q108 ∷ []) Eq.refl

private
  q109 : Eqn
  q109 = wE 1476 W
  q110 : Eqn
  q110 = sE 2243 lem-pass-X2-CK21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q111 : Eqn
  q111 = wE 1477 W

-- pass [CK21] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "乇丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞乇") ⟫ʷ
lem-pass-CK21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "乇丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞乇")
  (rw 0 q109 ∷
   rw 9 q74 ∷
   rw 1 q110 ∷
   rw 7 q111 ∷
   rw⁻ 6 q74 ∷ []) Eq.refl

private
  q112 : Eqn
  q112 = sE 2220 lem-pass-CS20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q113 : Eqn
  q113 = sE 2215 lem-pass-CK20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q114 : Eqn
  q114 = sE 1924 lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q115 : Eqn
  q115 = sE 2217 lem-pass-CKd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q116 : Eqn
  q116 = sE 2222 lem-pass-CSd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3

-- pass [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丘丞习丽习举丘丞丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丘丞习丽习举丘丞") ⟫ʷ
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丘丞习丽习举丘丞丈上中九丮九下三") (ℓ "丈上中九丮九下三丘丞习丽习举丘丞")
  (rw 8 q31 ∷
   rw⁻ 0 q112 ∷
   rw⁻ 1 q113 ∷
   rw 2 q114 ∷
   rw⁻ 6 q115 ∷
   rw⁻ 7 q116 ∷
   rw⁻ 0 q37 ∷ []) Eq.refl

private
  q117 : Eqn
  q117 = wE 2231 W
  q118 : Eqn
  q118 = sE 1175 lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q119 : Eqn
  q119 = sE 2240 lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q120 : Eqn
  q120 = wE 2232 W

-- pass [X1 CSd10 X1] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 5 steps
lem-pass-X1-CSd10-X1-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丒両丒丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丒両丒丈上中九丮九下三") (ℓ "丈上中九丮九下三丒両丒")
  (rw 0 q117 ∷
   rw 8 q118 ∷
   rw 5 q119 ∷
   rw 2 q118 ∷
   rw 6 q120 ∷ []) Eq.refl

private
  q121 : Eqn
  q121 = wE 2233 W
  q122 : Eqn
  q122 = wE 2234 W

-- pass [X1 CSd10 X1] [S0 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 Sd0]: 5 steps
lem-pass-X1-CSd10-X1-vs-S0-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-Sd0 : ⟪ (ℓ "丒両丒丈丈上中九丮九下三三") ⟫ʷ ≈ ⟪ (ℓ "丈丈上中九丮九下三三丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-S0-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-Sd0 = derive (ℓ "丒両丒丈丈上中九丮九下三三") (ℓ "丈丈上中九丮九下三三丒両丒")
  (rw 0 q121 ∷
   rw 9 q118 ∷
   rw 6 q119 ∷
   rw 3 q118 ∷
   rw 7 q122 ∷ []) Eq.refl

private
  q123 : Eqn
  q123 = wE 2113 W
  q124 : Eqn
  q124 = sE 2255 lem-pass-X3-CSd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q125 : Eqn
  q125 = wE 2114 W

-- pass [CSd31] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CSd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "举丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞举") ⟫ʷ
lem-pass-CSd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "举丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞举")
  (rw 0 q123 ∷
   rw 1 q124 ∷
   rw 9 q125 ∷ []) Eq.refl

private
  q126 : Eqn
  q126 = wE 1940 W
  q127 : Eqn
  q127 = sE 2251 lem-pass-X3-CKd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q128 : Eqn
  q128 = wE 1941 W

-- pass [CKd31] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CKd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "乕丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞乕") ⟫ʷ
lem-pass-CKd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "乕丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞乕")
  (rw 0 q126 ∷
   rw 1 q127 ∷
   rw 9 q128 ∷ []) Eq.refl

private
  q129 : Eqn
  q129 = wE 1366 W
  q130 : Eqn
  q130 = sE 2249 lem-pass-X3-CK31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q131 : Eqn
  q131 = wE 1367 W

-- pass [CK31] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CK31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "乔丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞乔") ⟫ʷ
lem-pass-CK31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "乔丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞乔")
  (rw 0 q129 ∷
   rw 1 q130 ∷
   rw 9 q131 ∷ []) Eq.refl

private
  q132 : Eqn
  q132 = wE 2111 W
  q133 : Eqn
  q133 = sE 2253 lem-pass-X3-CS31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q134 : Eqn
  q134 = wE 2112 W

-- pass [CS31] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CS31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "丽丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞丽") ⟫ʷ
lem-pass-CS31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "丽丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞丽")
  (rw 0 q132 ∷
   rw 1 q133 ∷
   rw 9 q134 ∷ []) Eq.refl

private
  q135 : Eqn
  q135 = sE 2256 lem-pass-X3-CSd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1

-- pass [CSd31] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 3 steps
lem-pass-CSd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (ℓ "举丞与丐习丽习举丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐习丽习举丑丏丞举") ⟫ʷ
lem-pass-CSd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (ℓ "举丞与丐习丽习举丑丏丞") (ℓ "丞与丐习丽习举丑丏丞举")
  (rw 0 q123 ∷
   rw 1 q135 ∷
   rw 9 q125 ∷ []) Eq.refl

private
  q136 : Eqn
  q136 = sE 2252 lem-pass-X3-CKd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1

-- pass [CKd31] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 3 steps
lem-pass-CKd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (ℓ "乕丞与丐习丽习举丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐习丽习举丑丏丞乕") ⟫ʷ
lem-pass-CKd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (ℓ "乕丞与丐习丽习举丑丏丞") (ℓ "丞与丐习丽习举丑丏丞乕")
  (rw 0 q126 ∷
   rw 1 q136 ∷
   rw 9 q128 ∷ []) Eq.refl

private
  q137 : Eqn
  q137 = sE 2250 lem-pass-X3-CK31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1

-- pass [CK31] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 3 steps
lem-pass-CK31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (ℓ "乔丞与丐习丽习举丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐习丽习举丑丏丞乔") ⟫ʷ
lem-pass-CK31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (ℓ "乔丞与丐习丽习举丑丏丞") (ℓ "丞与丐习丽习举丑丏丞乔")
  (rw 0 q129 ∷
   rw 1 q137 ∷
   rw 9 q131 ∷ []) Eq.refl

private
  q138 : Eqn
  q138 = sE 2254 lem-pass-X3-CS31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1

-- pass [CS31] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 3 steps
lem-pass-CS31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (ℓ "丽丞与丐习丽习举丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐习丽习举丑丏丞丽") ⟫ʷ
lem-pass-CS31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (ℓ "丽丞与丐习丽习举丑丏丞") (ℓ "丞与丐习丽习举丑丏丞丽")
  (rw 0 q132 ∷
   rw 1 q138 ∷
   rw 9 q134 ∷ []) Eq.refl

private
  q139 : Eqn
  q139 = wE 1778 W
  q140 : Eqn
  q140 = wE 257 W
  q141 : Eqn
  q141 = wE 258 W
  q142 : Eqn
  q142 = sE 2239 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13
  q143 : Eqn
  q143 = wE 1777 W

-- pass [X2 TOFF102 CS13 TOFF102 CSd13 X2] [TOFF102 CS13 TOFF102 CSd13]: 9 steps
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丘习丽习举丘习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丘习丽习举丘") ⟫ʷ
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丘习丽习举丘习丽习举") (ℓ "习丽习举丘习丽习举丘")
  (rw 5 q139 ∷
   rw 8 q140 ∷
   rw 9 q139 ∷
   rw 12 q141 ∷
   rw 1 q142 ∷
   rw 0 q143 ∷
   rw 1 q140 ∷
   rw 2 q143 ∷
   rw 3 q141 ∷ []) Eq.refl

private
  q144 : Eqn
  q144 = wE 1480 W
  q145 : Eqn
  q145 = sE 2246 lem-pass-X2-CSd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q146 : Eqn
  q146 = wE 1481 W

-- pass [CSd21] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 3 steps
lem-pass-CSd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (ℓ "丷丘与丐习丽习举丑丏丘") ⟫ʷ ≈ ⟪ (ℓ "丘与丐习丽习举丑丏丘丷") ⟫ʷ
lem-pass-CSd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = derive (ℓ "丷丘与丐习丽习举丑丏丘") (ℓ "丘与丐习丽习举丑丏丘丷")
  (rw 0 q144 ∷
   rw 1 q145 ∷
   rw 9 q146 ∷ []) Eq.refl

private
  q147 : Eqn
  q147 = wE 2235 W
  q148 : Eqn
  q148 = sE 2245 lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q149 : Eqn
  q149 = sE 869 lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q150 : Eqn
  q150 = sE 2059 lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q151 : Eqn
  q151 = wE 2236 W

-- pass [X2 CKd21 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X2-CKd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (ℓ "丘么丘与丐习丽习举丑丏") ⟫ʷ ≈ ⟪ (ℓ "与丐习丽习举丑丏丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (ℓ "丘么丘与丐习丽习举丑丏") (ℓ "与丐习丽习举丑丏丘么丘")
  (rw 0 q147 ∷
   rw 14 q148 ∷
   rw 11 q149 ∷
   rw 8 q149 ∷
   rw 5 q150 ∷
   rw 2 q149 ∷
   rw 6 q151 ∷ []) Eq.refl

private
  q152 : Eqn
  q152 = sE 2242 lem-pass-X2-CK21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1

-- pass [CK21] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 3 steps
lem-pass-CK21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (ℓ "乇丘与丐习丽习举丑丏丘") ⟫ʷ ≈ ⟪ (ℓ "丘与丐习丽习举丑丏丘乇") ⟫ʷ
lem-pass-CK21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = derive (ℓ "乇丘与丐习丽习举丑丏丘") (ℓ "丘与丐习丽习举丑丏丘乇")
  (rw 0 q109 ∷
   rw 1 q152 ∷
   rw 9 q111 ∷ []) Eq.refl

private
  q153 : Eqn
  q153 = wE 2237 W
  q154 : Eqn
  q154 = sE 904 lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q155 : Eqn
  q155 = wE 2238 W

-- pass [X2 CS21 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X2-CS21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (ℓ "丘丶丘与丐习丽习举丑丏") ⟫ʷ ≈ ⟪ (ℓ "与丐习丽习举丑丏丘丶丘") ⟫ʷ
lem-pass-X2-CS21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (ℓ "丘丶丘与丐习丽习举丑丏") (ℓ "与丐习丽习举丑丏丘丶丘")
  (rw 0 q153 ∷
   rw 8 q154 ∷
   rw 5 q148 ∷
   rw 2 q154 ∷
   rw 6 q155 ∷ []) Eq.refl

private
  q156 : Eqn
  q156 = eqn (ℓ "习丞") (ℓ "丞习") (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q157 : Eqn
  q157 = wE 1958 W
  q158 : Eqn
  q158 = wE 1959 W
  q159 : Eqn
  q159 = sE 2257 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13
  q160 : Eqn
  q160 = wE 1960 W
  q161 : Eqn
  q161 = wE 1961 W

-- pass [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3] [TOFF102 CS13 TOFF102 CSd13]: 31 steps
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丘丞习丽习举丘丞习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丘丞习丽习举丘丞") ⟫ʷ
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丘丞习丽习举丘丞习丽习举") (ℓ "习丽习举丘丞习丽习举丘丞")
  (rw⁻ 7 q156 ∷
   rw 8 q157 ∷
   rw⁻ 10 q156 ∷
   rw 11 q158 ∷
   rw 6 q139 ∷
   rw⁻ 9 q100 ∷
   rw 10 q141 ∷
   rw 11 q139 ∷
   rw⁻ 14 q102 ∷
   rw 15 q140 ∷
   rw 2 q159 ∷
   rw⁻ 1 q74 ∷
   rw⁻ 2 q156 ∷
   rw⁻ 3 q74 ∷
   rw⁻ 4 q91 ∷
   rw 5 q158 ∷
   rw⁻ 7 q74 ∷
   rw⁻ 8 q156 ∷
   rw⁻ 9 q74 ∷
   rw⁻ 10 q93 ∷
   rw 11 q157 ∷
   rw 0 q143 ∷
   rw⁻ 1 q100 ∷
   rw⁻ 2 q102 ∷
   rw 3 q140 ∷
   rw 4 q143 ∷
   rw⁻ 5 q102 ∷
   rw⁻ 6 q100 ∷
   rw 7 q141 ∷
   rw 1 q160 ∷
   rw 3 q161 ∷ []) Eq.refl

private
  q162 : Eqn
  q162 = sE 2259 lem-pass-X2-CSd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3

-- pass [CSd21] [X2 X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CSd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : ⟪ (ℓ "丷丘丞与丐习丽习举丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐习丽习举丑丏丘丞丷") ⟫ʷ
lem-pass-CSd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = derive (ℓ "丷丘丞与丐习丽习举丑丏丘丞") (ℓ "丘丞与丐习丽习举丑丏丘丞丷")
  (rw 0 q144 ∷
   rw 13 q74 ∷
   rw 1 q162 ∷
   rw 11 q146 ∷
   rw⁻ 10 q74 ∷ []) Eq.refl

-- pass [X2 CKd21 X2] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 9 steps
lem-pass-X2-CKd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (ℓ "丘么丘丞与丐习丽习举丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐习丽习举丑丏丞丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (ℓ "丘么丘丞与丐习丽习举丑丏丞") (ℓ "丞与丐习丽习举丑丏丞丘么丘")
  (rw 0 q82 ∷
   rw 1 q147 ∷
   rw 15 q148 ∷
   rw 12 q149 ∷
   rw 9 q149 ∷
   rw 6 q150 ∷
   rw 3 q149 ∷
   rw 7 q151 ∷
   rw 9 q82 ∷ []) Eq.refl

private
  q163 : Eqn
  q163 = sE 2258 lem-pass-X2-CK21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3

-- pass [CK21] [X2 X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : ⟪ (ℓ "乇丘丞与丐习丽习举丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐习丽习举丑丏丘丞乇") ⟫ʷ
lem-pass-CK21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = derive (ℓ "乇丘丞与丐习丽习举丑丏丘丞") (ℓ "丘丞与丐习丽习举丑丏丘丞乇")
  (rw 0 q109 ∷
   rw 13 q74 ∷
   rw 1 q163 ∷
   rw 11 q111 ∷
   rw⁻ 10 q74 ∷ []) Eq.refl

private
  q164 : Eqn
  q164 = wE 1493 W

-- pass [X2 CS21 X2] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 7 steps
lem-pass-X2-CS21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (ℓ "丘丶丘丞与丐习丽习举丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐习丽习举丑丏丞丘丶丘") ⟫ʷ
lem-pass-X2-CS21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (ℓ "丘丶丘丞与丐习丽习举丑丏丞") (ℓ "丞与丐习丽习举丑丏丞丘丶丘")
  (rw 0 q164 ∷
   rw 1 q153 ∷
   rw 9 q154 ∷
   rw 6 q148 ∷
   rw 3 q154 ∷
   rw 7 q155 ∷
   rw 9 q164 ∷ []) Eq.refl
