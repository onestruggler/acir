{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD721 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D721 (W : Ws) (Sᴰ : SD721) where

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
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12 : St 200
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12 : St 201
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12 = pickᴰ 1 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS12 : St 224
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS12 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CSd12 : St 225
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CSd12 = pickᴰ 3 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS12 : St 244
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS12 = pickᴰ 4 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CSd12 : St 245
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CSd12 = pickᴰ 5 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2 : St 293
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2 = pickᴰ 6 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2 : St 299
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2 = pickᴰ 7 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2 : St 365
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2 = pickᴰ 8 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2 : St 367
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2 = pickᴰ 9 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF103-X3 : St 377
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF103-X3 = pickᴰ 10 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-X2 : St 430
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-X2 = pickᴰ 11 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2 : St 431
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2 = pickᴰ 12 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-X2 : St 446
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-X2 = pickᴰ 13 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-X2 : St 448
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-X2 = pickᴰ 14 Sᴰ
  lem-pass-CCZ123-vs-X2-CKd20-X2 : St 2131
  lem-pass-CCZ123-vs-X2-CKd20-X2 = pickᴰ 15 Sᴰ
  lem-pass-CCZ123-vs-X2-CS02-X2 : St 2132
  lem-pass-CCZ123-vs-X2-CS02-X2 = pickᴰ 16 Sᴰ
  lem-pass-CCZ123-vs-X2-CSd02-X2 : St 2133
  lem-pass-CCZ123-vs-X2-CSd02-X2 = pickᴰ 17 Sᴰ
  lem-pass-CCZ123-vs-X2-CK20-X2 : St 2134
  lem-pass-CCZ123-vs-X2-CK20-X2 = pickᴰ 18 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 19 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF103-X3 : St 1655
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF103-X3 = pickᴰ 20 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3 : St 1664
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3 = pickᴰ 21 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF103-X3 : St 1665
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF103-X3 = pickᴰ 22 Sᴰ
  lem-S2-at1023 : St 1918
  lem-S2-at1023 = pickᴰ 23 Sᴰ
  lem-S2-at2013 : St 1942
  lem-S2-at2013 = pickᴰ 24 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2034
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 25 Sᴰ
  lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 2052
  lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 26 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2038
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 27 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2049
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 28 Sᴰ
  lem-pass-X3-CK32-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 2135
  lem-pass-X3-CK32-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 29 Sᴰ
  lem-pass-X3-CKd32-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 2136
  lem-pass-X3-CKd32-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 30 Sᴰ
  lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : St 2081
  lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 31 Sᴰ
  lem-S2-at2013-ᵖ-1 : St 2085
  lem-S2-at2013-ᵖ-1 = pickᴰ 32 Sᴰ
  lem-distribute-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12 : St 2137
  lem-distribute-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12 = pickᴰ 33 Sᴰ
  lem-distribute-Gad⟨t≡2-W≡⟨3⟩-d≡1-e≡1⟩-TOFF203-CS12-TOFF203-CSd12 : St 2138
  lem-distribute-Gad⟨t≡2-W≡⟨3⟩-d≡1-e≡1⟩-TOFF203-CS12-TOFF203-CSd12 = pickᴰ 34 Sᴰ
  lem-pass-CCZ123-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2139
  lem-pass-CCZ123-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 35 Sᴰ
  lem-pass-CCZ123-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : St 2140
  lem-pass-CCZ123-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = pickᴰ 36 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 2141
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 37 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 2142
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 38 Sᴰ
  lem-pass-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3-vs-CCZ123 : St 2143
  lem-pass-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3-vs-CCZ123 = pickᴰ 39 Sᴰ
  lem-pass-X2-CK20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : St 2144
  lem-pass-X2-CK20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = pickᴰ 40 Sᴰ
  lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2145
  lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 41 Sᴰ
  lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2146
  lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 42 Sᴰ
  lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2147
  lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 43 Sᴰ
  lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2148
  lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 44 Sᴰ
  lem-pass-X3-CK31-X3-vs-TOFF201-CS23-TOFF201-CSd23 : St 2149
  lem-pass-X3-CK31-X3-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 45 Sᴰ
  lem-pass-X3-CK32-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2150
  lem-pass-X3-CK32-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 46 Sᴰ
  lem-pass-X3-CKd30-X3-vs-Sd0-TOFF012-CS03-TOFF012-CSd03-S0 : St 2151
  lem-pass-X3-CKd30-X3-vs-Sd0-TOFF012-CS03-TOFF012-CSd03-S0 = pickᴰ 47 Sᴰ
  lem-pass-X3-CKd31-X3-vs-TOFF201-CS23-TOFF201-CSd23 : St 2152
  lem-pass-X3-CKd31-X3-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 48 Sᴰ
  lem-pass-X3-CKd32-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2153
  lem-pass-X3-CKd32-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 49 Sᴰ
  lem-pass-X3-CSd30-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : St 2154
  lem-pass-X3-CSd30-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = pickᴰ 50 Sᴰ
  lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CCZ123 : St 2155
  lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CCZ123 = pickᴰ 51 Sᴰ
  lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-CCZ123 : St 2156
  lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-CCZ123 = pickᴰ 52 Sᴰ

private
  q1 : Eqn
  q1 = sE 2133 lem-pass-CCZ123-vs-X2-CSd02-X2
  q2 : Eqn
  q2 = sE 2131 lem-pass-CCZ123-vs-X2-CKd20-X2
  q3 : Eqn
  q3 = sE 2132 lem-pass-CCZ123-vs-X2-CS02-X2
  q4 : Eqn
  q4 = sE 2139 lem-pass-CCZ123-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q5 : Eqn
  q5 = sE 2134 lem-pass-CCZ123-vs-X2-CK20-X2

-- CCZ(2,3,1) passes split Gad(t=0, W=(2, 3), d=SdKdSS, e=-1): 9 steps
lem-CCZ⟨231⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (CCZ123 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨231⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (CCZ123 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ CCZ123 ∷ [])
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
  q6 = wE 5 W
  q7 : Eqn
  q7 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q9 : Eqn
  q9 = wE 76 W
  q10 : Eqn
  q10 = wE 1499 W
  q11 : Eqn
  q11 = wE 29 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = wE 2061 W
  q14 : Eqn
  q14 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q15 : Eqn
  q15 = sE 2034 lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q16 : Eqn
  q16 = wE 2062 W

-- pass [X2 CSd20 X2] [X3 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 X3]: 27 steps
lem-pass-X2-CSd20-X2-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3 = derive (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 4 q6 ∷
   rw⁻ 3 q7 ∷
   rw⁻ 2 q8 ∷
   rw 1 q9 ∷
   rw⁻ 0 q8 ∷
   rw 1 q10 ∷
   rw 0 q7 ∷
   rw 1 q8 ∷
   rw 2 q11 ∷
   rw 3 q8 ∷
   rw 4 q12 ∷
   rw 1 q13 ∷
   rw 8 q14 ∷
   rw 5 q15 ∷
   rw 2 q14 ∷
   rw 6 q16 ∷
   rw 11 q6 ∷
   rw⁻ 10 q7 ∷
   rw⁻ 9 q8 ∷
   rw 8 q9 ∷
   rw⁻ 7 q8 ∷
   rw 8 q10 ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q11 ∷
   rw 10 q8 ∷
   rw 11 q12 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q18 : Eqn
  q18 = wE 2063 W
  q19 : Eqn
  q19 = wE 1 W
  q20 : Eqn
  q20 = wE 173 W
  q21 : Eqn
  q21 = wE 3 W
  q22 : Eqn
  q22 = wE 1482 W
  q23 : Eqn
  q23 = wE 175 W
  q24 : Eqn
  q24 = sE 2049 lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [X3 CSd30 X3] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 61 steps
lem-pass-X3-CSd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q6 ∷
   rw⁻ 3 q8 ∷
   rw⁻ 2 q7 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q17 ∷
   rw 2 q9 ∷
   rw⁻ 1 q17 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q7 ∷
   rw 1 q18 ∷
   rw 0 q8 ∷
   rw 1 q7 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q17 ∷
   rw 3 q11 ∷
   rw 4 q17 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q7 ∷
   rw 4 q12 ∷
   rw 4 q19 ∷
   rw 3 q20 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   rw 1 q20 ∷
   rw 2 q22 ∷
   rw 1 q23 ∷
   rw 4 q19 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q23 ∷
   rw 4 q21 ∷
   rw 1 q24 ∷
   rw 8 q19 ∷
   rw 7 q20 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 5 q20 ∷
   rw 6 q22 ∷
   rw 5 q23 ∷
   rw 8 q19 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q23 ∷
   rw 8 q21 ∷
   rw 9 q6 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 7 q7 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q17 ∷
   rw 7 q9 ∷
   rw⁻ 6 q17 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q7 ∷
   rw 6 q18 ∷
   rw 5 q8 ∷
   rw 6 q7 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   rw 8 q11 ∷
   rw 9 q17 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q12 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 7 W
  q26 : Eqn
  q26 = wE 2064 W
  q27 : Eqn
  q27 = wE 27 W
  q28 : Eqn
  q28 = wE 1490 W
  q29 : Eqn
  q29 = sE 2038 lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [X3 CS30 X3] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 61 steps
lem-pass-X3-CS30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (X3 ∷ CS03 ∷ X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 4 q6 ∷
   rw⁻ 3 q8 ∷
   rw⁻ 2 q7 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q17 ∷
   rw 2 q25 ∷
   rw⁻ 1 q17 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q7 ∷
   rw 1 q26 ∷
   rw 0 q8 ∷
   rw 1 q7 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q17 ∷
   rw 3 q27 ∷
   rw 4 q17 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q7 ∷
   rw 4 q12 ∷
   rw 4 q19 ∷
   rw 3 q20 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   rw 1 q20 ∷
   rw 2 q28 ∷
   rw 1 q23 ∷
   rw 4 q19 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q23 ∷
   rw 4 q21 ∷
   rw 1 q29 ∷
   rw 8 q19 ∷
   rw 7 q20 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 5 q20 ∷
   rw 6 q28 ∷
   rw 5 q23 ∷
   rw 8 q19 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q23 ∷
   rw 8 q21 ∷
   rw 9 q6 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 7 q7 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q17 ∷
   rw 7 q25 ∷
   rw⁻ 6 q17 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 5 q7 ∷
   rw 6 q26 ∷
   rw 5 q8 ∷
   rw 6 q7 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   rw 8 q27 ∷
   rw 9 q17 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q12 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = sE 365 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2
  q31 : Eqn
  q31 = sE 293 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2
  q32 : Eqn
  q32 = sE 2141 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3
  q33 : Eqn
  q33 = sE 299 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2
  q34 : Eqn
  q34 = sE 367 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2

-- Bar(SSKSKK;2,3->0) passes split Gad(t=1, W=(0, 2, 3), d=SK, e=-1): 5 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 0 q30 ∷
   rw 3 q31 ∷
   rw 6 q32 ∷
   rw 16 q33 ∷
   rw 19 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = sE 446 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-X2
  q36 : Eqn
  q36 = sE 430 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-X2
  q37 : Eqn
  q37 = sE 2142 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3
  q38 : Eqn
  q38 = sE 431 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2
  q39 : Eqn
  q39 = sE 448 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-X2

-- Bar(SSSKSS;2,3->0) passes split Gad(t=1, W=(0, 2, 3), d=SK, e=-1): 5 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 0 q35 ∷
   rw 3 q36 ∷
   rw 6 q37 ∷
   rw 16 q38 ∷
   rw 19 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = sE 2085 lem-S2-at2013-ᵖ-1
  q41 : Eqn
  q41 = wE 2071 W
  q42 : Eqn
  q42 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q43 : Eqn
  q43 = eqn (X0 ∷ CS12 ∷ []) (CS12 ∷ X0 ∷ []) (low₁-comm (X) (CS))
  q44 : Eqn
  q44 = wE 387 W
  q45 : Eqn
  q45 = eqn (CS12 ∷ X3 ∷ []) (X3 ∷ CS12 ∷ []) (low₃-comm ((CS ↑)) (X))
  q46 : Eqn
  q46 = wE 390 W
  q47 : Eqn
  q47 = eqn (X0 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X0 ∷ []) (low₁-comm (X) ((CS • CS • CS)))
  q48 : Eqn
  q48 = eqn (CS12⁻ ∷ X3 ∷ []) (X3 ∷ CS12⁻ ∷ []) (low₃-comm (((CS • CS • CS) ↑)) (X))

-- distribute Gad(t=2, W=(0, 3), d=1, e=-1) CS12 TOFF203 CSd12 TOFF203: 14 steps
lem-distribute-Gad⟨t≡2-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF203-CSd12-TOFF203 : ⟪ (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡2-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF203-CSd12-TOFF203 = derive (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) (CS12 ∷ X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ [])
  (rw 2 q40 ∷
   rw 3 q41 ∷
   rw 8 q41 ∷
   rw 13 q41 ∷
   rw 0 q42 ∷
   rw 1 q43 ∷
   rw 2 q44 ∷
   rw⁻ 0 q45 ∷
   rw 1 q46 ∷
   rw 6 q42 ∷
   rw 7 q47 ∷
   rw 8 q44 ∷
   rw⁻ 6 q48 ∷
   rw 7 q46 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = sE 2143 lem-pass-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3-vs-CCZ123

-- pass [CCZ123] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 1 steps
lem-pass-CCZ123-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (CCZ123 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = derive (CCZ123 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q49 ∷ []) Eq.refl

-- Bar(SSKSKK;2,3->0) passes split Gad(t=1, W=(0, 2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 0 q34 ∷
   rw 3 q33 ∷
   rw 6 q30 ∷
   rw 9 q30 ∷
   rw 12 q32 ∷
   rw 22 q34 ∷
   rw 25 q34 ∷
   rw 28 q31 ∷
   rw 31 q30 ∷ []) Eq.refl

-- Bar(SSSKSS;2,3->0) passes split Gad(t=1, W=(0, 2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 0 q39 ∷
   rw 3 q38 ∷
   rw 6 q35 ∷
   rw 9 q35 ∷
   rw 12 q37 ∷
   rw 22 q39 ∷
   rw 25 q39 ∷
   rw 28 q36 ∷
   rw 31 q35 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 1464 W
  q51 : Eqn
  q51 = sE 2151 lem-pass-X3-CKd30-X3-vs-Sd0-TOFF012-CS03-TOFF012-CSd03-S0
  q52 : Eqn
  q52 = wE 1465 W

-- pass [CKd30] [X3 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 X3]: 23 steps
lem-pass-CKd30-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 : ⟪ (CK30⁻ ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-pass-CKd30-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 = derive (CK30⁻ ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ CK30⁻ ∷ [])
  (rw 2 q19 ∷
   rw 1 q20 ∷
   re 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q21 ∷
   rw 1 q50 ∷
   rw 0 q23 ∷
   rw 1 q23 ∷
   rw 4 q19 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q23 ∷
   rw 4 q21 ∷
   rw 1 q51 ∷
   rw 11 q19 ∷
   rw 10 q20 ∷
   rw 9 q20 ∷
   re 8 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw 7 q20 ∷
   rw 8 q52 ∷
   rw 7 q23 ∷
   rw 10 q19 ∷
   re 8 3 (CK30⁻ ∷ []) ∷
   rw 9 q21 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = wE 1674 W
  q54 : Eqn
  q54 = sE 2136 lem-pass-X3-CKd32-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q55 : Eqn
  q55 = wE 1675 W

-- pass [CKd32] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 3 steps
lem-pass-CKd32-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (CK32⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK32⁻ ∷ []) ⟫ʷ
lem-pass-CKd32-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (CK32⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK32⁻ ∷ [])
  (rw 0 q53 ∷
   rw 1 q54 ∷
   rw 5 q55 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = sE 2140 lem-pass-CCZ123-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3

-- CCZ(3,1,2) passes split Gad(t=0, W=(3,), d=1, e=1): 1 steps
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ : ⟪ (CCZ123 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ = derive (CCZ123 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ [])
  (rw 0 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 1409 W
  q58 : Eqn
  q58 = sE 2135 lem-pass-X3-CK32-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q59 : Eqn
  q59 = wE 1410 W

-- pass [CK32] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 3 steps
lem-pass-CK32-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (CK32 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CK32-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (CK32 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK32 ∷ [])
  (rw 0 q57 ∷
   rw 1 q58 ∷
   rw 5 q59 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = wE 1709 W
  q61 : Eqn
  q61 = sE 2144 lem-pass-X2-CK20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3
  q62 : Eqn
  q62 = eqn (K0⁻ ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q63 : Eqn
  q63 = wE 1710 W
  q64 : Eqn
  q64 = wE 116 W
  q65 : Eqn
  q65 = wE 1711 W

-- CA CKd20 Gad(t=0, W=(3,), d=1, e=1): 7 steps
lem-CA-CKd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ : ⟪ (CK20⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-CA-CKd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ = derive (CK20⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ CK20⁻ ∷ [])
  (rw 0 q60 ∷
   rw 1 q61 ∷
   rw 0 q62 ∷
   rw 1 q63 ∷
   rw 6 q64 ∷
   rw 7 q62 ∷
   rw 8 q65 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 1466 W
  q67 : Eqn
  q67 = sE 2154 lem-pass-X3-CSd30-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0
  q68 : Eqn
  q68 = wE 1467 W

-- pass [CSd30] [X3 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 X3]: 23 steps
lem-pass-CSd30-vs-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X3 : ⟪ (CS03⁻ ∷ X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd30-vs-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X3 = derive (CS03⁻ ∷ X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ CS03⁻ ∷ [])
  (rw 2 q19 ∷
   rw 1 q20 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q21 ∷
   rw 1 q66 ∷
   rw 0 q23 ∷
   rw 1 q23 ∷
   rw 4 q19 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q23 ∷
   rw 4 q21 ∷
   rw 1 q67 ∷
   rw 11 q19 ∷
   rw 10 q20 ∷
   rw 9 q20 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw 7 q20 ∷
   rw 8 q68 ∷
   rw 7 q23 ∷
   rw 10 q19 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q21 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = wE 137 W
  q70 : Eqn
  q70 = wE 1497 W
  q71 : Eqn
  q71 = wE 139 W
  q72 : Eqn
  q72 = wE 1712 W
  q73 : Eqn
  q73 = sE 2052 lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03
  q74 : Eqn
  q74 = wE 1713 W

-- pass [X2 CKd20 X2] [X3 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 X3]: 25 steps
lem-pass-X2-CKd20-X2-vs-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X3 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X3 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 4 q6 ∷
   rw⁻ 3 q7 ∷
   rw⁻ 2 q8 ∷
   rw 1 q69 ∷
   rw⁻ 0 q8 ∷
   rw 1 q70 ∷
   rw 0 q7 ∷
   rw 1 q8 ∷
   rw 2 q71 ∷
   rw 3 q8 ∷
   rw 4 q12 ∷
   rw 1 q72 ∷
   rw 2 q73 ∷
   rw 6 q74 ∷
   rw 11 q6 ∷
   rw⁻ 10 q7 ∷
   rw⁻ 9 q8 ∷
   rw 8 q69 ∷
   rw⁻ 7 q8 ∷
   rw 8 q70 ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q71 ∷
   rw 10 q8 ∷
   rw 11 q12 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = sE 1918 lem-S2-at1023
  q76 : Eqn
  q76 = wE 225 W
  q77 : Eqn
  q77 = sE 1655 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF103-X3
  q78 : Eqn
  q78 = sE 200 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12
  q79 : Eqn
  q79 = sE 201 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12
  q80 : Eqn
  q80 = sE 2137 lem-distribute-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 13 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 30 q75 ∷
   rw 31 q76 ∷
   rw 34 q76 ∷
   rw 37 q76 ∷
   rw⁻ 32 q45 ∷
   rw 33 q46 ∷
   rw⁻ 36 q48 ∷
   rw 37 q46 ∷
   rw 0 q77 ∷
   rw 3 q78 ∷
   rw 4 q77 ∷
   rw 7 q79 ∷
   rw⁻ 0 q80 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = sE 2153 lem-pass-X3-CKd32-X3-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [CKd32] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 3 steps
lem-pass-CKd32-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (CK32⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK32⁻ ∷ []) ⟫ʷ
lem-pass-CKd32-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (CK32⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK32⁻ ∷ [])
  (rw 0 q53 ∷
   rw 1 q81 ∷
   rw 5 q55 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = sE 2155 lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CCZ123

-- pass [CCZ123] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 1 steps
lem-pass-CCZ123-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (CCZ123 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (CCZ123 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q82 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = sE 2150 lem-pass-X3-CK32-X3-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [CK32] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 3 steps
lem-pass-CK32-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (CK32 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CK32-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (CK32 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK32 ∷ [])
  (rw 0 q57 ∷
   rw 1 q83 ∷
   rw 5 q59 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = sE 1665 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF103-X3
  q85 : Eqn
  q85 = sE 224 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS12
  q86 : Eqn
  q86 = sE 225 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CSd12

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 13 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  (rw 32 q75 ∷
   rw 33 q76 ∷
   rw 36 q76 ∷
   rw 39 q76 ∷
   rw⁻ 34 q45 ∷
   rw 35 q46 ∷
   rw⁻ 38 q48 ∷
   rw 39 q46 ∷
   rw 0 q84 ∷
   rw 3 q85 ∷
   rw 4 q84 ∷
   rw 7 q86 ∷
   rw⁻ 0 q80 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = sE 377 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF103-X3
  q88 : Eqn
  q88 = sE 244 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS12
  q89 : Eqn
  q89 = sE 245 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CSd12

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 13 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 30 q75 ∷
   rw 31 q76 ∷
   rw 34 q76 ∷
   rw 37 q76 ∷
   rw⁻ 32 q45 ∷
   rw 33 q46 ∷
   rw⁻ 36 q48 ∷
   rw 37 q46 ∷
   rw 0 q87 ∷
   rw 3 q88 ∷
   rw 4 q87 ∷
   rw 7 q89 ∷
   rw⁻ 0 q80 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = wE 2148 W
  q91 : Eqn
  q91 = wE 2149 W
  q92 : Eqn
  q92 = sE 2147 lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q93 : Eqn
  q93 = sE 2145 lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q94 : Eqn
  q94 = sE 2148 lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q95 : Eqn
  q95 = wE 2150 W

-- pass [X2 CKd23 X2] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 9 steps
lem-pass-X2-CKd23-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (X2 ∷ CK23⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  (rw 0 q90 ∷
   rw 1 q91 ∷
   rw 13 q92 ∷
   rw 10 q93 ∷
   rw 7 q94 ∷
   rw 4 q93 ∷
   rw 1 q92 ∷
   rw 5 q91 ∷
   rw 5 q95 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = wE 2151 W
  q97 : Eqn
  q97 = wE 2152 W
  q98 : Eqn
  q98 = sE 2146 lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q99 : Eqn
  q99 = wE 2153 W

-- pass [X2 CK23 X2] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 9 steps
lem-pass-X2-CK23-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK23-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (X2 ∷ CK23 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ [])
  (rw 0 q96 ∷
   rw 1 q97 ∷
   rw 13 q94 ∷
   rw 10 q98 ∷
   rw 7 q92 ∷
   rw 4 q98 ∷
   rw 1 q94 ∷
   rw 5 q97 ∷
   rw 5 q99 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = wE 2154 W
  q101 : Eqn
  q101 = sE 2081 lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23
  q102 : Eqn
  q102 = wE 2155 W

-- pass [CS32] [X3 TOFF201 CS23 TOFF201 CSd23 X3]: 3 steps
lem-pass-CS32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : ⟪ (CS23 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = derive (CS23 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CS23 ∷ [])
  (rw 0 q100 ∷
   rw 1 q101 ∷
   rw 5 q102 ∷ []) Eq.refl

private
  q103 : Eqn
  q103 = sE 1942 lem-S2-at2013
  q104 : Eqn
  q104 = sE 1664 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3
  q105 : Eqn
  q105 = sE 2138 lem-distribute-Gad⟨t≡2-W≡⟨3⟩-d≡1-e≡1⟩-TOFF203-CS12-TOFF203-CSd12

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 TOFF201 CS23 TOFF201 CSd23 X3]: 13 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 30 q103 ∷
   rw 31 q76 ∷
   rw 34 q76 ∷
   rw 37 q76 ∷
   rw⁻ 32 q45 ∷
   rw 33 q46 ∷
   rw⁻ 36 q48 ∷
   rw 37 q46 ∷
   rw 0 q104 ∷
   rw 3 q88 ∷
   rw 4 q104 ∷
   rw 7 q89 ∷
   rw⁻ 0 q105 ∷ []) Eq.refl

private
  q106 : Eqn
  q106 = wE 1834 W
  q107 : Eqn
  q107 = wE 2156 W
  q108 : Eqn
  q108 = sE 2152 lem-pass-X3-CKd31-X3-vs-TOFF201-CS23-TOFF201-CSd23
  q109 : Eqn
  q109 = wE 2157 W

-- pass [X3 CKd31 X3] [K2 S2 S2 Kd2 TOFF201 CS23 TOFF201 CSd23 K2 Sd2 Sd2 Kd2]: 5 steps
lem-pass-X3-CKd31-X3-vs-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ []) (K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 0 q106 ∷
   rw 0 q107 ∷
   rw 4 q108 ∷
   rw 8 q109 ∷
   rw 12 q106 ∷ []) Eq.refl

private
  q110 : Eqn
  q110 = sE 2156 lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-CCZ123

-- pass [CCZ123] [X3 TOFF201 CS23 TOFF201 CSd23 X3]: 1 steps
lem-pass-CCZ123-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : ⟪ (CCZ123 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = derive (CCZ123 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q110 ∷ []) Eq.refl

private
  q111 : Eqn
  q111 = wE 1534 W
  q112 : Eqn
  q112 = wE 2158 W
  q113 : Eqn
  q113 = sE 2149 lem-pass-X3-CK31-X3-vs-TOFF201-CS23-TOFF201-CSd23
  q114 : Eqn
  q114 = wE 2159 W

-- pass [X3 CK31 X3] [K2 S2 S2 Kd2 TOFF201 CS23 TOFF201 CSd23 K2 Sd2 Sd2 Kd2]: 5 steps
lem-pass-X3-CK31-X3-vs-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2 = derive (X3 ∷ CK31 ∷ X3 ∷ K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ []) (K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 0 q111 ∷
   rw 0 q112 ∷
   rw 4 q113 ∷
   rw 8 q114 ∷
   rw 12 q111 ∷ []) Eq.refl
