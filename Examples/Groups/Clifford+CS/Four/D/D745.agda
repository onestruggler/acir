{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD745 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D745 (W : Ws) (Sᴰ : SD745) where

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
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3 : St 190
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3 : St 191
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3 = pickᴰ 1 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-X3 : St 196
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-X3 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd13-X3 : St 198
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd13-X3 = pickᴰ 3 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CK31-X3 : St 214
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CK31-X3 = pickᴰ 4 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CKd31-X3 : St 215
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CKd31-X3 = pickᴰ 5 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-X3 : St 220
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-X3 = pickᴰ 6 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CSd13-X3 : St 222
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CSd13-X3 = pickᴰ 7 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK32-X3 : St 226
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK32-X3 = pickᴰ 8 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd32-X3 : St 232
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd32-X3 = pickᴰ 9 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK31-X3 : St 235
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK31-X3 = pickᴰ 10 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd31-X3 : St 240
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd31-X3 = pickᴰ 11 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-X3 : St 241
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-X3 = pickᴰ 12 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd23-X3 : St 243
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd23-X3 = pickᴰ 13 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-X3 : St 389
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-X3 = pickᴰ 14 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd32-X3 : St 390
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd32-X3 = pickᴰ 15 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-X3 : St 392
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-X3 = pickᴰ 16 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd23-X3 : St 395
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd23-X3 = pickᴰ 17 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3 : St 400
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3 = pickᴰ 18 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd32-X3 : St 407
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd32-X3 = pickᴰ 19 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-X3 : St 2542
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-X3 = pickᴰ 20 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd13-X3 : St 2543
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd13-X3 = pickᴰ 21 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3 : St 2374
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3 = pickᴰ 22 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3 : St 2375
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3 = pickᴰ 23 Sᴰ
  lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2205
  lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 24 Sᴰ
  lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 1195
  lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 25 Sᴰ
  lem-CA-CS10-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡-1⟩ : St 2544
  lem-CA-CS10-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡-1⟩ = pickᴰ 26 Sᴰ
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩ : St 2545
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩ = pickᴰ 27 Sᴰ
  lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 2523
  lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 28 Sᴰ
  lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 2527
  lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 29 Sᴰ
  lem-pass-CKd30-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3 : St 2538
  lem-pass-CKd30-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3 = pickᴰ 30 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : St 2546
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = pickᴰ 31 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : St 2547
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = pickᴰ 32 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2548
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 33 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : St 2549
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = pickᴰ 34 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : St 2550
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = pickᴰ 35 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : St 2551
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = pickᴰ 36 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2552
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 37 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : St 2553
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = pickᴰ 38 Sᴰ
  lem-pass-X1-CK10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2554
  lem-pass-X1-CK10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 39 Sᴰ
  lem-pass-X2-CK23-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : St 2555
  lem-pass-X2-CK23-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = pickᴰ 40 Sᴰ
  lem-pass-X2-CKd21-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : St 2556
  lem-pass-X2-CKd21-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = pickᴰ 41 Sᴰ
  lem-pass-X2-CKd23-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : St 2557
  lem-pass-X2-CKd23-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = pickᴰ 42 Sᴰ
  lem-pass-X3-CK31-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 : St 2558
  lem-pass-X3-CK31-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 = pickᴰ 43 Sᴰ
  lem-pass-X3-CK32-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 : St 2559
  lem-pass-X3-CK32-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 = pickᴰ 44 Sᴰ
  lem-pass-X3-CK32-X3-vs-X0-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0 : St 2560
  lem-pass-X3-CK32-X3-vs-X0-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0 = pickᴰ 45 Sᴰ
  lem-pass-X3-CKd31-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 : St 2561
  lem-pass-X3-CKd31-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 = pickᴰ 46 Sᴰ
  lem-pass-X3-CKd32-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 : St 2562
  lem-pass-X3-CKd32-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 = pickᴰ 47 Sᴰ
  lem-pass-X3-CKd32-X3-vs-X0-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0 : St 2563
  lem-pass-X3-CKd32-X3-vs-X0-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0 = pickᴰ 48 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2564
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 49 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : St 2565
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = pickᴰ 50 Sᴰ
  lem-pass-X2-CK21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2566
  lem-pass-X2-CK21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 51 Sᴰ
  lem-pass-X2-CK23-X2-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : St 2567
  lem-pass-X2-CK23-X2-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = pickᴰ 52 Sᴰ
  lem-pass-X2-CKd20-X2-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3 : St 2568
  lem-pass-X2-CKd20-X2-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3 = pickᴰ 53 Sᴰ
  lem-pass-X2-CKd23-X2-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : St 2569
  lem-pass-X2-CKd23-X2-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = pickᴰ 54 Sᴰ
  lem-pass-X3-CK31-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 : St 2570
  lem-pass-X3-CK31-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 = pickᴰ 55 Sᴰ
  lem-pass-X3-CKd31-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 : St 2571
  lem-pass-X3-CKd31-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 = pickᴰ 56 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q6 : Eqn
  q6 = wE 2299 W
  q7 : Eqn
  q7 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q8 : Eqn
  q8 = sE 2545 lem-CA-CSd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩
  q9 : Eqn
  q9 = sE 2538 lem-pass-CKd30-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3
  q10 : Eqn
  q10 = sE 2544 lem-CA-CS10-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡-1⟩
  q11 : Eqn
  q11 = sE 2205 lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q12 : Eqn
  q12 = wE 2300 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 96 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中九丮九丞") (ℓ "丞中九丮九丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q1 ∷
   rw 28 q2 ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q4 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q3 ∷
   rw 15 q5 ∷
   rw 14 q2 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw 10 q5 ∷
   rw 9 q2 ∷
   rw 8 q5 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q4 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q4 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q4 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q4 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q4 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q4 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q6 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "乑") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乒") ∷
   rw⁻ 3 q7 ∷
   rw 4 q4 ∷
   rw 3 q8 ∷
   rw 2 q9 ∷
   rw 1 q10 ∷
   rw 0 q11 ∷
   rw 10 q1 ∷
   rw 9 q7 ∷
   re 8 1 (ℓ "乏久乏") ∷
   rw 10 q4 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw 8 q4 ∷
   rw 7 q12 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乑") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乑") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "乑") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "乓") ∷
   rw⁻ 13 q2 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q2 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q3 ∷
   rw⁻ 18 q3 ∷
   rw⁻ 19 q3 ∷
   rw⁻ 20 q2 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q3 ∷
   rw⁻ 23 q3 ∷
   rw⁻ 24 q3 ∷
   rw⁻ 25 q3 ∷
   rw⁻ 26 q3 ∷
   rw⁻ 27 q3 ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乓") ∷
   rw⁻ 29 q3 ∷
   rw⁻ 30 q3 ∷
   rw⁻ 31 q2 ∷
   rw⁻ 32 q3 ∷
   rw⁻ 33 q2 ∷
   rw⁻ 34 q2 ∷
   rw 35 q4 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = sE 196 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-X3
  q14 : Eqn
  q14 = sE 190 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3
  q15 : Eqn
  q15 = sE 2549 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3
  q16 : Eqn
  q16 = sE 191 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3
  q17 : Eqn
  q17 = sE 198 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd13-X3

-- Bar(SSKSKK;3,2->0) passes split Gad(t=1, W=(3,), d=SK, e=-1): 5 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞") (ℓ "丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q13 ∷
   rw 3 q14 ∷
   rw 6 q15 ∷
   rw 12 q16 ∷
   rw 15 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 1674 W
  q19 : Eqn
  q19 = sE 2562 lem-pass-X3-CKd32-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1
  q20 : Eqn
  q20 = wE 1675 W

-- pass [CKd32] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 3 steps
lem-pass-CKd32-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (ℓ "乘丞与丐丽习举习丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐丽习举习丑丏丞乘") ⟫ʷ
lem-pass-CKd32-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (ℓ "乘丞与丐丽习举习丑丏丞") (ℓ "丞与丐丽习举习丑丏丞乘")
  (rw 0 q18 ∷
   rw 1 q19 ∷
   rw 9 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 1409 W
  q22 : Eqn
  q22 = sE 2559 lem-pass-X3-CK32-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1
  q23 : Eqn
  q23 = wE 1410 W

-- pass [CK32] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 3 steps
lem-pass-CK32-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (ℓ "乗丞与丐丽习举习丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐丽习举习丑丏丞乗") ⟫ʷ
lem-pass-CK32-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (ℓ "乗丞与丐丽习举习丑丏丞") (ℓ "丞与丐丽习举习丑丏丞乗")
  (rw 0 q21 ∷
   rw 1 q22 ∷
   rw 9 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = sE 220 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-X3
  q25 : Eqn
  q25 = sE 214 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CK31-X3
  q26 : Eqn
  q26 = sE 2553 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3
  q27 : Eqn
  q27 = sE 215 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CKd31-X3
  q28 : Eqn
  q28 = sE 222 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CSd13-X3

-- Bar(SSSKSS;3,2->0) passes split Gad(t=1, W=(3,), d=SK, e=-1): 5 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞") (ℓ "丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 0 q24 ∷
   rw 3 q25 ∷
   rw 6 q26 ∷
   rw 12 q27 ∷
   rw 15 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = sE 2542 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-X3
  q30 : Eqn
  q30 = sE 235 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK31-X3
  q31 : Eqn
  q31 = sE 2546 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3
  q32 : Eqn
  q32 = sE 240 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd31-X3
  q33 : Eqn
  q33 = sE 2543 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd13-X3

-- Bar(SSKSKK;3,1->0) passes split Gad(t=1, W=(3,), d=SK, e=-1): 5 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩ = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞") (ℓ "丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 0 q29 ∷
   rw 3 q30 ∷
   rw 6 q31 ∷
   rw 12 q32 ∷
   rw 15 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 2301 W
  q35 : Eqn
  q35 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q36 : Eqn
  q36 = sE 2557 lem-pass-X2-CKd23-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3
  q37 : Eqn
  q37 = wE 2302 W

-- pass [CKd23] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CKd23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (ℓ "乎丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞乎") ⟫ʷ
lem-pass-CKd23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (ℓ "乎丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丞与丐丽习举习丑丏丘丞乎")
  (rw 0 q34 ∷
   rw 13 q35 ∷
   rw 1 q36 ∷
   rw 11 q37 ∷
   rw⁻ 10 q35 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = wE 2303 W
  q39 : Eqn
  q39 = sE 2555 lem-pass-X2-CK23-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3
  q40 : Eqn
  q40 = wE 2304 W

-- pass [CK23] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CK23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (ℓ "乍丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞乍") ⟫ʷ
lem-pass-CK23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (ℓ "乍丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丞与丐丽习举习丑丏丘丞乍")
  (rw 0 q38 ∷
   rw 13 q35 ∷
   rw 1 q39 ∷
   rw 11 q40 ∷
   rw⁻ 10 q35 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = sE 243 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd23-X3
  q42 : Eqn
  q42 = sE 232 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd32-X3
  q43 : Eqn
  q43 = sE 241 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-X3
  q44 : Eqn
  q44 = sE 2547 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3
  q45 : Eqn
  q45 = sE 226 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK32-X3

-- Bar(SSKSKK;3,1->0) passes split Gad(t=2, W=(3,), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞") (ℓ "丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 0 q41 ∷
   rw 3 q42 ∷
   rw 6 q43 ∷
   rw 9 q43 ∷
   rw 12 q44 ∷
   rw 18 q41 ∷
   rw 21 q41 ∷
   rw 24 q45 ∷
   rw 27 q43 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 1940 W
  q47 : Eqn
  q47 = sE 2561 lem-pass-X3-CKd31-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2
  q48 : Eqn
  q48 = wE 1941 W

-- pass [CKd31] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 3 steps
lem-pass-CKd31-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (ℓ "乕丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ ≈ ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞乕") ⟫ʷ
lem-pass-CKd31-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (ℓ "乕丞丕丗且且义乣乊乣丕丕世且丞") (ℓ "丞丕丗且且义乣乊乣丕丕世且丞乕")
  (rw 0 q46 ∷
   rw 1 q47 ∷
   rw 13 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 1366 W
  q50 : Eqn
  q50 = sE 2558 lem-pass-X3-CK31-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2
  q51 : Eqn
  q51 = wE 1367 W

-- pass [CK31] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 3 steps
lem-pass-CK31-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (ℓ "乔丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ ≈ ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞乔") ⟫ʷ
lem-pass-CK31-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (ℓ "乔丞丕丗且且义乣乊乣丕丕世且丞") (ℓ "丞丕丗且且义乣乊乣丕丕世且丞乔")
  (rw 0 q49 ∷
   rw 1 q50 ∷
   rw 13 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = sE 395 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd23-X3
  q53 : Eqn
  q53 = sE 390 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd32-X3
  q54 : Eqn
  q54 = sE 392 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-X3
  q55 : Eqn
  q55 = sE 2551 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3
  q56 : Eqn
  q56 = sE 389 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-X3

-- Bar(SSSKSS;3,1->0) passes split Gad(t=2, W=(3,), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞") (ℓ "丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 0 q52 ∷
   rw 3 q53 ∷
   rw 6 q54 ∷
   rw 9 q54 ∷
   rw 12 q55 ∷
   rw 18 q52 ∷
   rw 21 q52 ∷
   rw 24 q56 ∷
   rw 27 q54 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = sE 2375 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3
  q58 : Eqn
  q58 = sE 407 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd32-X3
  q59 : Eqn
  q59 = sE 2374 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3
  q60 : Eqn
  q60 = sE 2550 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3
  q61 : Eqn
  q61 = sE 400 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3

-- Bar(SSKSKK;3,2->0) passes split Gad(t=2, W=(3,), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞") (ℓ "丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q57 ∷
   rw 3 q58 ∷
   rw 6 q59 ∷
   rw 9 q59 ∷
   rw 12 q60 ∷
   rw 18 q57 ∷
   rw 21 q57 ∷
   rw 24 q61 ∷
   rw 27 q59 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 2205 W
  q63 : Eqn
  q63 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q64 : Eqn
  q64 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q65 : Eqn
  q65 = sE 2554 lem-pass-X1-CK10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q66 : Eqn
  q66 = wE 2206 W

-- pass [CK10] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 7 steps
lem-pass-CK10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (ℓ "临丒丘丞中九丮九丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞中九丮九丒丘丞临") ⟫ʷ
lem-pass-CK10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (ℓ "临丒丘丞中九丮九丒丘丞") (ℓ "丒丘丞中九丮九丒丘丞临")
  (rw 0 q62 ∷
   rw 10 q63 ∷
   rw 11 q64 ∷
   rw 1 q65 ∷
   rw 9 q66 ∷
   rw⁻ 8 q64 ∷
   rw⁻ 7 q63 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 1478 W
  q68 : Eqn
  q68 = sE 2556 lem-pass-X2-CKd21-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3
  q69 : Eqn
  q69 = wE 1479 W

-- pass [CKd21] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (ℓ "么丘丞丏丑与与丽习举习丏丏丐与丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞么") ⟫ʷ
lem-pass-CKd21-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (ℓ "么丘丞丏丑与与丽习举习丏丏丐与丘丞") (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞么")
  (rw 0 q67 ∷
   rw 17 q35 ∷
   rw 1 q68 ∷
   rw 15 q69 ∷
   rw⁻ 14 q35 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 1495 W
  q71 : Eqn
  q71 = wE 2421 W
  q72 : Eqn
  q72 = sE 1195 lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q73 : Eqn
  q73 = sE 2527 lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q74 : Eqn
  q74 = wE 2422 W

-- pass [X2 CK21 X2] [X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X3]: 9 steps
lem-pass-X2-CK21-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : ⟪ (ℓ "丘乇丘丞丏丑与与丽习举习丏丏丐与丞") ⟫ʷ ≈ ⟪ (ℓ "丞丏丑与与丽习举习丏丏丐与丞丘乇丘") ⟫ʷ
lem-pass-X2-CK21-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = derive (ℓ "丘乇丘丞丏丑与与丽习举习丏丏丐与丞") (ℓ "丞丏丑与与丽习举习丏丏丐与丞丘乇丘")
  (rw 0 q70 ∷
   rw 1 q71 ∷
   rw 17 q72 ∷
   rw 14 q73 ∷
   rw 11 q72 ∷
   rw 8 q72 ∷
   rw 5 q73 ∷
   rw 9 q74 ∷
   rw 13 q70 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = sE 2548 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3

-- Bar(SSKSKK;3,2->0) passes split Gad(t=1, W=(0, 3), d=SK, e=-1): 5 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞") (ℓ "丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q13 ∷
   rw 3 q14 ∷
   rw 6 q75 ∷
   rw 14 q16 ∷
   rw 17 q17 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q77 : Eqn
  q77 = sE 2563 lem-pass-X3-CKd32-X3-vs-X0-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0

-- pass [CKd32] [X0 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X3]: 5 steps
lem-pass-CKd32-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : ⟪ (ℓ "乘丌丞与丐丽习举习丑丏丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞与丐丽习举习丑丏丌丞乘") ⟫ʷ
lem-pass-CKd32-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = derive (ℓ "乘丌丞与丐丽习举习丑丏丌丞") (ℓ "丌丞与丐丽习举习丑丏丌丞乘")
  (rw 1 q76 ∷
   rw 0 q18 ∷
   rw 1 q77 ∷
   rw 11 q20 ∷
   rw⁻ 0 q76 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = sE 2560 lem-pass-X3-CK32-X3-vs-X0-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0

-- pass [CK32] [X0 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X3]: 5 steps
lem-pass-CK32-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : ⟪ (ℓ "乗丌丞与丐丽习举习丑丏丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞与丐丽习举习丑丏丌丞乗") ⟫ʷ
lem-pass-CK32-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = derive (ℓ "乗丌丞与丐丽习举习丑丏丌丞") (ℓ "丌丞与丐丽习举习丑丏丌丞乗")
  (rw 1 q76 ∷
   rw 0 q21 ∷
   rw 1 q78 ∷
   rw 11 q23 ∷
   rw⁻ 0 q76 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = sE 2552 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3

-- Bar(SSSKSS;3,2->0) passes split Gad(t=1, W=(0, 3), d=SK, e=-1): 5 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞") (ℓ "丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 0 q24 ∷
   rw 3 q25 ∷
   rw 6 q79 ∷
   rw 14 q27 ∷
   rw 17 q28 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = sE 2564 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3

-- Bar(SSKSKK;3,1->0) passes split Gad(t=1, W=(0, 3), d=SK, e=-1): 5 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞") (ℓ "丞丽丞丞乔丞丌丞丽习举习丌丞丞乕丞丞举丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 0 q29 ∷
   rw 3 q30 ∷
   rw 6 q80 ∷
   rw 14 q32 ∷
   rw 17 q33 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 1464 W
  q82 : Eqn
  q82 = sE 2568 lem-pass-X2-CKd20-X2-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3
  q83 : Eqn
  q83 = wE 1465 W

-- pass [CKd20] [X2 X3 Sd0 CS03 TOFF012 CSd03 TOFF012 S0 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3 : ⟪ (ℓ "久丘丞三中九丮九丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三中九丮九丈丘丞久") ⟫ʷ
lem-pass-CKd20-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3 = derive (ℓ "久丘丞三中九丮九丈丘丞") (ℓ "丘丞三中九丮九丈丘丞久")
  (rw 0 q81 ∷
   rw 11 q35 ∷
   rw 1 q82 ∷
   rw 9 q83 ∷
   rw⁻ 8 q35 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = wE 2311 W
  q85 : Eqn
  q85 = eqn (ℓ "下丘") (ℓ "丘下") (low₁-comm ((K • iI)) ((X ↑)))
  q86 : Eqn
  q86 = eqn (ℓ "下丞") (ℓ "丞下") (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q87 : Eqn
  q87 = wE 1710 W
  q88 : Eqn
  q88 = wE 116 W
  q89 : Eqn
  q89 = wE 2312 W

-- CA CKd10 Gad(t=0, W=(2, 3), d=1, e=-1): 9 steps
lem-CA-CKd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡-1⟩ : ⟪ (ℓ "丵丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞下中九丮九上丘丞丵") ⟫ʷ
lem-CA-CKd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡-1⟩ = derive (ℓ "丵丘丞中九丮九丘丞") (ℓ "丘丞下中九丮九上丘丞丵")
  (rw 0 q84 ∷
   rw 1 q65 ∷
   rw 0 q85 ∷
   rw 1 q86 ∷
   rw 2 q87 ∷
   rw 7 q88 ∷
   rw 8 q85 ∷
   rw 9 q86 ∷
   rw 10 q89 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = wE 2267 W
  q91 : Eqn
  q91 = wE 2268 W
  q92 : Eqn
  q92 = wE 2313 W
  q93 : Eqn
  q93 = sE 2523 lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q94 : Eqn
  q94 = wE 2314 W

-- pass [X1 CKd10 X1] [X2 X3 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 X2 X3]: 7 steps
lem-pass-X1-CKd10-X1-vs-X2-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2-X3 : ⟪ (ℓ "丒丵丒丘丞下中九丮九上丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞下中九丮九上丘丞丒丵丒") ⟫ʷ
lem-pass-X1-CKd10-X1-vs-X2-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2-X3 = derive (ℓ "丒丵丒丘丞下中九丮九上丘丞") (ℓ "丘丞下中九丮九上丘丞丒丵丒")
  (rw 0 q90 ∷
   rw 1 q91 ∷
   rw 2 q92 ∷
   rw 3 q93 ∷
   rw 7 q94 ∷
   rw 8 q90 ∷
   rw 9 q91 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q96 : Eqn
  q96 = wE 1476 W
  q97 : Eqn
  q97 = sE 2566 lem-pass-X2-CK21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3
  q98 : Eqn
  q98 = wE 1477 W

-- pass [CK21] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 7 steps
lem-pass-CK21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "乇丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞乇") ⟫ʷ
lem-pass-CK21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "乇丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞乇")
  (rw 1 q95 ∷
   rw 0 q96 ∷
   rw 11 q35 ∷
   rw 1 q97 ∷
   rw 9 q98 ∷
   rw⁻ 0 q95 ∷
   rw⁻ 8 q35 ∷ []) Eq.refl

private
  q99 : Eqn
  q99 = sE 2569 lem-pass-X2-CKd23-X2-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3

-- pass [CKd23] [X0 X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X2 X3]: 7 steps
lem-pass-CKd23-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 : ⟪ (ℓ "乎丌丘丞与丐丽习举习丑丏丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞乎") ⟫ʷ
lem-pass-CKd23-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 = derive (ℓ "乎丌丘丞与丐丽习举习丑丏丌丘丞") (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞乎")
  (rw 1 q95 ∷
   rw 0 q34 ∷
   rw 15 q35 ∷
   rw 1 q99 ∷
   rw 13 q37 ∷
   rw⁻ 0 q95 ∷
   rw⁻ 12 q35 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = sE 2567 lem-pass-X2-CK23-X2-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3

-- pass [CK23] [X0 X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X2 X3]: 7 steps
lem-pass-CK23-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 : ⟪ (ℓ "乍丌丘丞与丐丽习举习丑丏丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞乍") ⟫ʷ
lem-pass-CK23-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 = derive (ℓ "乍丌丘丞与丐丽习举习丑丏丌丘丞") (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞乍")
  (rw 1 q95 ∷
   rw 0 q38 ∷
   rw 15 q35 ∷
   rw 1 q100 ∷
   rw 13 q40 ∷
   rw⁻ 0 q95 ∷
   rw⁻ 12 q35 ∷ []) Eq.refl

private
  q101 : Eqn
  q101 = sE 2565 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3

-- Bar(SSKSKK;3,1->0) passes split Gad(t=2, W=(0, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞") (ℓ "丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 0 q41 ∷
   rw 3 q42 ∷
   rw 6 q43 ∷
   rw 9 q43 ∷
   rw 12 q101 ∷
   rw 20 q41 ∷
   rw 23 q41 ∷
   rw 26 q45 ∷
   rw 29 q43 ∷ []) Eq.refl

private
  q102 : Eqn
  q102 = sE 2571 lem-pass-X3-CKd31-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0

-- pass [CKd31] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 5 steps
lem-pass-CKd31-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (ℓ "乕丌丞丕丗且且义乣乊乣丕丕世且丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞乕") ⟫ʷ
lem-pass-CKd31-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (ℓ "乕丌丞丕丗且且义乣乊乣丕丕世且丌丞") (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞乕")
  (rw 1 q76 ∷
   rw 0 q46 ∷
   rw 1 q102 ∷
   rw 15 q48 ∷
   rw⁻ 0 q76 ∷ []) Eq.refl

private
  q103 : Eqn
  q103 = sE 2570 lem-pass-X3-CK31-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0

-- pass [CK31] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 5 steps
lem-pass-CK31-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (ℓ "乔丌丞丕丗且且义乣乊乣丕丕世且丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞乔") ⟫ʷ
lem-pass-CK31-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (ℓ "乔丌丞丕丗且且义乣乊乣丕丕世且丌丞") (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞乔")
  (rw 1 q76 ∷
   rw 0 q49 ∷
   rw 1 q103 ∷
   rw 15 q51 ∷
   rw⁻ 0 q76 ∷ []) Eq.refl
