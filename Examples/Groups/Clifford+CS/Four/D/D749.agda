{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD749 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D749 (W : Ws) (Sᴰ : SD749) where

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
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK31-X3 : St 235
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK31-X3 = pickᴰ 8 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd31-X3 : St 240
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd31-X3 = pickᴰ 9 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-X3 : St 2542
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-X3 = pickᴰ 10 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd13-X3 : St 2543
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd13-X3 = pickᴰ 11 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd31-X3 : St 2631
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd31-X3 = pickᴰ 12 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd13-X3 : St 2632
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd13-X3 = pickᴰ 13 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK31-X3 : St 2633
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK31-X3 = pickᴰ 14 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS13-X3 : St 2634
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS13-X3 = pickᴰ 15 Sᴰ
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1175
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 16 Sᴰ
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1191
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 17 Sᴰ
  lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 1195
  lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 18 Sᴰ
  lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 2523
  lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 19 Sᴰ
  lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 2527
  lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 20 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2552
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 21 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2564
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 22 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 2635
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 23 Sᴰ
  lem-pass-X2-CK23-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : St 2636
  lem-pass-X2-CK23-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = pickᴰ 24 Sᴰ
  lem-pass-X2-CKd23-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : St 2637
  lem-pass-X2-CKd23-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = pickᴰ 25 Sᴰ
  lem-pass-X3-CK32-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : St 2638
  lem-pass-X3-CK32-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = pickᴰ 26 Sᴰ
  lem-pass-X3-CKd32-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : St 2639
  lem-pass-X3-CKd32-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = pickᴰ 27 Sᴰ
  lem-pass-X3-CS31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : St 2640
  lem-pass-X3-CS31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = pickᴰ 28 Sᴰ
  lem-pass-X3-CSd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : St 2641
  lem-pass-X3-CSd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = pickᴰ 29 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 2642
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 30 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 2643
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 31 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2644
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 32 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 2645
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 33 Sᴰ
  lem-pass-X1-CK10-X1-vs-Kd0-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-K0 : St 2646
  lem-pass-X1-CK10-X1-vs-Kd0-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-K0 = pickᴰ 34 Sᴰ
  lem-pass-X1-CK10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2647
  lem-pass-X1-CK10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 35 Sᴰ
  lem-pass-X1-CK10-X1-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2648
  lem-pass-X1-CK10-X1-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 36 Sᴰ
  lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0 : St 2649
  lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0 = pickᴰ 37 Sᴰ
  lem-pass-X1-CSd10-X1-vs-S0-S0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-Sd0-Sd0 : St 2650
  lem-pass-X1-CSd10-X1-vs-S0-S0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-Sd0-Sd0 = pickᴰ 38 Sᴰ
  lem-pass-X2-CK20-X2-vs-S0-S0-K0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Kd0-Sd0-Sd0 : St 2651
  lem-pass-X2-CK20-X2-vs-S0-S0-K0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Kd0-Sd0-Sd0 = pickᴰ 39 Sᴰ
  lem-pass-X2-CKd21-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : St 2652
  lem-pass-X2-CKd21-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = pickᴰ 40 Sᴰ
  lem-pass-X3-CK31-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : St 2653
  lem-pass-X3-CK31-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = pickᴰ 41 Sᴰ
  lem-pass-X3-CK31-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : St 2654
  lem-pass-X3-CK31-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = pickᴰ 42 Sᴰ
  lem-pass-X3-CKd31-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : St 2655
  lem-pass-X3-CKd31-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = pickᴰ 43 Sᴰ
  lem-pass-X3-CKd31-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : St 2656
  lem-pass-X3-CKd31-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = pickᴰ 44 Sᴰ

private
  q1 : Eqn
  q1 = sE 222 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CSd13-X3
  q2 : Eqn
  q2 = sE 215 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CKd31-X3
  q3 : Eqn
  q3 = sE 220 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-X3
  q4 : Eqn
  q4 = sE 2552 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3
  q5 : Eqn
  q5 = sE 214 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CK31-X3

-- Bar(SSSKSS;3,2->0) passes split Gad(t=1, W=(0, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞") (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
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
  q6 = sE 2543 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd13-X3
  q7 : Eqn
  q7 = sE 240 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd31-X3
  q8 : Eqn
  q8 = sE 2542 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-X3
  q9 : Eqn
  q9 = sE 2564 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3
  q10 : Eqn
  q10 = sE 235 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK31-X3

-- Bar(SSKSKK;3,1->0) passes split Gad(t=1, W=(0, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞") (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
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
  q11 = wE 1833 W
  q12 : Eqn
  q12 = wE 1498 W
  q13 : Eqn
  q13 = sE 2527 lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [X2 CKd21 X2] [X0 CS13 TOFF102 CSd13 TOFF102 X0]: 5 steps
lem-pass-X2-CKd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : ⟪ (ℓ "丘么丘丌丽习举习丌") ⟫ʷ ≈ ⟪ (ℓ "丌丽习举习丌丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = derive (ℓ "丘么丘丌丽习举习丌") (ℓ "丌丽习举习丌丘么丘")
  (rw 0 q11 ∷
   rw 1 q12 ∷
   rw 1 q13 ∷
   rw 5 q12 ∷
   rw 5 q11 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q15 : Eqn
  q15 = wE 2301 W
  q16 : Eqn
  q16 = sE 2637 lem-pass-X2-CKd23-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0
  q17 : Eqn
  q17 = wE 2302 W

-- pass [CKd23] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 5 steps
lem-pass-CKd23-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (ℓ "乎丌丘丏丑与与丽习举习丏丏丐与丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘乎") ⟫ʷ
lem-pass-CKd23-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (ℓ "乎丌丘丏丑与与丽习举习丏丏丐与丌丘") (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘乎")
  (rw 1 q14 ∷
   rw 0 q15 ∷
   rw 1 q16 ∷
   rw 15 q17 ∷
   rw⁻ 0 q14 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 2303 W
  q19 : Eqn
  q19 = sE 2636 lem-pass-X2-CK23-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0
  q20 : Eqn
  q20 = wE 2304 W

-- pass [CK23] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 5 steps
lem-pass-CK23-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (ℓ "乍丌丘丏丑与与丽习举习丏丏丐与丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘乍") ⟫ʷ
lem-pass-CK23-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (ℓ "乍丌丘丏丑与与丽习举习丏丏丐与丌丘") (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘乍")
  (rw 1 q14 ∷
   rw 0 q18 ∷
   rw 1 q19 ∷
   rw 15 q20 ∷
   rw⁻ 0 q14 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q22 : Eqn
  q22 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q23 : Eqn
  q23 = wE 2111 W
  q24 : Eqn
  q24 = sE 2640 lem-pass-X3-CS31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2
  q25 : Eqn
  q25 = wE 2112 W

-- pass [CS31] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 7 steps
lem-pass-CS31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "丽丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞丽") ⟫ʷ
lem-pass-CS31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "丽丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞丽")
  (rw 2 q21 ∷
   rw 1 q22 ∷
   rw 0 q23 ∷
   rw 1 q24 ∷
   rw 9 q25 ∷
   rw⁻ 0 q22 ∷
   rw⁻ 1 q21 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 2113 W
  q27 : Eqn
  q27 = sE 2641 lem-pass-X3-CSd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2
  q28 : Eqn
  q28 = wE 2114 W

-- pass [CSd31] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 7 steps
lem-pass-CSd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "举丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞举") ⟫ʷ
lem-pass-CSd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "举丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞举")
  (rw 2 q21 ∷
   rw 1 q22 ∷
   rw 0 q26 ∷
   rw 1 q27 ∷
   rw 9 q28 ∷
   rw⁻ 0 q22 ∷
   rw⁻ 1 q21 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = sE 198 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd13-X3
  q30 : Eqn
  q30 = sE 191 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3
  q31 : Eqn
  q31 = sE 196 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-X3
  q32 : Eqn
  q32 = sE 2635 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3
  q33 : Eqn
  q33 = sE 190 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3

-- Bar(SSKSKK;3,2->0) passes split Gad(t=1, W=(0, 2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞") (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q29 ∷
   rw 3 q30 ∷
   rw 6 q31 ∷
   rw 9 q31 ∷
   rw 12 q32 ∷
   rw 22 q29 ∷
   rw 25 q29 ∷
   rw 28 q33 ∷
   rw 31 q31 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 1674 W
  q35 : Eqn
  q35 = sE 2639 lem-pass-X3-CKd32-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2
  q36 : Eqn
  q36 = wE 1675 W

-- pass [CKd32] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CKd32-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "乘丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乘") ⟫ʷ
lem-pass-CKd32-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "乘丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乘")
  (rw 2 q21 ∷
   rw 1 q22 ∷
   rw 0 q34 ∷
   rw 1 q35 ∷
   rw 17 q36 ∷
   rw⁻ 0 q22 ∷
   rw⁻ 1 q21 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 1409 W
  q38 : Eqn
  q38 = sE 2638 lem-pass-X3-CK32-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2
  q39 : Eqn
  q39 = wE 1410 W

-- pass [CK32] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CK32-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "乗丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乗") ⟫ʷ
lem-pass-CK32-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "乗丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乗")
  (rw 2 q21 ∷
   rw 1 q22 ∷
   rw 0 q37 ∷
   rw 1 q38 ∷
   rw 17 q39 ∷
   rw⁻ 0 q22 ∷
   rw⁻ 1 q21 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = sE 2645 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3

-- Bar(SSSKSS;3,2->0) passes split Gad(t=1, W=(0, 2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞") (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 0 q1 ∷
   rw 3 q2 ∷
   rw 6 q3 ∷
   rw 9 q3 ∷
   rw 12 q40 ∷
   rw 22 q1 ∷
   rw 25 q1 ∷
   rw 28 q5 ∷
   rw 31 q3 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = sE 2642 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3

-- Bar(SSKSKK;3,1->0) passes split Gad(t=1, W=(0, 2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞") (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 0 q6 ∷
   rw 3 q7 ∷
   rw 6 q8 ∷
   rw 9 q8 ∷
   rw 12 q41 ∷
   rw 22 q6 ∷
   rw 25 q6 ∷
   rw 28 q10 ∷
   rw 31 q8 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 2311 W
  q43 : Eqn
  q43 = sE 2648 lem-pass-X1-CK10-X1-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q44 : Eqn
  q44 = eqn (ℓ "下丞") (ℓ "丞下") (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q45 : Eqn
  q45 = wE 1710 W
  q46 : Eqn
  q46 = wE 116 W
  q47 : Eqn
  q47 = wE 2312 W

-- CA CKd10 Gad(t=0, W=(3,), d=1, e=-1): 7 steps
lem-CA-CKd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩ : ⟪ (ℓ "丵丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞下中九丮九上丞丵") ⟫ʷ
lem-CA-CKd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩ = derive (ℓ "丵丞中九丮九丞") (ℓ "丞下中九丮九上丞丵")
  (rw 0 q42 ∷
   rw 1 q43 ∷
   rw 0 q44 ∷
   rw 1 q45 ∷
   rw 6 q46 ∷
   rw 7 q44 ∷
   rw 8 q47 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 2268 W
  q49 : Eqn
  q49 = wE 2313 W
  q50 : Eqn
  q50 = sE 2523 lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q51 : Eqn
  q51 = wE 2314 W

-- pass [X1 CKd10 X1] [X3 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 X3]: 5 steps
lem-pass-X1-CKd10-X1-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3 : ⟪ (ℓ "丒丵丒丞下中九丮九上丞") ⟫ʷ ≈ ⟪ (ℓ "丞下中九丮九上丞丒丵丒") ⟫ʷ
lem-pass-X1-CKd10-X1-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3 = derive (ℓ "丒丵丒丞下中九丮九上丞") (ℓ "丞下中九丮九上丞丒丵丒")
  (rw 0 q48 ∷
   rw 1 q49 ∷
   rw 2 q50 ∷
   rw 6 q51 ∷
   rw 7 q48 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = sE 2647 lem-pass-X1-CK10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q53 : Eqn
  q53 = eqn (ℓ "下丘") (ℓ "丘下") (low₁-comm ((K • iI)) ((X ↑)))

-- CA CKd10 Gad(t=0, W=(2,), d=1, e=-1): 7 steps
lem-CA-CKd10-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ : ⟪ (ℓ "丵丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘下中九丮九上丘丵") ⟫ʷ
lem-CA-CKd10-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ = derive (ℓ "丵丘中九丮九丘") (ℓ "丘下中九丮九上丘丵")
  (rw 0 q42 ∷
   rw 1 q52 ∷
   rw 0 q53 ∷
   rw 1 q45 ∷
   rw 6 q46 ∷
   rw 7 q53 ∷
   rw 8 q47 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = wE 2267 W

-- pass [X1 CKd10 X1] [X2 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 X2]: 5 steps
lem-pass-X1-CKd10-X1-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 : ⟪ (ℓ "丒丵丒丘下中九丮九上丘") ⟫ʷ ≈ ⟪ (ℓ "丘下中九丮九上丘丒丵丒") ⟫ʷ
lem-pass-X1-CKd10-X1-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 = derive (ℓ "丒丵丒丘下中九丮九上丘") (ℓ "丘下中九丮九上丘丒丵丒")
  (rw 0 q54 ∷
   rw 1 q49 ∷
   rw 2 q50 ∷
   rw 6 q51 ∷
   rw 7 q54 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = wE 1940 W
  q56 : Eqn
  q56 = sE 2655 lem-pass-X3-CKd31-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0
  q57 : Eqn
  q57 = wE 1941 W

-- pass [CKd31] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 5 steps
lem-pass-CKd31-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (ℓ "乕丌丞丏丑与与丽习举习丏丏丐与丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞乕") ⟫ʷ
lem-pass-CKd31-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (ℓ "乕丌丞丏丑与与丽习举习丏丏丐与丌丞") (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞乕")
  (rw 1 q22 ∷
   rw 0 q55 ∷
   rw 1 q56 ∷
   rw 15 q57 ∷
   rw⁻ 0 q22 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 1366 W
  q59 : Eqn
  q59 = sE 2653 lem-pass-X3-CK31-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0
  q60 : Eqn
  q60 = wE 1367 W

-- pass [CK31] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 5 steps
lem-pass-CK31-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (ℓ "乔丌丞丏丑与与丽习举习丏丏丐与丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞乔") ⟫ʷ
lem-pass-CK31-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (ℓ "乔丌丞丏丑与与丽习举习丏丏丐与丌丞") (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞乔")
  (rw 1 q22 ∷
   rw 0 q58 ∷
   rw 1 q59 ∷
   rw 15 q60 ∷
   rw⁻ 0 q22 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = sE 2632 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd13-X3
  q62 : Eqn
  q62 = sE 2631 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd31-X3
  q63 : Eqn
  q63 = sE 2634 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS13-X3
  q64 : Eqn
  q64 = sE 2644 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3
  q65 : Eqn
  q65 = sE 2633 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK31-X3

-- Bar(SSSKSS;3,1->0) passes split Gad(t=1, W=(0, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞") (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 0 q61 ∷
   rw 3 q62 ∷
   rw 6 q63 ∷
   rw 9 q63 ∷
   rw 12 q64 ∷
   rw 20 q61 ∷
   rw 23 q61 ∷
   rw 26 q65 ∷
   rw 29 q63 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 1478 W
  q67 : Eqn
  q67 = sE 2652 lem-pass-X2-CKd21-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0
  q68 : Eqn
  q68 = wE 1479 W

-- pass [CKd21] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 5 steps
lem-pass-CKd21-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (ℓ "么丌丘丏丑与与丽习举习丏丏丐与丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘么") ⟫ʷ
lem-pass-CKd21-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (ℓ "么丌丘丏丑与与丽习举习丏丏丐与丌丘") (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘么")
  (rw 1 q14 ∷
   rw 0 q66 ∷
   rw 1 q67 ∷
   rw 15 q68 ∷
   rw⁻ 0 q14 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = wE 1533 W
  q70 : Eqn
  q70 = wE 2421 W
  q71 : Eqn
  q71 = sE 1195 lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q72 : Eqn
  q72 = wE 2422 W

-- pass [X2 CK21 X2] [X0 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0]: 9 steps
lem-pass-X2-CK21-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : ⟪ (ℓ "丘乇丘丌丏丑与与丽习举习丏丏丐与丌") ⟫ʷ ≈ ⟪ (ℓ "丌丏丑与与丽习举习丏丏丐与丌丘乇丘") ⟫ʷ
lem-pass-X2-CK21-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = derive (ℓ "丘乇丘丌丏丑与与丽习举习丏丏丐与丌") (ℓ "丌丏丑与与丽习举习丏丏丐与丌丘乇丘")
  (rw 0 q69 ∷
   rw 1 q70 ∷
   rw 17 q71 ∷
   rw 14 q13 ∷
   rw 11 q71 ∷
   rw 8 q71 ∷
   rw 5 q13 ∷
   rw 9 q72 ∷
   rw 13 q69 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = sE 2656 lem-pass-X3-CKd31-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2

-- pass [CKd31] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CKd31-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "乕丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乕") ⟫ʷ
lem-pass-CKd31-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "乕丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乕")
  (rw 2 q21 ∷
   rw 1 q22 ∷
   rw 0 q55 ∷
   rw 1 q73 ∷
   rw 17 q57 ∷
   rw⁻ 0 q22 ∷
   rw⁻ 1 q21 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = sE 2654 lem-pass-X3-CK31-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2

-- pass [CK31] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CK31-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "乔丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乔") ⟫ʷ
lem-pass-CK31-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "乔丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乔")
  (rw 2 q21 ∷
   rw 1 q22 ∷
   rw 0 q58 ∷
   rw 1 q74 ∷
   rw 17 q60 ∷
   rw⁻ 0 q22 ∷
   rw⁻ 1 q21 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = sE 2643 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3

-- Bar(SSSKSS;3,1->0) passes split Gad(t=1, W=(0, 2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞") (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 0 q61 ∷
   rw 3 q62 ∷
   rw 6 q63 ∷
   rw 9 q63 ∷
   rw 12 q75 ∷
   rw 22 q61 ∷
   rw 25 q61 ∷
   rw 28 q65 ∷
   rw 31 q63 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 2439 W
  q77 : Eqn
  q77 = sE 1175 lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q78 : Eqn
  q78 = wE 2440 W

-- pass [X1 CS10 X1] [S0 Kd0 Sd0 CS03 TOFF012 CSd03 TOFF012 S0 K0 Sd0]: 5 steps
lem-pass-X1-CS10-X1-vs-S0-Kd0-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-K0-Sd0 : ⟪ (ℓ "丒丠丒丈下三中九丮九丈上三") ⟫ʷ ≈ ⟪ (ℓ "丈下三中九丮九丈上三丒丠丒") ⟫ʷ
lem-pass-X1-CS10-X1-vs-S0-Kd0-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-K0-Sd0 = derive (ℓ "丒丠丒丈下三中九丮九丈上三") (ℓ "丈下三中九丮九丈上三丒丠丒")
  (rw 0 q76 ∷
   rw 9 q77 ∷
   rw 6 q77 ∷
   rw 3 q50 ∷
   rw 7 q78 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = sE 2646 lem-pass-X1-CK10-X1-vs-Kd0-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-K0
  q80 : Eqn
  q80 = wE 2441 W
  q81 : Eqn
  q81 = wE 2442 W

-- CA CKd10 Gad(t=0, W=(), d=KdSd, e=-1): 5 steps
lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡KdSd-e≡-1⟩ : ⟪ (ℓ "丵下三中九丮九丈上") ⟫ʷ ≈ ⟪ (ℓ "三下下中九丮九上上丈丵") ⟫ʷ
lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡KdSd-e≡-1⟩ = derive (ℓ "丵下三中九丮九丈上") (ℓ "三下下中九丮九上上丈丵")
  (rw 0 q42 ∷
   rw 1 q79 ∷
   rw 0 q80 ∷
   rw 7 q81 ∷
   rw 10 q47 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 2443 W
  q83 : Eqn
  q83 = sE 1191 lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q84 : Eqn
  q84 = wE 2444 W

-- pass [X1 CS10 X1] [Kd0 Kd0 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 K0 K0]: 5 steps
lem-pass-X1-CS10-X1-vs-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0 : ⟪ (ℓ "丒丠丒下下下中九丮九上上上") ⟫ʷ ≈ ⟪ (ℓ "下下下中九丮九上上上丒丠丒") ⟫ʷ
lem-pass-X1-CS10-X1-vs-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0 = derive (ℓ "丒丠丒下下下中九丮九上上上") (ℓ "下下下中九丮九上上上丒丠丒")
  (rw 0 q82 ∷
   rw 9 q83 ∷
   rw 6 q50 ∷
   rw 3 q83 ∷
   rw 7 q84 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 2445 W
  q86 : Eqn
  q86 = wE 2446 W

-- pass [X1 CKd10 X1] [Sd0 Kd0 Kd0 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 K0 K0 S0]: 7 steps
lem-pass-X1-CKd10-X1-vs-Sd0-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0-S0 : ⟪ (ℓ "丒丵丒三下下下中九丮九上上上丈") ⟫ʷ ≈ ⟪ (ℓ "三下下下中九丮九上上上丈丒丵丒") ⟫ʷ
lem-pass-X1-CKd10-X1-vs-Sd0-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0-S0 = derive (ℓ "丒丵丒三下下下中九丮九上上上丈") (ℓ "三下下下中九丮九上上上丈丒丵丒")
  (rw 0 q85 ∷
   rw 16 q50 ∷
   rw 13 q77 ∷
   rw 10 q77 ∷
   rw 7 q50 ∷
   rw 4 q83 ∷
   rw 8 q86 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = wE 1819 W
  q88 : Eqn
  q88 = sE 2649 lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0
  q89 : Eqn
  q89 = wE 2447 W
  q90 : Eqn
  q90 = wE 2448 W
  q91 : Eqn
  q91 = wE 1820 W

-- CA CS10 Gad(t=0, W=(), d=SKdS, e=-1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SKdS-e≡-1⟩ : ⟪ (ℓ "丠丈下丈中九丮九三上三") ⟫ʷ ≈ ⟪ (ℓ "丈丈下丈中九丮九三上三三丠") ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SKdS-e≡-1⟩ = derive (ℓ "丠丈下丈中九丮九三上三") (ℓ "丈丈下丈中九丮九三上三三丠")
  (rw 0 q87 ∷
   rw 1 q88 ∷
   rw 0 q89 ∷
   rw 8 q90 ∷
   rw 12 q91 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = wE 1709 W
  q93 : Eqn
  q93 = sE 2651 lem-pass-X2-CK20-X2-vs-S0-S0-K0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Kd0-Sd0-Sd0
  q94 : Eqn
  q94 = wE 2449 W
  q95 : Eqn
  q95 = wE 2450 W
  q96 : Eqn
  q96 = wE 1711 W

-- CA CKd20 Gad(t=0, W=(), d=SSKS, e=-1): 5 steps
lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SSKS-e≡-1⟩ : ⟪ (ℓ "久丈丈上丈中九丮九三下三三") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈下中九丮九上三三上丈久") ⟫ʷ
lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SSKS-e≡-1⟩ = derive (ℓ "久丈丈上丈中九丮九三下三三") (ℓ "三下丈丈下中九丮九上三三上丈久")
  (rw 0 q92 ∷
   rw 1 q93 ∷
   rw 0 q94 ∷
   rw 9 q95 ∷
   rw 14 q96 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = wE 2451 W
  q98 : Eqn
  q98 = wE 2452 W

-- pass [X1 CS10 X1] [Sd0 Kd0 S0 S0 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 Sd0 Sd0 K0 S0]: 5 steps
lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丒丠丒三下丈丈下中九丮九上三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈下中九丮九上三三上丈丒丠丒") ⟫ʷ
lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 = derive (ℓ "丒丠丒三下丈丈下中九丮九上三三上丈") (ℓ "三下丈丈下中九丮九上三三上丈丒丠丒")
  (rw 0 q97 ∷
   rw 11 q50 ∷
   rw 8 q50 ∷
   rw 5 q83 ∷
   rw 9 q98 ∷ []) Eq.refl

private
  q99 : Eqn
  q99 = wE 2453 W
  q100 : Eqn
  q100 = wE 2454 W

-- pass [X1 CK10 X1] [S0 S0 Kd0 S0 S0 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 Sd0 Sd0 K0 Sd0 Sd0]: 5 steps
lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-Sd0-Sd0 : ⟪ (ℓ "丒临丒丈丈下丈丈下中九丮九上三三上三三") ⟫ʷ ≈ ⟪ (ℓ "丈丈下丈丈下中九丮九上三三上三三丒临丒") ⟫ʷ
lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-Sd0-Sd0 = derive (ℓ "丒临丒丈丈下丈丈下中九丮九上三三上三三") (ℓ "丈丈下丈丈下中九丮九上三三上三三丒临丒")
  (rw 0 q99 ∷
   rw 12 q50 ∷
   rw 9 q50 ∷
   rw 6 q50 ∷
   rw 10 q100 ∷ []) Eq.refl

private
  q101 : Eqn
  q101 = sE 2650 lem-pass-X1-CSd10-X1-vs-S0-S0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-Sd0-Sd0
  q102 : Eqn
  q102 = wE 2455 W
  q103 : Eqn
  q103 = wE 2456 W

-- CA CS10 Gad(t=0, W=(), d=SSKSS, e=-1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSKSS-e≡-1⟩ : ⟪ (ℓ "丠丈丈上丈丈中九丮九三三下三三") ⟫ʷ ≈ ⟪ (ℓ "三上丈丈中九丮九三三下丈丠") ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSKSS-e≡-1⟩ = derive (ℓ "丠丈丈上丈丈中九丮九三三下三三") (ℓ "三上丈丈中九丮九三三下丈丠")
  (rw 0 q87 ∷
   rw 1 q101 ∷
   rw 0 q102 ∷
   rw 8 q103 ∷
   rw 12 q91 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = wE 2457 W
  q105 : Eqn
  q105 = wE 2458 W

-- pass [X1 CS10 X1] [S0 K0 Sd0 K0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Kd0 S0 Kd0 Sd0]: 5 steps
lem-pass-X1-CS10-X1-vs-S0-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0-Sd0 : ⟪ (ℓ "丒丠丒丈上三上上中九丮九下下丈下三") ⟫ʷ ≈ ⟪ (ℓ "丈上三上上中九丮九下下丈下三丒丠丒") ⟫ʷ
lem-pass-X1-CS10-X1-vs-S0-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0-Sd0 = derive (ℓ "丒丠丒丈上三上上中九丮九下下丈下三") (ℓ "丈上三上上中九丮九下下丈下三丒丠丒")
  (rw 0 q104 ∷
   rw 11 q77 ∷
   rw 8 q77 ∷
   rw 5 q50 ∷
   rw 9 q105 ∷ []) Eq.refl
