{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD606 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D606 (W : Ws) (Sᴰ : SD606) where

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
  lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CK31-X3 : St 1303
  lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CK31-X3 = pickᴰ 0 Sᴰ
  lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CK32-X3 : St 1304
  lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CK32-X3 = pickᴰ 1 Sᴰ
  lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CKd32-X3 : St 1305
  lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CKd32-X3 = pickᴰ 2 Sᴰ
  lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CKd31-X3 : St 1306
  lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CKd31-X3 = pickᴰ 3 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CK10-CS01-CS01-CKd10-X1 : St 491
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CK10-CS01-CS01-CKd10-X1 = pickᴰ 4 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CSd01-CKd10-CS01-CS01-X1 : St 492
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CSd01-CKd10-CS01-CS01-X1 = pickᴰ 5 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CX13-X1 : St 1307
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CX13-X1 = pickᴰ 6 Sᴰ
  lem-pass-CX31-vs-X3-TOFF123-X3 : St 1308
  lem-pass-CX31-vs-X3-TOFF123-X3 = pickᴰ 7 Sᴰ
  lem-pass-CK10-CS01-CS01-CKd10-vs-X1-TOFF312-X1 : St 1309
  lem-pass-CK10-CS01-CS01-CKd10-vs-X1-TOFF312-X1 = pickᴰ 8 Sᴰ
  lem-pass-CSd01-CKd10-CS01-CS01-vs-X1-TOFF312-X1 : St 1310
  lem-pass-CSd01-CKd10-CS01-CS01-vs-X1-TOFF312-X1 = pickᴰ 9 Sᴰ
  lem-pass-TOFF103-vs-X3-TOFF123-X3 : St 1283
  lem-pass-TOFF103-vs-X3-TOFF123-X3 = pickᴰ 10 Sᴰ
  lem-LF-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK12-CS23-CS23-CS23-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-S3-S3-S3-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS02-CS02-CS02-S0-CK02-CS02-CS02-CS02-CS02-CS02-CS02-S1-CK12-at-3 : St 1311
  lem-LF-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK12-CS23-CS23-CS23-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-S3-S3-S3-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS02-CS02-CS02-S0-CK02-CS02-CS02-CS02-CS02-CS02-CS02-S1-CK12-at-3 = pickᴰ 11 Sᴰ
  lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-TOFF213-X3 : St 1312
  lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-TOFF213-X3 = pickᴰ 12 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-X1 : St 1313
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-X1 = pickᴰ 13 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF312-X1 : St 1314
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF312-X1 = pickᴰ 14 Sᴰ
  lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-vs-X1-TOFF312-X1 : St 1315
  lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-vs-X1-TOFF312-X1 = pickᴰ 15 Sᴰ
  lem-pass-X2-X3-TOFF312-X2-X3-vs-X1-TOFF312-X1 : St 1316
  lem-pass-X2-X3-TOFF312-X2-X3-vs-X1-TOFF312-X1 = pickᴰ 16 Sᴰ

private
  q1 : Eqn
  q1 = sE 1311 lem-LF-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK12-CS23-CS23-CS23-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-S3-S3-S3-S3-CK32-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS02-CS02-CS02-S0-CK02-CS02-CS02-CS02-CS02-CS02-CS02-S1-CK12-at-3
  q2 : Eqn
  q2 = wE 225 W
  q3 : Eqn
  q3 = wE 871 W
  q4 : Eqn
  q4 = wE 873 W
  q5 : Eqn
  q5 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q6 : Eqn
  q6 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q7 : Eqn
  q7 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q8 : Eqn
  q8 = wE 1609 W
  q9 : Eqn
  q9 = eqn (ℓ "习丞") (ℓ "丞习") (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q10 : Eqn
  q10 = wE 173 W
  q11 : Eqn
  q11 = wE 389 W
  q12 : Eqn
  q12 = eqn (ℓ "丌义") (ℓ "义丌") (low₁-comm (X) ((CS ↑)))
  q13 : Eqn
  q13 = eqn (ℓ "丌乗") (ℓ "乗丌") (low₁-comm (X) ((CK₁₀ ↑)))
  q14 : Eqn
  q14 = eqn (ℓ "丌乓") (ℓ "乓丌") (low₁-comm (X) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q15 : Eqn
  q15 = eqn (ℓ "丌丶") (ℓ "丶丌") (low₁-comm (X) (CS))
  q16 : Eqn
  q16 = eqn (ℓ "丌为") (ℓ "为丌") (low₁-comm (X) (CK₀₁))
  q17 : Eqn
  q17 = eqn (ℓ "丌与") (ℓ "与丌") (low₁-comm (X) (S))
  q18 : Eqn
  q18 = wE 387 W

-- kk pieces X0 X2 X3 CS02 CS02 CK02 CS02 CX03 CS23 CS23 CS23 CK32 S3 CS2 at 3: 103 steps
lem-kk-pieces-X0-X2-X3-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23-CK32-S3-CS2-at-3 : ⟪ (ℓ "丌丘丞丧丧丫丧丰义义义乗业义义义义义义丰义义乗义为义义义业乗义义义义义义丰义义义义义义义义义义义义义义义义义义业业业业乗义义义义义义义义义丰丧丧丧丈丫丧丧丧丧丧丧与为丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丌丘丞丌丞乡丌丞丘丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丘丞丌丞乡丌丞丘丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞") ⟫ʷ
lem-kk-pieces-X0-X2-X3-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23-CK32-S3-CS2-at-3 = derive (ℓ "丌丘丞丧丧丫丧丰义义义乗业义义义义义义丰义义乗义为义义义业乗义义义义义义丰义义义义义义义义义义义义义义义义义义业业业业乗义义义义义义义义义丰丧丧丧丈丫丧丧丧丧丧丧与为丌丘丞") (ℓ "丌丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丌丘丞丌丞乡丌丞丘丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丘丞丌丞乡丌丞丘丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞")
  (rw 3 q1 ∷
   rw 32 q2 ∷
   rw 33 q3 ∷
   rw 34 q4 ∷
   rw 39 q2 ∷
   rw 40 q3 ∷
   rw 41 q4 ∷
   rw 76 q2 ∷
   rw 77 q3 ∷
   rw 78 q4 ∷
   rw 83 q2 ∷
   rw 84 q3 ∷
   rw 85 q4 ∷
   rw⁻ 32 q5 ∷
   rw⁻ 33 q6 ∷
   rw⁻ 32 q7 ∷
   rw 36 q5 ∷
   re 38 1 (ℓ "乏习乏") ∷
   rw 37 q8 ∷
   rw⁻ 38 q9 ∷
   rw 39 q10 ∷
   re 37 3 (ℓ "乡") ∷
   rw 38 q5 ∷
   rw 39 q11 ∷
   rw⁻ 38 q6 ∷
   rw 40 q7 ∷
   rw 41 q6 ∷
   rw 42 q12 ∷
   rw 43 q12 ∷
   rw 44 q12 ∷
   rw 45 q13 ∷
   rw 46 q12 ∷
   rw 47 q12 ∷
   rw 48 q14 ∷
   rw 49 q15 ∷
   rw 50 q15 ∷
   rw 51 q15 ∷
   rw 52 q15 ∷
   rw 53 q15 ∷
   rw 54 q15 ∷
   rw 55 q16 ∷
   rw 56 q17 ∷
   rw 57 q15 ∷
   rw 58 q15 ∷
   rw 59 q15 ∷
   rw 60 q15 ∷
   rw 61 q15 ∷
   rw 62 q15 ∷
   rw 63 q15 ∷
   rw 64 q15 ∷
   rw 65 q15 ∷
   rw 66 q14 ∷
   rw 67 q15 ∷
   rw 68 q15 ∷
   rw 69 q15 ∷
   rw 70 q16 ∷
   rw 71 q15 ∷
   rw 72 q15 ∷
   rw 73 q6 ∷
   rw 74 q7 ∷
   rw 75 q18 ∷
   rw⁻ 73 q5 ∷
   rw 76 q5 ∷
   re 78 1 (ℓ "乏习乏") ∷
   rw 77 q8 ∷
   rw⁻ 78 q9 ∷
   rw 79 q10 ∷
   re 77 3 (ℓ "乡") ∷
   rw 78 q5 ∷
   rw 79 q11 ∷
   rw⁻ 78 q6 ∷
   rw 80 q7 ∷
   rw 81 q6 ∷
   rw 82 q12 ∷
   rw 83 q12 ∷
   rw 84 q13 ∷
   rw 85 q12 ∷
   rw 86 q13 ∷
   rw 87 q13 ∷
   rw 88 q14 ∷
   rw 89 q16 ∷
   rw 90 q17 ∷
   rw 91 q16 ∷
   rw 92 q17 ∷
   rw 93 q15 ∷
   rw 94 q15 ∷
   rw 95 q15 ∷
   rw 96 q16 ∷
   rw 97 q17 ∷
   rw 98 q15 ∷
   rw 99 q15 ∷
   rw 100 q15 ∷
   rw 101 q15 ∷
   rw 102 q15 ∷
   rw 103 q15 ∷
   rw 104 q14 ∷
   rw 105 q15 ∷
   rw 106 q15 ∷
   rw 107 q16 ∷
   rw 108 q15 ∷
   rw 109 q16 ∷
   rw 110 q16 ∷
   rw 111 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = sE 1303 lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CK31-X3
  q20 : Eqn
  q20 = sE 1304 lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CK32-X3
  q21 : Eqn
  q21 = sE 1312 lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-TOFF213-X3
  q22 : Eqn
  q22 = sE 1305 lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CKd32-X3
  q23 : Eqn
  q23 = sE 1306 lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CKd31-X3

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes III units 1: 5 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-III-units-1 : ⟪ (ℓ "乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乔丞丞乗丞丞乥丞丞乘丞丞乕丞") ⟫ʷ ≈ ⟪ (ℓ "丞乔丞丞乗丞丞乥丞丞乘丞丞乕丞乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-III-units-1 = derive (ℓ "乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乔丞丞乗丞丞乥丞丞乘丞丞乕丞") (ℓ "丞乔丞丞乗丞丞乥丞丞乘丞丞乕丞乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧")
  (rw 0 q19 ∷
   rw 3 q20 ∷
   rw 6 q21 ∷
   rw 9 q22 ∷
   rw 12 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 1 W
  q25 : Eqn
  q25 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q26 : Eqn
  q26 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q27 : Eqn
  q27 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q28 : Eqn
  q28 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q29 : Eqn
  q29 = wE 3 W
  q30 : Eqn
  q30 = wE 196 W
  q31 : Eqn
  q31 = wE 1796 W
  q32 : Eqn
  q32 = sE 1283 lem-pass-TOFF103-vs-X3-TOFF123-X3
  q33 : Eqn
  q33 = sE 1308 lem-pass-CX31-vs-X3-TOFF123-X3
  q34 : Eqn
  q34 = wE 1797 W

-- pass [X0 TOFF103 X0] [X3 TOFF123 X3]: 124 steps
lem-pass-X0-TOFF103-X0-vs-X3-TOFF123-X3 : ⟪ (ℓ "丌乡丌丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞丌乡丌") ⟫ʷ
lem-pass-X0-TOFF103-X0-vs-X3-TOFF123-X3 = derive (ℓ "丌乡丌丞乢丞") (ℓ "丞乢丞丌乡丌")
  (rw 3 q24 ∷
   rw 2 q25 ∷
   re 1 1 (ℓ "乏习乏") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q26 ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q27 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q27 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q26 ∷
   rw⁻ 8 q28 ∷
   rw 9 q29 ∷
   rw 8 q28 ∷
   rw 7 q26 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q29 ∷
   rw 5 q27 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q29 ∷
   rw 3 q27 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q29 ∷
   rw 1 q26 ∷
   rw 2 q30 ∷
   re 2 8 (ℓ "习") ∷
   rw 0 q25 ∷
   rw 1 q31 ∷
   rw 2 q24 ∷
   re 0 3 (ℓ "乓") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q26 ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q27 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q27 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q26 ∷
   rw⁻ 8 q28 ∷
   rw 1 q24 ∷
   rw⁻ 2 q26 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q29 ∷
   rw⁻ 4 q27 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q29 ∷
   rw⁻ 6 q27 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q29 ∷
   rw⁻ 8 q26 ∷
   rw⁻ 9 q28 ∷
   rw 2 q30 ∷
   re 2 8 (ℓ "习") ∷
   re 1 3 (ℓ "乡") ∷
   rw 2 q29 ∷
   rw 1 q32 ∷
   rw 0 q33 ∷
   rw 5 q24 ∷
   re 4 1 (ℓ "乏习乏") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q27 ∷
   rw 9 q24 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q27 ∷
   rw 11 q24 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q26 ∷
   rw⁻ 11 q28 ∷
   rw 12 q29 ∷
   rw 11 q28 ∷
   rw 10 q26 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q29 ∷
   rw 8 q27 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q29 ∷
   rw 6 q27 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q29 ∷
   rw 4 q26 ∷
   rw 5 q30 ∷
   re 5 8 (ℓ "习") ∷
   re 3 1 (ℓ "乏乆乏") ∷
   rw 5 q29 ∷
   rw 4 q34 ∷
   rw⁻ 3 q25 ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q27 ∷
   rw 9 q24 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q27 ∷
   rw 11 q24 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q26 ∷
   rw⁻ 11 q28 ∷
   rw 4 q24 ∷
   rw⁻ 5 q26 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q29 ∷
   rw⁻ 7 q27 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q29 ∷
   rw⁻ 9 q27 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q29 ∷
   rw⁻ 11 q26 ∷
   rw⁻ 12 q28 ∷
   rw 5 q30 ∷
   re 5 8 (ℓ "习") ∷
   re 4 3 (ℓ "乡") ∷
   rw⁻ 5 q25 ∷
   rw 6 q29 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = sE 491 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CK10-CS01-CS01-CKd10-X1
  q36 : Eqn
  q36 = sE 492 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CSd01-CKd10-CS01-CS01-X1
  q37 : Eqn
  q37 = sE 1313 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-X1

-- Bar(SSKSKK;1,3->0) passes factors of X0 X1 X2 CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20 X0 X1 X2: 4 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-factors-of-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒临丠丠丵丒丒両丵丠丠丒丒临与临与丠丠丠临与丠丠丠丠丠丠丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丒临丠丠丵丒") ⟫ʷ ≈ ⟪ (ℓ "丒临丠丠丵丒丒両丵丠丠丒丒临与临与丠丠丠临与丠丠丠丠丠丠丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丒临丠丠丵丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-factors-of-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒临丠丠丵丒丒両丵丠丠丒丒临与临与丠丠丠临与丠丠丠丠丠丠丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丒临丠丠丵丒") (ℓ "丒临丠丠丵丒丒両丵丠丠丒丒临与临与丠丠丠临与丠丠丠丠丠丠丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丒临丠丠丵丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 0 q35 ∷
   rw 6 q36 ∷
   rw 12 q37 ∷
   rw 88 q35 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = sE 1307 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CX13-X1
  q39 : Eqn
  q39 = sE 1314 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF312-X1

-- Bar(SSKSKK;1,3->0) passes factors of X1 X2 X3 TOFF312 X1 X2 X3: 2 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-factors-of-X1-X2-X3-TOFF312-X1-X2-X3 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒乀丒丒乨丒") ⟫ʷ ≈ ⟪ (ℓ "丒乀丒丒乨丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-factors-of-X1-X2-X3-TOFF312-X1-X2-X3 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒乀丒丒乨丒") (ℓ "丒乀丒丒乨丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 0 q38 ∷
   rw 3 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 1798 W
  q41 : Eqn
  q41 = sE 1309 lem-pass-CK10-CS01-CS01-CKd10-vs-X1-TOFF312-X1
  q42 : Eqn
  q42 = sE 1315 lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-vs-X1-TOFF312-X1
  q43 : Eqn
  q43 = sE 1310 lem-pass-CSd01-CKd10-CS01-CS01-vs-X1-TOFF312-X1
  q44 : Eqn
  q44 = wE 1799 W

-- pass [X0 X2 CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20 X0 X2] [X1 TOFF312 X1]: 6 steps
lem-pass-X0-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X2-vs-X1-TOFF312-X1 : ⟪ (ℓ "丌丘丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丌丘丒乨丒") ⟫ʷ ≈ ⟪ (ℓ "丒乨丒丌丘丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丌丘") ⟫ʷ
lem-pass-X0-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X2-vs-X1-TOFF312-X1 = derive (ℓ "丌丘丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丌丘丒乨丒") (ℓ "丒乨丒丌丘丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丌丘")
  (rw 0 q40 ∷
   rw 82 q41 ∷
   rw 8 q42 ∷
   rw 4 q43 ∷
   rw 0 q41 ∷
   rw 3 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 1800 W
  q46 : Eqn
  q46 = wE 1801 W
  q47 : Eqn
  q47 = sE 1316 lem-pass-X2-X3-TOFF312-X2-X3-vs-X1-TOFF312-X1
  q48 : Eqn
  q48 = wE 1802 W
  q49 : Eqn
  q49 = wE 1803 W

-- pass [TOFF312] [X1 X2 X3 TOFF312 X1 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X1-X2-X3-TOFF312-X1-X2-X3 : ⟪ (ℓ "乨丒丘丞乨丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞乨丒丘丞乨") ⟫ʷ
lem-pass-TOFF312-vs-X1-X2-X3-TOFF312-X1-X2-X3 = derive (ℓ "乨丒丘丞乨丒丘丞") (ℓ "丒丘丞乨丒丘丞乨")
  (rw 0 q45 ∷
   rw 4 q46 ∷
   rw⁻ 1 q47 ∷
   rw 0 q48 ∷
   rw 7 q49 ∷ []) Eq.refl
