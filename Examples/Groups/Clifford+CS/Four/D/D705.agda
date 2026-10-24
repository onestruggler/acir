{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD705 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D705 (W : Ws) (Sᴰ : SD705) where

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
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 38
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 0 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3 : St 1730
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3 : St 1731
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3 = pickᴰ 2 Sᴰ
  lem-pass-CCZ123-vs-X2-CK21-X2 : St 1969
  lem-pass-CCZ123-vs-X2-CK21-X2 = pickᴰ 3 Sᴰ
  lem-pass-CCZ123-vs-X2-CKd21-X2 : St 1970
  lem-pass-CCZ123-vs-X2-CKd21-X2 = pickᴰ 4 Sᴰ
  lem-pass-CCZ123-vs-X2-CS12-X2 : St 1971
  lem-pass-CCZ123-vs-X2-CS12-X2 = pickᴰ 5 Sᴰ
  lem-pass-CCZ123-vs-X2-CSd12-X2 : St 1972
  lem-pass-CCZ123-vs-X2-CSd12-X2 = pickᴰ 6 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3 : St 1732
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3 = pickᴰ 7 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3 : St 1733
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3 = pickᴰ 8 Sᴰ
  lem-pass-CCZ123-vs-X1-CK10-X1 : St 1973
  lem-pass-CCZ123-vs-X1-CK10-X1 = pickᴰ 9 Sᴰ
  lem-pass-CCZ123-vs-X1-CKd10-X1 : St 1974
  lem-pass-CCZ123-vs-X1-CKd10-X1 = pickᴰ 10 Sᴰ
  lem-pass-CCZ123-vs-X1-CS01-X1 : St 1975
  lem-pass-CCZ123-vs-X1-CS01-X1 = pickᴰ 11 Sᴰ
  lem-pass-CCZ123-vs-X1-CSd01-X1 : St 1976
  lem-pass-CCZ123-vs-X1-CSd01-X1 = pickᴰ 12 Sᴰ
  lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 : St 635
  lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 13 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 841
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 14 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-CS12-CS12-CKd21-X2 : St 1281
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-CS12-CS12-CKd21-X2 = pickᴰ 15 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-CKd21-CS12-CS12-X2 : St 1296
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-CKd21-CS12-CS12-X2 = pickᴰ 16 Sᴰ
  lem-pass-X1-CK13-X1-vs-CS02-TOFF013-CSd02-TOFF013 : St 1977
  lem-pass-X1-CK13-X1-vs-CS02-TOFF013-CSd02-TOFF013 = pickᴰ 17 Sᴰ
  lem-pass-X1-CKd13-X1-vs-CS02-TOFF013-CSd02-TOFF013 : St 1978
  lem-pass-X1-CKd13-X1-vs-CS02-TOFF013-CSd02-TOFF013 = pickᴰ 18 Sᴰ
  lem-pass-X1-CS13-X1-vs-CS02-TOFF013-CSd02-TOFF013 : St 1979
  lem-pass-X1-CS13-X1-vs-CS02-TOFF013-CSd02-TOFF013 = pickᴰ 19 Sᴰ
  lem-pass-X1-CSd13-X1-vs-CS02-TOFF013-CSd02-TOFF013 : St 1980
  lem-pass-X1-CSd13-X1-vs-CS02-TOFF013-CSd02-TOFF013 = pickᴰ 20 Sᴰ
  lem-pass-X2-CK23-X2-vs-TOFF123-CS01-TOFF123-CSd01 : St 1981
  lem-pass-X2-CK23-X2-vs-TOFF123-CS01-TOFF123-CSd01 = pickᴰ 21 Sᴰ
  lem-pass-X2-CKd23-X2-vs-TOFF123-CS01-TOFF123-CSd01 : St 1982
  lem-pass-X2-CKd23-X2-vs-TOFF123-CS01-TOFF123-CSd01 = pickᴰ 22 Sᴰ
  lem-pass-X2-CS23-X2-vs-TOFF123-CS01-TOFF123-CSd01 : St 1983
  lem-pass-X2-CS23-X2-vs-TOFF123-CS01-TOFF123-CSd01 = pickᴰ 23 Sᴰ
  lem-pass-X2-CSd23-X2-vs-TOFF123-CS01-TOFF123-CSd01 : St 1984
  lem-pass-X2-CSd23-X2-vs-TOFF123-CS01-TOFF123-CSd01 = pickᴰ 24 Sᴰ
  lem-pass-X3-CK31-X3-vs-TOFF213-CS02-TOFF213-CSd02 : St 1985
  lem-pass-X3-CK31-X3-vs-TOFF213-CS02-TOFF213-CSd02 = pickᴰ 25 Sᴰ
  lem-pass-X3-CK32-X3-vs-TOFF123-CS01-TOFF123-CSd01 : St 1986
  lem-pass-X3-CK32-X3-vs-TOFF123-CS01-TOFF123-CSd01 = pickᴰ 26 Sᴰ
  lem-pass-X3-CKd31-X3-vs-TOFF213-CS02-TOFF213-CSd02 : St 1987
  lem-pass-X3-CKd31-X3-vs-TOFF213-CS02-TOFF213-CSd02 = pickᴰ 27 Sᴰ
  lem-pass-X3-CKd32-X3-vs-TOFF123-CS01-TOFF123-CSd01 : St 1988
  lem-pass-X3-CKd32-X3-vs-TOFF123-CS01-TOFF123-CSd01 = pickᴰ 28 Sᴰ
  lem-S2-at1023 : St 1918
  lem-S2-at1023 = pickᴰ 29 Sᴰ
  lem-S2-at1203 : St 1945
  lem-S2-at1203 = pickᴰ 30 Sᴰ
  lem-S2-at2013 : St 1942
  lem-S2-at2013 = pickᴰ 31 Sᴰ
  lem-S2-at2103 : St 1946
  lem-S2-at2103 = pickᴰ 32 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 1926
  lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 33 Sᴰ
  lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 1928
  lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 34 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 1930
  lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 35 Sᴰ
  lem-S2-ᵖ-1 : St 1931
  lem-S2-ᵖ-1 = pickᴰ 36 Sᴰ
  lem-pass-CCZ123-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 1989
  lem-pass-CCZ123-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 37 Sᴰ
  lem-pass-CCZ123-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : St 1990
  lem-pass-CCZ123-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = pickᴰ 38 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2 : St 1991
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2 = pickᴰ 39 Sᴰ
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ12-CCZ123 : St 1992
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ12-CCZ123 = pickᴰ 40 Sᴰ
  lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CZ12-CCZ123 : St 1993
  lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CZ12-CCZ123 = pickᴰ 41 Sᴰ
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CCZ123 : St 1994
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CCZ123 = pickᴰ 42 Sᴰ
  lem-pass-CCZ123-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 1995
  lem-pass-CCZ123-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 43 Sᴰ
  lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 1996
  lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 44 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-TOFF102-X0-X2 : St 1997
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-TOFF102-X0-X2 = pickᴰ 45 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-TOFF102-X0-X2 : St 1998
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-TOFF102-X0-X2 = pickᴰ 46 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CZ12-CCZ123 : St 1999
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CZ12-CCZ123 = pickᴰ 47 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CZ12-CCZ123 : St 2000
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CZ12-CCZ123 = pickᴰ 48 Sᴰ
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CCZ123 : St 2001
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CCZ123 = pickᴰ 49 Sᴰ
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CCZ123 : St 2002
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CCZ123 = pickᴰ 50 Sᴰ

private
  q1 : Eqn
  q1 = sE 1281 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-CS12-CS12-CKd21-X2
  q2 : Eqn
  q2 = sE 1296 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-CKd21-CS12-CS12-X2
  q3 : Eqn
  q3 = sE 1991 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2

-- Bar(SSSKSS;2,3->0) passes factors of X0 X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X0 X1 X2: 4 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乇丶丶么丘丘丷么丶丶丘丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘丘乇丶丶么丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇丶丶么丘丘丷么丶丶丘丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘丘乇丶丶么丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乇丶丶么丘丘丷么丶丶丘丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘丘乇丶丶么丘") (ℓ "丘乇丶丶么丘丘丷么丶丶丘丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘丘乇丶丶么丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 0 q1 ∷
   rw 6 q2 ∷
   rw 12 q3 ∷
   rw 88 q1 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = sE 1994 lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CCZ123

-- pass [CCZ123] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "乜丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "乜丞中九丮九丞") (ℓ "丞中九丮九丞乜")
  (rw⁻ 0 q4 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = wE 1985 W
  q6 : Eqn
  q6 = sE 1992 lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ12-CCZ123
  q7 : Eqn
  q7 = eqn (ℓ "丸丞") (ℓ "丞丸") (low₃-comm ((CZ ↑)) (X))
  q8 : Eqn
  q8 = wE 2036 W

-- pass [X3 CS13 TOFF102 CSd13 TOFF102 X3] [CCZ123]: 5 steps
lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CCZ123 : ⟪ (ℓ "丞丽习举习丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丞丽习举习丞") ⟫ʷ
lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CCZ123 = derive (ℓ "丞丽习举习丞乜") (ℓ "乜丞丽习举习丞")
  (rw 5 q5 ∷
   rw 1 q6 ∷
   rw⁻ 0 q7 ∷
   rw 1 q5 ∷
   rw 0 q8 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = sE 1971 lem-pass-CCZ123-vs-X2-CS12-X2
  q10 : Eqn
  q10 = sE 1969 lem-pass-CCZ123-vs-X2-CK21-X2
  q11 : Eqn
  q11 = sE 1990 lem-pass-CCZ123-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3
  q12 : Eqn
  q12 = sE 1970 lem-pass-CCZ123-vs-X2-CKd21-X2
  q13 : Eqn
  q13 = sE 1972 lem-pass-CCZ123-vs-X2-CSd12-X2

-- CCZ(2,1,3) passes split Gad(t=1, W=(2, 3), d=SK, e=-1): 5 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "乜丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘乜") ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ = derive (ℓ "乜丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘") (ℓ "丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘乜")
  (rw 0 q9 ∷
   rw 3 q10 ∷
   rw 6 q11 ∷
   rw 14 q12 ∷
   rw 17 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = sE 1993 lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CZ12-CCZ123

-- pass [X3 CS23 TOFF201 CSd23 TOFF201 X3] [CCZ123]: 5 steps
lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CCZ123 : ⟪ (ℓ "丞义乣乊乣丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丞义乣乊乣丞") ⟫ʷ
lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CCZ123 = derive (ℓ "丞义乣乊乣丞乜") (ℓ "乜丞义乣乊乣丞")
  (rw 5 q5 ∷
   rw 1 q14 ∷
   rw⁻ 0 q7 ∷
   rw 1 q5 ∷
   rw 0 q8 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = sE 1931 lem-S2-ᵖ-1
  q16 : Eqn
  q16 = sE 1979 lem-pass-X1-CS13-X1-vs-CS02-TOFF013-CSd02-TOFF013
  q17 : Eqn
  q17 = sE 1931 lem-S2-ᵖ-1

-- pass [X1 CS13 X1] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丒丽丒中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丒丽丒") ⟫ʷ
lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丒丽丒中九丮九") (ℓ "中九丮九丒丽丒")
  (rw 3 q15 ∷
   rw 0 q16 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = sE 1977 lem-pass-X1-CK13-X1-vs-CS02-TOFF013-CSd02-TOFF013

-- pass [X1 CK13 X1] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X1-CK13-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丒乁丒中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丒乁丒") ⟫ʷ
lem-pass-X1-CK13-X1-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丒乁丒中九丮九") (ℓ "中九丮九丒乁丒")
  (rw 3 q15 ∷
   rw 0 q18 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = sE 1980 lem-pass-X1-CSd13-X1-vs-CS02-TOFF013-CSd02-TOFF013

-- pass [X1 CSd13 X1] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丒举丒中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丒举丒") ⟫ʷ
lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丒举丒中九丮九") (ℓ "中九丮九丒举丒")
  (rw 3 q15 ∷
   rw 0 q19 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = sE 1975 lem-pass-CCZ123-vs-X1-CS01-X1
  q21 : Eqn
  q21 = sE 1973 lem-pass-CCZ123-vs-X1-CK10-X1
  q22 : Eqn
  q22 = sE 1989 lem-pass-CCZ123-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q23 : Eqn
  q23 = sE 1974 lem-pass-CCZ123-vs-X1-CKd10-X1
  q24 : Eqn
  q24 = sE 1976 lem-pass-CCZ123-vs-X1-CSd01-X1

-- CCZ(1,2,3) passes split Gad(t=0, W=(1, 2, 3), d=SK, e=-1): 5 steps
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "乜丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒") ⟫ʷ ≈ ⟪ (ℓ "丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒乜") ⟫ʷ
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ = derive (ℓ "乜丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒") (ℓ "丒丠丒丒临丒丒丘丞中九丮九丒丘丞丒丵丒丒両丒乜")
  (rw 0 q20 ∷
   rw 3 q21 ∷
   rw 6 q22 ∷
   rw 16 q23 ∷
   rw 19 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = sE 1978 lem-pass-X1-CKd13-X1-vs-CS02-TOFF013-CSd02-TOFF013

-- pass [X1 CKd13 X1] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丒乂丒中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丒乂丒") ⟫ʷ
lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丒乂丒中九丮九") (ℓ "中九丮九丒乂丒")
  (rw 3 q15 ∷
   rw 0 q25 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

-- CCZ(2,3,1) passes split Gad(t=1, W=(2, 3), d=SdKdSS, e=-1): 9 steps
lem-CCZ⟨231⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "乜丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘乜") ⟫ʷ
lem-CCZ⟨231⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "乜丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘") (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘乜")
  (rw 0 q13 ∷
   rw 3 q12 ∷
   rw 6 q9 ∷
   rw 9 q9 ∷
   rw 12 q11 ∷
   rw 20 q13 ∷
   rw 23 q13 ∷
   rw 26 q10 ∷
   rw 29 q9 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (ℓ "丌丸") (ℓ "丸丌") (low₁-comm (X) (CZ))
  q27 : Eqn
  q27 = eqn (ℓ "丌乜") (ℓ "乜丌") (low₁-comm (X) (CCZ))

-- pass [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3] [CCZ123]: 10 steps
lem-pass-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3-vs-CCZ123 : ⟪ (ℓ "丌丞丽习举习丌丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丌丞丽习举习丌丞") ⟫ʷ
lem-pass-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3-vs-CCZ123 = derive (ℓ "丌丞丽习举习丌丞乜") (ℓ "乜丌丞丽习举习丌丞")
  (rw 7 q5 ∷
   rw 6 q26 ∷
   rw 7 q27 ∷
   rw 2 q6 ∷
   rw⁻ 1 q7 ∷
   rw 2 q5 ∷
   rw 0 q26 ∷
   rw 1 q26 ∷
   rw 2 q27 ∷
   rw 0 q8 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = sE 2001 lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CCZ123

-- pass [CCZ123] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "乜丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "乜丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞乜")
  (rw⁻ 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 1102 W
  q30 : Eqn
  q30 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q31 : Eqn
  q31 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q32 : Eqn
  q32 = eqn (ℓ "丌丽") (ℓ "丽丌") (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))
  q33 : Eqn
  q33 = wE 387 W
  q34 : Eqn
  q34 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q35 : Eqn
  q35 = wE 257 W
  q36 : Eqn
  q36 = wE 389 W
  q37 : Eqn
  q37 = eqn (ℓ "习丞") (ℓ "丞习") (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q38 : Eqn
  q38 = wE 390 W
  q39 : Eqn
  q39 = eqn (ℓ "丌举") (ℓ "举丌") (low₁-comm (X) ((Swap ↑ • (CS • CS • CS) • Swap ↑)))
  q40 : Eqn
  q40 = wE 258 W
  q41 : Eqn
  q41 = sE 1730 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3
  q42 : Eqn
  q42 = sE 1997 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-TOFF102-X0-X2
  q43 : Eqn
  q43 = sE 1731 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3
  q44 : Eqn
  q44 = sE 635 lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 30 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 33 q29 ∷
   rw 40 q29 ∷
   rw 47 q29 ∷
   rw 29 q30 ∷
   rw 30 q31 ∷
   rw 31 q32 ∷
   rw 32 q33 ∷
   rw 29 q34 ∷
   rw 30 q35 ∷
   rw 31 q36 ∷
   rw⁻ 34 q37 ∷
   rw⁻ 35 q31 ∷
   rw⁻ 36 q34 ∷
   rw 37 q38 ∷
   rw 37 q30 ∷
   rw 38 q31 ∷
   rw 39 q39 ∷
   rw 40 q33 ∷
   rw 37 q34 ∷
   rw 38 q40 ∷
   rw 39 q36 ∷
   rw⁻ 42 q37 ∷
   rw⁻ 43 q31 ∷
   rw⁻ 44 q34 ∷
   rw 45 q38 ∷
   rw 0 q41 ∷
   rw 3 q42 ∷
   rw 8 q43 ∷
   rw 11 q42 ∷
   rw⁻ 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = sE 1995 lem-pass-CCZ123-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3

-- CCZ(2,1,3) passes split Gad(t=1, W=(0, 2, 3), d=SK, e=-1): 5 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "乜丘丶丘丘乇丘丌丘丞丽习举习丌丘丞丘么丘丘丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘丘乇丘丌丘丞丽习举习丌丘丞丘么丘丘丷丘乜") ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ = derive (ℓ "乜丘丶丘丘乇丘丌丘丞丽习举习丌丘丞丘么丘丘丷丘") (ℓ "丘丶丘丘乇丘丌丘丞丽习举习丌丘丞丘么丘丘丷丘乜")
  (rw 0 q9 ∷
   rw 3 q10 ∷
   rw 6 q45 ∷
   rw 16 q12 ∷
   rw 19 q13 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = sE 1732 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3
  q47 : Eqn
  q47 = sE 1998 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-TOFF102-X0-X2
  q48 : Eqn
  q48 = sE 1733 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 30 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 35 q29 ∷
   rw 42 q29 ∷
   rw 49 q29 ∷
   rw 31 q30 ∷
   rw 32 q31 ∷
   rw 33 q32 ∷
   rw 34 q33 ∷
   rw 31 q34 ∷
   rw 32 q35 ∷
   rw 33 q36 ∷
   rw⁻ 36 q37 ∷
   rw⁻ 37 q31 ∷
   rw⁻ 38 q34 ∷
   rw 39 q38 ∷
   rw 39 q30 ∷
   rw 40 q31 ∷
   rw 41 q39 ∷
   rw 42 q33 ∷
   rw 39 q34 ∷
   rw 40 q40 ∷
   rw 41 q36 ∷
   rw⁻ 44 q37 ∷
   rw⁻ 45 q31 ∷
   rw⁻ 46 q34 ∷
   rw 47 q38 ∷
   rw 0 q46 ∷
   rw 3 q47 ∷
   rw 8 q48 ∷
   rw 11 q47 ∷
   rw⁻ 0 q44 ∷ []) Eq.refl

-- pass [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3] [CCZ123]: 10 steps
lem-pass-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3-vs-CCZ123 : ⟪ (ℓ "丌丞义乣乊乣丌丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丌丞义乣乊乣丌丞") ⟫ʷ
lem-pass-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3-vs-CCZ123 = derive (ℓ "丌丞义乣乊乣丌丞乜") (ℓ "乜丌丞义乣乊乣丌丞")
  (rw 7 q5 ∷
   rw 6 q26 ∷
   rw 7 q27 ∷
   rw 2 q14 ∷
   rw⁻ 1 q7 ∷
   rw 2 q5 ∷
   rw 0 q26 ∷
   rw 1 q26 ∷
   rw 2 q27 ∷
   rw 0 q8 ∷ []) Eq.refl

-- CCZ(2,1,3) passes split Gad(t=1, W=(0, 2, 3), d=SdKdSS, e=-1): 9 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "乜丘丷丘丘么丘丘丶丘丘丶丘丌丘丞丽习举习丌丘丞丘丷丘丘丷丘丘乇丘丘丶丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丞丽习举习丌丘丞丘丷丘丘丷丘丘乇丘丘丶丘乜") ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "乜丘丷丘丘么丘丘丶丘丘丶丘丌丘丞丽习举习丌丘丞丘丷丘丘丷丘丘乇丘丘丶丘") (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丞丽习举习丌丘丞丘丷丘丘丷丘丘乇丘丘丶丘乜")
  (rw 0 q13 ∷
   rw 3 q12 ∷
   rw 6 q9 ∷
   rw 9 q9 ∷
   rw 12 q45 ∷
   rw 22 q13 ∷
   rw 25 q13 ∷
   rw 28 q10 ∷
   rw 31 q9 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 1 W
  q50 : Eqn
  q50 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q51 : Eqn
  q51 = wE 173 W
  q52 : Eqn
  q52 = wE 3 W
  q53 : Eqn
  q53 = wE 2059 W
  q54 : Eqn
  q54 = wE 175 W
  q55 : Eqn
  q55 = sE 1930 lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q56 : Eqn
  q56 = sE 841 lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q57 : Eqn
  q57 = sE 1926 lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q58 : Eqn
  q58 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q59 : Eqn
  q59 = wE 2060 W

-- pass [X3 CKd30 X3] [Sd0 TOFF012 CS03 TOFF012 CSd03 S0]: 45 steps
lem-pass-X3-CKd30-X3-vs-Sd0-TOFF012-CS03-TOFF012-CSd03-S0 : ⟪ (ℓ "丞乒丞三九中九丮丈") ⟫ʷ ≈ ⟪ (ℓ "三九中九丮丈丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd0-TOFF012-CS03-TOFF012-CSd03-S0 = derive (ℓ "丞乒丞三九中九丮丈") (ℓ "三九中九丮丈丞乒丞")
  (rw 4 q49 ∷
   rw 3 q50 ∷
   rw 2 q51 ∷
   re 1 1 (ℓ "乏久乏") ∷
   rw 3 q52 ∷
   rw 0 q51 ∷
   rw 1 q53 ∷
   rw⁻ 0 q50 ∷
   rw 1 q54 ∷
   rw 4 q49 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q54 ∷
   rw 4 q54 ∷
   rw 7 q49 ∷
   re 5 3 (ℓ "乒") ∷
   rw 6 q54 ∷
   rw 7 q54 ∷
   rw 10 q49 ∷
   re 8 3 (ℓ "丮") ∷
   rw 9 q54 ∷
   rw 10 q52 ∷
   rw 7 q55 ∷
   rw 4 q56 ∷
   rw 1 q57 ∷
   rw 15 q49 ∷
   rw 14 q58 ∷
   rw 13 q51 ∷
   re 12 1 (ℓ "乏丨乏") ∷
   rw 14 q52 ∷
   rw 11 q51 ∷
   rw 10 q51 ∷
   re 9 1 (ℓ "乏久乏") ∷
   rw 11 q52 ∷
   rw 8 q51 ∷
   rw 7 q51 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q52 ∷
   rw 5 q51 ∷
   rw 6 q59 ∷
   rw⁻ 5 q58 ∷
   rw 6 q54 ∷
   rw 9 q49 ∷
   re 7 3 (ℓ "乒") ∷
   rw 8 q54 ∷
   rw 9 q52 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = sE 2002 lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CCZ123

-- pass [CCZ123] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 1 steps
lem-pass-CCZ123-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (ℓ "乜丞九中九丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞九中九丮丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (ℓ "乜丞九中九丮丞") (ℓ "丞九中九丮丞乜")
  (rw⁻ 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 5 W
  q62 : Eqn
  q62 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q63 : Eqn
  q63 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q64 : Eqn
  q64 = wE 140 W
  q65 : Eqn
  q65 = wE 1495 W
  q66 : Eqn
  q66 = wE 142 W
  q67 : Eqn
  q67 = wE 31 W
  q68 : Eqn
  q68 = wE 1413 W
  q69 : Eqn
  q69 = sE 1928 lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X2 CK20 X2] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 25 steps
lem-pass-X2-CK20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (ℓ "丘乄丘丞九中九丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞九中九丮丞丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (ℓ "丘乄丘丞九中九丮丞") (ℓ "丞九中九丮丞丘乄丘")
  (rw 4 q61 ∷
   rw⁻ 3 q62 ∷
   rw⁻ 2 q63 ∷
   rw 1 q64 ∷
   rw⁻ 0 q63 ∷
   rw 1 q65 ∷
   rw 0 q62 ∷
   rw 1 q63 ∷
   rw 2 q66 ∷
   rw 3 q63 ∷
   rw 4 q67 ∷
   rw 1 q68 ∷
   rw 1 q69 ∷
   rw 5 q68 ∷
   rw 9 q61 ∷
   rw⁻ 8 q62 ∷
   rw⁻ 7 q63 ∷
   rw 6 q64 ∷
   rw⁻ 5 q63 ∷
   rw 6 q65 ∷
   rw 5 q62 ∷
   rw 6 q63 ∷
   rw 7 q66 ∷
   rw 8 q63 ∷
   rw 9 q67 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q71 : Eqn
  q71 = wE 2061 W
  q72 : Eqn
  q72 = sE 38 lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q73 : Eqn
  q73 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q74 : Eqn
  q74 = wE 2062 W

-- pass [X3 CSd30 X3] [Kd0 TOFF012 CS03 TOFF012 CSd03 K0]: 45 steps
lem-pass-X3-CSd30-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : ⟪ (ℓ "丞丮丞下九中九丮上") ⟫ʷ ≈ ⟪ (ℓ "下九中九丮上丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = derive (ℓ "丞丮丞下九中九丮上") (ℓ "下九中九丮上丞丮丞")
  (rw 4 q49 ∷
   rw 3 q70 ∷
   rw 2 q51 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q52 ∷
   rw 0 q51 ∷
   rw 1 q71 ∷
   rw⁻ 0 q70 ∷
   rw 1 q54 ∷
   rw 4 q49 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q54 ∷
   rw 4 q54 ∷
   rw 7 q49 ∷
   re 5 3 (ℓ "乑") ∷
   rw 6 q54 ∷
   rw 7 q54 ∷
   rw 10 q49 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q54 ∷
   rw 10 q52 ∷
   rw 7 q57 ∷
   rw 4 q72 ∷
   rw 1 q57 ∷
   rw 15 q49 ∷
   rw 14 q73 ∷
   rw 13 q51 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q52 ∷
   rw 11 q51 ∷
   rw 10 q51 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q52 ∷
   rw 8 q51 ∷
   rw 7 q51 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q52 ∷
   rw 5 q51 ∷
   rw 6 q74 ∷
   rw⁻ 5 q73 ∷
   rw 6 q54 ∷
   rw 9 q49 ∷
   re 7 3 (ℓ "丮") ∷
   rw 8 q54 ∷
   rw 9 q52 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 1462 W
  q76 : Eqn
  q76 = wE 1463 W

-- pass [CS30] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 23 steps
lem-pass-CS30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (ℓ "中丞九中九丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞九中九丮丞中") ⟫ʷ
lem-pass-CS30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (ℓ "中丞九中九丮丞") (ℓ "丞九中九丮丞中")
  (rw 2 q49 ∷
   rw 1 q51 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q52 ∷
   rw 1 q75 ∷
   rw 0 q54 ∷
   rw 1 q54 ∷
   rw 4 q49 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q54 ∷
   rw 4 q52 ∷
   rw 1 q57 ∷
   rw 9 q49 ∷
   rw 8 q51 ∷
   rw 7 q51 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q52 ∷
   rw 5 q51 ∷
   rw 6 q76 ∷
   rw 5 q54 ∷
   rw 8 q49 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q52 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = sE 1918 lem-S2-at1023
  q78 : Eqn
  q78 = wE 225 W
  q79 : Eqn
  q79 = eqn (ℓ "丶丞") (ℓ "丞丶") (low₃-comm ((CS ↑)) (X))
  q80 : Eqn
  q80 = eqn (ℓ "丷丞") (ℓ "丞丷") (low₃-comm (((CS • CS • CS) ↑)) (X))

-- distribute Gad(t=1, W=(3,), d=1, e=1) TOFF103 CS12 TOFF103 CSd12: 8 steps
lem-distribute-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12 : ⟪ (ℓ "丞习丽习举丞") ⟫ʷ ≈ ⟪ (ℓ "丞乡丞丶丞乡丞丷") ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12 = derive (ℓ "丞习丽习举丞") (ℓ "丞乡丞丶丞乡丞丷")
  (rw 1 q77 ∷
   rw 2 q78 ∷
   rw 5 q78 ∷
   rw 8 q78 ∷
   rw⁻ 3 q79 ∷
   rw 4 q38 ∷
   rw⁻ 7 q80 ∷
   rw 8 q38 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = sE 1945 lem-S2-at1203
  q82 : Eqn
  q82 = sE 1988 lem-pass-X3-CKd32-X3-vs-TOFF123-CS01-TOFF123-CSd01
  q83 : Eqn
  q83 = sE 1945 lem-S2-at1203

-- pass [X3 CKd32 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CKd32-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丞乘丞习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丞乘丞习丽习举") (ℓ "习丽习举丞乘丞")
  (rw 3 q81 ∷
   rw 0 q82 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = sE 1999 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CZ12-CCZ123

-- pass [X3 TOFF102 CS13 TOFF102 CSd13 X3] [CCZ123]: 5 steps
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CCZ123 : ⟪ (ℓ "丞习丽习举丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丞习丽习举丞") ⟫ʷ
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CCZ123 = derive (ℓ "丞习丽习举丞乜") (ℓ "乜丞习丽习举丞")
  (rw 5 q5 ∷
   rw 1 q84 ∷
   rw⁻ 0 q7 ∷
   rw 1 q5 ∷
   rw 0 q8 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = sE 1986 lem-pass-X3-CK32-X3-vs-TOFF123-CS01-TOFF123-CSd01

-- pass [X3 CK32 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CK32-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丞乗丞习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丞乗丞习丽习举") (ℓ "习丽习举丞乗丞")
  (rw 3 q81 ∷
   rw 0 q85 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = sE 1983 lem-pass-X2-CS23-X2-vs-TOFF123-CS01-TOFF123-CSd01

-- pass [X2 CS23 X2] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丘义丘习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丘义丘") ⟫ʷ
lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丘义丘习丽习举") (ℓ "习丽习举丘义丘")
  (rw 3 q81 ∷
   rw 0 q86 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = sE 1981 lem-pass-X2-CK23-X2-vs-TOFF123-CS01-TOFF123-CSd01

-- pass [X2 CK23 X2] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丘乍丘习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丘乍丘") ⟫ʷ
lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丘乍丘习丽习举") (ℓ "习丽习举丘乍丘")
  (rw 3 q81 ∷
   rw 0 q87 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = sE 1984 lem-pass-X2-CSd23-X2-vs-TOFF123-CS01-TOFF123-CSd01

-- pass [X2 CSd23 X2] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丘乊丘习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丘乊丘") ⟫ʷ
lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丘乊丘习丽习举") (ℓ "习丽习举丘乊丘")
  (rw 3 q81 ∷
   rw 0 q88 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = sE 1996 lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3

-- CCZ(2,1,3) passes split Gad(t=1, W=(2, 3), d=1, e=1): 1 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩ : ⟪ (ℓ "乜丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞乜") ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩ = derive (ℓ "乜丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞乜")
  (rw 0 q89 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = sE 1982 lem-pass-X2-CKd23-X2-vs-TOFF123-CS01-TOFF123-CSd01

-- pass [X2 CKd23 X2] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丘乎丘习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丘乎丘") ⟫ʷ
lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丘乎丘习丽习举") (ℓ "习丽习举丘乎丘")
  (rw 3 q81 ∷
   rw 0 q90 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = sE 1942 lem-S2-at2013

-- distribute Gad(t=2, W=(3,), d=1, e=1) TOFF203 CS12 TOFF203 CSd12: 8 steps
lem-distribute-Gad⟨t≡2-W≡⟨3⟩-d≡1-e≡1⟩-TOFF203-CS12-TOFF203-CSd12 : ⟪ (ℓ "丞乣义乣乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞乤丞丶丞乤丞丷") ⟫ʷ
lem-distribute-Gad⟨t≡2-W≡⟨3⟩-d≡1-e≡1⟩-TOFF203-CS12-TOFF203-CSd12 = derive (ℓ "丞乣义乣乊丞") (ℓ "丞乤丞丶丞乤丞丷")
  (rw 1 q91 ∷
   rw 2 q78 ∷
   rw 5 q78 ∷
   rw 8 q78 ∷
   rw⁻ 3 q79 ∷
   rw 4 q38 ∷
   rw⁻ 7 q80 ∷
   rw 8 q38 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = sE 1946 lem-S2-at2103
  q93 : Eqn
  q93 = sE 1987 lem-pass-X3-CKd31-X3-vs-TOFF213-CS02-TOFF213-CSd02
  q94 : Eqn
  q94 = sE 1946 lem-S2-at2103

-- pass [X3 CKd31 X3] [TOFF201 CS23 TOFF201 CSd23]: 3 steps
lem-pass-X3-CKd31-X3-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (ℓ "丞乕丞乣义乣乊") ⟫ʷ ≈ ⟪ (ℓ "乣义乣乊丞乕丞") ⟫ʷ
lem-pass-X3-CKd31-X3-vs-TOFF201-CS23-TOFF201-CSd23 = derive (ℓ "丞乕丞乣义乣乊") (ℓ "乣义乣乊丞乕丞")
  (rw 3 q92 ∷
   rw 0 q93 ∷
   rw⁻ 0 q94 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = sE 2000 lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CZ12-CCZ123

-- pass [X3 TOFF201 CS23 TOFF201 CSd23 X3] [CCZ123]: 5 steps
lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-CCZ123 : ⟪ (ℓ "丞乣义乣乊丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丞乣义乣乊丞") ⟫ʷ
lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-CCZ123 = derive (ℓ "丞乣义乣乊丞乜") (ℓ "乜丞乣义乣乊丞")
  (rw 5 q5 ∷
   rw 1 q95 ∷
   rw⁻ 0 q7 ∷
   rw 1 q5 ∷
   rw 0 q8 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = sE 1985 lem-pass-X3-CK31-X3-vs-TOFF213-CS02-TOFF213-CSd02

-- pass [X3 CK31 X3] [TOFF201 CS23 TOFF201 CSd23]: 3 steps
lem-pass-X3-CK31-X3-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (ℓ "丞乔丞乣义乣乊") ⟫ʷ ≈ ⟪ (ℓ "乣义乣乊丞乔丞") ⟫ʷ
lem-pass-X3-CK31-X3-vs-TOFF201-CS23-TOFF201-CSd23 = derive (ℓ "丞乔丞乣义乣乊") (ℓ "乣义乣乊丞乔丞")
  (rw 3 q92 ∷
   rw 0 q96 ∷
   rw⁻ 0 q94 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q98 : Eqn
  q98 = wE 1681 W
  q99 : Eqn
  q99 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q100 : Eqn
  q100 = wE 76 W
  q101 : Eqn
  q101 = wE 2063 W
  q102 : Eqn
  q102 = wE 29 W
  q103 : Eqn
  q103 = wE 1482 W

-- pass [X3 CSd30 X3] [X1 X2 TOFF012 CS03 TOFF012 CSd03 X1 X2]: 87 steps
lem-pass-X3-CSd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 : ⟪ (ℓ "丞丮丞丒丘九中九丮丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘九中九丮丒丘丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 = derive (ℓ "丞丮丞丒丘九中九丮丒丘") (ℓ "丒丘九中九丮丒丘丞丮丞")
  (rw 4 q49 ∷
   rw 3 q97 ∷
   rw 2 q51 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q52 ∷
   rw 0 q51 ∷
   rw 1 q98 ∷
   rw⁻ 0 q97 ∷
   rw 1 q54 ∷
   rw 4 q49 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q54 ∷
   rw 4 q52 ∷
   rw 5 q61 ∷
   rw⁻ 4 q63 ∷
   rw⁻ 3 q62 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw⁻ 4 q99 ∷
   rw 3 q100 ∷
   rw⁻ 2 q99 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 1 q62 ∷
   rw 2 q101 ∷
   rw 1 q63 ∷
   rw 2 q62 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q99 ∷
   rw 4 q102 ∷
   rw 5 q99 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q62 ∷
   rw 5 q67 ∷
   rw 5 q49 ∷
   rw 4 q51 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q52 ∷
   rw 2 q51 ∷
   rw 3 q103 ∷
   rw 2 q54 ∷
   rw 5 q49 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q54 ∷
   rw 5 q52 ∷
   rw 2 q55 ∷
   rw 9 q49 ∷
   rw 8 q51 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 9 q52 ∷
   rw 6 q51 ∷
   rw 7 q103 ∷
   rw 6 q54 ∷
   rw 9 q49 ∷
   re 7 3 (ℓ "丮") ∷
   rw 8 q54 ∷
   rw 9 q52 ∷
   rw 10 q49 ∷
   rw 9 q97 ∷
   rw 8 q51 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 9 q52 ∷
   rw 6 q51 ∷
   rw 7 q98 ∷
   rw⁻ 6 q97 ∷
   rw 7 q54 ∷
   rw 10 q49 ∷
   re 8 3 (ℓ "丮") ∷
   rw 9 q54 ∷
   rw 10 q52 ∷
   rw 11 q61 ∷
   rw⁻ 10 q63 ∷
   rw⁻ 9 q62 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw⁻ 10 q99 ∷
   rw 9 q100 ∷
   rw⁻ 8 q99 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 7 q62 ∷
   rw 8 q101 ∷
   rw 7 q63 ∷
   rw 8 q62 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q99 ∷
   rw 10 q102 ∷
   rw 11 q99 ∷
   re 9 3 (ℓ "丮") ∷
   rw 10 q62 ∷
   rw 11 q67 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = wE 1682 W
  q105 : Eqn
  q105 = wE 7 W
  q106 : Eqn
  q106 = wE 2064 W
  q107 : Eqn
  q107 = wE 27 W
  q108 : Eqn
  q108 = wE 1490 W

-- pass [X3 CS30 X3] [X1 X2 TOFF012 CS03 TOFF012 CSd03 X1 X2]: 87 steps
lem-pass-X3-CS30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 : ⟪ (ℓ "丞中丞丒丘九中九丮丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘九中九丮丒丘丞中丞") ⟫ʷ
lem-pass-X3-CS30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 = derive (ℓ "丞中丞丒丘九中九丮丒丘") (ℓ "丒丘九中九丮丒丘丞中丞")
  (rw 4 q49 ∷
   rw 3 q97 ∷
   rw 2 q51 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q52 ∷
   rw 0 q51 ∷
   rw 1 q104 ∷
   rw⁻ 0 q97 ∷
   rw 1 q54 ∷
   rw 4 q49 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q54 ∷
   rw 4 q52 ∷
   rw 5 q61 ∷
   rw⁻ 4 q63 ∷
   rw⁻ 3 q62 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q99 ∷
   rw 3 q105 ∷
   rw⁻ 2 q99 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 1 q62 ∷
   rw 2 q106 ∷
   rw 1 q63 ∷
   rw 2 q62 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q99 ∷
   rw 4 q107 ∷
   rw 5 q99 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q62 ∷
   rw 5 q67 ∷
   rw 5 q49 ∷
   rw 4 q51 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q52 ∷
   rw 2 q51 ∷
   rw 3 q108 ∷
   rw 2 q54 ∷
   rw 5 q49 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q54 ∷
   rw 5 q52 ∷
   rw 2 q57 ∷
   rw 9 q49 ∷
   rw 8 q51 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q52 ∷
   rw 6 q51 ∷
   rw 7 q108 ∷
   rw 6 q54 ∷
   rw 9 q49 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q54 ∷
   rw 9 q52 ∷
   rw 10 q49 ∷
   rw 9 q97 ∷
   rw 8 q51 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q52 ∷
   rw 6 q51 ∷
   rw 7 q104 ∷
   rw⁻ 6 q97 ∷
   rw 7 q54 ∷
   rw 10 q49 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q54 ∷
   rw 10 q52 ∷
   rw 11 q61 ∷
   rw⁻ 10 q63 ∷
   rw⁻ 9 q62 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q99 ∷
   rw 9 q105 ∷
   rw⁻ 8 q99 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 7 q62 ∷
   rw 8 q106 ∷
   rw 7 q63 ∷
   rw 8 q62 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q99 ∷
   rw 10 q107 ∷
   rw 11 q99 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q62 ∷
   rw 11 q67 ∷ []) Eq.refl
