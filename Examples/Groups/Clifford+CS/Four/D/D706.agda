{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD706 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D706 (W : Ws) (Sᴰ : SD706) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS13 : St 360
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS13 = pickᴰ 0 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CSd13 : St 361
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CSd13 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS13 : St 441
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS13 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-CSd13 : St 442
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-CSd13 = pickᴰ 3 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3 : St 1730
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3 = pickᴰ 4 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3 : St 1731
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3 = pickᴰ 5 Sᴰ
  lem-pass-CCZ123-vs-X2-CK21-X2 : St 1969
  lem-pass-CCZ123-vs-X2-CK21-X2 = pickᴰ 6 Sᴰ
  lem-pass-CCZ123-vs-X2-CKd21-X2 : St 1970
  lem-pass-CCZ123-vs-X2-CKd21-X2 = pickᴰ 7 Sᴰ
  lem-pass-CCZ123-vs-X2-CS12-X2 : St 1971
  lem-pass-CCZ123-vs-X2-CS12-X2 = pickᴰ 8 Sᴰ
  lem-pass-CCZ123-vs-X2-CSd12-X2 : St 1972
  lem-pass-CCZ123-vs-X2-CSd12-X2 = pickᴰ 9 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3 : St 1732
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3 = pickᴰ 10 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3 : St 1733
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3 = pickᴰ 11 Sᴰ
  lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 : St 639
  lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 12 Sᴰ
  lem-distribute-Gad⟨t≡1-W≡⟨0-2⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 : St 671
  lem-distribute-Gad⟨t≡1-W≡⟨0-2⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 13 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CX10-X1 : St 686
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CX10-X1 = pickᴰ 14 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CX10-X1 : St 687
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CX10-X1 = pickᴰ 15 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-CX10-X1 : St 688
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-CX10-X1 = pickᴰ 16 Sᴰ
  lem-pass-TOFF213-vs-X1-CX10-X1 : St 689
  lem-pass-TOFF213-vs-X1-CX10-X1 = pickᴰ 17 Sᴰ
  lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 851
  lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 18 Sᴰ
  lem-LF-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK20-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-S2-CK20-at-1 : St 2003
  lem-LF-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK20-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-S2-CK20-at-1 = pickᴰ 19 Sᴰ
  lem-S2-at1023 : St 1918
  lem-S2-at1023 = pickᴰ 20 Sᴰ
  lem-S2-at2013 : St 1942
  lem-S2-at2013 = pickᴰ 21 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 1926
  lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 22 Sᴰ
  lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 1928
  lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 23 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 1930
  lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 24 Sᴰ
  lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 1996
  lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 25 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-TOFF102-X0-X2 : St 1997
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-TOFF102-X0-X2 = pickᴰ 26 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-TOFF102-X0-X2 : St 1998
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-TOFF102-X0-X2 = pickᴰ 27 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CZ12-CCZ123 : St 1999
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CZ12-CCZ123 = pickᴰ 28 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CZ12-CCZ123 : St 2000
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CZ12-CCZ123 = pickᴰ 29 Sᴰ
  lem-hyb-sym-23-at0321 : St 2004
  lem-hyb-sym-23-at0321 = pickᴰ 30 Sᴰ
  lem-pass-CCZ123-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : St 2005
  lem-pass-CCZ123-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = pickᴰ 31 Sᴰ
  lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : St 2006
  lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = pickᴰ 32 Sᴰ
  lem-pass-CCZ123-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : St 2007
  lem-pass-CCZ123-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = pickᴰ 33 Sᴰ
  lem-pass-X1-CK13-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2008
  lem-pass-X1-CK13-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 34 Sᴰ
  lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2009
  lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 35 Sᴰ
  lem-pass-X1-CS13-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2010
  lem-pass-X1-CS13-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 36 Sᴰ
  lem-pass-X1-CSd13-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2011
  lem-pass-X1-CSd13-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 37 Sᴰ
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CCZ123 : St 2012
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CCZ123 = pickᴰ 38 Sᴰ
  lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CCZ123 : St 2013
  lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CCZ123 = pickᴰ 39 Sᴰ
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS13 : St 2014
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS13 = pickᴰ 40 Sᴰ

private
  q1 : Eqn
  q1 = wE 2065 W
  q2 : Eqn
  q2 = wE 2066 W
  q3 : Eqn
  q3 = sE 2010 lem-pass-X1-CS13-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q4 : Eqn
  q4 = sE 2008 lem-pass-X1-CK13-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q5 : Eqn
  q5 = sE 2011 lem-pass-X1-CSd13-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q6 : Eqn
  q6 = wE 2067 W

-- pass [X1 CKd13 X1] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 9 steps
lem-pass-X1-CKd13-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = derive (X1 ∷ CK13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  (rw 0 q1 ∷
   rw 2 q2 ∷
   rw 14 q3 ∷
   rw 11 q4 ∷
   rw 8 q5 ∷
   rw 5 q4 ∷
   rw 2 q3 ∷
   rw 6 q2 ∷
   rw 6 q6 ∷ []) Eq.refl

private
  q7 : Eqn
  q7 = sE 2007 lem-pass-CCZ123-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3

-- CCZ(1,2,3) passes split Gad(t=0, W=(1, 2, 3), d=1, e=1): 1 steps
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡1-e≡1⟩ : ⟪ (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡1-e≡1⟩ = derive (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  (rw 0 q7 ∷ []) Eq.refl

private
  q8 : Eqn
  q8 = wE 2068 W
  q9 : Eqn
  q9 = wE 2069 W
  q10 : Eqn
  q10 = sE 2009 lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q11 : Eqn
  q11 = wE 2070 W

-- pass [X1 CK13 X1] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 9 steps
lem-pass-X1-CK13-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = derive (X1 ∷ CK13 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  (rw 0 q8 ∷
   rw 2 q9 ∷
   rw 14 q5 ∷
   rw 11 q10 ∷
   rw 8 q3 ∷
   rw 5 q10 ∷
   rw 2 q5 ∷
   rw 6 q9 ∷
   rw 6 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = sE 1969 lem-pass-CCZ123-vs-X2-CK21-X2
  q13 : Eqn
  q13 = sE 1971 lem-pass-CCZ123-vs-X2-CS12-X2
  q14 : Eqn
  q14 = sE 1970 lem-pass-CCZ123-vs-X2-CKd21-X2
  q15 : Eqn
  q15 = sE 1996 lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q16 : Eqn
  q16 = sE 1972 lem-pass-CCZ123-vs-X2-CSd12-X2

-- CCZ(2,3,1) passes split Gad(t=1, W=(2, 3), d=KSSKd, e=1): 9 steps
lem-CCZ⟨231⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨231⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ = derive (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ [])
  (rw 0 q12 ∷
   rw 3 q13 ∷
   rw 6 q13 ∷
   rw 9 q14 ∷
   rw 12 q15 ∷
   rw 20 q12 ∷
   rw 23 q16 ∷
   rw 26 q16 ∷
   rw 29 q14 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = sE 1918 lem-S2-at1023
  q18 : Eqn
  q18 = wE 2071 W
  q19 : Eqn
  q19 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q20 : Eqn
  q20 = eqn (X0 ∷ CS12 ∷ []) (CS12 ∷ X0 ∷ []) (low₁-comm (X) (CS))
  q21 : Eqn
  q21 = wE 387 W
  q22 : Eqn
  q22 = eqn (CS12 ∷ X3 ∷ []) (X3 ∷ CS12 ∷ []) (low₃-comm ((CS ↑)) (X))
  q23 : Eqn
  q23 = wE 390 W
  q24 : Eqn
  q24 = eqn (X0 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X0 ∷ []) (low₁-comm (X) ((CS • CS • CS)))
  q25 : Eqn
  q25 = eqn (CS12⁻ ∷ X3 ∷ []) (X3 ∷ CS12⁻ ∷ []) (low₃-comm (((CS • CS • CS) ↑)) (X))

-- distribute Gad(t=1, W=(0, 3), d=1, e=1) TOFF103 CS12 TOFF103 CSd12: 14 steps
lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12 = derive (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ [])
  (rw 2 q17 ∷
   rw 3 q18 ∷
   rw 8 q18 ∷
   rw 13 q18 ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 7 q21 ∷
   rw⁻ 5 q22 ∷
   rw 6 q23 ∷
   rw 11 q19 ∷
   rw 12 q24 ∷
   rw 13 q21 ∷
   rw⁻ 11 q25 ∷
   rw 12 q23 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1985 W
  q27 : Eqn
  q27 = eqn (X0 ∷ CZ12 ∷ []) (CZ12 ∷ X0 ∷ []) (low₁-comm (X) (CZ))
  q28 : Eqn
  q28 = eqn (X0 ∷ CCZ123 ∷ []) (CCZ123 ∷ X0 ∷ []) (low₁-comm (X) (CCZ))
  q29 : Eqn
  q29 = sE 1999 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CZ12-CCZ123
  q30 : Eqn
  q30 = eqn (CZ12 ∷ X3 ∷ []) (X3 ∷ CZ12 ∷ []) (low₃-comm ((CZ ↑)) (X))
  q31 : Eqn
  q31 = wE 2036 W

-- pass [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3] [CCZ123]: 10 steps
lem-pass-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3-vs-CCZ123 : ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3-vs-CCZ123 = derive (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ [])
  (rw 7 q26 ∷
   rw 6 q27 ∷
   rw 7 q28 ∷
   rw 2 q29 ∷
   rw⁻ 1 q30 ∷
   rw 2 q26 ∷
   rw 0 q27 ∷
   rw 1 q27 ∷
   rw 2 q28 ∷
   rw 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 2013 lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CCZ123

-- pass [CCZ123] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (CCZ123 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = derive (CCZ123 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 5 W
  q34 : Eqn
  q34 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q35 : Eqn
  q35 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q36 : Eqn
  q36 = wE 76 W
  q37 : Eqn
  q37 = wE 1499 W
  q38 : Eqn
  q38 = wE 29 W
  q39 : Eqn
  q39 = wE 31 W
  q40 : Eqn
  q40 = wE 2061 W
  q41 : Eqn
  q41 = sE 851 lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03
  q42 : Eqn
  q42 = sE 1928 lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03
  q43 : Eqn
  q43 = wE 2062 W

-- pass [X2 CSd20 X2] [X3 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 X3]: 27 steps
lem-pass-X2-CSd20-X2-vs-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X3 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X3 = derive (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 4 q33 ∷
   rw⁻ 3 q34 ∷
   rw⁻ 2 q35 ∷
   rw 1 q36 ∷
   rw⁻ 0 q35 ∷
   rw 1 q37 ∷
   rw 0 q34 ∷
   rw 1 q35 ∷
   rw 2 q38 ∷
   rw 3 q35 ∷
   rw 4 q39 ∷
   rw 1 q40 ∷
   rw 8 q41 ∷
   rw 5 q42 ∷
   rw 2 q41 ∷
   rw 6 q43 ∷
   rw 11 q33 ∷
   rw⁻ 10 q34 ∷
   rw⁻ 9 q35 ∷
   rw 8 q36 ∷
   rw⁻ 7 q35 ∷
   rw 8 q37 ∷
   rw 7 q34 ∷
   rw 8 q35 ∷
   rw 9 q38 ∷
   rw 10 q35 ∷
   rw 11 q39 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q45 : Eqn
  q45 = wE 2063 W
  q46 : Eqn
  q46 = wE 1 W
  q47 : Eqn
  q47 = wE 173 W
  q48 : Eqn
  q48 = wE 3 W
  q49 : Eqn
  q49 = wE 1482 W
  q50 : Eqn
  q50 = wE 175 W
  q51 : Eqn
  q51 = sE 1930 lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X3 CSd30 X3] [X2 TOFF012 CS03 TOFF012 CSd03 X2]: 61 steps
lem-pass-X3-CSd30-X3-vs-X2-TOFF012-CS03-TOFF012-CSd03-X2 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X2-TOFF012-CS03-TOFF012-CSd03-X2 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q33 ∷
   rw⁻ 3 q35 ∷
   rw⁻ 2 q34 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q44 ∷
   rw 2 q36 ∷
   rw⁻ 1 q44 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q34 ∷
   rw 1 q45 ∷
   rw 0 q35 ∷
   rw 1 q34 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q44 ∷
   rw 3 q38 ∷
   rw 4 q44 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q34 ∷
   rw 4 q39 ∷
   rw 4 q46 ∷
   rw 3 q47 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q48 ∷
   rw 1 q47 ∷
   rw 2 q49 ∷
   rw 1 q50 ∷
   rw 4 q46 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q50 ∷
   rw 4 q48 ∷
   rw 1 q51 ∷
   rw 8 q46 ∷
   rw 7 q47 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q48 ∷
   rw 5 q47 ∷
   rw 6 q49 ∷
   rw 5 q50 ∷
   rw 8 q46 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q50 ∷
   rw 8 q48 ∷
   rw 9 q33 ∷
   rw⁻ 8 q35 ∷
   rw⁻ 7 q34 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q44 ∷
   rw 7 q36 ∷
   rw⁻ 6 q44 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q34 ∷
   rw 6 q45 ∷
   rw 5 q35 ∷
   rw 6 q34 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q44 ∷
   rw 8 q38 ∷
   rw 9 q44 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q34 ∷
   rw 9 q39 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = wE 7 W
  q53 : Eqn
  q53 = wE 2064 W
  q54 : Eqn
  q54 = wE 27 W
  q55 : Eqn
  q55 = wE 1490 W
  q56 : Eqn
  q56 = sE 1926 lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X3 CS30 X3] [X2 TOFF012 CS03 TOFF012 CSd03 X2]: 61 steps
lem-pass-X3-CS30-X3-vs-X2-TOFF012-CS03-TOFF012-CSd03-X2 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-X2-TOFF012-CS03-TOFF012-CSd03-X2 = derive (X3 ∷ CS03 ∷ X3 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 4 q33 ∷
   rw⁻ 3 q35 ∷
   rw⁻ 2 q34 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q44 ∷
   rw 2 q52 ∷
   rw⁻ 1 q44 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q34 ∷
   rw 1 q53 ∷
   rw 0 q35 ∷
   rw 1 q34 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q44 ∷
   rw 3 q54 ∷
   rw 4 q44 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q34 ∷
   rw 4 q39 ∷
   rw 4 q46 ∷
   rw 3 q47 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q48 ∷
   rw 1 q47 ∷
   rw 2 q55 ∷
   rw 1 q50 ∷
   rw 4 q46 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q50 ∷
   rw 4 q48 ∷
   rw 1 q56 ∷
   rw 8 q46 ∷
   rw 7 q47 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q48 ∷
   rw 5 q47 ∷
   rw 6 q55 ∷
   rw 5 q50 ∷
   rw 8 q46 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q50 ∷
   rw 8 q48 ∷
   rw 9 q33 ∷
   rw⁻ 8 q35 ∷
   rw⁻ 7 q34 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q44 ∷
   rw 7 q52 ∷
   rw⁻ 6 q44 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 5 q34 ∷
   rw 6 q53 ∷
   rw 5 q35 ∷
   rw 6 q34 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q44 ∷
   rw 8 q54 ∷
   rw 9 q44 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q34 ∷
   rw 9 q39 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 1102 W
  q58 : Eqn
  q58 = eqn (Toff102 ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ []) (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q59 : Eqn
  q59 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q60 : Eqn
  q60 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))
  q61 : Eqn
  q61 = eqn (X0 ∷ CS13 ∷ []) (CS13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))
  q62 : Eqn
  q62 = wE 257 W
  q63 : Eqn
  q63 = wE 389 W
  q64 : Eqn
  q64 = eqn (X0 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • (CS • CS • CS) • Swap ↑)))
  q65 : Eqn
  q65 = wE 258 W
  q66 : Eqn
  q66 = sE 1997 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-TOFF102-X0-X2
  q67 : Eqn
  q67 = sE 1730 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3
  q68 : Eqn
  q68 = sE 1731 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3
  q69 : Eqn
  q69 = sE 639 lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 30 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 33 q57 ∷
   rw 40 q57 ∷
   rw 47 q57 ∷
   rw⁻ 31 q58 ∷
   rw⁻ 32 q19 ∷
   rw⁻ 33 q59 ∷
   rw 34 q23 ∷
   rw 34 q60 ∷
   rw 35 q19 ∷
   rw 36 q61 ∷
   rw 37 q21 ∷
   rw 34 q59 ∷
   rw 35 q62 ∷
   rw 36 q63 ∷
   rw⁻ 39 q58 ∷
   rw⁻ 40 q19 ∷
   rw⁻ 41 q59 ∷
   rw 42 q23 ∷
   rw 42 q60 ∷
   rw 43 q19 ∷
   rw 44 q64 ∷
   rw 45 q21 ∷
   rw 42 q59 ∷
   rw 43 q65 ∷
   rw 44 q63 ∷
   rw 0 q66 ∷
   rw 5 q67 ∷
   rw 8 q66 ∷
   rw 13 q68 ∷
   rw⁻ 0 q69 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = sE 2006 lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3

-- CCZ(2,1,3) passes split Gad(t=1, W=(0, 2, 3), d=1, e=1): 1 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡1⟩ : ⟪ (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡1⟩ = derive (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  (rw 0 q70 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = sE 1998 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-TOFF102-X0-X2
  q72 : Eqn
  q72 = sE 1732 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3
  q73 : Eqn
  q73 = sE 1733 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 30 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 35 q57 ∷
   rw 42 q57 ∷
   rw 49 q57 ∷
   rw⁻ 33 q58 ∷
   rw⁻ 34 q19 ∷
   rw⁻ 35 q59 ∷
   rw 36 q23 ∷
   rw 36 q60 ∷
   rw 37 q19 ∷
   rw 38 q61 ∷
   rw 39 q21 ∷
   rw 36 q59 ∷
   rw 37 q62 ∷
   rw 38 q63 ∷
   rw⁻ 41 q58 ∷
   rw⁻ 42 q19 ∷
   rw⁻ 43 q59 ∷
   rw 44 q23 ∷
   rw 44 q60 ∷
   rw 45 q19 ∷
   rw 46 q64 ∷
   rw 47 q21 ∷
   rw 44 q59 ∷
   rw 45 q65 ∷
   rw 46 q63 ∷
   rw 0 q71 ∷
   rw 5 q72 ∷
   rw 8 q71 ∷
   rw 13 q73 ∷
   rw⁻ 0 q69 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = sE 1942 lem-S2-at2013

-- distribute Gad(t=2, W=(0, 3), d=1, e=1) TOFF203 CS12 TOFF203 CSd12: 14 steps
lem-distribute-Gad⟨t≡2-W≡⟨0-3⟩-d≡1-e≡1⟩-TOFF203-CS12-TOFF203-CSd12 : ⟪ (X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ CS12 ∷ X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡2-W≡⟨0-3⟩-d≡1-e≡1⟩-TOFF203-CS12-TOFF203-CSd12 = derive (X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ CS12 ∷ X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ [])
  (rw 2 q74 ∷
   rw 3 q18 ∷
   rw 8 q18 ∷
   rw 13 q18 ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 7 q21 ∷
   rw⁻ 5 q22 ∷
   rw 6 q23 ∷
   rw 11 q19 ∷
   rw 12 q24 ∷
   rw 13 q21 ∷
   rw⁻ 11 q25 ∷
   rw 12 q23 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = sE 2000 lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CZ12-CCZ123

-- pass [X0 X3 TOFF201 CS23 TOFF201 CSd23 X0 X3] [CCZ123]: 10 steps
lem-pass-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3-vs-CCZ123 : ⟪ (X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3-vs-CCZ123 = derive (X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ [])
  (rw 7 q26 ∷
   rw 6 q27 ∷
   rw 7 q28 ∷
   rw 2 q75 ∷
   rw⁻ 1 q30 ∷
   rw 2 q26 ∷
   rw 0 q27 ∷
   rw 1 q27 ∷
   rw 2 q28 ∷
   rw 0 q31 ∷ []) Eq.refl

-- CCZ(2,1,3) passes split Gad(t=1, W=(0, 2, 3), d=KSSKd, e=1): 9 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ = derive (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ [])
  (rw 0 q12 ∷
   rw 3 q13 ∷
   rw 6 q13 ∷
   rw 9 q14 ∷
   rw 12 q70 ∷
   rw 22 q12 ∷
   rw 25 q16 ∷
   rw 28 q16 ∷
   rw 31 q14 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = sE 2014 lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS13

-- pass [CS13] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 1 steps
lem-pass-CS13-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (CS13 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (CS13 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ [])
  (rw⁻ 0 q76 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = sE 2012 lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CCZ123

-- pass [CCZ123] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 1 steps
lem-pass-CCZ123-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (CCZ123 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (CCZ123 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q77 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 1149 W
  q79 : Eqn
  q79 = sE 360 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS13
  q80 : Eqn
  q80 = sE 361 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CSd13
  q81 : Eqn
  q81 = sE 671 lem-distribute-Gad⟨t≡1-W≡⟨0-2⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2]: 18 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 32 q78 ∷
   rw 37 q78 ∷
   rw 42 q78 ∷
   rw 29 q60 ∷
   rw 30 q61 ∷
   rw 31 q21 ∷
   rw 29 q62 ∷
   rw 30 q63 ∷
   rw 35 q60 ∷
   rw 36 q64 ∷
   rw 37 q21 ∷
   rw 35 q65 ∷
   rw 36 q63 ∷
   rw 0 q79 ∷
   rw 1 q66 ∷
   rw 6 q80 ∷
   rw 7 q66 ∷
   rw⁻ 0 q81 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = sE 2005 lem-pass-CCZ123-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2

-- CCZ(2,1,3) passes split Gad(t=1, W=(0, 2), d=SdKdSS, e=-1): 9 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (CCZ123 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ = derive (CCZ123 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ [])
  (rw 0 q16 ∷
   rw 3 q14 ∷
   rw 6 q13 ∷
   rw 9 q13 ∷
   rw 12 q82 ∷
   rw 20 q16 ∷
   rw 23 q16 ∷
   rw 26 q12 ∷
   rw 29 q13 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = sE 441 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS13
  q84 : Eqn
  q84 = sE 442 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-CSd13

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2]: 18 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 34 q78 ∷
   rw 39 q78 ∷
   rw 44 q78 ∷
   rw 31 q60 ∷
   rw 32 q61 ∷
   rw 33 q21 ∷
   rw 31 q62 ∷
   rw 32 q63 ∷
   rw 37 q60 ∷
   rw 38 q64 ∷
   rw 39 q21 ∷
   rw 37 q65 ∷
   rw 38 q63 ∷
   rw 0 q83 ∷
   rw 1 q71 ∷
   rw 6 q84 ∷
   rw 7 q71 ∷
   rw⁻ 0 q81 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 1419 W
  q86 : Eqn
  q86 = sE 2004 lem-hyb-sym-23-at0321
  q87 : Eqn
  q87 = sE 2003 lem-LF-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK20-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-S2-CK20-at-1
  q88 : Eqn
  q88 = sE 687 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CX10-X1
  q89 : Eqn
  q89 = sE 689 lem-pass-TOFF213-vs-X1-CX10-X1
  q90 : Eqn
  q90 = sE 688 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-CX10-X1
  q91 : Eqn
  q91 = sE 686 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CX10-X1
  q92 : Eqn
  q92 = sE 2003 lem-LF-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK20-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-S2-CK20-at-1
  q93 : Eqn
  q93 = sE 2004 lem-hyb-sym-23-at0321

-- Z passes X0 CS03 CS03 CK30 CS03 CX32 CS: 11 steps
lem-Z-passes-X0-CS03-CS03-CK30-CS03-CX32-CS : ⟪ (X1 ∷ CX10 ∷ X1 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S1 ∷ CK10 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S1 ∷ CK10 ∷ X0 ∷ X1 ∷ CX10 ∷ X1 ∷ []) ⟫ʷ
lem-Z-passes-X0-CS03-CS03-CK30-CS03-CX32-CS = derive (X1 ∷ CX10 ∷ X1 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S1 ∷ CK10 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S1 ∷ CK10 ∷ X0 ∷ X1 ∷ CX10 ∷ X1 ∷ [])
  (rw 0 q85 ∷
   rw 4 q86 ∷
   rw 4 q87 ∷
   rw⁻ 1 q88 ∷
   rw⁻ 30 q89 ∷
   rw⁻ 31 q90 ∷
   rw⁻ 62 q89 ∷
   rw⁻ 63 q91 ∷
   rw⁻ 1 q92 ∷
   rw⁻ 1 q93 ∷
   rw 81 q85 ∷ []) Eq.refl
