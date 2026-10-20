{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D743 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D008 W using (lem-pass-CS12-vs-CS03 ; lem-pass-S0-vs-CSd03 ; lem-pass-Sd0-vs-CS03 ; lem-pass-Sd0-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D009 W using (lem-pass-CCZ012-vs-Sd0 ; lem-pass-CS12-vs-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D010 W using (lem-K0-PPw3-Kd0 ; lem-cocycle-KdSK∣S ; lem-cocycle-KdSK∣SKdSK ; lem-cocycle-S∣KdSK ; lem-cocycle-S∣KdSKS ; lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D014 W using (lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D510 W using (lem-ROT-form ; lem-pass-CCZ012-vs-CS03 ; lem-pass-CS12-vs-TOFF012-CS03-TOFF012 ; lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D538 W using (lem-C⟨U'⟩≡eps ; lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012 ; lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 ; lem-pass-S0-vs-TOFF012-CS03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D541 W using (lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D596 W using (lem-ROT≡cF ; lem-pass-CKd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 ; lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-CS21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 ; lem-pass-CSd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
open import Examples.Groups.Clifford+CS.Four.D.D597 W using (lem-pass-CKd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3)
open import Examples.Groups.Clifford+CS.Four.D.D623 W using (lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D681 W using (lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D682 W using (lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D683 W using (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
open import Examples.Groups.Clifford+CS.Four.D.D701 W using (lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D702 W using (lem-pass-X3-CSd31-X3-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D712 W using (lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 ; lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 ; lem-pass-X3-CK30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 ; lem-pass-X3-CKd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 ; lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 ; lem-pass-X3-CS30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 ; lem-pass-X3-CSd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2)
open import Examples.Groups.Clifford+CS.Four.D.D713 W using (lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-3 ; lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-CSd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
open import Examples.Groups.Clifford+CS.Four.D.D714 W using (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D715 W using (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
open import Examples.Groups.Clifford+CS.Four.D.D726 W using (lem-PP-flip ; lem-PP2≡E ; lem-PPi2≡E ; lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF013-CS02-TOFF013-CSd02)
open import Examples.Groups.Clifford+CS.Four.D.D727 W using (lem-pass-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02)
open import Examples.Groups.Clifford+CS.Four.D.D728 W using (lem-pass-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3-vs-TOFF013-CS02-TOFF013-CSd02)
open import Examples.Groups.Clifford+CS.Four.D.D729 W using (lem-pass-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02)
open import Examples.Groups.Clifford+CS.Four.D.D730 W using (lem-CAw-KdSK-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ ; lem-CAw-S-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ ; lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2 ; lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 ; lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2 ; lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3 ; lem-pass-CCZ012-X3-K0-CS03-Kd0-X3-CCZ012-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 ; lem-pass-CK21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 ; lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-CSd03-vs-TOFF012-CS03-TOFF012 ; lem-pass-X1-CSd10-X1-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X1-CSd10-X1-vs-S0-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-Sd0 ; lem-pass-X2-CKd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 ; lem-pass-X2-CKd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-CKd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 ; lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-CS21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-CS21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 ; lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D731 W using (lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 ; lem-pass-CS32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 ; lem-pass-CSd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 ; lem-pass-X3-CS31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 ; lem-pass-X3-CS32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 ; lem-pass-X3-CSd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 ; lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-TOFF013-CS02-TOFF013-CSd02)
open import Examples.Groups.Clifford+CS.Four.D.D732 W using (lem-pass-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3-vs-TOFF013-CS02-TOFF013-CSd02 ; lem-pass-X3-CSd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0)
open import Examples.Groups.Clifford+CS.Four.D.D733 W using (lem-pass-X3-CKd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0)

private
  q1 : Eqn
  q1 = eqn (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (lem-ROT≡cF)
  q2 : Eqn
  q2 = eqn (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ []) (lem-ROT-form)
  q3 : Eqn
  q3 = eqn (K0⁻ ∷ K0 ∷ []) [] (wn 1339 W)
  q4 : Eqn
  q4 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) [] (wn 2402 W)
  q5 : Eqn
  q5 = eqn (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) [] (wn 2403 W)
  q6 : Eqn
  q6 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CCZ123 ∷ []) (lem-PPi2≡E)
  q7 : Eqn
  q7 = eqn (K0⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (CCZ))
  q8 : Eqn
  q8 = eqn (S0⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) (CCZ))
  q9 : Eqn
  q9 = eqn (K0 ∷ CCZ123 ∷ []) (CCZ123 ∷ K0 ∷ []) (low₁-comm (K) (CCZ))
  q10 : Eqn
  q10 = eqn (K0⁻ ∷ S0 ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) [] (wn 2404 W)
  q11 : Eqn
  q11 = eqn (Sw12 ∷ CCZ123 ∷ Sw12 ∷ []) (CCZ123 ∷ []) (wn 2405 W)
  q12 : Eqn
  q12 = eqn (Sw23 ∷ CCZ123 ∷ Sw23 ∷ []) (CCZ123 ∷ []) (wn 1880 W)
  q13 : Eqn
  q13 = eqn (K0 ∷ K0⁻ ∷ []) [] (wn 1846 W)

-- ROT2=E: 17 steps
lem-ROT2≡E : ⟪ (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
lem-ROT2≡E = derive (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ123 ∷ [])
  (rw 0 q1 ∷
   rw 4 q1 ∷
   rw 0 q2 ∷
   rw 18 q2 ∷
   rw 17 q3 ∷
   rw 14 q4 ∷
   rw 11 q5 ∷
   rw 7 q6 ∷
   rw⁻ 7 q7 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q9 ∷
   rw 4 q10 ∷
   rw 3 q11 ∷
   rw 2 q12 ∷
   rw 1 q11 ∷
   rw 0 q9 ∷
   rw 1 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (CCZ123 ∷ []) (lem-PP2≡E)
  q15 : Eqn
  q15 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)

-- PP4: 3 steps
lem-PP4 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-PP4 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) []
  (rw 0 q14 ∷
   rw 1 q14 ∷
   rw 0 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = eqn (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  (rw⁻ 0 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = eqn (X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ []) lem-pass-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [X1 X3 TOFF102 CS13 TOFF102 CSd13 X1 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 : ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 = derive (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  (rw⁻ 0 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = eqn (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) lem-pass-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = derive (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  (rw⁻ 0 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ []) lem-pass-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [X0 X1 X3 TOFF102 CS13 TOFF102 CSd13 X0 X1 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 : ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 = derive (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  (rw⁻ 0 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (Toff012 ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ []) (low₃-comm (Toff) (X))
  q21 : Eqn
  q21 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q22 : Eqn
  q22 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q23 : Eqn
  q23 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q24 : Eqn
  q24 = eqn (X2 ∷ CS02 ∷ []) (S0 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1962 W)
  q25 : Eqn
  q25 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q26 : Eqn
  q26 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q27 : Eqn
  q27 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ []) (CS02 ∷ S0⁻ ∷ []) (wn 2406 W)
  q28 : Eqn
  q28 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q29 : Eqn
  q29 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q30 : Eqn
  q30 = eqn (Toff012 ∷ S0 ∷ Toff012 ∷ []) (S0 ∷ CS12 ∷ CCZ012 ∷ []) (wn 2407 W)
  q31 : Eqn
  q31 = eqn (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) lem-pass-CSd03-vs-TOFF012-CS03-TOFF012
  q32 : Eqn
  q32 = eqn (S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ S0 ∷ []) lem-pass-S0-vs-TOFF012-CS03-TOFF012
  q33 : Eqn
  q33 = eqn (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS12 ∷ []) lem-pass-CS12-vs-TOFF012-CS03-TOFF012
  q34 : Eqn
  q34 = eqn (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CCZ012 ∷ []) lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012
  q35 : Eqn
  q35 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)
  q36 : Eqn
  q36 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)
  q37 : Eqn
  q37 = eqn (S0 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ S0 ∷ []) lem-pass-S0-vs-CSd03
  q38 : Eqn
  q38 = eqn (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS03)
  q39 : Eqn
  q39 = eqn (CCZ012 ∷ S0⁻ ∷ []) (S0⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-Sd0)
  q40 : Eqn
  q40 = eqn (CS12 ∷ CS03 ∷ []) (CS03 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CS03)
  q41 : Eqn
  q41 = eqn (CS12 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS12 ∷ []) (lem-pass-CS12-vs-Sd0)
  q42 : Eqn
  q42 = eqn (S0⁻ ∷ CS03 ∷ []) (CS03 ∷ S0⁻ ∷ []) lem-pass-Sd0-vs-CS03
  q43 : Eqn
  q43 = eqn (S0⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ S0⁻ ∷ []) lem-pass-Sd0-vs-CSd03
  q44 : Eqn
  q44 = eqn (S0 ∷ S0⁻ ∷ []) [] (wn 1728 W)
  q45 : Eqn
  q45 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)

-- merge3: 52 steps
lem-merge3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ012 ∷ []) ⟫ʷ
lem-merge3 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (CS12 ∷ CCZ012 ∷ [])
  (rw⁻ 4 q20 ∷
   rw 7 q21 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q22 ∷
   rw 5 q23 ∷
   rw 6 q24 ∷
   rw⁻ 5 q25 ∷
   rw 8 q21 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q26 ∷
   rw 8 q22 ∷
   rw⁻ 7 q20 ∷
   rw 11 q21 ∷
   rw 10 q23 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q22 ∷
   rw 8 q23 ∷
   rw 9 q27 ∷
   rw 10 q21 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q28 ∷
   rw 10 q22 ∷
   rw 6 q29 ∷
   rw 4 q30 ∷
   rw⁻ 0 q31 ∷
   rw⁻ 1 q32 ∷
   rw⁻ 2 q33 ∷
   rw⁻ 3 q34 ∷
   rw 6 q35 ∷
   rw 7 q21 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q22 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q22 ∷
   rw 6 q36 ∷
   rw 5 q22 ∷
   rw 4 q35 ∷
   rw⁻ 0 q37 ∷
   rw 3 q38 ∷
   rw 4 q39 ∷
   rw 2 q40 ∷
   rw 3 q41 ∷
   rw⁻ 2 q42 ∷
   rw⁻ 1 q43 ∷
   rw 0 q44 ∷
   rw 2 q21 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q22 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q22 ∷
   rw 1 q45 ∷
   rw 0 q22 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn [] (K0⁻ ∷ K0 ∷ []) (wn 54 W)
  q47 : Eqn
  q47 = eqn (K0 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0⁻ ∷ []) (CCZ012 ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ CCZ012 ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ []) (lem-K0-PPw3-Kd0)
  q48 : Eqn
  q48 = eqn (CCZ012 ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ CCZ012 ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ CCZ012 ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ []) (lem-pass-CCZ012-X3-K0-CS03-Kd0-X3-CCZ012-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q49 : Eqn
  q49 = eqn (K0 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0⁻ ∷ []) (CCZ012 ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ CCZ012 ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ []) lem-K0-PPw3-Kd0

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [Kd0 TOFF012 CS03 TOFF012 CSd03 K0]: 5 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = derive (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 0 q46 ∷
   rw 1 q47 ∷
   rw 1 q48 ∷
   rw⁻ 5 q49 ∷
   rw 12 q3 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) (lem-cocycle-S∣KdSKS)
  q51 : Eqn
  q51 = eqn (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) (lem-cocycle-KdSK∣S)
  q52 : Eqn
  q52 = eqn (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) [] (lem-C⟨U'⟩≡eps)
  q53 : Eqn
  q53 = eqn (CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (lem-CAw-KdSK-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩)
  q54 : Eqn
  q54 = eqn (CS03 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ CS03⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ []) (lem-CAw-S-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩)

-- C(SU'S): 5 steps
lem-C⟨SU'S⟩ : ⟪ (Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
lem-C⟨SU'S⟩ = derive (Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ [])
  (rw 0 q50 ∷
   rw 5 q51 ∷
   rw 5 q52 ∷
   rw 5 q53 ∷
   rw 4 q54 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) (lem-cocycle-KdSK∣SKdSK)
  q56 : Eqn
  q56 = eqn (Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) (lem-cocycle-S∣KdSK)

-- C(U'SU'): 12 steps
lem-C⟨U'SU'⟩ : ⟪ (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ
lem-C⟨U'SU'⟩ = derive (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ [])
  (rw 0 q55 ∷
   rw 0 q52 ∷
   rw 3 q56 ∷
   rw 8 q52 ∷
   rw 9 q21 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q22 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q22 ∷
   rw 8 q36 ∷
   rw 7 q22 ∷
   rw 0 q53 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn [] (CS02 ∷ CS02⁻ ∷ []) (wn 1357 W)
  q58 : Eqn
  q58 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)
  q59 : Eqn
  q59 = eqn (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) lem-PP-flip
  q60 : Eqn
  q60 = eqn (X0 ∷ X0 ∷ []) [] (wn 387 W)

-- PP-flip ^-1: 35 steps
lem-PP-flip-ᵖ-1 : ⟪ (X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-PP-flip-ᵖ-1 = derive (X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 6 q21 ∷
   rw 7 q57 ∷
   rw 8 q21 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q21 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q22 ∷
   rw 7 q29 ∷
   rw 8 q21 ∷
   rw 9 q58 ∷
   rw 10 q21 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 11 q21 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q22 ∷
   rw 9 q29 ∷
   rw⁻ 6 q59 ∷
   rw 5 q60 ∷
   rw 4 q35 ∷
   rw 5 q21 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q22 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q22 ∷
   rw 4 q45 ∷
   rw 3 q22 ∷
   rw 2 q35 ∷
   rw 3 q21 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q22 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q22 ∷
   rw 2 q36 ∷
   rw 1 q22 ∷
   rw 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q62 : Eqn
  q62 = eqn (X1 ∷ Sw01 ∷ []) (Sw01 ∷ X0 ∷ []) (wn 217 W)
  q63 : Eqn
  q63 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q64 : Eqn
  q64 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q65 : Eqn
  q65 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q66 : Eqn
  q66 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q67 : Eqn
  q67 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q68 : Eqn
  q68 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q69 : Eqn
  q69 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q70 : Eqn
  q70 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q71 : Eqn
  q71 = eqn (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-PP-flip)
  q72 : Eqn
  q72 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q73 : Eqn
  q73 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q74 : Eqn
  q74 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q75 : Eqn
  q75 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q76 : Eqn
  q76 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q77 : Eqn
  q77 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q78 : Eqn
  q78 = eqn (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 274 W)
  q79 : Eqn
  q79 = eqn (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) (wn 322 W)
  q80 : Eqn
  q80 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- PP-flip @1023: 69 steps
lem-PP-flip-at1023 : ⟪ (X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-PP-flip-at1023 = derive (X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  (rw 6 q61 ∷
   rw 5 q62 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q63 ∷
   rw 5 q64 ∷
   rw⁻ 4 q63 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 10 q65 ∷
   rw 9 q66 ∷
   rw 8 q67 ∷
   rw 7 q68 ∷
   rw 6 q64 ∷
   rw 5 q68 ∷
   rw 4 q69 ∷
   rw 3 q66 ∷
   rw 4 q70 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q63 ∷
   rw 3 q69 ∷
   rw⁻ 2 q63 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 8 q65 ∷
   rw 7 q66 ∷
   rw 6 q67 ∷
   rw 5 q68 ∷
   rw 4 q64 ∷
   rw 3 q68 ∷
   rw 2 q69 ∷
   rw 1 q66 ∷
   rw 2 q70 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 0 q62 ∷
   rw 1 q71 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 0 q63 ∷
   rw 1 q72 ∷
   rw 2 q63 ∷
   re 0 3 (CS13 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 1 q73 ∷
   rw 2 q74 ∷
   rw 3 q75 ∷
   rw 4 q76 ∷
   rw 5 q75 ∷
   rw 6 q72 ∷
   rw 7 q73 ∷
   rw 8 q77 ∷
   rw 1 q78 ∷
   re 1 8 (Toff102 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q63 ∷
   rw 3 q79 ∷
   rw 4 q63 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 3 q73 ∷
   rw 4 q74 ∷
   rw 5 q75 ∷
   rw 6 q76 ∷
   rw 7 q75 ∷
   rw 8 q72 ∷
   rw 9 q73 ∷
   rw 10 q77 ∷
   rw 3 q78 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 4 q80 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (CCZ123 ∷ []) lem-PP2≡E

-- E PPi: 17 steps
lem-E-PPi : ⟪ (CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-E-PPi = derive (CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q81 ∷
   rw 9 q21 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q22 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q22 ∷
   rw 8 q45 ∷
   rw 7 q22 ∷
   rw 6 q35 ∷
   rw 7 q21 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q22 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q22 ∷
   rw 6 q36 ∷
   rw 5 q22 ∷
   rw 4 q35 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = eqn (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3)
  q83 : Eqn
  q83 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2)
  q84 : Eqn
  q84 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2)
  q85 : Eqn
  q85 = eqn (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2)
  q86 : Eqn
  q86 = eqn (X3 ∷ CK30 ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2)
  q87 : Eqn
  q87 = eqn (X3 ∷ CS03 ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2)
  q88 : Eqn
  q88 = eqn (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3

-- pass [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 7 steps
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ [])
  (rw 0 q82 ∷
   rw 15 q83 ∷
   rw 12 q84 ∷
   rw 6 q85 ∷
   rw 3 q86 ∷
   rw 0 q87 ∷
   rw⁻ 6 q88 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = eqn [] (X3 ∷ X3 ∷ []) (wn 225 W)
  q90 : Eqn
  q90 = eqn (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q91 : Eqn
  q91 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [TOFF102 CS13 TOFF102 CSd13]: 37 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ [])
  (rw 10 q89 ∷
   rw 11 q29 ∷
   rw 12 q21 ∷
   rw 13 q57 ∷
   rw 14 q21 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q21 ∷
   re 13 3 (CS03⁻ ∷ []) ∷
   rw 14 q22 ∷
   rw 13 q29 ∷
   rw 14 q21 ∷
   rw 15 q58 ∷
   rw 16 q21 ∷
   re 14 3 (CS03⁻ ∷ []) ∷
   rw 17 q21 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q22 ∷
   rw 15 q89 ∷
   rw⁻ 6 q90 ∷
   rw 5 q91 ∷
   rw 4 q35 ∷
   rw 5 q21 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q22 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q22 ∷
   rw 4 q45 ∷
   rw 3 q22 ∷
   rw 2 q35 ∷
   rw 3 q21 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q22 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q22 ∷
   rw 2 q36 ∷
   rw 1 q22 ∷
   rw 0 q91 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q93 : Eqn
  q93 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q94 : Eqn
  q94 = eqn (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q95 : Eqn
  q95 = eqn (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q96 : Eqn
  q96 = eqn (X3 ∷ CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03)

-- pass [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3] [TOFF012 CS03 TOFF012 CSd03]: 7 steps
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ [])
  (rw 0 q82 ∷
   rw 15 q92 ∷
   rw 12 q93 ∷
   rw 6 q94 ∷
   rw 3 q95 ∷
   rw 0 q96 ∷
   rw⁻ 4 q88 ∷ []) Eq.refl

-- c -> ci E: 17 steps
lem-c--⟶-ci-E : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-c--⟶-ci-E = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CCZ123 ∷ [])
  (rw 0 q21 ∷
   rw 1 q57 ∷
   rw 2 q21 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q21 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q22 ∷
   rw 1 q29 ∷
   rw 2 q21 ∷
   rw 3 q58 ∷
   rw 4 q21 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 5 q21 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q22 ∷
   rw 3 q29 ∷
   rw 4 q14 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-3)
  q98 : Eqn
  q98 = eqn (CS03 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ []) lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q99 : Eqn
  q99 = eqn (CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ []) lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q100 : Eqn
  q100 = eqn (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q101 : Eqn
  q101 = eqn (CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ []) lem-pass-CKd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q102 : Eqn
  q102 = eqn (CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ []) lem-pass-CSd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q103 : Eqn
  q103 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ []) lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-3

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ [])
  (rw 6 q97 ∷
   rw⁻ 0 q98 ∷
   rw⁻ 1 q99 ∷
   rw 2 q100 ∷
   rw⁻ 6 q101 ∷
   rw⁻ 7 q102 ∷
   rw⁻ 0 q103 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (CS02 ∷ CK20 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2)
  q105 : Eqn
  q105 = eqn (CS02 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ []) lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q106 : Eqn
  q106 = eqn (CK20 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ []) lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q107 : Eqn
  q107 = eqn (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q108 : Eqn
  q108 = eqn (CK20⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20⁻ ∷ []) lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q109 : Eqn
  q109 = eqn (CS02⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ []) lem-pass-CSd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q110 : Eqn
  q110 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (CS02 ∷ CK20 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK20⁻ ∷ CS02⁻ ∷ []) lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2

-- pass [X2 CS03 TOFF012 CSd03 TOFF012 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ [])
  (rw 6 q104 ∷
   rw⁻ 0 q105 ∷
   rw⁻ 1 q106 ∷
   rw 2 q107 ∷
   rw⁻ 6 q108 ∷
   rw⁻ 7 q109 ∷
   rw⁻ 0 q110 ∷ []) Eq.refl

private
  q111 : Eqn
  q111 = eqn (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2)
  q112 : Eqn
  q112 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
  q113 : Eqn
  q113 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
  q114 : Eqn
  q114 = eqn (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
  q115 : Eqn
  q115 = eqn (X2 ∷ CK20 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
  q116 : Eqn
  q116 = eqn (X2 ∷ CS02 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
  q117 : Eqn
  q117 = eqn (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2

-- pass [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ [])
  (rw 0 q111 ∷
   rw 15 q112 ∷
   rw 12 q113 ∷
   rw 6 q114 ∷
   rw 3 q115 ∷
   rw 0 q116 ∷
   rw⁻ 8 q117 ∷ []) Eq.refl

private
  q118 : Eqn
  q118 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q119 : Eqn
  q119 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q120 : Eqn
  q120 = eqn (K0 ∷ X3 ∷ []) (X3 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑ ↑)))
  q121 : Eqn
  q121 = eqn (K0 ∷ X2 ∷ []) (X2 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑)))
  q122 : Eqn
  q122 = eqn (S0⁻ ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑)))
  q123 : Eqn
  q123 = eqn (K0⁻ ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑)))
  q124 : Eqn
  q124 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q125 : Eqn
  q125 = eqn (K0⁻ ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q126 : Eqn
  q126 = eqn (S0 ∷ K0 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ CS02 ∷ CK20 ∷ []) (wn 2222 W)
  q127 : Eqn
  q127 = eqn (K0⁻ ∷ S0⁻ ∷ []) (CK20⁻ ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2223 W)
  q128 : Eqn
  q128 = eqn (CK20 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK20 ∷ []) (lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
  q129 : Eqn
  q129 = eqn (CS02 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS02 ∷ []) (lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
  q130 : Eqn
  q130 = eqn (CS02 ∷ CK20 ∷ CK20⁻ ∷ CS02⁻ ∷ []) [] (wn 2224 W)

-- ca-split Gad(t=0, W=(2, 3), d=SK, e=-1) 2: 13 steps
lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 : ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 = derive (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw⁻ 1 q118 ∷
   rw⁻ 0 q119 ∷
   rw⁻ 2 q120 ∷
   rw⁻ 1 q121 ∷
   rw 9 q122 ∷
   rw 8 q123 ∷
   rw 10 q124 ∷
   rw 9 q125 ∷
   rw 0 q126 ∷
   rw 16 q127 ∷
   rw 7 q128 ∷
   rw 6 q129 ∷
   rw 14 q130 ∷ []) Eq.refl

private
  q131 : Eqn
  q131 = eqn (CK20⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1464 W)
  q132 : Eqn
  q132 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q133 : Eqn
  q133 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
  q134 : Eqn
  q134 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ []) (wn 1465 W)

-- pass [CKd20] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (CK20⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (CK20⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK20⁻ ∷ [])
  (rw 0 q131 ∷
   rw 9 q132 ∷
   rw 1 q133 ∷
   rw 7 q134 ∷
   rw⁻ 6 q132 ∷ []) Eq.refl

private
  q135 : Eqn
  q135 = eqn (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2)
  q136 : Eqn
  q136 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q137 : Eqn
  q137 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q138 : Eqn
  q138 = eqn (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q139 : Eqn
  q139 = eqn (X2 ∷ CK21 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q140 : Eqn
  q140 = eqn (X2 ∷ CS12 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q141 : Eqn
  q141 = eqn (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2

-- pass [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ [])
  (rw 0 q135 ∷
   rw 15 q136 ∷
   rw 12 q137 ∷
   rw 6 q138 ∷
   rw 3 q139 ∷
   rw 0 q140 ∷
   rw⁻ 8 q141 ∷ []) Eq.refl

private
  q142 : Eqn
  q142 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q143 : Eqn
  q143 = eqn (S1 ∷ X2 ∷ []) (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X))
  q144 : Eqn
  q144 = eqn (K1 ∷ X3 ∷ []) (X3 ∷ K1 ∷ []) (low-comm ((K ↑)) ((X ↑)))
  q145 : Eqn
  q145 = eqn (K1 ∷ X2 ∷ []) (X2 ∷ K1 ∷ []) (low-comm ((K ↑)) (X))
  q146 : Eqn
  q146 = eqn (S1⁻ ∷ X2 ∷ []) (X2 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (X))
  q147 : Eqn
  q147 = eqn (K1⁻ ∷ X2 ∷ []) (X2 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (X))
  q148 : Eqn
  q148 = eqn (S1⁻ ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) ((X ↑)))
  q149 : Eqn
  q149 = eqn (K1⁻ ∷ X3 ∷ []) (X3 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) ((X ↑)))
  q150 : Eqn
  q150 = eqn (S1 ∷ K1 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ CS12 ∷ CK21 ∷ []) (wn 2228 W)
  q151 : Eqn
  q151 = eqn (K1⁻ ∷ S1⁻ ∷ []) (CK21⁻ ∷ CS12⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 2229 W)
  q152 : Eqn
  q152 = eqn (CK21 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CK21 ∷ []) (lem-pass-CK21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3)
  q153 : Eqn
  q153 = eqn (CS12 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS12 ∷ []) (lem-pass-CS21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3)
  q154 : Eqn
  q154 = eqn (CS12 ∷ CK21 ∷ CK21⁻ ∷ CS12⁻ ∷ []) [] (wn 2230 W)

-- ca-split Gad(t=1, W=(2, 3), d=SK, e=1) 2: 13 steps
lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2 : ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2 = derive (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw⁻ 1 q142 ∷
   rw⁻ 0 q143 ∷
   rw⁻ 2 q144 ∷
   rw⁻ 1 q145 ∷
   rw 9 q146 ∷
   rw 8 q147 ∷
   rw 10 q148 ∷
   rw 9 q149 ∷
   rw 0 q150 ∷
   rw 16 q151 ∷
   rw 7 q152 ∷
   rw 6 q153 ∷
   rw 14 q154 ∷ []) Eq.refl

private
  q155 : Eqn
  q155 = eqn (CS01 ∷ []) (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1819 W)
  q156 : Eqn
  q156 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q157 : Eqn
  q157 = eqn (S0 ∷ S0 ∷ K0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ []) (wn 2408 W)
  q158 : Eqn
  q158 = eqn (K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ []) (wn 2409 W)
  q159 : Eqn
  q159 = eqn (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (CS01 ∷ []) (wn 1820 W)

-- CA CS10 Gad(t=0, W=(), d=SK, e=-1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ : ⟪ (CS01 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ = derive (CS01 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CS01 ∷ [])
  (rw 0 q155 ∷
   rw 1 q156 ∷
   rw 0 q157 ∷
   rw 7 q158 ∷
   rw 10 q159 ∷ []) Eq.refl

private
  q160 : Eqn
  q160 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-S0-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-Sd0)
  q161 : Eqn
  q161 = eqn (S0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (S0⁻ ∷ K0 ∷ []) (wn 2410 W)
  q162 : Eqn
  q162 = eqn (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0 ∷ S0 ∷ []) (wn 2411 W)

-- CA CS10 Gad(t=0, W=(), d=SSK, e=-1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSK-e≡-1⟩ : ⟪ (CS01 ∷ S0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSK-e≡-1⟩ = derive (CS01 ∷ S0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ CS01 ∷ [])
  (rw 0 q155 ∷
   rw 1 q160 ∷
   rw 0 q161 ∷
   rw 6 q162 ∷
   rw 8 q159 ∷ []) Eq.refl

private
  q163 : Eqn
  q163 = eqn (X2 ∷ CS02 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q164 : Eqn
  q164 = eqn (X2 ∷ CK20 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q165 : Eqn
  q165 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
  q166 : Eqn
  q166 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q167 : Eqn
  q167 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2]: 7 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 4 q111 ∷
   rw⁻ 0 q163 ∷
   rw⁻ 3 q164 ∷
   rw 6 q165 ∷
   rw⁻ 12 q166 ∷
   rw⁻ 15 q167 ∷
   rw⁻ 0 q117 ∷ []) Eq.refl

private
  q168 : Eqn
  q168 = eqn (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3)
  q169 : Eqn
  q169 = eqn (X3 ∷ CS13 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q170 : Eqn
  q170 = eqn (X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q171 : Eqn
  q171 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3)
  q172 : Eqn
  q172 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q173 : Eqn
  q173 = eqn (X3 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) lem-pass-X3-CSd31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q174 : Eqn
  q174 = eqn (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 7 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 4 q168 ∷
   rw⁻ 0 q169 ∷
   rw⁻ 3 q170 ∷
   rw 6 q171 ∷
   rw⁻ 12 q172 ∷
   rw⁻ 15 q173 ∷
   rw⁻ 0 q174 ∷ []) Eq.refl

private
  q175 : Eqn
  q175 = eqn (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q175 ∷ []) Eq.refl

private
  q176 : Eqn
  q176 = eqn (CK21⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1478 W)
  q177 : Eqn
  q177 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
  q178 : Eqn
  q178 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ []) (wn 1479 W)

-- pass [CKd21] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 3 steps
lem-pass-CKd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (CK21⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21⁻ ∷ []) ⟫ʷ
lem-pass-CKd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = derive (CK21⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21⁻ ∷ [])
  (rw 0 q176 ∷
   rw 1 q177 ∷
   rw 9 q178 ∷ []) Eq.refl

private
  q179 : Eqn
  q179 = eqn (CS12 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1474 W)
  q180 : Eqn
  q180 = eqn (X2 ∷ CS12 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
  q181 : Eqn
  q181 = eqn (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ []) (wn 1475 W)

-- pass [CS21] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 3 steps
lem-pass-CS21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (CS12 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = derive (CS12 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ [])
  (rw 0 q179 ∷
   rw 1 q180 ∷
   rw 9 q181 ∷ []) Eq.refl

private
  q182 : Eqn
  q182 = eqn (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q182 ∷ []) Eq.refl

private
  q183 : Eqn
  q183 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3)

-- pass [CKd21] [X2 X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : ⟪ (CK21⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK21⁻ ∷ []) ⟫ʷ
lem-pass-CKd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = derive (CK21⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK21⁻ ∷ [])
  (rw 0 q176 ∷
   rw 13 q132 ∷
   rw 1 q183 ∷
   rw 11 q178 ∷
   rw⁻ 10 q132 ∷ []) Eq.refl

private
  q184 : Eqn
  q184 = eqn (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3)

-- pass [CS21] [X2 X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CS21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : ⟪ (CS12 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = derive (CS12 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CS12 ∷ [])
  (rw 0 q179 ∷
   rw 13 q132 ∷
   rw 1 q184 ∷
   rw 11 q181 ∷
   rw⁻ 10 q132 ∷ []) Eq.refl

-- cls 0000PP0 1000PP0 = e: 17 steps
lem-cls-0000PP0-1000PP0-≡-e : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-cls-0000PP0-1000PP0-≡-e = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) []
  (rw 4 q71 ∷
   rw 5 q21 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q22 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q22 ∷
   rw 4 q45 ∷
   rw 3 q22 ∷
   rw 2 q35 ∷
   rw 3 q21 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q22 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q22 ∷
   rw 2 q36 ∷
   rw 1 q22 ∷
   rw 0 q35 ∷ []) Eq.refl

private
  q185 : Eqn
  q185 = eqn (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3)
  q186 : Eqn
  q186 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q187 : Eqn
  q187 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q188 : Eqn
  q188 = eqn (X3 ∷ CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q189 : Eqn
  q189 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
  q190 : Eqn
  q190 = eqn (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q191 : Eqn
  q191 = eqn (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ []) lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 11 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 4 q185 ∷
   rw⁻ 0 q186 ∷
   rw⁻ 3 q187 ∷
   rw⁻ 6 q188 ∷
   rw⁻ 9 q188 ∷
   rw 12 q189 ∷
   rw⁻ 18 q186 ∷
   rw⁻ 21 q186 ∷
   rw⁻ 24 q190 ∷
   rw⁻ 27 q188 ∷
   rw⁻ 0 q191 ∷ []) Eq.refl

private
  q192 : Eqn
  q192 = eqn (S2⁻ ∷ X3 ∷ []) (X3 ∷ S2⁻ ∷ []) (low₃-comm (((S • S • S) ↑ ↑)) (X))
  q193 : Eqn
  q193 = eqn (K2⁻ ∷ X3 ∷ []) (X3 ∷ K2⁻ ∷ []) (low₃-comm (((K • iI) ↑ ↑)) (X))
  q194 : Eqn
  q194 = eqn (S2 ∷ X3 ∷ []) (X3 ∷ S2 ∷ []) (low₃-comm ((S ↑ ↑)) (X))
  q195 : Eqn
  q195 = eqn (K2 ∷ X3 ∷ []) (X3 ∷ K2 ∷ []) (low₃-comm ((K ↑ ↑)) (X))
  q196 : Eqn
  q196 = eqn (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ []) (wn 2412 W)
  q197 : Eqn
  q197 = eqn (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (CS23⁻ ∷ CS23⁻ ∷ CK32 ∷ CS23 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (wn 2413 W)
  q198 : Eqn
  q198 = eqn (CS23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ []) (lem-pass-CS32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3)
  q199 : Eqn
  q199 = eqn (CK32⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK32⁻ ∷ []) (lem-pass-CKd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3)
  q200 : Eqn
  q200 = eqn (CS23⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23⁻ ∷ []) (lem-pass-CSd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3)
  q201 : Eqn
  q201 = eqn (CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ CS23⁻ ∷ CS23⁻ ∷ CK32 ∷ CS23 ∷ []) [] (wn 2414 W)

-- ca-split Gad(t=2, W=(3,), d=SdKdSS, e=-1) 3: 15 steps
lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 : ⟪ (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 = derive (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  (rw⁻ 0 q192 ∷
   rw⁻ 1 q193 ∷
   rw⁻ 2 q194 ∷
   rw⁻ 3 q194 ∷
   rw 12 q194 ∷
   rw 11 q195 ∷
   rw 10 q192 ∷
   rw 9 q192 ∷
   rw 0 q196 ∷
   rw 22 q197 ∷
   rw 15 q198 ∷
   rw 14 q198 ∷
   rw 13 q199 ∷
   rw 12 q200 ∷
   rw 18 q201 ∷ []) Eq.refl

private
  q202 : Eqn
  q202 = eqn (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [X3 TOFF201 CS23 TOFF201 CSd23 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = derive (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  (rw⁻ 0 q202 ∷ []) Eq.refl

private
  q203 : Eqn
  q203 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q204 : Eqn
  q204 = eqn (CS13 ∷ X3 ∷ []) (X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (wn 2111 W)
  q205 : Eqn
  q205 = eqn (X3 ∷ CS13 ∷ X3 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0)
  q206 : Eqn
  q206 = eqn (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ []) (wn 2112 W)

-- pass [CS31] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 5 steps
lem-pass-CS31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (CS13 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (CS13 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CS13 ∷ [])
  (rw 1 q203 ∷
   rw 0 q204 ∷
   rw 1 q205 ∷
   rw 7 q206 ∷
   rw⁻ 0 q203 ∷ []) Eq.refl

private
  q207 : Eqn
  q207 = eqn (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw⁻ 0 q207 ∷ []) Eq.refl

private
  q208 : Eqn
  q208 = eqn (CS23 ∷ X3 ∷ []) (X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (wn 2154 W)
  q209 : Eqn
  q209 = eqn (X3 ∷ CS23 ∷ X3 ∷ X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0)
  q210 : Eqn
  q210 = eqn (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ []) (wn 2155 W)

-- pass [CS32] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 5 steps
lem-pass-CS32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (CS23 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = derive (CS23 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23 ∷ [])
  (rw 1 q203 ∷
   rw 0 q208 ∷
   rw 1 q209 ∷
   rw 7 q210 ∷
   rw⁻ 0 q203 ∷ []) Eq.refl

private
  q211 : Eqn
  q211 = eqn (CS23⁻ ∷ X3 ∷ []) (X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (wn 2242 W)
  q212 : Eqn
  q212 = eqn (X3 ∷ CS23⁻ ∷ X3 ∷ X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0)
  q213 : Eqn
  q213 = eqn (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ []) (wn 2243 W)

-- pass [CSd32] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 5 steps
lem-pass-CSd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (CS23⁻ ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-CSd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = derive (CS23⁻ ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23⁻ ∷ [])
  (rw 1 q203 ∷
   rw 0 q211 ∷
   rw 1 q212 ∷
   rw 7 q213 ∷
   rw⁻ 0 q203 ∷ []) Eq.refl

private
  q214 : Eqn
  q214 = eqn (X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ []) lem-pass-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [X0 X3 TOFF201 CS23 TOFF201 CSd23 X0 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = derive (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  (rw⁻ 0 q214 ∷ []) Eq.refl

private
  q215 : Eqn
  q215 = eqn (CS02⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1466 W)
  q216 : Eqn
  q216 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ []) (X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0)
  q217 : Eqn
  q217 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ []) (wn 1467 W)

-- pass [CSd30] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 25 steps
lem-pass-CSd30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (CS03⁻ ∷ X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (CS03⁻ ∷ X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CS03⁻ ∷ [])
  (rw 1 q203 ∷
   rw 2 q21 ∷
   rw 1 q23 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q22 ∷
   rw 1 q215 ∷
   rw 0 q26 ∷
   rw 1 q26 ∷
   rw 4 q21 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q26 ∷
   rw 4 q22 ∷
   rw 1 q216 ∷
   rw 19 q21 ∷
   rw 18 q23 ∷
   rw 17 q23 ∷
   re 16 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q22 ∷
   rw 15 q23 ∷
   rw 16 q217 ∷
   rw 15 q26 ∷
   rw 18 q21 ∷
   re 16 3 (CS03⁻ ∷ []) ∷
   rw 17 q22 ∷
   rw⁻ 0 q203 ∷ []) Eq.refl

private
  q218 : Eqn
  q218 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ []) (X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0)

-- pass [CKd30] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 25 steps
lem-pass-CKd30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (CK30⁻ ∷ X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-pass-CKd30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (CK30⁻ ∷ X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CK30⁻ ∷ [])
  (rw 1 q203 ∷
   rw 2 q21 ∷
   rw 1 q23 ∷
   re 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q22 ∷
   rw 1 q131 ∷
   rw 0 q26 ∷
   rw 1 q26 ∷
   rw 4 q21 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q26 ∷
   rw 4 q22 ∷
   rw 1 q218 ∷
   rw 19 q21 ∷
   rw 18 q23 ∷
   rw 17 q23 ∷
   re 16 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q22 ∷
   rw 15 q23 ∷
   rw 16 q134 ∷
   rw 15 q26 ∷
   rw 18 q21 ∷
   re 16 3 (CK30⁻ ∷ []) ∷
   rw 17 q22 ∷
   rw⁻ 0 q203 ∷ []) Eq.refl
