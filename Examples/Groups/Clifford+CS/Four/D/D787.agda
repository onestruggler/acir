{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D787 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D422 W using (lem-b2g-0100R1)
open import Examples.Groups.Clifford+CS.Four.D.D591 W using (lem-conjF-X0-CS01-CS01-CK10-CS01-CX13-CS)
open import Examples.Groups.Clifford+CS.Four.D.D777 W using (lem-Pm-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩)
open import Examples.Groups.Clifford+CS.Four.D.D784 W using (lem-Hc-passes-copies-X0-CS01-CS01-CK10-CS01-CX13-CS-ᵖinv)

private
  q1 : Eqn
  q1 = eqn (X1 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (lem-b2g-0100R1)
  q2 : Eqn
  q2 = eqn [] (X3 ∷ X3 ∷ []) (wn 225 W)
  q3 : Eqn
  q3 = eqn [] (S0 ∷ S0⁻ ∷ []) (wn 1732 W)
  q4 : Eqn
  q4 = eqn [] (K0 ∷ K0⁻ ∷ []) (wn 116 W)
  q5 : Eqn
  q5 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q6 : Eqn
  q6 = eqn [] (CS02 ∷ CS02⁻ ∷ []) (wn 1357 W)
  q7 : Eqn
  q7 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q8 : Eqn
  q8 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q9 : Eqn
  q9 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)
  q10 : Eqn
  q10 = eqn [] (K0⁻ ∷ K0 ∷ []) (wn 54 W)
  q11 : Eqn
  q11 = eqn [] (S0⁻ ∷ S0 ∷ []) (wn 1726 W)
  q12 : Eqn
  q12 = eqn [] (X2 ∷ X2 ∷ []) (wn 871 W)
  q13 : Eqn
  q13 = eqn [] (S1⁻ ∷ S1 ∷ []) (wn 2580 W)
  q14 : Eqn
  q14 = eqn [] (K1⁻ ∷ K1 ∷ []) (wn 1510 W)
  q15 : Eqn
  q15 = eqn [] (S1 ∷ S1⁻ ∷ []) (wn 2578 W)
  q16 : Eqn
  q16 = eqn [] (CS13 ∷ CS13⁻ ∷ []) (wn 1376 W)
  q17 : Eqn
  q17 = eqn [] (Toff102 ∷ Toff102 ∷ []) (wn 1377 W)
  q18 : Eqn
  q18 = eqn [] (CS13⁻ ∷ CS13 ∷ []) (wn 1378 W)
  q19 : Eqn
  q19 = eqn [] (K1 ∷ K1⁻ ∷ []) (wn 2579 W)
  q20 : Eqn
  q20 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) (CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ []) (lem-Pm-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩)
  q21 : Eqn
  q21 = eqn (X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ X0 ∷ X3 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ X0 ∷ []) lem-Hc-passes-copies-X0-CS01-CS01-CK10-CS01-CX13-CS-ᵖinv
  q22 : Eqn
  q22 = eqn (CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ X0 ∷ []) (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK21 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK21 ∷ CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ []) (lem-conjF-X0-CS01-CS01-CK10-CS01-CX13-CS)
  q23 : Eqn
  q23 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) (CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ []) lem-Pm-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩
  q24 : Eqn
  q24 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)
  q25 : Eqn
  q25 = eqn (X2 ∷ X2 ∷ []) [] (wn 389 W)
  q26 : Eqn
  q26 = eqn (S1 ∷ S1⁻ ∷ []) [] (wn 2583 W)
  q27 : Eqn
  q27 = eqn (K1 ∷ K1⁻ ∷ []) [] (wn 2582 W)
  q28 : Eqn
  q28 = eqn (S1⁻ ∷ S1 ∷ []) [] (wn 2581 W)
  q29 : Eqn
  q29 = eqn (Toff102 ∷ Toff102 ∷ []) [] (wn 1380 W)
  q30 : Eqn
  q30 = eqn (CS13⁻ ∷ CS13 ∷ []) [] (wn 1379 W)
  q31 : Eqn
  q31 = eqn (CS13 ∷ CS13⁻ ∷ []) [] (wn 1381 W)
  q32 : Eqn
  q32 = eqn (K1⁻ ∷ K1 ∷ []) [] (wn 1509 W)
  q33 : Eqn
  q33 = eqn (S0⁻ ∷ S0 ∷ []) [] (wn 2487 W)
  q34 : Eqn
  q34 = eqn (K0⁻ ∷ K0 ∷ []) [] (wn 1339 W)
  q35 : Eqn
  q35 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)
  q36 : Eqn
  q36 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)
  q37 : Eqn
  q37 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)
  q38 : Eqn
  q38 = eqn (K0 ∷ K0⁻ ∷ []) [] (wn 1846 W)
  q39 : Eqn
  q39 = eqn (S0 ∷ S0⁻ ∷ []) [] (wn 1728 W)
  q40 : Eqn
  q40 = eqn (X1 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) lem-b2g-0100R1

-- shift 0000R0 0100R1 X0 CS01 CS01 CK10 CS01 CX13 CS: 230 steps
lem-shift-0000R0-0100R1-X0-CS01-CS01-CK10-CS01-CX13-CS : ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X1 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK21 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK21 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X1 ∷ []) ⟫ʷ
lem-shift-0000R0-0100R1-X0-CS01-CS01-CK10-CS01-CX13-CS = derive (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X1 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ X0 ∷ []) (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK21 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK21 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X1 ∷ [])
  (rw 8 q1 ∷
   rw 20 q2 ∷
   rw 21 q3 ∷
   rw 22 q4 ∷
   rw 23 q5 ∷
   rw 24 q6 ∷
   rw 25 q5 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q5 ∷
   re 24 3 (CS03⁻ ∷ []) ∷
   rw 25 q7 ∷
   rw 24 q8 ∷
   rw 25 q5 ∷
   rw 26 q9 ∷
   rw 27 q5 ∷
   re 25 3 (CS03⁻ ∷ []) ∷
   rw 28 q5 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q7 ∷
   rw 26 q8 ∷
   rw 27 q10 ∷
   rw 28 q11 ∷
   rw 29 q2 ∷
   rw 30 q12 ∷
   rw 31 q3 ∷
   rw 32 q4 ∷
   rw 33 q5 ∷
   rw 34 q6 ∷
   rw 35 q5 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q5 ∷
   re 34 3 (CS03⁻ ∷ []) ∷
   rw 35 q7 ∷
   rw 34 q8 ∷
   rw 35 q5 ∷
   rw 36 q9 ∷
   rw 37 q5 ∷
   re 35 3 (CS03⁻ ∷ []) ∷
   rw 38 q5 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q7 ∷
   rw 36 q8 ∷
   rw 37 q10 ∷
   rw 38 q11 ∷
   rw 39 q12 ∷
   rw 40 q12 ∷
   rw 41 q2 ∷
   rw 42 q3 ∷
   rw 43 q4 ∷
   rw 44 q5 ∷
   rw 45 q6 ∷
   rw 46 q5 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 47 q5 ∷
   re 45 3 (CS03⁻ ∷ []) ∷
   rw 46 q7 ∷
   rw 45 q8 ∷
   rw 46 q5 ∷
   rw 47 q9 ∷
   rw 48 q5 ∷
   re 46 3 (CS03⁻ ∷ []) ∷
   rw 49 q5 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q7 ∷
   rw 47 q8 ∷
   rw 48 q10 ∷
   rw 49 q11 ∷
   rw 50 q12 ∷
   rw 51 q2 ∷
   rw 52 q2 ∷
   rw 53 q13 ∷
   rw 54 q14 ∷
   rw 55 q15 ∷
   rw 56 q15 ∷
   rw 57 q16 ∷
   rw 58 q17 ∷
   rw 59 q18 ∷
   rw 60 q17 ∷
   rw 61 q13 ∷
   rw 62 q13 ∷
   rw 63 q19 ∷
   rw 64 q15 ∷
   rw 65 q2 ∷
   rw 66 q12 ∷
   rw 67 q13 ∷
   rw 68 q14 ∷
   rw 69 q15 ∷
   rw 70 q15 ∷
   rw 71 q16 ∷
   rw 72 q17 ∷
   rw 73 q18 ∷
   rw 74 q17 ∷
   rw 75 q13 ∷
   rw 76 q13 ∷
   rw 77 q19 ∷
   rw 78 q15 ∷
   rw 79 q12 ∷
   rw 80 q12 ∷
   rw 81 q2 ∷
   rw 82 q13 ∷
   rw 83 q14 ∷
   rw 84 q15 ∷
   rw 85 q15 ∷
   rw 86 q16 ∷
   rw 87 q17 ∷
   rw 88 q18 ∷
   rw 89 q17 ∷
   rw 90 q13 ∷
   rw 91 q13 ∷
   rw 92 q19 ∷
   rw 93 q15 ∷
   rw 94 q12 ∷
   rw 95 q2 ∷
   rw 0 q20 ∷
   rw⁻ 6 q21 ∷
   rw 0 q22 ∷
   rw⁻ 80 q23 ∷
   rw 175 q24 ∷
   rw 174 q25 ∷
   rw 173 q26 ∷
   rw 172 q27 ∷
   rw 171 q28 ∷
   rw 170 q28 ∷
   rw 169 q29 ∷
   rw 168 q30 ∷
   rw 167 q29 ∷
   rw 166 q31 ∷
   rw 165 q26 ∷
   rw 164 q26 ∷
   rw 163 q32 ∷
   rw 162 q28 ∷
   rw 161 q24 ∷
   rw 160 q25 ∷
   rw 159 q25 ∷
   rw 158 q26 ∷
   rw 157 q27 ∷
   rw 156 q28 ∷
   rw 155 q28 ∷
   rw 154 q29 ∷
   rw 153 q30 ∷
   rw 152 q29 ∷
   rw 151 q31 ∷
   rw 150 q26 ∷
   rw 149 q26 ∷
   rw 148 q32 ∷
   rw 147 q28 ∷
   rw 146 q25 ∷
   rw 145 q24 ∷
   rw 144 q26 ∷
   rw 143 q27 ∷
   rw 142 q28 ∷
   rw 141 q28 ∷
   rw 140 q29 ∷
   rw 139 q30 ∷
   rw 138 q29 ∷
   rw 137 q31 ∷
   rw 136 q26 ∷
   rw 135 q26 ∷
   rw 134 q32 ∷
   rw 133 q28 ∷
   rw 132 q24 ∷
   rw 131 q24 ∷
   rw 130 q25 ∷
   rw 129 q33 ∷
   rw 128 q34 ∷
   rw 127 q35 ∷
   rw 128 q5 ∷
   re 127 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 129 q7 ∷
   re 126 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 128 q7 ∷
   rw 127 q36 ∷
   rw 126 q7 ∷
   rw 125 q35 ∷
   rw 126 q5 ∷
   re 125 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 127 q7 ∷
   re 124 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 126 q7 ∷
   rw 125 q37 ∷
   rw 124 q7 ∷
   rw 123 q38 ∷
   rw 122 q39 ∷
   rw 121 q24 ∷
   rw 120 q25 ∷
   rw 119 q25 ∷
   rw 118 q33 ∷
   rw 117 q34 ∷
   rw 116 q35 ∷
   rw 117 q5 ∷
   re 116 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 118 q7 ∷
   re 115 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 117 q7 ∷
   rw 116 q36 ∷
   rw 115 q7 ∷
   rw 114 q35 ∷
   rw 115 q5 ∷
   re 114 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 116 q7 ∷
   re 113 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 115 q7 ∷
   rw 114 q37 ∷
   rw 113 q7 ∷
   rw 112 q38 ∷
   rw 111 q39 ∷
   rw 110 q25 ∷
   rw 109 q24 ∷
   rw 108 q33 ∷
   rw 107 q34 ∷
   rw 106 q35 ∷
   rw 107 q5 ∷
   re 106 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 108 q7 ∷
   re 105 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 107 q7 ∷
   rw 106 q36 ∷
   rw 105 q7 ∷
   rw 104 q35 ∷
   rw 105 q5 ∷
   re 104 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 106 q7 ∷
   re 103 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 105 q7 ∷
   rw 104 q37 ∷
   rw 103 q7 ∷
   rw 102 q38 ∷
   rw 101 q39 ∷
   rw 100 q24 ∷
   rw⁻ 88 q40 ∷ []) Eq.refl
