{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD119 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D119 (Sᴰ : SD119) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R : Ws → St 1840
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R = pickᴰ 0 Sᴰ
  lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R : Ws → St 1841
  lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R = pickᴰ 1 Sᴰ
  lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R : Ws → St 1842
  lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R = pickᴰ 2 Sᴰ
  lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R : Ws → St 1843
  lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R = pickᴰ 3 Sᴰ
  lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R : Ws → St 1844
  lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R = pickᴰ 4 Sᴰ
  lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R : Ws → St 1847
  lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R = pickᴰ 5 Sᴰ
  lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R : Ws → St 1848
  lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R = pickᴰ 6 Sᴰ
  lem-F4-K2-K1-at0440 : Ws → St 1849
  lem-F4-K2-K1-at0440 = pickᴰ 7 Sᴰ
  lem-F4-K2-K2-at0440 : Ws → St 1850
  lem-F4-K2-K2-at0440 = pickᴰ 8 Sᴰ
  lem-F4-CS1-CS1-at0440 : Ws → St 1851
  lem-F4-CS1-CS1-at0440 = pickᴰ 9 Sᴰ
  lem-F4-CS1-I-at0440 : Ws → St 1863
  lem-F4-CS1-I-at0440 = pickᴰ 10 Sᴰ
  lem-F4-CS1-K1-at0440 : Ws → St 1852
  lem-F4-CS1-K1-at0440 = pickᴰ 11 Sᴰ
  lem-F4-K2-CS2-at0440 : Ws → St 1856
  lem-F4-K2-CS2-at0440 = pickᴰ 12 Sᴰ
  lem-F5-12 : Ws → St 1816
  lem-F5-12 = pickᴰ 13 Sᴰ
  lem-F4-CS1-K2-at0440 : Ws → St 1858
  lem-F4-CS1-K2-at0440 = pickᴰ 14 Sᴰ
  lem-F4-CS1-CS2-at0440 : Ws → St 1859
  lem-F4-CS1-CS2-at0440 = pickᴰ 15 Sᴰ
  lem-F4-K2-CS1-at0440 : Ws → St 1861
  lem-F4-K2-CS1-at0440 = pickᴰ 16 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1861 (lem-F4-K2-CS1-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1850 (lem-F4-K2-K2-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1856 (lem-F4-K2-CS2-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1849 (lem-F4-K2-K1-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = wlE 18 (lit c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 146 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 6 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = wlE 3 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (c₂ (CS) (Swap))
  q10 : Ws → Eqn
  q10 c4 = wlE 4 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q12 : Ws → Eqn
  q12 c4 = wlE 24 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1816 (lem-F5-12 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q15 : Ws → Eqn
  q15 c4 = sE 1840 (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q17 : Ws → Eqn
  q17 c4 = sE 1841 (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q19 : Ws → Eqn
  q19 c4 = sE 1842 (lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R c4)
  q20 : Ws → Eqn
  q20 c4 = wlE 1456 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1843 (lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R c4)
  q22 : Ws → Eqn
  q22 c4 = wlE 1457 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1848 (lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 1458 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1844 (lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 1459 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1847 (lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1858 (lem-F4-CS1-K2-at0440 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1859 (lem-F4-CS1-CS2-at0440 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1863 (lem-F4-CS1-I-at0440 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1851 (lem-F4-CS1-CS1-at0440 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1852 (lem-F4-CS1-K1-at0440 c4)

-- ckt-TST @0440 part17: 105 steps
lem-ckt-TST-at0440-part17 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sw01 ∷ Sw12 ∷ X2 ∷ Sw23 ∷ Sb4-0-31-2 ∷ X3 ∷ Sb4-0-31-2 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-at0440-part17 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sw01 ∷ Sw12 ∷ X2 ∷ Sw23 ∷ Sb4-0-31-2 ∷ X3 ∷ Sb4-0-31-2 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw⁻ 226 (q1 c4) ∷
   rw⁻ 225 (q2 c4) ∷
   rw⁻ 224 (q3 c4) ∷
   rw⁻ 223 (q4 c4) ∷
   rw⁻ 238 (q5 c4) ∷
   rw 237 (q6 c4) ∷
   rw⁻ 239 (q7 c4) ∷
   re 238 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 240 (q7 c4) ∷
   rw⁻ 240 (q8 c4) ∷
   rw 239 (q9 c4) ∷
   rw⁻ 241 (q10 c4) ∷
   rw 240 (q11 c4) ∷
   rw⁻ 242 (q8 c4) ∷
   rw 241 (q9 c4) ∷
   rw⁻ 243 (q7 c4) ∷
   rw⁻ 242 (q7 c4) ∷
   re 243 3 (CS02 ∷ []) ∷
   rw⁻ 244 (q5 c4) ∷
   rw 243 (q12 c4) ∷
   rw⁻ 244 (q13 c4) ∷
   rw 243 (q14 c4) ∷
   rw 244 (q15 c4) ∷
   rw 245 (q14 c4) ∷
   rw 246 (q15 c4) ∷
   rw 247 (q5 c4) ∷
   rw 242 (q16 c4) ∷
   rw 243 (q17 c4) ∷
   rw 244 (q16 c4) ∷
   rw 245 (q17 c4) ∷
   rw 246 (q7 c4) ∷
   rw 241 (q18 c4) ∷
   rw 242 (q19 c4) ∷
   rw 243 (q18 c4) ∷
   rw 244 (q19 c4) ∷
   rw 245 (q8 c4) ∷
   rw 240 (q20 c4) ∷
   rw 241 (q21 c4) ∷
   rw 242 (q20 c4) ∷
   rw 243 (q21 c4) ∷
   rw 244 (q10 c4) ∷
   rw 239 (q22 c4) ∷
   rw 240 (q23 c4) ∷
   rw 241 (q22 c4) ∷
   rw 242 (q23 c4) ∷
   rw 243 (q8 c4) ∷
   rw 238 (q24 c4) ∷
   rw 239 (q25 c4) ∷
   rw 240 (q24 c4) ∷
   rw 241 (q25 c4) ∷
   rw 242 (q7 c4) ∷
   rw 237 (q26 c4) ∷
   rw 238 (q27 c4) ∷
   rw 239 (q26 c4) ∷
   rw 240 (q27 c4) ∷
   rw 241 (q5 c4) ∷
   rw⁻ 236 (q28 c4) ∷
   rw⁻ 235 (q29 c4) ∷
   rw⁻ 234 (q29 c4) ∷
   rw⁻ 233 (q29 c4) ∷
   rw⁻ 232 (q30 c4) ∷
   rw⁻ 231 (q28 c4) ∷
   rw⁻ 230 (q31 c4) ∷
   rw⁻ 229 (q31 c4) ∷
   rw⁻ 228 (q28 c4) ∷
   rw⁻ 227 (q29 c4) ∷
   rw⁻ 226 (q32 c4) ∷
   rw⁻ 242 (q5 c4) ∷
   rw 241 (q6 c4) ∷
   rw⁻ 243 (q7 c4) ∷
   re 242 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 244 (q7 c4) ∷
   rw⁻ 244 (q8 c4) ∷
   rw 243 (q9 c4) ∷
   rw⁻ 245 (q10 c4) ∷
   rw 244 (q11 c4) ∷
   rw⁻ 246 (q8 c4) ∷
   rw 245 (q9 c4) ∷
   rw⁻ 247 (q7 c4) ∷
   rw⁻ 246 (q7 c4) ∷
   re 247 3 (CS02 ∷ []) ∷
   rw⁻ 248 (q5 c4) ∷
   rw 247 (q12 c4) ∷
   rw⁻ 248 (q13 c4) ∷
   rw 247 (q14 c4) ∷
   rw 248 (q15 c4) ∷
   rw 249 (q14 c4) ∷
   rw 250 (q15 c4) ∷
   rw 251 (q5 c4) ∷
   rw 246 (q16 c4) ∷
   rw 247 (q17 c4) ∷
   rw 248 (q16 c4) ∷
   rw 249 (q17 c4) ∷
   rw 250 (q7 c4) ∷
   rw 245 (q18 c4) ∷
   rw 246 (q19 c4) ∷
   rw 247 (q18 c4) ∷
   rw 248 (q19 c4) ∷
   rw 249 (q8 c4) ∷
   rw 244 (q20 c4) ∷
   rw 245 (q21 c4) ∷
   rw 246 (q20 c4) ∷
   rw 247 (q21 c4) ∷
   rw 248 (q10 c4) ∷
   rw 243 (q22 c4) ∷ []) Eq.refl
