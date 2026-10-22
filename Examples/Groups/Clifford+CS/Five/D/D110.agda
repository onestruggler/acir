{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD110 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D110 (Sᴰ : SD110) where

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
  lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R : Ws → St 1680
  lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R = pickᴰ 0 Sᴰ
  lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R : Ws → St 1838
  lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R = pickᴰ 1 Sᴰ
  lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R : Ws → St 1839
  lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R = pickᴰ 2 Sᴰ
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R : Ws → St 1681
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R = pickᴰ 3 Sᴰ
  lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R : Ws → St 1682
  lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R = pickᴰ 4 Sᴰ
  lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R : Ws → St 1845
  lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R = pickᴰ 5 Sᴰ
  lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R : Ws → St 1846
  lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R = pickᴰ 6 Sᴰ
  lem-F4-K3-I-at0440 : Ws → St 1864
  lem-F4-K3-I-at0440 = pickᴰ 7 Sᴰ
  lem-F4-K3-K2-at0440 : Ws → St 1866
  lem-F4-K3-K2-at0440 = pickᴰ 8 Sᴰ
  lem-F4-K3-K3-at0440 : Ws → St 1871
  lem-F4-K3-K3-at0440 = pickᴰ 9 Sᴰ
  lem-F4-CS2-CS2-at0440 : Ws → St 1853
  lem-F4-CS2-CS2-at0440 = pickᴰ 10 Sᴰ
  lem-F4-CS2-I-at0440 : Ws → St 1854
  lem-F4-CS2-I-at0440 = pickᴰ 11 Sᴰ
  lem-F4-CS2-K2-at0440 : Ws → St 1855
  lem-F4-CS2-K2-at0440 = pickᴰ 12 Sᴰ
  lem-F4-K3-CS1-at0440 : Ws → St 1867
  lem-F4-K3-CS1-at0440 = pickᴰ 13 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 14 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1857
  lem-F4-CS2-K1-at0440 = pickᴰ 15 Sᴰ
  lem-F4-CS2-CS1-at0440 : Ws → St 1860
  lem-F4-CS2-CS1-at0440 = pickᴰ 16 Sᴰ
  lem-F4-CS2-K3-at0440 : Ws → St 1868
  lem-F4-CS2-K3-at0440 = pickᴰ 17 Sᴰ
  lem-F4-K3-CS2-at0440 : Ws → St 1869
  lem-F4-K3-CS2-at0440 = pickᴰ 18 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 6 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 1459 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1846 (lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 18 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1868 (lem-F4-CS2-K3-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1860 (lem-F4-CS2-CS1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1854 (lem-F4-CS2-I-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1853 (lem-F4-CS2-CS2-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1855 (lem-F4-CS2-K2-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1857 (lem-F4-CS2-K1-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))
  q12 : Ws → Eqn
  q12 c4 = wlE 47 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wlE 3 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 4 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CS12 ∷ Sw34 ∷ []) (Sw34 ∷ CS12 ∷ []) (c₃ (CS ↑) (Swap))
  q16 : Ws → Eqn
  q16 c4 = wlE 46 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1590 (lem-F5-23 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q19 : Ws → Eqn
  q19 c4 = sE 1681 (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q21 : Ws → Eqn
  q21 c4 = sE 1682 (lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q23 : Ws → Eqn
  q23 c4 = sE 1680 (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 1456 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1838 (lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 1457 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1839 (lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R c4)
  q28 : Ws → Eqn
  q28 c4 = wlE 1458 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1845 (lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R c4)
  q30 : Ws → Eqn
  q30 c4 = wlE 1716 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1869 (lem-F4-K3-CS2-at0440 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1871 (lem-F4-K3-K3-at0440 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1867 (lem-F4-K3-CS1-at0440 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1864 (lem-F4-K3-I-at0440 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1866 (lem-F4-K3-K2-at0440 c4)

-- ckt-TST @0440 part7: 149 steps
lem-ckt-TST-at0440-part7 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sw01 ∷ X1 ∷ Sb4-2-13-0 ∷ X1 ∷ Sb4-2-13-0 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-at0440-part7 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sw01 ∷ X1 ∷ Sb4-2-13-0 ∷ X1 ∷ Sb4-2-13-0 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw 133 (q1 c4) ∷
   rw 128 (q2 c4) ∷
   rw 129 (q3 c4) ∷
   rw 130 (q2 c4) ∷
   rw 131 (q3 c4) ∷
   rw 132 (q4 c4) ∷
   rw⁻ 127 (q5 c4) ∷
   rw⁻ 126 (q6 c4) ∷
   rw⁻ 125 (q7 c4) ∷
   rw⁻ 124 (q5 c4) ∷
   rw⁻ 123 (q8 c4) ∷
   rw⁻ 122 (q8 c4) ∷
   rw⁻ 121 (q5 c4) ∷
   rw⁻ 120 (q7 c4) ∷
   rw⁻ 119 (q9 c4) ∷
   rw⁻ 118 (q8 c4) ∷
   rw⁻ 117 (q8 c4) ∷
   rw⁻ 116 (q9 c4) ∷
   rw⁻ 115 (q7 c4) ∷
   rw⁻ 114 (q5 c4) ∷
   rw⁻ 113 (q8 c4) ∷
   rw⁻ 112 (q8 c4) ∷
   rw⁻ 111 (q5 c4) ∷
   rw⁻ 110 (q7 c4) ∷
   rw⁻ 109 (q9 c4) ∷
   rw⁻ 108 (q6 c4) ∷
   rw⁻ 107 (q6 c4) ∷
   rw⁻ 106 (q9 c4) ∷
   rw⁻ 105 (q8 c4) ∷
   rw⁻ 104 (q8 c4) ∷
   rw⁻ 103 (q8 c4) ∷
   rw⁻ 102 (q7 c4) ∷
   rw⁻ 101 (q9 c4) ∷
   rw⁻ 100 (q6 c4) ∷
   rw⁻ 99 (q6 c4) ∷
   rw⁻ 98 (q9 c4) ∷
   rw⁻ 97 (q8 c4) ∷
   rw⁻ 96 (q10 c4) ∷
   rw⁻ 133 (q4 c4) ∷
   rw⁻ 132 (q11 c4) ∷
   rw⁻ 134 (q1 c4) ∷
   rw 133 (q12 c4) ∷
   rw⁻ 135 (q13 c4) ∷
   re 134 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 136 (q13 c4) ∷
   rw⁻ 136 (q14 c4) ∷
   rw 135 (q15 c4) ∷
   rw⁻ 137 (q13 c4) ∷
   rw⁻ 136 (q13 c4) ∷
   re 137 3 (CS13 ∷ []) ∷
   rw⁻ 138 (q1 c4) ∷
   rw 137 (q16 c4) ∷
   rw⁻ 139 (q4 c4) ∷
   rw⁻ 138 (q11 c4) ∷
   rw⁻ 139 (q17 c4) ∷
   rw 138 (q18 c4) ∷
   rw 139 (q19 c4) ∷
   rw 140 (q18 c4) ∷
   rw 141 (q19 c4) ∷
   rw 142 (q4 c4) ∷
   rw 137 (q20 c4) ∷
   rw 138 (q21 c4) ∷
   rw 139 (q20 c4) ∷
   rw 140 (q21 c4) ∷
   rw 141 (q1 c4) ∷
   rw 136 (q22 c4) ∷
   rw 137 (q23 c4) ∷
   rw 138 (q22 c4) ∷
   rw 139 (q23 c4) ∷
   rw 140 (q13 c4) ∷
   rw 135 (q24 c4) ∷
   rw 136 (q25 c4) ∷
   rw 137 (q24 c4) ∷
   rw 138 (q25 c4) ∷
   rw 139 (q14 c4) ∷
   rw 134 (q26 c4) ∷
   rw 135 (q27 c4) ∷
   rw 136 (q26 c4) ∷
   rw 137 (q27 c4) ∷
   rw 138 (q13 c4) ∷
   rw 133 (q28 c4) ∷
   rw 134 (q29 c4) ∷
   rw 135 (q28 c4) ∷
   rw 136 (q29 c4) ∷
   rw 137 (q1 c4) ∷
   rw 132 (q2 c4) ∷
   rw 133 (q3 c4) ∷
   rw 134 (q2 c4) ∷
   rw 135 (q3 c4) ∷
   rw 136 (q4 c4) ∷
   rw⁻ 131 (q8 c4) ∷
   rw⁻ 130 (q5 c4) ∷
   rw⁻ 129 (q6 c4) ∷
   rw⁻ 128 (q7 c4) ∷
   rw⁻ 127 (q5 c4) ∷
   rw⁻ 126 (q8 c4) ∷
   rw⁻ 125 (q8 c4) ∷
   rw⁻ 124 (q5 c4) ∷
   rw⁻ 123 (q7 c4) ∷
   rw⁻ 122 (q9 c4) ∷
   rw⁻ 121 (q8 c4) ∷
   rw⁻ 120 (q8 c4) ∷
   rw⁻ 119 (q9 c4) ∷
   rw⁻ 118 (q7 c4) ∷
   rw⁻ 117 (q5 c4) ∷
   rw⁻ 116 (q8 c4) ∷
   rw⁻ 115 (q8 c4) ∷
   rw⁻ 114 (q5 c4) ∷
   rw⁻ 113 (q7 c4) ∷
   rw⁻ 112 (q9 c4) ∷
   rw⁻ 111 (q6 c4) ∷
   rw⁻ 110 (q6 c4) ∷
   rw⁻ 109 (q9 c4) ∷
   rw⁻ 108 (q8 c4) ∷
   rw⁻ 107 (q8 c4) ∷
   rw⁻ 106 (q8 c4) ∷
   rw⁻ 105 (q7 c4) ∷
   rw⁻ 104 (q9 c4) ∷
   rw⁻ 103 (q6 c4) ∷
   rw⁻ 102 (q6 c4) ∷
   rw⁻ 101 (q9 c4) ∷
   rw⁻ 100 (q8 c4) ∷
   rw⁻ 99 (q10 c4) ∷
   rw 136 (q30 c4) ∷
   rw⁻ 135 (q31 c4) ∷
   rw⁻ 134 (q31 c4) ∷
   rw⁻ 133 (q32 c4) ∷
   rw⁻ 132 (q33 c4) ∷
   rw⁻ 131 (q34 c4) ∷
   rw⁻ 130 (q32 c4) ∷
   rw⁻ 129 (q31 c4) ∷
   rw⁻ 128 (q31 c4) ∷
   rw⁻ 127 (q32 c4) ∷
   rw⁻ 126 (q34 c4) ∷
   rw⁻ 125 (q35 c4) ∷
   rw⁻ 124 (q31 c4) ∷
   rw⁻ 123 (q31 c4) ∷
   rw⁻ 122 (q35 c4) ∷
   rw⁻ 121 (q34 c4) ∷
   rw⁻ 120 (q32 c4) ∷
   rw⁻ 119 (q31 c4) ∷
   rw⁻ 118 (q31 c4) ∷
   rw⁻ 117 (q32 c4) ∷
   rw⁻ 116 (q34 c4) ∷
   rw⁻ 115 (q35 c4) ∷
   rw⁻ 114 (q33 c4) ∷
   rw⁻ 113 (q33 c4) ∷
   rw⁻ 112 (q35 c4) ∷
   rw⁻ 111 (q31 c4) ∷ []) Eq.refl
