{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D106 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-I-at0440 ; lem-F4-I-K1-at0440 ; lem-F4-I-K2-at0440 ; lem-F4-I-K3-at0440 ; lem-F4-K2-I-at0440 ; lem-F4-K2-K1-at0440 ; lem-F4-K2-K2-at0440 ; lem-F4-K2-K3-at0440 ; lem-F4-K3-I-at0440 ; lem-F4-K3-K1-at0440 ; lem-F4-K3-K2-at0440 ; lem-F4-K3-K3-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-F4-I-CS1-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-F4-CS2-CS2-at0440 ; lem-F4-CS2-I-at0440 ; lem-F4-CS2-K2-at0440 ; lem-F4-I-CS2-at0440 ; lem-F4-K2-CS2-at0440 ; lem-F4-K3-CS1-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F5-23)
open import Examples.Groups.Clifford+CS.Five.D.D033 using (lem-F4-CS2-K1-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D061 using (lem-F4-CS2-CS1-at0440 ; lem-F4-CS2-K3-at0440 ; lem-F4-K2-CS1-at0440 ; lem-F4-K3-CS2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R ; lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R ; lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R ; lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R ; lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R ; lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-I-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-K2-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-CS1-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-K1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (K3 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) (wl 1716 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (X0 ∷ CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (lem-F4-K3-CS2-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (lem-F4-K3-K3-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X0 ∷ CK03 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (lem-F4-K3-I-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (X0 ∷ CK03 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (lem-F4-K3-K2-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X0 ∷ CK03 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (lem-F4-K3-CS1-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (lem-F4-K3-K1-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (ι ∷ []) (wl 1461 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-K3-at0440 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-CS2-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-I-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-K2-at0440 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-CS1-at0440 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-K1-at0440 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (K2 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) (wl 1715 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-I-at0440 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-K3-at0440 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-CS2-at0440 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-K2-at0440 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-CS1-at0440 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-K1-at0440 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))
  q29 : Ws → Eqn
  q29 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl 47 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl 4 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CS12 ∷ Sw34 ∷ []) (Sw34 ∷ CS12 ∷ []) (c₃ (CS ↑) (Swap))
  q34 : Ws → Eqn
  q34 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl 46 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ []) (lem-F5-23 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q39 : Ws → Eqn
  q39 c4 = eqn (Sw12 ∷ Sb1-2-43-0 ∷ []) (Sb2-1-43-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q41 : Ws → Eqn
  q41 c4 = eqn (Sw23 ∷ Sb2-1-43-0 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) (wl 1456 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (Sw34 ∷ Sb3-1-42-0 ∷ []) (Sb4-1-32-0 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) (wl 1457 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (Sw23 ∷ Sb4-1-32-0 ∷ []) (Sb4-1-23-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) (wl 1458 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (Sw12 ∷ Sb4-1-23-0 ∷ []) (Sb4-2-13-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wl 1459 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (Sw01 ∷ Sb4-2-13-0 ∷ []) (Sb4-2-03-1 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-K3-at0440 c4)

-- ckt-TST @0440 part3: 181 steps
lem-ckt-TST-at0440-part3 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sw01 ∷ Sw12 ∷ X2 ∷ Sb4-1-23-0 ∷ X2 ∷ Sw23 ∷ Sb4-1-32-0 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-at0440-part3 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sw01 ∷ Sw12 ∷ X2 ∷ Sb4-1-23-0 ∷ X2 ∷ Sw23 ∷ Sb4-1-32-0 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw⁻ 58 (q1 c4) ∷
   rw⁻ 57 (q2 c4) ∷
   rw⁻ 56 (q3 c4) ∷
   rw⁻ 55 (q4 c4) ∷
   rw⁻ 54 (q4 c4) ∷
   rw⁻ 53 (q3 c4) ∷
   rw⁻ 52 (q1 c4) ∷
   rw⁻ 51 (q5 c4) ∷
   rw 72 (q6 c4) ∷
   rw⁻ 71 (q7 c4) ∷
   rw⁻ 70 (q7 c4) ∷
   rw⁻ 69 (q8 c4) ∷
   rw⁻ 68 (q9 c4) ∷
   rw⁻ 67 (q10 c4) ∷
   rw⁻ 66 (q11 c4) ∷
   rw⁻ 65 (q11 c4) ∷
   rw⁻ 64 (q10 c4) ∷
   rw⁻ 63 (q7 c4) ∷
   rw⁻ 62 (q7 c4) ∷
   rw⁻ 61 (q7 c4) ∷
   rw⁻ 60 (q9 c4) ∷
   rw⁻ 59 (q10 c4) ∷
   rw⁻ 58 (q11 c4) ∷
   rw⁻ 57 (q11 c4) ∷
   rw⁻ 56 (q10 c4) ∷
   rw⁻ 55 (q7 c4) ∷
   rw⁻ 54 (q12 c4) ∷
   rw⁻ 76 (q13 c4) ∷
   rw⁻ 75 (q14 c4) ∷
   rw⁻ 74 (q15 c4) ∷
   rw⁻ 73 (q15 c4) ∷
   rw⁻ 72 (q14 c4) ∷
   rw⁻ 71 (q16 c4) ∷
   rw⁻ 70 (q17 c4) ∷
   rw⁻ 69 (q18 c4) ∷
   rw⁻ 68 (q18 c4) ∷
   rw⁻ 67 (q17 c4) ∷
   rw⁻ 66 (q15 c4) ∷
   rw⁻ 65 (q15 c4) ∷
   rw⁻ 64 (q15 c4) ∷
   rw⁻ 63 (q16 c4) ∷
   rw⁻ 62 (q17 c4) ∷
   rw⁻ 61 (q18 c4) ∷
   rw⁻ 60 (q18 c4) ∷
   rw⁻ 59 (q17 c4) ∷
   rw⁻ 58 (q15 c4) ∷
   rw⁻ 57 (q19 c4) ∷
   rw 80 (q20 c4) ∷
   rw⁻ 79 (q21 c4) ∷
   rw⁻ 78 (q22 c4) ∷
   rw⁻ 77 (q23 c4) ∷
   rw⁻ 76 (q23 c4) ∷
   rw⁻ 75 (q22 c4) ∷
   rw⁻ 74 (q21 c4) ∷
   rw⁻ 73 (q24 c4) ∷
   rw⁻ 72 (q25 c4) ∷
   rw⁻ 71 (q25 c4) ∷
   rw⁻ 70 (q24 c4) ∷
   rw⁻ 69 (q23 c4) ∷
   rw⁻ 68 (q23 c4) ∷
   rw⁻ 67 (q23 c4) ∷
   rw⁻ 66 (q21 c4) ∷
   rw⁻ 65 (q24 c4) ∷
   rw⁻ 64 (q25 c4) ∷
   rw⁻ 63 (q25 c4) ∷
   rw⁻ 62 (q24 c4) ∷
   rw⁻ 61 (q23 c4) ∷
   rw⁻ 60 (q26 c4) ∷
   rw⁻ 85 (q27 c4) ∷
   rw⁻ 84 (q28 c4) ∷
   rw⁻ 86 (q29 c4) ∷
   rw 85 (q30 c4) ∷
   rw⁻ 87 (q31 c4) ∷
   re 86 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 88 (q31 c4) ∷
   rw⁻ 88 (q32 c4) ∷
   rw 87 (q33 c4) ∷
   rw⁻ 89 (q31 c4) ∷
   rw⁻ 88 (q31 c4) ∷
   re 89 3 (CS13 ∷ []) ∷
   rw⁻ 90 (q29 c4) ∷
   rw 89 (q34 c4) ∷
   rw⁻ 91 (q27 c4) ∷
   rw⁻ 90 (q28 c4) ∷
   rw⁻ 91 (q35 c4) ∷
   rw 90 (q36 c4) ∷
   rw 91 (q37 c4) ∷
   rw 92 (q36 c4) ∷
   rw 93 (q37 c4) ∷
   rw 94 (q27 c4) ∷
   rw 89 (q38 c4) ∷
   rw 90 (q39 c4) ∷
   rw 91 (q38 c4) ∷
   rw 92 (q39 c4) ∷
   rw 93 (q29 c4) ∷
   rw 88 (q40 c4) ∷
   rw 89 (q41 c4) ∷
   rw 90 (q40 c4) ∷
   rw 91 (q41 c4) ∷
   rw 92 (q31 c4) ∷
   rw 87 (q42 c4) ∷
   rw 88 (q43 c4) ∷
   rw 89 (q42 c4) ∷
   rw 90 (q43 c4) ∷
   rw 91 (q32 c4) ∷
   rw 86 (q44 c4) ∷
   rw 87 (q45 c4) ∷
   rw 88 (q44 c4) ∷
   rw 89 (q45 c4) ∷
   rw 90 (q31 c4) ∷
   rw 85 (q46 c4) ∷
   rw 86 (q47 c4) ∷
   rw 87 (q46 c4) ∷
   rw 88 (q47 c4) ∷
   rw 89 (q29 c4) ∷
   rw 84 (q48 c4) ∷
   rw 85 (q49 c4) ∷
   rw 86 (q48 c4) ∷
   rw 87 (q49 c4) ∷
   rw 88 (q27 c4) ∷
   rw⁻ 83 (q3 c4) ∷
   rw⁻ 82 (q2 c4) ∷
   rw⁻ 81 (q50 c4) ∷
   rw⁻ 80 (q1 c4) ∷
   rw⁻ 79 (q1 c4) ∷
   rw⁻ 78 (q50 c4) ∷
   rw⁻ 77 (q2 c4) ∷
   rw⁻ 76 (q3 c4) ∷
   rw⁻ 75 (q4 c4) ∷
   rw⁻ 74 (q4 c4) ∷
   rw⁻ 73 (q3 c4) ∷
   rw⁻ 72 (q1 c4) ∷
   rw⁻ 71 (q1 c4) ∷
   rw⁻ 70 (q1 c4) ∷
   rw⁻ 69 (q2 c4) ∷
   rw⁻ 68 (q3 c4) ∷
   rw⁻ 67 (q4 c4) ∷
   rw⁻ 66 (q4 c4) ∷
   rw⁻ 65 (q3 c4) ∷
   rw⁻ 64 (q1 c4) ∷
   rw⁻ 63 (q5 c4) ∷
   rw⁻ 89 (q27 c4) ∷
   rw⁻ 88 (q28 c4) ∷
   rw⁻ 90 (q29 c4) ∷
   rw 89 (q30 c4) ∷
   rw⁻ 91 (q31 c4) ∷
   re 90 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 92 (q31 c4) ∷
   rw⁻ 92 (q32 c4) ∷
   rw 91 (q33 c4) ∷
   rw⁻ 93 (q31 c4) ∷
   rw⁻ 92 (q31 c4) ∷
   re 93 3 (CS13 ∷ []) ∷
   rw⁻ 94 (q29 c4) ∷
   rw 93 (q34 c4) ∷
   rw⁻ 95 (q27 c4) ∷
   rw⁻ 94 (q28 c4) ∷
   rw⁻ 95 (q35 c4) ∷
   rw 94 (q36 c4) ∷
   rw 95 (q37 c4) ∷
   rw 96 (q36 c4) ∷
   rw 97 (q37 c4) ∷
   rw 98 (q27 c4) ∷
   rw 93 (q38 c4) ∷
   rw 94 (q39 c4) ∷
   rw 95 (q38 c4) ∷
   rw 96 (q39 c4) ∷
   rw 97 (q29 c4) ∷
   rw 92 (q40 c4) ∷
   rw 93 (q41 c4) ∷
   rw 94 (q40 c4) ∷
   rw 95 (q41 c4) ∷
   rw 96 (q31 c4) ∷
   rw 91 (q42 c4) ∷
   rw 92 (q43 c4) ∷
   rw 93 (q42 c4) ∷
   rw 94 (q43 c4) ∷
   rw 95 (q32 c4) ∷
   rw 90 (q44 c4) ∷
   rw 91 (q45 c4) ∷
   rw 92 (q44 c4) ∷ []) Eq.refl
