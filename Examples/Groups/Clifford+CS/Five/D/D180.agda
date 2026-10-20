{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D180 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0019 ; wl0056 ; wl0061 ; wl0062 ; wl0190 ; wl0212 ; wl0260 ; wl0283 ; wl0353 ; wl0661 ; wl0743 ; wl0754 ; wl0755 ; wl0762 ; wl0772 ; wl0775 ; wl0817 ; wl0818 ; wl0819 ; wl0820 ; wl0821 ; wl0822 ; wl0823 ; wl0824 ; wl0825 ; wl0826 ; wl0827 ; wl0828 ; wl0829 ; wl0830 ; wl0831 ; wl0832 ; wl0833 ; wl0834 ; wl0835 ; wl0836 ; wl0837 ; wl0838 ; wl0839 ; wl0840 ; wp0126 ; wp0343 ; wp0348 ; wp0349 ; wp0352 ; wp0365 ; wp0392 ; wp0411 ; wp0419 ; wp0420 ; wp0421 ; wp0422 ; wp0423 ; wp0424 ; wp0425 ; wp0426 ; wp0427 ; wp0428 ; wp0429 ; wp0430 ; wp0431 ; wp0432 ; wp0433 ; wp0434 ; wp0435 ; wp0436 ; wp0437)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D166 using (lem-sym12-at122441 ; lem-sym12-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-X1-beta-at1441 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 ; lem-beta-T-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at13213442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D179 using (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132130 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩ ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-SBOX⟨1·0·43·2⟩ ; lem-nat-2-SBOX⟨0·3·1·4⟩ ; lem-nat-2-SBOXd⟨0·3·1·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-2-SBOX⟨0·2·1·4⟩ ; lem-nat-2-SBOXd⟨0·2·1·4⟩ ; lem-nat-3-SBOX⟨0·2·1·3⟩ ; lem-nat-3-SBOX⟨0·2·1·4⟩ ; lem-nat-3-SBOXd⟨0·2·1·3⟩ ; lem-nat-3-SBOXd⟨0·2·1·4⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw23 ∷ Sb0-2-1-4 ∷ []) (Sb0-3-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·2·1·4⟩ (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sb0-1-23-4 ∷ Sb0-3-1-4 ∷ []) (Sb0-3-1-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩ c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw23 ∷ Sb0-3-1-4 ∷ []) (Sb0-2-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·1·4⟩ (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(0;3;1;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb0-2-1-4 ∷ []) (Sb0-2-1-4 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw34 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·1·3⟩ (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sb0-1-32-4 ∷ Sb0-2-1-4 ∷ []) (Sb0-2-1-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at2332 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw34 ∷ Sb0-2-1-4 ∷ []) (Sb0-2-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·1·4⟩ (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(0;3;1;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-3 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 0 (q11 c4) ∷
   rw 1 (q12 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw23 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-3-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·2·1·4⟩ (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sb0-1-23-4 ∷ Sb⁻0-3-1-4 ∷ []) (Sb⁻0-3-1-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩ c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw23 ∷ Sb⁻0-3-1-4 ∷ []) (Sb⁻0-2-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·3·1·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(0;3;1;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb⁻0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-2-1-4 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q13 c4) ∷
   rw 1 (q14 c4) ∷
   rw 0 (q15 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw34 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·1·3⟩ (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sb0-1-32-4 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-2-1-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at2332 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw34 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-2-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·1·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(0;3;1;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q16 c4) ∷
   rw 1 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw 1 (q12 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx0-2431 ∷ []) (Bx0-4231 ∷ []) (lem-sym12-at122441 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (X4 ∷ Bx0-4231 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx0-4231 ∷ []) (Bx0-2431 ∷ []) (lem-sym12-at1441 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ123 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Sb0-1-42-3 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at243243 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ123 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132130 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0212 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ []) (wl0743 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (K1⁻ ∷ K1 ∷ []) [] (wl0260 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (wl0817 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (wl0818 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (K1 ∷ X4 ∷ []) (X4 ∷ K1 ∷ []) (c₂ (K ↑) (X ↑ ↑))
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (wp0365 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ []) (wl0762 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ []) (wp0348 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (wp0349 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (K1⁻ ∷ X4 ∷ []) (X4 ∷ K1⁻ ∷ []) (c₂ ((K • iI) ↑) (X ↑ ↑))
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) (wl0819 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (wp0419 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (wl0820 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (wl0821 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (wp0420 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (wp0392 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CS14⁻ ∷ X4 ∷ CX23 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ X4 ∷ CS14⁻ ∷ []) (wl0822 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS14⁻ ∷ []) (wp0421 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ []) (wp0422 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ []) (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) (wl0823 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (wp0423 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ []) (wl0754 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (Sb0-1-42-3 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩-at243243 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ []) (wl0755 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (Sb0-1-42-3 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩-at243243 c4)

-- F4 CS12^0|CS23^1: 420 steps
lem-F4-CS12ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣CS23ᵖ1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw 2 (q21 c4) ∷
   rw 3 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw 1 (q24 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 1 (q20 c4) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 0 (q23 c4) ∷
   rw 4 (q25 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q27 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 5 (q29 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw⁻ 15 (q30 c4) ∷
   re 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   re 8 1 (CS13 ∷ []) ∷
   re 14 1 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q31 c4) ∷
   re 11 1 (Sb0-1-3-2 ∷ []) ∷
   re 17 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 2 (q33 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 12 (q34 c4) ∷
   rw 11 (q35 c4) ∷
   rw⁻ 10 (q34 c4) ∷
   rw 12 (q36 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw⁻ 16 (q19 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw⁻ 23 (q37 c4) ∷
   rw⁻ 20 (q38 c4) ∷
   rw⁻ 17 (q39 c4) ∷
   rw⁻ 14 (q38 c4) ∷
   rw⁻ 11 (q40 c4) ∷
   rw 14 (q19 c4) ∷
   rw 15 (q19 c4) ∷
   rw 16 (q19 c4) ∷
   rw 17 (q19 c4) ∷
   rw⁻ 13 (q36 c4) ∷
   rw⁻ 14 (q41 c4) ∷
   rw 13 (q42 c4) ∷
   rw⁻ 12 (q41 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   rw⁻ 6 (q34 c4) ∷
   rw 5 (q35 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 6 (q36 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw⁻ 16 (q19 c4) ∷
   rw⁻ 17 (q37 c4) ∷
   rw⁻ 14 (q38 c4) ∷
   rw⁻ 11 (q39 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw⁻ 5 (q40 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q19 c4) ∷
   rw 10 (q19 c4) ∷
   rw 11 (q19 c4) ∷
   rw⁻ 7 (q36 c4) ∷
   rw⁻ 8 (q41 c4) ∷
   rw 7 (q42 c4) ∷
   rw⁻ 6 (q41 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q19 c4) ∷
   rw 8 (q19 c4) ∷
   rw⁻ 5 (q33 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q19 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q19 c4) ∷
   re 5 5 (Sb0-1-42-3 ∷ []) ∷
   re 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   re 11 1 (CS13 ∷ []) ∷
   re 17 1 (CS13⁻ ∷ []) ∷
   rw⁻ 10 (q44 c4) ∷
   re 23 1 (Sb0-1-3-2 ∷ []) ∷
   re 29 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 7 (q45 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw⁻ 15 (q34 c4) ∷
   rw 14 (q35 c4) ∷
   rw⁻ 13 (q34 c4) ∷
   rw⁻ 14 (q46 c4) ∷
   rw⁻ 17 (q41 c4) ∷
   rw 16 (q42 c4) ∷
   rw⁻ 15 (q41 c4) ∷
   rw⁻ 18 (q34 c4) ∷
   rw 17 (q35 c4) ∷
   rw⁻ 16 (q34 c4) ∷
   rw 18 (q36 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw⁻ 25 (q19 c4) ∷
   rw⁻ 28 (q19 c4) ∷
   rw⁻ 29 (q47 c4) ∷
   rw⁻ 26 (q48 c4) ∷
   rw⁻ 23 (q49 c4) ∷
   rw⁻ 20 (q48 c4) ∷
   rw⁻ 17 (q50 c4) ∷
   rw 20 (q19 c4) ∷
   rw 21 (q19 c4) ∷
   rw 22 (q19 c4) ∷
   rw 23 (q19 c4) ∷
   rw⁻ 19 (q36 c4) ∷
   rw⁻ 20 (q41 c4) ∷
   rw 19 (q42 c4) ∷
   rw⁻ 18 (q41 c4) ∷
   rw⁻ 21 (q34 c4) ∷
   rw 20 (q35 c4) ∷
   rw⁻ 19 (q34 c4) ∷
   rw⁻ 20 (q46 c4) ∷
   rw⁻ 23 (q41 c4) ∷
   rw 22 (q42 c4) ∷
   rw⁻ 21 (q41 c4) ∷
   rw⁻ 24 (q34 c4) ∷
   rw 23 (q35 c4) ∷
   rw⁻ 22 (q34 c4) ∷
   rw⁻ 25 (q51 c4) ∷
   rw 24 (q52 c4) ∷
   rw⁻ 23 (q51 c4) ∷
   rw⁻ 26 (q41 c4) ∷
   rw 25 (q42 c4) ∷
   rw⁻ 24 (q41 c4) ∷
   rw⁻ 10 (q53 c4) ∷
   rw⁻ 9 (q34 c4) ∷
   rw 8 (q35 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw⁻ 11 (q41 c4) ∷
   rw 10 (q42 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   rw⁻ 12 (q34 c4) ∷
   rw 11 (q35 c4) ∷
   rw⁻ 10 (q34 c4) ∷
   rw 12 (q36 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw⁻ 16 (q19 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw⁻ 23 (q47 c4) ∷
   rw⁻ 20 (q48 c4) ∷
   rw⁻ 17 (q49 c4) ∷
   rw⁻ 14 (q48 c4) ∷
   rw⁻ 11 (q50 c4) ∷
   rw 14 (q19 c4) ∷
   rw 15 (q19 c4) ∷
   rw 16 (q19 c4) ∷
   rw 17 (q19 c4) ∷
   rw⁻ 13 (q36 c4) ∷
   rw⁻ 14 (q41 c4) ∷
   rw 13 (q42 c4) ∷
   rw⁻ 12 (q41 c4) ∷
   rw⁻ 15 (q34 c4) ∷
   rw 14 (q35 c4) ∷
   rw⁻ 13 (q34 c4) ∷
   rw⁻ 14 (q46 c4) ∷
   rw⁻ 17 (q41 c4) ∷
   rw 16 (q42 c4) ∷
   rw⁻ 15 (q41 c4) ∷
   rw⁻ 18 (q34 c4) ∷
   rw 17 (q35 c4) ∷
   rw⁻ 16 (q34 c4) ∷
   rw⁻ 19 (q51 c4) ∷
   rw 18 (q52 c4) ∷
   rw⁻ 17 (q51 c4) ∷
   rw⁻ 20 (q41 c4) ∷
   rw 19 (q42 c4) ∷
   rw⁻ 18 (q41 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw 18 (q19 c4) ∷
   rw 19 (q19 c4) ∷
   rw 20 (q19 c4) ∷
   rw⁻ 17 (q33 c4) ∷
   rw 18 (q19 c4) ∷
   rw 19 (q19 c4) ∷
   rw 20 (q19 c4) ∷
   rw 21 (q19 c4) ∷
   re 17 5 (Sb0-1-42-3 ∷ []) ∷
   rw 3 (q30 c4) ∷
   rw 4 (q30 c4) ∷
   rw 5 (q30 c4) ∷
   rw 6 (q30 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 1 (q28 c4) ∷
   re 5 1 (CS12 ∷ []) ∷
   rw⁻ 4 (q54 c4) ∷
   re 4 1 (Sb0-2-1-3 ∷ []) ∷
   rw 3 (q55 c4) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q54 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 7 (q29 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 11 (q30 c4) ∷
   rw⁻ 14 (q30 c4) ∷
   rw⁻ 17 (q30 c4) ∷
   re 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   re 10 1 (CS13 ∷ []) ∷
   re 16 1 (CS13⁻ ∷ []) ∷
   rw⁻ 9 (q31 c4) ∷
   re 13 1 (Sb0-1-3-2 ∷ []) ∷
   re 19 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 6 (q32 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw⁻ 14 (q34 c4) ∷
   rw 13 (q35 c4) ∷
   rw⁻ 12 (q34 c4) ∷
   rw 14 (q36 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw⁻ 18 (q19 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw⁻ 24 (q19 c4) ∷
   rw⁻ 25 (q37 c4) ∷
   rw⁻ 22 (q38 c4) ∷
   rw⁻ 19 (q39 c4) ∷
   rw⁻ 16 (q38 c4) ∷
   rw⁻ 13 (q40 c4) ∷
   rw 16 (q19 c4) ∷
   rw 17 (q19 c4) ∷
   rw 18 (q19 c4) ∷
   rw 19 (q19 c4) ∷
   rw⁻ 15 (q36 c4) ∷
   rw⁻ 16 (q41 c4) ∷
   rw 15 (q42 c4) ∷
   rw⁻ 14 (q41 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   rw⁻ 8 (q34 c4) ∷
   rw 7 (q35 c4) ∷
   rw⁻ 6 (q34 c4) ∷
   rw 8 (q36 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw⁻ 18 (q19 c4) ∷
   rw⁻ 19 (q37 c4) ∷
   rw⁻ 16 (q38 c4) ∷
   rw⁻ 13 (q39 c4) ∷
   rw⁻ 10 (q38 c4) ∷
   rw⁻ 7 (q40 c4) ∷
   rw 10 (q19 c4) ∷
   rw 11 (q19 c4) ∷
   rw 12 (q19 c4) ∷
   rw 13 (q19 c4) ∷
   rw⁻ 9 (q36 c4) ∷
   rw⁻ 10 (q41 c4) ∷
   rw 9 (q42 c4) ∷
   rw⁻ 8 (q41 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q19 c4) ∷
   rw 10 (q19 c4) ∷
   rw⁻ 7 (q33 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q19 c4) ∷
   rw 10 (q19 c4) ∷
   rw 11 (q19 c4) ∷
   re 7 5 (Sb0-1-42-3 ∷ []) ∷
   re 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   re 13 1 (CS13 ∷ []) ∷
   re 19 1 (CS13⁻ ∷ []) ∷
   rw⁻ 12 (q44 c4) ∷
   re 25 1 (Sb0-1-3-2 ∷ []) ∷
   re 31 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 9 (q45 c4) ∷
   rw 7 (q33 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 17 (q34 c4) ∷
   rw 16 (q35 c4) ∷
   rw⁻ 15 (q34 c4) ∷
   rw⁻ 16 (q46 c4) ∷
   rw⁻ 19 (q41 c4) ∷
   rw 18 (q42 c4) ∷
   rw⁻ 17 (q41 c4) ∷
   rw⁻ 20 (q34 c4) ∷
   rw 19 (q35 c4) ∷
   rw⁻ 18 (q34 c4) ∷
   rw 20 (q36 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw⁻ 24 (q19 c4) ∷
   rw⁻ 27 (q19 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw⁻ 31 (q47 c4) ∷
   rw⁻ 28 (q48 c4) ∷
   rw⁻ 25 (q49 c4) ∷
   rw⁻ 22 (q48 c4) ∷
   rw⁻ 19 (q50 c4) ∷
   rw 22 (q19 c4) ∷
   rw 23 (q19 c4) ∷
   rw 24 (q19 c4) ∷
   rw 25 (q19 c4) ∷
   rw⁻ 21 (q36 c4) ∷
   rw⁻ 22 (q41 c4) ∷
   rw 21 (q42 c4) ∷
   rw⁻ 20 (q41 c4) ∷
   rw⁻ 23 (q34 c4) ∷
   rw 22 (q35 c4) ∷
   rw⁻ 21 (q34 c4) ∷
   rw⁻ 22 (q46 c4) ∷
   rw⁻ 25 (q41 c4) ∷
   rw 24 (q42 c4) ∷
   rw⁻ 23 (q41 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw 25 (q35 c4) ∷
   rw⁻ 24 (q34 c4) ∷
   rw⁻ 27 (q51 c4) ∷
   rw 26 (q52 c4) ∷
   rw⁻ 25 (q51 c4) ∷
   rw⁻ 28 (q41 c4) ∷
   rw 27 (q42 c4) ∷
   rw⁻ 26 (q41 c4) ∷
   rw⁻ 12 (q53 c4) ∷
   rw⁻ 11 (q34 c4) ∷
   rw 10 (q35 c4) ∷
   rw⁻ 9 (q34 c4) ∷
   rw⁻ 10 (q46 c4) ∷
   rw⁻ 13 (q41 c4) ∷
   rw 12 (q42 c4) ∷
   rw⁻ 11 (q41 c4) ∷
   rw⁻ 14 (q34 c4) ∷
   rw 13 (q35 c4) ∷
   rw⁻ 12 (q34 c4) ∷
   rw 14 (q36 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw⁻ 18 (q19 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw⁻ 24 (q19 c4) ∷
   rw⁻ 25 (q47 c4) ∷
   rw⁻ 22 (q48 c4) ∷
   rw⁻ 19 (q49 c4) ∷
   rw⁻ 16 (q48 c4) ∷
   rw⁻ 13 (q50 c4) ∷
   rw 16 (q19 c4) ∷
   rw 17 (q19 c4) ∷
   rw 18 (q19 c4) ∷
   rw 19 (q19 c4) ∷
   rw⁻ 15 (q36 c4) ∷
   rw⁻ 16 (q41 c4) ∷
   rw 15 (q42 c4) ∷
   rw⁻ 14 (q41 c4) ∷
   rw⁻ 17 (q34 c4) ∷
   rw 16 (q35 c4) ∷
   rw⁻ 15 (q34 c4) ∷
   rw⁻ 16 (q46 c4) ∷
   rw⁻ 19 (q41 c4) ∷
   rw 18 (q42 c4) ∷
   rw⁻ 17 (q41 c4) ∷
   rw⁻ 20 (q34 c4) ∷
   rw 19 (q35 c4) ∷
   rw⁻ 18 (q34 c4) ∷
   rw⁻ 21 (q51 c4) ∷
   rw 20 (q52 c4) ∷
   rw⁻ 19 (q51 c4) ∷
   rw⁻ 22 (q41 c4) ∷
   rw 21 (q42 c4) ∷
   rw⁻ 20 (q41 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw 20 (q19 c4) ∷
   rw 21 (q19 c4) ∷
   rw 22 (q19 c4) ∷
   rw⁻ 19 (q33 c4) ∷
   rw 20 (q19 c4) ∷
   rw 21 (q19 c4) ∷
   rw 22 (q19 c4) ∷
   rw 23 (q19 c4) ∷
   re 19 5 (Sb0-1-42-3 ∷ []) ∷
   rw 5 (q30 c4) ∷
   rw 6 (q30 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q30 c4) ∷
   rw⁻ 4 (q29 c4) ∷
   rw 3 (q28 c4) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 6 (q56 c4) ∷
   re 6 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw 5 (q57 c4) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q56 c4) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (Sw01 ∷ Sb0-1-43-2 ∷ []) (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CS03 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CS03 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at13213442 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (Sw01 ∷ Sb1-0-43-2 ∷ []) (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 (lit c4))

-- auto CS01 | SBOX(2;0;31;4) @0113203442: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0113203442 : Ws → ⟪ (CS13 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CS13 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0113203442 c4 = derive (CS13 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS13 ∷ [])
  (rw⁻ 0 (q58 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw 2 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   rw 0 (q62 c4) ∷
   rw⁻ 1 (q63 c4) ∷
   rw 2 (q58 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = eqn (S4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ S4 ∷ []) (wl0824 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (S4 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ S4 ∷ []) (wl0825 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (S4 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ S4 ∷ []) (wl0826 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (S4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ S4 ∷ []) (wp0424 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (S4 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ S4 ∷ []) (wp0425 c4)

-- F4 CS23^0|iI^1: 30 steps
lem-F4-CS23ᵖ0∣iIᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣iIᵖ1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 2 (q19 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   re 13 1 (CS12⁻ ∷ []) ∷
   rw⁻ 12 (q64 c4) ∷
   re 14 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 9 (q65 c4) ∷
   re 7 1 (CS12 ∷ []) ∷
   rw⁻ 6 (q66 c4) ∷
   re 8 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q65 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw⁻ 6 (q69 c4) ∷
   rw⁻ 3 (q68 c4) ∷
   rw⁻ 0 (q69 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q19 c4) ∷
   re 2 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = eqn (CS04 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ []) (wp0426 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ CS04 ∷ []) (wp0427 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ []) (wp0343 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (CS04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ CS04 ∷ []) (wp0428 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (CS04 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ CS04 ∷ []) (wp0429 c4)

-- F4 CS23^0|S0^1: 30 steps
lem-F4-CS23ᵖ0∣S0ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣S0ᵖ1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 2 (q19 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   re 13 1 (CS12⁻ ∷ []) ∷
   rw⁻ 12 (q70 c4) ∷
   re 14 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 9 (q71 c4) ∷
   re 7 1 (CS12 ∷ []) ∷
   rw⁻ 6 (q72 c4) ∷
   re 8 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q71 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 9 (q73 c4) ∷
   rw⁻ 6 (q74 c4) ∷
   rw⁻ 3 (q73 c4) ∷
   rw⁻ 0 (q74 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q19 c4) ∷
   re 2 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = eqn (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ CS14 ∷ []) (wl0827 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CS14 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ CS14 ∷ []) (wl0828 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS14 ∷ []) (wl0829 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ CS14 ∷ []) (wp0430 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ CS14 ∷ []) (wp0431 c4)

-- F4 CS23^0|S1^1: 30 steps
lem-F4-CS23ᵖ0∣S1ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣S1ᵖ1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 2 (q19 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   re 13 1 (CS12⁻ ∷ []) ∷
   rw⁻ 12 (q75 c4) ∷
   re 14 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 9 (q76 c4) ∷
   re 7 1 (CS12 ∷ []) ∷
   rw⁻ 6 (q77 c4) ∷
   re 8 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q76 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 9 (q78 c4) ∷
   rw⁻ 6 (q79 c4) ∷
   rw⁻ 3 (q78 c4) ∷
   rw⁻ 0 (q79 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q19 c4) ∷
   re 2 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (CS24 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ CS24 ∷ []) (wl0830 (lit c4))
  q81 : Ws → Eqn
  q81 c4 = eqn (CS24 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ CS24 ∷ []) (wl0831 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (CS24 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS24 ∷ []) (wl0832 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (wp0352 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ []) (wl0834 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ []) (wp0432 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (wp0411 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ []) (wp0433 c4)

-- F4 CS23^0|S2^1: 58 steps
lem-F4-CS23ᵖ0∣S2ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣S2ᵖ1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 2 (q19 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   re 13 1 (CS12⁻ ∷ []) ∷
   rw⁻ 12 (q80 c4) ∷
   re 14 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 9 (q81 c4) ∷
   re 7 1 (CS12 ∷ []) ∷
   rw⁻ 6 (q82 c4) ∷
   re 8 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q81 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw 10 (q83 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw⁻ 21 (q84 c4) ∷
   rw⁻ 18 (q85 c4) ∷
   rw⁻ 15 (q86 c4) ∷
   rw⁻ 12 (q85 c4) ∷
   rw⁻ 9 (q87 c4) ∷
   rw 12 (q19 c4) ∷
   rw 13 (q19 c4) ∷
   rw 14 (q19 c4) ∷
   rw 15 (q19 c4) ∷
   rw⁻ 11 (q83 c4) ∷
   rw⁻ 6 (q88 c4) ∷
   rw 4 (q83 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 15 (q84 c4) ∷
   rw⁻ 12 (q85 c4) ∷
   rw⁻ 9 (q86 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw⁻ 3 (q87 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q19 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q19 c4) ∷
   rw⁻ 5 (q83 c4) ∷
   rw⁻ 0 (q88 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q19 c4) ∷
   re 2 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = eqn (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ []) (wl0835 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (CS34 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ CS34 ∷ []) (wl0836 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS34 ∷ []) (wl0837 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (CS34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ CS34 ∷ []) (wp0434 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (CS34 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ CS34 ∷ []) (wp0435 c4)

-- F4 CS23^0|S3^1: 30 steps
lem-F4-CS23ᵖ0∣S3ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣S3ᵖ1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 2 (q19 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   re 13 1 (CS12⁻ ∷ []) ∷
   rw⁻ 12 (q89 c4) ∷
   re 14 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 9 (q90 c4) ∷
   re 7 1 (CS12 ∷ []) ∷
   rw⁻ 6 (q91 c4) ∷
   re 8 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q90 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 9 (q92 c4) ∷
   rw⁻ 6 (q93 c4) ∷
   rw⁻ 3 (q92 c4) ∷
   rw⁻ 0 (q93 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q19 c4) ∷
   re 2 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q97 : Ws → Eqn
  q97 c4 = eqn (Sb0-1-43-2 ∷ K0 ∷ []) (K0 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2442 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (Sw12 ∷ Sb0-1-43-2 ∷ []) (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4))

-- auto SBOX(0;1;23;4) | K0 @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at122441 c4 = derive (Sb0-2-43-1 ∷ K0 ∷ []) (K0 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q94 c4) ∷
   rw 1 (q95 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw⁻ 0 (q96 c4) ∷
   rw 1 (q98 c4) ∷
   rw 2 (q94 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = eqn (CK40 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp0126 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (X4 ∷ ι ∷ []) (ι ∷ X4 ∷ []) (zc)
  q101 : Ws → Eqn
  q101 c4 = eqn (Sb0-2-43-1 ∷ ι ∷ []) (ι ∷ Sb0-2-43-1 ∷ []) (zc)
  q102 : Ws → Eqn
  q102 c4 = eqn (S4⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ S4⁻ ∷ []) (wl0838 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (S4⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ S4⁻ ∷ []) (wl0839 (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ S4⁻ ∷ []) (wl0840 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ S4⁻ ∷ []) (wp0436 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ S4⁻ ∷ []) (wp0437 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ []) (wl0772 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (Sb0-2-43-1 ∷ K0 ∷ []) (K0 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at122441 c4)

-- F4 CS23^0|K0^1: 131 steps
lem-F4-CS23ᵖ0∣K0ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣K0ᵖ1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 3 (q99 c4) ∷
   rw 2 (q100 c4) ∷
   rw 1 (q101 c4) ∷
   rw 0 (q100 c4) ∷
   re 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   re 14 1 (CS12⁻ ∷ []) ∷
   rw⁻ 13 (q102 c4) ∷
   re 15 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 10 (q103 c4) ∷
   re 8 1 (CS12 ∷ []) ∷
   rw⁻ 7 (q104 c4) ∷
   re 9 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q103 c4) ∷
   rw 2 (q67 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 10 (q105 c4) ∷
   rw⁻ 7 (q106 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   rw⁻ 1 (q106 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q19 c4) ∷
   rw⁻ 3 (q67 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q19 c4) ∷
   re 3 5 (Sb0-2-43-1 ∷ []) ∷
   re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q19 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   re 15 1 (CS12⁻ ∷ []) ∷
   rw⁻ 14 (q70 c4) ∷
   re 16 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 11 (q71 c4) ∷
   re 9 1 (CS12 ∷ []) ∷
   rw⁻ 8 (q72 c4) ∷
   re 10 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 5 (q71 c4) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw⁻ 11 (q73 c4) ∷
   rw⁻ 8 (q74 c4) ∷
   rw⁻ 5 (q73 c4) ∷
   rw⁻ 2 (q74 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q19 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q19 c4) ∷
   rw 8 (q19 c4) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 5 (q107 c4) ∷
   rw 4 (q108 c4) ∷
   rw⁻ 3 (q107 c4) ∷
   re 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   re 17 1 (CS12⁻ ∷ []) ∷
   rw⁻ 16 (q70 c4) ∷
   re 18 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 13 (q71 c4) ∷
   re 11 1 (CS12 ∷ []) ∷
   rw⁻ 10 (q72 c4) ∷
   re 12 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 7 (q71 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw⁻ 13 (q73 c4) ∷
   rw⁻ 10 (q74 c4) ∷
   rw⁻ 7 (q73 c4) ∷
   rw⁻ 4 (q74 c4) ∷
   rw 7 (q19 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q19 c4) ∷
   rw⁻ 6 (q67 c4) ∷
   rw 7 (q19 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q19 c4) ∷
   rw 10 (q19 c4) ∷
   re 6 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 7 (q107 c4) ∷
   rw 6 (q108 c4) ∷
   rw⁻ 5 (q107 c4) ∷
   re 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   re 19 1 (CS12⁻ ∷ []) ∷
   rw⁻ 18 (q70 c4) ∷
   re 20 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 15 (q71 c4) ∷
   re 13 1 (CS12 ∷ []) ∷
   rw⁻ 12 (q72 c4) ∷
   re 14 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 9 (q71 c4) ∷
   rw 7 (q67 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 15 (q73 c4) ∷
   rw⁻ 12 (q74 c4) ∷
   rw⁻ 9 (q73 c4) ∷
   rw⁻ 6 (q74 c4) ∷
   rw 9 (q19 c4) ∷
   rw 10 (q19 c4) ∷
   rw 11 (q19 c4) ∷
   rw⁻ 8 (q67 c4) ∷
   rw 9 (q19 c4) ∷
   rw 10 (q19 c4) ∷
   rw 11 (q19 c4) ∷
   rw 12 (q19 c4) ∷
   re 8 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 0 (q99 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (Sb0-1-43-2 ∷ K2 ∷ []) (K2 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2442 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl0062 (lit c4))

-- auto SBOX(0;1;23;4) | K4 @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at122441 c4 = derive (Sb0-2-43-1 ∷ K1 ∷ []) (K1 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q94 c4) ∷
   rw 1 (q95 c4) ∷
   rw⁻ 2 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw⁻ 0 (q111 c4) ∷
   rw 1 (q98 c4) ∷
   rw 2 (q94 c4) ∷ []) Eq.refl
