{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D201 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0160 ; wl0163 ; wl0164 ; wl0165 ; wl0328 ; wl0495 ; wl0889 ; wl0890 ; wl0891 ; wl0894 ; wl0910 ; wl0911 ; wl0912 ; wl0913 ; wl0914 ; wl0915 ; wl0916 ; wl0917 ; wl0918 ; wl0919 ; wl0920 ; wl0921 ; wl0922 ; wl0923 ; wl0924 ; wl0925 ; wl0926 ; wl0927 ; wl0928 ; wl0929 ; wp0462 ; wp0463 ; wp0464 ; wp0466 ; wp0467 ; wp0473 ; wp0474 ; wp0475 ; wp0476 ; wp0477 ; wp0478 ; wp0479 ; wp0480 ; wp0481 ; wp0482 ; wp0483 ; wp0484 ; wp0485 ; wp0486 ; wp0487 ; wp0488 ; wp0489 ; wp0490 ; wp0491 ; wp0492 ; wp0493 ; wp0494 ; wp0495 ; wp0496 ; wp0497 ; wp0498 ; wp0499 ; wp0500 ; wp0501)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-F0-at011220)
open import Examples.Groups.Clifford+CS.Five.D.D162 using (lem-F1-rel-266 ; lem-F1-rel-267 ; lem-F1-rel-268)
open import Examples.Groups.Clifford+CS.Five.D.D165 using (lem-F1-cx-ccz)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-F1-toff-ccz ; lem-F2-K0∣CS12 ; lem-F2-K0∣CS23 ; lem-F2-K1∣CS23 ; lem-F2-K2∣CS01 ; lem-F2-K3∣CS01 ; lem-F2-K3∣CS12 ; lem-F2-S0∣CS12 ; lem-F2-S0∣CS23 ; lem-F2-S1∣CS23 ; lem-F2-S2∣CS01 ; lem-F2-S3∣CS01 ; lem-F2-S3∣CS12 ; lem-F2-iI∣CS01 ; lem-F2-iI∣CS12 ; lem-F2-iI∣CS23 ; lem-F4-iIᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-F4-K0ᵖ0∣CS01ᵖ1 ; lem-F4-K0ᵖ0∣CS12ᵖ1 ; lem-F4-K0ᵖ0∣CS23ᵖ1 ; lem-F4-S0ᵖ0∣CS01ᵖ1 ; lem-F4-S0ᵖ0∣CS12ᵖ1 ; lem-F4-S0ᵖ0∣CS23ᵖ1 ; lem-F4-iIᵖ0∣CS12ᵖ1 ; lem-F4-iIᵖ0∣CS23ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-F0-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D186 using (lem-F2-CS01∣CS23)
open import Examples.Groups.Clifford+CS.Five.D.D195 using (lem-F1-rel-269)
open import Examples.Groups.Clifford+CS.Five.D.D200 using (lem-F0-at01122330 ; lem-F1-comm-CS-CS-at01122330 ; lem-F1-rel-272)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-SBOX⟨3·0·41·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-SBOX⟨0·2·43·1⟩ ; lem-nat-0-SBOX⟨1·2·43·0⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-SBOX⟨3·0·42·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-CK41 ; lem-nat-1-CK40 ; lem-nat-2-CK40)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-SBOX⟨3·0·42·1⟩ ; lem-nat-2-SBOX⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨3·0·41·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-0-SBOX⟨3·1·42·0⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw01 ∷ Sb1-2-43-0 ∷ []) (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4)

-- F0 @02132130: 5 steps
lem-F0-at02132130 : Ws → ⟪ (Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F0-at02132130 c4 = derive (Sb1-2-43-0 ∷ []) (Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q4 : Ws → Eqn
  q4 c4 = eqn (Sb0-1-42-3 ∷ []) (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Sb1-2-43-0 ∷ Sb3-1-42-0 ∷ []) (Sb3-1-42-0 ∷ Sb1-2-43-0 ∷ []) (lem-F1-comm-CS-CS-at01122330 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Sb3-1-42-0 ∷ []) (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Sb1-2-43-0 ∷ []) (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4)

-- tr comm-CS-CS at 1: 5 steps
lem-tr-comm-CS-CS-at-1 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm-CS-CS-at-1 c4 = derive (Sb0-2-43-1 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ [])
  (rw 0 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 0 (q5 c4) ∷
   rw 0 (q6 c4) ∷
   rw 1 (q7 c4) ∷ []) Eq.refl

private
  q8 : Ws → Eqn
  q8 c4 = eqn (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (lem-F1-rel-266 c4)

-- tr rel-266 at 0: 1 steps
lem-tr-rel-266-at-0 : Ws → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-tr-rel-266-at-0 c4 = derive (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ [])
  (rw 0 (q8 c4) ∷ []) Eq.refl

private
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw23 ∷ CK40 ∷ []) (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw23 ∷ Sb3-0-41-2 ∷ []) (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q13 : Ws → Eqn
  q13 c4 = eqn (CK41 ∷ Sw23 ∷ []) (Sw23 ∷ CK41 ∷ []) (wl0165 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) (wl0163 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw23 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4))

-- F1 rel-266 @2332: 45 steps
lem-F1-rel-266-at2332 : Ws → ⟪ (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266-at2332 c4 = derive (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q11 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 7 (q11 c4) ∷
   rw 8 (q11 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 10 (q12 c4) ∷
   rw 11 (q14 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q11 c4) ∷
   rw⁻ 15 (q13 c4) ∷
   rw 16 (q12 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q11 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q10 c4) ∷
   rw 21 (q12 c4) ∷
   rw 1 (q8 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q16 c4) ∷
   rw⁻ 3 (q15 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q16 c4) ∷
   rw 7 (q16 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 9 (q12 c4) ∷
   rw 10 (q17 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw 12 (q16 c4) ∷
   rw 13 (q16 c4) ∷
   rw⁻ 14 (q13 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw 17 (q16 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 19 (q15 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q9 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw12 ∷ CK40 ∷ []) (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw12 ∷ Sb3-0-42-1 ∷ []) (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q22 : Ws → Eqn
  q22 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl0160 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ []) (lem-F1-rel-266-at2332 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw12 ∷ Sb0-1-43-2 ∷ []) (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CK42 ∷ Sw12 ∷ []) (Sw12 ∷ CK41 ∷ []) (wl0164 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw12 ∷ Sb3-0-41-2 ∷ []) (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4))

-- F1 rel-266 @122331: 45 steps
lem-F1-rel-266-at122331 : Ws → ⟪ (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266-at122331 c4 = derive (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw 7 (q20 c4) ∷
   rw 8 (q20 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw 10 (q21 c4) ∷
   rw 11 (q23 c4) ∷
   rw⁻ 12 (q22 c4) ∷
   rw 13 (q20 c4) ∷
   rw 14 (q20 c4) ∷
   rw⁻ 15 (q22 c4) ∷
   rw 16 (q21 c4) ∷
   rw 17 (q19 c4) ∷
   rw 18 (q20 c4) ∷
   rw 19 (q20 c4) ∷
   rw 20 (q19 c4) ∷
   rw 21 (q21 c4) ∷
   rw 1 (q24 c4) ∷
   rw 0 (q25 c4) ∷
   rw 1 (q26 c4) ∷
   rw 2 (q26 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   rw 6 (q26 c4) ∷
   rw 7 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q21 c4) ∷
   rw 10 (q28 c4) ∷
   rw⁻ 11 (q27 c4) ∷
   rw 12 (q26 c4) ∷
   rw 13 (q26 c4) ∷
   rw⁻ 14 (q27 c4) ∷
   rw 15 (q21 c4) ∷
   rw 16 (q25 c4) ∷
   rw 17 (q26 c4) ∷
   rw 18 (q26 c4) ∷
   rw 19 (q25 c4) ∷
   rw 20 (q21 c4) ∷
   rw 21 (q18 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = eqn (Sw01 ∷ CK41 ∷ []) (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (Sw01 ∷ Sb3-1-42-0 ∷ []) (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))
  q33 : Ws → Eqn
  q33 c4 = eqn (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (lem-F1-rel-266-at122331 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Sw01 ∷ CK43 ∷ []) (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑))
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (Sw01 ∷ Sb3-0-42-1 ∷ []) (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4))

-- F1 rel-266 @01122330: 45 steps
lem-F1-rel-266-at01122330 : Ws → ⟪ (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266-at01122330 c4 = derive (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q29 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q30 c4) ∷
   rw 4 (q29 c4) ∷
   rw 5 (q31 c4) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q30 c4) ∷
   rw 9 (q32 c4) ∷
   rw 10 (q31 c4) ∷
   rw 11 (q2 c4) ∷
   rw 12 (q32 c4) ∷
   rw 13 (q30 c4) ∷
   rw 14 (q30 c4) ∷
   rw 15 (q32 c4) ∷
   rw 16 (q31 c4) ∷
   rw 17 (q29 c4) ∷
   rw 18 (q30 c4) ∷
   rw 19 (q30 c4) ∷
   rw 20 (q29 c4) ∷
   rw 21 (q31 c4) ∷
   rw 1 (q33 c4) ∷
   rw 0 (q34 c4) ∷
   rw 1 (q35 c4) ∷
   rw 2 (q35 c4) ∷
   rw 3 (q34 c4) ∷
   rw 4 (q31 c4) ∷
   rw 5 (q32 c4) ∷
   rw 6 (q35 c4) ∷
   rw 7 (q35 c4) ∷
   rw 8 (q32 c4) ∷
   rw 9 (q31 c4) ∷
   rw 10 (q36 c4) ∷
   rw 11 (q32 c4) ∷
   rw 12 (q35 c4) ∷
   rw 13 (q35 c4) ∷
   rw 14 (q32 c4) ∷
   rw 15 (q31 c4) ∷
   rw 16 (q34 c4) ∷
   rw 17 (q35 c4) ∷
   rw 18 (q35 c4) ∷
   rw 19 (q34 c4) ∷
   rw 20 (q31 c4) ∷
   rw 21 (q1 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = eqn (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ []) (lem-F1-rel-266-at01122330 c4)

-- tr rel-266 at 1: 19 steps
lem-tr-rel-266-at-1 : Ws → ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-tr-rel-266-at-1 c4 = derive (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  (rw 1 (q4 c4) ∷
   rw 2 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw 10 (q3 c4) ∷
   rw 12 (q4 c4) ∷
   rw 13 (q4 c4) ∷
   rw 17 (q4 c4) ∷
   rw 18 (q4 c4) ∷
   rw 0 (q37 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q7 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q7 c4) ∷
   rw 10 (q6 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q7 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q7 c4) ∷ []) Eq.refl

private
  q38 : Ws → Eqn
  q38 c4 = eqn (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (lem-F1-rel-267 c4)

-- tr rel-267 at 0: 1 steps
lem-tr-rel-267-at-0 : Ws → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-rel-267-at-0 c4 = derive (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q38 c4) ∷ []) Eq.refl

-- F1 rel-267 @2332: 39 steps
lem-F1-rel-267-at2332 : Ws → ⟪ (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-rel-267-at2332 c4 = derive (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q11 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 7 (q11 c4) ∷
   rw 8 (q11 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 10 (q12 c4) ∷
   rw 11 (q14 c4) ∷
   rw 12 (q14 c4) ∷
   rw⁻ 13 (q13 c4) ∷
   rw 14 (q11 c4) ∷
   rw 15 (q11 c4) ∷
   rw⁻ 16 (q13 c4) ∷
   rw 17 (q12 c4) ∷
   rw 18 (q10 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q11 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q12 c4) ∷
   rw 1 (q38 c4) ∷
   rw⁻ 0 (q13 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q17 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 4 (q12 c4) ∷
   rw 5 (q16 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 8 (q17 c4) ∷
   rw 9 (q17 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw 11 (q12 c4) ∷
   rw 12 (q16 c4) ∷
   rw 13 (q16 c4) ∷
   rw 14 (q9 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) (lem-F1-rel-267-at2332 c4)

-- F1 rel-267 @122331: 39 steps
lem-F1-rel-267-at122331 : Ws → ⟪ (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-rel-267-at122331 c4 = derive (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw 7 (q20 c4) ∷
   rw 8 (q20 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw 10 (q21 c4) ∷
   rw 11 (q23 c4) ∷
   rw 12 (q23 c4) ∷
   rw⁻ 13 (q22 c4) ∷
   rw 14 (q20 c4) ∷
   rw 15 (q20 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw 17 (q21 c4) ∷
   rw 18 (q19 c4) ∷
   rw 19 (q20 c4) ∷
   rw 20 (q20 c4) ∷
   rw 21 (q19 c4) ∷
   rw 22 (q21 c4) ∷
   rw 1 (q39 c4) ∷
   rw⁻ 0 (q27 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q28 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q26 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 8 (q28 c4) ∷
   rw 9 (q28 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 11 (q21 c4) ∷
   rw 12 (q26 c4) ∷
   rw 13 (q26 c4) ∷
   rw 14 (q18 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = eqn (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (lem-F1-rel-267-at122331 c4)

-- F1 rel-267 @01122330: 39 steps
lem-F1-rel-267-at01122330 : Ws → ⟪ (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ
lem-F1-rel-267-at01122330 c4 = derive (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q29 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q30 c4) ∷
   rw 4 (q29 c4) ∷
   rw 5 (q31 c4) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q30 c4) ∷
   rw 9 (q32 c4) ∷
   rw 10 (q31 c4) ∷
   rw 11 (q2 c4) ∷
   rw 12 (q2 c4) ∷
   rw 13 (q32 c4) ∷
   rw 14 (q30 c4) ∷
   rw 15 (q30 c4) ∷
   rw 16 (q32 c4) ∷
   rw 17 (q31 c4) ∷
   rw 18 (q29 c4) ∷
   rw 19 (q30 c4) ∷
   rw 20 (q30 c4) ∷
   rw 21 (q29 c4) ∷
   rw 22 (q31 c4) ∷
   rw 1 (q40 c4) ∷
   rw 0 (q32 c4) ∷
   rw 1 (q36 c4) ∷
   rw 2 (q36 c4) ∷
   rw 3 (q32 c4) ∷
   rw 4 (q31 c4) ∷
   rw 5 (q35 c4) ∷
   rw 6 (q35 c4) ∷
   rw 7 (q32 c4) ∷
   rw 8 (q36 c4) ∷
   rw 9 (q36 c4) ∷
   rw 10 (q32 c4) ∷
   rw 11 (q31 c4) ∷
   rw 12 (q35 c4) ∷
   rw 13 (q35 c4) ∷
   rw 14 (q1 c4) ∷ []) Eq.refl

private
  q41 : Ws → Eqn
  q41 c4 = eqn (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ []) (lem-F1-rel-267-at01122330 c4)

-- tr rel-267 at 1: 19 steps
lem-tr-rel-267-at-1 : Ws → ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-rel-267-at-1 c4 = derive (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  (rw 1 (q4 c4) ∷
   rw 2 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw 10 (q3 c4) ∷
   rw 11 (q3 c4) ∷
   rw 13 (q4 c4) ∷
   rw 14 (q4 c4) ∷
   rw 18 (q4 c4) ∷
   rw 19 (q4 c4) ∷
   rw 0 (q41 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q7 c4) ∷
   rw 8 (q6 c4) ∷
   rw 9 (q6 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q7 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = eqn (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (lem-F1-rel-268 c4)

-- tr rel-268 at 0: 1 steps
lem-tr-rel-268-at-0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
lem-tr-rel-268-at-0 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ [])
  (rw 0 (q42 c4) ∷ []) Eq.refl

-- F1 rel-268 @2332: 31 steps
lem-F1-rel-268-at2332 : Ws → ⟪ (Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268-at2332 c4 = derive (Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q14 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q12 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q11 c4) ∷
   rw⁻ 13 (q13 c4) ∷
   rw 14 (q12 c4) ∷
   rw 1 (q42 c4) ∷
   rw 0 (q17 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   rw 2 (q16 c4) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 5 (q12 c4) ∷
   rw 6 (q17 c4) ∷
   rw 7 (q17 c4) ∷
   rw 8 (q17 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 10 (q16 c4) ∷
   rw 11 (q16 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw 13 (q12 c4) ∷
   rw 14 (q9 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = eqn (Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ []) (lem-F1-rel-268-at2332 c4)

-- F1 rel-268 @122331: 31 steps
lem-F1-rel-268-at122331 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268-at122331 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q23 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 5 (q22 c4) ∷
   rw 6 (q21 c4) ∷
   rw 7 (q23 c4) ∷
   rw 8 (q23 c4) ∷
   rw 9 (q23 c4) ∷
   rw⁻ 10 (q22 c4) ∷
   rw 11 (q20 c4) ∷
   rw 12 (q20 c4) ∷
   rw⁻ 13 (q22 c4) ∷
   rw 14 (q21 c4) ∷
   rw 1 (q43 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 2 (q26 c4) ∷
   rw 3 (q26 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   rw 5 (q21 c4) ∷
   rw 6 (q28 c4) ∷
   rw 7 (q28 c4) ∷
   rw 8 (q28 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 10 (q26 c4) ∷
   rw 11 (q26 c4) ∷
   rw⁻ 12 (q27 c4) ∷
   rw 13 (q21 c4) ∷
   rw 14 (q18 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (lem-F1-rel-268-at122331 c4)

-- F1 rel-268 @01122330: 31 steps
lem-F1-rel-268-at01122330 : Ws → ⟪ (Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268-at01122330 c4 = derive (Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q32 c4) ∷
   rw 3 (q30 c4) ∷
   rw 4 (q30 c4) ∷
   rw 5 (q32 c4) ∷
   rw 6 (q31 c4) ∷
   rw 7 (q2 c4) ∷
   rw 8 (q2 c4) ∷
   rw 9 (q2 c4) ∷
   rw 10 (q32 c4) ∷
   rw 11 (q30 c4) ∷
   rw 12 (q30 c4) ∷
   rw 13 (q32 c4) ∷
   rw 14 (q31 c4) ∷
   rw 1 (q44 c4) ∷
   rw 0 (q36 c4) ∷
   rw 1 (q32 c4) ∷
   rw 2 (q35 c4) ∷
   rw 3 (q35 c4) ∷
   rw 4 (q32 c4) ∷
   rw 5 (q31 c4) ∷
   rw 6 (q36 c4) ∷
   rw 7 (q36 c4) ∷
   rw 8 (q36 c4) ∷
   rw 9 (q32 c4) ∷
   rw 10 (q35 c4) ∷
   rw 11 (q35 c4) ∷
   rw 12 (q32 c4) ∷
   rw 13 (q31 c4) ∷
   rw 14 (q1 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = eqn (Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ []) (lem-F1-rel-268-at01122330 c4)

-- tr rel-268 at 1: 17 steps
lem-tr-rel-268-at-1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-tr-rel-268-at-1 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ [])
  (rw 0 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 3 (q4 c4) ∷
   rw 6 (q3 c4) ∷
   rw 7 (q3 c4) ∷
   rw 8 (q3 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw 0 (q45 c4) ∷
   rw 0 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 3 (q7 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q6 c4) ∷
   rw 8 (q6 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q7 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = eqn (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (lem-F1-rel-269 c4)

-- tr rel-269 at 0: 1 steps
lem-tr-rel-269-at-0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-rel-269-at-0 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q46 c4) ∷ []) Eq.refl

-- F1 rel-269 @2332: 17 steps
lem-F1-rel-269-at2332 : Ws → ⟪ (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-rel-269-at2332 c4 = derive (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q14 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 7 (q11 c4) ∷
   rw 1 (q46 c4) ∷
   rw 0 (q17 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   rw 2 (q17 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 4 (q16 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q16 c4) ∷
   rw 7 (q9 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = eqn (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) (lem-F1-rel-269-at2332 c4)

-- F1 rel-269 @122331: 17 steps
lem-F1-rel-269-at122331 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-rel-269-at122331 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q23 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 3 (q23 c4) ∷
   rw⁻ 4 (q22 c4) ∷
   rw 5 (q20 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw 7 (q20 c4) ∷
   rw 1 (q47 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 2 (q28 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   rw 6 (q26 c4) ∷
   rw 7 (q18 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (lem-F1-rel-269-at122331 c4)

-- F1 rel-269 @01122330: 17 steps
lem-F1-rel-269-at01122330 : Ws → ⟪ (Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ
lem-F1-rel-269-at01122330 c4 = derive (Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q32 c4) ∷
   rw 3 (q2 c4) ∷
   rw 4 (q32 c4) ∷
   rw 5 (q30 c4) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q30 c4) ∷
   rw 1 (q48 c4) ∷
   rw 0 (q36 c4) ∷
   rw 1 (q32 c4) ∷
   rw 2 (q36 c4) ∷
   rw 3 (q32 c4) ∷
   rw 4 (q35 c4) ∷
   rw 5 (q32 c4) ∷
   rw 6 (q35 c4) ∷
   rw 7 (q1 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = eqn (Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ []) (lem-F1-rel-269-at01122330 c4)

-- tr rel-269 at 1: 9 steps
lem-tr-rel-269-at-1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-rel-269-at-1 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ [])
  (rw 0 (q3 c4) ∷
   rw 2 (q3 c4) ∷
   rw 4 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 0 (q49 c4) ∷
   rw 0 (q6 c4) ∷
   rw 2 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 6 (q7 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = eqn (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (lem-F1-rel-272 c4)

-- tr rel-272 at 0: 1 steps
lem-tr-rel-272-at-0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-tr-rel-272-at-0 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  (rw 0 (q50 c4) ∷ []) Eq.refl

-- F1 rel-272 @2332: 21 steps
lem-F1-rel-272-at2332 : Ws → ⟪ (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ
lem-F1-rel-272-at2332 c4 = derive (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q14 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 7 (q11 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 9 (q14 c4) ∷
   rw 1 (q50 c4) ∷
   rw 0 (q17 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   rw 2 (q17 c4) ∷
   rw 3 (q17 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 8 (q17 c4) ∷
   rw 9 (q9 c4) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = eqn (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ []) (lem-F1-rel-272-at2332 c4)

-- F1 rel-272 @122331: 21 steps
lem-F1-rel-272-at122331 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ
lem-F1-rel-272-at122331 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q23 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 3 (q23 c4) ∷
   rw 4 (q23 c4) ∷
   rw 5 (q23 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw 7 (q20 c4) ∷
   rw⁻ 8 (q22 c4) ∷
   rw 9 (q23 c4) ∷
   rw 1 (q51 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 2 (q28 c4) ∷
   rw 3 (q28 c4) ∷
   rw 4 (q28 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 8 (q28 c4) ∷
   rw 9 (q18 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ []) (lem-F1-rel-272-at122331 c4)

-- F1 rel-272 @01122330: 21 steps
lem-F1-rel-272-at01122330 : Ws → ⟪ (Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ
lem-F1-rel-272-at01122330 c4 = derive (Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q32 c4) ∷
   rw 3 (q2 c4) ∷
   rw 4 (q2 c4) ∷
   rw 5 (q2 c4) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q32 c4) ∷
   rw 9 (q2 c4) ∷
   rw 1 (q52 c4) ∷
   rw 0 (q36 c4) ∷
   rw 1 (q32 c4) ∷
   rw 2 (q36 c4) ∷
   rw 3 (q36 c4) ∷
   rw 4 (q36 c4) ∷
   rw 5 (q32 c4) ∷
   rw 6 (q35 c4) ∷
   rw 7 (q32 c4) ∷
   rw 8 (q36 c4) ∷
   rw 9 (q1 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = eqn (Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ []) (lem-F1-rel-272-at01122330 c4)

-- tr rel-272 at 1: 13 steps
lem-tr-rel-272-at-1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-rel-272-at-1 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q3 c4) ∷
   rw 2 (q3 c4) ∷
   rw 3 (q3 c4) ∷
   rw 4 (q3 c4) ∷
   rw 6 (q4 c4) ∷
   rw 8 (q3 c4) ∷
   rw 0 (q53 c4) ∷
   rw 0 (q6 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 8 (q6 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = eqn (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (lem-F1-cx-ccz c4)

-- tr cx-ccz at 0: 1 steps
lem-tr-cx-ccz-at-0 : Ws → ⟪ (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-tr-cx-ccz-at-0 c4 = derive (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  (rw 0 (q54 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = eqn (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (lem-F1-toff-ccz c4)

-- tr toff-ccz at 0: 1 steps
lem-tr-toff-ccz-at-0 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-tr-toff-ccz-at-0 c4 = derive (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  (rw 0 (q55 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = eqn (CS04 ∷ CS24 ∷ []) (CS24 ∷ CS04 ∷ []) (wp0476 c4)

-- tr comm1 S S1 at 0: 1 steps
lem-tr-comm1-S-S1-at-0 : Ws → ⟪ (CS24 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm1-S-S1-at-0 c4 = derive (CS24 ∷ CS04 ∷ []) (CS04 ∷ CS24 ∷ [])
  (rw⁻ 0 (q56 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (CK42 ∷ CS04 ∷ []) (CS04 ∷ CK42 ∷ []) (wp0477 c4)

-- tr comm1 S K1 at 0: 1 steps
lem-tr-comm1-S-K1-at-0 : Ws → ⟪ (CK42 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm1-S-K1-at-0 c4 = derive (CK42 ∷ CS04 ∷ []) (CS04 ∷ CK42 ∷ [])
  (rw 0 (q57 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = eqn (CS04 ∷ CS34 ∷ []) (CS34 ∷ CS04 ∷ []) (wp0478 c4)

-- tr comm1 S S2 at 0: 1 steps
lem-tr-comm1-S-S2-at-0 : Ws → ⟪ (CS34 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-S-S2-at-0 c4 = derive (CS34 ∷ CS04 ∷ []) (CS04 ∷ CS34 ∷ [])
  (rw⁻ 0 (q58 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = eqn (CK43 ∷ CS04 ∷ []) (CS04 ∷ CK43 ∷ []) (wp0479 c4)

-- tr comm1 S K2 at 0: 1 steps
lem-tr-comm1-S-K2-at-0 : Ws → ⟪ (CK43 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-S-K2-at-0 c4 = derive (CK43 ∷ CS04 ∷ []) (CS04 ∷ CK43 ∷ [])
  (rw 0 (q59 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (CS04 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS04 ∷ []) (lem-F2-S0∣CS12 c4)

-- tr comm1 S CS01 at 0: 1 steps
lem-tr-comm1-S-CS01-at-0 : Ws → ⟪ (Sb0-1-42-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-comm1-S-CS01-at-0 c4 = derive (Sb0-1-42-3 ∷ CS04 ∷ []) (CS04 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q60 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = eqn (CS04 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS04 ∷ []) (lem-F2-S0∣CS23 c4)

-- tr comm1 S CS12 at 0: 1 steps
lem-tr-comm1-S-CS12-at-0 : Ws → ⟪ (Sb0-2-43-1 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm1-S-CS12-at-0 c4 = derive (Sb0-2-43-1 ∷ CS04 ∷ []) (CS04 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q61 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = eqn (CK40 ∷ CS24 ∷ []) (CS24 ∷ CK40 ∷ []) (wp0483 c4)

-- tr comm1 K S1 at 0: 1 steps
lem-tr-comm1-K-S1-at-0 : Ws → ⟪ (CS24 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm1-K-S1-at-0 c4 = derive (CS24 ∷ CK40 ∷ []) (CK40 ∷ CS24 ∷ [])
  (rw⁻ 0 (q62 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (CK40 ∷ CK42 ∷ []) (CK42 ∷ CK40 ∷ []) (wp0484 c4)

-- tr comm1 K K1 at 0: 1 steps
lem-tr-comm1-K-K1-at-0 : Ws → ⟪ (CK42 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm1-K-K1-at-0 c4 = derive (CK42 ∷ CK40 ∷ []) (CK40 ∷ CK42 ∷ [])
  (rw⁻ 0 (q63 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = eqn (CK40 ∷ CS34 ∷ []) (CS34 ∷ CK40 ∷ []) (wp0485 c4)

-- tr comm1 K S2 at 0: 1 steps
lem-tr-comm1-K-S2-at-0 : Ws → ⟪ (CS34 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-K-S2-at-0 c4 = derive (CS34 ∷ CK40 ∷ []) (CK40 ∷ CS34 ∷ [])
  (rw⁻ 0 (q64 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (CK40 ∷ CK43 ∷ []) (CK43 ∷ CK40 ∷ []) (wp0486 c4)

-- tr comm1 K K2 at 0: 1 steps
lem-tr-comm1-K-K2-at-0 : Ws → ⟪ (CK43 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-K-K2-at-0 c4 = derive (CK43 ∷ CK40 ∷ []) (CK40 ∷ CK43 ∷ [])
  (rw⁻ 0 (q65 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = eqn (CK40 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK40 ∷ []) (lem-F2-K0∣CS12 c4)

-- tr comm1 K CS01 at 0: 1 steps
lem-tr-comm1-K-CS01-at-0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-comm1-K-CS01-at-0 c4 = derive (Sb0-1-42-3 ∷ CK40 ∷ []) (CK40 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = eqn (CK40 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK40 ∷ []) (lem-F2-K0∣CS23 c4)

-- tr comm1 K CS12 at 0: 1 steps
lem-tr-comm1-K-CS12-at-0 : Ws → ⟪ (Sb0-2-43-1 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm1-K-CS12-at-0 c4 = derive (Sb0-2-43-1 ∷ CK40 ∷ []) (CK40 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q67 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (CS14 ∷ CS24 ∷ []) (CS24 ∷ CS14 ∷ []) (wl0328 (lit c4))

-- tr comm1 S S0 at 1: 1 steps
lem-tr-comm1-S-S0-at-1 : Ws → ⟪ (CS24 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm1-S-S0-at-1 c4 = derive (CS24 ∷ CS14 ∷ []) (CS14 ∷ CS24 ∷ [])
  (rw⁻ 0 (q68 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (CK42 ∷ CS14 ∷ []) (CS14 ∷ CK42 ∷ []) (wl0911 (lit c4))

-- tr comm1 S K0 at 1: 1 steps
lem-tr-comm1-S-K0-at-1 : Ws → ⟪ (CK42 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm1-S-K0-at-1 c4 = derive (CK42 ∷ CS14 ∷ []) (CS14 ∷ CK42 ∷ [])
  (rw 0 (q69 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = eqn (CS14 ∷ CS34 ∷ []) (CS34 ∷ CS14 ∷ []) (wl0495 (lit c4))

-- tr comm1 S S1 at 1: 1 steps
lem-tr-comm1-S-S1-at-1 : Ws → ⟪ (CS34 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-S-S1-at-1 c4 = derive (CS34 ∷ CS14 ∷ []) (CS14 ∷ CS34 ∷ [])
  (rw⁻ 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : Ws → Eqn
  q71 c4 = eqn (CK43 ∷ CS14 ∷ []) (CS14 ∷ CK43 ∷ []) (wl0912 (lit c4))

-- tr comm1 S K1 at 1: 1 steps
lem-tr-comm1-S-K1-at-1 : Ws → ⟪ (CK43 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-S-K1-at-1 c4 = derive (CK43 ∷ CS14 ∷ []) (CS14 ∷ CK43 ∷ [])
  (rw 0 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (CS14 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS14 ∷ []) (lem-F2-S1∣CS23 c4)

-- tr comm1 S CS01 at 1: 1 steps
lem-tr-comm1-S-CS01-at-1 : Ws → ⟪ (Sb0-2-43-1 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm1-S-CS01-at-1 c4 = derive (Sb0-2-43-1 ∷ CS14 ∷ []) (CS14 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (CK41 ∷ CS24 ∷ []) (CS24 ∷ CK41 ∷ []) (wl0914 (lit c4))

-- tr comm1 K S0 at 1: 1 steps
lem-tr-comm1-K-S0-at-1 : Ws → ⟪ (CS24 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm1-K-S0-at-1 c4 = derive (CS24 ∷ CK41 ∷ []) (CK41 ∷ CS24 ∷ [])
  (rw⁻ 0 (q73 c4) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = eqn (CK41 ∷ CK42 ∷ []) (CK42 ∷ CK41 ∷ []) (wl0915 (lit c4))

-- tr comm1 K K0 at 1: 1 steps
lem-tr-comm1-K-K0-at-1 : Ws → ⟪ (CK42 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm1-K-K0-at-1 c4 = derive (CK42 ∷ CK41 ∷ []) (CK41 ∷ CK42 ∷ [])
  (rw⁻ 0 (q74 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = eqn (CK41 ∷ CS34 ∷ []) (CS34 ∷ CK41 ∷ []) (wl0916 (lit c4))

-- tr comm1 K S1 at 1: 1 steps
lem-tr-comm1-K-S1-at-1 : Ws → ⟪ (CS34 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-K-S1-at-1 c4 = derive (CS34 ∷ CK41 ∷ []) (CK41 ∷ CS34 ∷ [])
  (rw⁻ 0 (q75 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = eqn (CK41 ∷ CK43 ∷ []) (CK43 ∷ CK41 ∷ []) (wl0917 (lit c4))

-- tr comm1 K K1 at 1: 1 steps
lem-tr-comm1-K-K1-at-1 : Ws → ⟪ (CK43 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-K-K1-at-1 c4 = derive (CK43 ∷ CK41 ∷ []) (CK41 ∷ CK43 ∷ [])
  (rw⁻ 0 (q76 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (CK41 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK41 ∷ []) (lem-F2-K1∣CS23 c4)

-- tr comm1 K CS01 at 1: 1 steps
lem-tr-comm1-K-CS01-at-1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm1-K-CS01-at-1 c4 = derive (Sb0-2-43-1 ∷ CK41 ∷ []) (CK41 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = eqn (CS24 ∷ S4 ∷ []) (S4 ∷ CS24 ∷ []) (wl0918 (lit c4))

-- tr comm1 S I at 2: 1 steps
lem-tr-comm1-S-I-at-2 : Ws → ⟪ (S4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-S-I-at-2 c4 = derive (S4 ∷ CS24 ∷ []) (CS24 ∷ S4 ∷ [])
  (rw⁻ 0 (q78 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = eqn (CS24 ∷ CS34 ∷ []) (CS34 ∷ CS24 ∷ []) (wl0919 (lit c4))

-- tr comm1 S S0 at 2: 1 steps
lem-tr-comm1-S-S0-at-2 : Ws → ⟪ (CS34 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-S-S0-at-2 c4 = derive (CS34 ∷ CS24 ∷ []) (CS24 ∷ CS34 ∷ [])
  (rw⁻ 0 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (CK43 ∷ CS24 ∷ []) (CS24 ∷ CK43 ∷ []) (wl0920 (lit c4))

-- tr comm1 S K0 at 2: 1 steps
lem-tr-comm1-S-K0-at-2 : Ws → ⟪ (CK43 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-S-K0-at-2 c4 = derive (CK43 ∷ CS24 ∷ []) (CS24 ∷ CK43 ∷ [])
  (rw 0 (q80 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (CK42 ∷ S4 ∷ []) (S4 ∷ CK42 ∷ []) (wl0921 (lit c4))

-- tr comm1 K I at 2: 1 steps
lem-tr-comm1-K-I-at-2 : Ws → ⟪ (S4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-K-I-at-2 c4 = derive (S4 ∷ CK42 ∷ []) (CK42 ∷ S4 ∷ [])
  (rw⁻ 0 (q81 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = eqn (CK42 ∷ CS34 ∷ []) (CS34 ∷ CK42 ∷ []) (wl0922 (lit c4))

-- tr comm1 K S0 at 2: 1 steps
lem-tr-comm1-K-S0-at-2 : Ws → ⟪ (CS34 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-K-S0-at-2 c4 = derive (CS34 ∷ CK42 ∷ []) (CK42 ∷ CS34 ∷ [])
  (rw⁻ 0 (q82 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = eqn (CK42 ∷ CK43 ∷ []) (CK43 ∷ CK42 ∷ []) (wl0923 (lit c4))

-- tr comm1 K K0 at 2: 1 steps
lem-tr-comm1-K-K0-at-2 : Ws → ⟪ (CK43 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-K-K0-at-2 c4 = derive (CK43 ∷ CK42 ∷ []) (CK42 ∷ CK43 ∷ [])
  (rw⁻ 0 (q83 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = eqn (CS34 ∷ S4 ∷ []) (S4 ∷ CS34 ∷ []) (wl0924 (lit c4))

-- tr comm1 S I at 3: 1 steps
lem-tr-comm1-S-I-at-3 : Ws → ⟪ (S4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-S-I-at-3 c4 = derive (S4 ∷ CS34 ∷ []) (CS34 ∷ S4 ∷ [])
  (rw⁻ 0 (q84 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (CK43 ∷ S4 ∷ []) (S4 ∷ CK43 ∷ []) (wl0925 (lit c4))

-- tr comm1 K I at 3: 1 steps
lem-tr-comm1-K-I-at-3 : Ws → ⟪ (S4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-K-I-at-3 c4 = derive (S4 ∷ CK43 ∷ []) (CK43 ∷ S4 ∷ [])
  (rw⁻ 0 (q85 c4) ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = eqn (CS24 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ []) (lem-F2-S2∣CS01 c4)

-- tr comm2 S0 at 0: 1 steps
lem-tr-comm2-S0-at-0 : Ws → ⟪ (CS24 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm2-S0-at-0 c4 = derive (CS24 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ [])
  (rw 0 (q86 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = eqn (CK42 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ []) (lem-F2-K2∣CS01 c4)

-- tr comm2 K0 at 0: 1 steps
lem-tr-comm2-K0-at-0 : Ws → ⟪ (CK42 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm2-K0-at-0 c4 = derive (CK42 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ [])
  (rw 0 (q87 c4) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = eqn (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-F2-S3∣CS01 c4)

-- tr comm2 S1 at 0: 1 steps
lem-tr-comm2-S1-at-0 : Ws → ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm2-S1-at-0 c4 = derive (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ [])
  (rw 0 (q88 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = eqn (CK43 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ []) (lem-F2-K3∣CS01 c4)

-- tr comm2 K1 at 0: 1 steps
lem-tr-comm2-K1-at-0 : Ws → ⟪ (CK43 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm2-K1-at-0 c4 = derive (CK43 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ [])
  (rw 0 (q89 c4) ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = eqn (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) (lem-F2-CS01∣CS23 c4)

-- tr comm2 CS01 at 0: 1 steps
lem-tr-comm2-CS01-at-0 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm2-CS01-at-0 c4 = derive (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q90 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = eqn (S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ S4 ∷ []) (lem-F2-iI∣CS12 c4)

-- tr comm2 I at 1: 1 steps
lem-tr-comm2-I-at-1 : Ws → ⟪ (S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm2-I-at-1 c4 = derive (S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ S4 ∷ [])
  (rw 0 (q91 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = eqn (CS34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ []) (lem-F2-S3∣CS12 c4)

-- tr comm2 S0 at 1: 1 steps
lem-tr-comm2-S0-at-1 : Ws → ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm2-S0-at-1 c4 = derive (CS34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ [])
  (rw 0 (q92 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = eqn (CK43 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ []) (lem-F2-K3∣CS12 c4)

-- tr comm2 K0 at 1: 1 steps
lem-tr-comm2-K0-at-1 : Ws → ⟪ (CK43 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm2-K0-at-1 c4 = derive (CK43 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ [])
  (rw 0 (q93 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = eqn (S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ S4 ∷ []) (lem-F2-iI∣CS23 c4)

-- tr comm2 I at 2: 1 steps
lem-tr-comm2-I-at-2 : Ws → ⟪ (S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm2-I-at-2 c4 = derive (S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ S4 ∷ [])
  (rw 0 (q94 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (wl0891 (lit c4))

-- calc F4 I I: 1 steps
lem-calc-F4-I-I : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-I c4 = derive (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q95 c4) ∷ []) Eq.refl

private
  q96 : Ws → Eqn
  q96 c4 = eqn (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (wp0462 c4)

-- calc F4 I S0: 1 steps
lem-calc-F4-I-S0 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-S0 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q96 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = eqn (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (wp0487 c4)

-- calc F4 I K0: 1 steps
lem-calc-F4-I-K0 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-K0 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q97 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = eqn (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl0889 (lit c4))

-- calc F4 I S1: 1 steps
lem-calc-F4-I-S1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-S1 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q98 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = eqn (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (wl0890 (lit c4))

-- calc F4 I K1: 1 steps
lem-calc-F4-I-K1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-K1 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q99 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (wl0894 (lit c4))

-- calc F4 I S2: 1 steps
lem-calc-F4-I-S2 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-S2 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q100 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (wl0926 (lit c4))

-- calc F4 I K2: 1 steps
lem-calc-F4-I-K2 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-K2 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q101 c4) ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = eqn (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (wl0927 (lit c4))

-- calc F4 I S3: 1 steps
lem-calc-F4-I-S3 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-S3 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q102 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = eqn (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (wl0928 (lit c4))

-- calc F4 I K3: 1 steps
lem-calc-F4-I-K3 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-K3 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q103 c4) ∷ []) Eq.refl

private
  q104 : Ws → Eqn
  q104 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS01ᵖ1 c4)

-- calc F4 I CS01: 1 steps
lem-calc-F4-I-CS01 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-CS01 c4 = derive (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw 0 (q104 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS12ᵖ1 c4)

-- calc F4 I CS12: 1 steps
lem-calc-F4-I-CS12 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-CS12 c4 = derive (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw 0 (q105 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS23ᵖ1 c4)

-- calc F4 I CS23: 1 steps
lem-calc-F4-I-CS23 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-CS23 c4 = derive (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw 0 (q106 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = eqn (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4)

-- calc F4 S0 I: 1 steps
lem-calc-F4-S0-I : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-I c4 = derive (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q107 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4)

-- calc F4 S0 S0: 1 steps
lem-calc-F4-S0-S0 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-S0 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q108 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = eqn (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) (wp0488 c4)

-- calc F4 S0 K0: 1 steps
lem-calc-F4-S0-K0 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-K0 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q109 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = eqn (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4)

-- calc F4 S0 S1: 1 steps
lem-calc-F4-S0-S1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-S1 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q110 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = eqn (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (wp0467 c4)

-- calc F4 S0 K1: 1 steps
lem-calc-F4-S0-K1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-K1 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q111 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) (wp0489 c4)

-- calc F4 S0 S2: 1 steps
lem-calc-F4-S0-S2 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-S2 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q112 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) (wp0490 c4)

-- calc F4 S0 K2: 1 steps
lem-calc-F4-S0-K2 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-K2 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q113 c4) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = eqn (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) (wp0491 c4)

-- calc F4 S0 S3: 1 steps
lem-calc-F4-S0-S3 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-S3 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q114 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = eqn (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) (wp0492 c4)

-- calc F4 S0 K3: 1 steps
lem-calc-F4-S0-K3 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-K3 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q115 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)

-- calc F4 S0 CS01: 1 steps
lem-calc-F4-S0-CS01 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-CS01 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw 0 (q116 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0ᵖ0∣CS12ᵖ1 c4)

-- calc F4 S0 CS12: 1 steps
lem-calc-F4-S0-CS12 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-CS12 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw 0 (q117 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0ᵖ0∣CS23ᵖ1 c4)

-- calc F4 S0 CS23: 1 steps
lem-calc-F4-S0-CS23 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-CS23 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw 0 (q118 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = eqn (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) (wp0493 c4)

-- calc F4 K0 I: 1 steps
lem-calc-F4-K0-I : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-I c4 = derive (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q119 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = eqn (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (wp0494 c4)

-- calc F4 K0 S0: 1 steps
lem-calc-F4-K0-S0 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-S0 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q120 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp0495 c4)

-- calc F4 K0 K0: 1 steps
lem-calc-F4-K0-K0 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-K0 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q121 c4) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = eqn (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) (wp0496 c4)

-- calc F4 K0 S1: 1 steps
lem-calc-F4-K0-S1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-S1 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q122 c4) ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = eqn (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) (wp0497 c4)

-- calc F4 K0 K1: 1 steps
lem-calc-F4-K0-K1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-K1 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q123 c4) ∷ []) Eq.refl

private
  q124 : Ws → Eqn
  q124 c4 = eqn (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) (wp0498 c4)

-- calc F4 K0 S2: 1 steps
lem-calc-F4-K0-S2 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-S2 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q124 c4) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = eqn (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) (wp0499 c4)

-- calc F4 K0 K2: 1 steps
lem-calc-F4-K0-K2 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-K2 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q125 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) (wp0500 c4)

-- calc F4 K0 S3: 1 steps
lem-calc-F4-K0-S3 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-S3 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q126 c4) ∷ []) Eq.refl

private
  q127 : Ws → Eqn
  q127 c4 = eqn (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) (wp0501 c4)

-- calc F4 K0 K3: 1 steps
lem-calc-F4-K0-K3 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-K3 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q127 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0ᵖ0∣CS01ᵖ1 c4)

-- calc F4 K0 CS01: 1 steps
lem-calc-F4-K0-CS01 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-CS01 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw 0 (q128 c4) ∷ []) Eq.refl

private
  q129 : Ws → Eqn
  q129 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0ᵖ0∣CS12ᵖ1 c4)

-- calc F4 K0 CS12: 1 steps
lem-calc-F4-K0-CS12 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-CS12 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw 0 (q129 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0ᵖ0∣CS23ᵖ1 c4)

-- calc F4 K0 CS23: 1 steps
lem-calc-F4-K0-CS23 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-CS23 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw 0 (q130 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = eqn (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (wl0929 (lit c4))

-- calc F4 S1 I: 1 steps
lem-calc-F4-S1-I : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-I c4 = derive (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q131 c4) ∷ []) Eq.refl
