{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D201 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0160 ; wl0163 ; wl0164 ; wl0165 ; wl0328 ; wl0495 ; wl0889 ; wl0890 ; wl0891 ; wl0894 ; wl0910 ; wl0911 ; wl0912 ; wl0913 ; wl0914 ; wl0915 ; wl0916 ; wl0917 ; wl0918 ; wl0919 ; wl0920 ; wl0921 ; wl0922 ; wl0923 ; wl0924 ; wl0925 ; wl0926 ; wl0927 ; wl0928 ; wl0929 ; wp0462 ; wp0463 ; wp0464 ; wp0466 ; wp0467 ; wp0473 ; wp0474 ; wp0475 ; wp0476 ; wp0477 ; wp0478 ; wp0479 ; wp0480 ; wp0481 ; wp0482 ; wp0483 ; wp0484 ; wp0485 ; wp0486 ; wp0487 ; wp0488 ; wp0489 ; wp0490 ; wp0491 ; wp0492 ; wp0493 ; wp0494 ; wp0495 ; wp0496 ; wp0497 ; wp0498 ; wp0499 ; wp0500 ; wp0501)
open import Examples.Groups.Clifford+CS.Five.Chain
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
-- F0 @02132130: 5 steps
lem-F0-at02132130 : Ws → ⟪ (Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F0-at02132130 c4 = run b0
  where
  b0 : Chain (Sb1-2-43-0 ∷ []) (Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 1 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- tr comm-CS-CS at 1: 5 steps
lem-tr-comm-CS-CS-at-1 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm-CS-CS-at-1 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 1 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 0 2 (Sb3-1-42-0 ∷ Sb1-2-43-0 ∷ []) (lem-F1-comm-CS-CS-at01122330 c4) ▸
       at 0 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 1 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done


-- tr rel-266 at 0: 1 steps
lem-tr-rel-266-at-0 : Ws → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-tr-rel-266-at-0 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ [])
  b0 = at 0 21 (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (lem-F1-rel-266 c4) ▸ done


-- F1 rel-266 @2332: 45 steps
lem-F1-rel-266-at2332 : Ws → ⟪ (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266-at2332 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 3 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 5 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 6 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 7 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸ done

  b1 : Chain (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sw23 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ [])
  b1 = at 8 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 9 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 10 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 11 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 12 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 13 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 14 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 15 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸ done

  b2 : Chain (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sw23 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sw23 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sw23 ∷ [])
  b2 = at 16 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 17 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 18 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 19 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 20 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 21 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 1 21 (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (lem-F1-rel-266 c4) ▸
       at 0 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0163 (lit c4))) ▸ done

  b3 : Chain (CK43 ∷ Sw23 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sw23 ∷ []) (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw23 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sw23 ∷ [])
  b3 = at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 3 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0163 (lit c4))) ▸
       at 4 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 5 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 6 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 7 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 8 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸ done

  b4 : Chain (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw23 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sw23 ∷ []) (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sw23 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sw23 ∷ [])
  b4 = at 9 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 10 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 11 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 12 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 13 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 14 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 15 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 16 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0163 (lit c4))) ▸ done

  b5 : Chain (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sw23 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sw23 ∷ []) (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ [])
  b5 = at 17 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 18 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 19 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0163 (lit c4))) ▸
       at 20 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 21 2 [] (wl0006 (lit c4)) ▸ done


-- F1 rel-266 @122331: 45 steps
lem-F1-rel-266-at122331 : Ws → ⟪ (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266-at122331 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 2 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 3 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 5 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 6 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 7 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸ done

  b1 : Chain (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sw12 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ [])
  b1 = at 8 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 9 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 10 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 11 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 12 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 13 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 14 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 15 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸ done

  b2 : Chain (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sw12 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sw12 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ Sw12 ∷ [])
  b2 = at 16 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 17 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 18 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 19 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 20 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 21 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 1 21 (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ []) (lem-F1-rel-266-at2332 c4) ▸
       at 0 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸ done

  b3 : Chain (CK43 ∷ Sw12 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ Sw12 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sw12 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ Sw12 ∷ [])
  b3 = at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 3 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 4 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 5 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 6 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 7 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 8 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸ done

  b4 : Chain (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sw12 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ Sw12 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sw12 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ Sw12 ∷ [])
  b4 = at 9 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 10 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 11 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 12 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 13 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 14 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 15 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 16 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸ done

  b5 : Chain (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sw12 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ Sw12 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b5 = at 17 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 18 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 19 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 20 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 21 2 [] (wl0001 (lit c4)) ▸ done


-- F1 rel-266 @01122330: 45 steps
lem-F1-rel-266-at01122330 : Ws → ⟪ (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266-at01122330 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 2 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 3 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 5 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 6 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 7 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸ done

  b1 : Chain (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sw01 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ [])
  b1 = at 8 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 9 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 10 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 11 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 12 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 13 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 14 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 15 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸ done

  b2 : Chain (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sw01 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (CK43 ∷ Sw01 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sw01 ∷ [])
  b2 = at 16 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 17 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 18 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 19 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 20 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 21 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 1 21 (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (lem-F1-rel-266-at122331 c4) ▸
       at 0 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸ done

  b3 : Chain (CK43 ∷ Sw01 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sw01 ∷ []) (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sw01 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sw01 ∷ [])
  b3 = at 1 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 3 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 4 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 5 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 6 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 7 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 8 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸ done

  b4 : Chain (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sw01 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sw01 ∷ []) (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sw01 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sw01 ∷ [])
  b4 = at 9 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 10 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 11 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 12 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 13 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 14 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 15 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 16 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸ done

  b5 : Chain (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sw01 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sw01 ∷ []) (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ [])
  b5 = at 17 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 18 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 19 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 20 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 21 2 [] (wl0002 (lit c4)) ▸ done


-- tr rel-266 at 1: 19 steps
lem-tr-rel-266-at-1 : Ws → ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-tr-rel-266-at-1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 1 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 2 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 6 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 7 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 10 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 12 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 13 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 17 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸ done

  b1 : Chain (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ [])
  b1 = at 18 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 0 21 (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ []) (lem-F1-rel-266-at01122330 c4) ▸
       at 1 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 2 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 6 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 7 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 10 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 12 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done

  b2 : Chain (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b2 = at 13 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 17 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 18 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done


-- tr rel-267 at 0: 1 steps
lem-tr-rel-267-at-0 : Ws → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-rel-267-at-0 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 22 (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (lem-F1-rel-267 c4) ▸ done


-- F1 rel-267 @2332: 39 steps
lem-F1-rel-267-at2332 : Ws → ⟪ (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-rel-267-at2332 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 3 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 5 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 6 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 7 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸ done

  b1 : Chain (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw23 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ [])
  b1 = at 8 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 9 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 10 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 11 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 12 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 13 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 14 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 15 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸ done

  b2 : Chain (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw23 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (Sw23 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ [])
  b2 = at 16 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 17 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 18 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 19 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 20 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 21 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 22 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 1 22 (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (lem-F1-rel-267 c4) ▸ done

  b3 : Chain (Sw23 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ []) (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw23 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ [])
  b3 = at 0 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 1 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 3 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 4 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 5 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 6 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 7 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸ done

  b4 : Chain (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw23 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ []) (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ [])
  b4 = at 8 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 9 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 10 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 11 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 12 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 13 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 14 2 [] (wl0006 (lit c4)) ▸ done


-- F1 rel-267 @122331: 39 steps
lem-F1-rel-267-at122331 : Ws → ⟪ (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-rel-267-at122331 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 2 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 3 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 5 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 6 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 7 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸ done

  b1 : Chain (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sw12 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ [])
  b1 = at 8 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 9 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 10 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 11 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 12 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 13 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 14 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 15 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸ done

  b2 : Chain (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sw12 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (Sw12 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ [])
  b2 = at 16 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 17 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 18 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 19 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 20 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 21 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 22 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 1 22 (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) (lem-F1-rel-267-at2332 c4) ▸ done

  b3 : Chain (Sw12 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ []) (CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sw12 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ [])
  b3 = at 0 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 1 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 2 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 3 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 4 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 5 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 6 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 7 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸ done

  b4 : Chain (CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sw12 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ []) (CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  b4 = at 8 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 9 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 10 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 11 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 12 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 13 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 14 2 [] (wl0001 (lit c4)) ▸ done


-- F1 rel-267 @01122330: 39 steps
lem-F1-rel-267-at01122330 : Ws → ⟪ (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ
lem-F1-rel-267-at01122330 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 2 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 3 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 5 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 6 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 7 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸ done

  b1 : Chain (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sw01 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ [])
  b1 = at 8 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 9 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 10 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 11 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 12 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 13 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 14 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 15 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸ done

  b2 : Chain (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sw01 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (Sw01 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw01 ∷ [])
  b2 = at 16 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 17 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 18 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 19 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 20 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 21 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 22 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 1 22 (CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (lem-F1-rel-267-at122331 c4) ▸ done

  b3 : Chain (Sw01 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw01 ∷ []) (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sw01 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw01 ∷ [])
  b3 = at 0 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 1 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 2 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 3 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 4 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 5 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 6 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 7 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸ done

  b4 : Chain (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sw01 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw01 ∷ []) (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ [])
  b4 = at 8 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 9 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 10 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 11 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 12 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 13 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 14 2 [] (wl0002 (lit c4)) ▸ done


-- tr rel-267 at 1: 19 steps
lem-tr-rel-267-at-1 : Ws → ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-rel-267-at-1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 1 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 2 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 6 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 7 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 10 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 11 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 13 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 14 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸ done

  b1 : Chain (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ [])
  b1 = at 18 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 19 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 0 22 (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ []) (lem-F1-rel-267-at01122330 c4) ▸
       at 1 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 2 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 5 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 6 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 8 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸ done

  b2 : Chain (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  b2 = at 9 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 12 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 13 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done


-- tr rel-268 at 0: 1 steps
lem-tr-rel-268-at-0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
lem-tr-rel-268-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 0 14 (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (lem-F1-rel-268 c4) ▸ done


-- F1 rel-268 @2332: 31 steps
lem-F1-rel-268-at2332 : Ws → ⟪ (Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268-at2332 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ []) (Sw23 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 3 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 4 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 5 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 6 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 7 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸ done

  b1 : Chain (Sw23 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ []) (Sw23 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sw23 ∷ [])
  b1 = at 8 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 9 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 10 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 11 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 12 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 13 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 14 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 1 14 (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (lem-F1-rel-268 c4) ▸ done

  b2 : Chain (Sw23 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sw23 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sw23 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sw23 ∷ [])
  b2 = at 0 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 3 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 4 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 5 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 6 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 7 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸ done

  b3 : Chain (Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sw23 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sw23 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ [])
  b3 = at 8 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 9 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 10 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 11 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 12 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 13 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 14 2 [] (wl0006 (lit c4)) ▸ done


-- F1 rel-268 @122331: 31 steps
lem-F1-rel-268-at122331 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268-at122331 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ []) (Sw12 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 3 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 4 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 5 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 6 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 7 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸ done

  b1 : Chain (Sw12 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ []) (Sw12 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sw12 ∷ [])
  b1 = at 8 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 9 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 10 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 11 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 12 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 13 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 14 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 1 14 (Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ []) (lem-F1-rel-268-at2332 c4) ▸ done

  b2 : Chain (Sw12 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sw12 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sw12 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sw12 ∷ [])
  b2 = at 0 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 1 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 3 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 4 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 5 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 6 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 7 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸ done

  b3 : Chain (Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sw12 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sw12 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ [])
  b3 = at 8 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 9 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 10 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 11 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 12 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 13 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 14 2 [] (wl0001 (lit c4)) ▸ done


-- F1 rel-268 @01122330: 31 steps
lem-F1-rel-268-at01122330 : Ws → ⟪ (Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268-at01122330 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ []) (Sw01 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sw01 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 2 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 3 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 4 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 5 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 6 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 7 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sw01 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ []) (Sw01 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sw01 ∷ [])
  b1 = at 8 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 9 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 10 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 11 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 12 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 13 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 14 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 1 14 (Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (lem-F1-rel-268-at122331 c4) ▸ done

  b2 : Chain (Sw01 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sw01 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sw01 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sw01 ∷ [])
  b2 = at 0 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 1 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 3 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 4 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 5 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 6 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 7 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸ done

  b3 : Chain (Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sw01 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sw01 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ [])
  b3 = at 8 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 9 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 10 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 11 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 12 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 13 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 14 2 [] (wl0002 (lit c4)) ▸ done


-- tr rel-268 at 1: 17 steps
lem-tr-rel-268-at-1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-tr-rel-268-at-1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ [])
  b0 = at 0 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 2 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 3 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 6 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 7 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 8 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 10 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 11 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸ done

  b1 : Chain (Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ [])
  b1 = at 0 14 (Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ []) (lem-F1-rel-268-at01122330 c4) ▸
       at 0 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 2 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 3 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 6 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 7 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 8 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 10 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done

  b2 : Chain (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ [])
  b2 = at 11 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done


-- tr rel-269 at 0: 1 steps
lem-tr-rel-269-at-0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-rel-269-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 7 (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (lem-F1-rel-269 c4) ▸ done


-- F1 rel-269 @2332: 17 steps
lem-F1-rel-269-at2332 : Ws → ⟪ (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-rel-269-at2332 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ []) (Sw23 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 3 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 4 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 5 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 6 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 7 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸ done

  b1 : Chain (Sw23 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 1 7 (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (lem-F1-rel-269 c4) ▸
       at 0 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 2 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 3 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 4 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 5 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 6 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸ done

  b2 : Chain (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sw23 ∷ Sw23 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ [])
  b2 = at 7 2 [] (wl0006 (lit c4)) ▸ done


-- F1 rel-269 @122331: 17 steps
lem-F1-rel-269-at122331 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-rel-269-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ []) (Sw12 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 3 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 4 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 5 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 6 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 7 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸ done

  b1 : Chain (Sw12 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw12 ∷ [])
  b1 = at 1 7 (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) (lem-F1-rel-269-at2332 c4) ▸
       at 0 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 1 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 2 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 3 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 4 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 5 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 6 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸ done

  b2 : Chain (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw12 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ [])
  b2 = at 7 2 [] (wl0001 (lit c4)) ▸ done


-- F1 rel-269 @01122330: 17 steps
lem-F1-rel-269-at01122330 : Ws → ⟪ (Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ
lem-F1-rel-269-at01122330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ []) (Sw01 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 2 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 3 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 4 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 5 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 6 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 7 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 1 7 (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (lem-F1-rel-269-at122331 c4) ▸
       at 0 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 1 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 2 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 3 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 4 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 5 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 6 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸ done

  b2 : Chain (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sw01 ∷ Sw01 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ [])
  b2 = at 7 2 [] (wl0002 (lit c4)) ▸ done


-- tr rel-269 at 1: 9 steps
lem-tr-rel-269-at-1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-rel-269-at-1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb1-2-43-0 ∷ [])
  b0 = at 0 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 2 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 4 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 6 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 0 7 (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ []) (lem-F1-rel-269-at01122330 c4) ▸
       at 0 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 2 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 4 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done

  b1 : Chain (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb1-2-43-0 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ [])
  b1 = at 6 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done


-- tr rel-272 at 0: 1 steps
lem-tr-rel-272-at-0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-tr-rel-272-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 9 (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (lem-F1-rel-272 c4) ▸ done


-- F1 rel-272 @2332: 21 steps
lem-F1-rel-272-at2332 : Ws → ⟪ (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ
lem-F1-rel-272-at2332 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) (Sw23 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 3 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 4 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 5 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 6 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 7 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ (lit c4)) ▸ done

  b1 : Chain (Sw23 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sw23 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ [])
  b1 = at 8 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 9 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 9 (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (lem-F1-rel-272 c4) ▸
       at 0 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 2 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 3 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 4 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸ done

  b2 : Chain (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sw23 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ [])
  b2 = at 5 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 6 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 7 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 8 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 9 2 [] (wl0006 (lit c4)) ▸ done


-- F1 rel-272 @122331: 21 steps
lem-F1-rel-272-at122331 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ
lem-F1-rel-272-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (Sw12 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ CK42 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 3 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 4 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 5 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 6 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 7 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ (lit c4)) ▸ done

  b1 : Chain (Sw12 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sw12 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ [])
  b1 = at 8 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 9 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 9 (Sb3-0-41-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ []) (lem-F1-rel-272-at2332 c4) ▸
       at 0 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 1 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 2 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 3 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 4 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸ done

  b2 : Chain (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sw12 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ [])
  b2 = at 5 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 6 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 7 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 8 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 9 2 [] (wl0001 (lit c4)) ▸ done


-- F1 rel-272 @01122330: 21 steps
lem-F1-rel-272-at01122330 : Ws → ⟪ (Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ
lem-F1-rel-272-at01122330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb1-2-43-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ []) (Sw01 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ CK42 ∷ Sb1-2-43-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 2 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 3 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 4 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 5 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 6 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 7 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ (lit c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ CK42 ∷ Sb1-2-43-0 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sw01 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ [])
  b1 = at 8 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 9 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 1 9 (Sb3-0-42-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ []) (lem-F1-rel-272-at122331 c4) ▸
       at 0 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 1 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 2 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 3 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 4 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸ done

  b2 : Chain (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sw01 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ [])
  b2 = at 5 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 6 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 7 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 8 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 9 2 [] (wl0002 (lit c4)) ▸ done


-- tr rel-272 at 1: 13 steps
lem-tr-rel-272-at-1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-rel-272-at-1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ [])
  b0 = at 0 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 2 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 3 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 4 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 6 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 8 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 0 9 (Sb3-1-42-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ []) (lem-F1-rel-272-at01122330 c4) ▸
       at 0 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸ done

  b1 : Chain (Sb0-1-42-3 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ [])
  b1 = at 2 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 3 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 4 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 6 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 8 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸ done


-- tr cx-ccz at 0: 1 steps
lem-tr-cx-ccz-at-0 : Ws → ⟪ (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-tr-cx-ccz-at-0 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b0 = at 0 55 (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (lem-F1-cx-ccz c4) ▸ done


-- tr toff-ccz at 0: 1 steps
lem-tr-toff-ccz-at-0 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-tr-toff-ccz-at-0 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b0 = at 0 171 (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (lem-F1-toff-ccz c4) ▸ done


-- tr comm1 S S1 at 0: 1 steps
lem-tr-comm1-S-S1-at-0 : Ws → ⟪ (CS24 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm1-S-S1-at-0 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CS04 ∷ []) (CS04 ∷ CS24 ∷ [])
  b0 = at 0 2 (CS04 ∷ CS24 ∷ []) (sym (wp0476 c4)) ▸ done


-- tr comm1 S K1 at 0: 1 steps
lem-tr-comm1-S-K1-at-0 : Ws → ⟪ (CK42 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm1-S-K1-at-0 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CS04 ∷ []) (CS04 ∷ CK42 ∷ [])
  b0 = at 0 2 (CS04 ∷ CK42 ∷ []) (wp0477 c4) ▸ done


-- tr comm1 S S2 at 0: 1 steps
lem-tr-comm1-S-S2-at-0 : Ws → ⟪ (CS34 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-S-S2-at-0 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CS04 ∷ []) (CS04 ∷ CS34 ∷ [])
  b0 = at 0 2 (CS04 ∷ CS34 ∷ []) (sym (wp0478 c4)) ▸ done


-- tr comm1 S K2 at 0: 1 steps
lem-tr-comm1-S-K2-at-0 : Ws → ⟪ (CK43 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-S-K2-at-0 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CS04 ∷ []) (CS04 ∷ CK43 ∷ [])
  b0 = at 0 2 (CS04 ∷ CK43 ∷ []) (wp0479 c4) ▸ done


-- tr comm1 S CS01 at 0: 1 steps
lem-tr-comm1-S-CS01-at-0 : Ws → ⟪ (Sb0-1-42-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-comm1-S-CS01-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CS04 ∷ []) (CS04 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 2 (CS04 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F2-S0∣CS12 c4)) ▸ done


-- tr comm1 S CS12 at 0: 1 steps
lem-tr-comm1-S-CS12-at-0 : Ws → ⟪ (Sb0-2-43-1 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm1-S-CS12-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CS04 ∷ []) (CS04 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 2 (CS04 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F2-S0∣CS23 c4)) ▸ done


-- tr comm1 K S1 at 0: 1 steps
lem-tr-comm1-K-S1-at-0 : Ws → ⟪ (CS24 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm1-K-S1-at-0 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK40 ∷ []) (CK40 ∷ CS24 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS24 ∷ []) (sym (wp0483 c4)) ▸ done


-- tr comm1 K K1 at 0: 1 steps
lem-tr-comm1-K-K1-at-0 : Ws → ⟪ (CK42 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm1-K-K1-at-0 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CK40 ∷ []) (CK40 ∷ CK42 ∷ [])
  b0 = at 0 2 (CK40 ∷ CK42 ∷ []) (sym (wp0484 c4)) ▸ done


-- tr comm1 K S2 at 0: 1 steps
lem-tr-comm1-K-S2-at-0 : Ws → ⟪ (CS34 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-K-S2-at-0 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK40 ∷ []) (CK40 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS34 ∷ []) (sym (wp0485 c4)) ▸ done


-- tr comm1 K K2 at 0: 1 steps
lem-tr-comm1-K-K2-at-0 : Ws → ⟪ (CK43 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-K-K2-at-0 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CK40 ∷ []) (CK40 ∷ CK43 ∷ [])
  b0 = at 0 2 (CK40 ∷ CK43 ∷ []) (sym (wp0486 c4)) ▸ done


-- tr comm1 K CS01 at 0: 1 steps
lem-tr-comm1-K-CS01-at-0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-comm1-K-CS01-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK40 ∷ []) (CK40 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 2 (CK40 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F2-K0∣CS12 c4)) ▸ done


-- tr comm1 K CS12 at 0: 1 steps
lem-tr-comm1-K-CS12-at-0 : Ws → ⟪ (Sb0-2-43-1 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm1-K-CS12-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK40 ∷ []) (CK40 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 2 (CK40 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F2-K0∣CS23 c4)) ▸ done


-- tr comm1 S S0 at 1: 1 steps
lem-tr-comm1-S-S0-at-1 : Ws → ⟪ (CS24 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm1-S-S0-at-1 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CS14 ∷ []) (CS14 ∷ CS24 ∷ [])
  b0 = at 0 2 (CS14 ∷ CS24 ∷ []) (sym (wl0328 (lit c4))) ▸ done


-- tr comm1 S K0 at 1: 1 steps
lem-tr-comm1-S-K0-at-1 : Ws → ⟪ (CK42 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm1-S-K0-at-1 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CS14 ∷ []) (CS14 ∷ CK42 ∷ [])
  b0 = at 0 2 (CS14 ∷ CK42 ∷ []) (wl0911 (lit c4)) ▸ done


-- tr comm1 S S1 at 1: 1 steps
lem-tr-comm1-S-S1-at-1 : Ws → ⟪ (CS34 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-S-S1-at-1 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CS14 ∷ []) (CS14 ∷ CS34 ∷ [])
  b0 = at 0 2 (CS14 ∷ CS34 ∷ []) (sym (wl0495 (lit c4))) ▸ done


-- tr comm1 S K1 at 1: 1 steps
lem-tr-comm1-S-K1-at-1 : Ws → ⟪ (CK43 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-S-K1-at-1 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CS14 ∷ []) (CS14 ∷ CK43 ∷ [])
  b0 = at 0 2 (CS14 ∷ CK43 ∷ []) (wl0912 (lit c4)) ▸ done


-- tr comm1 S CS01 at 1: 1 steps
lem-tr-comm1-S-CS01-at-1 : Ws → ⟪ (Sb0-2-43-1 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm1-S-CS01-at-1 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CS14 ∷ []) (CS14 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 2 (CS14 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F2-S1∣CS23 c4)) ▸ done


-- tr comm1 K S0 at 1: 1 steps
lem-tr-comm1-K-S0-at-1 : Ws → ⟪ (CS24 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm1-K-S0-at-1 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK41 ∷ []) (CK41 ∷ CS24 ∷ [])
  b0 = at 0 2 (CK41 ∷ CS24 ∷ []) (sym (wl0914 (lit c4))) ▸ done


-- tr comm1 K K0 at 1: 1 steps
lem-tr-comm1-K-K0-at-1 : Ws → ⟪ (CK42 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm1-K-K0-at-1 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CK41 ∷ []) (CK41 ∷ CK42 ∷ [])
  b0 = at 0 2 (CK41 ∷ CK42 ∷ []) (sym (wl0915 (lit c4))) ▸ done


-- tr comm1 K S1 at 1: 1 steps
lem-tr-comm1-K-S1-at-1 : Ws → ⟪ (CS34 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-K-S1-at-1 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK41 ∷ []) (CK41 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK41 ∷ CS34 ∷ []) (sym (wl0916 (lit c4))) ▸ done


-- tr comm1 K K1 at 1: 1 steps
lem-tr-comm1-K-K1-at-1 : Ws → ⟪ (CK43 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-K-K1-at-1 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CK41 ∷ []) (CK41 ∷ CK43 ∷ [])
  b0 = at 0 2 (CK41 ∷ CK43 ∷ []) (sym (wl0917 (lit c4))) ▸ done


-- tr comm1 K CS01 at 1: 1 steps
lem-tr-comm1-K-CS01-at-1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm1-K-CS01-at-1 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK41 ∷ []) (CK41 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 2 (CK41 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F2-K1∣CS23 c4)) ▸ done


-- tr comm1 S I at 2: 1 steps
lem-tr-comm1-S-I-at-2 : Ws → ⟪ (S4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-S-I-at-2 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS24 ∷ []) (CS24 ∷ S4 ∷ [])
  b0 = at 0 2 (CS24 ∷ S4 ∷ []) (sym (wl0918 (lit c4))) ▸ done


-- tr comm1 S S0 at 2: 1 steps
lem-tr-comm1-S-S0-at-2 : Ws → ⟪ (CS34 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-S-S0-at-2 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CS24 ∷ []) (CS24 ∷ CS34 ∷ [])
  b0 = at 0 2 (CS24 ∷ CS34 ∷ []) (sym (wl0919 (lit c4))) ▸ done


-- tr comm1 S K0 at 2: 1 steps
lem-tr-comm1-S-K0-at-2 : Ws → ⟪ (CK43 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-S-K0-at-2 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CS24 ∷ []) (CS24 ∷ CK43 ∷ [])
  b0 = at 0 2 (CS24 ∷ CK43 ∷ []) (wl0920 (lit c4)) ▸ done


-- tr comm1 K I at 2: 1 steps
lem-tr-comm1-K-I-at-2 : Ws → ⟪ (S4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-K-I-at-2 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK42 ∷ []) (CK42 ∷ S4 ∷ [])
  b0 = at 0 2 (CK42 ∷ S4 ∷ []) (sym (wl0921 (lit c4))) ▸ done


-- tr comm1 K S0 at 2: 1 steps
lem-tr-comm1-K-S0-at-2 : Ws → ⟪ (CS34 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-K-S0-at-2 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK42 ∷ []) (CK42 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK42 ∷ CS34 ∷ []) (sym (wl0922 (lit c4))) ▸ done


-- tr comm1 K K0 at 2: 1 steps
lem-tr-comm1-K-K0-at-2 : Ws → ⟪ (CK43 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-K-K0-at-2 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CK42 ∷ []) (CK42 ∷ CK43 ∷ [])
  b0 = at 0 2 (CK42 ∷ CK43 ∷ []) (sym (wl0923 (lit c4))) ▸ done


-- tr comm1 S I at 3: 1 steps
lem-tr-comm1-S-I-at-3 : Ws → ⟪ (S4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-S-I-at-3 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS34 ∷ []) (CS34 ∷ S4 ∷ [])
  b0 = at 0 2 (CS34 ∷ S4 ∷ []) (sym (wl0924 (lit c4))) ▸ done


-- tr comm1 K I at 3: 1 steps
lem-tr-comm1-K-I-at-3 : Ws → ⟪ (S4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-K-I-at-3 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK43 ∷ []) (CK43 ∷ S4 ∷ [])
  b0 = at 0 2 (CK43 ∷ S4 ∷ []) (sym (wl0925 (lit c4))) ▸ done


-- tr comm2 S0 at 0: 1 steps
lem-tr-comm2-S0-at-0 : Ws → ⟪ (CS24 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm2-S0-at-0 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CS24 ∷ []) (lem-F2-S2∣CS01 c4) ▸ done


-- tr comm2 K0 at 0: 1 steps
lem-tr-comm2-K0-at-0 : Ws → ⟪ (CK42 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm2-K0-at-0 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CK42 ∷ []) (lem-F2-K2∣CS01 c4) ▸ done


-- tr comm2 S1 at 0: 1 steps
lem-tr-comm2-S1-at-0 : Ws → ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm2-S1-at-0 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-F2-S3∣CS01 c4) ▸ done


-- tr comm2 K1 at 0: 1 steps
lem-tr-comm2-K1-at-0 : Ws → ⟪ (CK43 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm2-K1-at-0 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CK43 ∷ []) (lem-F2-K3∣CS01 c4) ▸ done


-- tr comm2 CS01 at 0: 1 steps
lem-tr-comm2-CS01-at-0 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm2-CS01-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F2-CS01∣CS23 c4)) ▸ done


-- tr comm2 I at 1: 1 steps
lem-tr-comm2-I-at-1 : Ws → ⟪ (S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm2-I-at-1 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ S4 ∷ []) (lem-F2-iI∣CS12 c4) ▸ done


-- tr comm2 S0 at 1: 1 steps
lem-tr-comm2-S0-at-1 : Ws → ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm2-S0-at-1 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ CS34 ∷ []) (lem-F2-S3∣CS12 c4) ▸ done


-- tr comm2 K0 at 1: 1 steps
lem-tr-comm2-K0-at-1 : Ws → ⟪ (CK43 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm2-K0-at-1 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ CK43 ∷ []) (lem-F2-K3∣CS12 c4) ▸ done


-- tr comm2 I at 2: 1 steps
lem-tr-comm2-I-at-2 : Ws → ⟪ (S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm2-I-at-2 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb0-2-43-1 ∷ S4 ∷ []) (lem-F2-iI∣CS23 c4) ▸ done


-- calc F4 I I: 1 steps
lem-calc-F4-I-I : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-I c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0891 (lit c4))) ▸ done


-- calc F4 I S0: 1 steps
lem-calc-F4-I-S0 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0462 c4)) ▸ done


-- calc F4 I K0: 1 steps
lem-calc-F4-I-K0 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0487 c4)) ▸ done


-- calc F4 I S1: 1 steps
lem-calc-F4-I-S1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0889 (lit c4))) ▸ done


-- calc F4 I K1: 1 steps
lem-calc-F4-I-K1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0890 (lit c4))) ▸ done


-- calc F4 I S2: 1 steps
lem-calc-F4-I-S2 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0894 (lit c4))) ▸ done


-- calc F4 I K2: 1 steps
lem-calc-F4-I-K2 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0926 (lit c4))) ▸ done


-- calc F4 I S3: 1 steps
lem-calc-F4-I-S3 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0927 (lit c4))) ▸ done


-- calc F4 I K3: 1 steps
lem-calc-F4-I-K3 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0928 (lit c4))) ▸ done


-- calc F4 I CS01: 1 steps
lem-calc-F4-I-CS01 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 I CS12: 1 steps
lem-calc-F4-I-CS12 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 I CS23: 1 steps
lem-calc-F4-I-CS23 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 S0 I: 1 steps
lem-calc-F4-S0-I : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0463 c4)) ▸ done


-- calc F4 S0 S0: 1 steps
lem-calc-F4-S0-S0 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0464 c4)) ▸ done


-- calc F4 S0 K0: 1 steps
lem-calc-F4-S0-K0 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0488 c4)) ▸ done


-- calc F4 S0 S1: 1 steps
lem-calc-F4-S0-S1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0466 c4)) ▸ done


-- calc F4 S0 K1: 1 steps
lem-calc-F4-S0-K1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0467 c4)) ▸ done


-- calc F4 S0 S2: 1 steps
lem-calc-F4-S0-S2 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0489 c4)) ▸ done


-- calc F4 S0 K2: 1 steps
lem-calc-F4-S0-K2 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0490 c4)) ▸ done


-- calc F4 S0 S3: 1 steps
lem-calc-F4-S0-S3 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0491 c4)) ▸ done


-- calc F4 S0 K3: 1 steps
lem-calc-F4-S0-K3 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0492 c4)) ▸ done


-- calc F4 S0 CS01: 1 steps
lem-calc-F4-S0-CS01 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 S0 CS12: 1 steps
lem-calc-F4-S0-CS12 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 S0 CS23: 1 steps
lem-calc-F4-S0-CS23 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S0-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 K0 I: 1 steps
lem-calc-F4-K0-I : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0493 c4)) ▸ done


-- calc F4 K0 S0: 1 steps
lem-calc-F4-K0-S0 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0494 c4)) ▸ done


-- calc F4 K0 K0: 1 steps
lem-calc-F4-K0-K0 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0495 c4)) ▸ done


-- calc F4 K0 S1: 1 steps
lem-calc-F4-K0-S1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0496 c4)) ▸ done


-- calc F4 K0 K1: 1 steps
lem-calc-F4-K0-K1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0497 c4)) ▸ done


-- calc F4 K0 S2: 1 steps
lem-calc-F4-K0-S2 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0498 c4)) ▸ done


-- calc F4 K0 K2: 1 steps
lem-calc-F4-K0-K2 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0499 c4)) ▸ done


-- calc F4 K0 S3: 1 steps
lem-calc-F4-K0-S3 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0500 c4)) ▸ done


-- calc F4 K0 K3: 1 steps
lem-calc-F4-K0-K3 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0501 c4)) ▸ done


-- calc F4 K0 CS01: 1 steps
lem-calc-F4-K0-CS01 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 K0 CS12: 1 steps
lem-calc-F4-K0-CS12 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 K0 CS23: 1 steps
lem-calc-F4-K0-CS23 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K0-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 S1 I: 1 steps
lem-calc-F4-S1-I : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0929 (lit c4))) ▸ done

