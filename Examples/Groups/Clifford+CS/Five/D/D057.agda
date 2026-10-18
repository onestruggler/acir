{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D057 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0003 ; wl0006 ; wl0013 ; wl0017 ; wl0018 ; wl0087 ; wl0090 ; wl1083 ; wl1409 ; wl1410 ; wl1411 ; wl1417 ; wp1267)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F5-23)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-F4-I-CS2 ; lem-F4-I-I ; lem-F4-I-K2 ; lem-F4-I-S2 ; lem-F4-I-S3)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F4-K2-I ; lem-F4-K2-K2 ; lem-F4-K2-S2 ; lem-F4-K2-S3 ; lem-F4-S3-CS2 ; lem-F4-S3-I ; lem-F4-S3-K2 ; lem-F4-S3-S2 ; lem-F4-S3-S3)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-F4-CS2-I ; lem-F4-K2-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-F4-CS2-K2 ; lem-F4-CS2-S2 ; lem-F4-CS2-S3)
open import Examples.Groups.Clifford+CS.Five.D.D013 using (lem-F4-CS2-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D044 using (lem-F4-CS2-CS2-at02132031 ; lem-F4-I-CS2-at02132031 ; lem-F4-I-S2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D045 using (lem-F5-23-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D052 using (lem-F4-CS2-K3-at02132031 ; lem-F4-I-K3-at02132031 ; lem-F4-K3-CS2-at02132031 ; lem-F4-K3-K3-at02132031 ; lem-F4-S2-CS2-at02132031 ; lem-F4-S2-I-at02132031 ; lem-F4-S2-K3-at02132031 ; lem-F4-S2-S2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D056 using (lem-deb-Q-hi-eps)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L)
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-11f6930f ; lem-TR2-bf3fb9f8)
-- deb-Q-hi-split-a: 55 steps
lem-deb-Q-hi-split-a : Ws → ⟪ (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-deb-Q-hi-split-a c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 4 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4)) ▸
       at 3 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 8 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 7 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 6 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 12 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4)) ▸
       at 11 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b1 = at 10 4 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-K2-K2 c4)) ▸
       at 9 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 16 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 15 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 14 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 13 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 12 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 20 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b2 = at 19 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 18 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 17 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 16 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 15 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 24 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸
       at 23 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 22 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ ι ∷ S3 ∷ [])
  b3 = at 21 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 20 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 19 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 18 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 28 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸
       at 27 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 26 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 25 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ S3 ∷ [])
  b4 = at 24 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 23 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 22 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 21 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-I-S3 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-I-S3 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-I-S3 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ S4 ∷ CS34 ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-I-K2 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-I-K2 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 36 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸
       at 35 4 (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-S3-I c4)) ▸
       at 34 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ S4 ∷ CS34 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ [])
  b6 = at 33 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 32 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 31 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 30 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 29 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 28 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 27 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸ done


-- deb-Q-hi-split-b: 45 steps
lem-deb-Q-hi-split-b : Ws → ⟪ (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ []) ⟫ʷ
lem-deb-Q-hi-split-b c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 4 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4)) ▸
       at 3 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 8 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 7 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 6 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 12 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4)) ▸
       at 11 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ S3 ∷ S3 ∷ ι ∷ [])
  b1 = at 10 4 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-K2-K2 c4)) ▸
       at 9 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 16 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 15 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 14 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 13 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 12 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 20 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ S3 ∷ S3 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ S3 ∷ ι ∷ [])
  b2 = at 19 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 18 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 17 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 16 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 15 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 24 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸
       at 23 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 22 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ S3 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ ι ∷ [])
  b3 = at 21 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 20 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 19 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 18 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 28 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸
       at 27 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 26 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 25 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ [])
  b4 = at 24 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 23 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 22 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 21 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-I-S3 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-I-S3 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-I-S3 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-I-K2 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-I-K2 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸ done


-- deb-Q-hi: 175 steps
lem-deb-Q-hi : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-Q-hi c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (run b21)))))))))))))))))))))
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b0 = at 0 5 (CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (lem-TR2-bf3fb9f8 c4) ▸
       at 1 0 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (lem-deb-Q-hi-eps c4)) ▸
       at 55 4 (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2 c4) ▸
       at 52 4 (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-CS2 c4) ▸
       at 49 4 (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-CS2 c4) ▸
       at 46 4 (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-CS2 c4) ▸
       at 43 4 (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4) ▸
       at 40 4 (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-CS2 c4) ▸ done

  b1 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b1 = at 37 4 (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4) ▸
       at 34 4 (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-CS2 c4) ▸
       at 31 4 (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4) ▸
       at 56 4 (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K2 c4) ▸
       at 53 4 (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-K2 c4) ▸
       at 50 4 (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-K2 c4) ▸
       at 47 4 (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-K2 c4) ▸
       at 44 4 (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K2 c4) ▸ done

  b2 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b2 = at 41 4 (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-K2 c4) ▸
       at 38 4 (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K2 c4) ▸
       at 35 4 (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-K2 c4) ▸
       at 32 4 (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K2 c4) ▸
       at 57 4 (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2 c4) ▸
       at 54 4 (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-CS2 c4) ▸
       at 51 4 (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-CS2 c4) ▸
       at 48 4 (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-CS2 c4) ▸ done

  b3 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b3 = at 45 4 (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4) ▸
       at 42 4 (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-CS2 c4) ▸
       at 39 4 (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4) ▸
       at 36 4 (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-CS2 c4) ▸
       at 33 4 (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4) ▸
       at 58 4 (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K2 c4) ▸
       at 55 4 (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-K2 c4) ▸
       at 52 4 (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-K2 c4) ▸ done

  b4 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b4 = at 49 4 (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-K2 c4) ▸
       at 46 4 (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K2 c4) ▸
       at 43 4 (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-K2 c4) ▸
       at 40 4 (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K2 c4) ▸
       at 37 4 (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-K2 c4) ▸
       at 34 4 (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K2 c4) ▸
       at 59 4 (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2 c4) ▸
       at 56 4 (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-CS2 c4) ▸ done

  b5 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b5 = at 53 4 (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-CS2 c4) ▸
       at 50 4 (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-CS2 c4) ▸
       at 47 4 (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4) ▸
       at 44 4 (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-CS2 c4) ▸
       at 41 4 (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4) ▸
       at 38 4 (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-CS2 c4) ▸
       at 35 4 (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4) ▸
       at 60 4 (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3 c4) ▸ done

  b6 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b6 = at 57 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4) ▸
       at 54 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4) ▸
       at 51 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4) ▸
       at 48 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 45 4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S3 c4) ▸
       at 42 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 39 4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S3 c4) ▸
       at 36 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸ done

  b7 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b7 = at 61 4 (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3 c4) ▸
       at 58 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4) ▸
       at 55 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4) ▸
       at 52 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4) ▸
       at 49 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 46 4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S3 c4) ▸
       at 43 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 40 4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S3 c4) ▸ done

  b8 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b8 = at 37 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 62 4 (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3 c4) ▸
       at 59 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4) ▸
       at 56 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4) ▸
       at 53 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4) ▸
       at 50 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 47 4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S3 c4) ▸
       at 44 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸ done

  b9 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b9 = at 41 4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S3 c4) ▸
       at 38 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 63 4 (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I c4) ▸
       at 60 4 (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-I c4) ▸
       at 57 4 (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-I c4) ▸
       at 54 4 (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-I c4) ▸
       at 51 4 (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-I c4) ▸
       at 48 4 (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-I c4) ▸ done

  b10 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b10 = at 45 4 (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-I c4) ▸
       at 42 4 (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-I c4) ▸
       at 39 4 (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-I c4) ▸
       at 64 4 (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3 c4) ▸
       at 61 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4) ▸
       at 58 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4) ▸
       at 55 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4) ▸
       at 52 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸ done

  b11 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b11 = at 49 4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S3 c4) ▸
       at 46 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 43 4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S3 c4) ▸
       at 40 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 65 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4) ▸
       at 62 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 59 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 56 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸ done

  b12 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b12 = at 53 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 50 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 47 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 44 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 41 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 66 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4) ▸
       at 63 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 60 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸ done

  b13 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b13 = at 57 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 54 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 51 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 48 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 45 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 42 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 67 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4) ▸
       at 64 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸ done

  b14 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b14 = at 61 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 58 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 55 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 52 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 49 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 46 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 43 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 68 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4) ▸ done

  b15 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b15 = at 65 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 62 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 59 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 56 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 53 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 50 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 47 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 44 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸ done

  b16 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b16 = at 69 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4) ▸
       at 66 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 63 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 60 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 57 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 54 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 51 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 48 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸ done

  b17 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b17 = at 45 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 70 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4) ▸
       at 67 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 64 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 61 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 58 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 55 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 52 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸ done

  b18 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b18 = at 49 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 46 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 71 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4) ▸
       at 68 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 65 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 62 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 59 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 56 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸ done

  b19 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b19 = at 53 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 50 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 47 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 72 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4) ▸
       at 69 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 66 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 63 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 60 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸ done

  b20 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b20 = at 57 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 54 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 51 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 48 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 73 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4) ▸
       at 70 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 67 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸
       at 64 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4) ▸ done

  b21 : Chain (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b21 = at 61 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 58 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 55 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 52 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4) ▸
       at 49 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4) ▸
       at 1 40 (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (sym (lem-deb-Q-hi-split-a c4)) ▸
       at 20 36 (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ []) (sym (lem-deb-Q-hi-split-b c4)) ▸ done


-- deb-Q-lo-eps @02132031: 104 steps
lem-deb-Q-lo-eps-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-Q-lo-eps-at02132031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 2 2 [] (wl1083 (lit c4)) ▸
       at 3 2 [] (wl1083 (lit c4)) ▸
       at 4 2 [] (wl1083 (lit c4)) ▸
       at 5 2 [] (wl1083 (lit c4)) ▸
       at 6 2 [] (wl1083 (lit c4)) ▸
       at 7 2 [] (wl1083 (lit c4)) ▸
       at 8 2 [] (wl1083 (lit c4)) ▸
       at 9 2 [] (wl1083 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b1 = at 10 2 [] (wl1083 (lit c4)) ▸
       at 11 2 [] (wl1083 (lit c4)) ▸
       at 12 2 [] (wl1083 (lit c4)) ▸
       at 13 2 [] (wl1083 (lit c4)) ▸
       at 14 2 [] (wl1083 (lit c4)) ▸
       at 15 2 [] (wl1083 (lit c4)) ▸
       at 16 2 [] (wl1083 (lit c4)) ▸
       at 17 2 [] (wl1083 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sw12 ∷ X4 ∷ [])
  b2 = at 18 2 [] (wl1083 (lit c4)) ▸
       at 19 2 [] (wl1083 (lit c4)) ▸
       at 20 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 19 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸
       at 18 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 17 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 16 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 15 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sw12 ∷ X4 ∷ [])
  b3 = at 14 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 13 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 12 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 11 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 10 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 9 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸
       at 8 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 7 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸ done

  b4 : Chain (X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b4 = at 6 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 5 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 4 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 3 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 2 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 1 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 21 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 20 2 (Sw01 ∷ S4 ∷ []) (sym (c₂ (Swap) (S ↑ ↑))) ▸ done

  b5 : Chain (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b5 = at 19 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 18 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 17 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 16 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 15 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸
       at 14 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 13 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸
       at 12 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸ done

  b6 : Chain (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b6 = at 11 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 10 2 (Sw01 ∷ S4 ∷ []) (sym (c₂ (Swap) (S ↑ ↑))) ▸
       at 9 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 8 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 7 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 6 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 5 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸
       at 4 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸ done

  b7 : Chain (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b7 = at 3 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 21 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸
       at 20 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 19 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 18 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 17 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸ done

  b8 : Chain (X4 ∷ Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw23 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b8 = at 16 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 15 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 14 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 13 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 12 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 11 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸
       at 10 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 9 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸ done

  b9 : Chain (X4 ∷ Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw23 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw12 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b9 = at 8 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 7 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 6 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 5 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 4 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 3 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 23 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 22 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸ done

  b10 : Chain (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw12 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b10 = at 21 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 20 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 19 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 18 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 17 2 (Sw12 ∷ CK43 ∷ []) (sym (c₃ (Swap ↑) (CK₁₀))) ▸
       at 16 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 15 2 (Sw12 ∷ CK43 ∷ []) (sym (c₃ (Swap ↑) (CK₁₀))) ▸
       at 14 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸ done

  b11 : Chain (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b11 = at 13 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 12 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸
       at 11 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 10 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 9 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 8 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 7 2 (Sw12 ∷ CK43 ∷ []) (sym (c₃ (Swap ↑) (CK₁₀))) ▸
       at 6 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸ done

  b12 : Chain (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) []
  b12 = at 5 2 (Sw12 ∷ CK43 ∷ []) (sym (c₃ (Swap ↑) (CK₁₀))) ▸
       at 4 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 5 19 [] (lem-TR2-11f6930f c4) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸
       at 3 2 [] (wl0003 (lit c4)) ▸
       at 2 2 [] (wl0018 (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸
       at 0 2 [] (wl1083 (lit c4)) ▸ done


-- deb-Q-lo-split-a @02132031: 55 steps
lem-deb-Q-lo-split-a-at02132031 : Ws → ⟪ (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-deb-Q-lo-split-a-at02132031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 4 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4)) ▸
       at 3 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 8 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 7 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 6 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 12 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4)) ▸
       at 11 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b1 = at 10 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-K3-K3-at02132031 c4)) ▸
       at 9 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 16 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 14 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 13 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 12 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 20 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b2 = at 19 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 18 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 17 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 16 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 15 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 24 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 23 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ ι ∷ S0 ∷ [])
  b3 = at 21 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 20 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 19 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 18 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 28 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 27 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 26 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ S0 ∷ [])
  b4 = at 24 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 23 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 21 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at02132031 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at02132031 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-I-K3-at02132031 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-I-K3-at02132031 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 36 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 35 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-S2-I-at02132031 c4)) ▸
       at 34 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ [])
  b6 = at 33 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 32 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 31 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 29 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 28 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 27 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸ done


-- deb-Q-lo-split-b @02132031: 45 steps
lem-deb-Q-lo-split-b-at02132031 : Ws → ⟪ (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ []) ⟫ʷ
lem-deb-Q-lo-split-b-at02132031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ [])
  b0 = at 0 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 4 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4)) ▸
       at 3 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 8 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 7 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 6 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 12 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4)) ▸
       at 11 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S0 ∷ S0 ∷ ι ∷ [])
  b1 = at 10 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-K3-K3-at02132031 c4)) ▸
       at 9 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 16 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 14 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 13 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 12 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 20 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S0 ∷ S0 ∷ ι ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ S0 ∷ ι ∷ [])
  b2 = at 19 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 18 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 17 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 16 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 15 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 24 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 23 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ S0 ∷ ι ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ ι ∷ [])
  b3 = at 21 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 20 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 19 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 18 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 28 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 27 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 26 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ ι ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ [])
  b4 = at 24 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 23 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 21 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at02132031 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at02132031 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-I-K3-at02132031 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-I-K3-at02132031 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸ done

