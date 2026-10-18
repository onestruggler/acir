{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D046 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0003 ; wl0006 ; wl0011 ; wl0013 ; wl0017 ; wl0018 ; wl0087 ; wl0099)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D044 using (lem-F4-CS2-CS2-at02132031 ; lem-F4-CS2-I-at02132031 ; lem-F4-CS2-K2-at02132031 ; lem-F4-CS2-S2-at02132031 ; lem-F4-CS2-S3-at02132031 ; lem-F4-I-CS2-at02132031 ; lem-F4-I-I-at02132031 ; lem-F4-I-K2-at02132031 ; lem-F4-I-S3-at02132031 ; lem-F4-K2-CS2-at02132031 ; lem-F4-K2-I-at02132031 ; lem-F4-K2-K2-at02132031 ; lem-F4-K2-S3-at02132031 ; lem-F4-S3-CS2-at02132031 ; lem-F4-S3-I-at02132031 ; lem-F4-S3-K2-at02132031 ; lem-F4-S3-S3-at02132031 ; lem-S2-SBOX⟨0·2·43·1⟩-at02132031 ; lem-deb-P-hi-eps-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw1-R)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-CK40-sw0-L ; lem-comm-push-CK40-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-push-CK40-sw1-R ; lem-comm-push-CK41-sw0-R ; lem-comm-push-CS14-sw0-R ; lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R ; lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L)
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-570a2ddc)
-- deb-P-hi @02132031 part0: 368 steps
lem-deb-P-hi-at02132031-part0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ
lem-deb-P-hi-at02132031-part0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (run b45)))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 2 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 1 2 (Sw12 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw1-L (lit c4)) ▸
       at 0 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 3 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 2 2 (Sw01 ∷ CK41 ∷ []) (lem-comm-push-CK40-sw0-L (lit c4)) ▸
       at 1 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸ done

  b1 : Chain (Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 4 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 3 2 (Sw23 ∷ CK41 ∷ []) (wl0099 (lit c4)) ▸
       at 2 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 5 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 4 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 3 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸ done

  b2 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b2 = at 4 3 (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (lem-TR2-570a2ddc c4) ▸
       at 3 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 4 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 5 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 6 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 7 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 8 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 9 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸ done

  b3 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ Sw12 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b3 = at 10 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 11 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 12 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 13 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 14 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 15 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 16 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 17 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸ done

  b4 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ Sw12 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b4 = at 18 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 19 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 20 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 21 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 22 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 23 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 24 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 25 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸ done

  b5 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sw12 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b5 = at 26 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 27 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 28 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 29 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 30 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 31 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 32 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 33 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸ done

  b6 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sw12 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b6 = at 34 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 35 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 36 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 37 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 38 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 39 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 40 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 41 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸ done

  b7 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b7 = at 42 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 43 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 44 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 45 2 [] (wl0006 (lit c4)) ▸
       at 2 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 3 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 4 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 5 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸ done

  b8 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b8 = at 6 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 7 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 8 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 9 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 10 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 11 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 12 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 13 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸ done

  b9 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sw23 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ Sw23 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b9 = at 14 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 15 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 16 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 17 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 18 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 19 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 20 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 21 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸ done

  b10 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ Sw23 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b10 = at 22 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 23 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 24 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 25 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 26 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 27 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 28 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 29 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸ done

  b11 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw23 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b11 = at 30 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 31 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 32 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 33 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 34 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 35 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 36 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 37 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸ done

  b12 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw23 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ [])
  b12 = at 38 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 39 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 40 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 41 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 42 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 43 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 44 2 [] (wl0003 (lit c4)) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸ done

  b13 : Chain (Sw12 ∷ CK40 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ [])
  b13 = at 2 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 3 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 4 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 5 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 6 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 7 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 8 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 9 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸ done

  b14 : Chain (Sw12 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw01 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ [])
  b14 = at 10 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 11 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸
       at 12 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 13 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸
       at 14 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 15 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 16 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 17 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b15 : Chain (Sw12 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw01 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ [])
  b15 = at 18 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 19 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 20 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 21 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 22 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 23 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 24 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 25 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸ done

  b16 : Chain (Sw12 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ [])
  b16 = at 26 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 27 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 28 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 29 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 30 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸
       at 31 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 32 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸
       at 33 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸ done

  b17 : Chain (Sw12 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ [])
  b17 = at 34 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 35 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 36 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 37 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 38 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 39 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 40 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 41 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸ done

  b18 : Chain (Sw12 ∷ CK40 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ []) (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ [])
  b18 = at 42 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 43 2 [] (wl0018 (lit c4)) ▸
       at 0 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 3 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 4 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 5 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸ done

  b19 : Chain (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ []) (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ [])
  b19 = at 6 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 7 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 8 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 9 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 10 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 11 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 12 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 13 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸ done

  b20 : Chain (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ []) (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ [])
  b20 = at 14 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 15 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 16 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 17 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 18 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 19 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 20 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 21 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸ done

  b21 : Chain (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ []) (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ [])
  b21 = at 22 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 23 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 24 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 25 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 26 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 27 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 28 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 29 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸ done

  b22 : Chain (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sb1-0-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ []) (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ [])
  b22 = at 30 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 31 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 32 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 33 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 34 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 35 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 36 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 37 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸ done

  b23 : Chain (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b23 = at 38 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 39 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 40 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 41 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 42 2 [] (wl0006 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩-at02132031 c4) ▸
       at 2 0 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (sym (lem-deb-P-hi-eps-at02132031 c4)) ▸
       at 80 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸ done

  b24 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b24 = at 77 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 74 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4) ▸
       at 71 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 68 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 65 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 62 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 59 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 56 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸ done

  b25 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b25 = at 53 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 50 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 81 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 78 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 75 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4) ▸
       at 72 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 69 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 66 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸ done

  b26 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b26 = at 63 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 60 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 57 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 54 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 51 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 82 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 79 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 76 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4) ▸ done

  b27 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b27 = at 73 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 70 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 67 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 64 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 61 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 58 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 55 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 52 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸ done

  b28 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b28 = at 83 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 80 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 77 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4) ▸
       at 74 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 71 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 68 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 65 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 62 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸ done

  b29 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b29 = at 59 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 56 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 53 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 84 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 81 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 78 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4) ▸
       at 75 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 72 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸ done

  b30 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b30 = at 69 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 66 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 63 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 60 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 57 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 54 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 85 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 82 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸ done

  b31 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b31 = at 79 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4) ▸
       at 76 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 73 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 70 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 67 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 64 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 61 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 58 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸ done

  b32 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b32 = at 55 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 86 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 83 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 80 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4) ▸
       at 77 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 74 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 71 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 68 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸ done

  b33 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b33 = at 65 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 62 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 59 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 56 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 87 4 (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K2-at02132031 c4) ▸
       at 84 4 (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K2-at02132031 c4) ▸
       at 81 4 (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K2-at02132031 c4) ▸
       at 78 4 (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-K2-at02132031 c4) ▸ done

  b34 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b34 = at 75 4 (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-K2-at02132031 c4) ▸
       at 72 4 (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-K2-at02132031 c4) ▸
       at 69 4 (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K2-at02132031 c4) ▸
       at 66 4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-K2-at02132031 c4) ▸
       at 63 4 (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K2-at02132031 c4) ▸
       at 60 4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-K2-at02132031 c4) ▸
       at 57 4 (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K2-at02132031 c4) ▸
       at 88 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸ done

  b35 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b35 = at 85 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 82 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4) ▸
       at 79 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 76 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 73 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 70 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 67 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 64 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸ done

  b36 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b36 = at 61 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 58 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 89 4 (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K2-at02132031 c4) ▸
       at 86 4 (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K2-at02132031 c4) ▸
       at 83 4 (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K2-at02132031 c4) ▸
       at 80 4 (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-K2-at02132031 c4) ▸
       at 77 4 (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-K2-at02132031 c4) ▸
       at 74 4 (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-K2-at02132031 c4) ▸ done

  b37 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b37 = at 71 4 (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K2-at02132031 c4) ▸
       at 68 4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-K2-at02132031 c4) ▸
       at 65 4 (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K2-at02132031 c4) ▸
       at 62 4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-K2-at02132031 c4) ▸
       at 59 4 (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K2-at02132031 c4) ▸
       at 90 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 87 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 84 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4) ▸ done

  b38 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b38 = at 81 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 78 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 75 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4) ▸
       at 72 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 69 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 66 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸
       at 63 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4) ▸
       at 60 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4) ▸ done

  b39 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b39 = at 91 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 88 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 85 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3-at02132031 c4) ▸
       at 82 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4) ▸
       at 79 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4) ▸
       at 76 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4) ▸
       at 73 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 70 4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S3-at02132031 c4) ▸ done

  b40 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b40 = at 67 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 64 4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S3-at02132031 c4) ▸
       at 61 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 92 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 89 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 86 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3-at02132031 c4) ▸
       at 83 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4) ▸
       at 80 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4) ▸ done

  b41 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b41 = at 77 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4) ▸
       at 74 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 71 4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S3-at02132031 c4) ▸
       at 68 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 65 4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S3-at02132031 c4) ▸
       at 62 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 93 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 90 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸ done

  b42 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b42 = at 87 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3-at02132031 c4) ▸
       at 84 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4) ▸
       at 81 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4) ▸
       at 78 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4) ▸
       at 75 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 72 4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S3-at02132031 c4) ▸
       at 69 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 66 4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S3-at02132031 c4) ▸ done

  b43 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b43 = at 63 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 94 4 (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at02132031 c4) ▸
       at 91 4 (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at02132031 c4) ▸
       at 88 4 (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I-at02132031 c4) ▸
       at 85 4 (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-I-at02132031 c4) ▸
       at 82 4 (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-I-at02132031 c4) ▸
       at 79 4 (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-I-at02132031 c4) ▸
       at 76 4 (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at02132031 c4) ▸ done

  b44 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b44 = at 73 4 (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-I-at02132031 c4) ▸
       at 70 4 (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at02132031 c4) ▸
       at 67 4 (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-I-at02132031 c4) ▸
       at 64 4 (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at02132031 c4) ▸
       at 95 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 92 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 89 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3-at02132031 c4) ▸
       at 86 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4) ▸ done

  b45 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b45 = at 83 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4) ▸
       at 80 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4) ▸
       at 77 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 74 4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S3-at02132031 c4) ▸
       at 71 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 68 4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S3-at02132031 c4) ▸
       at 65 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4) ▸
       at 96 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸ done

