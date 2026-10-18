{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D047 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0003 ; wl0006 ; wl0011 ; wl0087 ; wl0099 ; wl0181 ; wl0206 ; wl0208 ; wl0209 ; wl0211 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0263 ; wl0314 ; wl0549 ; wl0551 ; wl0553 ; wl0557 ; wl0558 ; wl0575 ; wl0577 ; wl0579 ; wl0583 ; wl0585 ; wl0603 ; wl0605 ; wl0607 ; wl0643 ; wl0709 ; wl0710 ; wl0714 ; wl0716 ; wl0720 ; wl0723 ; wl0732 ; wl0734 ; wl0735 ; wl0894 ; wl0896 ; wl0900 ; wl0999 ; wl1000 ; wl1001 ; wl1002 ; wl1003 ; wl1004 ; wl1005 ; wl1006 ; wl1083 ; wl1113 ; wl1413 ; wp0052 ; wp0053 ; wp0055 ; wp0060 ; wp0061 ; wp0062 ; wp0064 ; wp0065 ; wp0067 ; wp0068 ; wp0069 ; wp0070 ; wp0071 ; wp0072 ; wp0074 ; wp0265 ; wp0380 ; wp0381 ; wp0407 ; wp0408 ; wp0458 ; wp0459 ; wp0518 ; wp0619 ; wp0620 ; wp0621 ; wp0625 ; wp0626 ; wp0634 ; wp0722 ; wp0805 ; wp0806 ; wp1264)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at243243 ; lem-box2-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D044 using (lem-F4-CS2-S2-at02132031 ; lem-F4-I-S2-at02132031 ; lem-F4-K2-S2-at02132031 ; lem-F4-S3-S2-at02132031)
open import Examples.Groups.Clifford+CS.FiveV.D.D045 using (lem-deb-P-hi-split-a-at02132031 ; lem-deb-P-hi-split-b-at02132031)
open import Examples.Groups.Clifford+CS.FiveV.D.D046 using (lem-deb-P-hi-at02132031-part0)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CX14-TOFF023)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CX32-CCZ014)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CK41-TOFF023 ; lem-comm-TOFF023-CK41)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CCZ014-CX23 ; lem-comm-TOFF023-CX14)
open import Examples.Groups.Clifford+CS.FiveV.D.R006 using (lem-comm-CCZ014-CX32 ; lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L)
open import Examples.Groups.Clifford+CS.FiveV.TR2 using (lem-TR2-0d166c34)
-- deb-P-hi @02132031 part1: 100 steps
lem-deb-P-hi-at02132031-part1 : Ws → ⟪ (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ
lem-deb-P-hi-at02132031-part1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b0 = at 93 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 90 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4) ▸
       at 87 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 84 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 81 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 78 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 75 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 72 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸ done

  b1 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b1 = at 69 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 66 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 97 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 94 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 91 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4) ▸
       at 88 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 85 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 82 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸ done

  b2 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b2 = at 79 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 76 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 73 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 70 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 67 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 98 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 95 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 92 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4) ▸ done

  b3 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b3 = at 89 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 86 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 83 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 80 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 77 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 74 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 71 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 68 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸ done

  b4 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b4 = at 99 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 96 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 93 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4) ▸
       at 90 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 87 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 84 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 81 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 78 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸ done

  b5 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b5 = at 75 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 72 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 69 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 100 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 97 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 94 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4) ▸
       at 91 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 88 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸ done

  b6 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b6 = at 85 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 82 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 79 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 76 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 73 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 70 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 101 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 98 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸ done

  b7 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b7 = at 95 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4) ▸
       at 92 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 89 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 86 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 83 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 80 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 77 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 74 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸ done

  b8 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b8 = at 71 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 102 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 99 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 96 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4) ▸
       at 93 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 90 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 87 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 84 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸ done

  b9 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b9 = at 81 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 78 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 75 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 72 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 103 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 100 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 97 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4) ▸
       at 94 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸ done

  b10 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b10 = at 91 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 88 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 85 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 82 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 79 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 76 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 73 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 104 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸ done

  b11 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b11 = at 101 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 98 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4) ▸
       at 95 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 92 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 89 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S2-at02132031 c4) ▸
       at 86 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 83 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 80 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸ done

  b12 : Chain (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b12 = at 77 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S2-at02132031 c4) ▸
       at 74 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4) ▸
       at 2 64 (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (sym (lem-deb-P-hi-split-a-at02132031 c4)) ▸
       at 27 44 (CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (sym (lem-deb-P-hi-split-b-at02132031 c4)) ▸ done


-- deb-P-hi @02132031: 2 steps
lem-deb-P-hi-at02132031 : Ws → ⟪ (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ
lem-deb-P-hi-at02132031 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  b0 = at 0 3 (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (lem-deb-P-hi-at02132031-part0 c4) ▸
       at 0 122 (CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (lem-deb-P-hi-at02132031-part1 c4) ▸ done


-- F1-CS-K0@0: 3 steps
lem-F1-CS-K0at0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0at0 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 3 (CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (lem-deb-P-hi-at02132031 c4) ▸
       at 0 43 (CS04 ∷ CK40 ∷ CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (wp1264 c4) ▸
       at 2 41 (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (sym (lem-deb-P-hi-at02132031 c4)) ▸ done


-- S2-SBOX(0;2;43;1) @132132: 86 steps
lem-S2-SBOX⟨0·2·43·1⟩-at132132 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩-at132132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ014 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 5 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 7 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 3 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 9 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 8 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ014 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 7 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 5 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 3 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 4 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 4 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 6 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸ done

  b3 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 12 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 11 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 10 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 8 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 6 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 7 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸ done

  b4 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 5 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 8 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 11 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 10 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 8 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸ done

  b5 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b5 = at 8 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 6 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 7 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 3 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸ done

  b6 : Chain (Bx0-1423 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ K3 ∷ CS24 ∷ CX32 ∷ CCZ014 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b6 = at 5 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 1 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 7 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 6 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 5 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸ done

  b7 : Chain (Bx0-1423 ∷ K3 ∷ CS24 ∷ CX32 ∷ CCZ014 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ014 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b7 = at 3 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 1 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 2 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 2 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 4 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 9 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸ done

  b8 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ014 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b8 = at 8 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 6 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 5 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 6 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸ done

  b9 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b9 = at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 6 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 5 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸ done

  b10 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ124 ∷ [])
  b10 = at 5 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 1 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 0 2 [] (lem-box2-at243243 c4) ▸
       at 0 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 2 2 [] (wl0263 (lit c4)) ▸
       at 0 8 (CCZ124 ∷ []) (sym (wl1113 (lit c4))) ▸ done


-- deb-P-hi-eps @132132: 86 steps
lem-deb-P-hi-eps-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-hi-eps-at132132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 2 2 [] (wl1083 (lit c4)) ▸
       at 3 2 [] (wl1083 (lit c4)) ▸
       at 4 2 [] (wl1083 (lit c4)) ▸
       at 5 2 [] (wl1083 (lit c4)) ▸
       at 6 2 [] (wl1083 (lit c4)) ▸
       at 7 2 [] (wl1083 (lit c4)) ▸
       at 8 2 [] (wl1083 (lit c4)) ▸
       at 9 2 [] (wl1083 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 10 2 [] (wl1083 (lit c4)) ▸
       at 11 2 [] (wl1083 (lit c4)) ▸
       at 12 2 [] (wl1083 (lit c4)) ▸
       at 13 2 [] (wl1083 (lit c4)) ▸
       at 14 2 [] (wl1083 (lit c4)) ▸
       at 15 2 [] (wl1083 (lit c4)) ▸
       at 16 2 [] (wl1083 (lit c4)) ▸
       at 17 2 [] (wl1083 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 18 2 [] (wl1083 (lit c4)) ▸
       at 19 2 [] (wl1083 (lit c4)) ▸
       at 20 2 [] (wl1083 (lit c4)) ▸
       at 21 2 [] (wl1083 (lit c4)) ▸
       at 22 2 [] (wl1083 (lit c4)) ▸
       at 23 2 [] (wl1083 (lit c4)) ▸
       at 24 2 [] (wl1083 (lit c4)) ▸
       at 25 2 [] (wl1083 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ Sw23 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw23 ∷ X4 ∷ [])
  b3 = at 26 2 [] (wl1083 (lit c4)) ▸
       at 27 2 [] (wl1083 (lit c4)) ▸
       at 28 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 27 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 26 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 25 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸
       at 24 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 23 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ Sw23 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw23 ∷ X4 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw23 ∷ S4 ∷ CS34 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw23 ∷ X4 ∷ [])
  b4 = at 22 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 21 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 20 2 (Sw23 ∷ CK41 ∷ []) (wl0099 (lit c4)) ▸
       at 19 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 18 2 (Sw23 ∷ CK41 ∷ []) (wl0099 (lit c4)) ▸
       at 17 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 16 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 15 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸ done

  b5 : Chain (X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sw23 ∷ S4 ∷ CS34 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw23 ∷ X4 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw23 ∷ X4 ∷ [])
  b5 = at 14 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 13 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 12 2 (Sw23 ∷ CS34 ∷ []) (wl0011 (lit c4)) ▸
       at 11 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 10 2 (Sw23 ∷ CK41 ∷ []) (wl0099 (lit c4)) ▸
       at 9 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 8 2 (Sw23 ∷ CK41 ∷ []) (wl0099 (lit c4)) ▸
       at 7 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸ done

  b6 : Chain (X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ X4 ∷ [])
  b6 = at 6 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 5 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 4 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 3 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 2 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 1 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 29 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 28 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸ done

  b7 : Chain (X4 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ X4 ∷ [])
  b7 = at 27 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 26 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸
       at 25 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 24 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 23 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 22 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 21 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 20 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸ done

  b8 : Chain (X4 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ X4 ∷ [])
  b8 = at 19 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 18 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 17 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 16 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸
       at 15 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 14 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 13 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 12 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸ done

  b9 : Chain (X4 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ X4 ∷ [])
  b9 = at 11 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 10 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 9 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 8 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 7 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 6 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 5 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 4 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸ done

  b10 : Chain (X4 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ X4 ∷ []) []
  b10 = at 3 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 2 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 3 27 [] (lem-TR2-0d166c34 c4) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸
       at 1 2 [] (wl0003 (lit c4)) ▸
       at 0 2 [] (wl1083 (lit c4)) ▸ done


-- F4-CS2-CS2 @132132: 286 steps
lem-F4-CS2-CS2-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-CS2-at132132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 4 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 6 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (wl0314 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 10 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 9 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS12⁻ ∷ []) (sym (wp0265 c4)) ▸
       at 7 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0314 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 4 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (wl0208 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 5 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸ done

  b3 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ014 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 6 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 8 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 9 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸ done

  b4 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ014 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 8 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 6 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 5 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 5 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 7 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸ done

  b5 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b5 = at 13 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 12 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 11 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 9 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 7 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 8 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸ done

  b6 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b6 = at 6 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 9 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 8 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 12 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 11 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 10 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 9 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸ done

  b7 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b7 = at 9 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 7 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 8 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 3 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 4 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸ done

  b8 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ014 ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b8 = at 5 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 6 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 8 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 7 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 6 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸ done

  b9 : Chain (X4 ∷ Bx0-1423 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ014 ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b9 = at 5 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 4 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 2 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 3 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 3 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 5 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 11 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸ done

  b10 : Chain (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b10 = at 10 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 9 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 7 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 5 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 6 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸ done

  b11 : Chain (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b11 = at 7 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 6 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 10 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 7 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b12 : Chain (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b12 = at 5 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 6 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (wl0314 (lit c4)) ▸ done

  b13 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b13 = at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS12⁻ ∷ []) (sym (wp0265 c4)) ▸
       at 5 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0314 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸ done

  b14 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CCZ014 ∷ CX32 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b14 = at 3 3 (X4 ∷ []) (wl0208 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (wl0314 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 5 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸ done

  b15 : Chain (Bx0-1423 ∷ X4 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CCZ014 ∷ CX32 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CCZ014 ∷ CX32 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b15 = at 4 2 (CCZ014 ∷ CS12⁻ ∷ []) (sym (wp0265 c4)) ▸
       at 3 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0314 (lit c4))) ▸
       at 3 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 4 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (wl0314 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸ done

  b16 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CCZ014 ∷ CX32 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b16 = at 6 2 (CCZ014 ∷ CS12⁻ ∷ []) (sym (wp0265 c4)) ▸
       at 5 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0314 (lit c4))) ▸
       at 5 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 8 (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) (wl0999 (lit c4)) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸ done

  b17 : Chain (Bx0-1423 ∷ X4 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b17 = at 3 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 5 2 [] (wl0263 (lit c4)) ▸
       at 4 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0894 (lit c4))) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸ done

  b18 : Chain (Bx0-1423 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b18 = at 6 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 6 (CX23 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1001 (lit c4))) ▸
       at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CX20 ∷ CX23 ∷ Toff023 ∷ []) (sym (wl1002 (lit c4))) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 4 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸ done

  b19 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b19 = at 10 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (CX32 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX32 (lit c4)) ▸
       at 12 2 (CS24⁻ ∷ CCZ014 ∷ []) (wp0722 c4) ▸
       at 13 2 (CX32 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX32 (lit c4)) ▸
       at 14 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸ done

  b20 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b20 = at 9 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 3 2 (CX20 ∷ Toff023 ∷ []) (sym (wl1003 (lit c4))) ▸
       at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 4 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 5 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 8 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸ done

  b21 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ CX23 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff023 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b21 = at 4 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 5 2 (CX20 ∷ CX23 ∷ Toff023 ∷ []) (sym (wl1002 (lit c4))) ▸
       at 7 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 9 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 8 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 11 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸ done

  b22 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ CX23 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff023 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ014 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b22 = at 12 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 8 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 9 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 3 3 (CCZ124 ∷ []) (sym (wp0380 c4)) ▸
       at 5 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 3 4 (CX23 ∷ Toff324 ∷ []) (wl1004 (lit c4)) ▸
       at 2 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 4 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸ done

  b23 : Chain (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ014 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CX23 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b23 = at 3 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 4 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 5 2 (CX32 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX32 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ CCZ014 ∷ []) (wp0722 c4) ▸
       at 7 2 (CX32 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX32 (lit c4)) ▸
       at 8 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 9 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 3 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸ done

  b24 : Chain (Bx0-1423 ∷ X4 ∷ CX23 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS13 ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b24 = at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (Toff324 ∷ X4 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 4 2 (CS13 ∷ X4 ∷ []) (sym (wl0896 (lit c4))) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS13 ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b25 = at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 5 (CS13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1005 (lit c4))) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 3 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b26 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ [])
  b26 = at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X4 ∷ []) (sym (wl0896 (lit c4))) ▸
       at 5 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0894 (lit c4))) ▸
       at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b27 = at 5 6 (CX23 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1001 (lit c4))) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (CX20 ∷ CX23 ∷ Toff023 ∷ []) (sym (wl1002 (lit c4))) ▸
       at 9 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 6 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 12 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸ done

  b28 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 12 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 13 2 (CX32 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX32 (lit c4)) ▸
       at 14 2 (CS24⁻ ∷ CCZ014 ∷ []) (wp0722 c4) ▸
       at 15 2 (CX32 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX32 (lit c4)) ▸
       at 16 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 11 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸ done

  b29 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ Toff023 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b29 = at 5 2 (CX20 ∷ Toff023 ∷ []) (sym (wl1003 (lit c4))) ▸
       at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 6 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 10 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b30 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ Toff023 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ CX23 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b30 = at 7 2 (CX20 ∷ CX23 ∷ Toff023 ∷ []) (sym (wl1002 (lit c4))) ▸
       at 9 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 11 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 10 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 11 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 12 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 13 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 14 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸ done

  b31 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ CX23 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ K3 ∷ CCZ014 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b31 = at 10 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 11 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 5 3 (CCZ124 ∷ []) (sym (wp0380 c4)) ▸
       at 7 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 5 4 (CX23 ∷ Toff324 ∷ []) (wl1004 (lit c4)) ▸
       at 4 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b32 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ K3 ∷ CCZ014 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b32 = at 6 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 7 2 (CX32 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX32 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ014 ∷ []) (wp0722 c4) ▸
       at 9 2 (CX32 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX32 (lit c4)) ▸
       at 10 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b33 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13⁻ ∷ X4 ∷ [])
  b33 = at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 3 (Toff324 ∷ X4 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ X4 ∷ []) (sym (wl0900 (lit c4))) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13⁻ ∷ X4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b34 = at 6 5 (CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1006 (lit c4))) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 6 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 5 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b35 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b35 = at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X4 ∷ []) (sym (wl0900 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4-I-CS2 @132132: 15 steps
lem-F4-I-CS2-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-CS2-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 4 (CCZ014 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0407 c4)) ▸
       at 1 4 (Toff023 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0408 c4)) ▸
       at 2 4 (CCZ014 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0407 c4)) ▸
       at 3 4 (Toff023 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0408 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0558 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (ι ∷ S4⁻ ∷ []) (wl0557 (lit c4)) ▸
       at 1 2 (X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0557 (lit c4))) ▸ done


-- F4-S3-CS2 @132132: 15 steps
lem-F4-S3-CS2-at132132 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-CS2-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 4 (CCZ014 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0458 c4)) ▸
       at 1 4 (Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0459 c4)) ▸
       at 2 4 (CCZ014 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0458 c4)) ▸
       at 3 4 (Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0459 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0585 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (S2 ∷ CS24⁻ ∷ []) (sym (wl0583 (lit c4))) ▸
       at 1 2 (X4 ∷ CS24 ∷ X4 ∷ []) (wl0583 (lit c4)) ▸ done


-- F4-K2-CS2 @132132: 17 steps
lem-F4-K2-CS2-at132132 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS2-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 4 (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0518 c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4)) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b1 = at 2 4 (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0518 c4)) ▸
       at 5 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0643 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4-CS2-K2 @132132: 19 steps
lem-F4-CS2-K2-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K2-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CK41 ∷ Toff023 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK41 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0734 (lit c4))) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 5 2 (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CK41 ∷ Toff023 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b1 = at 6 2 (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 3 4 (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) (wp0634 c4) ▸
       at 2 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 3 2 (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 1 4 (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) (wp0634 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 4 (CK41 ∷ X4 ∷ []) (sym (wl0723 (lit c4))) ▸ done


-- F4-I-K2 @132132: 1 steps
lem-F4-I-K2-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K2-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0553 (lit c4))) ▸ done


-- F4-S3-K2 @132132: 1 steps
lem-F4-S3-K2-at132132 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K2-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0579 (lit c4))) ▸ done


-- F4-K2-K2 @132132: 1 steps
lem-F4-K2-K2-at132132 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K2-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0607 (lit c4))) ▸ done


-- F4-CS2-S3 @132132: 15 steps
lem-F4-CS2-S3-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S3-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ S2 ∷ CS24⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S2 ∷ CS24⁻ ∷ X4 ∷ []) (sym (wl0714 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (S2 ∷ CS24⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0732 (lit c4))) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 3 (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) (sym (wp0625 c4)) ▸
       at 3 3 (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) (wp0626 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ S2 ∷ CS24⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 2 3 (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) (sym (wp0625 c4)) ▸
       at 1 3 (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) (wp0626 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 3 (CS24 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸ done


-- F4-I-S3 @132132: 1 steps
lem-F4-I-S3-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S3-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0551 (lit c4))) ▸ done


-- F4-S3-S3 @132132: 1 steps
lem-F4-S3-S3-at132132 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S3-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0577 (lit c4))) ▸ done


-- F4-K2-S3 @132132: 1 steps
lem-F4-K2-S3-at132132 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S3-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0605 (lit c4))) ▸ done


-- F4-CS2-I @132132: 17 steps
lem-F4-CS2-I-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-I-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ ι ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (ι ∷ S4⁻ ∷ X4 ∷ []) (wl0709 (lit c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 2 6 (ι1 ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (wp0619 c4) ▸
       at 2 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ ι ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ ι ∷ S4⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 4 3 (ι ∷ S4⁻ ∷ Toff023 ∷ []) (wp0620 c4) ▸
       at 3 3 (ι ∷ S4⁻ ∷ CCZ014 ∷ []) (wp0621 c4) ▸
       at 2 3 (ι ∷ S4⁻ ∷ Toff023 ∷ []) (wp0620 c4) ▸
       at 1 3 (ι ∷ S4⁻ ∷ CCZ014 ∷ []) (wp0621 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ ι ∷ S4⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 0 3 (S4 ∷ X4 ∷ []) (sym (wl0710 (lit c4))) ▸ done


-- F4-I-I @132132: 1 steps
lem-F4-I-I-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-I-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0549 (lit c4))) ▸ done


-- F4-S3-I @132132: 1 steps
lem-F4-S3-I-at132132 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-I-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0575 (lit c4))) ▸ done


-- F4-K2-I @132132: 1 steps
lem-F4-K2-I-at132132 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-I-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0603 (lit c4))) ▸ done

