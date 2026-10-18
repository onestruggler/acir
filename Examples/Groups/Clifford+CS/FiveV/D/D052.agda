{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D052 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0003 ; wl0006 ; wl0013 ; wl0017 ; wl0018 ; wl0087 ; wl0090 ; wl0553 ; wl0603 ; wl0604 ; wl0607 ; wl0642 ; wl0720 ; wl0721 ; wl0722 ; wl0723 ; wl1083 ; wl1411 ; wl1417 ; wp0257 ; wp0410 ; wp0411 ; wp0412 ; wp0416 ; wp0419 ; wp0420 ; wp0421 ; wp0494 ; wp0517 ; wp0614 ; wp1267)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at0210243143)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-F4-I-S3)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-F4-S2-S3 ; lem-box-cP-at0210233441 ; lem-box-perm-1423-at0210243143)
open import Examples.Groups.Clifford+CS.FiveV.D.D007 using (lem-F4-K3-S3)
open import Examples.Groups.Clifford+CS.FiveV.D.D008 using (lem-F4-CS2-S3)
open import Examples.Groups.Clifford+CS.FiveV.D.D044 using (lem-F4-CS2-CS2-at02132031 ; lem-F4-CS2-I-at02132031 ; lem-F4-CS2-S2-at02132031 ; lem-F4-I-CS2-at02132031 ; lem-F4-I-S2-at02132031)
open import Examples.Groups.Clifford+CS.FiveV.D.D045 using (lem-F5-23-at02132031)
open import Examples.Groups.Clifford+CS.FiveV.D.D050 using (lem-deb-P-lo-split-a ; lem-deb-P-lo-split-b)
open import Examples.Groups.Clifford+CS.FiveV.D.D051 using (lem-deb-P-lo-part0)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CSd04-TOFF213 ; lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS04-TOFF213)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CCZ023-CK41 ; lem-comm-CK41-CCZ023)
open import Examples.Groups.Clifford+CS.FiveV.D.R006 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L)
open import Examples.Groups.Clifford+CS.FiveV.TR2 using (lem-TR2-4726ca8d)
-- deb-P-lo part1: 32 steps
lem-deb-P-lo-part1 : Ws → ⟪ (CK43 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ
lem-deb-P-lo-part1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CK43 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) (CK43 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ [])
  b0 = at 93 4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S3 c4) ▸
       at 90 4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S3 c4) ▸
       at 87 4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S3 c4) ▸
       at 84 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 81 4 (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-S3 c4) ▸
       at 78 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 75 4 (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-S3 c4) ▸
       at 72 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸ done

  b1 : Chain (CK43 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) (CK43 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ [])
  b1 = at 103 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 100 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 97 4 (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3 c4) ▸
       at 94 4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S3 c4) ▸
       at 91 4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S3 c4) ▸
       at 88 4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S3 c4) ▸
       at 85 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 82 4 (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-S3 c4) ▸ done

  b2 : Chain (CK43 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) (CK43 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ [])
  b2 = at 79 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 76 4 (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-S3 c4) ▸
       at 73 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 104 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 101 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 98 4 (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3 c4) ▸
       at 95 4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S3 c4) ▸
       at 92 4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S3 c4) ▸ done

  b3 : Chain (CK43 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) (CK43 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS34 ∷ CS34 ∷ CS34 ∷ [])
  b3 = at 89 4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S3 c4) ▸
       at 86 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 83 4 (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-S3 c4) ▸
       at 80 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 77 4 (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-S3 c4) ▸
       at 74 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4) ▸
       at 2 64 (CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (sym (lem-deb-P-lo-split-a c4)) ▸
       at 27 44 (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (sym (lem-deb-P-lo-split-b c4)) ▸ done


-- deb-P-lo: 2 steps
lem-deb-P-lo : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ
lem-deb-P-lo c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (CK43 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS34 ∷ CS34 ∷ CS34 ∷ [])
  b0 = at 0 3 (CK43 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) (lem-deb-P-lo-part0 c4) ▸
       at 0 122 (CK43 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) (lem-deb-P-lo-part1 c4) ▸ done


-- deb-P-lo-eps @02132031: 144 steps
lem-deb-P-lo-eps-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-lo-eps-at02132031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (run b17)))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 2 2 [] (wl1083 (lit c4)) ▸
       at 3 2 [] (wl1083 (lit c4)) ▸
       at 4 2 [] (wl1083 (lit c4)) ▸
       at 5 2 [] (wl1083 (lit c4)) ▸
       at 6 2 [] (wl1083 (lit c4)) ▸
       at 7 2 [] (wl1083 (lit c4)) ▸
       at 8 2 [] (wl1083 (lit c4)) ▸
       at 9 2 [] (wl1083 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b1 = at 10 2 [] (wl1083 (lit c4)) ▸
       at 11 2 [] (wl1083 (lit c4)) ▸
       at 12 2 [] (wl1083 (lit c4)) ▸
       at 13 2 [] (wl1083 (lit c4)) ▸
       at 14 2 [] (wl1083 (lit c4)) ▸
       at 15 2 [] (wl1083 (lit c4)) ▸
       at 16 2 [] (wl1083 (lit c4)) ▸
       at 17 2 [] (wl1083 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 18 2 [] (wl1083 (lit c4)) ▸
       at 19 2 [] (wl1083 (lit c4)) ▸
       at 20 2 [] (wl1083 (lit c4)) ▸
       at 21 2 [] (wl1083 (lit c4)) ▸
       at 22 2 [] (wl1083 (lit c4)) ▸
       at 23 2 [] (wl1083 (lit c4)) ▸
       at 24 2 [] (wl1083 (lit c4)) ▸
       at 25 2 [] (wl1083 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ X4 ∷ [])
  b3 = at 26 2 [] (wl1083 (lit c4)) ▸
       at 27 2 [] (wl1083 (lit c4)) ▸
       at 28 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 27 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 26 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 25 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸
       at 24 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 23 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸ done

  b4 : Chain (X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ S4 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ X4 ∷ [])
  b4 = at 22 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 21 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 20 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 19 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 18 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 17 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 16 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 15 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸ done

  b5 : Chain (X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ S4 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ X4 ∷ [])
  b5 = at 14 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 13 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 12 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 11 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 10 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 9 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 8 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 7 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸ done

  b6 : Chain (X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb1-0-42-3 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b6 = at 6 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 5 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 4 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 3 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 2 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 1 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 29 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 28 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸ done

  b7 : Chain (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb1-0-42-3 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b7 = at 27 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 26 2 (Sw01 ∷ S4 ∷ []) (sym (c₂ (Swap) (S ↑ ↑))) ▸
       at 25 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 24 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 23 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 22 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 21 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸
       at 20 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸ done

  b8 : Chain (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b8 = at 19 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸
       at 18 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 17 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 16 2 (Sw01 ∷ S4 ∷ []) (sym (c₂ (Swap) (S ↑ ↑))) ▸
       at 15 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 14 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 13 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 12 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸ done

  b9 : Chain (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b9 = at 11 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸
       at 10 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 9 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸
       at 8 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 7 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 6 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 5 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 4 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸ done

  b10 : Chain (X4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw23 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b10 = at 3 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 2 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 30 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 29 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 28 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 27 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸
       at 26 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 25 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸ done

  b11 : Chain (X4 ∷ Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw23 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ S4 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b11 = at 24 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 23 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 22 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 21 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 20 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 19 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 18 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 17 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸ done

  b12 : Chain (X4 ∷ Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ S4 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b12 = at 16 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 15 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 14 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 13 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 12 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 11 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 10 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 9 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸ done

  b13 : Chain (X4 ∷ Sw12 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b13 = at 8 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 7 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 6 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 5 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 4 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 3 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 31 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 30 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸ done

  b14 : Chain (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b14 = at 29 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 28 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸
       at 27 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 26 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 25 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 24 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 23 2 (Sw12 ∷ CK43 ∷ []) (sym (c₃ (Swap ↑) (CK₁₀))) ▸
       at 22 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸ done

  b15 : Chain (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b15 = at 21 2 (Sw12 ∷ CK43 ∷ []) (sym (c₃ (Swap ↑) (CK₁₀))) ▸
       at 20 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 19 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 18 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸
       at 17 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 16 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 15 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 14 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸ done

  b16 : Chain (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ [])
  b16 = at 13 2 (Sw12 ∷ CK43 ∷ []) (sym (c₃ (Swap ↑) (CK₁₀))) ▸
       at 12 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 11 2 (Sw12 ∷ CK43 ∷ []) (sym (c₃ (Swap ↑) (CK₁₀))) ▸
       at 10 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 9 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 8 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 7 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 6 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸ done

  b17 : Chain (X4 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X4 ∷ []) []
  b17 = at 5 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 4 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 5 27 [] (lem-TR2-4726ca8d c4) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸
       at 3 2 [] (wl0003 (lit c4)) ▸
       at 2 2 [] (wl0018 (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸
       at 0 2 [] (wl1083 (lit c4)) ▸ done


-- F4-S2-CS2 @02132031: 18 steps
lem-F4-S2-CS2-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-CS2-at02132031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0419 c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 2 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ S0 ∷ CS04⁻ ∷ [])
  b1 = at 2 3 (S0 ∷ CS04⁻ ∷ []) (sym (wp0257 c4)) ▸
       at 2 3 (CCZ024 ∷ S0 ∷ CS04⁻ ∷ []) (sym (wp0420 c4)) ▸
       at 4 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸
       at 3 2 (Toff213 ∷ S0 ∷ []) (c₁ (S) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 6 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S0 ∷ CS04⁻ ∷ []) (wp0421 c4) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ S0 ∷ CS04⁻ ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (wp0257 c4) ▸ done


-- F4-K3-CS2 @02132031: 19 steps
lem-F4-K3-CS2-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS2-at02132031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ023 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (Bx2-0341 ∷ []) (lem-box-perm-1423-at0210243143 c4) ▸
       at 3 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0210233441 c4) ▸
       at 2 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (CCZ023 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff214 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0642 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 4 (Toff214 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0642 (lit c4))) ▸
       at 0 4 (Bx2-0341 ∷ []) (sym (lem-box-cP-at0210233441 c4)) ▸
       at 0 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1423-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0517 c4)) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4-CS2-K3 @02132031: 21 steps
lem-F4-CS2-K3-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K3-at02132031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (X4 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK41 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0614 c4)) ▸
       at 1 1 (Bx2-0341 ∷ []) (lem-box-perm-1423-at0210243143 c4) ▸
       at 1 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0210233441 c4) ▸
       at 4 4 (K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ []) (sym (wl0721 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx2-0341 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K1 ∷ CCZ023 ∷ []) (wl0722 (lit c4)) ▸
       at 4 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 (lit c4)) ▸
       at 5 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 2 4 (K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ []) (sym (wl0721 (lit c4))) ▸
       at 1 2 (K1 ∷ CCZ023 ∷ []) (wl0722 (lit c4)) ▸
       at 2 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 (lit c4)) ▸
       at 3 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 4 4 (Bx2-0341 ∷ []) (sym (lem-box-cP-at0210233441 c4)) ▸ done

  b2 : Chain (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx2-0341 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1423-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 4 (CK41 ∷ X4 ∷ []) (sym (wl0723 (lit c4))) ▸ done


-- F4-I-K3 @02132031: 1 steps
lem-F4-I-K3-at02132031 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K3-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0553 (lit c4))) ▸ done


-- F4-S2-K3 @02132031: 1 steps
lem-F4-S2-K3-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K3-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0416 c4)) ▸ done


-- F4-K3-K3 @02132031: 1 steps
lem-F4-K3-K3-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K3-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0607 (lit c4))) ▸ done


-- F4-S2-S2 @02132031: 1 steps
lem-F4-S2-S2-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S2-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸ done


-- F4-K3-S2 @02132031: 1 steps
lem-F4-K3-S2-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S2-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0494 c4)) ▸ done


-- F4-S2-I @02132031: 1 steps
lem-F4-S2-I-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-I-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0410 c4)) ▸ done


-- F4-K3-I @02132031: 1 steps
lem-F4-K3-I-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-I-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0603 (lit c4))) ▸ done


-- F4-S2-S3 @02132031: 1 steps
lem-F4-S2-S3-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S3-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0412 c4)) ▸ done


-- F4-K3-S3 @02132031: 1 steps
lem-F4-K3-S3-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S3-at02132031 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0604 (lit c4))) ▸ done


-- deb-P-lo-split-a @02132031: 136 steps
lem-deb-P-lo-split-a-at02132031 : Ws → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-deb-P-lo-split-a-at02132031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 4 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 3 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 8 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 7 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 6 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 12 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 11 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b1 = at 10 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 9 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 16 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 14 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 13 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 12 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 20 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b2 = at 19 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 18 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 17 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 16 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 24 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 23 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b3 = at 21 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 20 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 19 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 18 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 28 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4)) ▸
       at 27 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 26 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b4 = at 24 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 23 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 21 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 32 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 29 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b5 = at 28 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 27 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 26 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 24 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 36 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4)) ▸
       at 35 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 34 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-K3-K3-at02132031 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b6 = at 33 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 32 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 31 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 29 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 28 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 27 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 40 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b7 = at 39 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 38 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 37 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 36 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 35 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 34 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 33 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 32 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b8 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b8 = at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 44 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 43 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 42 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 41 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 40 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 39 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸ done

  b9 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ CS04 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b9 = at 38 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 37 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 36 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 35 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 34 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 33 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 48 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 47 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸ done

  b10 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ CS04 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ S0 ∷ ι ∷ S0 ∷ [])
  b10 = at 46 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 45 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 44 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 43 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 42 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 41 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 40 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 39 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸ done

  b11 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ ι ∷ S0 ∷ [])
  b11 = at 38 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 37 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 36 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 52 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 51 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 50 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 49 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 48 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸ done

  b12 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ ι ∷ S0 ∷ [])
  b12 = at 47 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 46 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 45 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 44 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 43 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 42 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 41 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 40 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸ done

  b13 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ S0 ∷ [])
  b13 = at 39 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 56 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 55 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at02132031 c4)) ▸
       at 54 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at02132031 c4)) ▸
       at 53 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at02132031 c4)) ▸
       at 52 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 51 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-I-K3-at02132031 c4)) ▸
       at 50 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸ done

  b14 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ S0 ∷ [])
  b14 = at 49 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-I-K3-at02132031 c4)) ▸
       at 48 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 47 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 46 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 45 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 44 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 43 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 42 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸ done

  b15 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ [])
  b15 = at 60 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 59 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-S2-I-at02132031 c4)) ▸
       at 58 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 57 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 56 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 55 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 54 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 53 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸ done

  b16 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ [])
  b16 = at 52 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 51 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 50 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 49 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 48 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 47 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 46 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 45 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸ done


-- deb-P-lo-split-b @02132031: 66 steps
lem-deb-P-lo-split-b-at02132031 : Ws → ⟪ (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-deb-P-lo-split-b-at02132031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 4 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4)) ▸
       at 3 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 8 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 7 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 6 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 12 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4)) ▸
       at 11 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ [])
  b1 = at 10 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-K3-K3-at02132031 c4)) ▸
       at 9 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K3-CS2-at02132031 c4)) ▸
       at 16 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 14 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 13 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 12 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 20 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ [])
  b2 = at 19 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 18 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 17 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 16 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 15 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 24 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 23 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ ι ∷ CS01 ∷ CS01 ∷ [])
  b3 = at 21 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 20 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 19 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 18 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 28 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 27 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 26 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S2-S2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS01 ∷ CS01 ∷ [])
  b4 = at 24 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 23 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S2-K3-at02132031 c4)) ▸
       at 21 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S2-CS2-at02132031 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at02132031 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S2-at02132031 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ CS01 ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-I-K3-at02132031 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-I-K3-at02132031 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 36 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 35 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I-at02132031 c4)) ▸
       at 34 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at02132031 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b6 = at 33 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at02132031 c4)) ▸
       at 32 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at02132031 c4)) ▸
       at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 29 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 28 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 27 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 40 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ [])
  b7 = at 39 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 38 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I-at02132031 c4)) ▸
       at 37 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at02132031 c4)) ▸
       at 36 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at02132031 c4)) ▸
       at 35 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS2-S2-at02132031 c4)) ▸
       at 34 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 33 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 32 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b8 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ [])
  b8 = at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K3-at02132031 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

