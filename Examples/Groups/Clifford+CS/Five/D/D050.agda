{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D050 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl1083 ; wl1411 ; wl1418 ; wl1419 ; wp1266)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F5-23)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-F4-I-CS2 ; lem-F4-I-K3 ; lem-F4-I-S2)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F4-S2-CS2 ; lem-F4-S2-I ; lem-F4-S2-K3 ; lem-F4-S2-S2)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-F4-CS2-I ; lem-F4-K3-CS2 ; lem-F4-K3-K3)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-F4-CS2-K3 ; lem-F4-CS2-S2)
open import Examples.Groups.Clifford+CS.Five.D.D013 using (lem-F4-CS2-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D048 using (lem-F4-CS2-S2-at132132 ; lem-F4-I-S2-at132132 ; lem-F4-K2-S2-at132132 ; lem-F4-S3-S2-at132132 ; lem-deb-P-hi-split-a-at132132 ; lem-deb-P-hi-split-b-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D049 using (lem-deb-P-hi-at132132-part0)
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-4726ca8d)
-- deb-P-hi @132132 part1: 64 steps
lem-deb-P-hi-at132132-part1 : Ws → ⟪ (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-P-hi-at132132-part1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b0 = at 87 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 84 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 81 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 78 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S2-at132132 c4) ▸
       at 75 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 72 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S2-at132132 c4) ▸
       at 69 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 100 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸ done

  b1 : Chain (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b1 = at 97 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 94 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at132132 c4) ▸
       at 91 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 88 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 85 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 82 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 79 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S2-at132132 c4) ▸
       at 76 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸ done

  b2 : Chain (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b2 = at 73 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S2-at132132 c4) ▸
       at 70 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 101 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 98 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 95 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at132132 c4) ▸
       at 92 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 89 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 86 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸ done

  b3 : Chain (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b3 = at 83 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 80 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S2-at132132 c4) ▸
       at 77 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 74 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S2-at132132 c4) ▸
       at 71 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 102 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 99 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 96 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at132132 c4) ▸ done

  b4 : Chain (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b4 = at 93 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 90 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 87 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 84 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 81 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S2-at132132 c4) ▸
       at 78 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 75 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S2-at132132 c4) ▸
       at 72 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸ done

  b5 : Chain (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b5 = at 103 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 100 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 97 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at132132 c4) ▸
       at 94 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 91 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 88 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 85 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 82 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S2-at132132 c4) ▸ done

  b6 : Chain (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b6 = at 79 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 76 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S2-at132132 c4) ▸
       at 73 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 104 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 101 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 98 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at132132 c4) ▸
       at 95 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 92 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸ done

  b7 : Chain (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b7 = at 89 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4) ▸
       at 86 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 83 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S2-at132132 c4) ▸
       at 80 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 77 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S2-at132132 c4) ▸
       at 74 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4) ▸
       at 2 64 (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (sym (lem-deb-P-hi-split-a-at132132 c4)) ▸
       at 27 44 (CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ []) (sym (lem-deb-P-hi-split-b-at132132 c4)) ▸ done


-- deb-P-hi @132132: 2 steps
lem-deb-P-hi-at132132 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-P-hi-at132132 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b0 = at 0 3 (CK41 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-deb-P-hi-at132132-part0 c4) ▸
       at 0 122 (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-deb-P-hi-at132132-part1 c4) ▸ done


-- F1-CS-K0@1: 7 steps
lem-F1-CS-K0at1 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K0at1 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 3 (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-deb-P-hi-at132132 c4) ▸
       at 16 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 35 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 0 43 (CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (wp1266 c4) ▸
       at 18 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 37 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 2 41 (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (sym (lem-deb-P-hi-at132132 c4)) ▸ done


-- deb-P-lo-eps: 28 steps
lem-deb-P-lo-eps : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-lo-eps c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 2 2 [] (wl1083 (lit c4)) ▸
       at 3 2 [] (wl1083 (lit c4)) ▸
       at 4 2 [] (wl1083 (lit c4)) ▸
       at 5 2 [] (wl1083 (lit c4)) ▸
       at 6 2 [] (wl1083 (lit c4)) ▸
       at 7 2 [] (wl1083 (lit c4)) ▸
       at 8 2 [] (wl1083 (lit c4)) ▸
       at 9 2 [] (wl1083 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 10 2 [] (wl1083 (lit c4)) ▸
       at 11 2 [] (wl1083 (lit c4)) ▸
       at 12 2 [] (wl1083 (lit c4)) ▸
       at 13 2 [] (wl1083 (lit c4)) ▸
       at 14 2 [] (wl1083 (lit c4)) ▸
       at 15 2 [] (wl1083 (lit c4)) ▸
       at 16 2 [] (wl1083 (lit c4)) ▸
       at 17 2 [] (wl1083 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 18 2 [] (wl1083 (lit c4)) ▸
       at 19 2 [] (wl1083 (lit c4)) ▸
       at 20 2 [] (wl1083 (lit c4)) ▸
       at 21 2 [] (wl1083 (lit c4)) ▸
       at 22 2 [] (wl1083 (lit c4)) ▸
       at 23 2 [] (wl1083 (lit c4)) ▸
       at 24 2 [] (wl1083 (lit c4)) ▸
       at 25 2 [] (wl1083 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) []
  b3 = at 26 2 [] (wl1083 (lit c4)) ▸
       at 27 2 [] (wl1083 (lit c4)) ▸
       at 1 27 [] (lem-TR2-4726ca8d c4) ▸
       at 0 2 [] (wl1083 (lit c4)) ▸ done


-- deb-P-lo-split-a: 136 steps
lem-deb-P-lo-split-a : Ws → ⟪ (CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-P-lo-split-a c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 4 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 3 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 8 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 7 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 6 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 12 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 11 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b1 = at 10 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 9 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 16 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 15 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 14 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 13 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 12 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 20 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b2 = at 19 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 18 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 17 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 16 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 15 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 24 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 23 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 22 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b3 = at 21 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 20 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 19 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 18 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 28 1 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl1419 (lit c4)) ▸
       at 27 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 26 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 25 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b4 = at 24 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 23 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 22 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 21 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 32 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 31 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 30 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 29 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b5 = at 28 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 27 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 26 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 25 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 24 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 36 1 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl1419 (lit c4)) ▸
       at 35 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 34 4 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-K3-K3 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b6 = at 33 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 32 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 31 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 30 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 29 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 28 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 27 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 40 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b7 = at 39 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 38 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 37 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 36 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 35 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 34 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 33 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 32 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

  b8 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b8 = at 31 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 30 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 44 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 43 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 42 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 41 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 40 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 39 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸ done

  b9 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b9 = at 38 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 37 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 36 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 35 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 34 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 33 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 48 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 47 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸ done

  b10 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b10 = at 46 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 45 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 44 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 43 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 42 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 41 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 40 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 39 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸ done

  b11 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ S2 ∷ [])
  b11 = at 38 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 37 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 36 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 52 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 51 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 50 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 49 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 48 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸ done

  b12 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ S2 ∷ [])
  b12 = at 47 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 46 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 45 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 44 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 43 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 42 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 41 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 40 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸ done

  b13 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ S2 ∷ [])
  b13 = at 39 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 56 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 55 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 54 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 53 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 52 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 51 4 (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-I-K3 c4)) ▸
       at 50 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸ done

  b14 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ S2 ∷ [])
  b14 = at 49 4 (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-I-K3 c4)) ▸
       at 48 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 47 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 46 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 45 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 44 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 43 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 42 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸ done

  b15 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ [])
  b15 = at 60 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 59 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-S2-I c4)) ▸
       at 58 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 57 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 56 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 55 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 54 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 53 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸ done

  b16 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ [])
  b16 = at 52 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 51 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 50 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 49 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 48 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 47 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 46 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 45 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸ done


-- deb-P-lo-split-b: 66 steps
lem-deb-P-lo-split-b : Ws → ⟪ (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-deb-P-lo-split-b c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 4 1 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl1419 (lit c4)) ▸
       at 3 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 8 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 7 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 6 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 12 1 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl1419 (lit c4)) ▸
       at 11 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ [])
  b1 = at 10 4 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-K3-K3 c4)) ▸
       at 9 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 16 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 15 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 14 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 13 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 12 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 20 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ [])
  b2 = at 19 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 18 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 17 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 16 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 15 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 24 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 23 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 22 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ CS23 ∷ CS23 ∷ [])
  b3 = at 21 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 20 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 19 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 18 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 28 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 27 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 26 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 25 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS23 ∷ CS23 ∷ [])
  b4 = at 24 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 23 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 22 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 21 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ CS23 ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-I-K3 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-I-K3 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 36 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 35 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I c4)) ▸
       at 34 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ [])
  b6 = at 33 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 32 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 31 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 30 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 29 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 28 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 27 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 40 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  b7 = at 39 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 38 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I c4)) ▸
       at 37 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 36 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 35 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 34 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 33 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 32 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

  b8 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  b8 = at 31 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 30 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

