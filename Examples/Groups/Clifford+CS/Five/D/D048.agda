{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D048 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl1411 ; wl1418 ; wl1419 ; wl1409 ; wl1410 ; wl1417)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F4-I-K2 ; lem-F4-I-K3 ; lem-F4-I-S2 ; lem-F4-I-S3 ; lem-F4-K2-K2 ; lem-F4-K3-K3 ; lem-F4-S2-I ; lem-F4-S2-K3 ; lem-F4-S2-S2 ; lem-F4-S3-I ; lem-F4-S3-K2 ; lem-F4-S3-S3)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-K2-at132132 ; lem-F4-I-S3-at132132 ; lem-F4-K2-K2-at132132 ; lem-F4-S3-I-at132132 ; lem-F4-S3-K2-at132132 ; lem-F4-S3-S3-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-F4-CS2-I ; lem-F4-CS2-S2 ; lem-F4-I-CS2 ; lem-F4-K2-CS2 ; lem-F4-S2-CS2 ; lem-F4-S3-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-F4-CS2-K2)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F4-CS2-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-F4-CS2-CS2-at132132 ; lem-F4-CS2-K2-at132132 ; lem-F4-I-CS2-at132132 ; lem-F4-K2-CS2-at132132 ; lem-F4-S3-CS2-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F4-CS2-K3 ; lem-F4-K3-CS2 ; lem-F5-23)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-F5-23-at132132)

-- deb-Q-lo-split-b: 45 steps
lem-deb-Q-lo-split-b : Ws → ⟪ (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) ⟫ʷ
lem-deb-Q-lo-split-b c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 4 1 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl1419 (lit c4)) ▸
       at 3 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 8 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 7 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 6 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 12 1 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl1419 (lit c4)) ▸
       at 11 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b1 = at 10 4 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-K3-K3 c4)) ▸
       at 9 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 16 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 15 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 14 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 13 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 12 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 20 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ [])
  b2 = at 19 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 18 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 17 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 16 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 15 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 24 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 23 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 22 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ [])
  b3 = at 21 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 20 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 19 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 18 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 28 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 27 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 26 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 25 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ [])
  b4 = at 24 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 23 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 22 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 21 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-I-K3 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-I-K3 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸ done

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

-- deb-Q-hi-split-a @132132: 55 steps
lem-deb-Q-hi-split-a-at132132 : Ws → ⟪ (CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-Q-hi-split-a-at132132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 4 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4)) ▸
       at 3 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K2-CS2-at132132 c4)) ▸
       at 8 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 7 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K2-at132132 c4)) ▸
       at 6 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 12 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4)) ▸
       at 11 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K2-CS2-at132132 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b1 = at 10 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-K2-K2-at132132 c4)) ▸
       at 9 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K2-CS2-at132132 c4)) ▸
       at 16 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 15 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K2-at132132 c4)) ▸
       at 14 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 13 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K2-at132132 c4)) ▸
       at 12 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 20 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ S2 ∷ [])
  b2 = at 19 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 18 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 17 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 16 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 15 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 24 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 23 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S3-S3-at132132 c4)) ▸
       at 22 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ S2 ∷ [])
  b3 = at 21 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 20 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 19 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 18 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 28 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 27 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S3-S3-at132132 c4)) ▸
       at 26 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S3-S3-at132132 c4)) ▸
       at 25 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ S2 ∷ [])
  b4 = at 24 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 23 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 22 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 21 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S3-at132132 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S3-at132132 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S3-at132132 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ S2 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-I-K2-at132132 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-I-K2-at132132 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 36 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 35 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-S3-I-at132132 c4)) ▸
       at 34 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S3-S3-at132132 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ [])
  b6 = at 33 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S3-S3-at132132 c4)) ▸
       at 32 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S3-S3-at132132 c4)) ▸
       at 31 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 30 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 29 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 28 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 27 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸ done

-- deb-Q-hi-split-b @132132: 45 steps
lem-deb-Q-hi-split-b-at132132 : Ws → ⟪ (CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) ⟫ʷ
lem-deb-Q-hi-split-b-at132132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 4 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4)) ▸
       at 3 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K2-CS2-at132132 c4)) ▸
       at 8 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 7 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K2-at132132 c4)) ▸
       at 6 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 12 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4)) ▸
       at 11 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K2-CS2-at132132 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b1 = at 10 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-K2-K2-at132132 c4)) ▸
       at 9 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K2-CS2-at132132 c4)) ▸
       at 16 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 15 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K2-at132132 c4)) ▸
       at 14 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 13 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS2-K2-at132132 c4)) ▸
       at 12 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 20 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ [])
  b2 = at 19 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 18 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 17 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 16 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 15 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 24 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 23 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S3-S3-at132132 c4)) ▸
       at 22 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ [])
  b3 = at 21 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 20 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 19 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 18 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 28 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 27 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S3-S3-at132132 c4)) ▸
       at 26 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S3-S3-at132132 c4)) ▸
       at 25 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ [])
  b4 = at 24 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 23 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 22 4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-S3-K2-at132132 c4)) ▸
       at 21 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S3-CS2-at132132 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S3-at132132 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S3-at132132 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S3-at132132 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-I-K2-at132132 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-I-K2-at132132 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸ done

-- deb-AD-split-a: 136 steps
lem-deb-AD-split-a : Ws → ⟪ (CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-AD-split-a c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
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

-- deb-AD-split-b: 66 steps
lem-deb-AD-split-b : Ws → ⟪ (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-deb-AD-split-b c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
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
