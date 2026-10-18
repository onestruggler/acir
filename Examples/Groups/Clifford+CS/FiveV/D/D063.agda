{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D063 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl1411 ; wl1418 ; wl1419)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-F5-23)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-F4-I-CS2 ; lem-F4-I-I ; lem-F4-I-K3 ; lem-F4-I-S2)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-F4-S2-CS2 ; lem-F4-S2-I ; lem-F4-S2-K3 ; lem-F4-S2-S2)
open import Examples.Groups.Clifford+CS.FiveV.D.D007 using (lem-F4-CS2-I ; lem-F4-K3-CS2 ; lem-F4-K3-I ; lem-F4-K3-K3 ; lem-F4-K3-S2)
open import Examples.Groups.Clifford+CS.FiveV.D.D008 using (lem-F4-CS2-K3 ; lem-F4-CS2-S2)
open import Examples.Groups.Clifford+CS.FiveV.D.D013 using (lem-F4-CS2-CS2)
-- deb-CKS-split-b: 190 steps
lem-deb-CKS-split-b : Ws → ⟪ (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) ⟫ʷ
lem-deb-CKS-split-b c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (run b23)))))))))))))))))))))))
  where
  b0 : Chain (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 4 1 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl1419 (lit c4)) ▸
       at 3 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 8 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 7 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 6 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 12 1 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl1419 (lit c4)) ▸
       at 11 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b1 = at 10 4 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-K3-K3 c4)) ▸
       at 9 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 16 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 15 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 14 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 13 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 12 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 20 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b2 = at 19 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 18 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 17 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 16 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 15 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 24 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 23 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 22 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b3 = at 21 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 20 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 19 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 18 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 28 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 27 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 26 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 25 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b4 = at 24 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 23 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 22 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 21 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-I-K3 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-I-K3 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 36 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 35 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I c4)) ▸
       at 34 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b6 = at 33 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 32 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 31 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 30 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 29 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 28 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 27 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 40 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b7 = at 39 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 38 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I c4)) ▸
       at 37 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 36 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 35 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 34 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 33 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 32 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

  b8 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b8 = at 31 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 30 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 44 1 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl1419 (lit c4)) ▸
       at 43 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 42 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 41 4 (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-K3-I c4)) ▸
       at 40 4 (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-K3-S2 c4)) ▸
       at 39 4 (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-K3-S2 c4)) ▸ done

  b9 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b9 = at 38 4 (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-K3-S2 c4)) ▸
       at 37 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 36 4 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-K3-K3 c4)) ▸
       at 35 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 34 4 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-K3-K3 c4)) ▸
       at 33 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 48 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 47 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸ done

  b10 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b10 = at 46 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 45 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 44 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I c4)) ▸
       at 43 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 42 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 41 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 40 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 39 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸ done

  b11 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b11 = at 38 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 37 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 36 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 52 1 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl1419 (lit c4)) ▸
       at 51 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 50 4 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-K3-K3 c4)) ▸
       at 49 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 48 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸ done

  b12 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b12 = at 47 4 (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-K3-I c4)) ▸
       at 46 4 (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-K3-S2 c4)) ▸
       at 45 4 (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-K3-S2 c4)) ▸
       at 44 4 (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-K3-S2 c4)) ▸
       at 43 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 42 4 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-K3-K3 c4)) ▸
       at 41 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 40 4 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-K3-K3 c4)) ▸ done

  b13 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b13 = at 39 4 (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K3-CS2 c4)) ▸
       at 56 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 55 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 54 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 53 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 52 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 51 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 50 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I c4)) ▸ done

  b14 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b14 = at 49 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 48 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 47 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS2-S2 c4)) ▸
       at 46 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 45 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 44 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 43 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-CS2-K3 c4)) ▸
       at 42 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

  b15 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b15 = at 60 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 59 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 58 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 57 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 56 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 55 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 54 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 53 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-S2-I c4)) ▸ done

  b16 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ [])
  b16 = at 52 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 51 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 50 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 49 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 48 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 47 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 46 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 45 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸ done

  b17 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ [])
  b17 = at 64 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 63 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 62 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 61 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 60 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 59 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 58 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 57 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸ done

  b18 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ [])
  b18 = at 56 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-S2-I c4)) ▸
       at 55 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 54 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 53 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 52 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 51 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 50 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 49 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸ done

  b19 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ [])
  b19 = at 48 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 68 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl1418 (lit c4)) ▸
       at 67 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 66 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 65 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 64 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 63 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 62 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸ done

  b20 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ [])
  b20 = at 61 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 60 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 59 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-S2-I c4)) ▸
       at 58 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 57 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 56 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-S2-S2 c4)) ▸
       at 55 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 54 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸ done

  b21 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ [])
  b21 = at 53 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 52 4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-S2-K3 c4)) ▸
       at 51 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S2-CS2 c4)) ▸
       at 72 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 71 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 70 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 69 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 68 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸ done

  b22 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ [])
  b22 = at 67 4 (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-I-K3 c4)) ▸
       at 66 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 65 4 (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-I-K3 c4)) ▸
       at 64 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 63 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 62 4 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-I-I c4)) ▸
       at 61 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 60 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸ done

  b23 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ [])
  b23 = at 59 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-I-S2 c4)) ▸
       at 58 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 57 4 (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-I-K3 c4)) ▸
       at 56 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 55 4 (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (sym (lem-F4-I-K3 c4)) ▸
       at 54 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸ done

